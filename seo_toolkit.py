#!/usr/bin/env python3
"""
SEO Toolkit - small CLI for technical SEO automation at scale (stdlib only).

Commands
  crawl      Discover URLs by crawling a site and write them to a CSV
  generate   Build segmented XML sitemaps + a sitemap index from a CSV of URLs
  audit      Crawl every URL in a sitemap (or sitemap index) and report SEO issues per page-type segment
  robots     Monitor robots.txt for changes and check that important URLs are not blocked
  logs       Analyse server access logs for Googlebot crawl behaviour and crawl waste

Examples
  python seo_toolkit.py crawl https://example.com --out urls.csv --max 500
  python seo_toolkit.py crawl https://example.com --out urls.csv --sitemaps sitemaps/
  python seo_toolkit.py generate urls.csv --base-url https://example.com --out sitemaps/
  python seo_toolkit.py audit https://example.com/sitemap.xml --limit 200 --out audit.csv
  python seo_toolkit.py robots https://example.com --urls important_urls.txt
  python seo_toolkit.py logs access.log
"""
import argparse
import csv
import difflib
import gzip
import hashlib
import os
import re
import sys
import time
import xml.etree.ElementTree as ET
from collections import Counter, defaultdict, deque
from concurrent.futures import ThreadPoolExecutor
from datetime import date
from html.parser import HTMLParser
from urllib import robotparser
from xml.sax.saxutils import escape
from urllib.error import HTTPError, URLError
from urllib.parse import urldefrag, urljoin, urlparse
from urllib.request import HTTPRedirectHandler, Request, build_opener, urlopen

UA = "SEOToolkit/1.0 (+technical SEO audit)"
MAX_URLS_PER_SITEMAP = 50_000  # Google limit (also 50MB uncompressed)
TITLE_MAX, DESC_MAX = 60, 160
SKIP_EXT = {
    ".jpg", ".jpeg", ".png", ".gif", ".webp", ".svg", ".ico", ".css", ".js",
    ".pdf", ".zip", ".gz", ".mp3", ".mp4", ".woff", ".woff2", ".ttf", ".eot",
    ".xml", ".json", ".txt", ".rss", ".atom",
}


# ----------------------------------------------------------------- helpers
class NoRedirect(HTTPRedirectHandler):
    """Do not follow redirects, so we can report 301/302 as they are."""
    def redirect_request(self, *args, **kwargs):
        return None


OPENER = build_opener(NoRedirect)


def fetch(url, timeout=15):
    """Return (status, headers, body_bytes). Status 0 means network error."""
    req = Request(url, headers={"User-Agent": UA})
    try:
        with OPENER.open(req, timeout=timeout) as r:
            return r.status, r.headers, r.read()
    except HTTPError as e:  # 3xx/4xx/5xx land here because redirects are disabled
        return e.code, e.headers, b""
    except (URLError, TimeoutError, OSError):
        return 0, {}, b""


def fetch_follow(url, timeout=15):
    """Fetch a URL following redirects. Return (final_url, status, content_type, body)."""
    req = Request(url, headers={"User-Agent": UA})
    try:
        with urlopen(req, timeout=timeout) as r:
            return r.geturl(), r.status, (r.headers.get("Content-Type") or ""), r.read()
    except HTTPError as e:
        return url, e.code, (e.headers.get("Content-Type") if e.headers else ""), b""
    except (URLError, TimeoutError, OSError) as e:
        print(f"  ! fetch failed {url}: {e}")
        return url, 0, "", b""


def segment_of(url):
    """Page-type segment = first path folder, e.g. /loans/personal-loan -> 'loans'."""
    parts = [p for p in urlparse(url).path.split("/") if p]
    return parts[0] if len(parts) > 1 else "root"


class PageParser(HTMLParser):
    def __init__(self):
        super().__init__()
        self.title, self.desc, self.robots, self.canonical = "", "", "", ""
        self.h1_count, self._in_title = 0, False

    def handle_starttag(self, tag, attrs):
        a = dict(attrs)
        if tag == "title":
            self._in_title = True
        elif tag == "h1":
            self.h1_count += 1
        elif tag == "meta":
            name = (a.get("name") or "").lower()
            if name == "description":
                self.desc = (a.get("content") or "").strip()
            elif name == "robots":
                self.robots = (a.get("content") or "").lower()
        elif tag == "link" and (a.get("rel") or "").lower() == "canonical":
            self.canonical = (a.get("href") or "").strip()

    def handle_endtag(self, tag):
        if tag == "title":
            self._in_title = False

    def handle_data(self, data):
        if self._in_title:
            self.title += data


class LinkParser(HTMLParser):
    """Collect absolute-ready href values from <a> tags."""
    def __init__(self):
        super().__init__()
        self.hrefs = []

    def handle_starttag(self, tag, attrs):
        if tag != "a":
            return
        href = dict(attrs).get("href")
        if href:
            self.hrefs.append(href.strip())


def strip_ns(tag):
    return tag.split("}", 1)[-1]


def normalize_url(url, base):
    """Resolve relative links, drop fragments, and keep http(s) only."""
    absolute = urljoin(base, url)
    absolute, _ = urldefrag(absolute)
    p = urlparse(absolute)
    if p.scheme not in ("http", "https") or not p.netloc:
        return None
    # Drop trailing slash except for bare domain roots
    path = p.path or "/"
    if path != "/" and path.endswith("/"):
        path = path.rstrip("/")
    return f"{p.scheme}://{p.netloc.lower()}{path}" + (f"?{p.query}" if p.query else "")


def same_site(url, seed_netloc):
    host = urlparse(url).netloc.lower()
    seed = seed_netloc.lower()
    return host == seed or host == f"www.{seed}" or seed == f"www.{host}"


def is_crawlable_page(url):
    path = urlparse(url).path.lower()
    _, ext = os.path.splitext(path)
    return ext not in SKIP_EXT


def read_sitemap(url, seen=None):
    """Recursively read a sitemap or sitemap index. Returns list of page URLs."""
    seen = seen if seen is not None else set()
    if url in seen:
        return []
    seen.add(url)
    status, _, body = fetch(url)
    if status != 200:
        print(f"  ! could not fetch sitemap {url} (status {status})")
        return []
    if body[:2] == b"\x1f\x8b":
        body = gzip.decompress(body)
    root = ET.fromstring(body)
    locs = [e.text.strip() for e in root.iter() if strip_ns(e.tag) == "loc" and e.text]
    if strip_ns(root.tag) == "sitemapindex":
        urls = []
        for child in locs:
            urls.extend(read_sitemap(child, seen))
        return urls
    return locs


# ------------------------------------------------------------------- crawl
def cmd_crawl(args):
    seed = args.seed.rstrip("/")
    seed_netloc = urlparse(seed).netloc
    if not seed_netloc:
        print(f"! invalid seed URL: {args.seed}")
        return

    rp = None
    if not args.ignore_robots:
        robots_url = f"{urlparse(seed).scheme}://{seed_netloc}/robots.txt"
        status, _, body = fetch(robots_url)
        if status == 200:
            rp = robotparser.RobotFileParser()
            rp.parse(body.decode("utf-8", errors="ignore").splitlines())
            print(f"Loaded robots.txt from {robots_url}")
        else:
            print(f"No usable robots.txt (status {status}); crawling without it.")

    queue = deque([normalize_url(seed, seed) or seed])
    seen, found = set(), []

    print(f"Crawling {seed} (max {args.max} pages)...")
    while queue and len(found) < args.max:
        url = queue.popleft()
        if url in seen:
            continue
        seen.add(url)
        if rp and not rp.can_fetch(UA, url):
            print(f"  skip (robots): {url}")
            continue

        final_url, status, ctype, body = fetch_follow(url)
        final_url = normalize_url(final_url, final_url) or final_url
        if final_url not in seen:
            seen.add(final_url)

        if status != 200:
            print(f"  [{status}] {url}")
            continue
        if "html" not in (ctype or "").lower() and body[:200].lstrip()[:1] != b"<":
            continue
        if not same_site(final_url, seed_netloc):
            continue

        found.append(final_url)
        print(f"  [{len(found):>4}/{args.max}] {final_url}")

        parser = LinkParser()
        try:
            parser.feed(body.decode("utf-8", errors="ignore"))
        except Exception:
            continue
        for href in parser.hrefs:
            link = normalize_url(href, final_url)
            if not link or link in seen:
                continue
            if not same_site(link, seed_netloc) or not is_crawlable_page(link):
                continue
            if args.no_query and "?" in link:
                continue
            queue.append(link)

        if args.delay > 0:
            time.sleep(args.delay)

    found = sorted(set(found))
    with open(args.out, "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["url", "lastmod"])
        for u in found:
            w.writerow([u, ""])
    print(f"\nWrote {len(found)} URLs -> {args.out}")

    if args.sitemaps:
        gen = argparse.Namespace(csv=args.out, base_url=seed, out=args.sitemaps)
        cmd_generate(gen)


# ---------------------------------------------------------------- generate
def cmd_generate(args):
    groups = defaultdict(list)
    with open(args.csv, newline="", encoding="utf-8") as f:
        for row in csv.DictReader(f):
            groups[segment_of(row["url"])].append((row["url"], row.get("lastmod", "")))

    os.makedirs(args.out, exist_ok=True)
    base = args.base_url.rstrip("/")
    index_entries = []
    for seg, rows in sorted(groups.items()):
        for n, start in enumerate(range(0, len(rows), MAX_URLS_PER_SITEMAP), 1):
            chunk = rows[start:start + MAX_URLS_PER_SITEMAP]
            name = f"sitemap-{seg}-{n}.xml"
            lines = ['<?xml version="1.0" encoding="UTF-8"?>',
                     '<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">']
            for u, lm in chunk:
                lines.append("  <url>")
                lines.append(f"    <loc>{escape(u)}</loc>")
                if lm:
                    lines.append(f"    <lastmod>{lm}</lastmod>")
                lines.append("  </url>")
            lines.append("</urlset>")
            with open(os.path.join(args.out, name), "w", encoding="utf-8") as f:
                f.write("\n".join(lines))
            index_entries.append(name)
            print(f"  wrote {name} ({len(chunk)} URLs)")

    idx = ['<?xml version="1.0" encoding="UTF-8"?>',
           '<sitemapindex xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">']
    for name in index_entries:
        idx += ["  <sitemap>", f"    <loc>{base}/{name}</loc>",
                f"    <lastmod>{date.today().isoformat()}</lastmod>", "  </sitemap>"]
    idx.append("</sitemapindex>")
    with open(os.path.join(args.out, "sitemap-index.xml"), "w", encoding="utf-8") as f:
        f.write("\n".join(idx))
    print(f"Done: {sum(len(v) for v in groups.values())} URLs, "
          f"{len(index_entries)} sitemaps, 1 index -> {args.out}/")


# ------------------------------------------------------------------- audit
def audit_one(url):
    status, headers, body = fetch(url)
    row = {"url": url, "segment": segment_of(url), "status": status, "redirect_to": "",
           "title": "", "title_len": 0, "description_len": 0, "canonical": "",
           "noindex": False, "h1_count": 0, "issues": []}
    issues = row["issues"]
    if status == 0:
        issues.append("unreachable")
        return row
    if 300 <= status < 400:
        row["redirect_to"] = headers.get("Location", "")
        issues.append(f"redirect_{status}_in_sitemap")
        return row
    if status != 200:
        issues.append(f"status_{status}")
        return row

    p = PageParser()
    p.feed(body.decode("utf-8", errors="ignore"))
    row.update(title=p.title.strip(), title_len=len(p.title.strip()),
               description_len=len(p.desc), canonical=p.canonical, h1_count=p.h1_count)
    x_robots = (headers.get("X-Robots-Tag") or "").lower()
    row["noindex"] = "noindex" in p.robots or "noindex" in x_robots

    if not row["title"]:
        issues.append("missing_title")
    elif row["title_len"] > TITLE_MAX:
        issues.append("title_too_long")
    if not p.desc:
        issues.append("missing_description")
    elif len(p.desc) > DESC_MAX:
        issues.append("description_too_long")
    if not p.canonical:
        issues.append("missing_canonical")
    elif p.canonical.rstrip("/") != url.rstrip("/"):
        issues.append("canonical_points_elsewhere")
    if row["noindex"]:
        issues.append("noindex_in_sitemap")
    if p.h1_count != 1:
        issues.append(f"h1_count_{p.h1_count}")
    return row


def cmd_audit(args):
    print(f"Reading sitemap: {args.sitemap}")
    urls = read_sitemap(args.sitemap)
    print(f"  found {len(urls)} URLs")
    if args.limit:
        urls = urls[: args.limit]
        print(f"  auditing first {len(urls)}")

    with ThreadPoolExecutor(max_workers=args.workers) as ex:
        rows = list(ex.map(audit_one, urls))

    # duplicate titles across the crawl
    titles = Counter(r["title"] for r in rows if r["title"])
    for r in rows:
        if r["title"] and titles[r["title"]] > 1:
            r["issues"].append("duplicate_title")

    with open(args.out, "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["url", "segment", "status", "redirect_to", "title", "title_len",
                    "description_len", "canonical", "noindex", "h1_count", "issues"])
        for r in rows:
            w.writerow([r["url"], r["segment"], r["status"], r["redirect_to"], r["title"],
                        r["title_len"], r["description_len"], r["canonical"], r["noindex"],
                        r["h1_count"], "; ".join(r["issues"])])

    by_seg = defaultdict(list)
    for r in rows:
        by_seg[r["segment"]].append(r)
    print(f"\n{'segment':<18}{'pages':>7}{'clean':>8}{'with issues':>13}")
    for seg, rs in sorted(by_seg.items(), key=lambda kv: -len(kv[1])):
        bad = sum(1 for r in rs if r["issues"])
        print(f"{seg:<18}{len(rs):>7}{len(rs) - bad:>8}{bad:>13}")
    issue_counts = Counter(i for r in rows for i in r["issues"])
    print("\nTop issues:")
    for issue, n in issue_counts.most_common(10):
        print(f"  {n:>5}  {issue}")
    print(f"\nFull report: {args.out}")


# ------------------------------------------------------------------ robots
def cmd_robots(args):
    site = args.site.rstrip("/")
    robots_url = f"{site}/robots.txt"
    status, _, body = fetch(robots_url)
    if status != 200:
        print(f"! robots.txt returned status {status} ({robots_url})")
        return
    text = body.decode("utf-8", errors="ignore")
    digest = hashlib.sha256(text.encode()).hexdigest()

    # 1) change detection against the last saved snapshot
    if os.path.exists(args.snapshot):
        old = open(args.snapshot, encoding="utf-8").read()
        if old != text:
            print("!! robots.txt CHANGED since last check:")
            for line in difflib.unified_diff(old.splitlines(), text.splitlines(),
                                             "previous", "current", lineterm=""):
                print("   " + line)
        else:
            print("robots.txt unchanged.")
    else:
        print("No previous snapshot, saving the first one.")
    with open(args.snapshot, "w", encoding="utf-8") as f:
        f.write(text)
    print(f"sha256: {digest[:16]}...")

    # 2) dangerous rules
    for line in text.splitlines():
        if re.match(r"(?i)\s*disallow:\s*/\s*$", line):
            print("!! 'Disallow: /' found - this blocks the whole site for that user-agent.")

    # 3) are important URLs blocked for Googlebot?
    if args.urls:
        rp = robotparser.RobotFileParser()
        rp.parse(text.splitlines())
        blocked = [u for u in (l.strip() for l in open(args.urls)) if u
                   and not rp.can_fetch("Googlebot", u)]
        print(f"\n{len(blocked)} important URL(s) blocked for Googlebot:")
        for u in blocked:
            print("  BLOCKED", u)


# -------------------------------------------------------------------- logs
LOG_RE = re.compile(r'^(\S+) \S+ \S+ \[[^\]]+\] "(?:\S+) (\S+)[^"]*" (\d{3}) \S+ "[^"]*" "([^"]*)"')


def cmd_logs(args):
    total = bot = 0
    status, segs, urls = Counter(), Counter(), Counter()
    param_hits = 0
    opener = gzip.open if args.logfile.endswith(".gz") else open
    with opener(args.logfile, "rt", errors="ignore") as f:
        for line in f:
            m = LOG_RE.match(line)
            if not m:
                continue
            total += 1
            _ip, path, code, ua = m.groups()
            if "googlebot" not in ua.lower():
                continue
            bot += 1
            status[code] += 1
            segs[segment_of("https://x" + path)] += 1
            urls[path] += 1
            if "?" in path:
                param_hits += 1

    if not bot:
        print(f"No Googlebot hits found in {total} log lines.")
        return
    print(f"Log lines: {total} | Googlebot hits: {bot} ({bot / total:.1%})")
    print("\nStatus codes (Googlebot):")
    for code, n in sorted(status.items()):
        print(f"  {code}: {n} ({n / bot:.1%})")
    print("\nCrawl share by page-type segment:")
    for seg, n in segs.most_common(10):
        print(f"  {seg:<18}{n:>7} ({n / bot:.1%})")
    print(f"\nCrawl waste: {param_hits} hits ({param_hits / bot:.1%}) on parameter URLs")
    non200 = sum(n for c, n in status.items() if c != "200")
    print(f"Crawl waste: {non200} hits ({non200 / bot:.1%}) on non-200 responses")
    print("\nMost crawled URLs:")
    for u, n in urls.most_common(args.top):
        print(f"  {n:>6}  {u}")
    print("\nNote: user-agent strings can be faked. For real analysis, verify Googlebot "
          "IPs with reverse DNS.")


# -------------------------------------------------------------------- main
def main():
    ap = argparse.ArgumentParser(description="Technical SEO automation toolkit")
    sub = ap.add_subparsers(dest="cmd", required=True)

    c = sub.add_parser("crawl", help="discover URLs by crawling a site; write urls.csv")
    c.add_argument("seed", help="starting URL, e.g. https://example.com")
    c.add_argument("--out", default="urls.csv", help="output CSV path (default: urls.csv)")
    c.add_argument("--max", type=int, default=500, help="max pages to crawl (default: 500)")
    c.add_argument("--delay", type=float, default=0.2, help="seconds between requests")
    c.add_argument("--no-query", action="store_true", help="skip URLs with ?query strings")
    c.add_argument("--ignore-robots", action="store_true", help="do not honour robots.txt")
    c.add_argument("--sitemaps", help="also run generate into this folder after crawling")
    c.set_defaults(func=cmd_crawl)

    g = sub.add_parser("generate", help="segmented sitemaps from a CSV (columns: url[,lastmod])")
    g.add_argument("csv")
    g.add_argument("--base-url", required=True)
    g.add_argument("--out", default="sitemaps")
    g.set_defaults(func=cmd_generate)

    a = sub.add_parser("audit", help="crawl sitemap URLs and report SEO issues")
    a.add_argument("sitemap")
    a.add_argument("--limit", type=int, default=0)
    a.add_argument("--workers", type=int, default=10)
    a.add_argument("--out", default="audit.csv")
    a.set_defaults(func=cmd_audit)

    r = sub.add_parser("robots", help="monitor robots.txt and check blocked URLs")
    r.add_argument("site")
    r.add_argument("--urls", help="text file of important URLs, one per line")
    r.add_argument("--snapshot", default="robots.snapshot.txt")
    r.set_defaults(func=cmd_robots)

    l = sub.add_parser("logs", help="Googlebot analysis from an access log")
    l.add_argument("logfile")
    l.add_argument("--top", type=int, default=10)
    l.set_defaults(func=cmd_logs)

    args = ap.parse_args()
    args.func(args)


if __name__ == "__main__":
    sys.exit(main())
