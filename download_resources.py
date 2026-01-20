#!/usr/bin/env python3

import argparse
import os
from html.parser import HTMLParser
from os import path
from urllib.parse import urljoin, urlsplit
from urllib.request import urlopen

BASE_URL = "https://projecteuler.net/"


class ResourceParser(HTMLParser):
    def __init__(self):
        super().__init__()
        self.urls = set()

    def handle_starttag(self, tag, attrs):
        for key, value in attrs:
            if key in {"href", "src"} and value:
                self.urls.add(value)


def iter_resource_urls(html_text):
    parser = ResourceParser()
    parser.feed(html_text)
    for url in sorted(parser.urls):
        yield url


def local_path_for_resource(resource_url):
    parsed = urlsplit(resource_url)
    resource_path = parsed.path
    if resource_path.startswith("/"):
        resource_path = resource_path[1:]
    if resource_path.startswith("resources/documents/") and resource_path.endswith(
        ".txt"
    ):
        filename = path.basename(resource_path)
        return path.join("data", "documents", filename)
    if resource_path.startswith("resources/images/"):
        filename = path.basename(resource_path)
        return path.join("data", "images", filename)
    return None


def download_resource(resource_url, dest_path):
    os.makedirs(path.dirname(dest_path), exist_ok=True)
    full_url = urljoin(BASE_URL, resource_url)
    with urlopen(full_url) as response, open(dest_path, "wb") as out_f:
        out_f.write(response.read())


def process_minimal_file(minimal_path):
    print(f"Processing {minimal_path}")
    with open(minimal_path, "r") as minimal_f:
        html_text = minimal_f.read()

    for resource_url in iter_resource_urls(html_text):
        local_path = local_path_for_resource(resource_url)
        if not local_path:
            continue
        print(f"  downloading {resource_url}")
        download_resource(resource_url, local_path)


def main():
    parser = argparse.ArgumentParser(
        description=(
            "Download resources referenced by Project Euler minimal HTML files."
        ),
        epilog=(
            "Examples:\n"
            "  download_resources.py data/minimal/42.html\n"
            "  download_resources.py data/minimal/84.html data/minimal/128.html\n"
            "  download_resources.py data/minimal/*.html"
        ),
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument(
        "minimal_html",
        nargs="+",
        metavar="HTML",
        help="One or more minimal HTML files to scan for resources.",
    )
    args = parser.parse_args()

    for minimal_path in args.minimal_html:
        if not minimal_path.endswith(".html"):
            raise SystemExit(f"Expected a .html file, got: {minimal_path}")
        process_minimal_file(minimal_path)


if __name__ == "__main__":
    main()
