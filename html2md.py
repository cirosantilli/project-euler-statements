#!/usr/bin/env python

import re
import os
from os import path
from html.parser import HTMLParser

from markdownify import markdownify

markdownify('<b>Yay</b> <a href="http://github.com">GitHub</a>')


class HTMLTitle(HTMLParser):
    is_title = False
    title = None

    def handle_data(self, data):
        if self.is_title:
            self.title = data
            self.is_title = False

    def handle_starttag(self, tag, attrs):
        if tag.lower() == "title":
            self.is_title = True


class HTMLText(HTMLParser):
    text = ""

    def handle_data(self, data):
        self.text += data


problem_dir = path.join("data", "problem")
minimal_dir = path.join("data", "minimal")
md_dir = path.join("data", "md")
os.makedirs(md_dir, exist_ok=True)
for bname in sorted(os.listdir(problem_dir), key=lambda s: int(s.split(".")[0])):
    bname_noext = path.splitext(bname)[0]
    with open(path.join(problem_dir, bname), "r") as problem_f:
        with open(path.join(minimal_dir, bname), "r") as minimal_f:
            f = HTMLTitle()
            f.feed(problem_f.read())
            with open(path.join(md_dir, f"{bname_noext}.md"), "w") as md_f:
                md_f.write(
                    f'# {re.sub(r' - Project Euler$', '', re.sub(r'^#\d+ ', '', f.title))}'
                    + "\n\n"
                    + markdownify(minimal_f.read())
                )
