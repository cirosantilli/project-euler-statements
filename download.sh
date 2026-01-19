#!/usr/bin/env bash
set -eux
mkdir -p data
mkdir -p data/minimal
mkdir -p data/problem
i="$(("$(ls -rv data/problem/ | head -n1 | sed 's/.html//')" + 1))"
# minimal= is always 200 with error "Data for that problem cannot be found" when problem not present.
# problem= redirects
while [ "$(curl -o /dev/null --silent --head --write-out '%{http_code}' "https://projecteuler.net/problem=$i")" = 200 ]; do
  echo "$i"
  wget -O "data/minimal/$i.html" "https://projecteuler.net/minimal=$i"
  wget -O "data/problem/$i.html" "https://projecteuler.net/problem=$i"
  ./download_resources.py "data/minimal/$i.html"
  i="$((i + 1))"
done
