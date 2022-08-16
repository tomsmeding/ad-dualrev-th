#!/usr/bin/env bash
set -euo pipefail
if [[ $# -ne 1 ]]; then
  echo >&2 "Usage: $0 <destdir>"
  exit 1
fi

destdir=$1
if [[ -e "$destdir" && ( ! -d "$destdir" || -n $(find "$destdir" -mindepth 1 -print -quit) ) ]]; then
  echo >&2 "Destination directory not empty"
  exit 1
fi
if [[ ! -e "$destdir" ]]; then
  mkdir -p "$destdir"
fi

docindexfile=$(cabal haddock ad-dualrev-th --haddock-hyperlink-source | tee /dev/stderr | tail -1)
docdir=$(dirname "$docindexfile")
cp -r "$docdir" "$destdir"
haddock-to-standalone "$destdir"
