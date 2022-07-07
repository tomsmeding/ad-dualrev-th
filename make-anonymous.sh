#!/usr/bin/env bash
set -euo pipefail
if [[ $# -ne 1 ]]; then
  echo >&2 "Usage: $0 <destination dir>"
  exit 1
fi
srcdir="$(dirname "$0")"
destdir="$1"

if [[ -n "$(find "$destdir" -mindepth 1 -print -quit)" ]]; then
  echo >&2 "Destination directory not empty"
  exit 1
fi

declare -A excluded
excluded[README.md]=1
excluded[hie.yaml]=1
excluded[make-anonymous.sh]=1

git ls-files | while read -r f; do
  if [[ "${excluded[$f]+a}" = a ]]; then
    echo "Skipped: <$f>"
    continue
  fi
  if [[ -n "$(tr -Cd / <<<"$f")" ]]; then
    mkdir -vp "$destdir/$(dirname "$f")"
  fi
  cp -v "$srcdir/$f" "$destdir/$f"
done

echo -----
echo Patching ad-dualrev-th.cabal ...

sed -n -i -f /dev/stdin "$destdir/ad-dualrev-th.cabal" <<EOF
: start
/^description:/ b block
/^extra-source-files:/ b block
/^source-repository / b block
/^homepage:/ d
/^author:/ d
/^maintainer:/ d
/^copyright:/ d
p
d
: block
n
/^\s/ b block
b start
EOF

echo Patching LICENSE ...

sed -i 's/Tom Smeding/Authors/' "$destdir/LICENSE"

echo -----

ok=1
set +e
grep -i smeding -r "$destdir" || ok=0
grep -i matthijs -r "$destdir" || ok=0
grep -i 11368 -r "$destdir" || ok=0  # The arxiv ID
set -e

if [[ ok = 0 ]]; then
  echo >&2 "Not anonymous!"
  exit 1
fi
