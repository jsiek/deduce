#!/bin/bash
# One-time setup before building the app in Xcode:
#   1. BeeWare's Python.xcframework  -> ipad/Support/
#   2. pinned pure-Python packages   -> ipad/build/app_packages/
#   3. lib/*.thm, so the app never re-proves (or writes into) the bundled stdlib
set -euo pipefail

IPAD="$(cd "$(dirname "$0")/.." && pwd)"
REPO="$(cd "${IPAD}/.." && pwd)"

bash "${IPAD}/scripts/fetch-python.sh"

rm -rf "${IPAD}/build/app_packages"
python3.13 -m pip install --quiet --no-deps --only-binary=:all: \
  --target "${IPAD}/build/app_packages" \
  lark==1.2.2 pygls==2.1.1 lsprotocol==2025.0.0 \
  cattrs==26.1.0 attrs==25.4.0 typing_extensions==4.14.1

(cd "${REPO}" && python3.13 deduce.py ./lib --dir ./lib --quiet)
echo "Ready: open ipad/Deduce.xcodeproj"
