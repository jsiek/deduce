#!/bin/bash
# Download BeeWare's prebuilt Python for iOS into ipad/Support/.
# Pinned by release tag and SHA-256; re-running is a no-op once present.
set -euo pipefail

TAG="3.13-b15"
ASSET="Python-3.13-iOS-support.b15.tar.gz"
SHA256="80175765a31babe43b0910395cf86ba4e8412adf1902b069d55b74d523ecc5d1"
URL="https://github.com/beeware/Python-Apple-support/releases/download/${TAG}/${ASSET}"

SUPPORT="$(cd "$(dirname "$0")/.." && pwd)/Support"
if [ -d "${SUPPORT}/Python.xcframework" ]; then
  echo "Python.xcframework already present in ${SUPPORT}"
  exit 0
fi

mkdir -p "${SUPPORT}"
curl --fail --location --silent --show-error --output "${SUPPORT}/${ASSET}" "${URL}"
echo "${SHA256}  ${SUPPORT}/${ASSET}" | shasum -a 256 --check
tar -xzf "${SUPPORT}/${ASSET}" -C "${SUPPORT}"
rm "${SUPPORT}/${ASSET}"
echo "Installed $(ls "${SUPPORT}")"
