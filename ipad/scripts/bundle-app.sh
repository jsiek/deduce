#!/bin/bash
# Xcode "Bundle Deduce" build phase. Copies the checker, the stdlib (with
# its .thm files), the samples and the vendored packages into the app,
# then runs BeeWare's install_python to add Python's own standard library.
set -euo pipefail

REPO="${PROJECT_DIR}/.."
APP="${CODESIGNING_FOLDER_PATH}/app"

if ! ls "${REPO}"/lib/*.thm > /dev/null 2>&1 || [ ! -d "${PROJECT_DIR}/build/app_packages" ]; then
  echo "error: run ipad/scripts/prepare.sh first" >&2
  exit 1
fi

mkdir -p "${APP}/lib" "${APP}/samples"
rsync -a --delete --exclude __pycache__ "${REPO}/abstract_syntax" "${REPO}/lsp" "${APP}/"
rsync -a "${REPO}"/*.py "${REPO}/Deduce.lark" "${PROJECT_DIR}/python/" "${APP}/"
rsync -a --delete --include '*.pf' --include '*.thm' --exclude '*' "${REPO}/lib/" "${APP}/lib/"
# A .thm older than its .pf makes the checker re-prove that module.
touch "${APP}"/lib/*.thm
rsync -a --delete "${PROJECT_DIR}/samples/" "${REPO}/examples/reverse_involutive.pf" "${APP}/samples/"
rsync -a --delete "${PROJECT_DIR}/build/app_packages/" "${CODESIGNING_FOLDER_PATH}/app_packages/"

source "${PROJECT_DIR}/Support/Python.xcframework/build/utils.sh"
install_python Support/Python.xcframework app app_packages
