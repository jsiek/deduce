#!/bin/bash
# Xcode "Bundle Deduce" build phase. Copies the checker, the stdlib (with
# its .thm files), the samples and the vendored packages into the app,
# then runs BeeWare's install_python to add Python's own standard library.
set -euo pipefail

REPO="${PROJECT_DIR}/.."
APP="${CODESIGNING_FOLDER_PATH}/app"

if [ ! -d "${PROJECT_DIR}/build/app_packages" ]; then
  echo "error: run ipad/scripts/prepare.sh first" >&2
  exit 1
fi
# The app skips re-proving a stdlib module only when its .thm is at least
# as new as its .pf, and it cannot write a fresh .thm into its read-only
# bundle, so a missing or stale .thm must be regenerated here on the Mac.
for pf in "${REPO}"/lib/*.pf; do
  thm="${pf%.pf}.thm"
  if [ ! -e "${thm}" ] || [ "${thm}" -ot "${pf}" ]; then
    echo "error: ${thm} is missing or older than its .pf; run ipad/scripts/prepare.sh" >&2
    exit 1
  fi
done

mkdir -p "${APP}/lib" "${APP}/samples" "${APP}/exercises"
rsync -a --delete "${PROJECT_DIR}/exercises/" "${APP}/exercises/"
rsync -a --delete --exclude __pycache__ "${REPO}/abstract_syntax" "${REPO}/lsp" "${APP}/"
rsync -a "${REPO}"/*.py "${REPO}/Deduce.lark" "${PROJECT_DIR}/python/" "${APP}/"
# -a preserves modification times, so each .thm stays at least as new as its .pf.
rsync -a --delete --include '*.pf' --include '*.thm' --exclude '*' "${REPO}/lib/" "${APP}/lib/"
rsync -a --delete "${PROJECT_DIR}/samples/" "${REPO}/examples/reverse_involutive.pf" "${APP}/samples/"
rsync -a --delete "${PROJECT_DIR}/build/app_packages/" "${CODESIGNING_FOLDER_PATH}/app_packages/"

source "${PROJECT_DIR}/Support/Python.xcframework/build/utils.sh"
install_python Support/Python.xcframework app app_packages
