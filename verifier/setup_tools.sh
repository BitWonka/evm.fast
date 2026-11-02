#!/usr/bin/env bash
# Build the verification tools next to the project: comparator, lean4export, nanoda and (on Linux) landrun.
#
#   verifier/setup_tools.sh          # builds into verifier/.tools/ and runs comparator's test suite
#
# Policy: the judge must be compiled with the project's exact Lean release, because it replays the
# export through the kernel it was compiled with and lean4export reads the project's .olean files.
# We therefore pin the comparator revision whose declared toolchain has the SAME MINOR VERSION as
# ours and override only the patch digit. A hash-pinned patch spools exports to files and replays
# deferred declarations in parallel across stock Lean kernel environments; comparison, axiom
# checks, primitives, and full kernel replay remain unchanged. Different minor versions and changes
# to those checks are refused here on purpose.
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
tools="${root}/verifier/.tools"
export PATH="${HOME}/.elan/bin:${PATH}"

# leanprover/comparator @ 2026-08-10 (merge of PR #70): declared toolchain v4.33.0, the last
# revision before the v4.34.0-rc1 bump. Its own manifest pins the matching lean4export.
readonly comparator_rev="c0c5a52d2aff92b457c3e5ed4a68c1ebc5795809"
readonly comparator_spool_sha256="880369b34e19efbc9dc2f35409dbde82cfdade00a3b3a70edc7ea9e9ab39f715"
# Zouuup/landrun (Linux only)
readonly landrun_rev="811cfff51ceaf3d9843708aa6d22e9b84ccac8b4"
# ammkrn/nanoda_lib (independent Lean kernel)
readonly nanoda_rev="998e0a84e4c1572ca279ff05007af6ec6639405a"

minor() { sed -E 's/^leanprover\/lean4:v([0-9]+\.[0-9]+)\..*$/\1/' "$1"; }

if ! command -v elan >/dev/null 2>&1; then
  echo "elan is required; install and verify it before bootstrapping the pinned verification tools" >&2
  exit 1
fi

clone_at() {  # url rev dest
  if [[ ! -d "$3/.git" ]]; then
    git clone --filter=blob:none --no-checkout "$1" "$3"
  fi
  git -C "$3" fetch --depth=1 origin "$2"
  git -C "$3" checkout --detach --force "$2"
  # Old untracked source files must not become inputs to the pinned build. Ignored build
  # caches remain, and Lake checks their source hashes before reusing them.
  git -C "$3" clean -ffd
  [[ "$(git -C "$3" rev-parse HEAD)" == "$2" ]]
  [[ -z "$(git -C "$3" status --porcelain --untracked-files=no)" ]] || { echo "dirty checkout: $3" >&2; exit 1; }
}

mkdir -p "${tools}"
clone_at https://github.com/leanprover/comparator.git "${comparator_rev}" "${tools}/comparator"

ours="$(minor "${root}/lean-toolchain")"
theirs="$(minor "${tools}/comparator/lean-toolchain")"
if [[ "${ours}" != "${theirs}" ]]; then
  echo "refusing: project toolchain minor ${ours} differs from comparator's declared ${theirs}" >&2
  exit 1
fi
echo "comparator declares $(cat "${tools}/comparator/lean-toolchain"); building with $(cat "${root}/lean-toolchain")"
cp "${root}/lean-toolchain" "${tools}/comparator/lean-toolchain"
# Avoid retaining tens of gigabytes of exporter stdout before parsing, and replay
# deferred declarations in parallel across stock Lean kernel environments. The patch
# uses secure temporary handles and the existing stream parser, and preserves
# comparison, both axiom closures, primitive checks and full kernel replay.
spool_patch="${root}/verifier/patches/comparator-file-spool.patch"
[[ "$(sha256sum "${spool_patch}" | cut -d ' ' -f 1)" == "${comparator_spool_sha256}" ]] || {
  echo "refusing: comparator patch hash changed" >&2; exit 1;
}
git -C "${tools}/comparator" apply --check "${spool_patch}"
git -C "${tools}/comparator" apply "${spool_patch}"
( cd "${tools}/comparator" && lake build lean4export comparator )

lean4export_bin="${tools}/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export"
comparator_bin="${tools}/comparator/.lake/build/bin/comparator"
[[ -x "${lean4export_bin}" && -x "${comparator_bin}" ]]

command -v cargo >/dev/null 2>&1 || { echo "Cargo is required to build nanoda" >&2; exit 1; }
clone_at https://github.com/ammkrn/nanoda_lib.git "${nanoda_rev}" "${tools}/nanoda_lib"
( cd "${tools}/nanoda_lib" && cargo build --release --bin nanoda_bin )
nanoda_bin="${tools}/nanoda_lib/target/release/nanoda_bin"
[[ -x "${nanoda_bin}" ]]

if [[ "$(uname -s)" == Linux ]]; then
  command -v go >/dev/null 2>&1 || { echo "Go 1.24+ is required to build landrun" >&2; exit 1; }
  clone_at https://github.com/Zouuup/landrun.git "${landrun_rev}" "${tools}/landrun"
  ( cd "${tools}/landrun" && go build -trimpath -o landrun ./cmd/landrun )
  landrun_bin="${tools}/landrun/landrun"
else
  echo "non-Linux host: landrun not built; local runs use comparator's fake-landrun shim (NOT a sandbox)" >&2
  landrun_bin="${tools}/comparator/scripts/fake-landrun.sh"
fi

# Acceptance: comparator's own test suite must pass on this toolchain.
echo "running comparator's test suite"
( cd "${tools}/comparator" && \
  COMPARATOR_LANDRUN="${landrun_bin}" COMPARATOR_LEAN4EXPORT="${lean4export_bin}" lean --run runtests.lean )

cat > "${tools}/env.sh" <<ENV
export COMPARATOR_BIN="${comparator_bin}"
export COMPARATOR_LEAN4EXPORT="${lean4export_bin}"
export COMPARATOR_LANDRUN="${landrun_bin}"
export COMPARATOR_NANODA="${nanoda_bin}"
ENV
echo "tools ready; source ${tools}/env.sh"
echo "  lean4export rev: $(python3 -c "import json;print([p['rev'] for p in json.load(open('${tools}/comparator/lake-manifest.json'))['packages'] if p['name']=='lean4export'][0])")"
