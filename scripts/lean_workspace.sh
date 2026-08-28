#!/usr/bin/env bash
# Resolve (or build) the Lake project a contribution is elaborated against and print
# its path on stdout. Everything else goes to stderr, so a caller can do
#     WORKSPACE="$(scripts/lean_workspace.sh "$commit")"
#
# Order of preference:
#   1. $CONTRIB_LEAN_WORKSPACE  — a workspace the runner already maintains.
#   2. $CONTRIB_LEAN_BOOTSTRAP=true — clone Formal Conjectures at the commit the pool
#      pins and build it, cached per commit under $CONTRIB_LEAN_CACHE.
#   3. fail with instructions rather than silently skipping the stage.
set -euo pipefail

commit="${1:?usage: lean_workspace.sh <formal-conjectures-commit>}"
cache="${CONTRIB_LEAN_CACHE:-${RUNNER_TOOL_CACHE:-$HOME/.cache}/formal-conjectures}"
repository="${CONTRIB_LEAN_REPO:-https://github.com/google-deepmind/formal-conjectures.git}"

log() { printf '%s\n' "$*" >&2; }

if [[ -n "${CONTRIB_LEAN_WORKSPACE:-}" ]]; then
  if [[ ! -d "$CONTRIB_LEAN_WORKSPACE" ]]; then
    log "CONTRIB_LEAN_WORKSPACE=$CONTRIB_LEAN_WORKSPACE does not exist on this runner"
    exit 1
  fi
  log "using the runner's prepared workspace"
  printf '%s\n' "$CONTRIB_LEAN_WORKSPACE"
  exit 0
fi

if [[ "${CONTRIB_LEAN_BOOTSTRAP:-false}" != "true" ]]; then
  log "No Lean workspace configured."
  log "Set the repository variable CONTRIB_LEAN_WORKSPACE to a prebuilt Lake project on the"
  log "DEV runner, or set CONTRIB_LEAN_BOOTSTRAP=true to let CI clone and build Formal"
  log "Conjectures itself (slow on a cold cache, then cached per commit)."
  exit 1
fi

# elan installs whatever toolchain the project's lean-toolchain file names.
export PATH="$HOME/.elan/bin:$PATH"
command -v elan >/dev/null || { log "elan is not installed on this runner"; exit 1; }

workspace="$cache/$commit"
if [[ -f "$workspace/.contrib-ready" ]]; then
  log "reusing cached workspace $workspace"
  printf '%s\n' "$workspace"
  exit 0
fi

log "building a workspace for formal-conjectures@$commit (slow the first time)"
rm -rf "$workspace"
mkdir -p "$(dirname "$workspace")"
git init -q "$workspace"
git -C "$workspace" remote add origin "$repository"
git -C "$workspace" fetch -q --depth 1 origin "$commit"
git -C "$workspace" checkout -q FETCH_HEAD

(
  cd "$workspace"
  lake exe cache get >&2 || log "mathlib cache unavailable; falling back to a full build"
  lake build >&2
)
touch "$workspace/.contrib-ready"
printf '%s\n' "$workspace"
