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

[[ "$commit" =~ ^[0-9a-f]{40}$ ]] || { log "expected a full 40-character commit SHA"; exit 1; }

validate_workspace() {
  local candidate actual dirty
  candidate="$(realpath "$1")"
  git -C "$candidate" rev-parse --is-inside-work-tree >/dev/null 2>&1 || {
    log "$candidate is not a git worktree"
    return 1
  }
  actual="$(git -C "$candidate" rev-parse HEAD)"
  if [[ "$actual" != "$commit" ]]; then
    log "$candidate is at $actual, but the pool pins $commit"
    return 1
  fi
  dirty="$(git -C "$candidate" status --porcelain --untracked-files=all)"
  if [[ -n "$dirty" ]]; then
    log "$candidate has tracked or untracked source changes"
    return 1
  fi
  printf '%s\n' "$candidate"
}

if [[ -n "${CONTRIB_LEAN_WORKSPACE:-}" ]]; then
  if [[ ! -d "$CONTRIB_LEAN_WORKSPACE" ]]; then
    log "CONTRIB_LEAN_WORKSPACE=$CONTRIB_LEAN_WORKSPACE does not exist on this runner"
    exit 1
  fi
  log "checking the runner's prepared workspace"
  validate_workspace "$CONTRIB_LEAN_WORKSPACE"
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
ready="$workspace/.git/contrib-ready"
if [[ -f "$ready" ]]; then
  log "reusing cached workspace $workspace"
  validate_workspace "$workspace"
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
validate_workspace "$workspace" >/dev/null
touch "$ready"
printf '%s\n' "$workspace"
