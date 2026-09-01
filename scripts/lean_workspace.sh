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

# A repository variable set through the web UI keeps whatever whitespace was pasted with it,
# and the value is never shown back with its bounds. CONTRIB_LEAN_BOOTSTRAP="true\n" reads as
# "true" everywhere a human looks and matches nothing here, so the stage reported that no
# workspace was configured while the variable sat there apparently set.
trim() {
  local value="$1"
  value="${value#"${value%%[![:space:]]*}"}"
  printf '%s' "${value%"${value##*[![:space:]]}"}"
}

commit="$(trim "${1:?usage: lean_workspace.sh <formal-conjectures-commit>}")"
workspace_setting="$(trim "${CONTRIB_LEAN_WORKSPACE:-}")"
bootstrap="$(trim "${CONTRIB_LEAN_BOOTSTRAP:-false}")"
cache="$(trim "${CONTRIB_LEAN_CACHE:-}")"
cache="${cache:-${RUNNER_TOOL_CACHE:-$HOME/.cache}/formal-conjectures}"
repository="$(trim "${CONTRIB_LEAN_REPO:-}")"
repository="${repository:-https://github.com/google-deepmind/formal-conjectures.git}"

log() { printf '%s\n' "$*" >&2; }

[[ "$commit" =~ ^[0-9a-f]{40}$ ]] || { log "expected a full 40-character commit SHA"; exit 1; }

# Each cached workspace is ~13GB and nothing else removes them, so a bumped pool commit used
# to leave the previous one on the runner forever. Prune from here rather than from a workflow
# or a timer: this is the only thing that knows which commit is current, and it owns $cache.
prune_superseded() {
  local keep="$1" old
  for old in "$cache"/*/; do
    [[ -d "$old" ]] || continue
    [[ "$(basename "$old")" != "$keep" ]] || continue
    log "removing superseded workspace $(basename "$old")"
    rm -rf "$old"
  done
}

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

if [[ -n "$workspace_setting" ]]; then
  if [[ ! -d "$workspace_setting" ]]; then
    log "CONTRIB_LEAN_WORKSPACE=$workspace_setting does not exist on this runner"
    exit 1
  fi
  log "checking the runner's prepared workspace"
  validate_workspace "$workspace_setting"
  exit 0
fi

if [[ "$bootstrap" != "true" ]]; then
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
  prune_superseded "$commit"
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
prune_superseded "$commit"
printf '%s\n' "$workspace"
