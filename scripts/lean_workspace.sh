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
# Audited pool commits are reconstructed locally, not published upstream. These
# inputs mirror the validator's source pin; the patch comes from the trusted pool.
source_root="$(cd "$(dirname "$0")/.." && pwd)"
pin_fields="$(python3 - "$source_root/lean-source.json" "$commit" <<'PY'
import json
import re
import sys

with open(sys.argv[1], encoding="utf-8") as stream:
    pin = json.load(stream)
if pin["commit"] == sys.argv[2]:
    assert re.fullmatch(r"[0-9a-f]{40}", pin["base_commit"])
    assert re.fullmatch(r"[0-9a-f]{64}", pin["patch_sha256"])
    print(pin["base_commit"])
    print(pin["patch_sha256"])
else:
    print(sys.argv[2])
    print("-")
PY
)"
mapfile -t source_pin <<< "$pin_fields"
base_commit="${source_pin[0]}"
patch_sha256="${source_pin[1]}"
git -C "$workspace" fetch -q --depth 1 origin "$base_commit"
git -C "$workspace" checkout -q FETCH_HEAD
if [[ "$patch_sha256" != "-" ]]; then
  patch="$source_root/conjectures/tiers/tier-1/formal-conjectures-audit-fixes.patch"
  actual_patch_sha256="$(sha256sum "$patch" | cut -d ' ' -f 1)"
  [[ "$actual_patch_sha256" == "$patch_sha256" ]] || {
    log "audit patch checksum does not match lean-source.json"
    exit 1
  }
  git -C "$workspace" apply --index "$patch"
  source_tree="$(git -C "$workspace" write-tree)"
  derived_commit="$(
    printf '%s\n' 'fix(ErdosProblems): correct audited candidate statements' |
      GIT_AUTHOR_NAME='Conjectures Pool Builder' \
      GIT_AUTHOR_EMAIL='pool@conjectures.io' \
      GIT_AUTHOR_DATE='2026-08-03T00:00:00Z' \
      GIT_COMMITTER_NAME='Conjectures Pool Builder' \
      GIT_COMMITTER_EMAIL='pool@conjectures.io' \
      GIT_COMMITTER_DATE='2026-08-03T00:00:00Z' \
      git -C "$workspace" commit-tree "$source_tree" -p "$base_commit"
  )"
  [[ "$derived_commit" == "$commit" ]] || {
    log "audit patch produced $derived_commit, but the pool pins $commit; refusing to build"
    exit 1
  }
  git -C "$workspace" checkout -q --detach "$derived_commit"
fi
validate_workspace "$workspace" >/dev/null

(
  cd "$workspace"
  lake exe cache get >&2 || log "mathlib cache unavailable; falling back to a full build"
  lake build >&2
)
validate_workspace "$workspace" >/dev/null
touch "$ready"
prune_superseded "$commit"
printf '%s\n' "$workspace"
