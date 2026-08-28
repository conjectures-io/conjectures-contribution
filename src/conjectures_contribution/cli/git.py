from __future__ import annotations

import subprocess
from pathlib import Path

from ..model import Change, ChangeKind


class GitError(RuntimeError):
    pass


_KINDS = {
    "A": ChangeKind.ADDED,
    "M": ChangeKind.MODIFIED,
    "T": ChangeKind.MODIFIED,
    "D": ChangeKind.DELETED,
}


def _run(argv: list[str], cwd: Path) -> str:
    try:
        result = subprocess.run(  # noqa: S603 - argv is literal; git resolves on PATH
            argv, cwd=cwd, capture_output=True, text=True, check=False
        )
    except FileNotFoundError:
        raise GitError(f"{argv[0]}: not installed") from None
    if result.returncode != 0:
        raise GitError(result.stderr.strip() or f"{' '.join(argv)} failed")
    return result.stdout


def run(root: Path, *args: str) -> str:
    return _run(["git", *args], cwd=root)


def gh(root: Path, *args: str) -> str:
    return _run(["gh", *args], cwd=root)


# Diffing the *merge base* against the working tree, rather than the base ref itself,
# is what makes one function serve both callers. Locally the merge base of HEAD with
# HEAD is HEAD, so uncommitted work still shows. In CI, anything that landed on the
# base branch after the contribution branched is excluded — diffing the base ref
# directly would report those files reversed and trip C011 and C012 on paths the
# contributor never touched.


def require_gh(root: Path) -> None:
    try:
        gh(root, "--version")
    except GitError as exc:
        raise GitError(
            "GitHub CLI (gh) is required to create a pull request; "
            "install it or submit with --no-pr"
        ) from exc
    try:
        gh(root, "auth", "status")
    except GitError as exc:
        raise GitError(
            "GitHub CLI is not authenticated; run `gh auth login` or submit with --no-pr"
        ) from exc


# Untracked files are the normal state of a freshly promoted contribution, so a diff
# alone would report an empty change set and pass C011 vacuously. Renames are split
# into a delete and an add so C012 sees the removal.
def merge_base(root: Path, base: str) -> str:
    try:
        return run(root, "merge-base", base, "HEAD").strip() or base
    except GitError:
        return base


def changes(root: Path, base: str) -> tuple[Change, ...]:
    collected: set[Change] = set()
    for line in run(
        root, "diff", "--name-status", "--no-renames", merge_base(root, base)
    ).splitlines():
        status, _, name = line.partition("\t")
        kind = _KINDS.get(status[:1])
        if kind is not None and name:
            collected.add(Change((root / name).resolve(), kind))
    for name in run(root, "ls-files", "--others", "--exclude-standard").splitlines():
        if name:
            collected.add(Change((root / name).resolve(), ChangeKind.ADDED))
    return tuple(sorted(collected))


def is_clean(root: Path) -> bool:
    return not run(root, "status", "--porcelain").strip()


def current_branch(root: Path) -> str:
    return run(root, "rev-parse", "--abbrev-ref", "HEAD").strip()


def revision(root: Path, name: str) -> str:
    return run(root, "rev-parse", name).strip()


def submission_changes(root: Path) -> tuple[tuple[str, ...], tuple[str, ...], tuple[str, ...]]:
    def paths(*args: str) -> tuple[str, ...]:
        return tuple(path for path in run(root, *args).split("\0") if path)

    staged = paths("diff", "--cached", "--name-only", "-z")
    unstaged = paths("diff", "--name-only", "-z")
    untracked = paths("ls-files", "--others", "--exclude-standard", "-z")
    return staged, unstaged, untracked
