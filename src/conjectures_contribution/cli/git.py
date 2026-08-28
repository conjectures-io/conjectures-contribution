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


# Untracked files are the normal state of a freshly promoted contribution, so a diff
# against the base alone would report an empty change set and pass C011 vacuously.
# Renames are split into a delete and an add so C012 sees the removal.
def changes(root: Path, base: str) -> tuple[Change, ...]:
    collected: set[Change] = set()
    for line in run(root, "diff", "--name-status", "--no-renames", base).splitlines():
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
