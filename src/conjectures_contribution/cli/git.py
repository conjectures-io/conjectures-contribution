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


def require_gh(root: Path) -> None:
    try:
        gh(root, "--version")
    except GitError as exc:
        raise GitError(
            "GitHub CLI (gh) is required to create a pull request. "
            "Install it from https://github.com/cli/cli, or submit with --no-pr"
        ) from exc
    try:
        gh(root, "auth", "status")
    except GitError as exc:
        raise GitError(
            "GitHub CLI is not authenticated; run `gh auth login` "
            "(https://github.com/cli/cli) or submit with --no-pr"
        ) from exc


def prepare_fork(
    root: Path,
    repository: str,
    repository_url: str,
    upstream_remote: str,
    fork_remote: str,
) -> tuple[str, str]:
    # Give gh a canonical github.com remote. This avoids SSH aliases that Git understands
    # but gh cannot associate with an authenticated GitHub host.
    try:
        existing = run(root, "remote", "get-url", upstream_remote).strip()
    except GitError:
        run(root, "remote", "add", upstream_remote, repository_url)
    else:
        if existing != repository_url:
            raise GitError(
                f"git remote {upstream_remote!r} points to {existing!r}, "
                f"expected {repository_url!r}"
            )
    # set-default takes a repository in OWNER/REPO form, not the name of a git remote:
    # passing the remote name fails with `expected the "[HOST/]OWNER/REPO" format`.
    gh(root, "repo", "set-default", repository)
    gh(root, "repo", "fork", "--remote", "--remote-name", fork_remote)
    owner = gh(root, "api", "user", "--jq", ".login").strip()
    if not owner:
        raise GitError("GitHub CLI did not return the authenticated account name")
    repository_name = repository.partition("/")[2]
    expected = f"/{owner}/{repository_name}".lower()
    for name in run(root, "remote").splitlines():
        url = run(root, "remote", "get-url", name).strip().removesuffix("/").removesuffix(".git")
        if url.replace(":", "/").lower().endswith(expected):
            return owner, name
    raise GitError("GitHub CLI created the fork but did not configure a Git remote for it")


# Diffing the merge base against the working tree excludes changes that landed on the
# base branch after a contribution branched. Untracked files are included because they
# are the normal state of a freshly promoted contribution; renames are split so C012
# sees the removal.
def merge_base(root: Path, base: str) -> str:
    try:
        return run(root, "merge-base", base, "HEAD").strip() or base
    except GitError:
        return base


def _require_commit(root: Path, revision: str) -> None:
    try:
        run(root, "rev-parse", "--verify", "--quiet", f"{revision}^{{commit}}")
    except GitError:
        raise GitError(
            f"base revision {revision} is not in this repository; "
            "fetch the base branch before checking a change set"
        ) from None


def changes(root: Path, base: str) -> tuple[Change, ...]:
    _require_commit(root, base)
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


def update_main(root: Path, repository_url: str) -> None:
    run(root, "fetch", "--recurse-submodules=on-demand", repository_url, "main")
    run(root, "merge", "--ff-only", "FETCH_HEAD")
    if revision(root, "HEAD") != revision(root, "FETCH_HEAD"):
        raise GitError(
            "local main contains commits not in canonical main; reconcile it before submitting"
        )
    # A superproject checkout updates only the recorded gitlink by default. Explicitly
    # update the worktree so validation reads the exact allowlist pinned by fetched main.
    run(root, "submodule", "update", "--init", "--recursive")


def submission_changes(root: Path) -> tuple[tuple[str, ...], tuple[str, ...], tuple[str, ...]]:
    def paths(*args: str) -> tuple[str, ...]:
        return tuple(path for path in run(root, *args).split("\0") if path)

    staged = paths("diff", "--cached", "--name-only", "-z")
    unstaged = paths("diff", "--name-only", "-z")
    untracked = paths("ls-files", "--others", "--exclude-standard", "-z")
    return staged, unstaged, untracked
