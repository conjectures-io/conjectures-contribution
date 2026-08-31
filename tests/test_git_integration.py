from __future__ import annotations

import shutil
import subprocess
from pathlib import Path

import pytest
from typer.testing import CliRunner

from conjectures_contribution.checks import ChangeKind
from conjectures_contribution.cli import git as git_cmd
from conjectures_contribution.cli import submit as submit_cmd
from conjectures_contribution.cli.git import (
    GitError,
    changes,
    prepare_fork,
    require_gh,
    update_main,
)
from conjectures_contribution.cli.main import app

from .conftest import Repo, make_repo, plain

pytestmark = pytest.mark.skipif(shutil.which("git") is None, reason="git is not installed")
runner = CliRunner()
GIT = shutil.which("git") or "git"


def _git(root: Path, *args: str) -> None:
    subprocess.run(["git", *args], cwd=root, check=True, capture_output=True)  # noqa: S603, S607


def _git_output(root: Path, *args: str) -> str:
    return subprocess.run(  # noqa: S603
        [GIT, *args], cwd=root, check=True, capture_output=True, text=True
    ).stdout.strip()


@pytest.fixture
def git_repo(tmp_path: Path) -> Repo:
    repo = make_repo(tmp_path)
    repo.contributions.mkdir(parents=True, exist_ok=True)
    (repo.contributions / "demo-1").mkdir()
    (repo.contributions / "demo-1" / "index.md").write_text("# demo-1\n", encoding="utf-8")
    # drafts/ is gitignored in the real repository; without that the scratch area
    # shows up in every change set as untracked additions.
    (tmp_path / ".gitignore").write_text("drafts/\n", encoding="utf-8")
    _git(tmp_path, "init", "--quiet", "--initial-branch", "master")
    _git(tmp_path, "config", "user.email", "test@example.invalid")
    _git(tmp_path, "config", "user.name", "Test")
    _git(tmp_path, "add", ".")
    _git(tmp_path, "commit", "--quiet", "--message", "baseline")
    return repo


@pytest.fixture
def submission_repo(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> tuple[Repo, Path, Path]:
    root = tmp_path / "work"
    root.mkdir()
    repo = make_repo(root)
    repo.contributions.mkdir(parents=True, exist_ok=True)
    repo.drafts.mkdir(parents=True, exist_ok=True)
    (repo.drafts / ".gitignore").write_text("*\n!.gitignore\n", encoding="utf-8")
    _git(root, "init", "--quiet", "--initial-branch", "main")
    _git(root, "config", "user.email", "test@example.invalid")
    _git(root, "config", "user.name", "Test")
    _git(root, "add", ".")
    _git(root, "commit", "--quiet", "--message", "baseline")

    remote = tmp_path / "origin.git"
    _git(tmp_path, "init", "--quiet", "--bare", str(remote))
    _git(root, "remote", "add", "origin", str(remote))
    _git(root, "remote", "add", submit_cmd.FORK_REMOTE, str(remote))
    _git(root, "push", "--quiet", "--set-upstream", "origin", "main")
    monkeypatch.setattr(submit_cmd, "UPSTREAM_URL", str(remote))
    return repo, repo.promote(), remote


def test_untracked_promotion_reports_as_added(git_repo: Repo) -> None:
    published = git_repo.promote()
    reported = changes(git_repo.root, "HEAD")
    assert {c.kind for c in reported} == {ChangeKind.ADDED}
    assert (published / "metadata.json").resolve() in {c.path for c in reported}


def test_modification_and_deletion_are_distinguished(git_repo: Repo) -> None:
    published = git_repo.promote()
    _git(git_repo.root, "add", ".")
    _git(git_repo.root, "commit", "--quiet", "--message", "contribution")

    (published / "sources.md").write_text("# Sources\ntampered\n", encoding="utf-8")
    (published / "metadata.json").unlink()
    by_path = {c.path: c.kind for c in changes(git_repo.root, "HEAD")}
    assert by_path[(published / "sources.md").resolve()] is ChangeKind.MODIFIED
    assert by_path[(published / "metadata.json").resolve()] is ChangeKind.DELETED


def test_deletion_only_changeset_is_caught(git_repo: Repo) -> None:
    published = git_repo.promote()
    _git(git_repo.root, "add", ".")
    _git(git_repo.root, "commit", "--quiet", "--message", "contribution")

    shutil.rmtree(published)
    reported = changes(git_repo.root, "HEAD")
    assert {c.kind for c in reported} == {ChangeKind.DELETED}
    # One finding per removed path, and C011 stays quiet: the paths are structurally
    # inside a contribution, so the removal is C012's to report.
    assert set(git_repo.changeset_errors(*reported)) == {"C012"}
    assert len(git_repo.changeset_errors(*reported)) == len(reported)


def test_changes_landing_on_the_base_branch_are_not_attributed_to_the_branch(
    git_repo: Repo,
) -> None:
    # A contribution branch that is behind main must not be blamed for main's commits.
    _git(git_repo.root, "switch", "--create", "contribution/demo", "--quiet")
    published = git_repo.promote()
    _git(git_repo.root, "add", ".")
    _git(git_repo.root, "commit", "--quiet", "--message", "contribution")

    _git(git_repo.root, "switch", "--quiet", "master")
    (git_repo.root / "README.md").write_text("moved on\n", encoding="utf-8")
    _git(git_repo.root, "add", ".")
    _git(git_repo.root, "commit", "--quiet", "--message", "unrelated")
    _git(git_repo.root, "switch", "--quiet", "contribution/demo")

    reported = changes(git_repo.root, "master")
    assert {c.kind for c in reported} == {ChangeKind.ADDED}
    assert all(c.path.is_relative_to(published) for c in reported)
    assert git_repo.changeset_errors(*reported) == ()


def test_submit_pushes_and_opens_a_pr_by_default(
    submission_repo: tuple[Repo, Path, Path], monkeypatch: pytest.MonkeyPatch
) -> None:
    repo, published, remote = submission_repo
    gh_calls: list[tuple[str, ...]] = []

    def record_gh(_root: Path, *args: str) -> str:
        gh_calls.append(args)
        return ""

    def accept_gh(_root: Path) -> None:
        pass

    def accept_fork(_root: Path, *_args: str) -> tuple[str, str]:
        return "contributor", submit_cmd.FORK_REMOTE

    monkeypatch.setattr(submit_cmd, "require_gh", accept_gh)
    monkeypatch.setattr(submit_cmd, "prepare_fork", accept_fork)
    monkeypatch.setattr(submit_cmd, "gh", record_gh)

    result = runner.invoke(app, ["--repo", str(repo.root), "submit", str(published)])

    assert result.exit_code == 0, result.output
    branch = f"contribution/{published.name[:12]}"
    assert _git_output(repo.root, "branch", "--show-current") == branch
    assert _git_output(repo.root, "rev-parse", "HEAD^") == _git_output(
        repo.root, "rev-parse", "origin/main"
    )
    assert _git_output(remote, "rev-parse", f"refs/heads/{branch}") == _git_output(
        repo.root, "rev-parse", "HEAD"
    )
    assert gh_calls == [
        (
            "pr",
            "create",
            "--repo",
            submit_cmd.UPSTREAM_REPOSITORY,
            "--base",
            "main",
            "--head",
            f"contributor:{branch}",
            "--title",
            "contribution: demo-1",
            "--body-file",
            ".github/pull_request_template.md",
        )
    ]


def test_submit_no_pr_still_pushes(submission_repo: tuple[Repo, Path, Path]) -> None:
    repo, published, remote = submission_repo
    result = runner.invoke(app, ["--repo", str(repo.root), "submit", str(published), "--no-pr"])
    assert result.exit_code == 0, result.output
    branch = f"contribution/{published.name[:12]}"
    assert _git_output(remote, "rev-parse", f"refs/heads/{branch}")


def test_submit_refuses_an_existing_staged_change(submission_repo: tuple[Repo, Path, Path]) -> None:
    repo, published, _remote = submission_repo
    staged = repo.root / "staged.txt"
    staged.write_text("do not commit me\n", encoding="utf-8")
    _git(repo.root, "add", staged.name)

    result = runner.invoke(app, ["--repo", str(repo.root), "submit", str(published), "--no-pr"])

    assert result.exit_code == 2
    assert "empty staging area" in result.output
    assert _git_output(repo.root, "branch", "--show-current") == "main"
    assert _git_output(repo.root, "diff", "--cached", "--name-only") == staged.name


def test_submit_refuses_untracked_files_outside_the_contribution(
    submission_repo: tuple[Repo, Path, Path],
) -> None:
    repo, published, _remote = submission_repo
    (repo.root / "notes.txt").write_text("unrelated\n", encoding="utf-8")
    result = runner.invoke(app, ["--repo", str(repo.root), "submit", str(published), "--no-pr"])
    assert result.exit_code == 2
    assert "untracked files outside" in result.output
    assert _git_output(repo.root, "branch", "--show-current") == "main"


def test_submit_refuses_tracked_modifications(
    submission_repo: tuple[Repo, Path, Path],
) -> None:
    repo, published, _remote = submission_repo
    (repo.root / "conjectures" / "allowlist.json").write_text("changed\n", encoding="utf-8")
    result = runner.invoke(app, ["--repo", str(repo.root), "submit", str(published), "--no-pr"])
    assert result.exit_code == 2
    assert "no tracked modifications" in result.output
    assert _git_output(repo.root, "branch", "--show-current") == "main"


def test_submit_refuses_local_commits_on_main(submission_repo: tuple[Repo, Path, Path]) -> None:
    repo, published, _remote = submission_repo
    (repo.root / "local.txt").write_text("local commit\n", encoding="utf-8")
    _git(repo.root, "add", "local.txt")
    _git(repo.root, "commit", "--quiet", "--message", "local-only")

    result = runner.invoke(app, ["--repo", str(repo.root), "submit", str(published), "--no-pr"])

    assert result.exit_code == 2
    assert "local main contains commits" in result.output
    assert _git_output(repo.root, "branch", "--show-current") == "main"


def test_submit_fast_forwards_main_before_branching(
    submission_repo: tuple[Repo, Path, Path],
) -> None:
    repo, published, _remote = submission_repo
    main = _git_output(repo.root, "rev-parse", "HEAD")
    tree = _git_output(repo.root, "rev-parse", "HEAD^{tree}")
    remote_main = _git_output(repo.root, "commit-tree", tree, "-p", main, "-m", "upstream update")
    _git(repo.root, "push", "--quiet", "origin", f"{remote_main}:refs/heads/main")

    result = runner.invoke(app, ["--repo", str(repo.root), "submit", str(published), "--no-pr"])

    assert result.exit_code == 0, result.output
    assert _git_output(repo.root, "rev-parse", "HEAD^") == remote_main


def test_submit_requires_no_pr_when_push_is_disabled(
    submission_repo: tuple[Repo, Path, Path],
) -> None:
    repo, published, _remote = submission_repo
    result = runner.invoke(app, ["--repo", str(repo.root), "submit", str(published), "--no-push"])
    assert result.exit_code == 2
    assert "--no-push requires --no-pr" in plain(result.output)


def test_submit_can_keep_the_commit_local(submission_repo: tuple[Repo, Path, Path]) -> None:
    repo, published, _remote = submission_repo
    result = runner.invoke(
        app,
        ["--repo", str(repo.root), "submit", str(published), "--no-push", "--no-pr"],
    )
    assert result.exit_code == 0, result.output
    branch = f"contribution/{published.name[:12]}"
    assert _git_output(repo.root, "ls-remote", "--heads", "origin", branch) == ""


def test_missing_gh_has_actionable_guidance(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    def missing(_root: Path, *_args: str) -> str:
        raise GitError("gh: not installed")

    monkeypatch.setattr(git_cmd, "gh", missing)
    # The message has to carry somewhere to get gh, not just the name of it.
    with pytest.raises(GitError, match=r"https://github\.com/cli/cli.*--no-pr"):
        require_gh(tmp_path)


def test_unauthenticated_gh_has_actionable_guidance(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    def unauthenticated(_root: Path, *args: str) -> str:
        if args == ("auth", "status"):
            raise GitError("not logged in")
        return "gh version"

    monkeypatch.setattr(git_cmd, "gh", unauthenticated)
    with pytest.raises(GitError, match=r"gh auth login.*--no-pr"):
        require_gh(tmp_path)


def test_prepare_fork_adds_canonical_and_fork_remotes(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    git_calls: list[tuple[str, ...]] = []
    gh_calls: list[tuple[str, ...]] = []

    def record_git(_root: Path, *args: str) -> str:
        git_calls.append(args)
        if args[:3] == ("remote", "get-url", "upstream"):
            raise GitError("missing")
        if args == ("remote",):
            return "fork\nupstream\n"
        if args == ("remote", "get-url", "fork"):
            return "git@github.com:contributor/repo.git\n"
        if args == ("remote", "get-url", "upstream"):
            return "https://github.com/owner/repo.git\n"
        return ""

    def record_gh(_root: Path, *args: str) -> str:
        gh_calls.append(args)
        return "contributor\n" if args[:2] == ("api", "user") else ""

    monkeypatch.setattr(git_cmd, "run", record_git)
    monkeypatch.setattr(git_cmd, "gh", record_gh)

    owner, remote = prepare_fork(
        tmp_path,
        "owner/repo",
        "https://github.com/owner/repo.git",
        "upstream",
        "fork",
    )

    assert owner == "contributor"
    assert remote == "fork"
    assert git_calls == [
        ("remote", "get-url", "upstream"),
        ("remote", "add", "upstream", "https://github.com/owner/repo.git"),
        ("remote",),
        ("remote", "get-url", "fork"),
    ]
    # set-default takes OWNER/REPO. Passing the remote name is what real gh rejects with
    # `expected the "[HOST/]OWNER/REPO" format`, and a mock that accepts any argument is
    # exactly how that reached a user.
    assert gh_calls == [
        ("repo", "set-default", "owner/repo"),
        ("repo", "fork", "--remote", "--remote-name", "fork"),
        ("api", "user", "--jq", ".login"),
    ]


def test_prepare_fork_reuses_an_existing_origin_fork(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    def git_output(_root: Path, *args: str) -> str:
        outputs: dict[tuple[str, ...], str] = {
            ("remote", "get-url", "upstream"): "https://github.com/owner/repo.git\n",
            ("remote",): "origin\nupstream\n",
            ("remote", "get-url", "origin"): "git@github.com:contributor/repo.git\n",
        }
        return outputs.get(args, "")

    def gh_output(_root: Path, *args: str) -> str:
        return "contributor\n" if args[:2] == ("api", "user") else ""

    monkeypatch.setattr(git_cmd, "run", git_output)
    monkeypatch.setattr(git_cmd, "gh", gh_output)

    assert prepare_fork(
        tmp_path,
        "owner/repo",
        "https://github.com/owner/repo.git",
        "upstream",
        "fork",
    ) == ("contributor", "origin")


def test_update_main_fetches_canonical_main_and_updates_submodules(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    calls: list[tuple[str, ...]] = []

    def record_run(_root: Path, *args: str) -> str:
        calls.append(args)
        return ""

    def same_revision(_root: Path, _name: str) -> str:
        return "same"

    monkeypatch.setattr(git_cmd, "run", record_run)
    monkeypatch.setattr(git_cmd, "revision", same_revision)

    update_main(tmp_path, "https://github.com/owner/repo.git")

    assert calls == [
        (
            "fetch",
            "--recurse-submodules=on-demand",
            "https://github.com/owner/repo.git",
            "main",
        ),
        ("merge", "--ff-only", "FETCH_HEAD"),
        ("submodule", "update", "--init", "--recursive"),
    ]


# gh validates this argument itself, so the guard belongs on the shape we send, not on a
# mock that would accept anything.
def test_prepare_fork_never_passes_a_remote_name_to_set_default(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    remotes = {"upstream", "fork"}
    seen: list[tuple[str, ...]] = []

    def record_git(_root: Path, *args: str) -> str:
        if args[:3] == ("remote", "get-url", "upstream"):
            raise GitError("missing")
        if args == ("remote",):
            return "fork\nupstream\n"
        if args == ("remote", "get-url", "fork"):
            return "git@github.com:contributor/repo.git\n"
        return ""

    def record_gh(_root: Path, *args: str) -> str:
        seen.append(args)
        if args[:2] == ("repo", "set-default"):
            target = args[2]
            if target in remotes or "/" not in target:
                raise GitError(f'expected the "[HOST/]OWNER/REPO" format, got "{target}"')
        return "contributor\n" if args[:2] == ("api", "user") else ""

    monkeypatch.setattr(git_cmd, "run", record_git)
    monkeypatch.setattr(git_cmd, "gh", record_gh)

    prepare_fork(tmp_path, "owner/repo", "https://github.com/owner/repo.git", "upstream", "fork")

    assert ("repo", "set-default", "owner/repo") in seen
