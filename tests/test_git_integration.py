from __future__ import annotations

import shutil
import subprocess
from pathlib import Path

import pytest
from typer.testing import CliRunner

from conjectures_contribution.checks import ChangeKind
from conjectures_contribution.cli import git as git_cmd
from conjectures_contribution.cli import submit as submit_cmd
from conjectures_contribution.cli.git import GitError, changes, require_gh
from conjectures_contribution.cli.main import app

from .conftest import Repo, make_repo

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
def submission_repo(tmp_path: Path) -> tuple[Repo, Path, Path]:
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
    _git(root, "push", "--quiet", "--set-upstream", "origin", "main")
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

    monkeypatch.setattr(submit_cmd, "require_gh", accept_gh)
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
    assert gh_calls == [("pr", "create", "--fill", "--base", "main")]


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
    assert "--no-push requires --no-pr" in result.output


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
    with pytest.raises(GitError, match="install it or submit with --no-pr"):
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
