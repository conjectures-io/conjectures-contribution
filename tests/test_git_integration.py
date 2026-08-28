from __future__ import annotations

import shutil
import subprocess
from pathlib import Path

import pytest

from conjectures_contribution.checks import ChangeKind
from conjectures_contribution.cli.git import changes

from .conftest import Repo, make_repo

pytestmark = pytest.mark.skipif(shutil.which("git") is None, reason="git is not installed")


def _git(root: Path, *args: str) -> None:
    subprocess.run(["git", *args], cwd=root, check=True, capture_output=True)  # noqa: S603, S607


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
