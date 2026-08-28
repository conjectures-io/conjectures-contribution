from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest

from conjectures_contribution import store
from conjectures_contribution.build import BuildError, Built
from conjectures_contribution.checks import Change, ChangeKind
from conjectures_contribution.model import (
    MAX_ARTIFACT_BYTES,
    METADATA_FILENAME,
    ContributionId,
    Draft,
    TargetSlug,
)

from .conftest import THEOREM, Repo, make_repo


def test_valid_contribution_has_no_errors(repo: Repo, published: Path) -> None:
    assert repo.errors(published) == ()


def test_missing_metadata(repo: Repo, published: Path) -> None:
    (published / METADATA_FILENAME).unlink()
    assert repo.errors(published) == ("C001",)


def test_invalid_json(repo: Repo, published: Path) -> None:
    (published / METADATA_FILENAME).write_text("{", encoding="utf-8")
    assert repo.errors(published) == ("C001",)


def test_unknown_payload_field(repo: Repo, published: Path) -> None:
    repo.rewrite_raw(published, lambda raw: {**raw, "payload": {**raw["payload"], "bonus": 1}})
    assert repo.errors(published) == ("C001",)


def test_unsafe_artifact_name_is_rejected_at_parse(repo: Repo, published: Path) -> None:
    def mutate(raw: dict[str, Any]) -> dict[str, Any]:
        payload = dict(raw["payload"])
        payload["artifacts"] = [{"name": "../evil", "sha256": "0" * 64, "size": 1}]
        return {**raw, "payload": payload}

    repo.rewrite_raw(published, mutate)
    assert repo.errors(published) == ("C001",)


def test_unknown_target(repo: Repo, published: Path) -> None:
    moved = repo.resign(published, target=TargetSlug("no-such-target"))
    assert repo.errors(moved) == ("C002",)


def test_retired_target(tmp_path: Path) -> None:
    repo = make_repo(tmp_path, retired=[THEOREM])
    assert repo.errors(repo.promote()) == ("C002",)


def test_reward_target_mismatch(repo: Repo, published: Path) -> None:
    moved = repo.resign(published, reward_target_id="fc-target:Other.other")
    assert repo.errors(moved) == ("C002",)


def test_stale_tasks_commit(repo: Repo, published: Path) -> None:
    moved = repo.resign(published, tasks_commit="a" * 40)
    assert repo.errors(moved) == ("C003",)


def test_payload_edited_without_resigning(repo: Repo, published: Path) -> None:
    repo.rewrite_raw(
        published, lambda raw: {**raw, "payload": {**raw["payload"], "title": "Rewritten"}}
    )
    assert repo.errors(published) == ("C004", "C006")


def test_directory_name_does_not_match_id(repo: Repo, published: Path) -> None:
    renamed = published.parent / ("f" * 64)
    published.rename(renamed)
    assert repo.errors(renamed) == ("C004",)


def test_duplicate_contribution_id(repo: Repo, published: Path) -> None:
    import shutil  # noqa: PLC0415 - only this test needs it

    twin = repo.contributions / "other-target" / published.name
    twin.parent.mkdir(parents=True)
    shutil.copytree(published, twin)
    assert repo.errors(published) == ("C005", "C015")
    assert repo.errors(twin) == ("C004", "C005", "C015")


def test_contribution_filed_under_the_wrong_target(repo: Repo, published: Path) -> None:
    moved = repo.contributions / "other-target" / published.name
    moved.parent.mkdir(parents=True)
    published.rename(moved)
    assert repo.errors(moved) == ("C004",)


def test_corrupted_signature(repo: Repo, published: Path) -> None:
    repo.rewrite_raw(published, lambda raw: {**raw, "signature": "0" * 128})
    assert repo.errors(published) == ("C006",)


def test_artifact_bytes_changed(repo: Repo, published: Path) -> None:
    (published / "sources.md").write_text("# Sources\nedited\n", encoding="utf-8")
    assert repo.errors(published) == ("C007", "C007")


def test_declared_artifact_missing(repo: Repo, published: Path) -> None:
    (published / "sources.md").unlink()
    assert repo.errors(published) == ("C007",)


def test_required_artifact_not_declared(repo: Repo) -> None:
    published = repo.promote(repo.draft(files={"script.lean": "-- sketch\n"}))
    assert repo.errors(published) == ("C007",)


def test_undeclared_file_in_directory(repo: Repo, published: Path) -> None:
    (published / "extra.md").write_text("smuggled\n", encoding="utf-8")
    assert repo.errors(published) == ("C008",)


def test_symlink_in_directory(repo: Repo, published: Path) -> None:
    (published / "link.md").symlink_to(published / "sources.md")
    assert repo.errors(published) == ("C008",)


def test_oversized_artifact(repo: Repo) -> None:
    directory = repo.draft(files={"sources.md": "x" * (MAX_ARTIFACT_BYTES + 1)})
    draft = Draft.parse(json.loads((directory / "draft.json").read_text()))
    published = Built.from_draft(draft, directory, repo.pool, repo.key).write(repo.contributions)
    assert repo.errors(published) == ("C009",)


def test_unknown_parent(repo: Repo, published: Path) -> None:
    moved = repo.resign(published, parents=(ContributionId("b" * 64),))
    assert repo.errors(moved) == ("C010",)


def test_known_parent(repo: Repo, published: Path) -> None:
    child = repo.promote(repo.draft(files={"sources.md": "# Sources\nchild\n"}))
    moved = repo.resign(child, parents=(repo.read(published).contribution_id,))
    assert repo.errors(moved) == ()


def _added(path: Path) -> Change:
    return Change(path.resolve(), ChangeKind.ADDED)


def test_changeset_confined_to_one_contribution(repo: Repo, published: Path) -> None:
    assert repo.changeset_errors(_added(published / "sources.md")) == ()


def test_changeset_touching_two_contributions(repo: Repo, published: Path) -> None:
    other = repo.promote(repo.draft(files={"sources.md": "# Sources\nother\n"}))
    assert repo.changeset_errors(
        _added(published / "sources.md"), _added(other / "sources.md")
    ) == ("C011",)


def test_changeset_touching_source_code(repo: Repo, published: Path) -> None:
    assert repo.changeset_errors(
        _added(published / "sources.md"), _added(repo.root / "src" / "checks.py")
    ) == ("C011",)


def test_changeset_touching_a_target_index(repo: Repo, published: Path) -> None:
    assert repo.changeset_errors(_added(published.parent / "index.md")) == ("C011",)


def test_changeset_with_no_contribution(repo: Repo) -> None:
    assert repo.changeset_errors(_added(repo.root / "pyproject.toml")) == ("C011",)


# Selecting only parseable bundles would let this directory escape every rule.
def test_files_added_to_a_bundle_without_metadata_are_checked(repo: Repo) -> None:
    stray = repo.contributions / "demo-1" / ("a" * 64)
    stray.mkdir(parents=True)
    (stray / "evil.sh").write_text("#!/bin/sh\n", encoding="utf-8")
    change = _added(stray / "evil.sh")
    assert store.touched(repo.contributions, [change]) == (stray,)
    assert repo.changeset_errors(change) == ()
    assert repo.errors(stray) == ("C001",)


def test_empty_changeset_is_silent(repo: Repo) -> None:
    assert repo.changeset_errors() == ()


def test_modifying_a_published_contribution(repo: Repo, published: Path) -> None:
    change = Change((published / "sources.md").resolve(), ChangeKind.MODIFIED)
    assert repo.changeset_errors(change) == ("C012",)


def test_deleting_a_published_contribution(repo: Repo, published: Path) -> None:
    change = Change((published / "sources.md").resolve(), ChangeKind.DELETED)
    assert repo.changeset_errors(change) == ("C012",)


def test_non_canonical_metadata(repo: Repo, published: Path) -> None:
    raw = (published / METADATA_FILENAME).read_bytes()
    (published / METADATA_FILENAME).write_bytes(raw.replace(b"\n", b"\n ", 1))
    assert repo.errors(published) == ("C013",)


# The reviewer reads the first "title"; json.loads keeps the last.
def test_duplicate_json_key_is_rejected(repo: Repo, published: Path) -> None:
    raw = (published / METADATA_FILENAME).read_text(encoding="utf-8")
    smuggled = raw.replace(
        '"title": "A partial reduction"',
        '"title": "Innocuous heading",\n    "title": "A partial reduction"',
    )
    (published / METADATA_FILENAME).write_text(smuggled, encoding="utf-8")
    assert repo.errors(published) == ("C013",)


def test_bidi_override_in_an_artifact(repo: Repo) -> None:
    published = repo.promote(repo.draft(files={"sources.md": "# Sources\n-- \u202esafe\n"}))
    assert repo.errors(published) == ("C014",)


def test_artifact_that_is_not_utf8(repo: Repo) -> None:
    published = repo.promote(repo.draft(files={"sources.md": b"# Sources\n\xff\xfe\n"}))
    assert repo.errors(published) == ("C014",)


def test_empty_artifact(repo: Repo) -> None:
    published = repo.promote(repo.draft(files={"sources.md": ""}))
    assert repo.errors(published) == ("C009",)


def test_identical_content_republished(repo: Repo) -> None:
    repo.promote()
    second = repo.promote(repo.draft(title="A different framing"))
    assert repo.errors(second) == ("C015",)


def test_unsafe_name_cannot_be_promoted(repo: Repo) -> None:
    directory = repo.draft()
    (directory / "Evil Name.md").write_text("x\n", encoding="utf-8")
    draft = Draft.parse(json.loads((directory / "draft.json").read_text()))
    with pytest.raises(BuildError):
        Built.from_draft(draft, directory, repo.pool, repo.key)
