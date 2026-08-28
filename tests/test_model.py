from __future__ import annotations

import pytest

from conjectures_contribution.canonical import derive_id
from conjectures_contribution.model import (
    ArtifactName,
    ArtifactRef,
    ContributionId,
    Kind,
    Mode,
    Payload,
    PublicKey,
    SchemaError,
    Sha256,
    TargetSlug,
)


def _artifact(name: str) -> ArtifactRef:
    return ArtifactRef(ArtifactName(name), Sha256.of(b""), 0)


def _payload(**overrides: object) -> Payload:
    base: dict[str, object] = {
        "schema_version": 1,
        "target": TargetSlug("demo-1"),
        "reward_target_id": "fc-target:Demo.demo",
        "tasks_commit": "0" * 40,
        "mode": Mode.EITHER,
        "kind": Kind.IDEA,
        "title": "A title",
        "author": PublicKey("a" * 64),
        "parents": (),
        "artifacts": (_artifact("sources.md"),),
    }
    return Payload(**{**base, **overrides})  # type: ignore[arg-type]


@pytest.mark.parametrize("name", ["../evil", "Upper.md", ".hidden", "metadata.json", "draft.json"])
def test_unsafe_artifact_names_are_rejected(name: str) -> None:
    with pytest.raises(SchemaError):
        ArtifactName(name)


@pytest.mark.parametrize("value", ["", "A" * 64, "0" * 63, "0" * 65])
def test_digest_width_is_enforced(value: str) -> None:
    with pytest.raises(SchemaError):
        Sha256(value)


def test_distinct_digest_types_do_not_compare_equal() -> None:
    digest: object = Sha256("0" * 64)
    assert digest != ContributionId("0" * 64)


def test_unsorted_parents_are_rejected() -> None:
    with pytest.raises(SchemaError):
        _payload(parents=(ContributionId("b" * 64), ContributionId("a" * 64)))


def test_duplicate_artifacts_are_rejected() -> None:
    with pytest.raises(SchemaError):
        _payload(artifacts=(_artifact("sources.md"), _artifact("sources.md")))


def test_empty_artifacts_are_rejected() -> None:
    with pytest.raises(SchemaError):
        _payload(artifacts=())


@pytest.mark.parametrize("title", ["", " padded ", "two\nlines", "x" * 121])
def test_bad_titles_are_rejected(title: str) -> None:
    with pytest.raises(SchemaError):
        _payload(title=title)


def test_round_trip_preserves_identity() -> None:
    payload = _payload()
    assert Payload.parse(payload.to_json()) == payload
    assert derive_id(Payload.parse(payload.to_json())) == derive_id(payload)


def test_id_is_bound_to_the_target() -> None:
    assert derive_id(_payload()) != derive_id(_payload(target=TargetSlug("demo-2")))


def test_id_is_bound_to_the_author() -> None:
    assert derive_id(_payload()) != derive_id(_payload(author=PublicKey("b" * 64)))
