from __future__ import annotations

import shutil
import tempfile
from collections.abc import Mapping
from dataclasses import dataclass
from pathlib import Path
from types import MappingProxyType
from typing import Self

from .canonical import canonical_bytes, derive_id, payload_bytes
from .model import (
    DRAFT_FILENAME,
    METADATA_FILENAME,
    SCHEMA_VERSION,
    ArtifactName,
    ArtifactRef,
    Contribution,
    Draft,
    Payload,
    SchemaError,
    Sha256,
)
from .pool import Pool
from .signing import SigningKey
from .wallet import RewardSigner


class BuildError(RuntimeError):
    pass


@dataclass(frozen=True, slots=True)
class Built:
    contribution: Contribution
    sources: Mapping[ArtifactName, Path]

    @classmethod
    def from_draft(
        cls,
        draft: Draft,
        directory: Path,
        pool: Pool,
        key: SigningKey,
        reward: RewardSigner | None = None,
    ) -> Self:
        target = pool.targets.get(draft.target)
        if target is None:
            raise BuildError(f"unknown target '{draft.target}' in the pinned pool")

        sources = _collect(directory)
        payload = Payload(
            schema_version=SCHEMA_VERSION,
            target=draft.target,
            reward_target_id=target.reward_target_id,
            tasks_commit=pool.tasks_commit,
            mode=draft.mode,
            kind=draft.kind,
            title=draft.title,
            author=key.public_key,
            reward=None if reward is None else reward.reward,
            parents=draft.parents,
            artifacts=tuple(
                ArtifactRef(name, Sha256.of(path.read_bytes()), path.stat().st_size)
                for name, path in sorted(sources.items())
            ),
        )
        # The reward signature covers the id, which already commits to the reward
        # addresses, so it can only be produced once the payload is final.
        contribution_id = derive_id(payload)
        return cls(
            contribution=Contribution(
                payload=payload,
                contribution_id=contribution_id,
                signature=key.sign(payload_bytes(payload)),
                reward_signature=None if reward is None else reward.sign(contribution_id),
            ),
            sources=sources,
        )

    def write(self, contributions_root: Path) -> Path:
        payload = self.contribution.payload
        destination = (
            contributions_root / str(payload.target) / str(self.contribution.contribution_id)
        )
        if destination.exists():
            raise BuildError(f"{destination}: already exists")
        destination.parent.mkdir(parents=True, exist_ok=True)

        staging = Path(tempfile.mkdtemp(dir=destination.parent, prefix=".staging-"))
        try:
            for artifact in payload.artifacts:
                shutil.copyfile(self.sources[artifact.name], staging / str(artifact.name))
            (staging / METADATA_FILENAME).write_bytes(canonical_bytes(self.contribution.to_json()))
            staging.rename(destination)
        except BaseException:
            shutil.rmtree(staging, ignore_errors=True)
            raise
        return destination


def _collect(directory: Path) -> Mapping[ArtifactName, Path]:
    if not directory.is_dir():
        raise BuildError(f"{directory}: not a directory")

    collected: dict[ArtifactName, Path] = {}
    for entry in sorted(directory.iterdir()):
        if entry.name == DRAFT_FILENAME:
            continue
        if entry.is_symlink() or not entry.is_file():
            raise BuildError(f"{entry.name}: only regular files may be promoted")
        try:
            collected[ArtifactName(entry.name)] = entry
        except SchemaError as exc:
            raise BuildError(str(exc)) from None

    if not collected:
        raise BuildError(f"{directory}: nothing to promote")
    return MappingProxyType(collected)
