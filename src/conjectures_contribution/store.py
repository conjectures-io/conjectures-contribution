from __future__ import annotations

import json
from collections import defaultdict
from collections.abc import Iterable, Iterator, Mapping
from dataclasses import dataclass
from pathlib import Path
from types import MappingProxyType
from typing import Self

from .model import METADATA_FILENAME, Change, Contribution, SchemaError

# <target>/<contribution-id>/<file>: the shallowest path that lies inside a bundle.
_BUNDLE_DEPTH = 3


def iter_contributions(root: Path) -> Iterator[Path]:
    if not root.is_dir():
        return
    for target in sorted(p for p in root.iterdir() if p.is_dir()):
        for candidate in sorted(p for p in target.iterdir() if p.is_dir()):
            if (candidate / METADATA_FILENAME).is_file():
                yield candidate


def contribution_directory(contributions_root: Path, path: Path) -> Path | None:
    try:
        relative = path.relative_to(contributions_root)
    except ValueError:
        return None
    if len(relative.parts) < _BUNDLE_DEPTH:
        return None
    return contributions_root / relative.parts[0] / relative.parts[1]


# Selection is by path, not by whether the directory parses: a change that drops files
# into a bundle with no metadata.json must still be checked, or it escapes every rule.
def touched(contributions_root: Path, changes: Iterable[Change]) -> tuple[Path, ...]:
    directories = {contribution_directory(contributions_root, c.path) for c in changes}
    return tuple(sorted(d for d in directories if d is not None and d.is_dir()))


@dataclass(frozen=True, slots=True)
class Published:
    by_id: Mapping[str, tuple[Path, ...]]
    by_content: Mapping[frozenset[str], tuple[Path, ...]]

    # Both indexes are multi-valued: collapsing duplicates here would hide exactly what
    # C005 and C015 exist to find.
    @classmethod
    def scan(cls, root: Path) -> Self:
        by_id: dict[str, list[Path]] = defaultdict(list)
        by_content: dict[frozenset[str], list[Path]] = defaultdict(list)
        for path in iter_contributions(root):
            by_id[path.name].append(path)
            fingerprint = _fingerprint(path)
            if fingerprint is not None:
                by_content[fingerprint].append(path)
        return cls(
            by_id=MappingProxyType({k: tuple(v) for k, v in by_id.items()}),
            by_content=MappingProxyType({k: tuple(v) for k, v in by_content.items()}),
        )


def _fingerprint(path: Path) -> frozenset[str] | None:
    try:
        raw = json.loads((path / METADATA_FILENAME).read_text(encoding="utf-8"))
        contribution = Contribution.parse(raw)
    except (OSError, json.JSONDecodeError, SchemaError):
        return None
    return frozenset(str(a.digest) for a in contribution.payload.artifacts)
