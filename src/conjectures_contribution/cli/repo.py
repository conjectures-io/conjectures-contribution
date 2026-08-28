from __future__ import annotations

import os
from dataclasses import dataclass
from pathlib import Path
from typing import Self

from ..pool import Pool

POOL_MARKER = Path("conjectures") / "allowlist.json"
DEFAULT_KEY = Path("~/.config/conjectures/ed25519.key")


class WorkspaceError(RuntimeError):
    pass


@dataclass(frozen=True, slots=True)
class Workspace:
    root: Path

    @classmethod
    def discover(cls, start: Path | None = None) -> Self:
        override = os.environ.get("CONJECTURES_CONTRIBUTION_ROOT")
        if override:
            return cls(Path(override).expanduser().resolve())
        current = (start or Path.cwd()).resolve()
        for candidate in (current, *current.parents):
            if (candidate / POOL_MARKER).is_file():
                return cls(candidate)
        raise WorkspaceError(f"no repository containing {POOL_MARKER} at or above {current}")

    @property
    def pool_root(self) -> Path:
        return self.root / "conjectures"

    @property
    def contributions(self) -> Path:
        return self.root / "contributions"

    @property
    def drafts(self) -> Path:
        return self.root / "drafts"

    def pool(self) -> Pool:
        return Pool.load(self.pool_root)


def key_path(override: Path | None) -> Path:
    if override is not None:
        return override.expanduser()
    return Path(os.environ.get("CONJECTURES_KEY", str(DEFAULT_KEY))).expanduser()
