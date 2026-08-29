from __future__ import annotations

import os
from dataclasses import dataclass
from pathlib import Path
from typing import Self

import typer

from ..pool import Pool
from . import config
from .config import Source

POOL_MARKER = Path("conjectures") / "allowlist.json"
ROOT_ENV = "CONJECTURES_CONTRIBUTION_ROOT"
DEFAULT_KEY = Path("~/.config/conjectures/ed25519.key")

_PIN_HINT = "\n\n  cd into the repository and re-pin it:\n    contrib repo pin"


class WorkspaceError(RuntimeError):
    pass


@dataclass(frozen=True, slots=True)
class Workspace:
    root: Path
    source: Source
    pool_override: Path | None = None

    # The walk-up sits above the pin on purpose: a checkout that moved is still found by anyone
    # working inside it, and only the run-from-anywhere convenience breaks.
    @classmethod
    def discover(
        cls,
        start: Path | None = None,
        *,
        override: Path | None = None,
        pool_override: Path | None = None,
    ) -> Self:
        pool = _checked_pool(pool_override) if pool_override is not None else None
        if override is not None:
            return cls(
                _checked(override, f"--repo {override}", require_pool=pool is None),
                Source.FLAG,
                pool,
            )
        env = os.environ.get(ROOT_ENV)
        if env:
            return cls(_checked(Path(env), f"{ROOT_ENV}={env}"), Source.ENV)

        current = (start or Path.cwd()).resolve()
        for candidate in (current, *current.parents):
            if (candidate / POOL_MARKER).is_file():
                return cls(candidate, Source.WALK)

        pinned = config.pinned_repo()
        if pinned is not None:
            path = Path(pinned).expanduser().resolve()
            if not (path / POOL_MARKER).is_file():
                raise WorkspaceError(
                    f"pinned repository {path} no longer contains {POOL_MARKER}{_PIN_HINT}"
                )
            return cls(path, Source.PIN)

        raise WorkspaceError(
            f"no repository containing {POOL_MARKER} at or above {current}"
            "\n\n  cd into the repository, or pin it once:\n    contrib repo pin <path>"
        )

    # Shell completion runs this on every Tab and must stay silent about everything.
    @classmethod
    def discover_quietly(cls, start: Path | None = None) -> Self | None:
        try:
            return cls.discover(start)
        except WorkspaceError:
            return None

    def contains(self, path: Path) -> bool:
        resolved = path.resolve()
        return resolved == self.root or self.root in resolved.parents

    @property
    def pool_root(self) -> Path:
        return self.pool_override or self.root / "conjectures"

    @property
    def contributions(self) -> Path:
        return self.root / "contributions"

    @property
    def drafts(self) -> Path:
        return self.root / "drafts"

    def pool(self) -> Pool:
        return Pool.load(self.pool_root)


@dataclass(frozen=True, slots=True)
class RootOptions:
    repo: Path | None
    pool: Path | None


# Every command resolves through this rather than Workspace.discover, so acting on a
# repository the caller is not standing in is never silent. --repo rides the click context
# rather than a module global, so one invocation cannot inherit the last one's choice.
def open_workspace(ctx: typer.Context | None = None) -> Workspace:
    options = ctx.obj if ctx is not None else None
    override = options.repo if isinstance(options, RootOptions) else None
    pool_override = options.pool if isinstance(options, RootOptions) else None
    workspace = Workspace.discover(override=override, pool_override=pool_override)
    if not workspace.contains(Path.cwd()):
        typer.secho(
            f"note: using repository at {workspace.root} ({workspace.source})",
            fg=typer.colors.CYAN,
            err=True,
        )
    return workspace


def _checked(path: Path, label: str, *, require_pool: bool = True) -> Path:
    resolved = path.expanduser().resolve()
    if require_pool and not (resolved / POOL_MARKER).is_file():
        raise WorkspaceError(f"{label} does not contain {POOL_MARKER}")
    if not require_pool and not (resolved / "contributions").is_dir():
        raise WorkspaceError(f"{label} does not contain a contributions directory")
    return resolved


def _checked_pool(path: Path) -> Path:
    resolved = path.expanduser().resolve()
    if not (resolved / "allowlist.json").is_file():
        raise WorkspaceError(f"--pool {path} does not contain allowlist.json")
    return resolved


def key_path(override: Path | None) -> Path:
    if override is not None:
        return override.expanduser()
    return Path(os.environ.get("CONJECTURES_KEY", str(DEFAULT_KEY))).expanduser()
