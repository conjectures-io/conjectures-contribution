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
CANDIDATE_MARKER = Path("contributions")
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

    # The root is located once and the pool attached once, so an override cannot be honoured on
    # one resolution path and silently dropped on another.
    @classmethod
    def discover(
        cls,
        start: Path | None = None,
        *,
        override: Path | None = None,
        pool_override: Path | None = None,
    ) -> Self:
        pool = _checked_pool(pool_override) if pool_override is not None else None
        root, source = _locate(start, override=override, external_pool=pool is not None)
        return cls(root, source, pool)

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


# The walk-up sits above the pin on purpose: a checkout that moved is still found by anyone
# working inside it, and only the run-from-anywhere convenience breaks.
def _locate(
    start: Path | None, *, override: Path | None, external_pool: bool
) -> tuple[Path, Source]:
    if override is not None:
        return _checked(override, f"--repo {override}", external_pool=external_pool), Source.FLAG
    env = os.environ.get(ROOT_ENV)
    if env:
        return _checked(Path(env), f"{ROOT_ENV}={env}", external_pool=external_pool), Source.ENV

    current = (start or Path.cwd()).resolve()
    for candidate in (current, *current.parents):
        if _is_repository(candidate, external_pool=external_pool):
            return candidate, Source.WALK

    marker = _marker(external_pool=external_pool)
    pinned = config.pinned_repo()
    if pinned is not None:
        path = Path(pinned).expanduser().resolve()
        if not _is_repository(path, external_pool=external_pool):
            raise WorkspaceError(f"pinned repository {path} no longer contains {marker}{_PIN_HINT}")
        return path, Source.PIN

    raise WorkspaceError(
        f"no repository containing {marker} at or above {current}"
        "\n\n  cd into the repository, or pin it once:\n    contrib repo pin <path>"
    )


# What identifies a repository depends on whether its pool travels with it: a CI candidate is
# checked out without the submodule, so --pool also accepts the directory it does have.
def _is_repository(path: Path, *, external_pool: bool) -> bool:
    return (path / POOL_MARKER).is_file() or (external_pool and (path / CANDIDATE_MARKER).is_dir())


def _marker(*, external_pool: bool) -> str:
    return f"{POOL_MARKER} or {CANDIDATE_MARKER}/" if external_pool else str(POOL_MARKER)


def _checked(path: Path, label: str, *, external_pool: bool) -> Path:
    resolved = path.expanduser().resolve()
    if not _is_repository(resolved, external_pool=external_pool):
        raise WorkspaceError(f"{label} does not contain {_marker(external_pool=external_pool)}")
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
