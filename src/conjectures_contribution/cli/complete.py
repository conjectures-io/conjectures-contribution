from __future__ import annotations

import functools
import os
from collections.abc import Callable, Iterable
from pathlib import Path

from ..model import DRAFT_FILENAME, Mode
from ..pool import DEFAULT_TIER
from . import config
from .repo import Workspace

# Every callback here runs on each Tab keystroke, so none may raise and none may be slow.
# Reading the pool through Pool.load would be both: it parses a 360 KB allowlist and 418
# manifests, and it raises PoolError on any inconsistency. The bundle directory names are what
# Pool.load derives slugs from anyway, so one listdir is both cheaper and no less correct.


def _never_raises(fn: Callable[[str], list[str]]) -> Callable[[str], list[str]]:
    @functools.wraps(fn)
    def wrapper(incomplete: str) -> list[str]:
        try:
            return fn(incomplete)
        except Exception:
            return []

    return wrapper


@_never_raises
def targets(incomplete: str) -> list[str]:
    return _match(_slugs(), incomplete)


@_never_raises
def drafts(incomplete: str) -> list[str]:
    return _match(_draft_names(), incomplete)


@_never_raises
def wallets(incomplete: str) -> list[str]:
    return _match(_wallet_names(), incomplete)


@_never_raises
def hotkeys(incomplete: str) -> list[str]:
    return _match(_hotkey_names(), incomplete)


def _slugs() -> list[str]:
    workspace = Workspace.discover_quietly()
    if workspace is None:
        return []
    found: list[str] = []
    for name in _listdir(workspace.pool_root / "pool" / DEFAULT_TIER):
        for mode in Mode:
            suffix = f"-{mode}"
            if name.endswith(suffix):
                found.append(name[: -len(suffix)])
                break
    return found


def _draft_names() -> list[str]:
    workspace = Workspace.discover_quietly()
    if workspace is None:
        return []
    root = workspace.drafts
    return [name for name in _listdir(root) if (root / name / DRAFT_FILENAME).is_file()]


def _wallet_names() -> list[str]:
    root = _wallet_path()
    return [name for name in _listdir(root) if (root / name).is_dir()]


def _hotkey_names() -> list[str]:
    settings = config.resolve()
    root = Path(settings.path.value).expanduser() / settings.name.value / "hotkeys"
    # btcli keeps the public half beside the private one; only the latter can sign.
    return [name for name in _listdir(root) if not name.endswith("pub.txt")]


def _wallet_path() -> Path:
    return Path(config.resolve().path.value).expanduser()


def _listdir(root: Path) -> list[str]:
    try:
        return os.listdir(root)  # noqa: PTH208 -- names only; Path.iterdir would build 400 objects
    except OSError:
        return []


def _match(candidates: Iterable[str], incomplete: str) -> list[str]:
    ordered = sorted(set(candidates))
    prefixed = [name for name in ordered if name.startswith(incomplete)]
    # A prefix nobody types is more useful as a substring search than as no answer at all.
    return prefixed or [name for name in ordered if incomplete in name]
