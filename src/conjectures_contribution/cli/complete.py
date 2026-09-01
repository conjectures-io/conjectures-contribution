from __future__ import annotations

import functools
import os
from collections.abc import Callable, Iterable
from datetime import UTC, datetime
from pathlib import Path
from typing import ParamSpec

import typer

from ..model import DRAFT_FILENAME, Mode
from ..pool import DEFAULT_TIER, Pool
from ..query.columns import Column, ColumnType
from ..query.corpus import read_corpus
from ..query.grains import GRAINS
from ..query.rows import ContributionRow
from ..query.values import Field, Source, Unavailable
from . import config
from .repo import Workspace, WorkspaceError

# Every callback here runs on each Tab keystroke, so none may raise and none may be slow.
# Reading the pool through Pool.load would be both: it parses a 360 KB allowlist and 418
# manifests, and it raises PoolError on any inconsistency. The bundle directory names are what
# Pool.load derives slugs from anyway, so one listdir is both cheaper and no less correct.


_P = ParamSpec("_P")


# Grain-aware callbacks take a context as well as the incomplete word, so the guard has to
# wrap both shapes rather than only the one-argument one.
def _never_raises(fn: Callable[_P, list[str]]) -> Callable[_P, list[str]]:
    @functools.wraps(fn)
    def wrapper(*args: _P.args, **kwargs: _P.kwargs) -> list[str]:
        try:
            return fn(*args, **kwargs)
        except Exception:
            return []

    return wrapper


@_never_raises
def targets(incomplete: str) -> list[str]:
    return _match(_slugs(), incomplete)


@_never_raises
def grains(incomplete: str) -> list[str]:
    return _match(GRAINS, incomplete)


# Typer supplies ctx and incomplete by annotation, not by name. Under resilient parsing the
# grain may be missing or unconverted, so completion and validation read the same table and a
# name that completes is always a name that validates.
@_never_raises
def sort_columns(ctx: typer.Context, incomplete: str) -> list[str]:
    return _match((c.name for c in _columns(ctx)), incomplete)


@_never_raises
def boolean_columns(ctx: typer.Context, incomplete: str) -> list[str]:
    return _match(
        (c.name for c in _columns(ctx) if c.type is ColumnType.BOOL),
        incomplete,
    )


@_never_raises
def windows(incomplete: str) -> list[str]:
    today = datetime.now(UTC).date()
    months = [today.replace(day=1, month=m).isoformat() for m in range(1, today.month + 1)]
    return _match(["7d", "30d", "90d", "6m", "1y", *months], incomplete)


@_never_raises
def declarations(incomplete: str) -> list[str]:
    return _match((name for row in _rows() for name in _available(row.declarations)), incomplete)


@_never_raises
def corpus_authors(incomplete: str) -> list[str]:
    return _match((str(r.author) for r in _rows() if not _hole(r.author)), incomplete)


@_never_raises
def corpus_coldkeys(incomplete: str) -> list[str]:
    return _match(
        (str(r.coldkey) for r in _rows() if r.coldkey is not None and not _hole(r.coldkey)),
        incomplete,
    )


# `hotkeys` below is a wallet hotkey name; this is a reward ss58 address. Different
# things, so different names — the first draft of this one shadowed the wallet one.
@_never_raises
def corpus_hotkeys(incomplete: str) -> list[str]:
    return _match(
        (str(r.hotkey) for r in _rows() if r.hotkey is not None and not _hole(r.hotkey)),
        incomplete,
    )


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


# Completing an option's *value* always leaves that option trailing with nothing after it,
# which is enough to make Click's resilient parse fall back to defaults — so `ctx.params`
# reports the default grain no matter what was typed. The typed word survives as a leftover
# in `ctx.args`, so read that first and fall back to the union rather than to a wrong grain.
def _columns(ctx: typer.Context) -> tuple[Column[object], ...]:
    typed = [*(str(a) for a in getattr(ctx, "args", ())), str(ctx.params.get("grain") or "")]
    for name in typed:
        grain = GRAINS.get(name)
        if grain is not None:
            return grain.columns
    return tuple(column for g in GRAINS.values() for column in g.columns)


# The pool costs 15 ms and feeds no column a completion offers, so it is never opened here.
def _rows() -> tuple[ContributionRow, ...]:
    workspace = Workspace.discover_quietly()
    if workspace is None:
        return ()
    corpus = read_corpus(
        workspace.root, workspace.contributions, _no_pool, frozenset({Source.TREE})
    )
    return corpus.contributions


def _no_pool() -> Pool:
    raise WorkspaceError("the pool is not read during completion")


def _hole(value: object) -> bool:
    return isinstance(value, Unavailable)


def _available(value: Field[tuple[str, ...]]) -> tuple[str, ...]:
    return () if isinstance(value, Unavailable) else value
