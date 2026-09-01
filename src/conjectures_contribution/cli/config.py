from __future__ import annotations

import json
import os
import tomllib
from dataclasses import dataclass
from enum import StrEnum
from pathlib import Path
from typing import Any

from ..wallet import DEFAULT_WALLET_PATH, WalletRef

ENV_PREFIX = "CONJECTURES_"

# Not derived from ENV_PREFIX: CONJECTURES_CONFIG_FILE is conjectures-miner's own variable, and
# sharing it would mean pointing the miner at a file silently repointed this tool too.
CONFIG_FILE_ENV = "CONJECTURES_CONTRIBUTION_CONFIG_FILE"
DEFAULT_CONFIG_FILE = Path("~/.config/conjectures/contribution.toml")


class ConfigKey(StrEnum):
    WALLET_NAME = "wallet_name"
    WALLET_HOTKEY = "wallet_hotkey"
    WALLET_PATH = "wallet_path"
    REPO_PATH = "repo_path"
    AUTHOR_KEY = "author_key"


class Source(StrEnum):
    FLAG = "flag"
    ENV = "env"
    FILE = "file"
    WALK = "walk-up"
    PIN = "pinned"
    DEFAULT = "default"


@dataclass(frozen=True, slots=True)
class Setting:
    value: str
    source: Source


@dataclass(frozen=True, slots=True)
class WalletSettings:
    name: Setting
    hotkey: Setting
    path: Setting

    @property
    def ref(self) -> WalletRef:
        return WalletRef(
            name=self.name.value,
            hotkey=self.hotkey.value,
            path=Path(self.path.value).expanduser(),
        )


def config_file() -> Path:
    override = os.environ.get(CONFIG_FILE_ENV)
    return Path(override).expanduser() if override else DEFAULT_CONFIG_FILE.expanduser()


def resolve(
    name: str | None = None, hotkey: str | None = None, path: Path | None = None
) -> WalletSettings:
    stored = _read(config_file())
    return WalletSettings(
        name=_pick("wallet_name", name, stored, "default"),
        hotkey=_pick("wallet_hotkey", hotkey, stored, "default"),
        path=_pick("wallet_path", path, stored, str(DEFAULT_WALLET_PATH)),
    )


# The repository is resolved by cli.repo, which puts the walk-up above this; all we own is
# whatever was written to the file.
def pinned_repo() -> str | None:
    return _string(_read(config_file()), "repo_path")


# The public half of the signing key, cached so a read-only query never has to open the
# private one. Written by `contrib key`, read by `contrib ls --mine`.
def author_key() -> str | None:
    return _string(_read(config_file()), "author_key")


def write(key: ConfigKey, value: str) -> None:
    stored = _read(config_file())
    stored[str(key)] = value
    _dump(stored)


def unset(key: ConfigKey) -> None:
    stored = _read(config_file())
    stored.pop(str(key), None)
    _dump(stored)


# Tolerant on read, canonical on write: only the keys we own survive, so this file cannot
# accumulate settings nothing reads. A TOML basic string is a JSON string for every character
# a path or wallet name can hold, which is what makes json.dumps the right escaper here.
def _dump(stored: dict[str, Any]) -> None:
    lines = [
        f"{key} = {json.dumps(value)}\n"
        for key in ConfigKey
        if (value := _string(stored, str(key))) is not None
    ]
    path = config_file()
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("".join(lines), encoding="utf-8")


def _pick(key: str, flag: str | Path | None, stored: dict[str, Any], fallback: str) -> Setting:
    if flag is not None:
        return Setting(str(flag), Source.FLAG)
    env = os.environ.get(f"{ENV_PREFIX}{key.upper()}")
    if env:
        return Setting(env, Source.ENV)
    value = _string(stored, key)
    if value is not None:
        return Setting(value, Source.FILE)
    return Setting(fallback, Source.DEFAULT)


def _string(stored: dict[str, Any], key: str) -> str | None:
    value = stored.get(key)
    return value if isinstance(value, str) and value else None


def _read(path: Path) -> dict[str, Any]:
    try:
        with path.open("rb") as handle:
            return tomllib.load(handle)
    except (FileNotFoundError, NotADirectoryError, PermissionError, tomllib.TOMLDecodeError):
        return {}
