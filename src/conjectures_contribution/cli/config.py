from __future__ import annotations

import os
import tomllib
from dataclasses import dataclass
from enum import StrEnum
from pathlib import Path
from typing import Any

from ..wallet import DEFAULT_WALLET_PATH, WalletRef

ENV_PREFIX = "CONJECTURES_"
CONFIG_FILE_ENV = f"{ENV_PREFIX}CONFIG_FILE"
DEFAULT_CONFIG_FILE = Path("~/.config/conjectures/config.toml")


class Source(StrEnum):
    FLAG = "flag"
    ENV = "env"
    FILE = "file"
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


def _pick(key: str, flag: str | Path | None, stored: dict[str, Any], fallback: str) -> Setting:
    if flag is not None:
        return Setting(str(flag), Source.FLAG)
    env = os.environ.get(f"{ENV_PREFIX}{key.upper()}")
    if env:
        return Setting(env, Source.ENV)
    value = stored.get(key)
    if isinstance(value, str) and value:
        return Setting(value, Source.FILE)
    return Setting(fallback, Source.DEFAULT)


# conjectures-miner owns this file and its full schema; we read three fields and ignore the
# rest, so a contributor who configured the miner needs nothing further here.
def _read(path: Path) -> dict[str, Any]:
    try:
        with path.open("rb") as handle:
            return tomllib.load(handle)
    except (FileNotFoundError, NotADirectoryError, PermissionError, tomllib.TOMLDecodeError):
        return {}
