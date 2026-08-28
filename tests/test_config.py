from __future__ import annotations

from pathlib import Path

import pytest

from conjectures_contribution.cli import config

WALLET_ENV = f"{config.ENV_PREFIX}WALLET_NAME"


@pytest.fixture(autouse=True)
def _isolated(  # pyright: ignore[reportUnusedFunction]
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    for name in ("WALLET_NAME", "WALLET_HOTKEY", "WALLET_PATH"):
        monkeypatch.delenv(f"{config.ENV_PREFIX}{name}", raising=False)
    monkeypatch.setenv(config.CONFIG_FILE_ENV, str(tmp_path / "config.toml"))


def _write(tmp_path: Path, body: str) -> None:
    (tmp_path / "config.toml").write_text(body, encoding="utf-8")


def test_defaults_match_bittensor() -> None:
    settings = config.resolve()
    assert (settings.name.value, settings.hotkey.value) == ("default", "default")
    assert settings.name.source is config.Source.DEFAULT
    assert settings.ref.directory == Path("~/.bittensor/wallets/default").expanduser()


def test_a_missing_config_file_is_not_an_error() -> None:
    assert config.resolve().name.source is config.Source.DEFAULT


# conjectures-miner owns this file; we read three fields and must tolerate the rest.
def test_the_miners_config_file_is_read(tmp_path: Path) -> None:
    _write(
        tmp_path,
        'wallet_name = "from-file"\n'
        'wallet_hotkey = "hk"\n'
        'api_base_url = "https://example.invalid"\n'
        'bittensor_network = "finney"\n',
    )
    settings = config.resolve()
    assert (settings.name.value, settings.name.source) == ("from-file", config.Source.FILE)
    assert settings.hotkey.value == "hk"


def test_a_malformed_config_file_falls_back_rather_than_crashing(tmp_path: Path) -> None:
    _write(tmp_path, "this is not = valid = toml\n")
    assert config.resolve().name.value == "default"


def test_env_beats_file(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    _write(tmp_path, 'wallet_name = "from-file"\n')
    monkeypatch.setenv(WALLET_ENV, "from-env")
    settings = config.resolve()
    assert (settings.name.value, settings.name.source) == ("from-env", config.Source.ENV)


def test_flag_beats_env(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    _write(tmp_path, 'wallet_name = "from-file"\n')
    monkeypatch.setenv(WALLET_ENV, "from-env")
    settings = config.resolve("from-flag")
    assert (settings.name.value, settings.name.source) == ("from-flag", config.Source.FLAG)


def test_a_non_string_setting_is_ignored(tmp_path: Path) -> None:
    _write(tmp_path, "wallet_name = 42\n")
    assert config.resolve().name.source is config.Source.DEFAULT
