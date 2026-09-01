from __future__ import annotations

from pathlib import Path

import pytest

from conjectures_contribution.cli import config

WALLET_ENV = f"{config.ENV_PREFIX}WALLET_NAME"
MINER_CONFIG_ENV = "CONJECTURES_CONFIG_FILE"
MINER_CONFIG_FILE = "config.toml"


@pytest.fixture(autouse=True)
def _isolated(  # pyright: ignore[reportUnusedFunction]
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    for name in ("WALLET_NAME", "WALLET_HOTKEY", "WALLET_PATH"):
        monkeypatch.delenv(f"{config.ENV_PREFIX}{name}", raising=False)
    monkeypatch.delenv(MINER_CONFIG_ENV, raising=False)
    monkeypatch.setenv(config.CONFIG_FILE_ENV, str(tmp_path / "contribution.toml"))


def _write(tmp_path: Path, body: str) -> None:
    (tmp_path / "contribution.toml").write_text(body, encoding="utf-8")


def _write_miner(tmp_path: Path, body: str) -> None:
    (tmp_path / MINER_CONFIG_FILE).write_text(body, encoding="utf-8")


def test_defaults_match_bittensor() -> None:
    settings = config.resolve()
    assert (settings.name.value, settings.hotkey.value) == ("default", "default")
    assert settings.name.source is config.Source.DEFAULT
    assert settings.ref.directory == Path("~/.bittensor/wallets/default").expanduser()


def test_the_default_config_file_is_ours_not_the_miners() -> None:
    assert config.DEFAULT_CONFIG_FILE.name == "contribution.toml"
    assert config.DEFAULT_CONFIG_FILE.parent == Path("~/.config/conjectures")


def test_a_missing_config_file_is_not_an_error() -> None:
    assert config.resolve().name.source is config.Source.DEFAULT


def test_our_own_config_file_is_read(tmp_path: Path) -> None:
    _write(tmp_path, 'wallet_name = "from-file"\nwallet_hotkey = "hk"\n')
    settings = config.resolve()
    assert (settings.name.value, settings.name.source) == ("from-file", config.Source.FILE)
    assert settings.hotkey.value == "hk"


# conjectures-miner declares its settings extra="forbid", so we could not share its file even
# if we wanted to: one unknown key of ours makes every miner command fail to load.
def test_the_miners_config_file_is_ignored(tmp_path: Path) -> None:
    _write_miner(tmp_path, 'wallet_name = "from-miner"\nwallet_hotkey = "miner-hk"\n')
    settings = config.resolve()
    assert settings.name.value == "default"
    assert settings.name.source is config.Source.DEFAULT


def test_the_miners_config_file_env_var_does_not_repoint_us(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    _write_miner(tmp_path, 'wallet_name = "from-miner"\n')
    monkeypatch.setenv(MINER_CONFIG_ENV, str(tmp_path / MINER_CONFIG_FILE))
    assert config.resolve().name.value == "default"


def test_unknown_keys_are_tolerated(tmp_path: Path) -> None:
    _write(
        tmp_path,
        'wallet_name = "from-file"\n'
        'api_base_url = "https://example.invalid"\n'
        "dev_signature = true\n",
    )
    assert config.resolve().name.value == "from-file"


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


def test_no_pinned_repo_by_default() -> None:
    assert config.pinned_repo() is None


def test_the_pinned_repo_is_read(tmp_path: Path) -> None:
    _write(tmp_path, f'repo_path = "{tmp_path}"\n')
    assert config.pinned_repo() == str(tmp_path)


def test_a_non_string_pinned_repo_is_ignored(tmp_path: Path) -> None:
    _write(tmp_path, "repo_path = 42\n")
    assert config.pinned_repo() is None


def test_the_config_keys_are_a_closed_set() -> None:
    assert {str(k) for k in config.ConfigKey} == {
        "wallet_name",
        "wallet_hotkey",
        "wallet_path",
        "repo_path",
        "author_key",
    }


def test_an_unknown_key_is_unrepresentable() -> None:
    with pytest.raises(ValueError, match="api_base_url"):
        config.ConfigKey("api_base_url")


def test_write_creates_the_parent_directory(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    target = tmp_path / "nested" / "deeper" / "contribution.toml"
    monkeypatch.setenv(config.CONFIG_FILE_ENV, str(target))
    config.write(config.ConfigKey.WALLET_NAME, "made-up")
    assert config.resolve().name.value == "made-up"


def test_a_value_with_quotes_and_backslashes_round_trips(tmp_path: Path) -> None:
    awkward = str(tmp_path / 'we"ird\\path')
    config.write(config.ConfigKey.REPO_PATH, awkward)
    assert config.pinned_repo() == awkward


def test_writing_a_second_key_preserves_the_first() -> None:
    config.write(config.ConfigKey.WALLET_NAME, "one")
    config.write(config.ConfigKey.WALLET_HOTKEY, "two")
    settings = config.resolve()
    assert (settings.name.value, settings.hotkey.value) == ("one", "two")


def test_unset_removes_one_key_and_leaves_the_rest() -> None:
    config.write(config.ConfigKey.WALLET_NAME, "one")
    config.write(config.ConfigKey.REPO_PATH, "/somewhere")
    config.unset(config.ConfigKey.REPO_PATH)
    assert config.pinned_repo() is None
    assert config.resolve().name.value == "one"


def test_unset_on_an_absent_key_is_not_an_error() -> None:
    config.unset(config.ConfigKey.REPO_PATH)
    assert config.pinned_repo() is None


# Tolerant on read, canonical on write: the file is ours and machine-managed, so a key we do
# not own does not survive the next `config set`.
def test_writing_drops_keys_we_do_not_own(tmp_path: Path) -> None:
    _write(tmp_path, 'wallet_name = "kept"\napi_base_url = "https://example.invalid"\n')
    config.write(config.ConfigKey.WALLET_HOTKEY, "hk")
    body = (tmp_path / "contribution.toml").read_text(encoding="utf-8")
    assert "api_base_url" not in body
    assert config.resolve().name.value == "kept"
