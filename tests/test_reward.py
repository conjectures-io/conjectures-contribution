from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any

import pytest
from bittensor_core import (
    Keypair,
    encrypt_keyfile_data,
    serialized_keypair_to_keyfile_data,
    ss58_encode,
)

from conjectures_contribution import reward as reward_module
from conjectures_contribution.checks import Severity, run_all
from conjectures_contribution.loader import load_context
from conjectures_contribution.model import (
    METADATA_FILENAME,
    ContributionId,
    Reward,
    SchemaError,
    Ss58Address,
)
from conjectures_contribution.store import Published
from conjectures_contribution.wallet import RewardSigner, WalletError, WalletRef, addresses

from .conftest import COLDKEY_URI, HOTKEY_URI, Repo, make_repo, reward_signer


def _findings(repo: Repo, directory: Path) -> tuple[tuple[str, Severity], ...]:
    context = load_context(
        directory,
        contributions_root=repo.contributions,
        pool=repo.pool,
        published=Published.scan(repo.contributions),
    )
    return tuple((f.check_id, f.severity) for f in run_all(context))


def _errors(repo: Repo, directory: Path) -> tuple[str, ...]:
    return tuple(i for i, s in _findings(repo, directory) if s is Severity.ERROR)


def _raw(directory: Path) -> dict[str, Any]:
    raw: dict[str, Any] = json.loads((directory / METADATA_FILENAME).read_text())
    return raw


# --- the record ------------------------------------------------------------------------


def test_a_promoted_contribution_carries_a_verifiable_reward(repo: Repo) -> None:
    published = repo.promote()
    raw = _raw(published)

    assert raw["payload"]["reward"] == {
        "coldkey": str(repo.reward.reward.coldkey),
        "hotkey": str(repo.reward.reward.hotkey),
    }
    assert _findings(repo, published) == ()
    assert reward_module.verify(
        repo.read(published).contribution_id,
        repo.reward.reward.hotkey,
        repo.read(published).reward_signature or pytest.fail("no reward signature"),
    )


def test_opting_out_warns_but_does_not_fail(repo: Repo) -> None:
    published = repo.promote(reward=False)
    raw = _raw(published)

    assert raw["payload"]["reward"] is None
    assert raw["reward_signature"] is None
    assert _findings(repo, published) == (("C018", Severity.WARNING),)


# The reward addresses are hashed into the id, so the same draft under two destinations is
# two contributions. This is what makes the payout destination unforgeable after the fact.
def test_the_reward_destination_is_bound_into_the_id(repo: Repo) -> None:
    with_reward = repo.promote(repo.draft(title="With a destination"))
    without = repo.promote(
        repo.draft(title="Without one", files={"sources.md": "# Elsewhere\n"}), reward=False
    )
    assert with_reward.name != without.name


# --- C016: well-formedness --------------------------------------------------------------


def test_a_reward_without_a_signature_is_caught(repo: Repo) -> None:
    published = repo.promote()
    repo.rewrite_raw(published, lambda raw: {**raw, "reward_signature": None})
    assert _errors(repo, published) == ("C016",)


def test_a_signature_without_a_reward_is_caught(repo: Repo) -> None:
    published = repo.promote(reward=False)
    repo.rewrite_raw(published, lambda raw: {**raw, "reward_signature": "ab" * 64})
    assert "C016" in _errors(repo, published)


# ss58_decode accepts any network's prefix and Keypair silently re-encodes it as 42, so only
# a round-trip rejects an address that names a different chain's account.
def test_a_polkadot_format_address_is_rejected(repo: Repo) -> None:
    foreign = ss58_encode(bytes(Keypair.create_from_uri(COLDKEY_URI).public_key), 0)
    published = repo.resign(
        repo.promote(),
        reward=Reward(coldkey=Ss58Address(str(foreign)), hotkey=repo.reward.reward.hotkey),
    )
    assert _errors(repo, published) == ("C016",)


def test_a_corrupted_checksum_is_rejected(repo: Repo) -> None:
    good = str(repo.reward.reward.coldkey)
    broken = good[:-1] + ("2" if good[-1] != "2" else "3")
    published = repo.resign(
        repo.promote(),
        reward=Reward(coldkey=Ss58Address(broken), hotkey=repo.reward.reward.hotkey),
    )
    assert _errors(repo, published) == ("C016",)


def test_a_reward_paying_its_own_signer_is_rejected() -> None:
    hotkey = Ss58Address(str(Keypair.create_from_uri(HOTKEY_URI).ss58_address))
    with pytest.raises(SchemaError):
        Reward(coldkey=hotkey, hotkey=hotkey)


@pytest.mark.parametrize("value", ["", "not-an-address", "5Grwva", "0" * 48])
def test_malformed_addresses_are_rejected_by_shape(value: str) -> None:
    with pytest.raises(SchemaError):
        Ss58Address(value)


# --- C017: the signature ----------------------------------------------------------------


def test_a_signature_over_another_id_does_not_verify(repo: Repo) -> None:
    published = repo.promote()
    stolen = repo.reward.sign(repo.read(published).contribution_id)
    other = repo.promote(
        repo.draft(title="Another contribution", files={"sources.md": "# Elsewhere\n\n- Other.\n"})
    )
    repo.rewrite_raw(other, lambda raw: {**raw, "reward_signature": str(stolen)})
    assert _errors(repo, other) == ("C017",)


def test_a_signature_from_the_wrong_hotkey_does_not_verify(repo: Repo) -> None:
    published = repo.promote(signer=reward_signer("//Charlie"))
    forged = repo.reward.sign(repo.read(published).contribution_id)
    repo.rewrite_raw(published, lambda raw: {**raw, "reward_signature": str(forged)})
    assert _errors(repo, published) == ("C017",)


# C016 owns malformed addresses; C017 repeating the complaint would be noise.
def test_a_malformed_hotkey_reports_only_once(repo: Repo) -> None:
    broken = str(repo.reward.reward.hotkey)[:-1] + "2"
    published = repo.resign(
        repo.promote(),
        reward=Reward(coldkey=repo.reward.reward.coldkey, hotkey=Ss58Address(broken)),
    )
    assert _errors(repo, published) == ("C016",)


# --- the domain prefix ------------------------------------------------------------------


def test_the_signed_message_is_domain_separated() -> None:
    contribution_id = ContributionId("a" * 64)
    assert (
        reward_module.reward_message(contribution_id)
        == hashlib.sha256(f"conjectures-contribution-v1:{contribution_id}".encode()).digest()
    )


# A hotkey's signature over a bare id must not be accepted; without the prefix a signature
# minted for one conjectures protocol could be replayed into this one.
def test_a_signature_over_the_bare_id_is_rejected(repo: Repo) -> None:
    published = repo.promote()
    bare = repo.reward.keypair.sign(str(repo.read(published).contribution_id).encode()).hex()
    repo.rewrite_raw(published, lambda raw: {**raw, "reward_signature": bare})
    assert _errors(repo, published) == ("C017",)


# --- the wallet on disk ------------------------------------------------------------------


def _wallet(tmp_path: Path, *, hotkeypub: bool = True, encrypted: bool = False) -> WalletRef:
    directory = tmp_path / "wallets" / "demo"
    (directory / "hotkeys").mkdir(parents=True)
    cold = Keypair.create_from_uri(COLDKEY_URI)
    hot = Keypair.create_from_uri(HOTKEY_URI)
    (directory / "coldkeypub.txt").write_bytes(serialized_keypair_to_keyfile_data(cold))

    hotkey_data = serialized_keypair_to_keyfile_data(hot)
    if encrypted:
        hotkey_data = bytes(encrypt_keyfile_data(hotkey_data, "hunter2"))
    (directory / "hotkeys" / "main").write_bytes(hotkey_data)
    if hotkeypub:
        (directory / "hotkeys" / "mainpub.txt").write_bytes(serialized_keypair_to_keyfile_data(hot))
    return WalletRef(name="demo", hotkey="main", path=tmp_path / "wallets")


def test_a_wallet_yields_both_addresses(tmp_path: Path) -> None:
    found = addresses(_wallet(tmp_path))
    assert str(found.coldkey) == str(Keypair.create_from_uri(COLDKEY_URI).ss58_address)
    assert str(found.hotkey) == str(Keypair.create_from_uri(HOTKEY_URI).ss58_address)


# Wallets written by older btcli carry no hotkeypub.txt; the private hotkey is unencrypted,
# so refusing such a wallet would be a self-inflicted limitation.
def test_a_wallet_without_hotkeypub_falls_back_to_the_hotkey(tmp_path: Path) -> None:
    found = addresses(_wallet(tmp_path, hotkeypub=False))
    assert str(found.hotkey) == str(Keypair.create_from_uri(HOTKEY_URI).ss58_address)


def test_an_encrypted_hotkey_is_refused_rather_than_prompted(tmp_path: Path) -> None:
    with pytest.raises(WalletError, match="does not prompt"):
        RewardSigner.open(_wallet(tmp_path, encrypted=True))


def test_a_missing_wallet_names_the_path(tmp_path: Path) -> None:
    ref = WalletRef(name="absent", hotkey="main", path=tmp_path / "wallets")
    with pytest.raises(WalletError, match=r"coldkeypub\.txt"):
        addresses(ref)


# The coldkey holds funds and most miners do not keep it on the machine at all. Nothing in
# this tool may open it, so the file's absence must not affect anything.
def test_nothing_opens_the_private_coldkey(tmp_path: Path) -> None:
    ref = _wallet(tmp_path)
    (ref.directory / "coldkey").write_bytes(b"deliberately unreadable")
    signer = RewardSigner.open(ref)
    assert str(signer.reward.coldkey) == str(Keypair.create_from_uri(COLDKEY_URI).ss58_address)


def test_the_whole_wallet_round_trips_through_a_contribution(tmp_path: Path) -> None:
    repo = make_repo(tmp_path)
    published = repo.promote(signer=RewardSigner.open(_wallet(tmp_path)))
    assert _findings(repo, published) == ()
