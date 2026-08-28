from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Self

from bittensor_core import (
    CRYPTO_SR25519,
    Keypair,
    deserialize_keypair_from_keyfile_data,
    keyfile_data_is_encrypted,
)

from .model import ContributionId, Reward, SchemaError, Signature, Ss58Address
from .reward import reward_message

DEFAULT_WALLET_PATH = Path("~/.bittensor/wallets")


class WalletError(RuntimeError):
    pass


@dataclass(frozen=True, slots=True)
class WalletRef:
    name: str
    hotkey: str
    path: Path

    @property
    def directory(self) -> Path:
        return self.path.expanduser() / self.name

    @property
    def coldkeypub(self) -> Path:
        return self.directory / "coldkeypub.txt"

    @property
    def hotkey_file(self) -> Path:
        return self.directory / "hotkeys" / self.hotkey

    @property
    def hotkeypub(self) -> Path:
        return self.directory / "hotkeys" / f"{self.hotkey}pub.txt"


@dataclass(frozen=True, slots=True, eq=False)
class RewardSigner:
    reward: Reward
    keypair: Keypair

    @classmethod
    def open(cls, ref: WalletRef) -> Self:
        return cls(reward=addresses(ref), keypair=_signing_hotkey(ref))

    def sign(self, contribution_id: ContributionId) -> Signature:
        return Signature(self.keypair.sign(reward_message(contribution_id)).hex())


def addresses(ref: WalletRef) -> Reward:
    coldkey = _address(ref.coldkeypub, "coldkey")
    # Wallets written by older btcli carry no hotkeypub.txt. The private hotkey is stored
    # unencrypted, so reading its address costs nothing and beats refusing the wallet.
    hotkey = _address(ref.hotkeypub if ref.hotkeypub.is_file() else ref.hotkey_file, "hotkey")
    try:
        return Reward(coldkey=coldkey, hotkey=hotkey)
    except SchemaError as exc:
        raise WalletError(f"{ref.directory}: {exc}") from None


def _address(path: Path, what: str) -> Ss58Address:
    try:
        raw = path.read_bytes()
    except FileNotFoundError:
        raise WalletError(f"{path}: no {what} in this wallet") from None
    except OSError as exc:
        raise WalletError(f"{path}: {exc.strerror}") from None
    try:
        return Ss58Address(str(deserialize_keypair_from_keyfile_data(raw).ss58_address))
    except (SchemaError, ValueError, TypeError) as exc:
        raise WalletError(f"{path}: not a readable {what} file ({exc})") from None


def _signing_hotkey(ref: WalletRef) -> Keypair:
    path = ref.hotkey_file
    try:
        raw = path.read_bytes()
    except FileNotFoundError:
        raise WalletError(f"{path}: no hotkey named '{ref.hotkey}' in this wallet") from None
    except OSError as exc:
        raise WalletError(f"{path}: {exc.strerror}") from None

    # Nothing in this tool prompts for a passphrase, so an encrypted hotkey is refused here
    # rather than left to surface as an unexplained C017 failure.
    if keyfile_data_is_encrypted(raw):
        raise WalletError(f"{path}: hotkey is encrypted; this tool does not prompt for a password")
    try:
        keypair = deserialize_keypair_from_keyfile_data(raw)
    except (ValueError, TypeError) as exc:
        raise WalletError(f"{path}: not a readable hotkey file ({exc})") from None
    if keypair.crypto_type != CRYPTO_SR25519:
        raise WalletError(f"{path}: reward signatures require an sr25519 hotkey")
    return keypair
