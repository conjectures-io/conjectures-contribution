from __future__ import annotations

import os
import secrets
from dataclasses import dataclass
from pathlib import Path
from typing import Self

from cryptography.exceptions import InvalidSignature
from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey, Ed25519PublicKey

from .model import PublicKey, Signature

SEED_BYTES = 32


class SigningError(RuntimeError):
    pass


def verify(message: bytes, key: PublicKey, signature: Signature) -> bool:
    try:
        public = Ed25519PublicKey.from_public_bytes(bytes.fromhex(key.value))
        public.verify(bytes.fromhex(signature.value), message)
    except (InvalidSignature, ValueError):
        return False
    return True


@dataclass(frozen=True, slots=True, eq=False)
class SigningKey:
    _private: Ed25519PrivateKey

    @classmethod
    def generate(cls) -> Self:
        return cls(Ed25519PrivateKey.from_private_bytes(secrets.token_bytes(SEED_BYTES)))

    @classmethod
    def load(cls, path: Path) -> Self:
        try:
            raw = path.read_text(encoding="utf-8").strip()
        except FileNotFoundError:
            raise SigningError(f"{path}: no signing key — run `contrib key generate`") from None
        if path.stat().st_mode & 0o077:
            raise SigningError(f"{path}: readable by group or others; run `chmod 600 {path}`")
        try:
            seed = bytes.fromhex(raw)
        except ValueError:
            raise SigningError(f"{path}: not a hex-encoded ed25519 seed") from None
        if len(seed) != SEED_BYTES:
            raise SigningError(f"{path}: expected a {SEED_BYTES}-byte seed, got {len(seed)}")
        return cls(Ed25519PrivateKey.from_private_bytes(seed))

    def save(self, path: Path) -> None:
        if path.exists():
            raise SigningError(f"{path}: already exists; refusing to overwrite a signing key")
        path.parent.mkdir(parents=True, exist_ok=True)
        fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
        with os.fdopen(fd, "w", encoding="utf-8") as handle:
            handle.write(self._seed().hex() + "\n")

    @property
    def public_key(self) -> PublicKey:
        raw = self._private.public_key().public_bytes(
            encoding=serialization.Encoding.Raw, format=serialization.PublicFormat.Raw
        )
        return PublicKey(raw.hex())

    def sign(self, message: bytes) -> Signature:
        return Signature(self._private.sign(message).hex())

    def _seed(self) -> bytes:
        return self._private.private_bytes(
            encoding=serialization.Encoding.Raw,
            format=serialization.PrivateFormat.Raw,
            encryption_algorithm=serialization.NoEncryption(),
        )
