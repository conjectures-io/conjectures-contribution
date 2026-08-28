from __future__ import annotations

import hashlib

from bittensor_core import Keypair, ss58_decode, ss58_encode

from .model import ContributionId, Signature, Ss58Address

# Shape and naming follow conjectures-miner's read_message: a versioned domain, a colon, the
# value, hashed, and the 32 raw bytes are what gets signed. The prefix is what stops a
# signature minted for one conjectures protocol from being replayed into another.
REWARD_DOMAIN = "conjectures-contribution-v1"

# Bittensor uses the generic substrate format. Pinned as a literal rather than imported: the
# constant has moved between bittensor major versions, and its value has not.
SS58_FORMAT = 42


def reward_message(contribution_id: ContributionId) -> bytes:
    return hashlib.sha256(f"{REWARD_DOMAIN}:{contribution_id}".encode()).digest()


def verify(contribution_id: ContributionId, hotkey: Ss58Address, signature: Signature) -> bool:
    try:
        keypair = Keypair(ss58_address=str(hotkey))
        return bool(keypair.verify(reward_message(contribution_id), bytes.fromhex(signature.value)))
    except (ValueError, TypeError):
        return False


# ss58_decode accepts any network's prefix and Keypair silently re-encodes it as 42, so a
# Polkadot address would round-trip into a Bittensor one that nobody wrote down. Only a string
# that survives the round trip unchanged names the account it appears to name.
def is_canonical(address: Ss58Address) -> bool:
    value = str(address)
    try:
        return bool(ss58_encode(ss58_decode(value), SS58_FORMAT) == value)
    except (ValueError, TypeError):
        return False
