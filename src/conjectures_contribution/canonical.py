from __future__ import annotations

import json
from typing import Any

from .model import ContributionId, Payload


# Byte-for-byte the serialisation conjectures-tasks publishes its digests over.
def canonical_bytes(value: Any) -> bytes:
    return json.dumps(value, indent=2, sort_keys=True).encode("utf-8") + b"\n"


def payload_bytes(payload: Payload) -> bytes:
    return canonical_bytes(payload.to_json())


def derive_id(payload: Payload) -> ContributionId:
    return ContributionId.of(payload_bytes(payload))
