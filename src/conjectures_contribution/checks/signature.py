from __future__ import annotations

from collections.abc import Iterator

from .. import signing
from ..canonical import payload_bytes
from ..model import METADATA_FILENAME, Contribution
from .base import CheckContext, Finding, Severity, needs_contribution
from .registry import register


@register("C006", "author signature verifies over the payload")
@needs_contribution
def signature_valid(_ctx: CheckContext, contribution: Contribution) -> Iterator[Finding]:
    payload = contribution.payload
    if not signing.verify(payload_bytes(payload), payload.author, contribution.signature):
        yield Finding(
            "C006",
            Severity.ERROR,
            f"signature does not verify under author key {payload.author}",
            METADATA_FILENAME,
        )
