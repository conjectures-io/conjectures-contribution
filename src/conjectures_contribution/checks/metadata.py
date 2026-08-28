from __future__ import annotations

from collections.abc import Iterator

from ..canonical import canonical_bytes
from ..model import METADATA_FILENAME
from .base import CheckContext, Finding, Severity
from .registry import register


@register("C001", "metadata schema is valid")
def metadata_schema(ctx: CheckContext) -> Iterator[Finding]:
    if ctx.parse_error is not None:
        yield Finding("C001", Severity.ERROR, ctx.parse_error, METADATA_FILENAME)


# json.loads silently keeps the last of a duplicated key, so a reviewer can read one
# target in the diff while the parser sees another. Byte equality with the canonical
# re-serialisation is what closes that, along with every other formatting trick.
@register("C013", "metadata.json is stored in canonical form")
def canonical_metadata(ctx: CheckContext) -> Iterator[Finding]:
    if ctx.raw is None or ctx.raw_bytes is None:
        return
    if ctx.raw_bytes != canonical_bytes(ctx.raw):
        yield Finding(
            "C013",
            Severity.ERROR,
            "not canonical JSON: expected indent=2, sorted keys, one trailing newline",
            METADATA_FILENAME,
        )
