from __future__ import annotations

import re
from collections.abc import Iterator

from ..model import MAX_ARTIFACT_BYTES, Contribution
from .base import CheckContext, Finding, Severity, needs_contribution
from .registry import register

SOURCES_ARTIFACT = "sources.md"
SHORTENERS = frozenset(
    {"bit.ly", "tinyurl.com", "t.co", "goo.gl", "ow.ly", "is.gd", "buff.ly", "rb.gy"}
)
# Both repetitions are bounded. Unbounded ones backtrack quadratically, and an
# artifact is attacker-supplied text: a single long line would hang the scan.
URL_RE = re.compile(r"(?P<scheme>[a-zA-Z][a-zA-Z0-9+.-]{0,31})://(?P<host>[^/\s)\]>\"']{1,253})")
IPV4_RE = re.compile(r"^\d{1,3}(\.\d{1,3}){3}(:\d+)?$")
BOM = b"\xef\xbb\xbf"


def _artifact_bytes(ctx: CheckContext, contribution: Contribution) -> Iterator[tuple[str, bytes]]:
    for artifact in contribution.payload.artifacts:
        path = ctx.directory / str(artifact.name)
        if not path.is_file() or path.is_symlink() or path.stat().st_size > MAX_ARTIFACT_BYTES:
            continue
        yield str(artifact.name), path.read_bytes()


# The content hash is over bytes, so an editor that rewrites line endings or adds a
# BOM changes the contribution id. Normalising here means a miner on Windows finds
# out before signing rather than after CI rejects the signature.
@register("C022", "artifacts are LF-terminated text without a byte-order mark")
@needs_contribution
def line_endings(ctx: CheckContext, contribution: Contribution) -> Iterator[Finding]:
    for name, blob in _artifact_bytes(ctx, contribution):
        if blob.startswith(BOM):
            yield Finding("C022", Severity.ERROR, "starts with a UTF-8 byte-order mark", name)
        if b"\r" in blob:
            yield Finding("C022", Severity.ERROR, "uses CR or CRLF line endings; use LF", name)
        if blob and not blob.endswith(b"\n"):
            yield Finding("C022", Severity.ERROR, "does not end with a newline", name)


@register("C023", "sources.md attributes the work with citable links")
@needs_contribution
def sources_attribution(ctx: CheckContext, _contribution: Contribution) -> Iterator[Finding]:
    path = ctx.directory / SOURCES_ARTIFACT
    # An oversized artifact is C009's finding; scanning it here would be the DoS.
    if not path.is_file() or path.is_symlink() or path.stat().st_size > MAX_ARTIFACT_BYTES:
        return
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError):
        return

    body = [line.strip() for line in text.splitlines() if line.strip() and not line.startswith("#")]
    if not body:
        yield Finding(
            "C023",
            Severity.ERROR,
            "say where this came from — a paper, a Mathlib file, a prior contribution, "
            "or the words 'original work'",
            SOURCES_ARTIFACT,
        )

    for number, line in enumerate(text.splitlines(), start=1):
        for match in URL_RE.finditer(line):
            scheme = match.group("scheme").lower()
            host = match.group("host").lower()
            if scheme == "http":
                yield Finding(
                    "C023", Severity.ERROR, f"line {number}: use https for {host}", SOURCES_ARTIFACT
                )
            elif scheme != "https":
                yield Finding(
                    "C023",
                    Severity.ERROR,
                    f"line {number}: `{scheme}://` is not a link",
                    SOURCES_ARTIFACT,
                )
            if IPV4_RE.match(host):
                yield Finding(
                    "C023",
                    Severity.ERROR,
                    f"line {number}: a raw IP address is not a citation",
                    SOURCES_ARTIFACT,
                )
            if host.split(":")[0] in SHORTENERS:
                yield Finding(
                    "C023",
                    Severity.ERROR,
                    f"line {number}: {host} is a link shortener; cite the real URL",
                    SOURCES_ARTIFACT,
                )
