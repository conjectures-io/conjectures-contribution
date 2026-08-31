from __future__ import annotations

import unicodedata
from collections.abc import Iterator

from ..model import (
    MAX_ARTIFACT_BYTES,
    MAX_ARTIFACTS,
    MAX_TOTAL_BYTES,
    METADATA_FILENAME,
    REQUIRED_ARTIFACT_SUFFIXES,
    REQUIRED_ARTIFACTS,
    Contribution,
    Sha256,
)
from .base import CheckContext, Finding, Severity, needs_contribution
from .registry import register

PERMITTED_CONTROLS = frozenset({"\t", "\n", "\r"})


@register("C007", "declared artifacts exist with matching size and digest")
@needs_contribution
def artifacts_match(ctx: CheckContext, contribution: Contribution) -> Iterator[Finding]:
    declared = {str(a.name) for a in contribution.payload.artifacts}
    for name in sorted(REQUIRED_ARTIFACTS - declared):
        yield Finding("C007", Severity.ERROR, f"required artifact '{name}' is not declared")

    for suffix in sorted(REQUIRED_ARTIFACT_SUFFIXES):
        if not any(name.endswith(suffix) for name in declared):
            yield Finding(
                "C007",
                Severity.ERROR,
                f"at least one '{suffix}' artifact is required; "
                "a contribution is Lean somebody else can use",
            )

    for artifact in contribution.payload.artifacts:
        path = ctx.directory / str(artifact.name)
        if not path.is_file() or path.is_symlink():
            yield Finding(
                "C007", Severity.ERROR, "declared artifact is missing", str(artifact.name)
            )
            continue
        actual_size = path.stat().st_size
        if actual_size != artifact.size:
            yield Finding(
                "C007",
                Severity.ERROR,
                f"size is {actual_size}, metadata declares {artifact.size}",
                str(artifact.name),
            )
        # An oversized file is C009's to report; hashing it here would be the DoS.
        if actual_size > MAX_ARTIFACT_BYTES:
            continue
        actual_digest = Sha256.of(path.read_bytes())
        if actual_digest != artifact.digest:
            yield Finding(
                "C007",
                Severity.ERROR,
                f"sha256 is {actual_digest}, metadata declares {artifact.digest}",
                str(artifact.name),
            )


@register("C008", "directory holds only the declared, safely named regular files")
@needs_contribution
def directory_safe(ctx: CheckContext, contribution: Contribution) -> Iterator[Finding]:
    expected = {METADATA_FILENAME} | {str(a.name) for a in contribution.payload.artifacts}
    for entry in sorted(ctx.directory.iterdir()):
        if entry.is_symlink():
            yield Finding("C008", Severity.ERROR, "symlinks are not permitted", entry.name)
            continue
        if entry.is_dir():
            yield Finding("C008", Severity.ERROR, "subdirectories are not permitted", entry.name)
            continue
        if not entry.is_file():
            yield Finding("C008", Severity.ERROR, "not a regular file", entry.name)
            continue
        if entry.name not in expected:
            yield Finding("C008", Severity.ERROR, "file is not declared in metadata", entry.name)


@register("C009", "size limits are respected")
@needs_contribution
def size_limits(ctx: CheckContext, contribution: Contribution) -> Iterator[Finding]:
    artifacts = contribution.payload.artifacts
    if len(artifacts) > MAX_ARTIFACTS:
        yield Finding(
            "C009", Severity.ERROR, f"{len(artifacts)} artifacts declared, limit is {MAX_ARTIFACTS}"
        )

    total = 0
    for artifact in artifacts:
        path = ctx.directory / str(artifact.name)
        if not path.is_file() or path.is_symlink():
            continue
        size = path.stat().st_size
        total += size
        if size == 0:
            yield Finding("C009", Severity.ERROR, "artifact is empty", str(artifact.name))
        if size > MAX_ARTIFACT_BYTES:
            yield Finding(
                "C009",
                Severity.ERROR,
                f"{size} bytes exceeds the {MAX_ARTIFACT_BYTES} byte per-file limit",
                str(artifact.name),
            )
    if total > MAX_TOTAL_BYTES:
        yield Finding(
            "C009", Severity.ERROR, f"{total} bytes total exceeds the {MAX_TOTAL_BYTES} byte limit"
        )


# Contributions are read by humans before they are trusted. Bidi overrides and other
# Cf characters let a Lean file render as something other than what the kernel sees.
@register("C014", "artifacts are UTF-8 text without control or bidi characters")
@needs_contribution
def artifacts_are_text(ctx: CheckContext, contribution: Contribution) -> Iterator[Finding]:
    for artifact in contribution.payload.artifacts:
        path = ctx.directory / str(artifact.name)
        if not path.is_file() or path.is_symlink() or path.stat().st_size > MAX_ARTIFACT_BYTES:
            continue
        try:
            text = path.read_bytes().decode("utf-8")
        except UnicodeDecodeError:
            yield Finding("C014", Severity.ERROR, "not valid UTF-8", str(artifact.name))
            continue
        offending = sorted(
            {
                ch
                for ch in text
                if ch not in PERMITTED_CONTROLS and unicodedata.category(ch) in {"Cc", "Cf"}
            }
        )
        if offending:
            codepoints = ", ".join(f"U+{ord(ch):04X}" for ch in offending)
            yield Finding(
                "C014",
                Severity.ERROR,
                f"control or bidi characters: {codepoints}",
                str(artifact.name),
            )
