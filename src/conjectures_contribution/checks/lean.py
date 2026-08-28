from __future__ import annotations

from collections.abc import Iterator

from ..lean import (
    ALLOWED_IMPORT_ROOTS,
    HEARTBEATS_RE,
    IMPORT_RE,
    LEAN_SUFFIX,
    MAX_DECLARATIONS,
    MAX_HEARTBEATS_REVIEW,
    REVIEW_IMPORT_ROOTS,
    RULES,
    Verdict,
    declarations,
    strip_comments,
)
from ..model import MAX_ARTIFACT_BYTES, Contribution
from .base import CheckContext, Finding, Severity, needs_contribution
from .registry import register

_SEVERITY = {Verdict.REJECT: Severity.ERROR, Verdict.REVIEW: Severity.REVIEW}


def _sources(ctx: CheckContext, contribution: Contribution) -> Iterator[tuple[str, str]]:
    for artifact in contribution.payload.artifacts:
        name = str(artifact.name)
        if not name.endswith(LEAN_SUFFIX):
            continue
        path = ctx.directory / name
        # Missing, oversized and non-UTF-8 artifacts are C007, C009 and C014's to
        # report; re-reporting them here would bury the finding that matters.
        if not path.is_file() or path.is_symlink() or path.stat().st_size > MAX_ARTIFACT_BYTES:
            continue
        try:
            yield name, path.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError):
            continue


@register("C019", "Lean sources execute no code and forge no proofs")
@needs_contribution
def lean_constructs(ctx: CheckContext, contribution: Contribution) -> Iterator[Finding]:
    for name, text in _sources(ctx, contribution):
        for number, line in enumerate(strip_comments(text), start=1):
            for rule in RULES:
                if rule.pattern.search(line):
                    yield Finding(
                        "C019", _SEVERITY[rule.verdict], f"line {number}: {rule.message}", name
                    )
            budget = HEARTBEATS_RE.search(line)
            if budget and int(budget.group(1)) > MAX_HEARTBEATS_REVIEW:
                yield Finding(
                    "C019",
                    Severity.REVIEW,
                    f"line {number}: `maxHeartbeats {budget.group(1)}` is a long budget",
                    name,
                )


@register("C020", "Lean imports are on the allowlist")
@needs_contribution
def lean_imports(ctx: CheckContext, contribution: Contribution) -> Iterator[Finding]:
    permitted = ", ".join(sorted(ALLOWED_IMPORT_ROOTS))
    for name, text in _sources(ctx, contribution):
        for number, line in enumerate(strip_comments(text), start=1):
            match = IMPORT_RE.match(line)
            if match is None:
                continue
            module = match.group(1)
            root = module.split(".", 1)[0]
            if root in REVIEW_IMPORT_ROOTS:
                yield Finding(
                    "C020",
                    Severity.REVIEW,
                    f"line {number}: `import {module}` pulls in the metaprogramming API",
                    name,
                )
            elif root not in ALLOWED_IMPORT_ROOTS:
                yield Finding(
                    "C020",
                    Severity.ERROR,
                    f"line {number}: `import {module}` is not on the allowlist ({permitted})",
                    name,
                )


# Each file is elaborated on its own, against the pool's Lean environment. A file
# that declares nothing cannot help anyone; a declaration at the root namespace
# collides with Mathlib and with every other contribution to the same target.
@register("C021", "Lean sources declare something, inside a namespace of their own")
@needs_contribution
def lean_declarations(ctx: CheckContext, contribution: Contribution) -> Iterator[Finding]:
    seen: dict[str, str] = {}
    for name, text in _sources(ctx, contribution):
        names = declarations(text)
        if not names:
            yield Finding("C021", Severity.ERROR, "declares nothing", name)
        if len(names) > MAX_DECLARATIONS:
            yield Finding(
                "C021",
                Severity.ERROR,
                f"{len(names)} declarations exceeds the limit of {MAX_DECLARATIONS}",
                name,
            )
        unqualified = [n for n in names if "." not in n]
        if unqualified:
            listed = ", ".join(unqualified[:5])
            yield Finding(
                "C021",
                Severity.REVIEW,
                f"declares {listed} at the root namespace; wrap the file in a `namespace`",
                name,
            )
        for declared in names:
            other = seen.get(declared)
            if other is not None:
                yield Finding(
                    "C021", Severity.ERROR, f"`{declared}` is also declared in {other}", name
                )
            else:
                seen[declared] = name
