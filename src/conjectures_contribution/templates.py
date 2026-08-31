"""Text `contrib new` scaffolds.

Kept here rather than in the CLI so the checks can recognise their own
scaffolding: a draft promoted without editing it is a contribution that passes
every structural rule while saying nothing, which is exactly the submission the
rules exist to catch.
"""

from __future__ import annotations

SOURCES_FILENAME = "sources.md"
SCRIPT_FILENAME = "script.lean"

SOURCES_TEMPLATE = """# Sources

Cite what this builds on: papers, Mathlib declarations, prior contributions.
"""

SCRIPT_TEMPLATE = """import Mathlib

/-!
# {slug}

Say what this file provides, and why it helps someone attacking the target.
-/

namespace Contribution.{namespace}

-- Replace this with the lemma you actually want to share.
theorem placeholder : True := trivial

end Contribution.{namespace}
"""

# Substrings that only survive when a contributor never edited the scaffold. Matched
# on the stripped line, so reflowing or indenting the text does not slip past.
PLACEHOLDERS: tuple[str, ...] = (
    "Cite what this builds on: papers, Mathlib declarations, prior contributions.",
    "Say what this file provides, and why it helps someone attacking the target.",
    "Replace this with the lemma you actually want to share.",
    "theorem placeholder : True := trivial",
)


def namespace_for(slug: str) -> str:
    """`erdos-100-parts-i` -> `Erdos100PartsI`, so the scaffold names itself."""
    return "".join(part.capitalize() for part in slug.split("-") if part) or "Draft"
