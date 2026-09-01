"""What the corpus could not read, and which question it might have spoiled.

Deliberately not `checks.Finding`: a finding is keyed by check id, a note by the source
path that failed. Merging them would leave one of the two carrying a field it never fills.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import StrEnum


class Level(StrEnum):
    ERROR = "error"
    # A row we could not build at all: the answer is missing something.
    WARNING = "warning"
    # A source we read, but which predates this tool: the rows are there and some of
    # their fields are holes. A different sentence, and a different remedy.
    NOTICE = "notice"


@dataclass(frozen=True, slots=True)
class Note:
    level: Level
    source: str
    message: str
    # The target whose row this failure cost us, when it cost us one. A note that names
    # no slug is about the corpus as a whole and is never scoped away.
    slug: str | None = None
