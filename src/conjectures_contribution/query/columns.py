"""A column declared once: its name, type, source, and how to read it off a row.

Everything downstream is derived from this table — `--json` keys, table headers, the
`--sort` and `--is` vocabularies, completion, and which sources a query has to load. The
`ColumnType` tag is what buys back the value type the heterogeneous tuple loses.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from enum import StrEnum
from typing import Generic, TypeVar

from .values import Source


class ColumnType(StrEnum):
    STR = "str"
    INT = "int"
    DATE = "date"
    BOOL = "bool"
    # Filter is membership, sort is size, the table shows the count and `--json` the
    # elements. Fixed once here so no future set column re-litigates them.
    SET = "set"


R = TypeVar("R")


@dataclass(frozen=True, slots=True)
class Column(Generic[R]):
    name: str
    type: ColumnType
    get: Callable[[R], object]
    help: str
    source: Source = Source.TREE
    width: int | None = None
