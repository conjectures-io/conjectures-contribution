"""Two renderings of the same rows, dispatching on the column's type tag.

The table is for a terminal: a set is its size, a long key is truncated, a hole is `?`
and an absence is `—`. `--json` is for a pipe: full values, every column, both a hole and
an absence as `null`, and never a `0` standing in for either.
"""

from __future__ import annotations

import json
from collections.abc import Sequence
from typing import Any, assert_never, cast

from .columns import Column, ColumnType
from .query import Query
from .values import Date, Unavailable

HOLE = "?"
ABSENT = "—"
GAP = "  "


def render(rows: Sequence[Any], query: Query) -> str:
    return render_json(rows, query) if query.as_json else render_table(rows, query)


def render_json(rows: Sequence[Any], query: Query) -> str:
    return json.dumps(
        [{c.name: _as_json(c, c.get(row)) for c in query.projection} for row in rows],
        indent=2,
    )


def render_table(rows: Sequence[Any], query: Query) -> str:
    if not rows:
        return ""
    header = [c.name for c in query.projection]
    body = [[_as_text(c, c.get(row)) for c in query.projection] for row in rows]
    widths = [max(len(cell) for cell in column) for column in zip(header, *body, strict=True)]
    lines = [_line(header, widths), *(_line(cells, widths) for cells in body)]
    return "\n".join(lines) + "\n"


def _line(cells: Sequence[str], widths: Sequence[int]) -> str:
    return GAP.join(cell.ljust(width) for cell, width in zip(cells, widths, strict=True)).rstrip()


def _as_text(column: Column[Any], value: object) -> str:
    if isinstance(value, Unavailable):
        return HOLE
    if value is None:
        return ABSENT
    if column.type is ColumnType.STR:
        text = cast("str", value)
        return text[: column.width] if column.width is not None else text
    if column.type is ColumnType.INT:
        return str(cast("int", value))
    if column.type is ColumnType.DATE:
        return str(cast("Date", value))
    if column.type is ColumnType.BOOL:
        return "yes" if value else "no"
    if column.type is ColumnType.SET:
        return str(len(cast("tuple[object, ...]", value)))
    assert_never(column.type)


def _as_json(column: Column[Any], value: object) -> Any:
    if value is None or isinstance(value, Unavailable):
        return None
    if column.type is ColumnType.STR:
        return cast("str", value)
    if column.type is ColumnType.INT:
        return cast("int", value)
    if column.type is ColumnType.DATE:
        return str(cast("Date", value))
    if column.type is ColumnType.BOOL:
        return bool(value)
    if column.type is ColumnType.SET:
        return [str(item) for item in cast("tuple[object, ...]", value)]
    assert_never(column.type)
