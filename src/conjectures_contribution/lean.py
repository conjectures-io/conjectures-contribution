"""Syntactic analysis of Lean sources.

Elaborating Lean is arbitrary code execution: `#eval`, `initialize`, `run_cmd` and
`@[extern]` all run at compile time, and `native_decide` and `axiom` forge proofs
the kernel never sees. This module is the gate that runs before any of that
reaches a runner. It is deliberately syntactic — a filter, not a proof of safety;
the elaboration stage still applies a timeout, a memory cap and network isolation.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from enum import StrEnum

LEAN_SUFFIX = ".lean"

ALLOWED_IMPORT_ROOTS = frozenset(
    {
        "Mathlib",
        "Std",
        "Init",
        "Batteries",
        "Aesop",
        "Qq",
        "Plausible",
        "ProofWidgets",
        "ImportGraph",
        "FormalConjectures",
        "TaskSupport",
    }
)
REVIEW_IMPORT_ROOTS = frozenset({"Lean"})
MAX_HEARTBEATS_REVIEW = 1_000_000
MAX_DECLARATIONS = 200
RESERVED_NAMESPACE = "Bounty"


class Verdict(StrEnum):
    REJECT = "reject"
    REVIEW = "review"


@dataclass(frozen=True, slots=True)
class Rule:
    code: str
    verdict: Verdict
    pattern: re.Pattern[str]
    message: str


def _rule(code: str, verdict: Verdict, pattern: str, message: str) -> Rule:
    return Rule(code, verdict, re.compile(pattern), message)


RULES: tuple[Rule, ...] = (
    # -- proof integrity --------------------------------------------------
    _rule(
        "sorry",
        Verdict.REJECT,
        r"(?<![\w.])sorry(?![\w])",
        "`sorry` leaves a hole; a contribution must compile without one",
    ),
    _rule(
        "sorry",
        Verdict.REJECT,
        r"(?<![\w.])(admit|sorryAx)(?![\w])",
        "`admit`/`sorryAx` leaves a hole; a contribution must compile without one",
    ),
    _rule(
        "axiom",
        Verdict.REJECT,
        r"^\s*(@\[[^\]]*\]\s*)*axiom(?![\w])",
        "`axiom` can introduce an inconsistency that silently 'proves' the target",
    ),
    _rule(
        "native",
        Verdict.REJECT,
        r"(?<![\w.])native_decide(?![\w])",
        "`native_decide` trusts the compiler instead of the kernel",
    ),
    _rule(
        "native",
        Verdict.REJECT,
        r"(?<![\w])Lean\.ofReduceBool(?![\w])",
        "`Lean.ofReduceBool` is the `native_decide` trust hole",
    ),
    _rule(
        "kernel",
        Verdict.REJECT,
        r"set_option\s+debug\.",
        "`set_option debug.*` can disable kernel type checking",
    ),
    _rule(
        "heartbeats",
        Verdict.REJECT,
        r"set_option\s+maxHeartbeats\s+0(?![\d])",
        "`maxHeartbeats 0` removes the elaboration bound; give an explicit budget",
    ),
    # -- code execution ---------------------------------------------------
    _rule("eval", Verdict.REJECT, r"#eval!?(?![\w])", "`#eval` executes code at elaboration time"),
    _rule(
        "eval",
        Verdict.REJECT,
        r"(?<![\w])(run_cmd|run_elab)(?![\w])",
        "`run_cmd`/`run_elab` executes code at elaboration time",
    ),
    _rule("eval", Verdict.REJECT, r"#exit(?![\w])", "`#exit` halts elaboration"),
    _rule(
        "initialize",
        Verdict.REJECT,
        r"^\s*(builtin_)?initialize(?![\w])",
        "top-level `initialize` runs IO whenever the module is imported",
    ),
    _rule(
        "unsafe", Verdict.REJECT, r"(?<![\w])unsafe(?![\w])", "`unsafe` bypasses the type system"
    ),
    _rule(
        "ffi",
        Verdict.REJECT,
        r"@\[\s*[^\]]*\b(extern|implemented_by|init|builtin_init)\b",
        "FFI and implementation-swapping attributes are not accepted",
    ),
    # -- host access ------------------------------------------------------
    _rule(
        "io",
        Verdict.REJECT,
        r"(?<![\w])IO\.(FS|Process|Ref|getEnv|setEnv|rand|Channel)",
        "filesystem, process and environment access are not accepted",
    ),
    _rule(
        "io",
        Verdict.REJECT,
        r"(?<![\w])System\.(FilePath|Platform|Uri)(?![\w])",
        "filesystem and platform access are not accepted",
    ),
    _rule(
        "io",
        Verdict.REJECT,
        r":\s*IO\s+(Unit|Bool|String|Nat|\()",
        "definitions in the `IO` monad are not accepted",
    ),
    # -- reserved names ---------------------------------------------------
    _rule(
        "reserved",
        Verdict.REJECT,
        rf"^\s*namespace\s+{RESERVED_NAMESPACE}(?![\w])",
        f"`{RESERVED_NAMESPACE}` is the task's own namespace; pick your own",
    ),
    _rule(
        "reserved",
        Verdict.REJECT,
        rf"(?<![\w]){RESERVED_NAMESPACE}\.target(?![\w])",
        "a contribution must not define or reference the task's `Bounty.target`",
    ),
    # -- allowed, but read by a human -------------------------------------
    _rule(
        "metaprogram",
        Verdict.REVIEW,
        r"^\s*(scoped\s+|local\s+)*(macro|macro_rules|elab|elab_rules|syntax|"
        r"declare_syntax_cat|notation)(?![\w])",
        "metaprogramming or syntax extension — allowed, but a human reads this one",
    ),
    _rule(
        "attribute",
        Verdict.REVIEW,
        r"^\s*attribute\s+\[",
        "a global `attribute` changes behaviour for every downstream import",
    ),
    _rule(
        "open-lean",
        Verdict.REVIEW,
        r"^\s*open\s+Lean(?![\w])",
        "`open Lean` exposes the metaprogramming API",
    ),
)

DECLARATION_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+|nonrec\s+|scoped\s+|local\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque|alias)"
    r"\s+([^\s:{(\[⟨]+)"
)
NAMESPACE_RE = re.compile(r"^\s*namespace\s+([\w.«».']+)")
SECTION_RE = re.compile(r"^\s*section(?:\s+([\w.«».']+))?\s*$")
END_RE = re.compile(r"^\s*end(?:\s+([\w.«».']+))?\s*$")
IMPORT_RE = re.compile(r"^\s*import\s+([\w.«».']+)")
HEARTBEATS_RE = re.compile(r"set_option\s+maxHeartbeats\s+(\d+)")


# Prose is allowed to say "sorry"; code is not. Blanking comments in place keeps
# line numbers, which is what the diff annotations point at.
def strip_comments(text: str) -> list[str]:
    stripped: list[str] = []
    depth = 0
    for line in text.split("\n"):
        buffer: list[str] = []
        index = 0
        while index < len(line):
            pair = line[index : index + 2]
            if depth == 0 and pair == "--":
                break
            if pair == "/-":
                depth += 1
                buffer.append("  ")
                index += 2
                continue
            if pair == "-/" and depth > 0:
                depth -= 1
                buffer.append("  ")
                index += 2
                continue
            buffer.append(" " if depth else line[index])
            index += 1
        stripped.append("".join(buffer))
    return stripped


# Fully-qualified names, in source order. The index publishes these so the next
# miner can see what a contribution provides without opening it.
def declarations(text: str) -> tuple[str, ...]:
    names: list[str] = []
    scopes: list[str | None] = []
    for line in strip_comments(text):
        namespace = NAMESPACE_RE.match(line)
        if namespace:
            scopes.append(namespace.group(1))
            continue
        if SECTION_RE.match(line):
            scopes.append(None)
            continue
        if END_RE.match(line):
            if scopes:
                scopes.pop()
            continue
        declaration = DECLARATION_RE.match(line)
        if declaration:
            prefix = ".".join(scope for scope in scopes if scope)
            name = declaration.group(1)
            names.append(f"{prefix}.{name}" if prefix else name)
    return tuple(names)
