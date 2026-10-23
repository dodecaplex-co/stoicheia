"""Prepare Jev's audit questions for Stoicheia's Books I and II.

The questions compare Heath's enunciations with the Lean statements and their declared
scope; inspect citation and hypothesis use in individual proof units; ask whether the
representation bridges state the conditional connections; compare the commentary with
its named declarations and declared route; and inspect the Heath figures and captions.
Bridge dependency placement is supplied as context in bridge_placement but is not itself
adjudicated; a bridge-stated answer does not establish all of P13.
They do not check proofs in Lean, verify historical quotations, or inspect the figures
at a glance. Helper signatures expose their use, not the work inside their proofs.
Ten synthetic defect controls change generated rows only. Expectations report the
review records' claims and remain local, as do provenance, mutations and coverage.

Run from anywhere with Python 3.11 or later, using only the standard library, the
repository's heath.py and jev.py, imported by path, and the comment reader the scripts
share, `comment_end`, taken alone from the repository's check_fidelity.py:

    python3 scripts/audit/jev_questions.py --commit REV
    python3 scripts/audit/jev_questions.py --commit REV --check
    python3 scripts/audit/jev_questions.py --commit REV --out PATH

Generation reads no credentials and sends nothing. Every evidence file is compared with
`git show REV:path`; every excerpt records its exact source slice and hash. Failure to read
the committed evidence, missing evidence, ambiguous names and differences from the revision
are errors. Evidence paths must be relative, without parent traversal or symlinks, and
resolve inside the repository. Both helpers' paths pass those checks, and must name regular
files, before either helper runs; so does the reader's, before it is defined. Each Lean
file's header is read by a small parser following Lean 4.35's grammar, before any masking:
an optional `module`, then imports in the four forms
`import`, `public import`, `meta import` and `public meta import`, each naming one module of
plain or «...» components and ending its line, with ordinary comments between the words. A
doc comment or any other word before an import, `prelude`, `import all`, a block comment
running on from an import's line, and any `import` after the header outside a «...» name are
refused. Both output paths reject symlinks,
evidence files, tracked files other than the two default outputs, Git metadata, protected
paths independently of the index, and collisions with each other; an output may be
outside the repository.
Both outputs are assembled and validated before either is written, using temporary
files and replacement without following a final symlink.
The checks cover links and aliases present when it runs, not a concurrent writer racing
it in the same tree.
--commit REV --check regenerates twice in memory and compares the bytes with both files
on disk. The manifest stays beside this script's default output,
including when --out selects another questions file. States over 12,000 characters are
labelled locally, never shortened; option orders rotate independently for ordinary rows
and controls. Keep the input and manifest beside any later answers: the client does not
copy these local provenance fields into its results.
"""

from __future__ import annotations

import argparse
import ast
import copy
import hashlib
import importlib.util
import json
import os
import re
import stat
import subprocess
import sys
import tempfile
import tomllib
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Any

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
OUTPUT = ROOT / 'docs/reports/acceptance/jev/audit-books-I-II.jsonl'
MANIFEST = OUTPUT.with_name('audit-books-I-II-manifest.json')
DEFAULT_OUTPUTS = (OUTPUT, MANIFEST)
LIMIT = 12000


class Refusal(ValueError):
    """Evidence that cannot support a reproducible question set."""


def require(condition: Any, message: str) -> None:
    if not condition:
        raise Refusal(message)


def dumps(value: Any) -> str:
    return json.dumps(value, ensure_ascii=False, allow_nan=False)


def sha(data: bytes | str) -> str:
    return 'sha256:' + hashlib.sha256(data.encode('utf-8') if isinstance(data, str) else data).hexdigest()


def relative(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def checked_path(path: Path) -> Path:
    """Reject symlinks throughout a path before resolving it, including missing leaves."""
    path = path.absolute()
    current = Path(path.anchor)
    for part in path.parts[1:]:
        current /= part
        try:
            mode = current.lstat().st_mode
        except FileNotFoundError:
            continue
        require(not stat.S_ISLNK(mode), f'{path}: symlink component {current}')
    return path.resolve()


def evidence_path(path: str) -> Path:
    local = Path(path)
    require(not local.is_absolute() and '..' not in local.parts,
            f'{path}: evidence path must be relative with no .. component')
    resolved = checked_path(ROOT / local)
    require(resolved.is_relative_to(ROOT), f'{path}: evidence path resolves outside the repository')
    return resolved


def read_no_follow(path: Path) -> bytes:
    """Refuse a final symlink even if it appeared after the component checks."""
    with os.fdopen(os.open(path, os.O_RDONLY | os.O_NOFOLLOW), 'rb') as stream:
        return stream.read()


HELPERS = (('jev_questions_heath', 'scripts/heath.py'),
           ('jev_questions_client', 'scripts/audit/jev.py'))


def helper_modules(helpers: tuple[tuple[str, str], ...]) -> list:
    """Check every helper's path, then read and compile each, before any helper runs."""
    checked = []
    for name, path in helpers:
        resolved = evidence_path(path)
        require(resolved.is_file(), f'{path}: helper module is missing or not a regular file')
        checked.append((name, path, resolved))
    # Each helper runs from the bytes read here, never through a final symlink.
    code = [(name, path, resolved, compile(read_no_follow(resolved), str(resolved), 'exec',
                                           dont_inherit=True))
            for name, path, resolved in checked]
    result = []
    for name, path, resolved, compiled in code:
        spec = importlib.util.spec_from_file_location(name, resolved)
        require(spec is not None, f'cannot import {path}')
        loaded = importlib.util.module_from_spec(spec)
        sys.modules[name] = loaded
        exec(compiled, loaded.__dict__)
        result.append(loaded)
    return result


# check_fidelity's reader of where a Lean comment ends, shared with it (#206). The file
# imports heath and generated_counts by name, which a generator run by path, as with
# `python3 -I`, cannot import, so the function is taken alone and nothing else of it runs.
READER = ('jev_questions_reader', 'scripts/check_fidelity.py', 'comment_end')


def shared_function(name: str, path: str, function: str):
    """Check a helper's path, then define its top-level `function` alone, from the bytes
    read."""
    resolved = evidence_path(path)
    require(resolved.is_file(), f'{path}: helper module is missing or not a regular file')
    tree = ast.parse(read_no_follow(resolved), str(resolved))
    found = [node for node in tree.body
             if isinstance(node, ast.FunctionDef) and node.name == function]
    require(len(found) == 1, f'{path}: defines no single function {function}')
    namespace = {'__name__': name}
    exec(compile(ast.Module(found, type_ignores=[]), str(resolved), 'exec', dont_inherit=True),
         namespace)
    return namespace[function]


try:
    heath, jev = helper_modules(HELPERS)
    shared_comment_end = shared_function(*READER)
except (Refusal, OSError) as error:
    if __name__ != '__main__':
        raise
    raise SystemExit(f'refused: {error}') from None


class Evidence:
    def __init__(self, commit: str):
        require(re.fullmatch(r'[0-9a-f]{40}', commit), '--commit requires a full commit hash')
        self.commit = commit
        self.data: dict[str, bytes] = {}

    def read(self, path: str) -> str:
        if path not in self.data:
            raw = read_no_follow(evidence_path(path))
            try:
                result = subprocess.run(['git', 'show', f'{self.commit}:{path}'], cwd=ROOT,
                                        capture_output=True, check=False)
            except OSError as error:
                raise Refusal(f'git show could not read committed evidence for {path}: {error}') from error
            if result.returncode:
                reason = result.stderr.decode('utf-8', errors='replace')
                raise Refusal(f'git show failed for {path}: {reason.strip()}')
            require(result.stdout == raw, f'{path}: differs from evidence commit {self.commit}')
            self.data[path] = raw
        return self.data[path].decode('utf-8')

    def excerpt(self, source: dict, field: str, path: str, start: int, end: int,
                *, transformation: str | None = None) -> str:
        raw = self.read(path)
        require(0 <= start < end <= len(raw), f'{path}: invalid excerpt {start}:{end}')
        text = raw[start:end]
        entry = {'field': field, 'path': path, 'start': start, 'end': end,
                 'lines': [raw.count('\n', 0, start) + 1, raw.count('\n', 0, end - 1) + 1],
                 'sha256': sha(text)}
        if transformation:
            entry['transformation'] = transformation
        source['excerpts'].append(entry)
        return text

    def whole(self, source: dict, field: str, path: str) -> str:
        return self.excerpt(source, field, path, 0, len(self.read(path)))

    def unchanged(self) -> None:
        for path, raw in self.data.items():
            require(read_no_follow(evidence_path(path)) == raw, f'{path}: changed during generation')


# A small source lexer, not a Lean elaborator. Masking preserves offsets and line breaks.
# Strings, nested comments and balanced binders cannot terminate a signature.
# Lean 4.35's name characters (Init/Meta/Defs.lean, isIdFirst and isIdRest): a name begins
# with an ASCII letter, `_` or a letter-like character, and goes on with these, ASCII digits,
# `'`, `!`, `?` and subscripts. The ranges are written as `re` escapes, in Lean's hex values.
LETTER_LIKE = ('\\u03b1-\\u03ba\\u03bc-\\u03c9\\u0391-\\u039f\\u03a1\\u03a2\\u03a4-\\u03a9'
               '\\u03ca-\\u03fb\\u1f00-\\u1ffe\\u2100-\\u214f\\U0001d49c-\\U0001d59f'
               '\\u00c0-\\u00d6\\u00d8-\\u00f6\\u00f8-\\u00ff\\u0100-\\u017f')
SUBSCRIPTS = '\\u2080-\\u2089\\u2090-\\u209c\\u1d62-\\u1d6a\\u2c7c'
NAME_REST = 'A-Za-z_' + LETTER_LIKE + "0-9'!?" + SUBSCRIPTS
IDENT = '[A-Za-z_' + LETTER_LIKE + '][' + NAME_REST + ']*'
LEAN_NAME = re.compile(IDENT)
NAME = IDENT + r'(?:\.' + IDENT + r')*'
TOKEN = re.compile(NAME)
MODULE_COMPONENT = r'(?:' + IDENT + r'|«[^»\n]+»)'
MODULE_NAME = re.compile(MODULE_COMPONENT + r'(?:\.' + MODULE_COMPONENT + r')*')
MODULE_PART = re.compile(MODULE_COMPONENT)
KEYWORD_LEFT = r'(?<![' + NAME_REST + r'.«])'
KEYWORD_RIGHT = r'(?![' + NAME_REST + r'»])'
COMMAND = re.compile(
    r'^(?:@\[[^\n]*?\]\s*)?(?:(?:private|protected|noncomputable|unsafe)\s+)*'
    r'(theorem|lemma|def|abbrev|axiom|opaque|structure|inductive|instance|example|'
    r'namespace|section|end|open|variable|notation\S*|infix\S*|prefix\S*|'
    r'postfix\S*|attribute|set_option)\b', re.M)
# Lean 4.35's module header (Lean/Parser/Module/Syntax.lean) is an optional `module`, an
# optional `prelude`, then any number of imports, each `[public] [meta] import [all] M`. The
# generator reads the subset without `prelude` and `all`, each import ending its line.
HEADER_WORDS = frozenset({'module', 'prelude', 'public', 'meta', 'all', 'import'})
IMPORT_WORD = re.compile(KEYWORD_LEFT + 'import' + KEYWORD_RIGHT)
QUOTED_NAME = re.compile(r'«[^»\n]*»')
# A command that can declare a token: a notation whose words before `=>` hold a bar could make
# a bar an operator, and one whose token joins a name character to another, as `-x` does,
# could end a word where the patterns below see none; a macro, an elaborator or a binder
# predicate can give any syntax a meaning.
SYNTAX_WORD = re.compile(KEYWORD_LEFT
                         + r'(?:notation|infixl|infixr|infix|prefix|postfix'
                         + r'|(macro_rules|macro|elab_rules|elab|binder_predicate))'
                         + KEYWORD_RIGHT)
# A character of a name, to Lean or to the patterns' \w.
NAME_CHARACTER = re.compile(r'[\w' + NAME_REST + ']')
# The whitespace Lean reads between tokens (Lean/Parser/Basic.lean, `whitespace`, which refuses
# a tab and a carriage return), narrower than Python's: a no-break space may stand in a token.
WHITESPACE = ' \n'
# The tokens of Lean 4.35's token table (Lean.Parser.getTokenTable; toolchain 4.35.0, commit
# eb6cafb7) that begin with a letter or `_`: 282 of the 507 that the toolchain's `lean` lists
# on a scratch file importing Lean, Std and Lake (Lake.DSL adds none). Lean reads one as a
# keyword where it begins a name and is at least as long as the name, as `trace[` is.
KEYWORD_TOKENS = frozenset('''
    EStack⟨ Macro.trace[ Prop Sort StateRefT Type _ abbrev add_decl_doc assert!
    assert_not_exists assert_not_imported at attribute aux_def axiom bif
    binder_predicate binop% binop_lazy% binrel% binrel_no_prop% break
    builtin_cbv_simproc builtin_cbv_simproc_decl builtin_cbv_simproc_pattern%
    builtin_dsimproc builtin_dsimproc_decl builtin_grind_propagator builtin_initialize
    builtin_simproc builtin_simproc_decl builtin_simproc_pattern% by by? by_elab calc
    catch cbv_eval cbv_simproc cbv_simproc_decl cbv_simproc_pattern% class clear%
    coinductive coinductive_fixpoint continue date( datespec( datetime( dbg_trace
    debug_assert! decl_name% declare_bitwise_int_theorems declare_bitwise_uint_theorems
    declare_command_config_elab declare_command_config_elab_legacy declare_config_elab
    declare_config_elab_legacy declare_core_config_elab declare_eval_bin
    declare_eval_bin_bitwise declare_eval_bin_bool_pred declare_int_theorems
    declare_simp_like_tactic declare_sint_simprocs declare_syntax_cat
    declare_term_config_elab declare_uint_simprocs declare_uint_theorems decreasing_by
    def def_eval_config_item default_or_ofNonempty% deprecated_module deprecated_syntax
    deriving do docs_to_verso dsimproc dsimproc_decl elab elabToSyntax% elab_rules
    elab_stx_quot else end ensure_expected_type% ensure_type_of% estack⟨ eval_prec
    eval_prio exact?% example exists export extends f! finally for for_in% for_in'%
    forall from fun gen_injective_theorems% generalizing grind_annotated grind_pattern
    grind_propagator have haveI hiding hydrate_opaque_type idbg if import in include
    include_str inductive inductive_fixpoint inferInstanceAs infix infixl infixr
    init_grind_norm init_quot initialize instance json% leading_parser leftact% let letI
    let_delayed let_expr let_fun let_mvar% let_tmp let_λ local logNamedError
    logNamedErrorAt logNamedWarning logNamedWarningAt m! macro macro_rules match
    match_expr matches max_prec meta mod_cast monotonicity_by mut mutual namespace
    nat_lit no_error_if_unused% no_implicit_lambda% no_index nofun nomatch noncomputable
    nonempty_type nonrec norm_cast_add_elim notation offset( omit opaque open panic!
    partial partial_fixpoint postfix prefix println! private private_decl% protected
    public recall recall? recommended_spelling register_builtin_option
    register_error_explanation register_grind_attr register_label_attr
    register_linter_set register_option register_parser_alias register_simp_attr
    register_sym_dsimp register_sym_simp register_sym_simp_attr register_tactic_tag
    register_try?_tactic renaming repeat reportDbgIssue! reportEMatchIssue! reportIssue!
    reprove reset_grind_attrs% return rightact% run_cmd run_elab run_meta s!
    satisfies_binder_pred% scoped seal section sepBy( sepBy1( set_library_suggestions
    set_option show show_panel_widgets show_term show_term_elab simproc simproc_decl
    simproc_pattern% sorry struct_inst_default% structure suffices syntax tactic_alt
    tactic_extension tactic_name tactic_tag termination_by termination_by? test_extern
    then theorem throwError throwErrorAt throwNamedError throwNamedErrorAt time(
    timezone( trace[ trace_goal[ trailing_parser try type_of% unicode( unif_hint
    universe unless unlock_limits unop% unreachable! unsafe unseal until using using!
    value_of% variable wait_for_expected_type% wait_if_contains_mvar%
    wait_if_type_contains_mvar% wait_if_type_mvar% where while with with_annotate_term
    with_decl_name% with_weak_namespace without_expected_type zoned( Σ Σ' λ
'''.split())


def comment_end(src: str, i: int) -> int:
    """Return the end of the line comment or nested block comment that starts at i, as Lean
    reads it (check_fidelity.py's `comment_end`)."""
    end = shared_comment_end(src, i)
    require(end is not None, 'unterminated Lean comment')
    return end


def string_literals(src: str, start: int, end: int) -> list[str]:
    """Return the contents of the strings that open in src[start:end], outside comments;
    start must stand outside every string and comment."""
    found = []
    i = start
    while i < end:
        if src.startswith(('--', '/-'), i):
            i = comment_end(src, i)
        elif src[i] == '"':
            j = i + 1
            while j < len(src) and src[j] != '"':
                j += 2 if src[j] == '\\' else 1
            found.append(src[i + 1:j])
            i = j + 1
        else:
            i += 1
    return found


def mask(src: str) -> tuple[str, list[tuple[int, int]]]:
    out = list(src)
    comments = []
    i = 0
    while i < len(src):
        start = i
        if src.startswith(('--', '/-'), i):
            i = comment_end(src, i)
            comments.append((start, i))
        elif src[i] == '"':
            i += 1
            while i < len(src):
                if src[i] == '\\':
                    i += 2
                elif src[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            else:
                raise Refusal('unterminated Lean string')
        else:
            i += 1
            continue
        for j in range(start, min(i, len(src))):
            if src[j] != '\n':
                out[j] = ' '
    return ''.join(out), comments


def assignment(clean: str, start: int, end: int) -> int | None:
    stack = []
    pairs = {')': '(', ']': '[', '}': '{', '⟩': '⟨'}
    i = start
    while i < end:
        c = clean[i]
        if c in '([{⟨':
            stack.append(c)
        elif c in pairs:
            require(stack and stack.pop() == pairs[c], 'unbalanced declaration delimiters')
        elif clean.startswith(':=', i) and not stack:
            return i
        i += 1
    require(not stack, 'unclosed declaration delimiter')
    return None


def header_tokens(src: str, comments: list[tuple[int, int]]):
    """Yield the tokens of a Lean header as (text, start, end), before any masking.

    Whitespace and ordinary comments separate tokens; each comment is added to comments. A
    doc comment is one token, and so is a module name, read whole with its «...» components,
    so that nothing inside them is read as syntax. Any other character is a token by itself.
    At the end of the text the stream yields ('', len(src), len(src)) for ever.
    """
    i = 0
    while True:
        while i < len(src) and src[i] in ' \t\r\n':
            i += 1
        if i == len(src):
            yield '', i, i
            continue
        if src.startswith(('--', '/-'), i) and not src.startswith(('/--', '/-!'), i):
            end = comment_end(src, i)
            comments.append((i, end))
        elif src.startswith('/-', i):
            end = comment_end(src, i)
            yield src[i:end], i, end
        else:
            found = MODULE_NAME.match(src, i)
            end = found.end() if found else i + 1
            yield src[i:end], i, end
        i = end


def module_path(name: str) -> str | None:
    """Return the file a module name names, one folder per component, or None if a component
    could leave its folder."""
    parts = [part[1:-1] if part.startswith('«') else part for part in MODULE_PART.findall(name)]
    if any(part in ('.', '..') or '/' in part for part in parts):
        return None
    return '/'.join(parts) + '.lean'


def lean_source(path: str, raw: str) -> tuple[str, list[tuple[int, int]], list[tuple[str, int, int]]]:
    """Read a Lean file's header, then mask the file; return the masked text, its comments and
    its imports, each with its module's file and the span of its words to the end of its line.

    The header is an optional `module`, then any number of `[public] [meta] import M`, each
    ending its line, with ordinary comments between the words. As in Lean, an import is read
    only whole, so `public section` after the header ends it. An import naming anything but one
    module, and an `import` anywhere after the header unless within a whole «...» name, are
    refused: so is any other word before an import, `prelude`, `import all`, a doc comment
    among the imports or a block comment that opens on an import's line and closes on a later
    one. The header is blank in the masked text.
    """
    comments: list[tuple[int, int]] = []
    stream = header_tokens(raw, comments)
    tokens: list[tuple[str, int, int]] = []

    def token(k: int) -> tuple[str, int, int]:
        while len(tokens) <= k:
            tokens.append(next(stream))
        return tokens[k]

    k = 1 if token(0)[0] == 'module' else 0
    end = token(0)[2] if k else 0
    imports = []
    while True:
        j = k + (token(k)[0] == 'public')
        j += token(j)[0] == 'meta'
        if token(j)[0] != 'import':
            break
        name, _, end = token(j + 1)
        following = token(j + 2)
        newline = raw.find('\n', end)
        line_end = len(raw) if newline < 0 else newline + 1
        file = module_path(name) if MODULE_NAME.fullmatch(name) else None
        # A block comment opening on the import's line must close there, so that the
        # import's span ends outside it.
        require(file and name not in HEADER_WORDS
                and (not following[0] or '\n' in raw[end:following[1]])
                and not any(token(k)[1] <= a < line_end and raw.startswith('/-', a)
                            and '\n' in raw[a:b] for a, b in comments),
                f'{path}: unsupported import {raw[token(k)[1]:line_end].rstrip()!r}')
        imports.append((file, token(k)[1], line_end))
        k = j + 2
    rest, rest_comments = mask(raw[end:])
    clean = re.sub(r'[^\n]', ' ', raw[:end]) + rest
    # A whole «...» name is one identifier, so an `import` within it is no import.
    names = QUOTED_NAME.sub(lambda found: ' ' * len(found.group()), clean)
    later = IMPORT_WORD.search(names, end)
    if later:
        line_end = raw.find('\n', later.start())
        line = raw[raw.rfind('\n', 0, later.start()) + 1:len(raw) if line_end < 0 else line_end]
        raise Refusal(f'{path}: unsupported import {line!r}')
    comments = [c for c in comments if c[0] < end] + [(a + end, b + end) for a, b in rest_comments]
    return clean, comments, imports


@dataclass(frozen=True)
class Declaration:
    name: str
    path: str
    kind: str
    start: int
    keyword: int
    name_end: int
    end: int
    signature_end: int
    body: int
    namespace: str
    context: tuple[tuple[int, int], ...]
    opens: tuple[str, ...]


class Index:
    def __init__(self, evidence: Evidence):
        self.evidence = evidence
        self.decls: dict[str, Declaration] = {}
        self.clean: dict[str, str] = {}
        self.raw: dict[str, str] = {}
        self.imports: dict[str, list[tuple[str, int, int]]] = {}
        self.notation: list[tuple[str, int, int]] = []
        self.visible_cache: dict[str, set[str]] = {}
        for path in sorted((ROOT / 'Elements').rglob('*.lean')):
            self.add(relative(path))
        self.by_tail: dict[str, list[str]] = {}
        for name in self.decls:
            self.by_tail.setdefault(name.rsplit('.', 1)[-1], []).append(name)

    def add(self, path: str) -> None:
        raw = self.evidence.read(path)
        # Refused since the masking, which opened a comment with `/-` alone, ended `/--/` at
        # once where Lean's doc comment runs on to a later `-/`. The masking now reads it as
        # Lean does (`comment_end`, #206), and the refusal stands.
        require('/--/' not in raw, f'{path}: unsupported doc comment opening /--/')
        clean, comments, self.imports[path] = lean_source(path, raw)
        self.clean[path] = clean
        self.raw[path] = raw
        # Wherever one stands, local or scoped included. The bar is sought in the raw text, so
        # within the notation's strings; the `=>` in the masked text, so outside them. Each
        # string is a token, read without its spaces: it may be a name, or hold no character
        # of a name, as `‖` and `∠` do, and is refused otherwise.
        for found in SYNTAX_WORD.finditer(clean):
            require(not found.group(1), f'{path}: unsupported command {found.group()}')
            arrow = clean.find('=>', found.end())
            stop = len(raw) if arrow < 0 else arrow
            require('|' not in raw[found.start():stop],
                    f'{path}: unsupported {found.group()} with a bar')
            for atom in string_literals(raw, found.start(), stop):
                atom = atom.strip()
                # Lean reads a token whole, `/--+` too, where the masking opens a comment.
                require((LEAN_NAME.fullmatch(atom) or not NAME_CHARACTER.search(atom))
                        and '--' not in atom and '/-' not in atom,
                        f'{path}: unsupported {found.group()} token {atom!r}')
        commands = list(COMMAND.finditer(clean))
        namespace = ''
        frames: list[tuple[str, int, int]] = []
        contexts: list[tuple[int, int]] = []
        opens: list[str] = []
        for idx, match in enumerate(commands):
            kind = match.group(1)
            start = match.start()
            next_start = commands[idx + 1].start() if idx + 1 < len(commands) else len(raw)
            # A leading top-level comment belongs to the following command, not this one.
            stop = next_start
            for a, b in comments:
                if match.end() < a < next_start and raw[raw.rfind('\n', 0, a) + 1:a] == '':
                    if not clean[b:next_start].strip():
                        stop = min(stop, a)
            end = len(raw[:stop].rstrip())
            line_end = raw.find('\n', start)
            line_end = len(raw) if line_end < 0 else line_end
            if kind in ('namespace', 'section'):
                frames.append((namespace, len(contexts), len(opens)))
                if kind == 'namespace':
                    part = clean[match.end():line_end].strip()
                    namespace = namespace + '.' + part if namespace else part
                contexts.append((start, line_end))
                continue
            if kind == 'end':
                require(frames, f'{path}: unpaired namespace end')
                namespace, c, o = frames.pop()
                contexts, opens = contexts[:c], opens[:o]
                continue
            if kind in ('open', 'variable'):
                contexts.append((start, end))
                if kind == 'open':
                    opens.extend(TOKEN.findall(clean[match.end():end]))
                continue
            if kind.startswith(('notation', 'infix', 'prefix', 'postfix')):
                self.notation.append((path, start, end))
                continue
            if kind in ('example', 'attribute', 'set_option'):
                continue
            nm = re.match(r'\s+(' + NAME + r')', clean[match.end():end])
            if nm is None:
                require(kind == 'instance', f'{path}:{start}: unnamed {kind}')
                continue
            short = nm.group(1)
            name = short.removeprefix('_root_.') if short.startswith('_root_.') else namespace + '.' + short
            require(name not in self.decls, f'{path}: ambiguous declaration {name}')
            name_end = match.end() + nm.end()
            kw = match.start(1)
            doc_start = start
            for a, b in reversed(comments):
                if b <= start and raw[a:a + 3] == '/--' and not raw[b:start].strip():
                    doc_start = a
                    break
            assign = assignment(clean, name_end, end)
            sig_end = assign if assign is not None else end
            if assign is None and kind in ('def', 'abbrev'):
                eq = re.search(r'^\s+\|', clean[name_end:end], re.M)
                if eq:
                    sig_end = name_end + eq.start()
            self.decls[name] = Declaration(name, path, kind, doc_start, kw, name_end, end,
                                           len(raw[:sig_end].rstrip()),
                                           assign + 2 if assign is not None else end,
                                           namespace, tuple(contexts), tuple(opens))

    def visible(self, path: str, visiting: frozenset[str] = frozenset()) -> set[str]:
        if path in self.visible_cache:
            return self.visible_cache[path]
        require(path not in visiting, f'{path}: import cycle')
        result = {path}
        for imported, _, _ in self.imports[path]:
            if imported.startswith('Elements/'):
                require(imported in self.imports, f'{path}: missing import {imported}')
                result |= self.visible(imported, visiting | {path})
        self.visible_cache[path] = result
        return result

    def resolve(self, token: str, consumer: Declaration, *, required: bool = False,
                commentary: bool = False) -> str | None:
        # A dotted declaration opens its parent namespaces for its own type and body.
        # For example, fan.positions within Fitted.fan names Fitted.fan.positions.
        prefixes = consumer.name.split('.')[:-1]
        for n in range(len(prefixes), -1, -1):
            candidate = '.'.join(prefixes[:n] + [token])
            if candidate in self.decls:
                return candidate
        candidates = set()
        # An opened namespace is named from the root, from Elements, or from the consumer's
        # namespace or any enclosing it: `open Prop4 in` within Elements.BookI opens
        # Elements.BookI.Prop4.
        parts = consumer.namespace.split('.') if consumer.namespace else []
        scopes = {'', 'Elements.'} | {'.'.join(parts[:n]) + '.' for n in range(1, len(parts) + 1)}
        for opened in (*consumer.opens, *(['Elements', 'Elements.Tacit'] if commentary else [])):
            for prefix in sorted(scopes):
                candidate = prefix + opened + '.' + token
                if candidate in self.decls:
                    candidates.add(candidate)
        require(len(candidates) <= 1, f'{consumer.path}: ambiguous name {token}: {sorted(candidates)}')
        if candidates:
            return next(iter(candidates))
        if required:
            raise Refusal(f'{consumer.path}: unresolved name {token}')
        return None

    def get(self, name: str) -> Declaration:
        require(name in self.decls, f'unresolved declaration {name}')
        return self.decls[name]

    def quote(self, source: dict, field: str, name: str, *, full: bool = False,
              doc: bool = True) -> str:
        d = self.get(name)
        return self.evidence.excerpt(source, field, d.path, d.start if doc else d.keyword,
                                     d.end if full else d.signature_end)

    def context(self, source: dict, field: str, names: list[str]) -> dict:
        result = {}
        for name in sorted(set(names)):
            d = self.get(name)
            result[name] = [self.evidence.excerpt(source, field + '.' + name, d.path, a, b)
                            for a, b in d.context]
        return result

    def import_text(self, source: dict, field: str, path: str) -> str:
        spans = self.imports[path]
        if not spans:
            return ''
        return self.evidence.excerpt(source, field, path, spans[0][1], spans[-1][2])


REGISTRY = {
    'Words': 'Point Line Circle OnLine SameSide Between OnCircle InsideCircle Centre Collinear '
             'OppositeSides OutsideCircle LinesMeet LineMeetsCircle CirclesMeet',
    'Definitions': 'Triangle Parallel Equilateral Square IsAcute IsObtuse IsRightAngle Isosceles '
                   'RightAngledTriangle',
    'Phrases': 'AreParallel SameSideOf OppositeSidesOf OnRay InsideTriangle Parallelogram quadArea '
               'InOrder segments endOf OnFiniteLine OnOrInsideTriangle Corners triples Fitted '
               'Rectilineal Rectilineal.area Apart Apart.area',
    'DefinitionsII': 'Rectangle Contain rect sq',
    'Magnitudes': 'Kind MagnitudeImpl Magnitude Length Angle Area len ang area rightAngle Magnitude.sum',
}
SYMBOLS = {'‖': 'len', '∠': 'ang', '△': 'area', '∟': 'rightAngle'}
AREA_BRIDGES = ['Elements.Parallelogram.cross', 'Elements.Parallelogram.quadArea_rotate',
                'Elements.BookI.Prop34', 'Elements.BookI.Prop34.bisect']
RECT_BRIDGES = ['Elements.Rectangle.congr', 'Elements.Rectangle.contained',
                'Elements.Rectangle.eq_rect', 'Elements.Square.eq_sq', 'Elements.Square.described']
FIGURE_BRIDGES = ['Elements.Fitted.triangle', 'Elements.Fitted.inside_pairwise',
                  'Elements.Rectilineal.toApart', 'Elements.Rectilineal.area_toApart',
                  'Elements.Fitted.fan']


def bundle(book: str, n: int) -> tuple[list[str], list[str]]:
    definitions, bridges = [], []
    if book == 'I' and (34 <= n <= 38 or 41 <= n <= 48):
        definitions += ['Parallelogram', 'quadArea']
        bridges += AREA_BRIDGES
        if n >= 46:
            definitions += ['Square']
            bridges += ['Elements.BookI.Prop46.square_eq']
    if book == 'II':
        definitions += ['Rectangle', 'Contain', 'rect', 'sq', 'Parallelogram', 'quadArea', 'Square']
        bridges += RECT_BRIDGES
    if (book, n) in [('I', 45), ('II', 14)]:
        definitions += ['Apart', 'Fitted', 'Rectilineal']
        bridges += FIGURE_BRIDGES
    if (book, n) == ('II', 1):
        definitions += ['InOrder', 'segments', 'endOf', 'Magnitude.sum']
        bridges += ['Elements.InOrder.between_end', 'Elements.rect_self_left',
                    'Elements.rect_self_right', 'Elements.sq_self']
    return definitions, bridges


def glossary(index: Index, source: dict, code: list[str], extra: list[str] = ()) -> dict:
    registry = {name: 'Elements.' + name for words in REGISTRY.values() for name in words.split()}
    for file, words in REGISTRY.items():
        for name in words.split():
            d = index.get(registry[name])
            require(d.path == f'Elements/Foundations/{file}.lean', f'glossary registry moved: {name}')
    selected = set(extra)
    pending = '\n'.join(code)
    while True:
        clean = mask(pending)[0]
        tokens = set(TOKEN.findall(clean))
        found = {n for n in registry if any(t == n or t.endswith('.' + n) for t in tokens)}
        found |= {name for symbol, name in SYMBOLS.items() if symbol in clean}
        found |= {n + '.area' for n in ('Apart', 'Rectilineal') if n in selected | found}
        added = found - selected
        # Explicit selections must take part in the first dependency expansion too.
        if not added and not pending:
            break
        selected |= found
        text = '\n'.join(index.evidence.read(index.get(registry[n]).path)[index.get(registry[n]).keyword:
                          index.get(registry[n]).end] for n in sorted(selected))
        if text == pending:
            break
        pending = text
    definitions = {n: index.quote(source, 'definitions.' + n, registry[n], full=True) for n in sorted(selected)}
    notation = {}
    for path, a, b in index.notation:
        raw = index.evidence.read(path)[a:b]
        if any(n in selected for n in SYMBOLS.values() if n in TOKEN.findall(mask(raw)[0])):
            notation[f'{path}:{index.evidence.read(path).count(chr(10), 0, a) + 1}'] = index.evidence.excerpt(
                source, 'notation', path, a, b)
    return {'definitions': definitions, 'notation': notation,
            'definition_context': index.context(source, 'definition_context', [registry[n] for n in selected])}


class Calls:
    """Reconcile source calls with certificate dependency walks, without reading comments.

    Field calls collect every Elements declaration T.f whose type name T occurs in the
    unit or in a collected signature, repeating to closure. Namespace prefixes do not
    restrict these conservative candidates, and no receiver type is guessed. Constructors
    and named structure projections are quoted through their enclosing declaration, which
    contains their exact signatures and docstrings. An inductive's constructors are each
    named after a `|` outside every bracket in the declaration, on a line that opens `  |`,
    several to a line as `| a | b | c`; there they are declared, not called. An inductive
    is read only in the plain forms `constructors` names, and refused otherwise. The
    glossary's supplied definitions also expose their underlying types, including
    AreParallel within Parallelogram.

    The fixed core/projection allowlist is: 1, 2, symm, trans, refl, mp, mpr, elim, left, right,
    ne, imp, inl, inr, resolve_left, resolve_right, map, Pairwise, mem_append, mem_cons,
    mem_cons_of_mem, mem_cons_self, mem_singleton, mem_singleton_self, not_mem_nil,
    mem_nil_iff, forall_mem_cons, cons_ne_nil, append_ne_nil_of_right_ne_nil, append_assoc,
    append_nil, nil_append, cons_append, pairwise_append, pairwise_singleton,
    byContradiction, epsilon_spec. These names exempt only fields with no project candidate;
    symm, for example, still collects every eligible geometric signature. Any remaining field
    is unresolved.
    """

    CORE_FIELDS = frozenset({
        '1', '2', 'symm', 'trans', 'refl', 'mp', 'mpr', 'elim', 'left', 'right', 'ne', 'imp',
        'inl', 'inr', 'resolve_left', 'resolve_right', 'map', 'Pairwise', 'mem_append',
        'mem_cons', 'mem_cons_of_mem', 'mem_cons_self', 'mem_singleton', 'mem_singleton_self',
        'not_mem_nil', 'mem_nil_iff', 'forall_mem_cons', 'cons_ne_nil',
        'append_ne_nil_of_right_ne_nil', 'append_assoc', 'append_nil', 'nil_append',
        'cons_append', 'pairwise_append', 'pairwise_singleton', 'byContradiction', 'epsilon_spec',
    })
    REFERENCE = re.compile(r'(?:' + IDENT + r'|(?<=\.)[0-9]+)(?:\.(?:' + IDENT + r'|[0-9]+))*')
    CONSTRUCTOR_LINE = re.compile(r'^  \|[^\n]*', re.M)
    CONSTRUCTOR = re.compile(r'\|\s*(' + IDENT + ')')
    CLOSERS = {')': '(', ']': '[', '}': '{', '⟩': '⟨', '⦄': '⦃', '⟧': '⟦', '›': '‹'}
    # The plain forms, the only ones `constructors` reads from an inductive's name to the end
    # of its constructors: whitespace and name characters; a dot after a name character, a
    # bracket or a space, and before a name character; the brackets ( ) [ ] { } ⦃ ⦄ ⟨ ⟩; the
    # symbols : , → ∀ ∈ × + |; and no keyword but those of PLAIN_WORDS. A match is a word, to
    # be read against KEYWORD_TOKENS, or a dot or a character outside the plain forms.
    PLAIN_WORDS = frozenset({'Type', 'Prop', 'Sort', 'where', '_'})
    UNPLAIN = re.compile('(?P<word>' + LEAN_NAME.pattern + ')'
                         '|(?P<after>(?<![' + WHITESPACE + NAME_REST
                         + '()\\[\\]{}⦃⦄⟨⟩])\\.)|(?P<before>\\.(?![' + NAME_REST + ']))'
                         '|[^' + WHITESPACE + NAME_REST + '.()\\[\\]{}⦃⦄⟨⟩:,→∀∈×+|]')
    # The longest keyword token at a place, as Lean's token table reads it.
    KEYWORD = re.compile('|'.join(re.escape(token) for token in
                                  sorted(KEYWORD_TOKENS, key=lambda token: (-len(token), token))))
    # Words after which a `|` may begin an alternative or a pattern, as in
    # `| mk : Q <| match 0 with | Known.bar n => n | _ => 0`: of `fun`, `match` or
    # `match_expr`, of a `let`, `have`, `haveI`, `letI`, `let_fun`, `let_delayed` or `let_tmp`
    # by equations or of `let_expr`, of `matches`, of a tactic, of `do`, or of a computed field
    # after `with`. The plain forms hold none of them; a bar after one is refused first, with
    # that reason.
    ALTERNATIVES = re.compile(KEYWORD_LEFT
                              + r'(?:fun|match|match_expr|matches|let|let_expr|have|by'
                              + r'|do|with|haveI|letI|let_fun|let_delayed|let_tmp)'
                              + KEYWORD_RIGHT + '|λ')
    # A line that is blank, opens `  |` or opens with three spaces continues the constructors;
    # a line opening with a bar after fewer spaces is refused, not taken as their end.
    CONSTRUCTORS_END = re.compile(r'(?! *$|  \||   )', re.M)
    # A declaration's keyword, or `recall`, begins a command wherever it stands on its line,
    # and ends the constructors.
    COMMAND_WORD = re.compile(KEYWORD_LEFT
                              + r'(?:def|theorem|abbrev|instance|example|opaque|axiom'
                              + r'|structure|class|inductive|deriving|mutual|recall)'
                              + KEYWORD_RIGHT)
    # Three forms would make the masked text, or the words in it, other than Lean reads them.
    # A string, a char literal or a «...» name, whose brackets and bars the masking may misread,
    # and a `»`, which may end a «...» name Lean opened before the inductive.
    LITERAL = re.compile(r"[\"«»]|(?<![\w'₀-₉!?])'")
    # A number glued to a word or a quote, as in `0x5matches` or `0'a'`, where Lean ends the
    # number, so that a keyword after it would go unseen and a quote would open a char literal;
    # and a quote after a bare `!` or `?`, which opens one, as in `!'a'matches`.
    GLUED = re.compile(r"(?<![\w'₀-₉!?])(?:[0-9]+(?:[^\W\d]|['!?])|[!?]+')")
    # A dash or a slash after which the masking opens a comment, after anything but whitespace
    # or a name character: Lean may read it within a token, as in `\/-`, `//-` or a notation's
    # `+--`, and open no comment there. After whitespace too Lean reads a notation's `/--+`
    # whole; the index refuses every notation token holding `--` or `/-`.
    OPENER = re.compile('--|/-')
    # Two forms the plain forms leave out are refused first, with a reason of their own: a
    # word character Lean reads in no name, such as `²` or `ж` (but `λ`, which ALTERNATIVES
    # reads), a subscript that begins a word, as after `→ₑ`, and `#`, which begins Lean's
    # commands, each read whole, as `#where` is in `#wheredef`; and a dot glued to a symbol
    # before a word, as in `..matches` or `⊗.matches`, which the patterns take for a field.
    FOREIGN = re.compile('[^\\W' + NAME_REST + 'λ]|(?<![\\w\'!?])[' + SUBSCRIPTS + ']|#')
    DOT = re.compile('(?<=[^\\s\\w' + NAME_REST + '()\\[\\]{}⟨⟩⦃⦄⟦⟧‹›])\\.(?=\\w)')

    def __init__(self, index: Index, facts: dict):
        self.index = index
        self.facts = facts
        self.by_name = {'Elements.' + p['name']: p for p in facts.values()}
        self.cache: dict[tuple[str, tuple[str, ...]], tuple[list[dict], set[str]]] = {}
        self.unresolved: dict[str, set[str]] = {}
        self.types = {n for n, d in index.decls.items()
                      if d.kind in ('def', 'abbrev', 'opaque', 'axiom', 'structure', 'inductive')}
        self.members: dict[str, set[str]] = {}
        for name, d in index.decls.items():
            if d.kind == 'inductive':
                found = [m.group(1) for m in self.constructors(index.clean[d.path], d)]
            elif d.kind == 'structure':
                found = re.findall(r'^  (' + IDENT + r')(?![' + NAME_REST + '])',
                                   index.clean[d.path][d.name_end:d.end], re.M)
            else:
                continue
            for member in found:
                self.members.setdefault(member, set()).add(name)

    def constructors(self, clean: str, d: Declaration) -> list[re.Match]:
        """Return each constructor name of inductive d: the name after a `|` outside every
        bracket in the declaration, on a line that opens `  |`.

        The reader accepts only the plain forms main's inductives are written in, and refuses
        everything else. From the inductive's name to the end of its constructors, the masked
        text may hold only whitespace and name characters; a dot after a name character, a
        bracket or a space, and before a name character; the brackets ( ) [ ] { } ⦃ ⦄ ⟨ ⟩;
        the symbols : , → ∀ ∈ × + |; and no keyword Lean 4.35 reads (KEYWORD_TOKENS) but
        `Type`, `Prop`, `Sort`, `where` and `_`. An alternative or a pattern after a bar needs
        `=>` or a keyword, so in these forms each bar outside every bracket separates
        constructors or stands beside another, as in `||`, which separates none; any other
        bar is refused, as are constructors at four spaces or on the inductive's own line.

        So that the masked text, and the words in it, are those Lean reads, the
        declaration's raw text may hold no string, char literal, «...» name or `»`
        (LITERAL), no number glued to a word or a quote (GLUED), and no comment opening
        after anything but whitespace or a name character, where Lean may read the dash or
        slash within a token (OPENER); a comment in it may hold no `{`, and a line comment
        no `-/`, at which Lean, put within a comment, a «...» name or an interpolated string
        by something earlier such as `'"'`, would leave it; and the index refuses, in any
        file it reads, a doc comment opening `/--/`, and a notation token holding `--` or
        `/-`, which Lean reads whole where the masking opens a comment. Some forms outside
        the plain forms are refused first, with a reason of their own: those FOREIGN and
        DOT name, anywhere in the declaration, and a bar after a word ALTERNATIVES names.

        The constructors end before the first line outside every bracket that is not blank
        and opens neither `  |` nor three spaces, where a deriving clause or a command
        begins, and before a declaration's keyword or `recall` outside every bracket,
        wherever it stands on its line, as in `| mk def f`; what follows is read for uses.
        Brackets are counted from the name across lines, and an unbalanced one is refused.
        The index refuses a notation whose words before `=>` hold a bar, or whose token joins
        a name character to another, and every macro, elaborator and binder-predicate
        command; `scripts/check_fidelity.py`, not this generator, refuses in `Elements/` the
        attributes that make a declaration an elaborator or a parser, such as
        `@[term_elab k]`."""
        require(not self.LITERAL.search(self.index.raw[d.path], d.name_end, d.end),
                f'{d.path}: unsupported string, char literal or quoted name in {d.name}')
        require(not self.GLUED.search(clean, d.name_end, d.end),
                f'{d.path}: unsupported number or literal glued to a word in {d.name}')
        foreign = self.FOREIGN.search(clean, d.name_end, d.end)
        if foreign:
            raise Refusal(f'{d.path}: unsupported character {foreign.group()!r} in {d.name}')
        raw = self.index.raw[d.path]
        for found in self.OPENER.finditer(raw, d.name_end, d.end):
            before = raw[found.start() - 1]
            require(clean[found.start() - 1] != before or before in WHITESPACE
                    or NAME_CHARACTER.match(before),
                    f'{d.path}: unsupported comment glued to {before!r} in {d.name}')
        # Where the masking misread something before the inductive, as it reads '"', Lean may be
        # within a comment, a «...» name or an interpolated string at its keyword, and leave it
        # at `-/`, `»` or `{`. LITERAL refuses `»` and `"`; a comment here may hold no `{`, and a
        # line comment no `-/`, so Lean leaves none of them where the masking reads no code.
        i = d.name_end
        while i < d.end:
            if raw.startswith(('--', '/-'), i):
                end = comment_end(raw, i)
                require('{' not in raw[i:end] and not (raw[i] == '-' and '-/' in raw[i:end]),
                        f'{d.path}: unsupported {{ or -/ in a comment in {d.name}')
                i = end
            else:
                i += 1
        require(not self.DOT.search(clean, d.name_end, d.end),
                f'{d.path}: unsupported dot glued to a symbol in {d.name}')
        lines = {line.start(): line.end()
                 for line in self.CONSTRUCTOR_LINE.finditer(clean, d.name_end, d.end)}
        words = {found.start(): found.group()
                 for found in self.ALTERNATIVES.finditer(clean, d.name_end, d.end)}
        commands = {found.start() for found in self.COMMAND_WORD.finditer(clean, d.name_end, d.end)}
        found, stack, line_end, word, stop = [], [], -1, None, d.end
        for i in range(d.name_end, d.end):
            if not stack and clean[i - 1] == '\n' and self.CONSTRUCTORS_END.match(clean, i):
                require(not re.match(r' *\|', clean[i:]),
                        f'{d.path}: unsupported bar in an inductive, {d.name}')
                stop = i
                break
            line_end = lines.get(i, line_end)
            c = clean[i]
            if c in '([{⟨⦃⟦‹':
                stack.append(c)
            elif c in self.CLOSERS:
                require(stack and stack.pop() == self.CLOSERS[c],
                        f'{d.path}: unbalanced brackets in {d.name}')
            elif stack:
                continue
            elif i in commands:
                stop = i
                break
            elif i in words:
                word = word or words[i]
            elif c == '|' and clean[i - 1] not in '|<' and clean[i + 1:i + 2] not in ('|', '>'):
                # Off a constructor line, line_end is behind i and nothing matches.
                match = self.CONSTRUCTOR.match(clean, i, line_end)
                require(word is None, f'{d.path}: unsupported bar after {word!r} in {d.name}')
                require(match, f'{d.path}: unsupported bar in an inductive, {d.name}')
                found.append(match)
        require(not stack, f'{d.path}: unbalanced brackets in {d.name}')
        for unplain in self.UNPLAIN.finditer(clean, d.name_end, stop):
            if unplain.lastgroup == 'word':
                keyword = self.KEYWORD.match(clean, unplain.start(), stop)
                if (not keyword or keyword.end() < unplain.end()
                        or keyword.group() in self.PLAIN_WORDS):
                    continue
                what = f'the keyword {keyword.group()!r}'
            elif unplain.lastgroup == 'after':
                what = f'a dot after {clean[unplain.start() - 1]!r}'
            elif unplain.lastgroup == 'before':
                what = f'a dot before {clean[unplain.end():unplain.end() + 1]!r}'
            else:
                what = f'the character {unplain.group()!r}'
            raise Refusal(f'{d.path}: {d.name} holds {what}, outside the plain forms an '
                          'inductive may hold')
        return found

    def type_names(self, text: str, consumer: Declaration) -> set[str]:
        found = set()
        for token in TOKEN.findall(text):
            parts = token.split('.')
            for count in range(1, len(parts) + 1):
                name = self.index.resolve('.'.join(parts[:count]), consumer)
                if name in self.types:
                    found.add(name.rsplit('.', 1)[-1])
        return found

    def direct(self, name: str, signatures: tuple[str, ...] = ()) -> list[dict]:
        key = (name, signatures)
        if key in self.cache:
            calls, unresolved = self.cache[key]
            self.unresolved[name] = unresolved
            return calls
        d = self.index.get(name)
        clean = self.index.clean[d.path]
        visible = self.index.visible(d.path)
        calls = []
        fields = []

        def record(target: str, match: re.Match, resolution: str) -> None:
            calls.append({'name': target, 'token': match.group(), 'path': d.path,
                          'line': clean.count('\n', 0, match.start()) + 1,
                          'start': match.start(), 'end': match.end(),
                          'position': 'proof' if match.start() >= d.body else 'type',
                          'resolution': resolution})

        declared = ({found.start(1) for found in self.constructors(clean, d)}
                    if d.kind == 'inductive' else set())
        for match in self.REFERENCE.finditer(clean, d.name_end, d.end):
            if match.start() in declared:
                continue
            token = match.group()
            parts = token.split('.')
            after_expression = clean[match.start() - 1:match.start()] == '.'
            target, consumed = None, 0
            if not after_expression:
                for count in range(len(parts), 0, -1):
                    target = self.index.resolve('.'.join(parts[:count]), d)
                    if target:
                        consumed = count
                        break
            if target:
                called = self.index.get(target)
                require(called.path in visible, f'{d.path}: {target} is not imported')
                require(called.path != d.path or called.keyword <= d.keyword,
                        f'{d.path}: forward declaration use {target} in {name}')
                record(target, match, 'namespace')
            elif re.search(r'(?:^|\.)Prop\d+', token):
                raise Refusal(f'{d.path}: unresolved proposition call {token} in {name}')
            start = consumed if target else (0 if after_expression else 1)
            fields.extend((part, match) for part in parts[start:])

        type_names = self.type_names(clean[d.name_end:d.end], d)
        collected = set(signatures) | {name} | {c['name'] for c in calls}
        inspected = set()
        candidates: dict[str, set[str]] = {}
        while True:
            previous_types = set(type_names)
            for selected in sorted(collected - inspected):
                sd = self.index.get(selected)
                type_names |= self.type_names(self.index.clean[sd.path][sd.name_end:sd.signature_end], sd)
                inspected.add(selected)
            for words in REGISTRY.values():
                for word in words.split():
                    if word in type_names:
                        td = self.index.get('Elements.' + word)
                        type_names |= self.type_names(self.index.clean[td.path][td.name_end:td.end], td)
            added = set()
            for field, _ in fields:
                matches = {n for n in self.index.by_tail.get(field, [])
                           if n.rsplit('.', 2)[-2] in type_names}
                matches |= {n for n in self.members.get(field, set())
                            if n.rsplit('.', 1)[-1] in type_names}
                candidates[field] = matches
                added |= matches
            if added <= collected and type_names == previous_types:
                break
            collected |= added
        unresolved = set()
        for field, match in fields:
            for target in sorted(candidates[field]):
                record(target, match, 'field candidates via signature closure')
            if not candidates[field] and field not in self.CORE_FIELDS:
                unresolved.add(f'{name}:{clean.count(chr(10), 0, match.start()) + 1}: {match.group()} ({field})')
        calls = list({(c['start'], c['end'], c['name']): c for c in calls}.values())
        calls.sort(key=lambda c: (c['start'], c['name']))
        self.cache[key] = calls, unresolved
        self.unresolved[name] = unresolved
        return calls

    def unit(self, ref: str) -> dict:
        fact = self.facts[ref]
        name = 'Elements.' + fact['name']
        hints = tuple(sorted('Elements.' + s['name'] for s in fact['shared_steps']))
        inherited = {s['name']: s for entries in fact['inherited'].values() for s in entries}
        for short, step in inherited.items():
            require(self.index.get('Elements.' + short).path == step['file'],
                    f'{ref}: inherited helper path changed: {short}')
        for step in fact['shared_steps']:
            d = self.index.get('Elements.' + step['name'])
            require(d.path == step['file'], f'{ref}: shared step path changed: {step["name"]}')
        own_namespace = heath.parse_ref(ref).lean.split('.porism')[0]
        if fact['kind'] != 'proposition':
            own_namespace = heath.parse_ref(fact['of']).lean
        discovered: dict[str, list[dict]] = {}
        dependencies = set()
        signatures = set(hints) | {'Elements.' + n for n in inherited}
        signatures |= {'Elements.' + self.facts[r]['name'] for r in fact['cites']}
        owners = {name}
        shared_seen = set()
        while True:
            previous = (set(owners), set(signatures))
            for current in sorted(owners):
                found = self.direct(current, tuple(sorted(signatures)))
                discovered[current] = found
                signatures.update(call['name'] for call in found)
                for call in found:
                    target = call['name']
                    if target == name:
                        continue
                    if target in self.by_name:
                        dependencies.add(self.by_name[target]['ref'])
                    elif target.startswith(own_namespace + '.'):
                        owners.add(target)
                    elif target in hints:
                        shared_seen.add(target)
                        step = next(s for s in fact['shared_steps'] if 'Elements.' + s['name'] == target)
                        dependencies.update(step['brings_in'])
            if previous == (owners, signatures):
                break
        unresolved = sorted({token for owner in owners for token in self.unresolved[owner]})
        require(not unresolved, f'{ref}: unresolved names: {unresolved}')
        # All certificate steps must be accounted for in the reachable source, including
        # field notation. A mismatch is an extraction failure, never a passing audit.
        missing_steps = set(hints) - shared_seen
        require(not missing_steps, f'{ref}: certificate steps not resolved in source: {sorted(missing_steps)}')
        require(dependencies == set(fact['cites']),
                f'{ref}: source/certificate mismatch: source-only {sorted(dependencies - set(fact["cites"]))}; '
                f'certificate-only {sorted(set(fact["cites"]) - dependencies)}')
        return {'ref': ref, 'declaration': name, 'reachable_helpers': sorted(set(discovered) - {name}),
                'calls_found': [{'in': owner, **call} for owner, found in discovered.items() for call in found],
                'facts_cites': fact['cites'], 'facts_shared_steps': fact['shared_steps'],
                'facts_inherited_helpers': sorted('Elements.' + n for n in inherited),
                'source_cites': sorted(dependencies, key=lambda r: (heath.prop_key(r), r)),
                'unresolved_names': unresolved, 'row': None,
                'helper_bodies_audited': False}


def tables(e: Evidence, source: dict, path: str, record: dict, keys: tuple[str, ...]) -> dict:
    result = {}
    raw = e.read(path)
    for key in keys:
        if key not in record:
            continue
        found = re.search(r'^\[' + re.escape(key) + r'\]\s*\n', raw, re.M)
        require(found is not None, f'{path}: missing original [{key}]')
        following = re.search(r'^\[', raw[found.end():], re.M)
        end = found.end() + following.start() if following else len(raw)
        original = e.excerpt(source, 'record.' + key, path, found.start(), end,
                             transformation='tomllib table; statement fingerprint omitted' if key == 'statement'
                             else 'tomllib table')
        parsed = tomllib.loads(original)[key]
        require(parsed == record[key], f'{path}: table extraction mismatch for {key}')
        if key == 'statement':
            parsed.pop('fingerprint', None)
        result[key] = parsed
    return result


def terms(e: Evidence, source: dict, record: dict) -> dict:
    path = 'review/terms.toml'
    raw = e.read(path)
    valid = heath.load_terms()
    result = {}
    for tag in record.get('representation', {}).get('tags', []):
        require(tag in valid, f'{path}: unknown representation {tag}')
        found = re.search(r'^\[tag\.' + re.escape(tag) + r'\]\s*\n', raw, re.M)
        require(found is not None, f'{path}: missing tag {tag}')
        following = re.search(r'^\[', raw[found.end():], re.M)
        end = found.end() + following.start() if following else len(raw)
        text = e.excerpt(source, 'terms.' + tag, path, found.start(), end, transformation='tomllib table')
        result[tag] = tomllib.loads(text)['tag'][tag]
        require(result[tag] == valid[tag], f'{path}: changed term {tag}')
    return result


def heath_text(e: Evidence, source: dict, book: str, n: int, *, proof: bool = True,
               field: str = '') -> dict:
    path = relative(heath.heath_path(book, n))
    raw = e.read(path)
    _, enunciation, paragraphs = heath.read(book, n)
    matches = list(re.finditer(r'^\*([^\n]+)\*([^\n]*)$', raw, re.M))
    require(len(matches) == 1, f'{path}: expected one single-line italic enunciation')
    match = matches[0]
    result = {'enunciation': e.excerpt(source, field + 'enunciation', path, *match.span(1))}
    require(heath.normalize(result['enunciation'] + match.group(2)) == enunciation,
            f'{path}: enunciation mismatch')
    if match.group(2).strip():
        result['enunciation_reference'] = e.excerpt(source, field + 'enunciation_reference',
                                                   path, *match.span(2))
    if proof:
        start = match.end()
        while start < len(raw) and raw[start].isspace():
            start += 1
        result['heath_proof'] = e.excerpt(source, field + 'heath_proof', path, start, len(raw))
        checked = heath.HTML_COMMENT.sub('', raw[start:])
        require([heath.normalize(p) for p in checked.split('\n\n') if p.strip()] == paragraphs,
                f'{path}: proof extraction mismatch')
    if heath.bracketed(book, n):
        heading = re.search(r'^# \[.*$', raw, re.M)
        require(heading is not None, f'{path}: bracketed heading missing')
        result['heath_heading'] = e.excerpt(source, field + 'heath_heading', path, *heading.span())
    porism = heath.heath_porism(book, n)
    if porism:
        matches = [m for m in re.finditer(r'[^\n]+(?:\n(?!\n)[^\n]+)*', raw)
                   if heath.normalize(m.group()) == porism]
        require(len(matches) == 1, f'{path}: porism paragraph is not unique')
        result['heath_porism'] = e.excerpt(source, field + 'heath_porism', path, *matches[0].span())
    return result


def statement(index: Index, source: dict, ref: str, field: str) -> str:
    parsed = heath.parse_ref(ref)
    d = index.get(parsed.lean)
    if parsed.kind == 'proposition':
        span = heath.theorem_span(index.evidence.read(d.path), parsed.n)
        require(span and span.start == d.start and span.start <= d.keyword < span.end,
                f'{ref}: main theorem disagrees with heath.theorem_span')
    return index.quote(source, field, d.name, doc=False)


def caption(e: Evidence, source: dict, book: str, n: int) -> str:
    path = f'book/{book}/{n:02d}.md'
    raw = e.read(path)
    image = f'../../figures/{book}/{n:02d}.svg'
    require(raw.count(image) == 1, f'{path}: Heath image is not unique')
    start = raw.index(image)
    image_end = raw.find('</p>', start)
    require(image_end >= 0, f'{path}: image paragraph missing')
    tail = raw[image_end + 4:]
    found = re.match(r'\s*(<p[^>]*>\s*<em>.*?</em>\s*</p>)', tail, re.S)
    if found:
        return e.excerpt(source, 'caption', path, image_end + 4 + found.start(1),
                         image_end + 4 + found.end(1))
    return ''


SCOPE = {
    'type': 'choice',
    'instructions': "Does the Lean statement cover the enunciation? The enunciation is `enunciation`, Euclid's words in Heath's translation; the main Lean statement is `lean_statement`, with its porism and companions in `attached_statements`; `record` is what the review record says about the statement's scope. Judge these declarations together, including the porism when one is supplied, using the notation, definitions and representation qualifications given here.",
    'criteria': {
        'fully': "The Lean statements together prove every clause of `enunciation` and of the supplied porism for every configuration Euclid's words admit, in the stated representation. A hypothesis that only names what his words already presuppose, as that the corners of a triangle are not on one straight line, is not a restriction.",
        'restricted, exactly as the note says': "The Lean statements together leave out some configuration Euclid's words admit, or leave some clause without a formal conclusion, and `record` names every such restriction and omission.",
        'restricted beyond what the note says': 'The Lean statements together leave out some configuration Euclid\'s words admit, or leave some clause without a formal conclusion, that `record` does not name. A record whose scope is "full" names none.',
        'cannot tell': 'What is given here is not enough to decide.',
    },
}
CITATIONS = {
    'type': 'choice',
    'instructions': "Does every proposition called by the proof unit in `lean_proof` do work towards its conclusion or a substantive intermediate step of Euclid's argument? Also check for artificial hypothesis uses. Judge this unit's uses of the supplied helper signatures; helper bodies are outside this question. Heath's sentences stand as `--` lines and `cited` gives exact enunciations. In Lean, `have h : T := p` proves T by p and calls the result h; `obtain ⟨…⟩ := p` takes p apart into named pieces; `rw [h34, h37, …]` rewrites the goal by the equalities named. Follow uses through helper calls and tactics as well as explicit names. An anonymous binding or an unused hypothesis alone does not establish a defect. If both defects occur, choose `a dummy citation`.",
    'criteria': {
        'all do work': 'Every proposition call supports a later step or the conclusion, or establishes a substantive intermediate fact tied to a real sentence of Euclid. No hypothesis is mentioned merely to look used. With no proposition calls the citation part alone is vacuous; hypothesis use must still be inspected.',
        'a dummy citation': 'Some proposition call does no substantive work: its result neither supports the argument nor establishes a substantive intermediate fact, and merely supplies a citation while the step is done another way.',
        'an artificial hypothesis use': 'No dummy citation is established, but a hypothesis is mentioned only so that it looks used, and does no substantive work.',
        'cannot tell': 'What is given here is not enough to decide.',
    },
}
REPRESENTATION = {
    'type': 'choice',
    'instructions': "Do the supplied definitions and bridge signatures state the conditional connections between the represented objects named in `represented_objects` and Euclid's objects in `enunciation`, within the convention and limitations in `record` and `terms`? Check all hypotheses and conclusions. A definition may itself supply a connection; a choice definition alone does not prove that its choice represents a given object. `bridge_placement` distinguishes declarations available before the main theorem from explanatory declarations at or after it; the latter are not premises available to that proof. This question asks what the supplied declarations state, not whether each invocation meets its premises, whether a proof passes Lean or whether the bridges are placed correctly in the dependency order. A `bridge stated` answer alone therefore does not establish all of P13. A missing supplied bridge does not establish that none exists elsewhere.",
    'criteria': {
        'bridge stated': 'The supplied declarations state each needed conditional connection under the relevant hypotheses and within the disclosed convention.',
        'bridge missing or inadequate': 'A needed connection has no adequate declaration supplied, or its premises make it unavailable for the represented objects under discussion.',
        'no bridge required': 'The supplied material uses no representation requiring such a bridge; a tag may instead describe a change of hypotheses or scope.',
        'cannot tell': 'The supplied context is insufficient to judge the conditional connection or its intended hypotheses.',
    },
}
COMMENTARY = {
    'type': 'choice',
    'instructions': "Does what `commentary` says about the statement's scope, the route of the proof and the named Lean declarations agree with the supplied statements, declaration signatures and record? Judge the mathematical account under the disclosed conventions. Quotation accuracy, historical attribution and voice are outside this question. Signatures alone need not settle a claim about a proof's internal steps; choose `cannot tell` where the supplied evidence does not settle it.",
    'criteria': {
        'agrees': 'The commentary agrees with the supplied scope, declared route and named declarations.',
        'conflicts': 'A mathematical claim about the scope, route or a named declaration conflicts with the supplied evidence.',
        'cannot tell': 'What is given here is not enough to decide.',
    },
}
FIGURE = {
    'type': 'choice',
    'instructions': "Does the image named in `figure` agree with `heath_proof`, the main Lean statement and its own caption? Check the letters, incidence, betweenness, order and sides for the stage illustrated. A drawing need not depict every configuration of the theorem. For an impossible supposition in a reductio, allow only the specific incompatibility identified in the caption as belonging to that supposition. All other relationships must agree, and the caption's own claims must match the image. An ordinary error remains a defect even if disclosed. Judge geometry, not numerical accuracy measured from pixels.",
    'criteria': {
        'agrees': 'The letters and arrangement agree with the illustrated stage, and the caption describes the image accurately; only a specifically identified incompatibility of an impossible supposition is excepted.',
        'disagrees': 'A letter, geometric relationship or caption conflicts with the illustrated stage beyond that specific reductio exception.',
        'cannot tell': 'What is given here is not enough to decide.',
    },
}


class Generator:
    def __init__(self, commit: str):
        self.evidence = Evidence(commit)
        self.index = Index(self.evidence)
        self.facts_data = json.loads(self.evidence.read('facts.json'))
        self.facts = {p['ref']: p for p in self.facts_data['propositions']}
        require(len(self.facts) == len(self.facts_data['propositions']), 'duplicate facts.json reference')
        self.calls = Calls(self.index, self.facts)
        self.rows: list[dict] = []
        self.coverage: dict[str, dict] = {}
        for path in ('scripts/heath.py', 'scripts/audit/jev.py', 'review/SCHEMA.md', 'Certificate/FIELDS.md'):
            self.evidence.read(path)

    def source(self, book: str, n: int) -> dict:
        return {'commit': self.evidence.commit, 'heath': f'heath/{book}/{n:02d}.md',
                'lean': f'Elements/Book{book}/Prop{n:02d}.lean', 'record': f'review/{book}/{n:02d}.toml',
                'facts': 'facts.json', 'excerpts': []}

    def row(self, ref: str, item: int, suffix: str, source: dict, state: dict,
            question: dict, verdict: str | None, expectation: dict[str, str], key: str) -> dict:
        table, field = key.rsplit('.', 1)
        row = {'id': f'{item:02d}-{ref.replace(" ", "-").replace("Por.", "porism")}-{suffix}',
               'item': item, 'ref': ref, 'seeded': False, 'source': source,
               'why': f'{source["record"]} [{table}].{field} = {dumps(verdict)}; '
                      'the expectation reports the record\'s claim for this bounded question.',
               'state': state, 'question': copy.deepcopy(question)}
        if verdict in expectation:
            row['expected'] = expectation[verdict]
        else:
            row['expectation_unavailable'] = {'field': key, 'verdict': verdict}
        self.rows.append(row)
        return row

    def signatures(self, source: dict, names: list[str], field: str) -> dict:
        return {n: self.index.quote(source, field + '.' + n, n) for n in sorted(set(names))}

    def bridges(self, source: dict, book: str, n: int) -> tuple[dict, list[str], dict]:
        objects, names = bundle(book, n)
        quoted = {name: self.index.quote(source, 'bridges.' + name, name,
                                        full=self.index.get(name).kind in ('def', 'abbrev'))
                  for name in sorted(set(names))}
        main = self.index.get(heath.parse_ref(f'{book}.{n}').lean)
        placement = {}
        for name in names:
            d = self.index.get(name)
            calls = self.calls.direct(name)
            prop_calls = [c for c in calls if re.search(r'\.Book[IVX]+\.Prop\d+', c['name'])]
            available = (d.path in self.index.visible(main.path) and
                         (d.path != main.path or d.keyword < main.keyword))
            # These signatures explain a representation, and may be corollaries of
            # the consumer. They must never be misreported as available premises.
            placement[name] = {'path': d.path, 'line': self.index.clean[d.path].count('\n', 0, d.keyword) + 1,
                               'available_before_main': available,
                               'role': 'available declaration' if available else 'explanatory later declaration',
                               'body_proposition_calls': prop_calls}
            require(book != 'I' or '/BookII/' not in d.path,
                    f'{book}.{n}: a Book II bridge cannot justify Book I')
        extra = {'bridge_context': self.index.context(source, 'bridge_context', names),
                 'consumer_imports': self.index.import_text(source, 'consumer_imports', main.path),
                 'bridge_imports': {path: self.index.import_text(source, 'bridge_imports.' + path, path)
                                    for path in sorted({self.index.get(name).path for name in names})}}
        return quoted, objects, {'state': extra, 'placement': placement}

    def cited(self, source: dict, refs: list[str]) -> dict:
        result = {}
        for ref in sorted(set(refs), key=lambda r: (heath.prop_key(r), r)):
            p = heath.parse_ref(ref)
            result[ref] = heath_text(self.evidence, source, p.book, p.n, proof=False,
                                     field='cited.' + ref + '.')
        return result

    def proposition(self, book: str, n: int) -> None:
        e, index = self.evidence, self.index
        ref = f'{book}.{n}'
        fact = self.facts[ref]
        path = f'review/{book}/{n:02d}.toml'
        record = tomllib.loads(e.read(path))
        # load_review also reads Heath's text (including the porism) and, for
        # representation tags, the terms catalogue. Guard all three before the helper.
        e.read(relative(heath.heath_path(book, n)))
        e.read('review/terms.toml')
        heath.load_review(book, n)
        require(record['statement']['fingerprint'] == heath.review_fingerprint(self.facts_data, ref),
                f'{path}: stale statement fingerprint')
        lean = heath.lean_path(book, n)
        e.read(relative(lean))
        require(record['review']['lean'] == heath.file_hash(lean),
                f'{path}: stale Lean fingerprint')
        attached = sorted(fact['attached'], key=lambda r: (heath.prop_key(r), r))
        require(attached == fact['attached'], f'{ref}: attachment order differs from contract')
        require(set(attached) == {p['ref'] for p in self.facts.values() if p.get('of') == ref},
                f'{ref}: attachment coverage mismatch')
        require(set(record['statement'].get('companions', [])) ==
                {a for a in attached if self.facts[a]['kind'] == 'companion'},
                f'{ref}: record companions differ from facts.json')
        for target in [ref] + attached:
            require(heath.parse_ref(target).lean == 'Elements.' + self.facts[target]['name'],
                    f'{target}: declaration name differs from facts.json')
        verdicts = record['review'].get('items', {})
        coverage = {'rows': [], 'proof_units': [], 'commentary_non_declarations': []}
        self.coverage[ref] = coverage
        first = len(self.rows)

        source = self.source(book, n)
        state = {'proposition': ref, **heath_text(e, source, book, n),
                 'lean_statement': statement(index, source, ref, 'lean_statement'),
                 'attached_statements': {a: statement(index, source, a, 'attached_statements.' + a)
                                         for a in attached},
                 'record': tables(e, source, path, record, ('statement', 'representation', 'coverage')),
                 'terms': terms(e, source, record)}
        bridges, objects, bridge_info = self.bridges(source, book, n)
        if bridges:
            state['bridges'] = bridges
            state.update(bridge_info['state'])
        state.update(glossary(index, source,
                              [state['lean_statement'], *state['attached_statements'].values(), *bridges.values()],
                              objects))
        state['statement_context'] = index.context(source, 'statement_context',
                                                    [heath.parse_ref(a).lean for a in [ref] + attached])
        self.row(ref, 9, 'scope', source, state, SCOPE, record['statement']['scope'],
                 {'full': 'fully', 'restricted': 'restricted, exactly as the note says',
                  'partial': 'restricted, exactly as the note says'}, 'statement.scope')

        for target in [ref] + attached:
            unit = self.calls.unit(target)
            coverage['proof_units'].append(unit)
            if target != ref and not unit['source_cites']:
                unit['omission_reason'] = 'Attachment calls no proposition or proposition-derived helper.'
                continue
            source = self.source(book, n)
            name = heath.parse_ref(target).lean
            signatures = {c['name'] for c in unit['calls_found'] if c['name'] != name}
            signatures |= {'Elements.' + self.facts[r]['name'] for r in unit['facts_cites']}
            signatures |= set(unit['reachable_helpers'])
            signatures |= set(unit['facts_inherited_helpers'])
            helpers = self.signatures(source, sorted(signatures), 'helper_signatures')
            state = {'proposition': ref, 'proof_unit': target, **heath_text(e, source, book, n),
                     'lean_proof': index.quote(source, 'lean_proof', name, full=True),
                     'helper_signatures': helpers,
                     'declaration_context': index.context(source, 'declaration_context', [name, *signatures])}
            heath_refs = heath.citations(heath.read(book, n)[2])
            state['cited'] = self.cited(source, [*heath_refs, *unit['facts_cites'], *unit['source_cites']])
            state['citation_origins'] = {'heath': sorted(heath_refs, key=lambda r: (heath.prop_key(r), r)),
                                         'certificate': unit['facts_cites'], 'source': unit['source_cites']}
            state.update(glossary(index, source, [state['lean_proof'], *helpers.values()]))
            question = copy.deepcopy(CITATIONS)
            policy_path = 'docs/FORMALIZATION.md'
            policy = e.read(policy_path)
            anchor = 'A checked intermediate fact tied to a real sentence of Euclid is legitimate, even if the\n  final proof term could do without it.'
            require(policy.count(anchor) == 1, f'{policy_path}: policy quotation is not unique')
            start = policy.index(anchor)
            quoted = e.excerpt(source, 'question.instructions.policy', policy_path, start, start + len(anchor))
            question['instructions'] += '\n\n' + policy_path + ', section 5:\n' + quoted
            row = self.row(target, 10, 'citations', source, state, question, verdicts.get('passages'),
                           {'pass': 'all do work'}, 'review.items.passages')
            unit['row'] = row['id']
            for call in unit['calls_found']:
                call['row'] = row['id']
                call['evidence'] = 'body' if call['in'] == name else 'reachable helper signature only'

        source = self.source(book, n)
        bridges, objects, bridge_info = self.bridges(source, book, n)
        state = {'proposition': ref, **heath_text(e, source, book, n, proof=False),
                 'lean_statement': statement(index, source, ref, 'lean_statement'),
                 'attached_statements': {a: statement(index, source, a, 'attached_statements.' + a)
                                         for a in attached},
                 'record': tables(e, source, path, record, ('statement', 'representation')),
                 'terms': terms(e, source, record), 'represented_objects': objects, 'bridges': bridges,
                 'bridge_placement': bridge_info['placement'],
                 **bridge_info['state']}
        state.update(glossary(index, source,
                              [state['lean_statement'], *state['attached_statements'].values(), *bridges.values()],
                              objects))
        state['statement_context'] = index.context(source, 'statement_context',
                                                    [heath.parse_ref(a).lean for a in [ref] + attached])
        coverage['bridge_placement'] = bridge_info['placement']
        self.row(ref, 11, 'representation', source, state, REPRESENTATION, verdicts.get('representations'),
                 {'pass': 'bridge stated', 'fail': 'bridge missing or inadequate', 'n/a': 'no bridge required'},
                 'review.items.representations')

        source = self.source(book, n)
        mishnah = e.whole(source, 'commentary', f'mishnah/{book}/{n:02d}.md')
        named = []
        consumer = index.get(heath.parse_ref(ref).lean)
        for token in sorted(set(re.findall(r'`([^`]+)`', mishnah))):
            resolved = index.resolve(token, consumer, commentary=True) if re.fullmatch(NAME, token) else None
            if resolved:
                named.append(resolved)
            else:
                coverage['commentary_non_declarations'].append(token)
        declarations = self.signatures(source, named, 'named_declarations')
        state = {'proposition': ref, 'commentary': mishnah,
                 'heath_proof': heath_text(e, source, book, n)['heath_proof'],
                 'lean_proof': index.quote(source, 'lean_proof', consumer.name, full=True),
                 'record': tables(e, source, path, record, ('statement', 'route')),
                 'lean_statement': statement(index, source, ref, 'lean_statement'),
                 'attached_statements': {a: statement(index, source, a, 'attached_statements.' + a)
                                         for a in attached}, 'named_declarations': declarations,
                 'declaration_context': index.context(source, 'declaration_context',
                                                       [consumer.name, *named, *[heath.parse_ref(a).lean for a in attached]])}
        state.update(glossary(index, source,
                              [state['lean_statement'], *state['attached_statements'].values(),
                               state['lean_proof'], *declarations.values()]))
        self.row(ref, 12, 'commentary', source, state, COMMENTARY, verdicts.get('commentary'),
                 {'pass': 'agrees'}, 'review.items.commentary')

        source = self.source(book, n)
        heath_state = heath_text(e, source, book, n)
        # R4 fixes this state's evidence narrowly; headings remain part of Heath's text.
        heath_state.pop('heath_porism', None)
        state = {**heath_state, 'lean_statement': statement(index, source, ref, 'lean_statement'),
                 'caption': caption(e, source, book, n), 'figure': f'JEV_HEATH_{book}_{n}'}
        row = self.row(ref, 13, 'figure', source, state, FIGURE, verdicts.get('figures'),
                       {'pass': 'agrees'}, 'review.items.figures')
        figure_path = f'figures/{book}/{n:02d}.svg'
        e.read(figure_path)
        source['figure'] = figure_path
        source['page'] = f'book/{book}/{n:02d}.md'
        row['assets'] = {state['figure']: figure_path}
        coverage['rows'] = [r['id'] for r in self.rows[first:]]

    def controls(self) -> None:
        originals = {r['id']: r for r in self.rows}
        counts: Counter = Counter()

        def control(rid: str, expected: str) -> dict:
            row = copy.deepcopy(originals[rid])
            counts[row['item']] += 1
            row['id'] += f'-seeded-{counts[row["item"]]}'
            row['seeded'] = True
            row['expected'] = expected
            row['why'] = 'Synthetic defect control; the mutation, not the record, determines the expectation.'
            row['mutation'] = {'base_id': rid, 'base_state_sha256': sha(dumps(row['state'])), 'changes': []}
            self.rows.append(row)
            parent = heath.parse_ref(row['ref']).parent
            self.coverage[parent]['rows'].append(row['id'])
            return row

        def change(row: dict, field: list[str], old: str, new: str) -> None:
            value = row
            for part in field[:-1]:
                value = value[part]
            text = value[field[-1]]
            require(isinstance(text, str) and text.count(old) == 1,
                    f'{row["id"]}: mutation anchor is not unique: {old!r}')
            value[field[-1]] = text.replace(old, new)
            row['mutation']['changes'].append({'operation': 'replace', 'field': field, 'old': old, 'new': new,
                                               'before_sha256': sha(text), 'after_sha256': sha(value[field[-1]])})

        def remove(row: dict, field: list[str]) -> None:
            value = row
            for part in field[:-1]:
                value = value[part]
            old = value.pop(field[-1])
            row['mutation']['changes'].append({'operation': 'remove', 'field': field, 'old': old,
                                               'before_sha256': sha(old if isinstance(old, str) else dumps(old))})

        row = control('09-I.6-scope', 'restricted beyond what the note says')
        change(row, ['state', 'lean_statement'], '(hABC : Triangle A B C)',
               '(hABC : Triangle A B C) (hACBC : ‖A C‖ = ‖B C‖)')
        row = control('09-I.5-scope', 'restricted beyond what the note says')
        change(row, ['state', 'lean_statement'], ' ∧ ∠ C B D = ∠ B C E', '')
        row = control('10-I.41-citations', 'a dummy citation')
        change(row, ['state', 'lean_proof'], ':= by\n',
               ':= by\n  have unrelated := @Elements.BookI.Prop15\n')
        row['state']['helper_signatures']['Elements.BookI.Prop15'] = self.index.quote(
            row['source'], 'helper_signatures.Elements.BookI.Prop15', 'Elements.BookI.Prop15')
        row['state']['cited'].update(self.cited(row['source'], ['I.15']))
        row['state']['declaration_context'].update(self.index.context(
            row['source'], 'declaration_context', ['Elements.BookI.Prop15']))
        for origin in ('certificate', 'source'):
            old = row['state']['citation_origins'][origin]
            new = sorted([*old, 'I.15'], key=lambda r: (heath.prop_key(r), r))
            row['state']['citation_origins'][origin] = new
            row['mutation']['changes'].append({'operation': 'replace',
                                               'field': ['state', 'citation_origins', origin],
                                               'old': old, 'new': new,
                                               'before_sha256': sha(dumps(old)),
                                               'after_sha256': sha(dumps(new))})
        row['mutation']['added_evidence'] = [
            'Elements.BookI.Prop15', 'I.15',
            'citation_origins.certificate:I.15', 'citation_origins.source:I.15'
        ]
        row = control('10-I.41-citations', 'an artificial hypothesis use')
        change(row, ['state', 'lean_proof'], '(hE : Collinear A D E)',
               '(hE : Collinear A D E) (hAA : A = A)')
        change(row, ['state', 'lean_proof'], ':= by\n', ':= by\n  have unused := hAA\n')
        row = control('11-II.4-representation', 'bridge missing or inadequate')
        for name in list(row['state']['bridges']):
            remove(row, ['state', 'bridges', name])
            remove(row, ['state', 'bridge_context', name])
            remove(row, ['state', 'bridge_placement', name])
        remaining_paths = {self.index.get(name).path for name in row['state']['bridges']}
        for path in list(row['state']['bridge_imports']):
            if path not in remaining_paths:
                remove(row, ['state', 'bridge_imports', path])
        row = control('11-II.4-representation', 'bridge missing or inadequate')
        for name in row['state']['bridges']:
            d = self.index.get(name)
            raw = self.evidence.read(d.path)
            anchor = raw[d.keyword:d.name_end]
            change(row, ['state', 'bridges', name], anchor, anchor + ' (impossible : False)')
        for rid, wrong in [('13-I.37-figure', 'figures/I/01.svg'), ('13-II.4-figure', 'figures/I/31.svg')]:
            row = control(rid, 'disagrees')
            key = row['state']['figure']
            change(row, ['assets', key], row['assets'][key], wrong)
            self.evidence.read(wrong)
            row['source']['control_figure'] = wrong
        row = control('12-I.39-commentary', 'conflicts')
        change(row, ['state', 'commentary'], 'EBC is a part of DBC and the less',
               'EBC is a part of DBC and the greater')
        row = control('12-I.40-commentary', 'conflicts')
        change(row, ['state', 'commentary'], 'our I.38 makes ABC equal to FCE',
               'our I.38 makes ABC greater than FCE')
        require(dict(counts) == {9: 2, 10: 2, 11: 2, 13: 2, 12: 2}, 'control coverage changed')

    def finish(self) -> tuple[bytes, bytes, dict]:
        for book, count in [('I', 48), ('II', 14)]:
            for n in range(1, count + 1):
                self.proposition(book, n)
        self.controls()
        # Parents, numeric item, main unit before attachments, then controls of that item.
        self.rows.sort(key=lambda r: (heath.prop_key(heath.parse_ref(r['ref']).parent), r['item'],
                                      r['seeded'], heath.prop_key(r['ref']), r['ref'], r['id']))
        ordinals: Counter = Counter()
        seen: set[str] = set()
        for row in self.rows:
            criteria = list(row['question']['criteria'].items())
            offset = ordinals[row['seeded']] % len(criteria)
            ordinals[row['seeded']] += 1
            row['question']['criteria'] = dict(criteria[offset:] + criteria[:offset])
            row['option_rotation'] = offset
            row['state_characters'] = len(dumps(row['state']))
            row['long_context'] = row['state_characters'] > LIMIT
            problems = jev.check_row(row, row['id'], seen)
            require(not problems, '\n'.join(problems))
            require(not any(k in row['state'] for k in ('review', 'expected', 'why', 'source', 'long_context')),
                    f'{row["id"]}: local labels leaked into state')
            require('fingerprint' not in row['state'].get('record', {}).get('statement', {}),
                    f'{row["id"]}: fingerprint leaked into state')
            if row['item'] in (10, 13):
                require('record' not in row['state'], f'{row["id"]}: review record leaked')
            for excerpt in row['source']['excerpts']:
                raw = self.evidence.read(excerpt['path'])
                require(sha(raw[excerpt['start']:excerpt['end']]) == excerpt['sha256'],
                        f'{row["id"]}: source slice changed')
            # Every quoted source and every control asset has its original file hash.
            paths = {x['path'] for x in row['source']['excerpts']}
            paths |= {row['source'][k] for k in ('heath', 'lean', 'record', 'facts')}
            paths |= set(row.get('assets', {}).values())
            if 'page' in row['source']:
                paths.add(row['source']['page'])
            row['source']['files'] = {p: sha(self.evidence.read(p)) for p in sorted(paths)}
        by_id = {r['id']: r for r in self.rows}
        for ref, coverage in self.coverage.items():
            coverage['unresolved_names'] = sorted({token for unit in coverage['proof_units']
                                                   for token in unit['unresolved_names']})
            coverage['rows'] = [r['id'] for r in self.rows if heath.parse_ref(r['ref']).parent == ref]
            coverage['states'] = {rid: {'characters': by_id[rid]['state_characters'],
                                       'long_context': by_id[rid]['long_context'],
                                       'seeded': by_id[rid]['seeded']} for rid in coverage['rows']}
        self.evidence.unchanged()
        counts = {str(item): {'not_seeded': sum(r['item'] == item and not r['seeded'] for r in self.rows),
                             'seeded': sum(r['item'] == item and r['seeded'] for r in self.rows)}
                  for item in range(9, 14)}
        largest = max(self.rows, key=lambda r: r['state_characters'])
        unresolved = sorted({token for names in self.calls.unresolved.values() for token in names})
        require(not unresolved, f'unresolved names: {unresolved}')
        manifest = {'commit': self.evidence.commit,
                    'evidence_verification': 'all evidence bytes equal git show',
                    'state_size_measure': 'len(json.dumps(state, ensure_ascii=False, allow_nan=False))',
                    'long_context_threshold': LIMIT, 'rows': len(self.rows), 'rows_by_item': counts,
                    'proof_units': sum(len(p['proof_units']) for p in self.coverage.values()),
                    'long_context_states': sum(r['long_context'] for r in self.rows),
                    'largest_state': {'id': largest['id'], 'characters': largest['state_characters']},
                    'unresolved_names': unresolved,
                    'core_projection_allowlist': sorted(Calls.CORE_FIELDS),
                    'coverage_limits': [
                        'Citation questions inspect one unit body and helper signatures, not helper bodies.',
                        'Reachable helper calls are reconciled locally; their bodies receive no independent question.',
                        'Representation questions inspect conditional statements, not premise discharge or kernel checks.',
                        'Representation rows supply dependency placement as context in bridge_placement, but do not '
                        'adjudicate it; a bridge-stated answer does not establish correct placement or all of P13.',
                        'Commentary questions exclude quotation accuracy, attribution and voice.',
                        'Figure questions inspect the Heath figure only.',
                        'Record expectations are claims to test, not independent findings.',
                        'Score controls and production rows separately by item, option order and long_context; '
                        'an order disagreement remains unresolved regardless of the client agreement bar.'
                    ], 'propositions': self.coverage,
                    'evidence_files': {p: sha(raw) for p, raw in sorted(self.evidence.data.items())}}
        rows_bytes = ''.join(dumps(r) + '\n' for r in self.rows).encode('utf-8')
        manifest['questions_sha256'] = sha(rows_bytes)
        manifest_bytes = (json.dumps(manifest, ensure_ascii=False, allow_nan=False, indent=2) + '\n').encode('utf-8')
        require('\u2014' not in rows_bytes.decode() and '\u2014' not in manifest_bytes.decode(),
                'an evidence excerpt contains prohibited punctuation')
        return rows_bytes, manifest_bytes, manifest


def file_identity(path: Path) -> tuple[int, int] | None:
    try:
        info = path.stat()
    except FileNotFoundError:
        return None
    return info.st_dev, info.st_ino


def protected_paths() -> set[Path]:
    """Read the protected tuples without importing or running the push script."""
    policy = 'scripts/safe_push.py'
    try:
        tree = ast.parse(read_no_follow(evidence_path(policy)), filename=policy)
    except SyntaxError as error:
        raise Refusal(f'{policy}: cannot parse protected path lists: {error}') from error
    values: dict[str, tuple[str, ...]] = {}
    names = {'PROTECTED', 'PROTECTED_JUDGED'}
    for node in tree.body:
        if (isinstance(node, ast.Assign) and len(node.targets) == 1
                and isinstance(node.targets[0], ast.Name) and node.targets[0].id in names):
            value = ast.literal_eval(node.value)
            require(isinstance(value, tuple) and value and all(isinstance(p, str) for p in value),
                    f'{policy}: protected paths must be nonempty tuples of strings')
            values[node.targets[0].id] = value
        elif (isinstance(node, ast.AugAssign) and isinstance(node.target, ast.Name)
              and node.target.id == 'PROTECTED'):
            require(isinstance(node.op, ast.Add) and isinstance(node.value, ast.Name)
                    and node.value.id in values and 'PROTECTED' in values,
                    f'{policy}: unsupported protected path extension')
            values['PROTECTED'] += values[node.value.id]
    require(names <= values.keys() and set(values['PROTECTED_JUDGED']) <= set(values['PROTECTED']),
            f'{policy}: missing protected path lists or extension')
    # Standing ownership and source restrictions in AGENTS.md and docs/WORKFLOW.md,
    # section 4, beyond the push policy.
    declared = ('AGENTS.md', 'Elements/Foundations/', 'Elements/Companions.lean',
                'docs/briefs/0002-decisions.md', 'docs/decisions/', 'docs/PROGRAM.md',
                'docs/program.toml', 'facts.json', 'book/', 'CERTIFICATE.md', 'GRAPH.md',
                'README.md', 'heath/')
    roots = {ROOT / '.git'}
    for name in (*values['PROTECTED'], *declared,
                 'scripts/audit/jev_questions.py', 'scripts/heath.py', 'scripts/audit/jev.py'):
        path = Path(name)
        require(not path.is_absolute() and '..' not in path.parts and path.parts,
                f'{policy}: invalid protected path {name!r}')
        roots.add(ROOT / path)
    for arguments in (['--absolute-git-dir'], ['--path-format=absolute', '--git-common-dir']):
        result = subprocess.run(['git', 'rev-parse', *arguments], cwd=ROOT,
                                capture_output=True, check=False)
        require(result.returncode == 0,
                'cannot locate Git metadata: ' + result.stderr.decode('utf-8', errors='replace').strip())
        path = Path(os.fsdecode(result.stdout).rstrip('\n'))
        require(path.is_absolute(), 'Git metadata path must be absolute')
        roots.add(path)
    return roots | {path.resolve() for path in roots}


def protected_identities(roots: set[Path]) -> set[tuple[int, int]]:
    """Include untracked descendants so a hard link outside a protected tree is refused."""
    identities = set()

    def failed(error: OSError) -> None:
        raise error

    for root in roots:
        if any(root != parent and root.is_relative_to(parent) for parent in roots):
            continue
        identities.add(file_identity(root))
        if not root.is_dir():
            continue
        for directory, dirs, files in os.walk(root, onerror=failed):
            identities.update(file_identity(Path(directory) / name) for name in dirs + files)
    return identities - {None}


def output_paths(paths: list[Path], evidence_files: dict[str, str]) -> list[Path]:
    """Validate both destinations before reading or writing either one."""
    resolved = [checked_path(path) for path in paths]
    left, right = resolved
    identities = [file_identity(path) for path in resolved]
    # Treat names differing only in case as a collision even before either file exists,
    # so the same invocation is safe on both case-sensitive and case-insensitive volumes.
    same_name = (left.name.casefold() == right.name.casefold()
                 and file_identity(left.parent) is not None
                 and file_identity(left.parent) == file_identity(right.parent))
    require(left != right and not same_name
            and not (identities[0] is not None and identities[0] == identities[1]),
            'questions and manifest destinations must differ')
    evidence = {evidence_path(path) for path in evidence_files}
    evidence_ids = {file_identity(path) for path in evidence} - {None}
    result = subprocess.run(['git', 'ls-files', '-z'], cwd=ROOT, capture_output=True, check=False)
    require(result.returncode == 0,
            'cannot list tracked files: ' + result.stderr.decode('utf-8', errors='replace').strip())
    tracked = {ROOT / os.fsdecode(name) for name in result.stdout.split(b'\0') if name}
    protected = {path.resolve() for path in tracked if path not in DEFAULT_OUTPUTS}
    protected_names = {path.as_posix().casefold() for path in protected}
    protected_ids = {file_identity(path) for path in protected} - {None}
    for path, identity in zip(resolved, identities):
        require(path not in evidence and identity not in evidence_ids,
                f'{path}: destination would replace an evidence file')
        require(path.as_posix().casefold() not in protected_names and identity not in protected_ids,
                f'{path}: destination would replace a tracked input')
    roots = protected_paths()
    root_names = {path.as_posix().casefold() for path in roots}
    protected_ids = protected_identities(roots)
    for path in resolved:
        require(not any(parent.as_posix().casefold() in root_names
                        or file_identity(parent) in protected_ids
                        for parent in (path, *path.parents)),
                f'{path}: destination would replace a protected path or Git metadata')
    return resolved


def write_output(path: Path, data: bytes) -> None:
    """Replace the destination itself, never the target of a final symlink."""
    checked_path(path)
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(dir=path.parent, prefix=f'.{path.name}.', delete=False) as stream:
            temporary = Path(stream.name)
            stream.write(data)
        checked_path(path)
        os.replace(temporary, path)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--commit', required=True)
    parser.add_argument('--out', type=Path, default=OUTPUT)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args(argv)
    try:
        first = Generator(args.commit).finish()
        second = Generator(args.commit).finish()
        require(first[:2] == second[:2], 'two generations differ')
        rows, manifest_bytes, manifest = first
        paths = output_paths([args.out, MANIFEST], manifest['evidence_files'])
        destinations = list(zip(paths, (rows, manifest_bytes)))
        if args.check:
            different = [str(p) for p, data in destinations
                         if not checked_path(p).is_file() or read_no_follow(p) != data]
            require(not different, 'generated files differ: ' + ', '.join(different))
        else:
            for path, data in destinations:
                write_output(path, data)
        print(('Checked' if args.check else 'Wrote') + f' {manifest["rows"]} rows; two generations identical.')
        for item, count in manifest['rows_by_item'].items():
            print(f'Item {item}: {count["not_seeded"]} not seeded, {count["seeded"]} seeded.')
        print(f'Proof units: {manifest["proof_units"]}; long_context states: {manifest["long_context_states"]}.')
        print(f'Largest state: {manifest["largest_state"]["characters"]} characters, {manifest["largest_state"]["id"]}.')
        print(f'Unresolved names: {len(manifest["unresolved_names"])}. Evidence: '
              + manifest['evidence_verification'] + '.')
        return 0
    except (Refusal, jev.Failure, heath.ReviewError, OSError, ValueError, KeyError) as error:
        print(f'refused: {error}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
