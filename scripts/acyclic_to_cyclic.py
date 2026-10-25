#!/usr/bin/env python3
"""acyclic_to_cyclic.py FILE... (in place) | --out-dir DIR FILE...

Rewrites SMT-LIB files from the predicate rel.acyclic of cycle-ext to the
predicate rel.cyclic, with (rel.cyclic R) iff (x, x) in (rel.tclosure R) for
some x:

  (not (rel.acyclic (tuple R1 ... Rk)))  ->  (rel.cyclic U)
  (rel.acyclic (tuple R1 ... Rk))        ->  (not (rel.cyclic U))

where U is R1 for k = 1 and (set.union R1 (set.union R2 ... Rk)) otherwise
(rel.acyclic of a tuple meant acyclicity of the union of its relations).
Comments and all other text are kept. In regression headers, the options
--rels-acyclic-flatten-union and --rels-acyclic-self-loop, whose behaviour is
built into rel.cyclic, are removed.
"""
import os
import re
import sys


def skip_comment(s, i):
    while i < len(s) and s[i] != "\n":
        i += 1
    return i


def span_end(s, i):
    """s[i] == '('; return the index after the matching ')'."""
    depth, n = 0, len(s)
    while i < n:
        c = s[i]
        if c == ";":
            i = skip_comment(s, i)
            continue
        if c == '"':
            i += 1
            while i < n and s[i] != '"':
                i += 1
        elif c == "|":
            i += 1
            while i < n and s[i] != "|":
                i += 1
        elif c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
            if depth == 0:
                return i + 1
        i += 1
    raise ValueError("unbalanced parentheses")


def items(s):
    """Top-level items of the s-expression body s (no outer parentheses)."""
    out, i, n = [], 0, len(s)
    while i < n:
        c = s[i]
        if c.isspace():
            i += 1
        elif c == ";":
            i = skip_comment(s, i)
        elif c == "(":
            j = span_end(s, i)
            out.append(s[i:j])
            i = j
        else:
            j = i
            while j < n and not s[j].isspace() and s[j] not in "()":
                j += 1
            out.append(s[i:j])
            i = j
    return out


def union_of(rels):
    if len(rels) == 1:
        return rels[0]
    return "(set.union %s %s)" % (rels[0], union_of(rels[1:]))


def relation_of_acyclic(span):
    """span = '(rel.acyclic ARG)'; the relation whose acyclicity it states."""
    body = items(span[1:-1])
    assert body[0] == "rel.acyclic" and len(body) == 2, span[:80]
    arg = body[1]
    if arg.startswith("("):
        sub = items(arg[1:-1])
        if sub and sub[0] == "tuple":
            return union_of(sub[1:])
    raise ValueError("rel.acyclic of a non-tuple argument: %s" % arg[:80])


def convert(s):
    out, i, n, count = [], 0, len(s), 0
    while i < n:
        c = s[i]
        if c == ";":
            j = skip_comment(s, i)
            out.append(s[i:j])
            i = j
            continue
        if c == "(":
            j = span_end(s, i)
            head = items(s[i + 1:j - 1])
            if head and head[0] == "not" and len(head) == 2 and head[1].startswith("(rel.acyclic"):
                out.append("(rel.cyclic %s)" % convert(relation_of_acyclic(head[1]))[0])
                count += 1
                i = j
                continue
            if head and head[0] == "rel.acyclic":
                out.append("(not (rel.cyclic %s))" % convert(relation_of_acyclic(s[i:j]))[0])
                count += 1
                i = j
                continue
            out.append("(")
            i += 1
            continue
        out.append(c)
        i += 1
    return "".join(out), count


def fix_options(s):
    def fix(m):
        line = m.group(0)
        line = re.sub(r"\s*--rels-acyclic-flatten-union", "", line)
        line = re.sub(r"\s*--rels-acyclic-self-loop", "", line)
        return line
    return re.sub(r"^; COMMAND-LINE:.*$", fix, s, flags=re.M)


def main(argv):
    out_dir = None
    if argv and argv[0] == "--out-dir":
        out_dir, argv = argv[1], argv[2:]
        os.makedirs(out_dir, exist_ok=True)
    for f in argv:
        s = open(f).read()
        t, count = convert(s)
        t = fix_options(t)
        dst = os.path.join(out_dir, os.path.basename(f)) if out_dir else f
        open(dst, "w").write(t)
        print("%-60s %d rewritten" % (f, count))


if __name__ == "__main__":
    main(sys.argv[1:])
