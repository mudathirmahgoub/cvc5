#!/usr/bin/env python3
"""LaTeX tables and a markdown report from measure.py's usage.json and ablation.json.

usage: make_tables.py OUTDIR_OF_MEASURE FIGURES_DIR
writes FIGURES_DIR/evidence-matrix.tex, evidence-examples-*.tex and OUTDIR/REPORT.md
"""
import json
import os
import re
import sys

NAMES = {
    "SETS_RELS_ACYCLIC_SELF_LOOP": "Cycle-Def", "SETS_RELS_INST_CYCLE": "Inst-Cycle",
    "SETS_RELS_SAME_OPERANDS": "Same-Operands", "SETS_RELS_UNROLL_CYCLE": "Unroll",
    "SETS_RELS_SPLIT_CYCLE_LEN": "Split-Len", "SETS_RELS_ALTERNATE": "Alternate",
    "SETS_RELS_ALT_CLOSE": "Alt-Close", "SETS_RELS_CHORD": "Chord",
    "SETS_RELS_DISTINCT": "Distinct", "SETS_RELS_BACKWARD": "Backward",
    "SETS_RELS_LAST_CALL_COMPLETION": "LC completion", "SETS_RELS_ANCHOR_BRANCH": "Branch",
    "SETS_RELS_ACYCLIC_DOWN": "Acyclic-Down", "SETS_RELS_REGISTER": "Register",
    "SETS_RELS_ANCHOR_INCLUSION": "Inclusion", "SETS_RELS_ANCHOR_CONFLICT": "Anchor conflict",
    "SETS_RELS_TC_SUBSET_SYNTACTIC": "TC-Sub: in TC(X)", "SETS_RELS_TC_SUBSET_SELF": "TC-Sub: R trans.",
    "SETS_RELS_TC_SUBSET_PRODUCT": "TC-Sub: A×B", "SETS_RELS_TC_SUBSET_INTER_MINUS": "TC-Sub: ∩/∖",
    "SETS_RELS_TC_SUBSET_SUPERSET": "TC-Sub: R⊆S", "SETS_RELS_FUNCTIONAL": "Fun-UF",
    "SETS_RELS_FUNCTIONAL_PAIR": "Fun-Pairs", "SETS_RELS_NOT_FUNCTIONAL": "Not-Fun",
    "SETS_RELS_TCLOSURE_DOWN_LAZY": "TC-Down (lazy)",
    "SETS_RELS_TCLOSURE_GROUNDING_CONFLICT": "Ground-TC",
    "SETS_RELS_JOIN_GROUNDING_CONFLICT": "Ground-Join", "SETS_RELS_TCLOSURE_UP": "TC-Up",
    "SETS_RELS_TCLOSURE_DOWN": "TC-Down", "SETS_RELS_JOIN_COMPOSE": "Join-Compose",
    "SETS_RELS_JOIN_SPLIT_1": "Join-Split",
    "GROUP_CLOSURE_INDUCTION": "all TC-Subset", "GROUP_MINIMALITY": "all minimality",
    "GROUP_ANCHORS": "all anchors", "GROUP_FUNCTIONAL": "Fun-UF + Fun-Pairs",
}
CONFIGS = ["default", "fmf-unsat", "nofmf-unsat", "stoponly", "fmf-unsat-rules",
           "nofmf-unsat-rules", "nofmf-unsat-hammer"]
SHORT = {"default": "def", "fmf-unsat": "FMF", "nofmf-unsat": "noFMF", "stoponly": "stop",
         "fmf-unsat-rules": "FMF+R", "nofmf-unsat-rules": "noFMF+R", "nofmf-unsat-hammer": "noFMF+H"}
BSHORT = lambda b: b.replace("-th", "").replace("-just-rf", "r").replace("-no-ltts", "n").replace("-", "")


def parse(s):
    toks = re.findall(r"\(|\)|[^\s()]+", s)
    def rec(i):
        if toks[i] == "(":
            out, i = [], i + 1
            while toks[i] != ")":
                x, i = rec(i)
                out.append(x)
            return out, i + 1
        return toks[i], i + 1
    return rec(0)[0]


def unlet(t, env=None):
    env = env or {}
    if isinstance(t, str):
        return env.get(t, t)
    if t and t[0] == "let":
        env2 = dict(env)
        for b in t[1]:
            env2[b[0]] = unlet(b[1], env2)
        return unlet(t[2], env2)
    return [unlet(x, env) for x in t]


def pp(t):
    if isinstance(t, str):
        return re.sub(r"^(\w+?)_(\d+)$", r"\1\2", t)
    h = t[0]
    a = [pp(x) for x in t[1:]]
    if h == "rel.join": return f"{a[0]};{a[1]}"
    if h == "rel.tclosure": return (a[0] if re.fullmatch(r"[\w-]+", a[0]) else f"({a[0]})") + "+"
    if h == "rel.iden": return f"[{a[0]}]"
    if h == "rel.transpose": return f"({a[0]})^-1"
    if h == "rel.product": return f"{a[0]}×{a[1]}"
    if h == "set.union": return "(" + " ∪ ".join(a) + ")"
    if h == "set.inter": return "(" + " ∩ ".join(a) + ")"
    if h == "set.minus": return f"({a[0]} ∖ {a[1]})"
    if h == "set.member": return f"{a[0]} ∈ {a[1]}"
    if h == "tuple": return "(" + ",".join(a) + ")"
    if h == "=": return f"{a[0]} = {a[1]}"
    if h == "not":
        x = t[1]
        if isinstance(x, list) and x[0] == "set.member": return f"{pp(x[1])} ∉ {pp(x[2])}"
        if isinstance(x, list) and x[0] == "=": return f"{pp(x[1])} ≠ {pp(x[2])}"
        return "¬(" + a[0] + ")"
    if h in ("and", "or"):
        parts = []
        for x, px in zip(t[1:], a):
            nested = isinstance(x, list) and x and x[0] in ("and", "or") and x[0] != h
            parts.append(f"({px})" if nested else px)
        return (" ∧ " if h == "and" else " ∨ ").join(parts)
    if h == "as" and t[1] == "set.empty": return "∅"
    if h == "=>": return f"{a[0]} ⇒ {a[1]}"
    if h in ("<", "<=", ">=", ">"): return f"{a[0]} {h} {a[1]}"
    if h == "rel.cyclic": return f"cyc({a[0]})"
    if h == "rel.is-functional": return f"fun({a[0]})"
    if h == "distinct": return "distinct(" + ",".join(a) + ")"
    if h == "set.singleton": return "{" + a[0] + "}"
    if isinstance(h, list) and h and h[0] == "_" and h[1] == "tuple.select":
        return f"{a[0]}.{h[2]}"
    return "(" + " ".join([h if isinstance(h, str) else pp(h)] + a) + ")"


def tex(s):
    s = s.replace("\\", "\\textbackslash{}").replace("_", "\\_").replace("{", "\\{").replace("}", "\\}")
    for a, b in {"∈": "$\\in$", "∉": "$\\notin$", "∪": "$\\cup$", "∩": "$\\cap$", "∖": "$\\setminus$",
                 "×": "$\\times$", "⇒": "$\\Rightarrow$", "∧": "$\\wedge$", "∨": "$\\vee$",
                 "¬": "$\\neg$", "≠": "$\\ne$", "⊆": "$\\subseteq$", "∅": "$\\emptyset$", "·": "$\\cdot$", "^-1": "$^{-1}$", "<=": "$\\le$", ">=": "$\\ge$"}.items():
        s = s.replace(a, b)
    return s


def main():
    mdir, fdir = sys.argv[1:3]
    os.makedirs(fdir, exist_ok=True)
    usage = json.load(open(os.path.join(mdir, "usage.json")))
    abl = json.load(open(os.path.join(mdir, "ablation.json")))
    ablated = {k.split("||")[1] for k in abl}
    rules = [r for r in NAMES if any(u["counts"].get(r, 0) for u in usage.values()) or r in ablated]
    unused = [r for r in NAMES if r not in rules and not r.startswith("GROUP_")]
    lost, wrong, kept, fired = {}, {}, {}, {}
    for key, res in abl.items():
        pair, rule = key.split("||")
        b, c = pair.split("|")
        fired.setdefault(rule, {}).setdefault(c, []).append(b)
        if res["answer"] in ("sat", "unsat") and res["answer"] == usage[pair]["expected"]:
            kept.setdefault(rule, {}).setdefault(c, []).append(b)
        elif res["answer"] in ("sat", "unsat") or res["answer"] == "error" \
                or res["answer"].startswith("Fatal"):
            wrong.setdefault(rule, {}).setdefault(c, []).append(b)
        else:
            lost.setdefault(rule, {}).setdefault(c, []).append(b)
    # matrix: per rule and configuration, the benchmarks lost without it (bold),
    # wrong (red), or a dot if it fired but was not needed
    FAMILIES = [
        ["SETS_RELS_ACYCLIC_SELF_LOOP", "SETS_RELS_INST_CYCLE", "SETS_RELS_UNROLL_CYCLE",
         "SETS_RELS_SPLIT_CYCLE_LEN", "SETS_RELS_ALTERNATE", "SETS_RELS_ALT_CLOSE",
         "SETS_RELS_CHORD", "SETS_RELS_DISTINCT", "SETS_RELS_BACKWARD", "GROUP_MINIMALITY",
         "SETS_RELS_LAST_CALL_COMPLETION", "SETS_RELS_ANCHOR_BRANCH"],
        ["SETS_RELS_ACYCLIC_DOWN", "SETS_RELS_REGISTER", "SETS_RELS_ANCHOR_INCLUSION",
         "SETS_RELS_TC_SUBSET_SYNTACTIC", "SETS_RELS_TC_SUBSET_SELF", "SETS_RELS_TC_SUBSET_PRODUCT",
         "SETS_RELS_TC_SUBSET_INTER_MINUS", "SETS_RELS_TC_SUBSET_SUPERSET",
         "GROUP_CLOSURE_INDUCTION", "SETS_RELS_FUNCTIONAL"],
        ["SETS_RELS_TCLOSURE_DOWN_LAZY", "SETS_RELS_TCLOSURE_UP", "SETS_RELS_TCLOSURE_DOWN",
         "SETS_RELS_JOIN_COMPOSE", "SETS_RELS_JOIN_SPLIT_1"],
    ]
    lines = []
    md = ["| rule | " + " | ".join(SHORT[c] for c in CONFIGS) + " |",
          "|---|" + "---|" * len(CONFIGS)]
    fam_lines = {i: ["\\begin{tabular}{@{}l" + "p{1.62cm}" * len(CONFIGS) + "@{}}", "\\toprule",
                     "rule & " + " & ".join(SHORT[c] for c in CONFIGS) + " \\\\", "\\midrule"]
                 for i in range(len(FAMILIES))}
    for r in rules:
        cells, mcells = [], []
        for c in CONFIGS:
            l = sorted(lost.get(r, {}).get(c, []))
            w = sorted(wrong.get(r, {}).get(c, []))
            f = fired.get(r, {}).get(c, [])
            parts = [f"\\textbf{{{BSHORT(b)}}}" for b in l] + [f"\\bad{{{BSHORT(b)}}}" for b in w]
            mparts = [f"**{b}**" for b in l] + [f"WRONG {b}" for b in w]
            cells.append(", ".join(parts) if parts else ("$\\cdot$" if f else ""))
            mcells.append(", ".join(mparts) if mparts else ("· (fires, not needed)" if f else ""))
        row = tex(NAMES[r]).replace("\\textbackslash{}", "\\") + " & " + " & ".join(cells) + " \\\\"
        for i, fam in enumerate(FAMILIES):
            if r in fam:
                fam_lines[i].append(row)
        md.append(f"| {NAMES[r]} | " + " | ".join(mcells) + " |")
    for i, fl in fam_lines.items():
        fl += ["\\bottomrule", "\\end{tabular}"]
        open(os.path.join(fdir, f"evidence-matrix-{i + 1}.tex"), "w").write("\n".join(fl) + "\n")
    # examples: one lemma per rule, from the pair where it is needed (else where it fires)
    ex_rows = []
    exf = os.path.join(mdir, "examples.json")
    curated = json.load(open(exf)) if os.path.exists(exf) else {}
    for r in rules:
        if r in curated:
            try:
                text = pp(unlet(parse(curated[r]["lemma"])))
            except Exception:
                text = curated[r]["lemma"]
            if len(text) > 230:
                text = text[:227] + "..."
            ex_rows.append((r, curated[r]["pair"], text))
            continue
        src = None
        for pair, u in usage.items():
            b, c = pair.split("|")
            if b in lost.get(r, {}).get(c, []) and r in u["examples"]:
                src = (pair, u["examples"][r]); break
        if src is None:
            for pair, u in usage.items():
                if r in u["examples"]:
                    src = (pair, u["examples"][r]); break
        if src is None:
            continue
        try:
            text = pp(unlet(parse(src[1])))
        except Exception:
            text = src[1]
        if len(text) > 230:
            text = text[:227] + "..."
        ex_rows.append((r, src[0], text))
    for i in range(0, len(ex_rows), 9):
        chunk = ex_rows[i:i + 9]
        out = ["\\begin{tabular}{@{}p{2.2cm}p{2.0cm}p{9.6cm}@{}}", "\\toprule",
               "rule & benchmark, configuration & a lemma it sent \\\\", "\\midrule"]
        for r, pair, text in chunk:
            b, c = pair.split("|")
            out.append(f"{tex(NAMES[r])} & {BSHORT(b)}, {SHORT[c]} & {{\\ttfamily\\raggedright {tex(text)}}} \\\\")
        out += ["\\bottomrule", "\\end{tabular}"]
        open(os.path.join(fdir, f"evidence-examples-{i // 9 + 1}.tex"), "w").write("\n".join(out) + "\n")
    # report
    rep = ["# Evidence for the rules of the relations calculus", "",
           "Lost (bold): without the rule the pair is no longer solved; WRONG: wrong answer or",
           "failed model check without it; · : the rule fires but the pair is solved without it.", ""]
    rep += md + ["", "## Never fired on any solved pair", ""] + [f"- {NAMES[r]}" for r in unused]
    rep += ["", "## Examples", ""]
    for r, pair, text in ex_rows:
        rep.append(f"- **{NAMES[r]}** ({pair}): `{text}`")
    rep += ["", "## Summary per rule", ""]
    for r in rules:
        nl = sum(len(v) for v in lost.get(r, {}).values())
        nw = sum(len(v) for v in wrong.get(r, {}).values())
        nf = sum(len(v) for v in fired.get(r, {}).values())
        tot = sum(u["counts"].get(r, 0) for u in usage.values())
        rep.append(f"- {NAMES[r]}: fires on {nf} pairs ({tot} lemmas); needed on {nl}, wrong without it on {nw}")
    open(os.path.join(mdir, "REPORT.md"), "w").write("\n".join(rep) + "\n")
    print("\n".join(rep))


if __name__ == "__main__":
    main()
