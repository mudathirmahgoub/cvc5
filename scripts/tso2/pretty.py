import sys, re
def parse(s):
    toks = re.findall(r"\(|\)|[^\s()]+", s)
    def rec(i):
        if toks[i] == "(":
            out, i = [], i + 1
            while toks[i] != ")":
                x, i = rec(i); out.append(x)
            return out, i + 1
        return toks[i], i + 1
    res, i = [], 0
    while i < len(toks):
        x, i = rec(i); res.append(x)
    return res
DEFS = {}
def pp(t):
    if isinstance(t, str): return t
    h = t[0]
    if h == "rel.join": return pp(t[1]) + ";" + pp(t[2])
    if h == "rel.tclosure":
        a = pp(t[1]); return (a if re.fullmatch(r"[\w-]+", a) else "(" + a + ")") + "+"
    if h == "rel.iden": return "[" + pp(t[1]) + "]"
    if h == "rel.transpose": return "(" + pp(t[1]) + ")^-1"
    if h == "set.union": return "(" + pp(t[1]) + " ∪ " + pp(t[2]) + ")"
    if h == "set.inter": return "(" + pp(t[1]) + " ∩ " + pp(t[2]) + ")"
    if h == "set.minus": return "(" + pp(t[1]) + " \\ " + pp(t[2]) + ")"
    if h == "irreflexive": return "irr(" + pp(t[1]) + ")"
    if h == "rel.cyclic": return "cyc(" + pp(t[1]) + ")"
    if h == "not": return "¬" + pp(t[1])
    if h == "and": return "  ∧  ".join(pp(x) for x in t[1:])
    if h == "=": return pp(t[1]) + " = " + pp(t[2])
    return "(" + " ".join(pp(x) for x in t) + ")"
def main():
    src = open(sys.argv[1]).read()
    src = re.sub(r";[^\n]*", "", src)
    for form in parse(src):
        if isinstance(form, list) and form and form[0] == "define-fun" and form[1] in ("ppo","ghb","implied","poWR","po-loc","rfe","coi","coe","fri","fre","A","mcm"):
            print("DEF", form[1], "=", pp(form[4]))
    started = False
    for form in parse(src):
        if isinstance(form, list) and form and form[0] == "assert":
            s = pp(form[1])
            if "irr(" in s or "cyc(po" in s or s.startswith("¬mcm") or "mcm" in s:
                for part in s.split("  ∧  "):
                    print("T", part)

if __name__ == "__main__":
    main()
