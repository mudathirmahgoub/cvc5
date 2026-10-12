import re, sys
sys.path.insert(0, "tso2")
from pretty import parse, pp
src, goal, out = sys.argv[1], sys.argv[2], sys.argv[3]
keep = set(sys.argv[4].split("|"))
s = open(src).read()
start = s.index(";; ==== litmus templates")
end = s.index(";; ---- core count")
block = s[start:end]
kept = []
def sexp(t):
    return t if isinstance(t, str) else "(" + " ".join(sexp(x) for x in t) + ")"
for form in parse(re.sub(r";[^\n]*", "", block)):
    if not (isinstance(form, list) and form[0] == "assert"):
        continue
    body = form[1]
    parts = body[1:] if isinstance(body, list) and body[0] == "and" else [body]
    for p in parts:
        if pp(p) in keep:
            kept.append("(assert " + sexp(p) + ")")
r = s[:start] + ";; ==== templates used by the proof ====\n" + "\n".join(sorted(set(kept))) + "\n\n" + s[end:]
r = r.replace("(assert (not mcm))", "(assert " + goal + ")")
open(out, "w").write(r)
print(len(set(kept)), "templates kept")
