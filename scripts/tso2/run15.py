import subprocess, sys, time, glob, os
from concurrent.futures import ThreadPoolExecutor
cvc5, limit, jobs = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
opts = sys.argv[4].split()
files = sorted(glob.glob("rsb-main/benchmarks-ltts/*.smt2"))
def run(f):
    t = time.time()
    p = subprocess.run([cvc5, *opts, f"--tlimit={limit*1000}", f], capture_output=True, text=True)
    out = (p.stdout + p.stderr).strip().splitlines()
    a = out[0] if out else "?"
    return os.path.basename(f)[:-5], "timeout" if "timeout" in a else a, time.time() - t
with ThreadPoolExecutor(jobs) as ex:
    for name, a, e in ex.map(run, files):
        print(f"{name:22s} {a:8s} {e:7.1f}s", flush=True)
