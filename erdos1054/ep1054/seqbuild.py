"""Build the vendored `Principia` library ONE MODULE AT A TIME, in dependency order.

Lake 5.0.0 has no `-j`, and `LEAN_NUM_THREADS` does not bound how many `lean` processes it runs
at once, so a plain `lake build` compiles ~4 heavy modules concurrently. The `MNum*` kernel
certificates then exceed the 16 GB CI runner (oom-kill at 14.8 G + 10.8 G swap, runs 37174571376
and 37177504797). Building each module with its own `lake build <Module>` call, dependencies
first, keeps exactly one `lean` compiling at a time. A later plain `lake build` only replays.

usage: python3 seqbuild.py            (run from erdos1054/ep1054)
"""
import os
import re
import subprocess
import sys

IMP = re.compile(r"^import\s+(Principia\.[\w.]+)\s*$")


def module_of(path):
    return path[:-len(".lean")].replace(os.sep, ".").replace("/", ".")


mods = {}
for root, _, files in os.walk("Principia"):
    for f in files:
        if f.endswith(".lean"):
            p = os.path.join(root, f)
            deps = []
            with open(p, encoding="utf-8") as h:
                for line in h:
                    m = IMP.match(line.strip())
                    if m:
                        deps.append(m.group(1))
            mods[module_of(p)] = deps

order, state = [], {}


def visit(m):
    if state.get(m) == 2:
        return
    if state.get(m) == 1:
        sys.exit("import cycle at " + m)
    state[m] = 1
    for d in mods.get(m, []):
        if d in mods:
            visit(d)
    state[m] = 2
    order.append(m)


sys.setrecursionlimit(10000)
for m in sorted(mods):
    visit(m)

print(f"seqbuild: {len(order)} modules", flush=True)
for i, m in enumerate(order, 1):
    r = subprocess.run(["lake", "build", m], capture_output=True, text=True)
    if r.returncode != 0:
        print(r.stdout[-4000:], r.stderr[-4000:])
        sys.exit(f"seqbuild: FAILED at {i}/{len(order)} {m}")
    if i % 25 == 0 or i == len(order):
        print(f"seqbuild: {i}/{len(order)} {m}", flush=True)
print("seqbuild: done", flush=True)
