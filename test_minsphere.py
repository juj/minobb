#!/usr/bin/env python3
"""
test_minsphere.py - checks that minsphere() returns the minimum enclosing sphere.

Builds test/test_minsphere.cpp into tmp/, and runs it in parallel on each
.glb/.gltf file under the GLB directory, and on each of its built-in
synthetic point sets (degenerate and numerically nasty inputs: points on a
line, in a plane, on one sphere, tiny, huge, far from the origin, not finite).
The tool computes the sphere twice, from the vertex positions and from their
convex hull, and verifies both (see the header of test/test_minsphere.cpp).

PASS if both spheres
  - contain every input point,
  - are the smallest spheres to the precision of floats: a lower bound for the
    radius of any sphere around the support points proves that no sphere can
    be smaller by more than the rounding of the center and of the radius to
    floats,
  - have support points that are input points on the sphere.

Usage:        python test_minsphere.py [glb_dir] [--filter TEXT] [--jobs N] [--timeout SECONDS]
Exit status:  0 = all passed, 1 = at least one failure
"""

import argparse
import concurrent.futures
import json
import os
import shutil
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.abspath(__file__))
TMP_DIR = os.path.join(ROOT, "tmp")
EXE = os.path.join(TMP_DIR, "test_minsphere.exe")

CXX = shutil.which("clang++") or "clang++"
SOURCES = ["minsphere.cpp", "convex_hull.cpp", "glb.cpp", os.path.join("test", "test_minsphere.cpp")]


def build():
    os.makedirs(TMP_DIR, exist_ok=True)
    cmd = [CXX, "-O3", "-std=c++17", "-I.", "-o", EXE] + SOURCES
    if subprocess.run(cmd, cwd=ROOT).returncode != 0:
        sys.exit("FAILED: could not build test_minsphere.exe")


def find_cases(glb_dir, text):
    """The test cases: the glTF files under glb_dir, then the synthetic point sets of the tool."""
    cases = []
    for dirpath, _dirnames, filenames in sorted(os.walk(glb_dir)):
        for name in sorted(filenames):
            if name.lower().endswith((".glb", ".gltf")):
                path = os.path.join(dirpath, name)
                cases.append({"name": os.path.relpath(path, glb_dir).replace(os.sep, "/"), "arg": path})
    for name in subprocess.run([EXE, "--list"], capture_output=True, text=True).stdout.split():
        cases.append({"name": name, "arg": name})
    return [c for c in cases if text in c["name"]]


def run_case(case, timeout):
    """Runs the tool on one case. Returns the case with the output of the tool added to it."""
    try:
        p = subprocess.run([EXE, case["arg"]], capture_output=True, timeout=timeout, cwd=ROOT)
        data = json.loads(p.stdout.decode("utf-8", "replace"))
    except subprocess.TimeoutExpired:
        data = {"error": f"timeout (> {timeout:.0f} s)"}
    except ValueError:
        data = {"error": f"crashed (exit code {p.returncode})"}
    return dict(case, ok=data.get("ok", False), error=data.get("error", ""), points=data.get("points", 0),
                hull_vertices=data.get("hull_vertices", 0), seconds=data.get("seconds", {}),
                sphere=data.get("sphere", {}), sphere_of_hull=data.get("sphere_of_hull", {}))


def main():
    ap = argparse.ArgumentParser(description=__doc__.strip().splitlines()[0])
    ap.add_argument("glb_dir", nargs="?", default=os.path.join(ROOT, "test", "glb"),
                    help="directory to search for .glb/.gltf files (default: test/glb)")
    ap.add_argument("--filter", default="", metavar="TEXT", help="only run the cases whose name contains TEXT")
    ap.add_argument("--jobs", type=int, default=os.cpu_count() or 4, help="parallel worker count (default: cpu count)")
    ap.add_argument("--timeout", type=float, default=600.0, help="per-case timeout in seconds (default: 600)")
    args = ap.parse_args()

    build()
    cases = find_cases(os.path.abspath(args.glb_dir), args.filter)
    if not cases:
        sys.exit(f"FAILED: no test cases found (glb directory: {args.glb_dir})")

    print(f"Checking {len(cases)} spheres ({args.jobs} workers):")
    t0 = time.time()
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        results = []
        for r in pool.map(lambda c: run_case(c, args.timeout), cases):
            results.append(r)
            s = r["seconds"]
            detail = (f"{r['points']} points, radius {r['sphere'].get('radius', 0):.6g} through {r['sphere'].get('support', 0)} of them, "
                      f"{r['sphere'].get('excess', 0) * 100:+.1e} % over the lower bound"
                      f"  ({s.get('sphere', 0) * 1000:.3f} ms; of the hull's {r['hull_vertices']} vertices"
                      f" {s.get('sphere_of_hull', 0) * 1000:.3f} ms)") if r["ok"] else r["error"]
            print(f"  {'PASS' if r['ok'] else 'FAIL'}  {r['name']}  {detail}", flush=True)

    failed = [r for r in results if not r["ok"]]
    passed = [r for r in results if r["ok"]]
    print(f"\n{len(results) - len(failed)}/{len(results)} spheres passed" + (f" ({len(failed)} FAILED)" if failed else ""))
    if passed:
        total = lambda key: sum(r["seconds"].get(key, 0) for r in passed)
        slowest = max(passed, key=lambda r: r["seconds"].get("sphere", 0))
        # How much larger the radius is than the lower bound, as a multiple of what the rounding to floats allows.
        used = max((r[k].get("excess", 0) / r[k]["allowed"] for r in passed for k in ("sphere", "sphere_of_hull")
                    if r[k].get("allowed", 0) > 0), default=0.0)
        print(f"largest radius over the lower bound among the passed: {used * 100:.0f} % of what the rounding of the"
              f" center and the radius to floats allows")
        print(f"minsphere() of the points took {total('sphere'):.3f} s in total, at most {slowest['seconds'].get('sphere', 0) * 1000:.1f} ms"
              f" ({slowest['points']} points); of the convex hulls {total('sphere_of_hull'):.3f} s in total"
              f" (the hulls themselves {total('hull'):.1f} s); wall time {time.time() - t0:.0f} s")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
