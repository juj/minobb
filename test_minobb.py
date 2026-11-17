#!/usr/bin/env python3
"""
test_minobb.py - checks that minobb() returns the minimum volume OBB.

Builds test/test_minobb.cpp into tmp/, and runs it in parallel on
  - each .glb/.gltf file under the GLB directory,
  - the saved point sets test/case_seed*.txt,
  - a few hundred generated point sets: random clouds of different sizes and
    positions, boxes, prisms, lattices, thin plates, planar and collinear
    points, and ellipsoids.
The tool computes the box with minobb(), and the true minimum volume box with
an exhaustive search in double precision that is independent of minobb.cpp
(see the header of test/test_minobb.cpp).

PASS if the box of minobb()
  - has orthonormal axes and contains all the input points, and
  - is at most 0.01 % larger in volume than the ground truth box, after each
    extent of the latter has been granted an absolute error of 2e-6 times the
    size of the box: the axes of an OBB are single precision floats, which
    cannot orient a box more accurately than that. (This only matters for thin
    boxes. If the ground truth box is flat within that error, its volume says
    nothing, and the areas of the largest faces are compared instead.)

The ground truth of a hull of tens of thousands of vertices takes minutes to
compute, so for the GLB files it is cached next to the file as <name>.gt.json.
The cache is used until the file or the sources that the ground truth depends
on change. (For a hull of hundreds of thousands of vertices it takes an hour
of CPU time: the search for such a hull runs on as many threads as there are
workers.)

Usage:        python test_minobb.py [glb_dir] [--filter TEXT] [--jobs N] [--refresh]
Exit status:  0 = all passed, 1 = at least one failure
"""

import argparse
import concurrent.futures
import glob
import json
import math
import os
import random
import shutil
import struct
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.abspath(__file__))
TMP_DIR = os.path.join(ROOT, "tmp")
CASE_DIR = os.path.join(TMP_DIR, "minobb_cases")
EXE = os.path.join(TMP_DIR, "test_minobb.exe")

CXX = shutil.which("clang++") or "clang++"
SOURCES = ["minobb.cpp", "convex_hull.cpp", "glb.cpp", os.path.join("test", "test_minobb.cpp")]
GROUND_TRUTH_SOURCES = ["convex_hull.cpp", "glb.cpp", os.path.join("test", "test_minobb.cpp")]

TOLERANCE = 1e-4  # of the volume
SLACK = 2e-6      # of the size of the box, on each of its extents
TIMEOUT = 3600.0  # seconds per run of the tool
LARGE_HULL = 250000  # hull edges from which the ground truth is searched for on all the workers' threads


def build():
    os.makedirs(TMP_DIR, exist_ok=True)
    if subprocess.run([CXX, "-O3", "-std=c++17", "-I.", "-o", EXE] + SOURCES, cwd=ROOT).returncode != 0:
        sys.exit("FAILED: could not build test_minobb.exe")


def generate_cases():
    """Writes the generated point sets to tmp/minobb_cases/*.txt (the same ones on every run)."""
    shutil.rmtree(CASE_DIR, ignore_errors=True)
    os.makedirs(CASE_DIR)

    def save(name, points):
        with open(os.path.join(CASE_DIR, name + ".txt"), "w") as f:
            for p in points:  # Rounded to floats here, so that the text is exactly what the tool reads.
                f.write("%.9g %.9g %.9g\n" % struct.unpack("3f", struct.pack("3f", *p)))

    def rotation(r):
        a, b, c = (r.uniform(0, 2 * math.pi) for _ in range(3))
        ca, sa, cb, sb, cc, sc = math.cos(a), math.sin(a), math.cos(b), math.sin(b), math.cos(c), math.sin(c)
        m = [[cb * cc, sa * sb * cc - ca * sc, ca * sb * cc + sa * sc],
             [cb * sc, sa * sb * sc + ca * cc, ca * sb * sc - sa * cc], [-sb, sa * cb, ca * cb]]
        return lambda p: tuple(sum(m[i][j] * p[j] for j in range(3)) for i in range(3))

    for i in range(150):  # Random points in a ball: plain, tiny, huge, far from the origin, flattened.
        r = random.Random(1000 + i)
        points = []
        while len(points) < 20 + 380 * (i % 7) // 6:
            p = tuple(r.uniform(-8, 8) for _ in range(3))
            if sum(c * c for c in p) <= 64:
                points.append(p)
        kind = i % 5
        save("ball_%03d" % i, [p if kind == 0 else tuple(c * 1e-4 for c in p) if kind == 1 else
                               tuple(c * 3e5 for c in p) if kind == 2 else (p[0] + 4096, p[1] - 2048, p[2] + 1024)
                               if kind == 3 else (p[0], p[1] * 0.05, p[2] * 0.3) for p in points])
    for i in range(60):  # Only a few points: every contact configuration matters.
        r = random.Random(2000 + i)
        save("few_%03d" % i, [tuple(r.uniform(-1, 1) for _ in range(3)) for _ in range(4 + i % 6)])
    for i in range(40):  # Rotated boxes with points inside.
        r = random.Random(3000 + i)
        turn, e = rotation(r), [r.uniform(0.2, 5) for _ in range(3)]
        points = [turn((x * e[0], y * e[1], z * e[2])) for x in (-1, 1) for y in (-1, 1) for z in (-1, 1)]
        save("box_%03d" % i, points + [turn(tuple(r.uniform(-1, 1) * c for c in e)) for _ in range(50)])
    for i in range(40):  # Rotated prisms and cylinders.
        r = random.Random(4000 + i)
        turn, k, h, a = rotation(r), (3, 5, 6, 7, 12, 32, 64)[i % 7], r.uniform(0.05, 4), r.uniform(0.5, 2)
        save("prism_%03d" % i, [turn((a * math.cos(2 * math.pi * j / k), math.sin(2 * math.pi * j / k), s * h))
                                for j in range(k) for s in (-1, 1)])
    for i in range(20):  # Axis aligned lattices: coplanar and tied vertices everywhere.
        r = random.Random(5000 + i)
        d = [r.randint(1, 6) for _ in range(3)]
        points = [(x, y, z) for x in range(d[0] + 1) for y in range(d[1] + 1) for z in range(d[2] + 1)]
        save("lattice_%03d" % i, [p for p in points if i % 2 == 0 or r.random() < 0.6])
    for i in range(40):  # Rotated plates that are from 1e-1 down to 1e-7 thick: nearly, and numerically, flat.
        r = random.Random(6000 + i)
        turn, t = rotation(r), 10 ** -(1 + 6 * i / 39)
        save("plate_%03d" % i, [turn((r.uniform(-1, 1), r.uniform(-0.6, 0.6), r.uniform(-t, t))) for _ in range(8 + 3 * i)])
    for i in range(16):  # Points in a plane, or on a line: exactly (axis aligned), or up to rounding (rotated).
        r = random.Random(8000 + i)
        turn = rotation(r) if i % 2 else (lambda p: p)
        save("planar_%03d" % i, [turn((r.uniform(-3, 3), r.uniform(-1, 1) * (i % 4 < 2), 0.25)) for _ in range(3 + 5 * i)])
    save("point_000", [(1.5, -2.5, 3.5)] * 3)
    for i in range(20):  # Ellipsoids: all points are hull vertices, with many short edges.
        r = random.Random(7000 + i)
        e, points = [r.uniform(0.3, 3) for _ in range(3)], []
        for _ in range(50 + 13 * i):
            p = [r.gauss(0, 1) for _ in range(3)]
            length = math.sqrt(sum(c * c for c in p))
            points.append(tuple(p[k] / length * e[k] for k in range(3)))
        save("ellipsoid_%03d" % i, points)


def find_cases(glb_dir, text):
    cases = []
    for dirpath, _dirnames, filenames in sorted(os.walk(glb_dir)):
        for name in sorted(filenames):
            if name.lower().endswith((".glb", ".gltf")):
                path = os.path.join(dirpath, name)
                cases.append({"name": os.path.relpath(path, glb_dir).replace(os.sep, "/"), "path": path,
                              "cache": os.path.splitext(path)[0] + ".gt.json"})
    for path in sorted(glob.glob(os.path.join(ROOT, "test", "case_seed*.txt")) + glob.glob(os.path.join(CASE_DIR, "*.txt"))):
        cases.append({"name": "@" + os.path.splitext(os.path.basename(path))[0], "path": path, "cache": None})
    return [c for c in cases if text in c["name"]]


def judge(result):
    """Returns the reason why the box of minobb() fails, or None if it passes; how much larger the box is than
    the ground truth box, as a fraction (of the volume; of the area of a flat box; of the length of a box that
    is a line); and "thin", "flat" or "line" if the precision of floats mattered."""
    if result["orthonormality_error"] > 1e-5:
        return "the axes are not orthonormal (error %.1e)" % result["orthonormality_error"], 0.0, ""
    if result["outside"] > 1e-6 * result["diagonal"]:
        return "an input point is %.1e outside of the box" % result["outside"], 0.0, ""
    references = [result[k]["extents"] for k in ("gt", "sweep", "flat") if k in result]
    pad = SLACK * max(e[2] for e in references)
    volume = lambda e: (e[0] + pad) * (e[1] + pad) * (e[2] + pad)
    r = min(references, key=volume)
    m = result["minobb"]["extents"]
    failed = m[0] * m[1] * m[2] > (1 + TOLERANCE) * volume(r)
    if r[0] <= pad / 2:  # A flat reference box: its volume says nothing, compare the areas as well.
        failed = failed or m[1] * m[2] > (1 + TOLERANCE) * (r[1] + pad) * (r[2] + pad)
    if r[1] <= pad / 2:  # Not even an area: compare the lengths as well.
        failed = failed or m[2] > (1 + TOLERANCE) * (r[2] + pad)
        excess = m[2] / r[2] - 1 if r[2] > 0 else 0.0
        kind = "line"
    elif r[0] <= pad / 2:
        excess = m[1] * m[2] / (r[1] * r[2]) - 1
        kind = "flat"
    else:
        excess = m[0] * m[1] * m[2] / (r[0] * r[1] * r[2]) - 1
        kind = "thin" if excess > TOLERANCE else ""
    if failed:
        return "the box [%.6g %.6g %.6g] is not optimal: [%.6g %.6g %.6g] is" % (tuple(m) + tuple(r)), excess, kind
    return None, excess, kind


def run_tool(case, *args):
    """Runs the tool on one case. Returns its JSON output, or {"error": why there is none}."""
    try:
        p = subprocess.run([EXE, case["path"], *args], capture_output=True, text=True, timeout=TIMEOUT, cwd=ROOT)
        return json.loads(p.stdout)
    except subprocess.TimeoutExpired:
        return {"error": f"timeout (> {TIMEOUT:.0f} s)"}
    except ValueError:
        return {"error": f"crashed (exit code {p.returncode})"}


def run_case(case, stamp, refresh, jobs):
    """Computes the box of minobb() for one case, and its ground truth unless that is in the cache."""
    result = run_tool(case)
    if "error" in result:
        return dict(case, failure=result["error"], seconds={})
    hull = result["hull"]
    if not result["valid"]:
        return dict(case, failure="minobb() did not return a box", seconds={})
    cached = None
    if case["cache"] and not refresh and os.path.exists(case["cache"]):
        with open(case["cache"], encoding="utf-8") as f:
            cached = json.load(f)
        if cached.get("stamp") != [stamp, os.path.getmtime(case["path"])]:
            cached = None
    if cached:
        result.update(cached["boxes"])
    else:
        truth = run_tool(case, "--ground-truth", str(jobs if hull["edges"] >= LARGE_HULL else 1))
        if "error" in truth:
            return dict(case, failure="ground truth: " + truth["error"], seconds={})
        boxes = {k: truth[k] for k in ("gt", "sweep", "flat") if k in truth}
        result.update(boxes)
        result["seconds"].update({k: truth["seconds"][k] for k in ("ground_truth", "sweep")})
        if case["cache"]:
            with open(case["cache"], "w", encoding="utf-8") as f:
                json.dump({"stamp": [stamp, os.path.getmtime(case["path"])], "boxes": boxes}, f)
    failure, excess, kind = judge(result)
    return dict(case, failure=failure, excess=excess, kind=kind, seconds=result["seconds"], hull=hull,
                volume=result["minobb"]["volume"], computed=not cached)


def main():
    ap = argparse.ArgumentParser(description=__doc__.strip().splitlines()[0])
    ap.add_argument("glb_dir", nargs="?", default=os.path.join(ROOT, "test", "glb"),
                    help="directory to search for .glb/.gltf files (default: test/glb)")
    ap.add_argument("--filter", default="", metavar="TEXT", help="only run the cases whose name contains TEXT")
    ap.add_argument("--jobs", type=int, default=os.cpu_count() or 4, help="parallel worker count (default: cpu count)")
    ap.add_argument("--refresh", action="store_true", help="recompute the cached ground truths")
    args = ap.parse_args()

    build()
    generate_cases()
    cases = find_cases(os.path.abspath(args.glb_dir), args.filter)
    if not cases:
        sys.exit(f"FAILED: no test cases found (glb directory: {args.glb_dir})")
    stamp = max(os.path.getmtime(os.path.join(ROOT, s)) for s in GROUND_TRUTH_SOURCES)

    print(f"Checking {len(cases)} boxes against ground truth ({args.jobs} workers):")
    t0 = time.time()
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        results = []
        for r in pool.map(lambda c: run_case(c, stamp, args.refresh, args.jobs), cases):
            results.append(r)
            detail = r["failure"] or (
                f"{r['hull']['vertices']} hull vertices, volume {r['volume']:.6g}, "
                + {"": "{:+.1e} % vs. the optimum", "flat": "flat: area {:+.1e} % vs. the optimum",
                   "line": "a line: length {:+.1e} % vs. the optimum",
                   "thin": "thin: {:+.1e} % vs. the optimum is within the precision of floats"}[r["kind"]].format(r["excess"] * 100)
                + f"  ({r['seconds']['minobb'] * 1000:.1f} ms)")
            print(f"  {'FAIL' if r['failure'] else 'PASS'}  {r['name']}  {detail}", flush=True)

    failed = [r for r in results if r["failure"]]
    done = [r for r in results if r["seconds"]]
    print(f"\n{len(results) - len(failed)}/{len(results)} boxes passed" + (f" ({len(failed)} FAILED)" if failed else ""))
    if done:
        worst = lambda kind: max((r["excess"] for r in done if r["kind"] == kind and not r["failure"]), default=0.0) * 100
        count = lambda kind: sum(r["kind"] == kind for r in done)
        print(f"largest excess over the optimum among the passed: volume {worst(''):.1e} %;"
              f" area of the {count('flat')} flat boxes {worst('flat'):.1e} %;"
              f" length of the {count('line')} boxes that are lines {worst('line'):.1e} %;"
              f" {count('thin')} thin boxes are within the precision of floats (volume up to {worst('thin'):.1e} %)")
        print(f"minobb() took {sum(r['seconds']['minobb'] for r in done):.1f} s in total,"
              f" at most {max(r['seconds']['minobb'] for r in done):.1f} s")
        print(f"ground truth: {sum(r['computed'] for r in done)} computed"
              f" (in {sum(r['seconds']['ground_truth'] + r['seconds']['sweep'] for r in done):.0f} s),"
              f" {sum(not r['computed'] for r in done)} from the cache; wall time {time.time() - t0:.0f} s")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
