#!/usr/bin/env python3
"""Builds test/minobb_glb.exe and recomputes the sibling .json (convex hull,
minimum-volume OBB, AABBs, timing) for every .glb under test/glb, in parallel
via subprocesses.

Each <name>.glb produces:
  <name>.json     - the JSON document (hull, obb, aabb_vertices, aabb_hull, timing)
  <name>.json.err - the tool's stderr info lines

The hull/OBB are computed over ALL world-space points (no subsampling).

Usage (from the repo root):
  python calculate_obb.py [--timeout SECONDS] [--jobs N]

Files that exceed --timeout are killed and reported; the rest still complete.

The timings in the .json files (which build_index.py plots into glb.html) are
taken while the other workers run. For timings that are not slowed down by
them, use fewer workers than the machine has fast cores, e.g. --jobs 8.
"""

import argparse
import concurrent.futures
import json
import os
import subprocess
import sys

REPO_ROOT = os.path.dirname(os.path.abspath(__file__))
GLB_DIR = os.path.join(REPO_ROOT, "test", "glb")
EXE = os.path.join(REPO_ROOT, "test", "minobb_glb.exe")

BUILD_CMD = [
    "clang++", "-O3", "-std=c++17", "-I.",
    "-o", os.path.join("test", "minobb_glb.exe"),
    "minobb.cpp", "convex_hull.cpp", "glb.cpp", os.path.join("test", "minobb_glb.cpp"),
]


def build() -> None:
    print("building minobb_glb.exe ...")
    r = subprocess.run(BUILD_CMD, cwd=REPO_ROOT)
    if r.returncode != 0:
        sys.exit("error: build failed")
    print("build ok")


def find_glbs():
    glbs = []
    for dirpath, _dirnames, filenames in os.walk(GLB_DIR):
        for name in filenames:
            if name.lower().endswith(".glb"):
                glbs.append(os.path.join(dirpath, name))
    glbs.sort()
    return glbs


def compute_one(glb_path: str, timeout: float):
    """Runs minobb_glb.exe on one GLB. Returns (glb_path, status, total_sec)."""
    base = os.path.splitext(glb_path)[0]
    json_path = base + ".json"
    err_path = base + ".json.err"
    try:
        with open(json_path, "wb") as out, open(err_path, "wb") as err:
            proc = subprocess.run(
                [EXE, glb_path, "0"],
                stdout=out, stderr=err,
                timeout=timeout,
                cwd=REPO_ROOT,
            )
        if proc.returncode != 0:
            return (glb_path, f"error (exit {proc.returncode})", None)
        # Total generation time from the JSON's timing section.
        try:
            with open(json_path, encoding="utf-8") as f:
                data = json.load(f)
            t = data.get("timing", {})
            total = float(t.get("hull_sec", 0.0)) + float(t.get("obb_sec", 0.0))
        except (OSError, ValueError, TypeError) as e:
            return (glb_path, f"error (bad json: {e})", None)
        if data.get("obb", {}).get("degenerate") and data.get("hull", {}).get("vertices"):
            return (glb_path, "error (no obb)", total)
        return (glb_path, "ok", total)
    except subprocess.TimeoutExpired:
#        print(f'TIMEOUT, DELETING {glb_path}')
#        os.remove(glb_path)
        return (glb_path, f"timeout (> {timeout:.0f}s)", None)
    except OSError as e:
        return (glb_path, f"error ({e})", None)


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--timeout", type=float, default=3600.0,
                    help="per-file timeout in seconds (default: 3600; the largest hulls take several minutes)")
    ap.add_argument("--jobs", type=int, default=os.cpu_count() or 4,
                    help="parallel worker count (default: cpu count)")
    args = ap.parse_args()

    build()

    glbs = find_glbs()
    if not glbs:
        sys.exit(f"error: no .glb files found under {GLB_DIR}")
    print(f"computing hull+obb for {len(glbs)} files "
          f"({args.jobs} workers, timeout {args.timeout:.0f}s) ...\n")

    results = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futures = {pool.submit(compute_one, g, args.timeout): g for g in glbs}
        for fut in concurrent.futures.as_completed(futures):
            glb, status, total = fut.result()
            name = os.path.basename(glb)
            folder = os.path.basename(os.path.dirname(glb))
            time_s = f"{total:8.3f}s" if total is not None else "      -- "
            print(f"  {status:20s} {time_s}  {folder}/{name}")
            results.append((glb, status, total))

    ok = sum(1 for _, s, _ in results if s == "ok")
    print(f"\n{ok}/{len(results)} ok")
    bad = [(g, s) for g, s, _ in results if s != "ok"]
    if bad:
        print("problems:")
        for g, s in bad:
            print(f"  {s}: {os.path.relpath(g, REPO_ROOT)}")


if __name__ == "__main__":
    main()
