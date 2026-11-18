#!/usr/bin/env python3
"""
test_glb.py - regression test for the GLB hull/OBB/sphere pipeline.

For every .glb under test/glb that has a reference .json next to it, this
recomputes the convex hull, the minimum-volume OBB and the minimum enclosing
sphere with minobb_glb (freshly built into tmp/) over ALL world-space points
(no subsampling), and compares the convex hull volume, the OBB volume and the
radius of the sphere against the values stored in the reference .json. (A
reference .json from before the sphere was added has no sphere to compare.)

PASS if every value matches (relative tolerance 1e-6); FAIL otherwise.
The reference .json files are never modified (results go to tmp/glbtest/).

Usage:        python test/test_glb.py
Exit status:  0 = all passed, 1 = at least one failure
"""

import json
import os
import shutil
import subprocess
import sys
import tempfile

TEST_DIR = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(TEST_DIR)
GLB_DIR = os.path.join(TEST_DIR, "glb")
TMP_DIR = os.path.join(ROOT, "tmp")
GLBTEST_DIR = os.path.join(TMP_DIR, "glbtest")

CXX = shutil.which("clang++") or "clang++"
REL_TOL = 1e-6          # volumes round-trip through JSON with 9 significant digits
TIMEOUT = 3600.0        # per-GLB timeout in seconds (the largest hulls take several minutes)


def build_exe():
    """Builds tmp/minobb_glb.exe fresh. Returns the exe path, or None."""
    if os.path.isdir(TMP_DIR):
        shutil.rmtree(TMP_DIR)
    os.makedirs(TMP_DIR)
    exe = os.path.join(TMP_DIR, "minobb_glb.exe")
    cmd = [CXX, "-O2", "-std=c++17", "-I.",
           "-o", os.path.relpath(exe, ROOT),
           "minobb.cpp", "minsphere.cpp", "convex_hull.cpp", "glb.cpp", os.path.join("test", "minobb_glb.cpp")]
    p = subprocess.run(cmd, cwd=ROOT)
    if p.returncode != 0 or not os.path.exists(exe):
        return None
    return exe


def polyhedron_volume(vertices, faces):
    """Exact volume of a closed polyhedron (divergence theorem).

    Faces may be n-gons; each is fan-triangulated from its first vertex.
    """
    vol = 0.0
    for f in faces:
        a = vertices[f[0]]
        for i in range(1, len(f) - 1):
            b, c = vertices[f[i]], vertices[f[i + 1]]
            vol += (a[0] * (b[1] * c[2] - b[2] * c[1])
                    - a[1] * (b[0] * c[2] - b[2] * c[0])
                    + a[2] * (b[0] * c[1] - b[1] * c[0]))
    return abs(vol) / 6.0


def hull_volume(hull):
    if not hull or not hull.get("vertices") or not hull.get("faces"):
        return 0.0
    return polyhedron_volume(hull["vertices"], hull["faces"])


def obb_volume(obb):
    if not obb:
        return 0.0
    return float(obb.get("volume", 0.0))


def sphere_radius(sphere):
    """The radius of the sphere of the JSON, or None if the JSON has no sphere."""
    if sphere is None:
        return None
    return float(sphere.get("radius", 0.0))


def close(a, b):
    return abs(a - b) <= REL_TOL * max(1.0, abs(a), abs(b))


def find_glbs():
    glbs = []
    for dirpath, _dirnames, filenames in os.walk(GLB_DIR):
        for name in filenames:
            if name.lower().endswith(".glb"):
                glbs.append(os.path.join(dirpath, name))
    glbs.sort()
    return glbs


def main():
    exe = build_exe()
    if exe is None:
        print("FAILED: could not build minobb_glb.exe")
        return 1

    os.makedirs(GLBTEST_DIR, exist_ok=True)
    glbs = find_glbs()
    if not glbs:
        print(f"FAILED: no .glb files found under {GLB_DIR}")
        return 1

    n_pass = 0
    n_fail = 0
    n_skip = 0
    for glb in glbs:
        rel = os.path.relpath(glb, ROOT).replace(os.sep, "/")
        label = os.path.basename(os.path.dirname(glb)) + "/" + os.path.basename(glb)
        base = os.path.splitext(glb)[0]
        ref_path = base + ".json"
        if not os.path.exists(ref_path):
            print(f"  SKIP  {label}  (no reference .json)")
            n_skip += 1
            continue

        out_path = os.path.join(GLBTEST_DIR, os.path.basename(base) + ".json")
        try:
            with open(out_path, "wb") as out, open(os.devnull, "wb") as err:
                p = subprocess.run([exe, glb, "0"], stdout=out, stderr=err,
                                   timeout=TIMEOUT, cwd=ROOT)
            if p.returncode != 0:
                print(f"  FAIL  {label}  (minobb_glb exited {p.returncode})")
                n_fail += 1
                continue
            with open(out_path, encoding="utf-8") as f:
                new = json.load(f)
            with open(ref_path, encoding="utf-8") as f:
                ref = json.load(f)
        except subprocess.TimeoutExpired:
            print(f"  FAIL  {label}  (timeout > {TIMEOUT:.0f}s)")
            n_fail += 1
            continue
        except (OSError, ValueError) as e:
            print(f"  FAIL  {label}  (error: {e})")
            n_fail += 1
            continue

        rh, nh = hull_volume(ref.get("hull")), hull_volume(new.get("hull"))
        ro, no = obb_volume(ref.get("obb")), obb_volume(new.get("obb"))
        rs, ns = sphere_radius(ref.get("sphere")), sphere_radius(new.get("sphere"))
        ok = close(rh, nh) and close(ro, no) and ns is not None and (rs is None or close(rs, ns))
        if ok:
            n_pass += 1
            print(f"  PASS  {label}  hull {rh:.6g}  obb {ro:.6g}  sphere radius {ns:.6g}")
        else:
            n_fail += 1
            print(f"  FAIL  {label}")
            print(f"        hull volume: reference {rh:.9g} vs new {nh:.9g}")
            print(f"        obb volume:  reference {ro:.9g} vs new {no:.9g}")
            print(f"        sphere radius: reference {rs} vs new {ns}")

    total = n_pass + n_fail
    suffix = f" ({n_fail} FAILED)" if n_fail else ""
    print(f"\n{n_pass}/{total} GLBs passed{suffix}" + (f" ({n_skip} skipped)" if n_skip else ""))
    return 0 if n_fail == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
