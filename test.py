#!/usr/bin/env python
"""
test.py - build and run all test cases for the minobb project.

Test sources live under test/ (see that directory). All temporary build
artifacts (object files, executables) are compiled under tmp/ and are
recreated from scratch on every run.

No external dependencies: only minobb.h/minobb.cpp from this repository,
a C++ compiler.

Usage:  python test.py
"""
import glob
import os
import re
import shutil
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.abspath(__file__))
TEST_DIR = os.path.join(ROOT, "test")
TMP_DIR = os.path.join(ROOT, "tmp")

CXX = shutil.which("g++") or "g++"
CXXFLAGS = ["-O2"]

results = []


def log(msg):
    print(msg, flush=True)


def run(cmd, cwd=None, timeout=600):
    t0 = time.time()
    p = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=timeout)
    dur = time.time() - t0
    out = (p.stdout or "") + ("" if p.returncode == 0 else "\n[stderr]\n" + (p.stderr or ""))
    return p.returncode, out.strip(), dur


def record(name, ok, detail, dur):
    results.append((name, ok, detail, dur))
    log(f"  {'PASS' if ok else 'FAIL'}  {name}  ({dur:.1f}s)  {detail}")


def build_exe(name, cpp_sources, extra_includes=()):
    """cpp_sources: list of absolute paths to .cpp files."""
    exe = os.path.join(TMP_DIR, name + ".exe")
    cmd = ([CXX] + CXXFLAGS + list(extra_includes)
           + list(cpp_sources) + ["-o", exe])
    rc, out, _ = run(cmd)
    if rc != 0:
        log(f"  build failed for {name}:\n{out}")
        return None
    return exe


# ---------------------------------------------------------------- tests

def t_testobb():
    """Self-check of minobb() against the paper's worked examples A)-D)."""
    exe = build_exe("testobb", [os.path.join(TEST_DIR, "testobb.cpp"),
                                os.path.join(ROOT, "minobb.cpp")], ["-I", ROOT])
    if not exe:
        record("testobb", False, "build failed", 0.0)
        return
    rc, out, dur = run([exe])
    ok = rc == 0 and "ALL TESTS PASSED" in out
    record("testobb", ok, "worked examples A-D of Jylanki 2015", dur)
    if not ok:
        log(out)


def t_repro_minimal():
    """Nearly-planar 5-point set: containment + volume vs double-precision optimum."""
    exe = build_exe("repro_minimal", [os.path.join(TEST_DIR, "repro_minimal.cpp")], ["-I", ROOT])
    if not exe:
        record("repro_minimal", False, "build failed", 0.0)
        return
    rc, out, dur = run([exe])
    ok = rc == 0 and "FAILS TO CONTAIN" not in out
    m = re.search(r"volume = ([\d.]+)", out)
    record("repro_minimal", ok, f"volume = {m.group(1) if m else '?'} (expect ~6.0890)", dur)
    if not ok:
        log(out)


def t_contcheck():
    """All saved case files: OBB must enclose every point."""
    exe = build_exe("contcheck", [os.path.join(TEST_DIR, "contcheck.cpp")], ["-I", ROOT])
    if not exe:
        record("contcheck", False, "build failed", 0.0)
        return
    cases = sorted(glob.glob(os.path.join(TEST_DIR, "case_seed*.txt")))
    if not cases:
        record("contcheck", False, "no case_seed*.txt files found", 0.0)
        return
    rc, out, dur = run([exe] + cases)
    worst = max((float(m.group(1)) for m in re.finditer(r"worstViolation=([-\d.eE+]+)", out)),
                default=1.0)
    ok = rc == 0 and len(re.findall(r"worstViolation", out)) == len(cases) and worst < 1e-4
    record("contcheck", ok, f"{len(cases)} case files, worst violation = {worst:.1e}", dur)
    if not ok:
        log(out)


def t_glb():
    """GLB pipeline: recompute hull/OBB for all GLBs, compare volumes to the
    reference .json files (see test_glb.py)."""
    script = os.path.join(TEST_DIR, "test_glb.py")
    if not os.path.exists(script):
        record("glb", False, "test_glb.py not found", 0.0)
        return
    rc, out, dur = run([sys.executable, script], timeout=3600)
    m = re.search(r"(\d+)/(\d+) GLBs passed", out)
    ok = rc == 0 and "FAILED" not in out
    record("glb", ok, m.group(0) if m else ("ok" if ok else "see output"), dur)
    if not ok:
        log(out)


# ---------------------------------------------------------------- main

def main():
    if not os.path.isdir(TEST_DIR):
        print(f"missing test directory: {TEST_DIR}")
        return 1

    # fresh tmp/ for all build artifacts
    if os.path.isdir(TMP_DIR):
        shutil.rmtree(TMP_DIR)
    os.makedirs(TMP_DIR)

    log("Running tests:")
    t_testobb()
    t_repro_minimal()
    t_contcheck()
    t_glb()

    nfail = sum(1 for _, ok, _, _ in results if not ok)
    log(f"\n{len(results) - nfail}/{len(results)} tests passed")
    return 0 if nfail == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
