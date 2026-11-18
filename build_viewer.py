#!/usr/bin/env python3
"""Compiles the minimum OBB calculation code to WebAssembly with Emscripten,
and writes site/calculator.js, which site/view.html uses to compute the convex
hull, the bounding boxes and the minimum enclosing sphere of the models that
are dropped on the page.

The inputs are minobb.cpp, minsphere.cpp, convex_hull.cpp, web/calculator.cpp (the functions
that the page calls) and web/calculator_api.js (the JavaScript interface, see
its head comment). The output is a single file: the WebAssembly module is
embedded in calculator.js, so nothing else needs to be deployed with it.
site/view.html itself is not generated, it only loads calculator.js.

After the build, the calculator is run once under Node.js on the example of
the README, as a check that the build works (skipped if there is no `node`).

Requires `em++` of the Emscripten SDK on the path. Run from anywhere:
  python build_viewer.py
To try the result, serve the repo root (python -m http.server) and open
site/view.html."""

import argparse
import os
import shutil
import subprocess
import sys

REPO_ROOT = os.path.dirname(os.path.abspath(__file__))
OUT_FILE = os.path.join("site", "calculator.js")

SOURCES = ["minobb.cpp", "minsphere.cpp", "convex_hull.cpp", os.path.join("web", "calculator.cpp")]
API_JS = os.path.join("web", "calculator_api.js")

EMXX_FLAGS = [
    "-O3", "-std=c++17", "-I.",
    # convex_hull.cpp asks for strict floating point with a pragma that this
    # target does not know. It has nothing else: there is no fast-math here.
    "-Wno-ignored-pragmas",
    "-sSINGLE_FILE",                      # The .wasm goes inside the .js.
    "-sMODULARIZE", "-sEXPORT_NAME=createMinobbModule",
    "-sENVIRONMENT=web,worker,node",
    "-sFILESYSTEM=0",
    # The points of a model with millions of vertices take hundreds of megabytes.
    "-sALLOW_MEMORY_GROWTH", "-sMAXIMUM_MEMORY=4GB",
    "-sSTACK_SIZE=4MB",                   # The default of 64 KB is small next to the 1 MB of a native build.
    "-sEXPORTED_FUNCTIONS=_malloc,_free", # (The functions of calculator.cpp export themselves.)
    "-sEXPORTED_RUNTIME_METHODS=HEAPU8,HEAP32,HEAPF32,HEAPF64",
    "--extern-post-js", API_JS,
    "--output-eol", "linux",              # The same file comes out on every platform.
]

# Computes the box and the sphere of the six points of the README's example,
# and checks them against what a native build gives.
SMOKE_TEST_JS = r"""
const calculator = require(process.argv[1]);
const points = new Float32Array([0,0,0, 4,1,0, 1,3,0, 2,2,5, 5,4,1, 0,1,4]);
const check = (ok, what) => { if (!ok) { console.error('FAILED: ' + what); process.exit(1); } };
(async () => {
  for (const tolerance of [undefined, 0]) {
    const data = await calculator.compute(points, tolerance);
    const obb = data.obb;
    check(data.vertices == 6 && data.hull.vertices.length == 6 && data.hull.faces.length == 8, 'the hull');
    check(data.aabb_vertices.volume == 100 && data.aabb_hull.volume == 100, 'the axis-aligned box');
    check(Math.abs(obb.volume - 77.64707) < (tolerance === 0 ? 1e-4 : 77.64707 * 0.0015), 'the volume of the OBB');
    const sphere = data.sphere;
    check(Math.abs(sphere.radius - 3.4363444) < 1e-6 && sphere.support.length == 3, 'the minimum sphere');
    for (let i = 0; i < points.length; i += 3)
      check(Math.hypot(points[i] - sphere.center[0], points[i + 1] - sphere.center[1], points[i + 2] - sphere.center[2]) <= sphere.radius, 'the sphere contains the points');
    for (let i = 0; i < points.length; i += 3)
      for (let a = 0; a < 3; ++a) {
        let d = 0;
        for (let c = 0; c < 3; ++c) d += obb.axes[a][c] * (points[i + c] - obb.center[c]);
        check(Math.abs(d) <= obb.half_extents[a] + 1e-5, 'the OBB contains the points');
      }
  }
  console.log('test ok: the box of the README example has the volume 77.647, and its sphere the radius 3.4363');
})().catch(e => { console.error(e); process.exit(1); });
"""


def build(emxx: str) -> None:
    os.makedirs(os.path.join(REPO_ROOT, os.path.dirname(OUT_FILE)), exist_ok=True)
    cmd = [emxx] + EMXX_FLAGS + SOURCES + ["-o", OUT_FILE]
    print("building " + OUT_FILE.replace(os.sep, "/") + " ...", flush=True)
    print("  " + " ".join(["em++"] + cmd[1:]).replace(os.sep, "/"), flush=True)
    r = subprocess.run(cmd, cwd=REPO_ROOT)
    if r.returncode != 0:
        sys.exit("error: build failed")
    size = os.path.getsize(os.path.join(REPO_ROOT, OUT_FILE))
    print(f"build ok: {size:,} bytes", flush=True)


def smoke_test(node: str) -> None:
    r = subprocess.run([node, "-e", SMOKE_TEST_JS, os.path.join(REPO_ROOT, OUT_FILE)], cwd=REPO_ROOT)
    if r.returncode != 0:
        sys.exit("error: the built calculator does not work")


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0],
                                 epilog="Writes site/calculator.js. Requires em++ (Emscripten) on the path.")
    ap.add_argument("--no-test", action="store_true",
                    help="do not run the built calculator under Node.js after the build")
    args = ap.parse_args()

    emxx = shutil.which("em++")
    if not emxx:
        sys.exit("error: em++ not found on the path. Install the Emscripten SDK (https://emscripten.org) "
                 "and activate it.")
    build(emxx)

    if not args.no_test:
        node = shutil.which("node")
        if node:
            smoke_test(node)
        else:
            print("note: node not found on the path, the built calculator was not tested")


if __name__ == "__main__":
    main()
