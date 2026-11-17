#!/usr/bin/env python3
"""
test_convex_hull.py - tests convex_hull() on every glTF model under glb/.

Builds test/test_convex_hull.cpp into tmp/, and runs it in parallel on each
.glb/.gltf file under the GLB directory, and on each of its built-in
synthetic point sets (degenerate and numerically nasty inputs). The tool
computes the convex hull of the vertex positions, and verifies it with exact
arithmetic (see the header of test/test_convex_hull.cpp).

PASS if the hull was verified to be correct; FAIL otherwise (wrong hull,
crash, timeout, unreadable file).

The results go to convex_hull_report/: index.html is a report with a 3D
viewer for clicking through the test cases, data/<case>.js are the hulls.
The report can be opened straight from disk. To also overlay the original
models in it, serve it over http: run "python -m http.server" in this
directory and open http://localhost:8000/convex_hull_report/

No dependencies besides a C++ compiler (clang++).

Usage:        python test_convex_hull.py [glb_dir] [--filter TEXT] [--jobs N] [--timeout SECONDS]
Exit status:  0 = all passed, 1 = at least one failure
"""

import argparse
import concurrent.futures
import json
import os
import re
import shutil
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.abspath(__file__))
TMP_DIR = os.path.join(ROOT, "tmp")
REPORT_DIR = os.path.join(ROOT, "convex_hull_report")
DATA_DIR = os.path.join(REPORT_DIR, "data")
EXE = os.path.join(TMP_DIR, "test_convex_hull.exe")

CXX = shutil.which("clang++") or "clang++"
SOURCES = ["convex_hull.cpp", "glb.cpp", os.path.join("test", "test_convex_hull.cpp")]


def build():
    os.makedirs(TMP_DIR, exist_ok=True)
    cmd = [CXX, "-O3", "-std=c++17", "-I.", "-o", EXE] + SOURCES
    if subprocess.run(cmd, cwd=ROOT).returncode != 0:
        sys.exit("FAILED: could not build test_convex_hull.exe")


def find_cases(glb_dir, text):
    """The test cases: the glTF files under glb_dir, then the synthetic point sets of the tool."""
    cases = []
    for dirpath, _dirnames, filenames in sorted(os.walk(glb_dir)):
        for name in sorted(filenames):
            if name.lower().endswith((".glb", ".gltf")):
                path = os.path.join(dirpath, name)
                rel = os.path.relpath(path, glb_dir).replace(os.sep, "/")
                cases.append({"id": re.sub(r"\W", "_", rel), "name": rel, "arg": path,
                              "glb": os.path.relpath(path, REPORT_DIR).replace(os.sep, "/")})
    for name in subprocess.run([EXE, "--list"], capture_output=True, text=True).stdout.split():
        cases.append({"id": "synthetic_" + name[1:], "name": name, "arg": name, "glb": None})
    return [c for c in cases if text in c["name"]]


def run_case(case, timeout):
    """Runs the tool on one case and saves its output for the report. Returns the case with the result
    summary (everything but the bulky arrays) added to it."""
    out = ""
    try:
        p = subprocess.run([EXE, case["arg"]], capture_output=True, timeout=timeout, cwd=ROOT)
        out = p.stdout.decode("utf-8", "replace")
        data = json.loads(out)
    except subprocess.TimeoutExpired:
        data = {"error": f"timeout (> {timeout:.0f} s)"}
    except ValueError:
        data = {"error": f"crashed (exit code {p.returncode})"}
    if "ok" not in data:
        out = json.dumps(data)
    with open(os.path.join(DATA_DIR, case["id"] + ".js"), "w", encoding="utf-8") as f:
        f.write(f"caseData({json.dumps(case['id'])}, {out});\n")

    faces, vertices, degenerate = data.get("faces", []), len(data.get("vertices", [])) // 3, data.get("degenerate", False)
    edges = sum(map(len, faces)) // 2 if not degenerate else len(faces[0]) if faces else vertices - 1
    return dict(case, ok=data.get("ok", False), error=data.get("error", ""), points=data.get("points", 0),
                vertices=vertices, faces=len(faces), edges=max(edges, 0),
                largest=max(map(len, faces), default=0), degenerate=degenerate,
                volume=data.get("volume", 0), area=data.get("area", 0), seconds=data.get("seconds", {}))


def main():
    ap = argparse.ArgumentParser(description=__doc__.strip().splitlines()[0])
    ap.add_argument("glb_dir", nargs="?", default=os.path.join(ROOT, "glb"),
                    help="directory to search for .glb/.gltf files (default: glb/)")
    ap.add_argument("--filter", default="", metavar="TEXT", help="only run the cases whose name contains TEXT")
    ap.add_argument("--jobs", type=int, default=os.cpu_count() or 4, help="parallel worker count (default: cpu count)")
    ap.add_argument("--timeout", type=float, default=300.0, help="per-case timeout in seconds (default: 300)")
    args = ap.parse_args()

    build()
    cases = find_cases(os.path.abspath(args.glb_dir), args.filter)
    if not cases:
        sys.exit(f"FAILED: no test cases found (glb directory: {args.glb_dir})")
    shutil.rmtree(DATA_DIR, ignore_errors=True)
    os.makedirs(DATA_DIR)

    print(f"Computing {len(cases)} convex hulls ({args.jobs} workers):")
    t0 = time.time()
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        results = []
        for r in pool.map(lambda c: run_case(c, args.timeout), cases):
            results.append(r)
            detail = (f"{r['points']} points -> {r['vertices']} vertices, {r['faces']} faces"
                      f"  ({r['seconds'].get('hull', 0) * 1000:.1f} ms)") if r["ok"] else r["error"]
            print(f"  {'PASS' if r['ok'] else 'FAIL'}  {r['name']}  {detail}", flush=True)

    summary = json.dumps([{k: v for k, v in r.items() if k != "arg"} for r in results]).replace("</", "<\\/")
    with open(os.path.join(REPORT_DIR, "index.html"), "w", encoding="utf-8") as f:
        f.write(REPORT_HTML.replace("/*CASES*/[]", summary).replace("<!--DATE-->", time.strftime("%Y-%m-%d %H:%M")))

    failed = [r for r in results if not r["ok"]]
    hull_time = sum(r["seconds"].get("hull", 0) for r in results)
    print(f"\n{len(results) - len(failed)}/{len(results)} hulls passed" + (f" ({len(failed)} FAILED)" if failed else "")
          + f"  (convex_hull() {hull_time:.2f} s in total, wall time {time.time() - t0:.1f} s)")
    print(f"report: {os.path.join(REPORT_DIR, 'index.html')}")
    return 1 if failed else 0


REPORT_HTML = r"""<!DOCTYPE html>
<html>
<head>
<meta charset="utf-8">
<title>convex_hull() test report</title>
<style>
  html { color-scheme: dark; }
  html, body { margin: 0; height: 100%; overflow: hidden; background: #202020; color: #ddd; font: 13px/1.5 monospace; }
  #side { position: absolute; left: 0; top: 0; bottom: 0; width: 400px; display: flex; flex-direction: column; background: #181818; }
  #head { padding: 8px 10px; border-bottom: 1px solid #444; }
  #head h1 { font-size: 15px; margin: 0 0 4px; }
  #head input, #head select { font: inherit; margin-top: 4px; }
  #list { flex: 1; overflow-y: scroll; }
  .case { padding: 3px 10px; cursor: pointer; border-bottom: 1px solid #262626; }
  .case div { white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }
  .case:hover { background: #2a2a2a; }
  .case.selected { background: #2f4f6f; }
  .pass { color: #6c6; }
  .fail { color: #f66; }
  .dim { color: #888; }
  #view { position: absolute; left: 400px; right: 0; top: 0; bottom: 0; }
  #view canvas { display: block; }
  .panel { position: absolute; top: 8px; background: rgba(0, 0, 0, 0.6); padding: 6px 10px; border-radius: 4px; }
  #hud { left: 8px; white-space: pre; pointer-events: none; }
  #options { right: 8px; user-select: none; }
  #options label { display: block; cursor: pointer; }
  #options input { vertical-align: middle; }
</style>
<script type="importmap">
{
  "imports": {
    "three": "https://cdn.jsdelivr.net/npm/three@0.160.0/build/three.module.js",
    "three/addons/": "https://cdn.jsdelivr.net/npm/three@0.160.0/examples/jsm/"
  }
}
</script>
</head>
<body>
<div id="side">
  <div id="head">
    <h1>convex_hull() test report</h1>
    <div id="summary"></div>
    <div class="dim"><!--DATE--> &middot; keys: &uarr; &darr; to step through the cases</div>
    <input type="text" id="filter" placeholder="filter by name" size="18">
    <select id="sort">
      <option value="">sort: failures first</option>
      <option value="name">sort: name</option>
      <option value="points">sort: input points</option>
      <option value="vertices">sort: hull vertices</option>
      <option value="largest">sort: largest face</option>
      <option value="hull">sort: hull time</option>
    </select>
  </div>
  <div id="list"></div>
</div>
<div id="view">
  <canvas id="canvas"></canvas>
  <div id="hud" class="panel"></div>
  <div id="options" class="panel">
    <label><input type="checkbox" id="show-faces" checked> hull faces</label>
    <label><input type="checkbox" id="show-edges" checked> hull edges</label>
    <label><input type="checkbox" id="show-vertices"> hull vertices</label>
    <label><input type="checkbox" id="show-points" checked> input points</label>
    <label><input type="checkbox" id="show-model"> GLB model</label>
  </div>
</div>
<script type="module">
import * as THREE from 'three';
import { OrbitControls } from 'three/addons/controls/OrbitControls.js';
import { GLTFLoader } from 'three/addons/loaders/GLTFLoader.js';

const CASES = /*CASES*/[];
const $ = id => document.getElementById(id);
const num = x => x.toLocaleString('en-US');
const count = (n, one, many) => num(n) + ' ' + (n == 1 ? one : many || one + 's');
const ms = x => ((x || 0) * 1000).toFixed(x < 0.01 ? 2 : 0) + ' ms';
const esc = s => s.replace(/[&<>"]/g, c => '&#' + c.charCodeAt(0) + ';');

// ---- 3D view ----

const view = $('view');
const renderer = new THREE.WebGLRenderer({ canvas: $('canvas'), antialias: true });
renderer.setPixelRatio(devicePixelRatio);
const scene = new THREE.Scene();
scene.background = new THREE.Color(0x202020);
scene.add(new THREE.AmbientLight(0xffffff, 0.8));
const sun = new THREE.DirectionalLight(0xffffff, 1.5);
sun.position.set(1, 2, 1.5);
scene.add(sun);
const camera = new THREE.PerspectiveCamera(50, 1, 0.01, 100);
camera.position.set(1.2, 0.9, 1.4);
const controls = new OrbitControls(camera, renderer.domElement);
function resize() {
  renderer.setSize(view.clientWidth, view.clientHeight);
  camera.aspect = view.clientWidth / view.clientHeight;
  camera.updateProjectionMatrix();
}
addEventListener('resize', resize);
resize();
renderer.setAnimationLoop(() => { controls.update(); renderer.render(scene, camera); });

// The layers of the current case, by the name of their checkbox.
const layers = {};
const LAYERS = ['faces', 'edges', 'vertices', 'points', 'model'];

function setLayer(name, object) {
  if (layers[name]) {
    scene.remove(layers[name]);
    layers[name].traverse(o => { o.geometry?.dispose(); o.material?.dispose?.(); });
  }
  layers[name] = object;
  if (object) {
    object.visible = $('show-' + name).checked;
    scene.add(object);
  }
}

function geometry(positions) {
  const g = new THREE.BufferGeometry();
  g.setAttribute('position', new THREE.Float32BufferAttribute(positions, 3));
  return g;
}

// Shows the output of test_convex_hull for case c. Everything is drawn relative to the center of the
// bounding box, in units of its size: models may be tiny, huge, or far away from the origin.
let center = [0, 0, 0], scale = 1;
function show(c, data) {
  const V = data.vertices || [], faces = data.faces || [], sample = data.sample || [];
  const bounds = [0, 1, 2].map(k => {
    let lo = Infinity, hi = -Infinity;
    for (const a of [V, sample]) for (let i = k; i < a.length; i += 3) { lo = Math.min(lo, a[i]); hi = Math.max(hi, a[i]); }
    return lo <= hi ? [lo, hi] : [0, 0];
  });
  center = bounds.map(b => (b[0] + b[1]) / 2);
  scale = 2 / (Math.hypot(...bounds.map(b => b[1] - b[0])) || 1);
  const local = a => Array.from(a, (x, i) => (x - center[i % 3]) * scale);
  const P = local(V), at = i => P.slice(3 * i, 3 * i + 3);

  const triangles = [], lines = [];
  for (const f of faces) {
    for (let i = 1; i + 1 < f.length; ++i) triangles.push(...at(f[0]), ...at(f[i]), ...at(f[i + 1]));
    f.forEach((a, i) => { const b = f[(i + 1) % f.length]; if (a < b || data.degenerate) lines.push(...at(a), ...at(b)); });
  }
  if (!faces.length && V.length == 6) lines.push(...P);
  const mesh = new THREE.Mesh(geometry(triangles), new THREE.MeshLambertMaterial({
    color: 0x33ccff, transparent: true, opacity: 0.3, depthWrite: false, side: THREE.DoubleSide }));
  mesh.geometry.computeVertexNormals();
  setLayer('faces', mesh);
  setLayer('edges', new THREE.LineSegments(geometry(lines), new THREE.LineBasicMaterial({ color: 0x33ccff })));
  setLayer('vertices', new THREE.Points(geometry(P), new THREE.PointsMaterial({ color: 0xffffff, size: 5, sizeAttenuation: false })));
  setLayer('points', new THREE.Points(geometry(local(sample)), new THREE.PointsMaterial({ color: 0xffaa33, size: 2, sizeAttenuation: false })));
  setLayer('model', null);
  $('show-vertices').parentNode.style.display = V.length ? '' : 'none';
  $('show-model').parentNode.style.display = c.glb ? '' : 'none';
  if (c.glb && $('show-model').checked) loadModel(c);

  // Keep the viewing direction, reset the distance.
  camera.position.sub(controls.target).setLength(2.4);
  controls.target.set(0, 0, 0);

  const s = c.seconds || {};
  const subset = sample.length / 3 < data.finite_points ? `  (${num(sample.length / 3)} shown)` : '';
  $('hud').innerHTML = `<b>${esc(c.name)}</b>\n` +
    (c.ok ? '<span class="pass">PASS</span>  the hull was verified to be exact' : `<span class="fail">FAIL  ${esc(c.error)}</span>`) + '\n\n' +
    `input   ${count(c.points, 'point')}${subset}\n` +
    `hull    ${count(c.vertices, 'vertex', 'vertices')}, ${count(c.edges, 'edge')}, ${count(c.faces, 'face')}` +
    (c.degenerate ? '  (degenerate: ' + (c.faces ? 'planar' : c.vertices > 1 ? 'collinear' : 'a point') + ')' : '') + '\n' +
    (c.largest > 3 ? `        largest face has ${num(c.largest)} corners\n` : '') +
    `volume  ${c.volume.toPrecision(6)}   area  ${c.area.toPrecision(6)}\n` +
    `time    hull ${ms(s.hull)}, load ${ms(s.load)}, verify ${ms(s.verify)}`;
}

// The original model can only be fetched over http(s), not from a file:// page.
function loadModel(c) {
  const hud = $('hud').innerHTML;
  new GLTFLoader().load(c.glb, gltf => {
    if (c !== current || layers.model) return;
    const model = new THREE.Group();
    model.add(gltf.scene);
    model.scale.setScalar(scale);
    model.position.set(...center.map(x => -x * scale));
    setLayer('model', model);
  }, undefined, () => {
    if (c === current) $('hud').innerHTML = hud + '\n\n<span class="fail">Cannot load the GLB model: serve the report over http\n(python -m http.server in the repository root).</span>';
  });
}

// The checkboxes are remembered across visits.
let shown = {};
try { shown = JSON.parse(localStorage.getItem('convex_hull_report')) || {}; } catch (e) {}
for (const name of LAYERS) {
  const box = $('show-' + name);
  if (name in shown) box.checked = shown[name];
  box.addEventListener('change', () => {
    shown[name] = box.checked;
    try { localStorage.setItem('convex_hull_report', JSON.stringify(shown)); } catch (e) {}
    if (layers[name]) layers[name].visible = box.checked;
    else if (name == 'model' && box.checked && current && current.glb) loadModel(current);
  });
}

// ---- Case list ----

// The data of a case is in a script file that calls caseData(): unlike fetch(), that works from file:// too.
let current = null;
window.caseData = (id, data) => { if (current && current.id == id) show(current, data); };

function select(c) {
  if (!c || c === current) return;
  current = c;
  history.replaceState(null, '', '#' + c.id);
  for (const e of $('list').children) e.classList.toggle('selected', e.dataset.id == c.id);
  $('list').querySelector('.selected')?.scrollIntoView({ block: 'nearest' });
  $('hud').textContent = 'loading ' + c.name + ' ...';
  const script = document.createElement('script');
  script.src = 'data/' + c.id + '.js';
  script.onload = () => script.remove();
  script.onerror = () => { $('hud').textContent = 'cannot load ' + script.src; };
  document.head.appendChild(script);
}

let listed = [];
function list() {
  const text = $('filter').value.toLowerCase(), key = $('sort').value;
  const value = c => key == 'hull' ? c.seconds.hull || 0 : c[key];
  listed = CASES.filter(c => c.name.toLowerCase().includes(text));
  if (key == 'name') listed.sort((a, b) => a.name.localeCompare(b.name));
  else if (key) listed.sort((a, b) => value(b) - value(a));
  else listed.sort((a, b) => a.ok - b.ok);
  $('list').innerHTML = listed.map(c =>
    `<div class="case${c === current ? ' selected' : ''}" data-id="${c.id}" title="${esc(c.name)}">` +
    `<div><span class="${c.ok ? 'pass' : 'fail'}">${c.ok ? 'PASS' : 'FAIL'}</span> ${esc(c.name.replace(/^.*\//, ''))}</div>` +
    `<div class="dim">${c.ok ? '' : esc(c.error) + ' &middot; '}${count(c.points, 'point')} &rarr; ` +
    `${count(c.vertices, 'vertex', 'vertices')}, ${count(c.faces, 'face')} &middot; ${ms(c.seconds.hull)}</div></div>`).join('');
}

$('list').addEventListener('click', e => select(CASES.find(c => c.id == e.target.closest('.case')?.dataset.id)));
$('filter').addEventListener('input', list);
$('sort').addEventListener('change', list);
addEventListener('keydown', e => {
  const step = { ArrowDown: 1, ArrowUp: -1 }[e.key];
  if (!step || e.target.tagName == 'SELECT') return;
  e.preventDefault();
  select(listed[Math.max(0, Math.min(listed.length - 1, listed.indexOf(current) + step))]);
});

const failed = CASES.filter(c => !c.ok).length;
$('summary').innerHTML = `<span class="${failed ? 'fail' : 'pass'}">${CASES.length - failed}/${CASES.length} hulls passed` +
  (failed ? `, ${failed} FAILED` : '') + `</span> <span class="dim">(${CASES.filter(c => c.glb).length} GLB files, ` +
  `${CASES.filter(c => !c.glb).length} synthetic)</span>`;
list();
select(CASES.find(c => c.id == location.hash.slice(1)) || listed[0]);
</script>
</body>
</html>
"""


if __name__ == "__main__":
    sys.exit(main())
