#!/usr/bin/env python3
"""Scans test/glb for .glb files and writes glb.html: two scatter plots of the
computation times (convex hull against the number of input vertices, OBB
against the number of hull vertices), and below them a table of the files with
links to view.html?url=<relative path>. A point of a plot opens the same link.

The numbers come from the sibling <name>.json of each .glb, which
calculate_obb.py writes. Run from the repo root: python build_index.py"""

import html
import json
import os
import re
import urllib.parse

GLB_DIR = "test/glb"
OUT_FILE = "glb.html"


def load_entry(p: str):
    """What the sibling .json of a .glb says about it, or None if the .json is
    missing or has no timing info: the number of input points and of hull
    vertices, the hull and OBB times in seconds (no OBB time if minobb() gave
    up on the hull as too large), and whether the hull is flat."""
    path = os.path.splitext(p)[0] + ".json"
    if not os.path.exists(path):
        return None
    try:
        with open(path, encoding="utf-8") as f:
            data = json.load(f)
        hull, timing = data["hull"], data["timing"]
        no_box = bool(data["obb"]["degenerate"]) and len(hull["vertices"]) > 0
        return {
            "points": int(data["vertices"]),
            "hull": len(hull["vertices"]),
            "flat": bool(hull["degenerate"]),
            "hull_sec": float(timing["hull_sec"]),
            "obb_sec": None if no_box else float(timing["obb_sec"]),
        }
    except (OSError, ValueError, TypeError, KeyError):
        return None


def format_time(seconds: float) -> str:
    for scale, unit in ((1.0, "s"), (1e-3, "ms"), (1e-6, "µs")):
        if seconds >= scale:
            return f"{seconds / scale:.3g} {unit}" if seconds < 1000 else f"{seconds:.0f} s"
    return f"{seconds * 1e9:.3g} ns"


def main() -> None:
    files = []
    for dirpath, _dirnames, filenames in os.walk(GLB_DIR):
        for name in filenames:
            if name.lower().endswith(".glb"):
                p = os.path.join(dirpath, name)
                files.append((p, load_entry(p)))

    # Sort by total generation time, slowest first; entries without timing
    # info (no .json) go last, alphabetically.
    def sort_key(item):
        p, e = item
        if e is None:
            return (1, 0.0, p)
        return (0, -(e["hull_sec"] + (e["obb_sec"] or 0.0)), p)

    files.sort(key=sort_key)

    data = []       # One row per file that has numbers, for the plots.
    table = []      # The same numbers as text: every file, in the same order.
    no_box = []     # The files that are left out of the OBB plot.
    for p, e in files:
        url = p.replace(os.sep, "/")
        href = "view.html?url=" + urllib.parse.quote(url, safe="/")
        name = os.path.basename(p)
        link = f'<td><a href="{html.escape(href, quote=True)}">{html.escape(name)}</a></td>' \
               f'<td class="dim">{html.escape(os.path.basename(os.path.dirname(p)))}</td>'
        if e is None:
            table.append(f'    <tr>{link}<td class="dim" colspan="4">not computed</td></tr>')
            continue
        if e["obb_sec"] is None:
            no_box.append(f'<a href="{html.escape(href, quote=True)}">{html.escape(name)}</a>'
                          f' ({e["hull"]:,} hull vertices)')
        flat = ' <span class="dim">flat</span>' if e["flat"] else ""
        obb = '<td class="dim">none: too large</td>' if e["obb_sec"] is None \
            else f'<td>{format_time(e["obb_sec"])}</td>'
        table.append(f'    <tr data-i="{len(data)}">{link}<td>{e["points"]:,}</td><td>{e["hull"]:,}{flat}</td>'
                     f'<td>{format_time(e["hull_sec"])}</td>{obb}</tr>')
        data.append([href, name, e["points"], e["hull"], e["hull_sec"], e["obb_sec"], int(e["flat"])])

    if not table:
        table.append('    <tr><td class="dim" colspan="6">no .glb files found under ' + html.escape(GLB_DIR) + '</td></tr>')
    legend = "<div></div>"  # (Each figure has the same four parts, empty or not.)
    if any(row[6] for row in data):
        legend = ('<div class="legend">'
                  '<span><svg width="12" height="12"><circle cx="6" cy="6" r="4" style="fill: var(--series-1)"/></svg>'
                  'solid hull</span>'
                  '<span><svg width="12" height="12"><path d="M6 1 11 6 6 11 1 6Z" style="fill: var(--series-2)"/></svg>'
                  'flat hull (planar or collinear input)</span></div>')
    note = "<div></div>"
    if no_box:
        note = (f'<p class="note">Not shown: {len(no_box)} file{"s" if len(no_box) > 1 else ""} with a hull over the'
                f' size limit of minobb(), which returned no box: {", ".join(no_box)}.</p>')

    values = {
        "COUNT": str(len(files)),
        "HULL_COUNT": str(len(data)),
        "OBB_COUNT": str(len(data) - len(no_box)),
        "LEGEND": legend,
        "NOTE": note,
        "ROWS": "\n".join(table),
        # (No "<" in the data, so that nothing in it can end the script element.)
        "DATA": json.dumps(data, separators=(",", ":")).replace("<", "\\u003c"),
    }
    page = re.sub(r"@([A-Z_]+)@", lambda m: values[m.group(1)], PAGE)
    with open(OUT_FILE, "w", encoding="utf-8") as f:
        f.write(page)
    print(f"wrote {OUT_FILE} with {len(files)} links, {len(data)} of them in the plots")


PAGE = r"""<!DOCTYPE html>
<html>
<head>
<meta charset="utf-8">
<title>GLB files</title>
<style>
  :root {
    color-scheme: dark;
    --surface: #1a1a19; --raised: #2a2a28; --border: rgba(255, 255, 255, 0.10);
    --ink: #f0efec; --ink-2: #c3c2b7; --muted: #898781; --grid: #2c2c2a; --axis: #383835;
    --series-1: #3987e5; --series-2: #d95926;
  }
  body { font: 15px/1.6 monospace; background: #202020; color: #ddd; max-width: 1280px; margin: 24px auto; padding: 0 16px; }
  a { color: #6cf; text-decoration: none; }
  a:hover { text-decoration: underline; }
  .dim { color: #777; font-size: 12px; }

  .controls { display: flex; flex-wrap: wrap; align-items: center; gap: 8px 12px; margin: 0 0 12px; }
  .controls button { font: inherit; font-size: 13px; color: var(--ink-2); background: none; border: 1px solid var(--border); border-radius: 4px; padding: 2px 10px; cursor: pointer; }
  .controls button:hover { color: var(--ink); background: var(--raised); }
  .controls button[aria-pressed="true"] { color: var(--ink); background: var(--raised); }
  .seg { display: inline-flex; }
  .seg button:first-child { border-radius: 4px 0 0 4px; }
  .seg button:last-child { border-radius: 0 4px 4px 0; border-left: none; }
  /* Each figure is a caption, a legend, a plot and a note. The rows are shared, so that the plots line up. */
  .charts { display: grid; grid-template-columns: repeat(auto-fit, minmax(480px, 1fr)); gap: 0 16px; margin-bottom: 12px; }
  figure { display: grid; grid-template-rows: subgrid; grid-row: span 4; margin: 0 0 16px; padding: 14px 14px 8px;
           background: var(--surface); border: 1px solid var(--border); border-radius: 6px; min-width: 0; }
  figcaption b { display: block; font-size: 15px; color: var(--ink); }
  figcaption span, .legend, .note { font-size: 12px; color: var(--ink-2); }
  .legend { display: flex; flex-wrap: wrap; gap: 4px 16px; margin-top: 4px; }
  .legend svg { vertical-align: -1px; margin-right: 6px; }
  .note { margin: 4px 0 6px; }
  .plot { position: relative; height: 420px; margin-top: 6px; }
  .plot canvas { display: block; width: 100%; height: 100%; touch-action: none; cursor: grab; }
  .tip { position: absolute; left: 0; top: 0; display: none; pointer-events: none; white-space: nowrap; z-index: 1;
         font-size: 12px; line-height: 1.5; color: var(--ink-2); background: var(--raised);
         border: 1px solid var(--border); border-radius: 6px; padding: 8px 10px; box-shadow: 0 4px 16px rgba(0, 0, 0, 0.5); }
  .tip .value { font-size: 16px; font-weight: bold; color: var(--ink); }
  .tip .grid { display: grid; grid-template-columns: auto auto; gap: 0 14px; margin: 6px 0; }
  .tip .grid b { color: var(--ink); text-align: right; }
  .tip .hint { color: var(--muted); }

  table { border-collapse: collapse; }
  th { text-align: right; font-weight: normal; font-size: 12px; color: var(--muted); padding: 2px 10px; border-bottom: 1px solid var(--axis); }
  td { text-align: right; padding: 2px 10px; white-space: nowrap; }
  th:first-child, td:first-child { text-align: left; padding-left: 0; }
  th:nth-child(2), td:nth-child(2) { text-align: left; }
  td[colspan] { text-align: left; }
  tbody tr:hover { background: var(--surface); }
</style>
</head>
<body>
<h1>GLB files (@COUNT@)</h1>
<div class="controls">
  <span class="seg" role="group" aria-label="Axis scale"><button type="button" data-scale="log" aria-pressed="true">Log axes</button><button type="button" data-scale="linear" aria-pressed="false">Linear axes</button></span>
  <button type="button" id="reset">Reset zoom</button>
  <span class="dim">Scroll to zoom (over an axis: that axis only), drag to pan, double-click to reset. Click a point to open the file in the viewer.</span>
</div>
<div class="charts">
  <figure id="chart-hull">
    <figcaption><b>Convex hull time</b><span>convex_hull() on one thread, by the number of input vertices. One point per file (@HULL_COUNT@).</span></figcaption>
    @LEGEND@
    <div class="plot"><canvas role="img" aria-label="Scatter plot of the convex hull computation time against the number of input vertices, one point per file. The table below has the same numbers."></canvas><div class="tip"></div></div>
    <div></div>
  </figure>
  <figure id="chart-obb">
    <figcaption><b>Minimum OBB time</b><span>minobb() on one thread, by the number of hull vertices. One point per file (@OBB_COUNT@).</span></figcaption>
    @LEGEND@
    <div class="plot"><canvas role="img" aria-label="Scatter plot of the minimum OBB computation time against the number of vertices of the convex hull, one point per file. The table below has the same numbers."></canvas><div class="tip"></div></div>
    @NOTE@
  </figure>
</div>
<table id="files">
  <thead><tr><th>File</th><th>Folder</th><th>Input vertices</th><th>Hull vertices</th><th>Hull time</th><th>OBB time</th></tr></thead>
  <tbody>
@ROWS@
  </tbody>
</table>
<script type="application/json" id="glb-data">@DATA@</script>
<script>
(function () {
  'use strict';
  // One row per file: link, name, input vertices, hull vertices, hull seconds, OBB seconds (null: no box), flat hull.
  const rows = JSON.parse(document.getElementById('glb-data').textContent);
  const HREF = 0, NAME = 1, POINTS = 2, HULL = 3, HULL_SEC = 4, OBB_SEC = 5, FLAT = 6;

  const css = getComputedStyle(document.documentElement);
  const color = name => css.getPropertyValue(name).trim();
  const SURFACE = color('--surface'), GRID = color('--grid'), AXIS = color('--axis'), MUTED = color('--muted');
  const INK = color('--ink'), INK2 = color('--ink-2'), SERIES = [color('--series-1'), color('--series-2')];
  const FONT = '12px ' + getComputedStyle(document.body).fontFamily;
  const MARGIN = { left: 76, right: 20, top: 28, bottom: 46 };
  const RADIUS = 4, RING = 2, HIT_RADIUS = 24;
  const COUNT_UNITS = [[1e6, 'M'], [1e3, 'K'], [1, '']];
  const TIME_UNITS = [[1, ' s'], [1e-3, ' ms'], [1e-6, ' µs'], [1e-9, ' ns']];
  const STORE = 'glb-plots';

  let logScale = true;
  const fwd = v => logScale ? Math.log10(v) : v;         // A value to its axis coordinate,
  const inv = t => logScale ? Math.pow(10, t) : t;       // and back.
  const pow10 = e => Number('1e' + e);

  // ---- Numbers as text.
  function unitFor(units, v) {
    for (const u of units) if (v >= u[0] * 0.9995) return u;
    return units[units.length - 1];
  }
  const short = (v, u) => String(Number((v / u[0]).toPrecision(3))) + u[1];
  // The label of an axis tick. Unevenly spaced ticks (step 0: a logarithmic axis) each get the unit that suits
  // them. Evenly spaced ones share the unit of the largest, and the decimals that the step between them takes.
  function tickLabel(units, v, step, largest) {
    if (v === 0) return '0';
    if (!step) return short(v, unitFor(units, v));
    const u = unitFor(units, largest);
    const decimals = Math.min(Math.max(Math.ceil(-Math.log10(step / u[0]) - 1e-9), 0), 9);
    return (v / u[0]).toFixed(decimals) + u[1];
  }
  const fullCount = v => v.toLocaleString('en-US');
  const fullTime = s => short(s, unitFor(TIME_UNITS, s));

  // ---- Axis ticks.
  function niceStep(raw) {
    const p = Math.pow(10, Math.floor(Math.log10(raw))), f = raw / p;
    return (f <= 1 ? 1 : f <= 2 ? 2 : f <= 5 ? 5 : 10) * p;
  }
  // About `count` tick values for the range [lo, hi] of axis coordinates, and the step between them (0 if they
  // are not evenly spaced). A logarithmic axis gets powers of ten, or 1-2-5 steps when it shows only a few
  // decades, or the ticks of a linear axis when it shows less than that.
  function ticks(lo, hi, count) {
    const values = [];
    if (logScale) {
      const decades = Math.floor(hi) - Math.ceil(lo) + 1;
      if (decades >= 3) {
        const every = Math.ceil(decades / count);
        for (let e = Math.ceil(lo / every) * every; e <= hi; e += every) values.push(pow10(e));
        return { values, step: 0 };
      }
      for (let e = Math.floor(lo); e <= hi; ++e)
        for (const m of [1, 2, 5])
          if (e + Math.log10(m) >= lo && e + Math.log10(m) <= hi) values.push(m * pow10(e));
      if (values.length >= 3) return { values, step: 0 };
      values.length = 0;
    }
    const a = inv(lo), b = inv(hi), step = niceStep((b - a) / count);
    for (let i = Math.max(Math.ceil(a / step), 0); i * step <= b; ++i) values.push(i * step);
    return { values, step };
  }

  // ---- The plots.
  const charts = [];
  let hover = -1;         // The row under the pointer, in a plot or in the table.
  let hoverChart = null;  // The plot that shows its tooltip.

  function makeChart(id, spec) {
    const figure = document.getElementById(id);
    const plot = figure.querySelector('.plot'), canvas = plot.querySelector('canvas'), tip = plot.querySelector('.tip');
    const ctx = canvas.getContext('2d');
    // The rows that have a point in this plot: the solid hulls first, so that the few flat ones end up on top.
    const points = rows.map((r, i) => i).filter(i => rows[i][spec.x] > 0 && rows[i][spec.y] > 0)
      .sort((a, b) => rows[a][FLAT] - rows[b][FLAT]);
    const chart = { spec, view: null, home: null, draw: () => { if (!queued) { queued = true; requestAnimationFrame(draw); } } };
    let w = 0, h = 0, queued = false;
    let drag = null;      // While a button is down: where it went down, and the view at that time.
    let panned = false;   // Whether that turned into a pan, which is then not a click.

    const left = () => MARGIN.left, right = () => w - MARGIN.right, top = () => MARGIN.top, bottom = () => h - MARGIN.bottom;
    const sx = t => left() + (t - chart.view.x0) / (chart.view.x1 - chart.view.x0) * (right() - left());
    const sy = t => bottom() - (t - chart.view.y0) / (chart.view.y1 - chart.view.y0) * (bottom() - top());
    const local = e => { const r = canvas.getBoundingClientRect(); return [e.clientX - r.left, e.clientY - r.top]; };
    // The axes that the pointer acts on: just one of them when it is on that axis, outside of the plot area.
    const axesAt = (px, py) => py > bottom() ? 'x' : px < left() ? 'y' : 'xy';

    chart.reset = function () {
      let x0 = Infinity, x1 = -Infinity, y0 = Infinity, y1 = -Infinity;
      for (const i of points) {
        const x = fwd(rows[i][spec.x]), y = fwd(rows[i][spec.y]);
        x0 = Math.min(x0, x); x1 = Math.max(x1, x); y0 = Math.min(y0, y); y1 = Math.max(y1, y);
      }
      if (!points.length) { x0 = y0 = 0; x1 = y1 = 1; }
      if (!logScale) x0 = y0 = 0;
      const px = (x1 - x0) * 0.04 || 0.5, py = (y1 - y0) * 0.06 || 0.5;
      chart.home = { x0: x0 - px, x1: x1 + px, y0: y0 - py, y1: y1 + py };
      chart.view = Object.assign({}, chart.home);
    };

    // The view stays within sensible limits: inside of a box that is a little larger than the view of all the
    // data, and not zoomed in beyond a ten-thousandth of that.
    function limit(a, b, span, start) {
      const v = chart.view, full = chart.home[b] - chart.home[a], lo = chart.home[a] - full / 8, hi = chart.home[b] + full / 8;
      span = Math.min(Math.max(span, full * 1e-4), hi - lo);
      v[a] = Math.min(Math.max(start(span), lo), hi - span);
      v[b] = v[a] + span;
    }

    // Scales the view by `factor` along the given axes, keeping what is at the fractions (fx, fy) of it in place.
    function zoom(factor, fx, fy, axes) {
      const v = chart.view;
      if (axes.includes('x')) { const t = v.x0 + fx * (v.x1 - v.x0); limit('x0', 'x1', (v.x1 - v.x0) * factor, span => t - fx * span); }
      if (axes.includes('y')) { const t = v.y0 + fy * (v.y1 - v.y0); limit('y0', 'y1', (v.y1 - v.y0) * factor, span => t - fy * span); }
      changed();
    }

    function changed() {
      chart.draw();
      try {
        sessionStorage.setItem(STORE, JSON.stringify({ log: logScale, views: charts.map(c => c.view) }));
      } catch (e) { /* The view is just not remembered then. */ }
    }

    function path(x, y, flat, r) {
      ctx.beginPath();
      if (flat) { const d = r * 1.3; ctx.moveTo(x, y - d); ctx.lineTo(x + d, y); ctx.lineTo(x, y + d); ctx.lineTo(x - d, y); ctx.closePath(); }
      else ctx.arc(x, y, r, 0, 2 * Math.PI);
    }

    function draw() {
      queued = false;
      const dpr = window.devicePixelRatio || 1, L = left(), R = right(), T = top(), B = bottom(), v = chart.view;
      if (R - L < 40 || B - T < 40) return;
      ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
      ctx.fillStyle = SURFACE;
      ctx.fillRect(0, 0, w, h);
      ctx.font = FONT;
      ctx.lineWidth = 1;

      // Grid and axes: hairlines, on whole pixels.
      const xt = ticks(v.x0, v.x1, Math.max(2, Math.floor((R - L) / 64)));
      const yt = ticks(v.y0, v.y1, Math.max(2, Math.floor((B - T) / 40)));
      ctx.strokeStyle = GRID;
      ctx.beginPath();
      for (const t of xt.values) { const x = Math.round(sx(fwd(t))) + 0.5; ctx.moveTo(x, T); ctx.lineTo(x, B); }
      for (const t of yt.values) { const y = Math.round(sy(fwd(t))) + 0.5; ctx.moveTo(L, y); ctx.lineTo(R, y); }
      ctx.stroke();
      ctx.strokeStyle = AXIS;
      ctx.beginPath();
      ctx.moveTo(L + 0.5, T); ctx.lineTo(L + 0.5, B + 0.5); ctx.lineTo(R, B + 0.5);
      ctx.stroke();

      // Tick labels and axis titles.
      ctx.fillStyle = MUTED;
      ctx.textBaseline = 'top';
      ctx.textAlign = 'center';
      for (const t of xt.values) {
        const label = tickLabel(spec.xUnits, t, xt.step, xt.values[xt.values.length - 1]), half = ctx.measureText(label).width / 2;
        ctx.fillText(label, Math.min(Math.max(sx(fwd(t)), half + 2), w - half - 2), B + 8);
      }
      ctx.textBaseline = 'middle';
      ctx.textAlign = 'right';
      for (const t of yt.values) ctx.fillText(tickLabel(TIME_UNITS, t, yt.step, yt.values[yt.values.length - 1]), L - 8, sy(fwd(t)));
      ctx.fillStyle = INK2;
      ctx.textBaseline = 'alphabetic';
      ctx.textAlign = 'center';
      ctx.fillText(spec.xTitle, (L + R) / 2, h - 8);
      ctx.textAlign = 'left';
      ctx.fillText('time', 8, 16);

      // The points, each with a ring of the surface color around it that keeps overlapping ones apart.
      ctx.save();
      ctx.beginPath();
      ctx.rect(L, T, R - L, B - T);
      ctx.clip();
      for (const i of points) {
        const x = sx(fwd(rows[i][spec.x])), y = sy(fwd(rows[i][spec.y]));
        if (x < L - 8 || x > R + 8 || y < T - 8 || y > B + 8) continue;
        ctx.fillStyle = SURFACE; path(x, y, rows[i][FLAT], RADIUS + RING); ctx.fill();
        ctx.fillStyle = SERIES[rows[i][FLAT]]; path(x, y, rows[i][FLAT], RADIUS); ctx.fill();
      }
      // The row under the pointer: lines to its values on the axes, and a larger, outlined point.
      const p = position(hover);
      if (p) {
        ctx.strokeStyle = MUTED;
        ctx.beginPath();
        ctx.moveTo(L, Math.round(p[1]) + 0.5); ctx.lineTo(p[0], Math.round(p[1]) + 0.5);
        ctx.moveTo(Math.round(p[0]) + 0.5, B); ctx.lineTo(Math.round(p[0]) + 0.5, p[1]);
        ctx.stroke();
        ctx.fillStyle = SURFACE; path(p[0], p[1], rows[hover][FLAT], RADIUS + 2 + RING); ctx.fill();
        ctx.fillStyle = SERIES[rows[hover][FLAT]]; path(p[0], p[1], rows[hover][FLAT], RADIUS + 2); ctx.fill();
        ctx.strokeStyle = INK; ctx.lineWidth = 1.5; ctx.stroke();
      }
      ctx.restore();
    }

    // Where the point of a row is on the canvas, or null if it has none in the visible part of this plot.
    function position(i) {
      if (i < 0 || !(rows[i][spec.x] > 0 && rows[i][spec.y] > 0)) return null;
      const x = sx(fwd(rows[i][spec.x])), y = sy(fwd(rows[i][spec.y]));
      return x < left() || x > right() || y < top() || y > bottom() ? null : [x, y];
    }

    // The row whose point is the closest to the pointer: it does not have to be hit, only to be near.
    function pick(px, py) {
      let best = -1, distance = HIT_RADIUS * HIT_RADIUS;
      for (const i of points) {
        const p = position(i);
        if (!p) continue;
        const d = (p[0] - px) * (p[0] - px) + (p[1] - py) * (p[1] - py);
        if (d <= distance) { distance = d; best = i; }
      }
      return best;
    }

    chart.showTip = function () {
      const p = hoverChart === chart ? position(hover) : null;
      tip.style.display = p ? 'block' : 'none';
      if (!p) return;
      const r = rows[hover];
      const add = (parent, tag, cls, text) => {
        const e = document.createElement(tag);
        if (cls) e.className = cls;
        e.textContent = text;   // File names are data: never markup.
        parent.appendChild(e);
        return e;
      };
      tip.textContent = '';
      add(tip, 'div', 'value', fullTime(r[spec.y]));
      add(tip, 'div', '', spec.yName);
      const grid = add(tip, 'div', 'grid', '');
      const pair = (name, value) => { add(grid, 'span', '', name); add(grid, 'b', '', value); };
      pair('input vertices', fullCount(r[POINTS]));
      pair('hull vertices', fullCount(r[HULL]) + (r[FLAT] ? ' (flat hull)' : ''));
      if (spec.y !== HULL_SEC) pair('hull time', fullTime(r[HULL_SEC]));
      if (spec.y !== OBB_SEC) pair('OBB time', r[OBB_SEC] === null ? 'none: hull too large' : fullTime(r[OBB_SEC]));
      add(tip, 'div', '', r[NAME]);
      add(tip, 'div', 'hint', 'click to open in the viewer');
      let x = p[0] + 14, y = p[1] + 14;
      if (x + tip.offsetWidth > w) x = p[0] - 14 - tip.offsetWidth;
      if (y + tip.offsetHeight > h) y = p[1] - 14 - tip.offsetHeight;
      tip.style.transform = 'translate(' + Math.max(x, 0) + 'px,' + Math.max(y, 0) + 'px)';
    };

    function resize() {
      const dpr = window.devicePixelRatio || 1;
      w = plot.clientWidth; h = plot.clientHeight;
      canvas.width = Math.round(w * dpr); canvas.height = Math.round(h * dpr);
      draw();
      chart.showTip();
    }

    canvas.addEventListener('pointerdown', e => {
      if (e.button !== 0) return;
      const [px, py] = local(e);
      drag = { x: e.clientX, y: e.clientY, view: Object.assign({}, chart.view), axes: axesAt(px, py) };
      panned = false;
      canvas.setPointerCapture(e.pointerId);
    });
    canvas.addEventListener('pointermove', e => {
      const [px, py] = local(e);
      if (drag) {
        const dx = e.clientX - drag.x, dy = e.clientY - drag.y, v = chart.view, d = drag.view;
        if (!panned && Math.abs(dx) + Math.abs(dy) < 4) return;
        panned = true;
        canvas.style.cursor = 'grabbing';
        setHover(-1, null);
        if (drag.axes.includes('x')) limit('x0', 'x1', d.x1 - d.x0, () => d.x0 - dx / (right() - left()) * (d.x1 - d.x0));
        if (drag.axes.includes('y')) limit('y0', 'y1', d.y1 - d.y0, () => d.y0 + dy / (bottom() - top()) * (d.y1 - d.y0));
        changed();
        return;
      }
      const i = pick(px, py);
      canvas.style.cursor = i >= 0 ? 'pointer' : 'grab';
      setHover(i, chart);
    });
    const release = () => { drag = null; canvas.style.cursor = 'grab'; };
    canvas.addEventListener('pointerup', release);
    canvas.addEventListener('pointercancel', release);
    canvas.addEventListener('pointerleave', () => { if (!drag) setHover(-1, null); });
    canvas.addEventListener('wheel', e => {
      e.preventDefault();
      const [px, py] = local(e);
      zoom(Math.exp((e.deltaMode === 1 ? e.deltaY * 33 : e.deltaY) * 0.0015), (px - left()) / (right() - left()),
        (bottom() - py) / (bottom() - top()), axesAt(px, py));
      if (!drag) setHover(pick(px, py), chart);
    }, { passive: false });
    canvas.addEventListener('dblclick', () => { chart.reset(); changed(); });
    // A click on a point is a click on the link of its file: it opens the viewer, in a new tab with Ctrl,
    // Shift or the middle button.
    const open = e => {
      const i = panned ? -1 : pick(...local(e));
      if (i < 0) return;
      if (e.button === 1 || e.ctrlKey || e.metaKey || e.shiftKey) window.open(rows[i][HREF], '_blank', 'noopener');
      else location.href = rows[i][HREF];
    };
    canvas.addEventListener('click', open);
    canvas.addEventListener('auxclick', e => { if (e.button === 1) open(e); });
    canvas.addEventListener('mousedown', e => { if (e.button === 1) e.preventDefault(); }); // No autoscroll.
    new ResizeObserver(resize).observe(plot);
    window.addEventListener('resize', resize);

    chart.reset();
    charts.push(chart);
    return chart;
  }

  function setHover(i, chart) {
    if (i === hover && chart === hoverChart) return;
    hover = i; hoverChart = chart;
    for (const c of charts) { c.draw(); c.showTip(); }
  }

  makeChart('chart-hull', { x: POINTS, y: HULL_SEC, xUnits: COUNT_UNITS, xTitle: 'input vertices', yName: 'convex hull time' });
  makeChart('chart-obb', { x: HULL, y: OBB_SEC, xUnits: COUNT_UNITS, xTitle: 'hull vertices', yName: 'minimum OBB time' });

  // ---- The controls above the plots, which act on both.
  const scaleButtons = document.querySelectorAll('[data-scale]');
  function setScale(log) {
    logScale = log;
    for (const b of scaleButtons) b.setAttribute('aria-pressed', String((b.dataset.scale === 'log') === log));
    for (const c of charts) c.reset();
  }
  function redraw() { for (const c of charts) { c.draw(); c.showTip(); } }
  for (const b of scaleButtons) b.addEventListener('click', () => { setScale(b.dataset.scale === 'log'); redraw(); sessionStorage.removeItem(STORE); });
  document.getElementById('reset').addEventListener('click', () => { setScale(logScale); redraw(); sessionStorage.removeItem(STORE); });

  // Coming back from the viewer, show the plots as they were left.
  try {
    const saved = JSON.parse(sessionStorage.getItem(STORE));
    const ok = v => v && ['x0', 'x1', 'y0', 'y1'].every(k => Number.isFinite(v[k])) && v.x1 > v.x0 && v.y1 > v.y0;
    if (saved && saved.views.length === charts.length && saved.views.every(ok)) {
      setScale(!!saved.log);
      charts.forEach((c, i) => { c.view = saved.views[i]; });
    }
  } catch (e) { /* Nothing usable was saved. */ }
  redraw();

  // A row of the table points out its file in the plots.
  const body = document.querySelector('#files tbody');
  body.addEventListener('mouseover', e => { const tr = e.target.closest('tr[data-i]'); setHover(tr ? Number(tr.dataset.i) : -1, null); });
  body.addEventListener('mouseleave', () => setHover(-1, null));
})();
</script>
</body>
</html>
"""


if __name__ == "__main__":
    main()
