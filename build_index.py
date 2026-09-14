#!/usr/bin/env python3
"""Scans test/glb for .glb files and writes glb.html listing them as links
to view.html?url=<relative path>. Run from the repo root: python build_index.py"""

import html
import json
import os

GLB_DIR = "test/glb"
OUT_FILE = "glb.html"


def load_timing(p: str):
    """Total hull+obb generation time in seconds from the sibling .json,
    or None if the .json is missing or has no timing info."""
    path = os.path.splitext(p)[0] + ".json"
    if not os.path.exists(path):
        return None
    try:
        with open(path, encoding="utf-8") as f:
            data = json.load(f)
        t = data.get("timing", {})
        return float(t.get("hull_sec", 0.0)) + float(t.get("obb_sec", 0.0))
    except (OSError, ValueError, TypeError):
        return None


def main() -> None:
    glb_paths = []
    for dirpath, _dirnames, filenames in os.walk(GLB_DIR):
        for name in filenames:
            if name.lower().endswith(".glb"):
                glb_paths.append(os.path.join(dirpath, name))

    # Sort by total generation time, slowest first; entries without timing
    # info (no .json) go last, alphabetically.
    def sort_key(p):
        t = load_timing(p)
        if t is None:
            return (1, 0.0, p)
        return (0, -t, p)

    glb_paths.sort(key=sort_key)

    rows = []
    for p in glb_paths:
        url = p.replace(os.sep, "/")
        label = os.path.basename(p)
        folder = os.path.basename(os.path.dirname(p))
        t = load_timing(p)
        if t is None:
            marker = ""
        else:
            marker = f" [hull+obb {t:.3f}s]"
        rows.append(
            f'    <li><a href="view.html?url={html.escape(url, quote=True)}">'
            f'{html.escape(label)}{html.escape(marker)}</a> '
            f'<span class="dim">{html.escape(folder)}</span></li>'
        )

    page = f"""<!DOCTYPE html>
<html>
<head>
<meta charset="utf-8">
<title>GLB files</title>
<style>
  body {{ font: 15px/1.6 monospace; background: #202020; color: #ddd; max-width: 720px; margin: 24px auto; padding: 0 16px; }}
  a {{ color: #6cf; text-decoration: none; }}
  a:hover {{ text-decoration: underline; }}
  .dim {{ color: #777; font-size: 12px; }}
  li {{ margin: 4px 0; }}
</style>
</head>
<body>
<h1>GLB files ({len(glb_paths)})</h1>
<ul>
{chr(10).join(rows) if rows else '    <li class="dim">no .glb files found under ' + html.escape(GLB_DIR) + '</li>'}
</ul>
</body>
</html>
"""
    with open(OUT_FILE, "w", encoding="utf-8") as f:
        f.write(page)
    print(f"wrote {OUT_FILE} with {len(glb_paths)} links")


if __name__ == "__main__":
    main()
