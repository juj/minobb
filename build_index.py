#!/usr/bin/env python3
"""Scans test/glb for .glb files and writes glb.html listing them as links
to view.html?url=<relative path>. Run from the repo root: python build_index.py"""

import html
import os

GLB_DIR = "test/glb"
OUT_FILE = "glb.html"


def main() -> None:
    glb_paths = []
    for dirpath, _dirnames, filenames in os.walk(GLB_DIR):
        for name in filenames:
            if name.lower().endswith(".glb"):
                glb_paths.append(os.path.join(dirpath, name))
    glb_paths.sort()

    rows = []
    for p in glb_paths:
        url = p.replace(os.sep, "/")
        label = os.path.basename(p)
        folder = os.path.basename(os.path.dirname(p))
        has_json = os.path.exists(os.path.splitext(p)[0] + ".json")
        marker = " [hull+obb]" if has_json else ""
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
