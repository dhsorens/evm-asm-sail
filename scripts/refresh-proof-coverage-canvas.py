#!/usr/bin/env python3
"""Refresh SpecRef ↔ Evm proof-coverage views from the living docs.

Markdown is source of truth:
  docs/opcode-coverage.md
  docs/comparison-matrix.md

Outputs (kept in sync from the same DATA snapshot):
  docs/index.html                   — site source (Pages `/docs` → live URL below)
  ~/.cursor/.../proof-coverage.canvas.tsx — Cursor canvas DATA blob (if present)

Live site (after pushing docs/index.html on main):
  https://derekhsorensen.com/evm-asm-sail/

  python3 scripts/refresh-proof-coverage-canvas.py
"""

from __future__ import annotations

import html
import json
import re
import sys
from collections import Counter
from datetime import date
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
OPCODE_DOC = REPO / "docs" / "opcode-coverage.md"
COMPARISON_DOC = REPO / "docs" / "comparison-matrix.md"
HTML_OUT = REPO / "docs" / "index.html"
SITE_URL = "https://derekhsorensen.com/evm-asm-sail/"
GITHUB_BLOB = "https://github.com/dhsorens/evm-asm-sail/blob/main/"
CANVAS = (
    Path.home()
    / ".cursor"
    / "projects"
    / "Users-dhsorens-devel-evm-evm-asm-sail"
    / "canvases"
    / "proof-coverage.canvas.tsx"
)

OUTCOME_REL = {
    "relationFile": "EvmSpecsVerify/Relations/Outcome.lean",
    "stepResultRelLine": 53,
    "errorRelLine": 35,
}


def parse_md_tables(text: str):
    sections: list[tuple[str | None, list[str], list[dict[str, str]]]] = []
    current: str | None = None
    lines = text.splitlines()
    i = 0
    while i < len(lines):
        line = lines[i]
        if line.startswith("## "):
            current = line[3:].strip()
            i += 1
            continue
        if (
            line.startswith("|")
            and i + 1 < len(lines)
            and re.match(r"^\|[\s\-|]+\|$", lines[i + 1])
        ):
            headers = [c.strip() for c in line.strip("|").split("|")]
            i += 2
            rows: list[dict[str, str]] = []
            while i < len(lines) and lines[i].startswith("|"):
                cells = [c.strip() for c in lines[i].strip("|").split("|")]
                if not re.match(r"^[\s\-:]+$", "".join(cells).replace("|", "")):
                    rows.append(dict(zip(headers, cells)))
                i += 1
            sections.append((current, headers, rows))
            continue
        i += 1
    return sections


def strip_md(value: str) -> str:
    return re.sub(r"[*`]", "", value).strip()


def status_kind(status: str) -> str:
    cleaned = strip_md(status)
    if not cleaned:
        return ""
    return cleaned.split()[0]


def find_decl_line(rel_path: str, name: str) -> int | None:
    path = REPO / rel_path
    if not path.is_file():
        return None
    pat = re.compile(
        rf"^(?:theorem|lemma|def|inductive|structure|abbrev)\s+{re.escape(name)}\b"
    )
    for i, line in enumerate(path.read_text().splitlines(), start=1):
        if pat.match(line):
            return i
    return None


def parse_proof(status: str) -> dict | None:
    cleaned = strip_md(status)
    kind = status_kind(status)
    proof: dict = {**OUTCOME_REL}

    m = re.match(
        r"^(unstated|stated|success-proven|full|n/a)\b(?:\s*\((.*)\)|\s+(.+))?$",
        cleaned,
        flags=re.IGNORECASE | re.DOTALL,
    )
    if not m:
        return proof if kind != "unstated" else None

    body = (m.group(2) or m.group(3) or "").strip()
    if kind == "unstated" and not body:
        return None

    if body:
        proof["note"] = body

    if kind in ("full", "stated", "success-proven") and m.group(2):
        parts = re.split(r"\s*[—–]\s*", m.group(2).strip(), maxsplit=1)
        head = parts[0].strip()
        tail = parts[1].strip() if len(parts) > 1 else ""

        md = re.match(
            r"^\[`?([A-Za-z_][\w']*)`?\]\("
            r"(?:\.\./)*"
            r"((?:EvmSpecsVerify|extraction)[^)#\s]+?\.lean)"
            r"(?:#L\d+)?"
            r"\)",
            head,
        )
        hm = md
        if not hm:
            hm = re.match(
                r"^([A-Za-z_][\w']*)\s*,\s*((?:EvmSpecsVerify|extraction)[^\s,]+\.lean)",
                head,
            )
        if not hm:
            hm = re.match(r"^([A-Za-z_][\w']*)\s*,\s*([^\s,]+\.lean)", head)
        if hm:
            theorem = hm.group(1)
            file_path = hm.group(2)
            proof["theorem"] = theorem
            proof["file"] = file_path
            line = find_decl_line(file_path, theorem)
            if line is not None:
                proof["line"] = line

        if tail:
            segs = [s.strip() for s in tail.split(";") if s.strip()]
            if segs:
                outcomes = [
                    x.strip() for x in re.split(r"[/,]", segs[0]) if x.strip()
                ]
                if outcomes:
                    proof["outcomes"] = outcomes
            if len(segs) > 1:
                un = segs[1]
                um = re.match(r"^(\w+)\s+unreachable\b(.*)$", un, flags=re.I)
                if um:
                    proof["unreachable"] = [um.group(1)]
                    rest = um.group(2).strip(" :,—–")
                    if rest:
                        proof["unreachableNote"] = rest
                else:
                    proof["unreachableNote"] = un

    return proof


def load_data() -> dict:
    opc = parse_md_tables(OPCODE_DOC.read_text())
    cmp = parse_md_tables(COMPARISON_DOC.read_text())

    opcodes: list[dict] = []
    opcode_counts: dict[str, int] = {}
    for sec, headers, rows in opc:
        if sec == "Counts (must match `EvmSpecsVerify/Coverage/Registry.lean`)":
            for r in rows:
                label = strip_md(r.get("status", "")).lower()
                count_raw = strip_md(r.get("count", "0")).replace(",", "")
                try:
                    count = int(count_raw)
                except ValueError:
                    continue
                if label.startswith("total"):
                    opcode_counts["total"] = count
                elif label.startswith("n/a"):
                    opcode_counts["n/a"] = count
                else:
                    opcode_counts[label.split()[0]] = count
            continue
        if sec in ("Shape classes",) or sec is None:
            continue
        if "opcode" not in headers:
            continue
        for r in rows:
            shape = r.get("shape", "")
            shape_family = re.split(r"[\s(+]", shape)[0]
            spec = r.get("SpecRef", "")
            partial = "*(partial)*" in spec
            status = r.get("status", "")
            entry: dict = {
                "family": sec,
                "opcode": r["opcode"],
                "byte": r.get("byte", ""),
                "specRef": spec.replace(" *(partial)*", "").replace("`", ""),
                "evm": r.get("`Evm`", r.get("Evm", "")).replace("`", ""),
                "shape": shape,
                "shapeFamily": shape_family,
                "status": strip_md(status),
                "statusKind": status_kind(status),
                "partial": partial,
            }
            proof = parse_proof(status)
            if proof is not None:
                entry["proof"] = proof
            opcodes.append(entry)

    components: list[dict] = []
    for sec, headers, rows in cmp:
        if sec in ("Monads and outcomes", "Error kind mapping (ErrorRel)"):
            continue
        if "component" not in headers:
            continue
        for r in rows:
            spec = r.get("SpecRef repr", "")
            evm = r.get("`Evm` repr", r.get("Evm repr", ""))
            status = r.get("status", "")
            components.append(
                {
                    "section": sec,
                    "component": r["component"],
                    "specRef": spec,
                    "evm": evm,
                    "relation": r.get("relation", ""),
                    "invariants": r.get("invariants", ""),
                    "status": strip_md(status),
                    "statusKind": status_kind(status),
                    "specRefShort": spec[:80] + ("…" if len(spec) > 80 else ""),
                    "evmShort": evm[:80] + ("…" if len(evm) > 80 else ""),
                }
            )

    return {
        "opcodes": opcodes,
        "components": components,
        "opcodeCounts": opcode_counts,
        "glossary": {
            "unstated": "No SpecRef ↔ Evm step theorem yet for this opcode.",
            "stated": "A theorem exists but may still cite unfinished lemmas.",
            "success-proven": "Only the success path is proved — not acceptable as final coverage.",
            "full": "Full StepResultRel: success plus every reachable failure (e.g. underflow, OOG). Unreachable failures may be omitted with justification.",
            "n/a": "Out of scope for this tranche (with a recorded reason).",
        },
        "links": {
            "opcodeLegend": {"path": "docs/opcode-coverage.md", "line": 8},
            "outcomeRel": OUTCOME_REL,
        },
        "source": {
            "opcodeDoc": "docs/opcode-coverage.md",
            "comparisonDoc": "docs/comparison-matrix.md",
            "asOf": date.today().isoformat(),
        },
    }


def replace_data_blob(canvas_text: str, data: dict) -> str:
    marker = "const DATA = "
    start = canvas_text.find(marker)
    if start < 0:
        raise SystemExit("canvas missing `const DATA = ` marker")
    start += len(marker)
    end = canvas_text.find(" as const;", start)
    if end < 0:
        raise SystemExit("canvas missing ` as const;` after DATA")
    return canvas_text[:start] + json.dumps(data, indent=2) + canvas_text[end:]


def esc(value: object) -> str:
    return html.escape(str(value), quote=True)


def ext_a(href: str, text: str, *, title: str | None = None) -> str:
    """External/site link: always open in a new tab. Use for every <a> in docs/index.html."""
    attrs = (
        f"href='{esc(href)}' target='_blank' rel='noopener noreferrer'"
    )
    if title is not None:
        attrs += f" title='{esc(title)}'"
    return f"<a {attrs}>{text}</a>"


def repo_href(rel_path: str, line: int | None = None) -> str:
    """GitHub blob link: only docs/ is published, so in-repo relative paths 404 on the site."""
    href = GITHUB_BLOB + rel_path
    if line:
        # markdown renders by default on GitHub, where line anchors do nothing
        href += f"?plain=1#L{line}" if rel_path.endswith(".md") else f"#L{line}"
    return href


def next_slice(opcodes: list[dict]) -> list[dict]:
    """Preferred unstated follow-ups after the ALU binop sweep (PROGRESS M1 residual → M2)."""
    preferred = [
        "ISZERO",
        "NOT",
        "CLZ",
        "ADDMOD",
        "MULMOD",
        "EXP",
        "POP",
        "PUSH (n, w)",
        "DUP n",
        "MLOAD",
        "JUMPI",
        "SLOAD",
        "RETURN",
    ]
    by_name = {o["opcode"]: o for o in opcodes if o["statusKind"] == "unstated"}
    ranked = [by_name[name] for name in preferred if name in by_name]
    if ranked:
        return ranked[:8]
    # Fallback: any remaining unstated ALU-family rows, then other unstated
    alu = [
        o
        for o in opcodes
        if o["statusKind"] == "unstated" and o["family"] == "ALU family"
    ]
    if alu:
        return alu[:8]
    return [o for o in opcodes if o["statusKind"] == "unstated"][:8]


def next_slice_blurb(slice_rows: list[dict], full_count: int) -> str:
    if not slice_rows:
        return (
            f"<code>{esc(full_count)}</code> opcodes are <code>full</code>. "
            "No unstated suggested-next rows remain in the default queue."
        )
    heads = ", ".join(f"<code>{esc(o['opcode'])}</code>" for o in slice_rows[:3])
    return (
        f"<code>{esc(full_count)}</code> opcodes are <code>full</code> "
        "(ALU binop sweep landed). Suggested next: "
        f"{heads}, then continue the M1 residual / M2 shape validators "
        "(unops, ternops, EXP, PUSHn, DUPn, MLOAD, JUMPI, SLOAD, RETURN)."
    )


def render_html(data: dict) -> str:
    counts = data["opcodeCounts"]
    glossary = data["glossary"]
    opcodes = data["opcodes"]
    components = data["components"]
    as_of = data["source"]["asOf"]
    families = Counter(o["family"] for o in opcodes)
    unrelated = sum(1 for c in components if c["statusKind"] == "unrelated")
    slice_rows = next_slice(opcodes)
    slice_blurb = next_slice_blurb(slice_rows, counts.get("full", 0))
    outcome = data["links"]["outcomeRel"]
    legend = data["links"]["opcodeLegend"]
    legend_href = repo_href(legend["path"], legend.get("line"))
    comparison_href = repo_href(data["source"]["comparisonDoc"])
    opcode_doc_href = repo_href(data["source"]["opcodeDoc"])

    family_bars = "".join(
        f'<div class="bar-row"><span class="bar-label">{esc(name)}</span>'
        f'<div class="bar-track"><div class="bar-fill" style="width:{100 * n / max(len(opcodes), 1):.1f}%"></div></div>'
        f'<span class="bar-n">{n}</span></div>'
        for name, n in sorted(families.items(), key=lambda kv: -kv[1])
    )

    glossary_html = "".join(
        f'<div class="glossary-row"><span class="pill">{esc(k)}</span>'
        f'<span>{esc(glossary[k])}</span></div>'
        for k in ("full", "success-proven", "stated", "unstated", "n/a")
        if k in glossary
    )

    slice_html = "".join(
        "<tr>"
        f"<td>{esc(o['opcode'])}</td><td><code>{esc(o['byte'])}</code></td>"
        f"<td><code>{esc(o['specRef'])}</code></td><td><code>{esc(o['evm'])}</code></td>"
        f"<td>{esc(o['shape'])}</td><td><span class='pill'>{esc(o['statusKind'])}</span></td>"
        "</tr>"
        for o in slice_rows
    )

    opcode_details = []
    for o in opcodes:
        proof = o.get("proof") or {}
        open_attr = " open" if o["statusKind"] == "full" else ""
        badges = (
            f"<span class='pill status-{esc(o['statusKind']).replace('/', '')}'>"
            f"{esc(o['statusKind'])}</span>"
        )
        if o.get("partial"):
            badges += " <span class='pill'>partial</span>"
        if proof.get("theorem"):
            badges += " <span class='pill'>theorem</span>"

        meaning = glossary.get(o["statusKind"], "")
        body_parts = [
            f"<p><strong>Status meaning:</strong> {esc(meaning)}</p>",
            (
                "<p class='meta'>SpecRef <code>"
                + esc(o["specRef"])
                + "</code> · Evm <code>"
                + esc(o["evm"])
                + "</code> · shape <code>"
                + esc(o["shape"])
                + "</code></p>"
            ),
        ]

        if proof.get("theorem") and proof.get("file"):
            line = proof.get("line")
            thm = ext_a(
                repo_href(proof["file"], line),
                "<code>" + esc(proof["theorem"]) + "</code>",
            )
            body_parts.append(
                "<p><strong>Step theorem:</strong> "
                + thm
                + (f" @ line {esc(line)}" if line else "")
                + "</p>"
            )
            links = [
                ext_a(repo_href(proof["file"], line), esc(proof["file"])),
                ext_a(
                    repo_href(
                        outcome["relationFile"], outcome.get("stepResultRelLine")
                    ),
                    "StepResultRel",
                ),
                ext_a(
                    repo_href(outcome["relationFile"], outcome.get("errorRelLine")),
                    "ErrorRel",
                ),
            ]
            body_parts.append("<p class='links'>" + " · ".join(links) + "</p>")

        if proof.get("outcomes"):
            pills = " ".join(
                f"<span class='pill'>{esc(x)}</span>" for x in proof["outcomes"]
            )
            body_parts.append(f"<p><strong>Covered outcomes:</strong> {pills}</p>")

        if proof.get("unreachable"):
            note = proof.get("unreachableNote", "")
            body_parts.append(
                "<p class='muted'>Unreachable (omitted): "
                + esc(", ".join(proof["unreachable"]))
                + (f" — {esc(note)}" if note else "")
                + "</p>"
            )

        if o["statusKind"] == "unstated":
            body_parts.append(
                "<p class='muted'>Not proved yet — see Suggested next vertical slice.</p>"
            )
        elif o["statusKind"] == "n/a" and proof.get("note"):
            body_parts.append(f"<p class='muted'>Reason: {esc(proof['note'])}</p>")

        body_parts.append(
            "<p class='links'>"
            + ext_a(legend_href, "Status legend (docs)")
            + "</p>"
        )

        search = " ".join(
            [
                o["opcode"],
                o["byte"],
                o["family"],
                o["shape"],
                o["specRef"],
                o["evm"],
                o["statusKind"],
                proof.get("theorem", ""),
            ]
        ).lower()

        opcode_details.append(
            f"<details class='opcode'{open_attr} data-status='{esc(o['statusKind'])}' "
            f"data-family='{esc(o['family'])}' data-shape='{esc(o['shapeFamily'])}' "
            f"data-search='{esc(search)}'>"
            f"<summary><span class='sum-title'>{esc(o['opcode'])} "
            f"<code>{esc(o['byte'])}</code> · {esc(o['shapeFamily'])}</span>"
            f"<span class='sum-badges'>{badges}</span></summary>"
            f"<div class='detail'>{''.join(body_parts)}</div></details>"
        )

    component_rows = "".join(
        "<tr>"
        f"<td>{esc(c['component'])}</td>"
        f"<td>{esc(c['section'].replace(' (tranche ≥ 3)', ''))}</td>"
        f"<td><code>{esc(c['relation'])}</code></td>"
        f"<td class='clip' title='{esc(c['specRef'])}'>{esc(c['specRefShort'])}</td>"
        f"<td class='clip' title='{esc(c['evm'])}'>{esc(c['evmShort'])}</td>"
        f"<td><span class='pill'>{esc(c['statusKind'])}</span></td>"
        "</tr>"
        for c in components
    )

    return f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8" />
<meta name="viewport" content="width=device-width, initial-scale=1" />
<title>SpecRef ↔ Evm proof coverage</title>
<style>
  :root {{
    color-scheme: light dark;
    --bg: #0f1115;
    --fg: #e8eaed;
    --muted: #9aa0a6;
    --card: #1a1d24;
    --stroke: #2c313a;
    --accent: #8ab4f8;
    --ok: #81c995;
    --warn: #fdd663;
    --info: #aecbfa;
    --mono: ui-monospace, SFMono-Regular, Menlo, Consolas, monospace;
    --sans: ui-sans-serif, system-ui, -apple-system, Segoe UI, Roboto, Helvetica, Arial, sans-serif;
  }}
  @media (prefers-color-scheme: light) {{
    :root {{
      --bg: #f7f8fa;
      --fg: #202124;
      --muted: #5f6368;
      --card: #ffffff;
      --stroke: #dadce0;
      --accent: #1a73e8;
      --ok: #188038;
      --warn: #b06000;
      --info: #1967d2;
    }}
  }}
  * {{ box-sizing: border-box; }}
  body {{
    margin: 0;
    font: 15px/1.5 var(--sans);
    background: var(--bg);
    color: var(--fg);
  }}
  main {{ max-width: 1080px; margin: 0 auto; padding: 28px 20px 64px; }}
  h1 {{ font-size: 1.75rem; margin: 0 0 8px; }}
  h2 {{ font-size: 1.2rem; margin: 28px 0 10px; }}
  a {{ color: var(--accent); }}
  code {{ font-family: var(--mono); font-size: 0.92em; }}
  .muted {{ color: var(--muted); }}
  .banner {{
    border: 1px solid var(--stroke);
    background: var(--card);
    border-radius: 10px;
    padding: 12px 14px;
    margin: 14px 0 22px;
    color: var(--muted);
    font-size: 0.92rem;
  }}
  .stats {{
    display: grid;
    grid-template-columns: repeat(4, minmax(0, 1fr));
    gap: 12px;
    margin: 18px 0;
  }}
  @media (max-width: 800px) {{
    .stats {{ grid-template-columns: repeat(2, minmax(0, 1fr)); }}
  }}
  .stat {{
    background: var(--card);
    border: 1px solid var(--stroke);
    border-radius: 10px;
    padding: 14px;
  }}
  .stat .v {{ font-size: 1.6rem; font-weight: 650; }}
  .stat .l {{ color: var(--muted); font-size: 0.85rem; margin-top: 4px; }}
  .card {{
    background: var(--card);
    border: 1px solid var(--stroke);
    border-radius: 10px;
    padding: 14px 16px;
    margin: 14px 0;
  }}
  .pill {{
    display: inline-block;
    border: 1px solid var(--stroke);
    border-radius: 999px;
    padding: 1px 8px;
    font-size: 0.78rem;
    color: var(--muted);
    white-space: nowrap;
  }}
  .status-full {{ color: var(--ok); border-color: color-mix(in srgb, var(--ok) 40%, var(--stroke)); }}
  .status-unstated {{ color: var(--warn); }}
  .status-na {{ color: var(--info); }}
  .glossary-row {{ display: flex; gap: 10px; align-items: flex-start; margin: 8px 0; }}
  .bar-row {{ display: grid; grid-template-columns: 180px 1fr 40px; gap: 10px; align-items: center; margin: 6px 0; }}
  .bar-label {{ font-size: 0.85rem; color: var(--muted); overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }}
  .bar-track {{ height: 8px; background: var(--stroke); border-radius: 99px; overflow: hidden; }}
  .bar-fill {{ height: 100%; background: var(--accent); }}
  .bar-n {{ text-align: right; font-variant-numeric: tabular-nums; color: var(--muted); font-size: 0.85rem; }}
  table {{ width: 100%; border-collapse: collapse; font-size: 0.92rem; }}
  th, td {{ text-align: left; padding: 8px 6px; border-bottom: 1px solid var(--stroke); vertical-align: top; }}
  th {{ color: var(--muted); font-weight: 600; }}
  .clip {{ max-width: 220px; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }}
  .filters {{
    display: grid;
    grid-template-columns: repeat(4, minmax(0, 1fr));
    gap: 8px;
    margin: 10px 0;
  }}
  @media (max-width: 800px) {{
    .filters {{ grid-template-columns: 1fr 1fr; }}
  }}
  select, input[type="search"] {{
    width: 100%;
    padding: 8px 10px;
    border-radius: 8px;
    border: 1px solid var(--stroke);
    background: var(--bg);
    color: var(--fg);
  }}
  details.opcode {{
    border: 1px solid var(--stroke);
    border-radius: 8px;
    margin: 6px 0;
    background: var(--card);
  }}
  details.opcode > summary {{
    list-style: none;
    cursor: pointer;
    display: flex;
    justify-content: space-between;
    gap: 12px;
    align-items: center;
    padding: 10px 12px;
  }}
  details.opcode > summary::-webkit-details-marker {{ display: none; }}
  .sum-title {{ font-weight: 600; }}
  .sum-badges {{ display: flex; gap: 6px; flex-wrap: wrap; justify-content: flex-end; }}
  .detail {{ padding: 0 12px 12px; border-top: 1px solid var(--stroke); }}
  .detail .links a {{ margin-right: 4px; }}
  .meta {{ color: var(--muted); font-size: 0.9rem; }}
  .hidden {{ display: none !important; }}
</style>
</head>
<body>
<main>
  <h1>SpecRef ↔ Evm proof coverage</h1>
  <p class="muted">
    Generated snapshot from the living matrices (same data as the Cursor canvas).
    As of <code>{esc(as_of)}</code>.
  </p>
  <div class="banner">
    Source of truth:
    {ext_a(opcode_doc_href, "docs/opcode-coverage.md")} ·
    {ext_a(comparison_href, "docs/comparison-matrix.md")}.
    Live at {ext_a(SITE_URL, esc(SITE_URL))}.
    Refresh canvas + this page with <code>python3 scripts/refresh-proof-coverage-canvas.py</code>, then push on <code>main</code> to publish.
  </div>

  <div class="stats">
    <div class="stat"><div class="v">{esc(counts.get("full", 0))}</div><div class="l">Opcodes full (of {esc(counts.get("total", 90))} AST)</div></div>
    <div class="stat"><div class="v">{esc(counts.get("unstated", 0))}</div><div class="l">Opcodes unstated</div></div>
    <div class="stat"><div class="v">{esc(counts.get("n/a", 0))}</div><div class="l">Opcodes n/a this tranche</div></div>
    <div class="stat"><div class="v">{esc(unrelated)}</div><div class="l">State components unrelated</div></div>
  </div>

  <div class="card">
    <h2 style="margin-top:0">What opcode statuses mean</h2>
    {glossary_html}
    <p class="links">{ext_a(legend_href, "Legend in docs")} ·
    {ext_a(repo_href(outcome['relationFile'], outcome.get('stepResultRelLine')), "StepResultRel")}</p>
  </div>

  <div class="card">
    <h2 style="margin-top:0">Opcode rows by family</h2>
    <p class="muted">{esc(len(opcodes))} coverage rows (PUSH/DUP/SWAP/LOG collapsed) · {esc(counts.get("total", "?"))} AST constructors</p>
    {family_bars}
  </div>

  <div class="card">
    <h2 style="margin-top:0">Suggested next vertical slice</h2>
    <p>{slice_blurb}</p>
    <table>
      <thead><tr><th>Opcode</th><th>Byte</th><th>SpecRef</th><th>Evm</th><th>Shape</th><th>Status</th></tr></thead>
      <tbody>{slice_html}</tbody>
    </table>
  </div>

  <h2>Opcode coverage</h2>
  <p class="muted">Expand a row for status meaning, outcomes, and links into theorem / relation files.</p>
  <div class="filters">
    <select id="f-status"><option value="all">All statuses</option></select>
    <select id="f-family"><option value="all">All families</option></select>
    <select id="f-shape"><option value="all">All shapes</option></select>
    <input id="f-q" type="search" placeholder="Filter opcode / handler / theorem…" />
  </div>
  <div id="opcodes">
    {''.join(opcode_details)}
  </div>

  <h2>Comparison matrix (state components)</h2>
  <p class="muted">Statuses: unrelated · related · proven-scope · n/a.</p>
  <div class="card" style="overflow:auto">
    <table>
      <thead><tr><th>Component</th><th>Section</th><th>Relation</th><th>SpecRef</th><th>Evm</th><th>Status</th></tr></thead>
      <tbody>{component_rows}</tbody>
    </table>
  </div>
</main>
<script>
(() => {{
  const statusSel = document.getElementById("f-status");
  const familySel = document.getElementById("f-family");
  const shapeSel = document.getElementById("f-shape");
  const qInput = document.getElementById("f-q");
  const items = [...document.querySelectorAll("details.opcode")];

  function fill(sel, values) {{
    [...new Set(values)].sort().forEach((v) => {{
      const opt = document.createElement("option");
      opt.value = v; opt.textContent = v;
      sel.appendChild(opt);
    }});
  }}
  fill(statusSel, items.map((el) => el.dataset.status));
  fill(familySel, items.map((el) => el.dataset.family));
  fill(shapeSel, items.map((el) => el.dataset.shape));

  function apply() {{
    const st = statusSel.value;
    const fam = familySel.value;
    const sh = shapeSel.value;
    const q = qInput.value.trim().toLowerCase();
    items.forEach((el) => {{
      const ok =
        (st === "all" || el.dataset.status === st) &&
        (fam === "all" || el.dataset.family === fam) &&
        (sh === "all" || el.dataset.shape === sh) &&
        (!q || (el.dataset.search || "").includes(q));
      el.classList.toggle("hidden", !ok);
    }});
  }}
  [statusSel, familySel, shapeSel, qInput].forEach((el) => el.addEventListener("input", apply));
}})();
</script>
</body>
</html>
"""


def write_html(data: dict) -> None:
    HTML_OUT.parent.mkdir(parents=True, exist_ok=True)
    HTML_OUT.write_text(render_html(data))


def main() -> int:
    data = load_data()
    write_html(data)
    with_proof = sum(1 for o in data["opcodes"] if "proof" in o)
    print(
        f"wrote {HTML_OUT.relative_to(REPO)}: "
        f"{len(data['opcodes'])} opcode rows ({with_proof} with proof metadata), "
        f"{len(data['components'])} components, asOf={data['source']['asOf']}"
    )

    if CANVAS.exists():
        CANVAS.write_text(replace_data_blob(CANVAS.read_text(), data))
        print(f"refreshed canvas DATA in {CANVAS.name}")
    else:
        print(
            f"note: canvas not found at {CANVAS} — skipped canvas refresh",
            file=sys.stderr,
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
