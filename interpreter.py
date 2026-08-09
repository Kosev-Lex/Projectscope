#!/usr/bin/env python3
# interpreter.py
# focus_lineages
#
# This interpreter program is a partner analytical app meant to work with the output from projectscope.py.
# NYKG stands for Nyreth Knowledge Graph. This prototype system was created to turn my codebase into a KG, and
# make relationships explicit and navigable.
#
# This program was built to try to manage the many complex modules
# used in Nyreth. It was created on 16 Feb 2026. JL Kosev-Lex.
#
# GUI for nykg.focus_lineages.v1 logs.
# - Open a focus_lineages_*.json
# - Filter chains (only-cross, min len, min crossings, contains, module contains)
# - Inspect chain details
# - Export filtered chains to JSON/CSV
#
# Pure PyQt6. No web. No messagebox.

from __future__ import annotations

import json
import os
import re
import sys
from dataclasses import dataclass
from typing import Any, Dict, List, Optional, Tuple

from PyQt6.QtCore import Qt
from PyQt6.QtGui import QFont
from PyQt6.QtWidgets import (
    QApplication, QMainWindow, QWidget, QVBoxLayout, QHBoxLayout,
    QPushButton, QLabel, QFileDialog, QLineEdit, QTextEdit,
    QCheckBox, QSpinBox, QTabWidget, QTableWidget, QTableWidgetItem,
    QHeaderView, QSplitter, QComboBox
)
import time  # <-- add near your other imports if not already present

def now_iso() -> str:
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())


def try_int(v: Any, default: int = 0) -> int:
    try:
        return int(v)
    except Exception:
        return default


def safe_str(v: Any) -> str:
    return "" if v is None else str(v)


def load_json(path: str) -> Any:
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)


def save_json(path: str, payload: Any) -> None:
    with open(path, "w", encoding="utf-8") as f:
        json.dump(payload, f, indent=2)


def save_csv(path: str, rows: List[Dict[str, Any]], headers: List[str]) -> None:
    # minimal csv writer (no external deps)
    def esc(x: Any) -> str:
        s = safe_str(x).replace("\r", " ").replace("\n", " ").strip()
        if any(c in s for c in [",", '"']):
            s = '"' + s.replace('"', '""') + '"'
        return s

    with open(path, "w", encoding="utf-8") as f:
        f.write(",".join(headers) + "\n")
        for r in rows:
            f.write(",".join(esc(r.get(h, "")) for h in headers) + "\n")


@dataclass
class ChainRow:
    idx: int
    score: float
    length: int
    cross: int
    hubs: int
    deg_sum: int
    modules: str
    start: str
    end: str
    chain_text: str
    raw: Dict[str, Any]


def _extract_steps(chain: Dict[str, Any]) -> List[Dict[str, str]]:
    ids = chain.get("path_ids") if isinstance(chain.get("path_ids"), list) else []
    labels = chain.get("path_labels") if isinstance(chain.get("path_labels"), list) else []
    mods = chain.get("modules") if isinstance(chain.get("modules"), list) else []

    out: List[Dict[str, str]] = []
    n = max(len(ids), len(labels), len(mods))
    for i in range(n):
        out.append({
            "id": safe_str(ids[i]) if i < len(ids) else "",
            "label": safe_str(labels[i]) if i < len(labels) else "",
            "module": safe_str(mods[i]) if i < len(mods) else "",
        })
    return out


def _pretty_chain(steps: List[Dict[str, str]]) -> str:
    parts = []
    for s in steps:
        lab = s.get("label") or s.get("id") or ""
        parts.append(lab)
    return "  ->  ".join([p for p in parts if p])


def _compute_modules(steps: List[Dict[str, str]]) -> List[str]:
    mods = []
    for s in steps:
        m = (s.get("module") or "").strip()
        if m and (not mods or mods[-1] != m):
            mods.append(m)
    return mods


def normalize_focus_lineages(payload: Any) -> Tuple[Dict[str, Any], List[ChainRow]]:
    """
    Supports nykg.focus_lineages.v1:
      payload keys:
        - schema, saved_at, build, root
        - params, stats, module_sizes, hub_nodes
        - chains: [{path_ids,path_labels,modules,crossings,hub_hits,deg_sum,start}, ...]
    """
    meta: Dict[str, Any] = {}
    chains: List[Dict[str, Any]] = []

    if isinstance(payload, dict):
        schema = payload.get("schema") or ""
        saved_at = payload.get("saved_at") or ""
        build = payload.get("build") or ""
        root = payload.get("root") or ""

        params = payload.get("params") if isinstance(payload.get("params"), dict) else {}
        stats = payload.get("stats") if isinstance(payload.get("stats"), dict) else {}

        headline = {
            "chains_kept": try_int(stats.get("chains_kept"), 0),
            "cross_module_edges": try_int(stats.get("cross_module_edges"), 0),
            "nodes": try_int(stats.get("nodes"), 0),
            "edges": try_int(stats.get("edges"), 0),
            "functions_methods": try_int(stats.get("functions_methods"), 0),
            "calls_total": try_int(stats.get("calls_total"), 0),
            "hubs_n": try_int(stats.get("hubs_n"), 0),
            "chains_considered": try_int(stats.get("chains_considered"), 0),
        }

        meta = {
            "schema": schema,
            "saved_at": saved_at,
            "build": build,
            "root": root,
            "params": params,
            "stats": stats,
            "headline": headline,
            "module_sizes": payload.get("module_sizes") if isinstance(payload.get("module_sizes"), list) else [],
            "hub_nodes": payload.get("hub_nodes") if isinstance(payload.get("hub_nodes"), list) else [],
        }

        v = payload.get("chains")
        if isinstance(v, list):
            chains = [c for c in v if isinstance(c, dict)]
        else:
            chains = []
    elif isinstance(payload, list):
        chains = [c for c in payload if isinstance(c, dict)]
        meta = {"schema": "", "saved_at": "", "build": "", "root": "", "params": {}, "stats": {}, "headline": {}}

    rows: List[ChainRow] = []
    for i, raw in enumerate(chains):
        steps = _extract_steps(raw)
        length = len([s for s in steps if (s.get("id") or s.get("label"))])

        mods = _compute_modules(steps)
        crossings = try_int(raw.get("crossings"), max(0, len(mods) - 1))
        hub_hits = try_int(raw.get("hub_hits"), 0)
        deg_sum = try_int(raw.get("deg_sum"), 0)

        # prefer deg_sum if present (>0), else heuristic
        score = float(deg_sum) if deg_sum > 0 else float(length + crossings * 10 + hub_hits * 2)

        chain_text = raw.get("chain_text")
        if not isinstance(chain_text, str) or not chain_text.strip():
            chain_text = _pretty_chain(steps)

        start_label = ""
        end_label = ""
        if steps:
            start_label = (steps[0].get("label") or steps[0].get("id") or "")
            end_label = (steps[-1].get("label") or steps[-1].get("id") or "")

        rows.append(ChainRow(
            idx=i,
            score=score,
            length=length,
            cross=crossings,
            hubs=hub_hits,
            deg_sum=deg_sum,
            modules=" | ".join(mods),
            start=start_label,
            end=end_label,
            chain_text=chain_text,
            raw=raw
        ))

    return meta, rows


class FocusLineagesGUI(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("Focus Lineages — GUI")
        self.resize(1700, 980)

        self.file_path: Optional[str] = None
        self.meta: Dict[str, Any] = {}
        self.rows_all: List[ChainRow] = []
        self.rows_view: List[ChainRow] = []

        root = QWidget()
        outer = QVBoxLayout(root)

        # --- top bar ---
        top = QHBoxLayout()
        btn_open = QPushButton("Open…")
        btn_open.clicked.connect(self.on_open)
        top.addWidget(btn_open)

        self.lbl_file = QLabel("No file loaded.")
        self.lbl_file.setTextInteractionFlags(Qt.TextInteractionFlag.TextSelectableByMouse)
        top.addWidget(self.lbl_file, stretch=1)

        btn_export_json = QPushButton("Export JSON…")
        btn_export_json.clicked.connect(self.on_export_json)
        top.addWidget(btn_export_json)

        btn_export_csv = QPushButton("Export CSV…")
        btn_export_csv.clicked.connect(self.on_export_csv)
        top.addWidget(btn_export_csv)

        outer.addLayout(top)

        # --- header summary ---
        self.lbl_header = QLabel("")
        self.lbl_header.setTextInteractionFlags(Qt.TextInteractionFlag.TextSelectableByMouse)
        f = QFont()
        f.setPointSize(10)
        self.lbl_header.setFont(f)
        outer.addWidget(self.lbl_header)

        # --- tabs ---
        self.tabs = QTabWidget()
        outer.addWidget(self.tabs, stretch=1)

        # ===== Chains tab =====
        chains_tab = QWidget()
        chains_layout = QVBoxLayout(chains_tab)

        filters = QHBoxLayout()

        self.chk_only_cross = QCheckBox("Only cross-module (crossings>0)")
        self.chk_only_cross.stateChanged.connect(self.apply_filters)
        filters.addWidget(self.chk_only_cross)

        filters.addWidget(QLabel("Min len:"))
        self.spin_min_len = QSpinBox()
        self.spin_min_len.setRange(0, 50)
        self.spin_min_len.setValue(2)
        self.spin_min_len.valueChanged.connect(self.apply_filters)
        filters.addWidget(self.spin_min_len)

        filters.addWidget(QLabel("Min crossings:"))
        self.spin_min_cross = QSpinBox()
        self.spin_min_cross.setRange(0, 50)
        self.spin_min_cross.setValue(0)
        self.spin_min_cross.valueChanged.connect(self.apply_filters)
        filters.addWidget(self.spin_min_cross)

        filters.addWidget(QLabel("Contains:"))
        self.txt_contains = QLineEdit()
        self.txt_contains.setPlaceholderText("substring in chain/start/end/modules")
        self.txt_contains.textChanged.connect(self.apply_filters)
        filters.addWidget(self.txt_contains, stretch=1)

        filters.addWidget(QLabel("Module contains:"))
        self.txt_mod_contains = QLineEdit()
        self.txt_mod_contains.setPlaceholderText("e.g. registry")
        self.txt_mod_contains.textChanged.connect(self.apply_filters)
        filters.addWidget(self.txt_mod_contains, stretch=1)

        filters.addWidget(QLabel("Sort:"))
        self.cmb_sort = QComboBox()
        self.cmb_sort.addItems(["score desc", "len desc", "cross desc", "hubs desc", "deg_sum desc"])
        self.cmb_sort.currentTextChanged.connect(self.apply_filters)
        filters.addWidget(self.cmb_sort)

        chains_layout.addLayout(filters)

        splitter = QSplitter()
        chains_layout.addWidget(splitter, stretch=1)

        self.tbl_chains = QTableWidget(0, 9)
        self.tbl_chains.setHorizontalHeaderLabels([
            "idx", "score", "len", "cross", "hubs", "deg_sum", "modules", "start", "end"
        ])
        self.tbl_chains.setSelectionBehavior(QTableWidget.SelectionBehavior.SelectRows)
        self.tbl_chains.setSelectionMode(QTableWidget.SelectionMode.SingleSelection)
        self.tbl_chains.itemSelectionChanged.connect(self.on_chain_selected)
        self.tbl_chains.horizontalHeader().setSectionResizeMode(QHeaderView.ResizeMode.Interactive)
        self.tbl_chains.horizontalHeader().setStretchLastSection(True)
        splitter.addWidget(self.tbl_chains)

        self.txt_details = QTextEdit()
        self.txt_details.setReadOnly(True)
        splitter.addWidget(self.txt_details)
        splitter.setSizes([1050, 650])

        self.tabs.addTab(chains_tab, "Chains")

        # ===== Hubs tab =====
        hubs_tab = QWidget()
        hubs_layout = QVBoxLayout(hubs_tab)

        self.tbl_hubs = QTableWidget(0, 6)
        self.tbl_hubs.setHorizontalHeaderLabels(["degree", "in", "out", "module", "label", "id"])
        self.tbl_hubs.setSelectionBehavior(QTableWidget.SelectionBehavior.SelectRows)
        self.tbl_hubs.setSelectionMode(QTableWidget.SelectionMode.SingleSelection)
        self.tbl_hubs.horizontalHeader().setSectionResizeMode(QHeaderView.ResizeMode.Interactive)
        self.tbl_hubs.horizontalHeader().setStretchLastSection(True)
        hubs_layout.addWidget(self.tbl_hubs, stretch=1)

        self.tabs.addTab(hubs_tab, "Hubs")

        # ===== Modules tab =====
        mods_tab = QWidget()
        mods_layout = QVBoxLayout(mods_tab)

        self.tbl_mods = QTableWidget(0, 3)
        self.tbl_mods.setHorizontalHeaderLabels(["lines", "module", "file_path"])
        self.tbl_mods.setSelectionBehavior(QTableWidget.SelectionBehavior.SelectRows)
        self.tbl_mods.setSelectionMode(QTableWidget.SelectionMode.SingleSelection)
        self.tbl_mods.horizontalHeader().setSectionResizeMode(QHeaderView.ResizeMode.Interactive)
        self.tbl_mods.horizontalHeader().setStretchLastSection(True)
        mods_layout.addWidget(self.tbl_mods, stretch=1)

        self.tabs.addTab(mods_tab, "Modules")

        self.setCentralWidget(root)

        # initial empty view
        self._render_header()

    def _render_header(self) -> None:
        schema = safe_str(self.meta.get("schema"))
        saved_at = safe_str(self.meta.get("saved_at"))
        build = safe_str(self.meta.get("build"))
        root = safe_str(self.meta.get("root"))
        hl = self.meta.get("headline") if isinstance(self.meta.get("headline"), dict) else {}

        lines = []
        if self.file_path:
            lines.append(f"File: {self.file_path}")
        if schema:
            lines.append(f"schema: {schema}")
        if saved_at:
            lines.append(f"saved_at: {saved_at}")
        if build:
            lines.append(f"build: {build}")
        if root:
            lines.append(f"root: {root}")

        if hl:
            lines.append(
                f"chains_kept: {try_int(hl.get('chains_kept'))} | "
                f"cross_module_edges: {try_int(hl.get('cross_module_edges'))} | "
                f"nodes: {try_int(hl.get('nodes'))} | edges: {try_int(hl.get('edges'))} | "
                f"calls_total: {try_int(hl.get('calls_total'))} | hubs_n: {try_int(hl.get('hubs_n'))}"
            )

        self.lbl_header.setText("\n".join(lines) if lines else "")

    def on_open(self) -> None:
        path, _ = QFileDialog.getOpenFileName(self, "Open focus_lineages JSON", "", "JSON (*.json)")
        if not path:
            return
        self.load_file(path)

    def load_file(self, path: str) -> None:
        self.file_path = path
        self.lbl_file.setText(path)

        try:
            payload = load_json(path)
        except Exception as e:
            self.meta = {}
            self.rows_all = []
            self.rows_view = []
            self._render_header()
            self.tbl_chains.setRowCount(0)
            self.txt_details.setPlainText(f"Failed to load JSON:\n{e}")
            return

        self.meta, self.rows_all = normalize_focus_lineages(payload)
        self.rows_view = list(self.rows_all)

        self._render_header()
        self.populate_hubs()
        self.populate_modules()
        self.apply_filters()

    def apply_filters(self) -> None:
        # If nothing loaded yet, keep UI sane.
        if not self.rows_all:
            self.rows_view = []
            self.populate_chains()
            return

        rows = list(self.rows_all)

        only_cross = self.chk_only_cross.isChecked()
        min_len = int(self.spin_min_len.value())
        min_cross = int(self.spin_min_cross.value())
        contains = (self.txt_contains.text() or "").strip().lower()
        mod_contains = (self.txt_mod_contains.text() or "").strip().lower()

        def match(r: ChainRow) -> bool:
            if only_cross and r.cross <= 0:
                return False
            if r.length < min_len:
                return False
            if r.cross < min_cross:
                return False
            if mod_contains and mod_contains not in (r.modules or "").lower():
                return False
            if contains:
                blob = " ".join([
                    safe_str(r.modules),
                    safe_str(r.start),
                    safe_str(r.end),
                    safe_str(r.chain_text),
                ]).lower()
                if contains not in blob:
                    return False
            return True

        rows = [r for r in rows if match(r)]

        # sort
        mode = self.cmb_sort.currentText() or "score desc"
        if mode.startswith("score"):
            rows.sort(key=lambda r: (r.score, r.cross, r.length, r.deg_sum), reverse=True)
        elif mode.startswith("len"):
            rows.sort(key=lambda r: (r.length, r.cross, r.score, r.deg_sum), reverse=True)
        elif mode.startswith("cross"):
            rows.sort(key=lambda r: (r.cross, r.length, r.score, r.deg_sum), reverse=True)
        elif mode.startswith("hubs"):
            rows.sort(key=lambda r: (r.hubs, r.cross, r.length, r.score), reverse=True)
        else:  # deg_sum
            rows.sort(key=lambda r: (r.deg_sum, r.cross, r.length, r.score), reverse=True)

        self.rows_view = rows
        self.populate_chains()

        # optional: keep header informative (no extra UI widgets required)
        # Shows "visible/total" at end of header label
        try:
            base = self.lbl_header.text().split("\n")
            base = [ln for ln in base if not ln.startswith("visible: ")]
            base.append(f"visible: {len(self.rows_view)} / {len(self.rows_all)}")
            self.lbl_header.setText("\n".join(base))
        except Exception:
            pass

    def populate_chains(self) -> None:
        self.tbl_chains.setRowCount(0)
        self.tbl_chains.setRowCount(len(self.rows_view))

        for i, r in enumerate(self.rows_view):
            vals = [
                r.idx,
                f"{r.score:.1f}",
                r.length,
                r.cross,
                r.hubs,
                r.deg_sum,
                r.modules,
                r.start,
                r.end,
            ]
            for c, v in enumerate(vals):
                it = QTableWidgetItem(safe_str(v))
                it.setFlags(it.flags() ^ Qt.ItemFlag.ItemIsEditable)
                self.tbl_chains.setItem(i, c, it)

        self.tbl_chains.resizeColumnsToContents()
        if self.rows_view:
            self.tbl_chains.selectRow(0)
        else:
            self.txt_details.setPlainText("(no chains match filters)")

    def on_chain_selected(self) -> None:
        sel = self.tbl_chains.selectedItems()
        if not sel:
            return
        row = sel[0].row()
        if row < 0 or row >= len(self.rows_view):
            return
        r = self.rows_view[row]

        raw = r.raw or {}
        steps = _extract_steps(raw)
        pretty = r.chain_text or _pretty_chain(steps)

        lines = []
        lines.append(f"idx: {r.idx}")
        lines.append(f"score: {r.score:.1f} | len: {r.length} | crossings: {r.cross} | hub_hits: {r.hubs} | deg_sum: {r.deg_sum}")
        if r.modules:
            lines.append(f"modules: {r.modules}")
        lines.append("")
        lines.append("chain:")
        lines.append(pretty)
        lines.append("")
        lines.append("raw:")
        lines.append(json.dumps(raw, indent=2))

        self.txt_details.setPlainText("\n".join(lines))

    def populate_hubs(self) -> None:
        hubs = self.meta.get("hub_nodes") if isinstance(self.meta.get("hub_nodes"), list) else []
        hubs = [h for h in hubs if isinstance(h, dict)]
        hubs.sort(key=lambda h: try_int(h.get("degree"), 0), reverse=True)

        self.tbl_hubs.setRowCount(0)
        self.tbl_hubs.setRowCount(len(hubs))

        for i, h in enumerate(hubs):
            vals = [
                try_int(h.get("degree"), 0),
                try_int(h.get("in"), 0),
                try_int(h.get("out"), 0),
                safe_str(h.get("module")),
                safe_str(h.get("label")),
                safe_str(h.get("id")),
            ]
            for c, v in enumerate(vals):
                it = QTableWidgetItem(safe_str(v))
                it.setFlags(it.flags() ^ Qt.ItemFlag.ItemIsEditable)
                self.tbl_hubs.setItem(i, c, it)

        self.tbl_hubs.resizeColumnsToContents()

    def populate_modules(self) -> None:
        mods = self.meta.get("module_sizes") if isinstance(self.meta.get("module_sizes"), list) else []
        mods = [m for m in mods if isinstance(m, dict)]
        mods.sort(key=lambda m: try_int(m.get("lines"), 0), reverse=True)

        self.tbl_mods.setRowCount(0)
        self.tbl_mods.setRowCount(len(mods))

        for i, m in enumerate(mods):
            vals = [
                try_int(m.get("lines"), 0),
                safe_str(m.get("module")),
                safe_str(m.get("file_path")),
            ]
            for c, v in enumerate(vals):
                it = QTableWidgetItem(safe_str(v))
                it.setFlags(it.flags() ^ Qt.ItemFlag.ItemIsEditable)
                self.tbl_mods.setItem(i, c, it)

        self.tbl_mods.resizeColumnsToContents()

    def _active_tab_name(self) -> str:
        """Returns the current tab label (e.g., 'Chains', 'Hubs', 'Modules')."""
        i = int(self.tabs.currentIndex())
        return safe_str(self.tabs.tabText(i))

    def _export_tablewidget_to_csv(self, table: QTableWidget, out_path: str) -> None:
        """
        Export EXACTLY what is visible in the table (current rows/cols),
        with the current header labels.
        """
        headers: List[str] = []
        for c in range(table.columnCount()):
            h = table.horizontalHeaderItem(c)
            headers.append(h.text() if h else f"col_{c}")

        rows: List[Dict[str, Any]] = []
        for r in range(table.rowCount()):
            rec: Dict[str, Any] = {}
            for c in range(table.columnCount()):
                it = table.item(r, c)
                rec[headers[c]] = it.text() if it else ""
            rows.append(rec)

        save_csv(out_path, rows, headers)

    def on_export_csv(self) -> None:
        """
        Export by tab, saving only what's currently shown in the UI.

        - Chains: exports filtered/sorted rows_view (the chains table).
        - Hubs: exports the hubs table.
        - Modules: exports the modules table.
        """
        tab = self._active_tab_name().lower()

        # sensible default filename per tab
        default_name = "export.csv"
        if "chain" in tab:
            default_name = "chains_filtered.csv"
        elif "hub" in tab:
            default_name = "hubs.csv"
        elif "module" in tab:
            default_name = "modules.csv"

        out, _ = QFileDialog.getSaveFileName(
            self,
            f"Export {self._active_tab_name()} to CSV",
            default_name,
            "CSV (*.csv)"
        )
        if not out:
            return

        try:
            # ===== CHAINS TAB: export rows_view (what chains table is showing) =====
            if "chain" in tab:
                # Export the CURRENT VIEW (self.rows_view), not the full raw objects.
                rows: List[Dict[str, Any]] = []
                for r in self.rows_view:
                    rows.append({
                        "idx": r.idx,
                        "score": f"{r.score:.1f}",
                        "len": r.length,
                        "cross": r.cross,
                        "hubs": r.hubs,
                        "deg_sum": r.deg_sum,
                        "modules": r.modules,
                        "start": r.start,
                        "end": r.end,
                        "chain": r.chain_text,
                        # keep minimal linkage payload if you want it in CSV too:
                        "path_ids": " -> ".join(r.path_ids or []),
                        "modules_seq": " -> ".join(r.modules_seq or []),
                    })

                headers = [
                    "idx", "score", "len", "cross", "hubs", "deg_sum",
                    "modules", "start", "end", "chain", "path_ids", "modules_seq"
                ]
                save_csv(out, rows, headers)
                self.txt_details.setPlainText(f"Exported Chains CSV:\n{out}\nrows={len(rows)}")
                return

            # ===== HUBS TAB: export exactly what’s shown in tbl_hubs =====
            if "hub" in tab:
                self._export_tablewidget_to_csv(self.tbl_hubs, out)
                self.txt_details.setPlainText(f"Exported Hubs CSV:\n{out}\nrows={self.tbl_hubs.rowCount()}")
                return

            # ===== MODULES TAB: export exactly what’s shown in tbl_mods =====
            if "module" in tab:
                self._export_tablewidget_to_csv(self.tbl_mods, out)
                self.txt_details.setPlainText(f"Exported Modules CSV:\n{out}\nrows={self.tbl_mods.rowCount()}")
                return

            # fallback: export the currently visible table, if you add future tabs
            self._export_tablewidget_to_csv(self.tbl_chains, out)
            self.txt_details.setPlainText(f"Exported CSV:\n{out}\nrows={self.tbl_chains.rowCount()}")

        except Exception as e:
            self.txt_details.setPlainText(f"Export CSV failed:\n{e}")

    def on_export_json(self) -> None:
        """
        Export by tab, minimal + what-you-see.

        - Chains: exports minimal linkage objects (score + path_ids + modules_seq).
        - Hubs/Modules: exports visible table rows as simple dicts.
        """
        tab = self._active_tab_name().lower()

        default_name = "export.json"
        if "chain" in tab:
            default_name = "chains_filtered_min.json"
        elif "hub" in tab:
            default_name = "hubs.json"
        elif "module" in tab:
            default_name = "modules.json"

        out, _ = QFileDialog.getSaveFileName(
            self,
            f"Export {self._active_tab_name()} to JSON",
            default_name,
            "JSON (*.json)"
        )
        if not out:
            return

        try:
            if "chain" in tab:
                # minimal: what you said you actually want
                chains = []
                for r in self.rows_view:
                    chains.append({
                        "score": int(round(r.score)),
                        "path_ids": list(r.path_ids or []),
                        "modules": list(r.modules_seq or []),
                    })

                payload = {
                    "schema": "nykg.focus_lineages.filtered_min.v1",
                    "saved_at": now_iso(),
                    "source_file": self.file_path,
                    "tab": "Chains",
                    "filters": {
                        "only_cross": self.chk_only_cross.isChecked(),
                        "min_len": int(self.spin_min_len.value()),
                        "min_cross": int(self.spin_min_cross.value()),
                        "contains": (self.txt_contains.text() or "").strip(),
                        "module_contains": (self.txt_mod_contains.text() or "").strip(),
                        "sort": self.cmb_sort.currentText(),
                    },
                    "count": len(chains),
                    "chains": chains,
                }
                save_json(out, payload)
                self.txt_details.setPlainText(f"Exported Chains JSON:\n{out}\ncount={len(chains)}")
                return

            def table_to_rows(table: QTableWidget) -> List[Dict[str, Any]]:
                headers = []
                for c in range(table.columnCount()):
                    h = table.horizontalHeaderItem(c)
                    headers.append(h.text() if h else f"col_{c}")
                rows = []
                for r in range(table.rowCount()):
                    rec = {}
                    for c in range(table.columnCount()):
                        it = table.item(r, c)
                        rec[headers[c]] = it.text() if it else ""
                    rows.append(rec)
                return rows

            if "hub" in tab:
                payload = {
                    "schema": "nykg.focus_lineages.hubs.view.v1",
                    "saved_at": now_iso(),
                    "source_file": self.file_path,
                    "tab": "Hubs",
                    "count": int(self.tbl_hubs.rowCount()),
                    "rows": table_to_rows(self.tbl_hubs),
                }
                save_json(out, payload)
                self.txt_details.setPlainText(f"Exported Hubs JSON:\n{out}\ncount={payload['count']}")
                return

            if "module" in tab:
                payload = {
                    "schema": "nykg.focus_lineages.modules.view.v1",
                    "saved_at": now_iso(),
                    "source_file": self.file_path,
                    "tab": "Modules",
                    "count": int(self.tbl_mods.rowCount()),
                    "rows": table_to_rows(self.tbl_mods),
                }
                save_json(out, payload)
                self.txt_details.setPlainText(f"Exported Modules JSON:\n{out}\ncount={payload['count']}")
                return

            self.txt_details.setPlainText("Export JSON: unknown tab.")

        except Exception as e:
            self.txt_details.setPlainText(f"Export JSON failed:\n{e}")



def main() -> None:
    app = QApplication(sys.argv)
    w = FocusLineagesGUI()
    w.show()

    # Convenience: allow drag/drop file path via argv
    if len(sys.argv) >= 2 and os.path.exists(sys.argv[1]) and sys.argv[1].lower().endswith(".json"):
        w.load_file(sys.argv[1])

    sys.exit(app.exec())


if __name__ == "__main__":
    main()
