#!/usr/bin/env python3
#
# projectscope.py
# nykg_hardreset
#
# NYKG stands for Nyreth Knowledge Graph. This prototype system was created to turn my codebase into a KG, and
# make relationships explicit and navigable. This program was built to try to manage the many complex modules
# used in Nyreth. It was created on 16 Feb 2026. JL Kosev-Lex.
#
# Hard reset KG explorer:
# - Pure Qt (QGraphicsView/QGraphicsScene). NO WebEngine. NO Cytoscape. NO Flask. NO OpenAI. NO QMessageBox.
# - Always shows a rectangular grid layout (no "black dot" empty view).
# - Nodes + edges are selectable. Edge click shows caller->callee details.
# - Edge selections can be saved to JSON.
# - Layout + DB persist to per-project workspace anchored to script directory.
#
# B-mode lineage logging:
# - Logs ONLY:
#   (1) cross-module chains (any hop crosses module boundary), and
#   (2) within-module chains that include at least one hub node with degree >= K.
# - Depth-limited, fan-out limited, ranked, and bounded per-start.
# - Output is a manageable JSON file per run.

from __future__ import annotations

import argparse
import ast
import hashlib
import json
import os
import re
import sys
import time
from dataclasses import dataclass
from typing import Any, Dict, List, Optional, Tuple
from collections import defaultdict

from PyQt6.QtCore import Qt, QPointF, QRectF, pyqtSignal
from PyQt6.QtGui import QBrush, QColor, QFont, QPainter, QPen, QTransform
from PyQt6.QtWidgets import (
    QApplication, QMainWindow, QWidget, QVBoxLayout, QHBoxLayout,
    QPushButton, QLabel, QFileDialog, QLineEdit, QTextEdit, QSplitter,
    QCheckBox, QTreeWidget, QTreeWidgetItem, QAbstractItemView, QComboBox,
    QInputDialog, QGraphicsView, QGraphicsScene, QGraphicsItem,
    QGraphicsRectItem, QGraphicsTextItem, QGraphicsPathItem
)

# -----------------------------
# Build stamp (so you can prove you're running THIS file)
# -----------------------------
NYKG_BUILD = "NYKG HARD RESET BUILD 2026-02-17 (Qt scene, edge-select, grid-default, layout-persist, GROUPS+FOCUS-LOG)"

# -----------------------------
# Utility
# -----------------------------
def now_iso() -> str:
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())

def now_stamp() -> str:
    return time.strftime("%Y%m%d_%H%M%S", time.gmtime())

def sha256_bytes(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()

def norm_path(p: str) -> str:
    return os.path.normpath(p).replace("\\", "/")

def read_text(p: str) -> str:
    with open(p, "r", encoding="utf-8", errors="replace") as f:
        return f.read()

def read_bytes(p: str) -> bytes:
    with open(p, "rb") as f:
        return f.read()

def ensure_dir(p: str) -> None:
    os.makedirs(p, exist_ok=True)

def safe_name(name: str) -> str:
    name = (name or "").strip()
    name = re.sub(r"[^a-zA-Z0-9_\- ]+", "", name)
    name = re.sub(r"\s+", " ", name).strip()
    return name or "Project"

def try_count_lines(file_path: str) -> int:
    try:
        txt = read_text(file_path)
        return txt.count("\n") + (1 if txt else 0)
    except Exception:
        return 0

# -----------------------------
# Workspace anchoring (script dir)
# -----------------------------
APP_DIR = os.path.dirname(os.path.abspath(__file__))
WORKSPACES_DIR = norm_path(os.path.join(APP_DIR, "kg_workspaces"))

def workspace_dir(name: str) -> str:
    return norm_path(os.path.join(WORKSPACES_DIR, safe_name(name)))

def workspace_paths(name: str) -> Tuple[str, str, str]:
    wdir = workspace_dir(name)
    ensure_dir(wdir)
    db = norm_path(os.path.join(wdir, "kg_db.json"))
    layout = norm_path(os.path.join(wdir, "layout.json"))
    meta = norm_path(os.path.join(wdir, "meta.json"))
    return db, layout, meta

def list_workspaces() -> List[str]:
    if not os.path.isdir(WORKSPACES_DIR):
        return []
    out = []
    for n in os.listdir(WORKSPACES_DIR):
        p = os.path.join(WORKSPACES_DIR, n)
        if os.path.isdir(p) and os.path.exists(os.path.join(p, "kg_db.json")):
            out.append(n)
    out.sort(key=lambda s: s.lower())
    return out

def write_meta(meta_path: str, root: str) -> None:
    with open(meta_path, "w", encoding="utf-8") as f:
        json.dump({"root": norm_path(root), "saved_at": now_iso()}, f, indent=2)

def read_meta(meta_path: str) -> Dict[str, Any]:
    if not os.path.exists(meta_path):
        return {}
    try:
        with open(meta_path, "r", encoding="utf-8") as f:
            return json.load(f) or {}
    except Exception:
        return {}

# -----------------------------
# Graph Model
# -----------------------------
@dataclass
class Node:
    id: str
    type: str
    label: str
    meta: Dict[str, Any]

@dataclass
class Edge:
    id: str
    type: str
    src: str
    dst: str
    meta: Dict[str, Any]

def make_edge_id(etype: str, src: str, dst: str, extra: Optional[str] = None) -> str:
    base = f"{etype}|{src}|{dst}|{extra or ''}"
    return "e:" + sha256_bytes(base.encode("utf-8"))[:20]

def module_qualname(repo_root: str, file_path: str) -> str:
    rp = norm_path(os.path.relpath(file_path, repo_root))
    if rp.endswith(".py"):
        rp = rp[:-3]
    return rp.replace("/", ".")

def stable_symbol_id(modq: str, kind: str, name: str, arity: Optional[int] = None, cls: Optional[str] = None) -> str:
    if kind == "class":
        return f"sym:{modq}:class:{name}"
    if kind == "method":
        return f"sym:{modq}:class:{cls}:method:{name}:{arity if arity is not None else 'na'}"
    return f"sym:{modq}:func:{name}:{arity if arity is not None else 'na'}"

class GraphStore:
    def __init__(self, root: str):
        self.root = norm_path(root)
        self.nodes: Dict[str, Node] = {}
        self.edges: Dict[str, Edge] = {}
        self.owners: Dict[str, str] = {}  # node_or_edge_id -> owner module id

        # indexing for call resolution
        self.name_index_funcs: Dict[str, List[str]] = {}  # simple name -> [node_id]

    def rebuild_indexes(self) -> None:
        self.name_index_funcs.clear()
        for nid, n in self.nodes.items():
            if n.type in ("Function", "Method"):
                nm = (n.meta.get("name") or "").strip()
                if nm:
                    self.name_index_funcs.setdefault(nm, []).append(nid)

    def upsert_node(self, node: Node, owner_module_id: Optional[str] = None) -> None:
        self.nodes[node.id] = node
        if owner_module_id:
            self.owners[node.id] = owner_module_id

    def upsert_edge(self, edge: Edge, owner_module_id: Optional[str] = None) -> None:
        self.edges[edge.id] = edge
        if owner_module_id:
            self.owners[edge.id] = owner_module_id

    def remove_owner_module(self, module_id: str) -> None:
        # delete edges first
        for eid, owner in list(self.owners.items()):
            if owner == module_id and eid in self.edges:
                self.edges.pop(eid, None)
                self.owners.pop(eid, None)
        # delete nodes
        for nid, owner in list(self.owners.items()):
            if owner == module_id and nid in self.nodes:
                self.nodes.pop(nid, None)
                self.owners.pop(nid, None)
        # cleanup dangling edges
        for eid, e in list(self.edges.items()):
            if e.src not in self.nodes or e.dst not in self.nodes:
                self.edges.pop(eid, None)
                self.owners.pop(eid, None)
        self.rebuild_indexes()

    def save(self, path: str) -> None:
        payload = {
            "schema": "nykg.hardreset.v1",
            "saved_at": now_iso(),
            "root": self.root,
            "nodes": {nid: {"id": n.id, "type": n.type, "label": n.label, "meta": n.meta or {}} for nid, n in self.nodes.items()},
            "edges": {eid: {"id": e.id, "type": e.type, "src": e.src, "dst": e.dst, "meta": e.meta or {}} for eid, e in self.edges.items()},
            "owners": dict(self.owners),
        }
        with open(path, "w", encoding="utf-8") as f:
            json.dump(payload, f, indent=2)

    @staticmethod
    def load(path: str) -> "GraphStore":
        with open(path, "r", encoding="utf-8") as f:
            payload = json.load(f) or {}
        gs = GraphStore(payload.get("root") or os.getcwd())
        for nid, nd in (payload.get("nodes") or {}).items():
            gs.nodes[nid] = Node(id=nd["id"], type=nd["type"], label=nd["label"], meta=nd.get("meta") or {})
        for eid, ed in (payload.get("edges") or {}).items():
            gs.edges[eid] = Edge(id=ed["id"], type=ed["type"], src=ed["src"], dst=ed["dst"], meta=ed.get("meta") or {})
        gs.owners = payload.get("owners") or {}
        gs.rebuild_indexes()
        return gs

# -----------------------------
# Layout persistence (Qt-native)
# -----------------------------
def load_layout(path: str) -> Dict[str, Any]:
    if not path or not os.path.exists(path):
        return {"positions": {}, "view": {"tx": 0.0, "ty": 0.0, "scale": 1.0}}

    try:
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f) or {}
    except Exception:
        return {"positions": {}, "view": {"tx": 0.0, "ty": 0.0, "scale": 1.0}}

    positions = data.get("positions") or {}
    view = data.get("view") or {}
    # normalize
    pos_out: Dict[str, Dict[str, float]] = {}
    for nid, p in positions.items():
        if isinstance(p, dict) and "x" in p and "y" in p:
            try:
                pos_out[str(nid)] = {"x": float(p["x"]), "y": float(p["y"])}
            except Exception:
                pass
    v_out = {"tx": 0.0, "ty": 0.0, "scale": 1.0}
    try:
        v_out["tx"] = float(view.get("tx", 0.0))
        v_out["ty"] = float(view.get("ty", 0.0))
        v_out["scale"] = float(view.get("scale", 1.0))
    except Exception:
        pass
    return {"positions": pos_out, "view": v_out}

def save_layout(path: str, positions: Dict[str, Dict[str, float]], view: Dict[str, float]) -> None:
    if not path:
        return
    payload = {
        "schema": "nykg.hardreset.layout.v1",
        "saved_at": now_iso(),
        "positions": positions or {},
        "view": view or {"tx": 0.0, "ty": 0.0, "scale": 1.0},
    }
    with open(path, "w", encoding="utf-8") as f:
        json.dump(payload, f, indent=2)

# -----------------------------
# AST ingestion (simple but reliable)
# -----------------------------
def _call_text(fn: ast.AST) -> Tuple[str, str]:
    if isinstance(fn, ast.Name):
        return fn.id, "name"
    if isinstance(fn, ast.Attribute):
        parts = []
        cur = fn
        while isinstance(cur, ast.Attribute):
            parts.append(cur.attr)
            cur = cur.value
        if isinstance(cur, ast.Name):
            parts.append(cur.id)
        parts.reverse()
        return ".".join(parts), "attr"
    try:
        return ast.unparse(fn), "expr"
    except Exception:
        return fn.__class__.__name__, "expr"

class ModuleParseResult:
    def __init__(self) -> None:
        self.modq: str = ""
        self.file_path: str = ""
        self.file_hash: str = ""
        self.import_alias_map: Dict[str, str] = {}
        self.def_classes: List[Dict[str, Any]] = []
        self.def_funcs: List[Dict[str, Any]] = []
        self.calls: List[Dict[str, Any]] = []

class ModuleParser(ast.NodeVisitor):
    def __init__(self, repo_root: str, file_path: str):
        self.repo_root = norm_path(repo_root)
        self.file_path = norm_path(file_path)
        self.modq = module_qualname(self.repo_root, self.file_path)
        self.result = ModuleParseResult()
        self.result.modq = self.modq
        self.result.file_path = self.file_path
        self.current_class: Optional[str] = None
        self._func_stack: List[str] = []  # sym_id stack
        b = read_bytes(self.file_path)
        self.result.file_hash = sha256_bytes(b)
        self._src = read_text(self.file_path)

    def parse(self) -> ModuleParseResult:
        tree = ast.parse(self._src, filename=self.file_path)
        self.visit(tree)
        return self.result

    def visit_Import(self, node: ast.Import) -> Any:
        for alias in node.names:
            name = alias.name
            asname = alias.asname
            if asname:
                self.result.import_alias_map[asname] = name
            else:
                head = name.split(".")[0]
                self.result.import_alias_map[head] = head
        self.generic_visit(node)

    def visit_ImportFrom(self, node: ast.ImportFrom) -> Any:
        mod = node.module or ""
        for alias in node.names:
            name = alias.name
            asname = alias.asname
            local = asname or name
            self.result.import_alias_map[local] = f"{mod}.{name}" if mod else name
        self.generic_visit(node)

    def visit_ClassDef(self, node: ast.ClassDef) -> Any:
        cls_name = node.name
        cls_id = stable_symbol_id(self.modq, "class", cls_name)
        self.result.def_classes.append({
            "id": cls_id,
            "name": cls_name,
            "lineno": getattr(node, "lineno", None),
            "doc": ast.get_docstring(node) or "",
        })
        prev = self.current_class
        self.current_class = cls_name
        self.generic_visit(node)
        self.current_class = prev

    def visit_FunctionDef(self, node: ast.FunctionDef) -> Any:
        self._handle_function(node, is_async=False)

    def visit_AsyncFunctionDef(self, node: ast.AsyncFunctionDef) -> Any:
        self._handle_function(node, is_async=True)

    def _handle_function(self, node: Any, is_async: bool) -> None:
        fn_name = node.name
        args = node.args
        arity = len(getattr(args, "args", [])) + len(getattr(args, "kwonlyargs", []))
        if self.current_class:
            sym_id = stable_symbol_id(self.modq, "method", fn_name, arity=arity, cls=self.current_class)
            kind = "method"
            label = f"{self.modq}.{self.current_class}.{fn_name}"
        else:
            sym_id = stable_symbol_id(self.modq, "func", fn_name, arity=arity)
            kind = "function"
            label = f"{self.modq}.{fn_name}"

        self.result.def_funcs.append({
            "id": sym_id,
            "name": fn_name,
            "kind": kind,
            "class": self.current_class,
            "lineno": getattr(node, "lineno", None),
            "arity": arity,
            "args": [a.arg for a in getattr(args, "args", [])],
            "doc": ast.get_docstring(node) or "",
            "is_async": bool(is_async),
            "label": label,
        })

        self._func_stack.append(sym_id)
        self.generic_visit(node)
        self._func_stack.pop()

    def visit_Call(self, node: ast.Call) -> Any:
        if not self._func_stack:
            self.generic_visit(node)
            return
        caller = self._func_stack[-1]
        callee_text, callee_kind = _call_text(node.func)
        self.result.calls.append({
            "caller": caller,
            "callee_text": callee_text,
            "callee_kind": callee_kind,
            "lineno": getattr(node, "lineno", None),
            "argc": len(getattr(node, "args", []) or []),
        })
        self.generic_visit(node)

def resolve_callee(gs: GraphStore, caller_modq: str, callee_text: str, callee_kind: str, import_alias_map: Dict[str, str]) -> Tuple[str, float]:
    def best_candidate_by_name(name: str) -> Optional[str]:
        cands = gs.name_index_funcs.get(name) or []
        if not cands:
            return None
        # prefer same module if possible
        for nid in cands:
            if nid.startswith(f"sym:{caller_modq}:"):
                return nid
        return cands[0]

    if callee_kind == "name":
        nm = callee_text
        cand = best_candidate_by_name(nm)
        if cand:
            return cand, 0.70 if cand.startswith(f"sym:{caller_modq}:") else 0.35
        if nm in import_alias_map:
            tail = import_alias_map[nm].split(".")[-1]
            cand2 = best_candidate_by_name(tail)
            if cand2:
                return cand2, 0.30
        return f"unresolved:{caller_modq}:{nm}", 0.10

    if callee_kind == "attr":
        tail = callee_text.split(".")[-1]
        cand = best_candidate_by_name(tail)
        if cand:
            return cand, 0.25
        return f"unresolved:{caller_modq}:{callee_text}", 0.10

    return f"unresolved:{caller_modq}:{callee_text}", 0.05

def ingest_module(gs: GraphStore, file_path: str) -> str:
    file_path = norm_path(file_path)
    parser = ModuleParser(gs.root, file_path)
    res = parser.parse()

    modq = res.modq
    mod_id = f"module:{modq}"

    # Module node (owner = itself)
    gs.upsert_node(Node(
        id=mod_id,
        type="Module",
        label=modq,
        meta={"module": modq, "file_path": file_path, "file_hash": res.file_hash, "last_ingested": now_iso()}
    ), owner_module_id=mod_id)

    # Classes
    for c in res.def_classes:
        cid = c["id"]
        gs.upsert_node(Node(
            id=cid, type="Class", label=f"{modq}.{c['name']}",
            meta={"module": modq, "name": c["name"], "lineno": c.get("lineno"), "doc": c.get("doc") or ""}
        ), owner_module_id=mod_id)

    # Functions & Methods
    for fn in res.def_funcs:
        fid = fn["id"]
        ntype = "Method" if fn.get("kind") == "method" else "Function"
        gs.upsert_node(Node(
            id=fid, type=ntype, label=fn.get("label") or fid,
            meta={
                "module": modq,
                "name": fn["name"],
                "class": fn.get("class"),
                "lineno": fn.get("lineno"),
                "arity": fn.get("arity"),
                "args": fn.get("args") or [],
                "doc": fn.get("doc") or "",
                "is_async": bool(fn.get("is_async")),
            }
        ), owner_module_id=mod_id)

    gs.rebuild_indexes()

    # Calls edges
    for call in res.calls:
        caller = call["caller"]
        target_id, conf = resolve_callee(gs, modq, call["callee_text"], call["callee_kind"], res.import_alias_map)

        if target_id.startswith("unresolved:") and target_id not in gs.nodes:
            gs.upsert_node(Node(
                id=target_id, type="UnresolvedSymbol",
                label=call["callee_text"],
                meta={"module": modq, "callee_text": call["callee_text"]}
            ), owner_module_id=mod_id)

        gs.upsert_edge(Edge(
            id=make_edge_id("CALLS", caller, target_id, extra=f"{call.get('lineno')}|{call['callee_text']}"),
            type="CALLS",
            src=caller,
            dst=target_id,
            meta={
                "callee_text": call["callee_text"],
                "lineno": call.get("lineno"),
                "argc": call.get("argc"),
                "confidence": conf,
            }
        ), owner_module_id=mod_id)

    gs.rebuild_indexes()
    return mod_id

# -----------------------------
# Focus lineage logging (Option B)
# -----------------------------
def build_focus_lineage_log(
    gs: GraphStore,
    degree_k: int = 8,
    max_len: int = 5,
    max_out_per_node: int = 8,
    max_chains_per_start: int = 25,
    max_total_chains: int = 12000,
) -> Dict[str, Any]:
    """
    Produce a bounded, high-signal lineage log.

    Keeps:
      - Cross-module chains (any hop where module(src) != module(dst))
      - Within-module chains that include at least one hub node with degree >= degree_k

    Notes:
      - Chains are node-id sequences with derived module labels, crossings count, and a score.
      - Enumeration is depth-limited DFS with fan-out limit per node and per-start cap.
    """
    # identify function-like nodes
    fn_ids = [nid for nid, n in gs.nodes.items() if n.type in ("Function", "Method")]
    fn_set = set(fn_ids)

    def mod_of(nid: str) -> str:
        n = gs.nodes.get(nid)
        return (n.meta.get("module") if n else "") or ""

    # degree (in+out over CALLS, restricted to function-like nodes on each side when possible)
    indeg = defaultdict(int)
    outdeg = defaultdict(int)
    adj = defaultdict(list)  # src -> [dst]

    cross_edges = 0
    total_calls = 0

    for e in gs.edges.values():
        if e.type != "CALLS":
            continue
        total_calls += 1

        s = e.src
        t = e.dst

        # adjacency: allow unresolved too, but it will stop chains naturally
        adj[s].append(t)

        outdeg[s] += 1
        indeg[t] += 1

        ms = mod_of(s)
        mt = mod_of(t)
        if ms and mt and ms != mt:
            cross_edges += 1

    degree = {nid: (indeg.get(nid, 0) + outdeg.get(nid, 0)) for nid in set(list(indeg.keys()) + list(outdeg.keys()))}
    hubs = {nid for nid, d in degree.items() if d >= int(degree_k)}

    # pre-sort outgoing for "best-first" exploration:
    # prefer edges that cross modules and targets with higher degree
    def sort_key(src: str, dst: str) -> Tuple[int, int]:
        ms = mod_of(src)
        mt = mod_of(dst)
        crosses = 1 if (ms and mt and ms != mt) else 0
        return (crosses, degree.get(dst, 0))

    sorted_adj: Dict[str, List[str]] = {}
    for s, lst in adj.items():
        uniq = list(dict.fromkeys(lst))  # stable de-dup, preserves order
        uniq.sort(key=lambda d: sort_key(s, d), reverse=True)
        sorted_adj[s] = uniq[: int(max_out_per_node)]

    # score a chain: crossings dominate, then hub count, then total degrees
    def chain_metrics(path: List[str]) -> Tuple[int, int, int]:
        crossings = 0
        hub_hits = 0
        deg_sum = 0
        for i, nid in enumerate(path):
            if nid in hubs:
                hub_hits += 1
            deg_sum += degree.get(nid, 0)
            if i > 0:
                ms = mod_of(path[i - 1])
                mt = mod_of(nid)
                if ms and mt and ms != mt:
                    crossings += 1
        return crossings, hub_hits, deg_sum

    def chain_is_kept(path: List[str]) -> bool:
        crossings, hub_hits, _ = chain_metrics(path)
        if crossings >= 1:
            return True
        # within-module: keep only if includes at least one hub node
        return hub_hits >= 1

    # choose starts: prefer hubs and any function with outbound calls
    starts = []
    for nid in fn_ids:
        if outdeg.get(nid, 0) > 0:
            starts.append(nid)
    # rank starts: hubs first, then by degree
    starts.sort(key=lambda n: ((1 if n in hubs else 0), degree.get(n, 0), outdeg.get(n, 0)), reverse=True)

    chains_out: List[Dict[str, Any]] = []

    total_considered = 0

    def label_of(nid: str) -> str:
        n = gs.nodes.get(nid)
        return n.label if n else nid

    def dfs_from(start: str) -> None:
        nonlocal total_considered, chains_out

        kept_for_start: List[Tuple[Tuple[int, int, int], List[str]]] = []

        stack: List[Tuple[List[str], set]] = [([start], {start})]

        while stack:
            path, seen = stack.pop()
            total_considered += 1
            if total_considered > 600000:  # hard guardrail
                break

            if len(path) >= 2 and chain_is_kept(path):
                m = chain_metrics(path)
                kept_for_start.append((m, path[:]))
                # bound per-start
                if len(kept_for_start) >= int(max_chains_per_start) * 4:
                    # we'll prune later after sorting
                    pass

            if len(path) >= int(max_len):
                continue

            last = path[-1]
            for nxt in (sorted_adj.get(last) or []):
                # stop quickly on unresolved leaves
                if nxt.startswith("unresolved:"):
                    new_path = path + [nxt]
                    if chain_is_kept(new_path):
                        m = chain_metrics(new_path)
                        kept_for_start.append((m, new_path))
                    continue

                # avoid cycles
                if nxt in seen:
                    continue
                stack.append((path + [nxt], seen | {nxt}))

        # take best for start
        kept_for_start.sort(key=lambda t: t[0], reverse=True)
        kept_for_start = kept_for_start[: int(max_chains_per_start)]

        for m, path in kept_for_start:
            crossings, hub_hits, deg_sum = m
            chains_out.append({
                "path_ids": path,
                "path_labels": [label_of(x) for x in path],
                "modules": [mod_of(x) for x in path],
                "crossings": int(crossings),
                "hub_hits": int(hub_hits),
                "deg_sum": int(deg_sum),
                "start": start,
            })

    for s in starts:
        if len(chains_out) >= int(max_total_chains):
            break
        dfs_from(s)

    # global prune
    chains_out.sort(key=lambda c: (c["crossings"], c["hub_hits"], c["deg_sum"]), reverse=True)
    chains_out = chains_out[: int(max_total_chains)]

    # build inter-module summary
    inter = defaultdict(int)
    for e in gs.edges.values():
        if e.type != "CALLS":
            continue
        ms = mod_of(e.src)
        mt = mod_of(e.dst)
        if ms and mt and ms != mt:
            inter[(ms, mt)] += 1

    inter_list = [{"src_module": k[0], "dst_module": k[1], "calls": int(v)} for k, v in inter.items()]
    inter_list.sort(key=lambda d: d["calls"], reverse=True)

    # module sizes (line counts)
    module_nodes = [n for n in gs.nodes.values() if n.type == "Module"]
    mod_sizes = []
    for m in module_nodes:
        fp = (m.meta.get("file_path") or "").strip()
        lines = try_count_lines(fp) if fp else 0
        mod_sizes.append({
            "module": m.meta.get("module") or m.label,
            "file_path": fp,
            "lines": int(lines),
        })
    mod_sizes.sort(key=lambda d: d["lines"], reverse=True)

    # hub list
    hub_list = [{"id": nid, "label": label_of(nid), "module": mod_of(nid), "degree": int(degree.get(nid, 0)),
                 "in": int(indeg.get(nid, 0)), "out": int(outdeg.get(nid, 0))}
                for nid in sorted(hubs, key=lambda x: degree.get(x, 0), reverse=True)]
    hub_list = hub_list[:800]

    return {
        "schema": "nykg.focus_lineages.v1",
        "saved_at": now_iso(),
        "build": NYKG_BUILD,
        "root": gs.root,
        "params": {
            "degree_k": int(degree_k),
            "max_len": int(max_len),
            "max_out_per_node": int(max_out_per_node),
            "max_chains_per_start": int(max_chains_per_start),
            "max_total_chains": int(max_total_chains),
        },
        "stats": {
            "nodes": len(gs.nodes),
            "edges": len(gs.edges),
            "functions_methods": len(fn_ids),
            "calls_total": int(total_calls),
            "cross_module_edges": int(cross_edges),
            "hubs_n": int(len(hubs)),
            "chains_kept": int(len(chains_out)),
            "chains_considered": int(total_considered),
        },
        "module_sizes": mod_sizes,
        "hub_nodes": hub_list,
        "inter_module_calls": inter_list[:800],
        "chains": chains_out,
    }

# -----------------------------
# Qt Graphics Items (Nodes & Edges)
# -----------------------------
class NodeItem(QGraphicsRectItem):
    def __init__(self, node: Node, rect: QRectF):
        super().__init__(rect)
        self.node = node
        self.setFlag(QGraphicsItem.GraphicsItemFlag.ItemIsMovable, True)
        self.setFlag(QGraphicsItem.GraphicsItemFlag.ItemIsSelectable, True)
        self.setFlag(QGraphicsItem.GraphicsItemFlag.ItemSendsGeometryChanges, True)

        self.text = QGraphicsTextItem(node.label, self)
        self.text.setDefaultTextColor(QColor("#111"))
        f = QFont()
        f.setPointSize(9 if node.type != "Module" else 10)
        f.setBold(node.type == "Module")
        self.text.setFont(f)
        self.text.setTextWidth(rect.width() - 10)
        self.text.setPos(rect.x() + 5, rect.y() + 5)

        # color by type
        color = {
            "Module": "#e8e8e8",
            "Class": "#d9eefc",
            "Function": "#dff6df",
            "Method": "#dff6df",
            "UnresolvedSymbol": "#ffe7cc",
        }.get(node.type, "#eeeeee")
        self.setBrush(QBrush(QColor(color)))
        self.setPen(QPen(QColor("#333"), 1))

        # keep nodes above edges and above group frame
        self.setZValue(0)

    def itemChange(self, change: QGraphicsItem.GraphicsItemChange, value):
        if change == QGraphicsItem.GraphicsItemChange.ItemPositionHasChanged:
            p: QPointF = self.scenePos()  # scene coordinates even when parented
            sc = self.scene()
            if sc and hasattr(sc, "_on_node_moved") and sc._on_node_moved:
                try:
                    sc._on_node_moved(self.node.id, p.x(), p.y())
                except Exception:
                    pass
        return super().itemChange(change, value)

class EdgeItem(QGraphicsPathItem):
    def __init__(self, edge: Edge, src_item: NodeItem, dst_item: NodeItem):
        super().__init__()
        self.edge = edge
        self.src_item = src_item
        self.dst_item = dst_item

        self.setFlag(QGraphicsItem.GraphicsItemFlag.ItemIsSelectable, True)

        # Put edges BEHIND everything for legibility.
        self.setZValue(-50)

        # thinner visible pen + thick "hit" shape via stroker
        self.pen_normal = QPen(QColor(120, 120, 120, 160), 2)
        self.pen_selected = QPen(QColor("#00aaff"), 4)
        self.setPen(self.pen_normal)

        self.update_path()

    def update_path(self) -> None:
        s = self.src_item.sceneBoundingRect().center()
        t = self.dst_item.sceneBoundingRect().center()

        dx = (t.x() - s.x()) * 0.5
        c1 = QPointF(s.x() + dx, s.y())
        c2 = QPointF(t.x() - dx, t.y())

        from PyQt6.QtGui import QPainterPath
        path = QPainterPath(s)
        path.cubicTo(c1, c2, t)
        self.setPath(path)

    def paint(self, painter: QPainter, option, widget=None):
        self.setPen(self.pen_selected if self.isSelected() else self.pen_normal)
        super().paint(painter, option, widget)

    def shape(self):
        from PyQt6.QtGui import QPainterPathStroker
        stroker = QPainterPathStroker()
        stroker.setWidth(14.0)
        return stroker.createStroke(self.path())

class ModuleGroupItem(QGraphicsRectItem):
    def __init__(self, module_id: str, modq: str, rect: QRectF):
        super().__init__(rect)
        self.module_id = module_id
        self.modq = modq

        self.setFlag(QGraphicsItem.GraphicsItemFlag.ItemIsMovable, True)
        self.setFlag(QGraphicsItem.GraphicsItemFlag.ItemIsSelectable, True)
        self.setFlag(QGraphicsItem.GraphicsItemFlag.ItemSendsGeometryChanges, True)

        # Behind nodes; edges are even further behind (-50)
        self.setZValue(-20)

        # subtle frame
        self.setBrush(QBrush(QColor(245, 245, 245, 120)))
        self.setPen(QPen(QColor("#666"), 2))

        # title label (local coords)
        self.title = QGraphicsTextItem(f"Module: {modq}", self)
        self.title.setDefaultTextColor(QColor("#222"))
        f = QFont()
        f.setPointSize(10)
        f.setBold(True)
        self.title.setFont(f)
        self.title.setPos(8, 6)

    def itemChange(self, change: QGraphicsItem.GraphicsItemChange, value):
        if change == QGraphicsItem.GraphicsItemChange.ItemPositionHasChanged:
            sc = self.scene()
            if sc and hasattr(sc, "_on_group_moved") and sc._on_group_moved:
                try:
                    sc._on_group_moved(self)
                except Exception:
                    pass
        return super().itemChange(change, value)

# -----------------------------
# Scene + View
# -----------------------------
class KGScene(QGraphicsScene):
    def __init__(self):
        super().__init__()
        self._on_node_moved = None  # assigned by MainWindow
        self._on_group_moved = None  # assigned by MainWindow

class KGView(QGraphicsView):
    viewChanged = pyqtSignal(float, float, float)  # tx, ty, scale

    def __init__(self, scene: KGScene):
        super().__init__(scene)
        self.setRenderHint(QPainter.RenderHint.Antialiasing, True)
        self.setDragMode(QGraphicsView.DragMode.ScrollHandDrag)
        self.setViewportUpdateMode(QGraphicsView.ViewportUpdateMode.FullViewportUpdate)

    def wheelEvent(self, event):
        zoom_in = 1.15
        zoom_out = 1.0 / zoom_in
        old_pos = self.mapToScene(event.position().toPoint())
        factor = zoom_in if event.angleDelta().y() > 0 else zoom_out
        self.scale(factor, factor)
        new_pos = self.mapToScene(event.position().toPoint())
        delta = new_pos - old_pos
        self.translate(delta.x(), delta.y())
        self._report_view()
        event.accept()

    def mouseReleaseEvent(self, event):
        super().mouseReleaseEvent(event)
        self._report_view()

    def _report_view(self):
        tr = self.transform()
        self.viewChanged.emit(tr.m31(), tr.m32(), tr.m11())

# -----------------------------
# Main Window
# -----------------------------
class MainWindow(QMainWindow):
    def __init__(self, root: str, initial_project: str = "Default"):
        super().__init__()
        self.setWindowTitle(f"Nyreth KG Explorer — {NYKG_BUILD}")
        self.resize(1700, 980)
        print(NYKG_BUILD)

        ensure_dir(WORKSPACES_DIR)
        self.current_project = safe_name(initial_project)
        self.db_path, self.layout_path, self.meta_path = workspace_paths(self.current_project)

        # load DB
        if os.path.exists(self.db_path):
            self.gs = GraphStore.load(self.db_path)
        else:
            self.gs = GraphStore(root)

        # per-project root from meta.json
        meta = read_meta(self.meta_path)
        proj_root = meta.get("root") or root
        self.gs.root = norm_path(proj_root)
        write_meta(self.meta_path, self.gs.root)

        # layout
        lay = load_layout(self.layout_path)
        self.layout_positions: Dict[str, Dict[str, float]] = lay.get("positions") or {}
        self.view_state: Dict[str, float] = lay.get("view") or {"tx": 0.0, "ty": 0.0, "scale": 1.0}

        # selection logging
        self.capture = False
        self.selection_log: List[Dict[str, Any]] = []
        self._rebuilding_scene = False  # guard: ignore move callbacks during refresh_scene()

        # ---------- UI ----------
        splitter = QSplitter()
        left = QWidget()
        left_layout = QVBoxLayout(left)

        row1 = QHBoxLayout()
        row2 = QHBoxLayout()
        row3 = QHBoxLayout()

        row1.addWidget(QLabel("Project:"))
        self.project_combo = QComboBox()
        projects = list_workspaces() or [self.current_project]
        if self.current_project not in projects:
            projects.append(self.current_project)
            projects.sort(key=lambda s: s.lower())
        self.project_combo.addItems(projects)
        self.project_combo.setCurrentText(self.current_project)
        self.project_combo.currentTextChanged.connect(self.on_project_changed)
        row1.addWidget(self.project_combo)

        btn_newproj = QPushButton("New…")
        btn_newproj.clicked.connect(self.on_project_new)
        row1.addWidget(btn_newproj)

        btn_renameproj = QPushButton("Ren…")
        btn_renameproj.clicked.connect(self.on_project_rename)
        row1.addWidget(btn_renameproj)

        btn_delproj = QPushButton("Del")
        btn_delproj.clicked.connect(self.on_project_delete)
        row1.addWidget(btn_delproj)

        left_layout.addLayout(row1)

        btn_add = QPushButton("Add…")
        btn_add.clicked.connect(self.on_add_modules)
        row2.addWidget(btn_add)

        btn_remove = QPushButton("Remove Module")
        btn_remove.clicked.connect(self.on_remove_selected_module)
        row2.addWidget(btn_remove)

        btn_fit = QPushButton("Fit Rectangle")
        btn_fit.clicked.connect(self.on_fit)
        row2.addWidget(btn_fit)

        btn_save = QPushButton("Save")
        btn_save.clicked.connect(self.on_save_all)
        row2.addWidget(btn_save)

        left_layout.addLayout(row2)

        # Focus lineage log controls (Option B)
        btn_log = QPushButton("Log Focus Chains…")
        btn_log.clicked.connect(self.on_log_focus_chains)
        row3.addWidget(btn_log)

        btn_modlinks = QPushButton("Module Links…")
        btn_modlinks.clicked.connect(self.on_export_module_links)
        row3.addWidget(btn_modlinks)

        self.k_degree = QLineEdit()
        self.k_degree.setPlaceholderText("K (hub degree) e.g. 8")
        self.k_degree.setText("8")
        self.k_degree.setMaximumWidth(140)
        row3.addWidget(self.k_degree)

        self.max_len = QLineEdit()
        self.max_len.setPlaceholderText("max_len e.g. 5")
        self.max_len.setText("5")
        self.max_len.setMaximumWidth(140)
        row3.addWidget(self.max_len)

        left_layout.addLayout(row3)

        self.search = QLineEdit()
        self.search.setPlaceholderText("Search (label substring) Enter=focus")
        self.search.returnPressed.connect(self.on_search_focus)
        left_layout.addWidget(self.search)

        left_layout.addWidget(QLabel("Project Tree:"))
        self.tree = QTreeWidget()
        self.tree.setHeaderHidden(True)
        self.tree.setSelectionMode(QAbstractItemView.SelectionMode.SingleSelection)
        self.tree.itemClicked.connect(self.on_tree_clicked)
        left_layout.addWidget(self.tree, stretch=1)

        self.chk_capture = QCheckBox("Capture selections (nodes/edges)")
        self.chk_capture.setChecked(False)
        self.chk_capture.stateChanged.connect(self.on_capture_toggle)
        left_layout.addWidget(self.chk_capture)

        btn_save_sel = QPushButton("Save Selections…")
        btn_save_sel.clicked.connect(self.on_save_selections)
        left_layout.addWidget(btn_save_sel)

        left_layout.addWidget(QLabel("Details:"))
        self.details = QTextEdit()
        self.details.setReadOnly(True)
        self.details.setMinimumHeight(280)
        left_layout.addWidget(self.details)

        left_layout.addWidget(QLabel("Diagnostics:"))
        self.diag = QTextEdit()
        self.diag.setReadOnly(True)
        self.diag.setMinimumHeight(160)
        left_layout.addWidget(self.diag)

        self.stats = QLabel("")
        left_layout.addWidget(self.stats)

        # graphics
        self.scene = KGScene()
        self.scene._on_node_moved = self.on_node_moved
        self.scene._on_group_moved = self.on_group_moved
        self.scene.selectionChanged.connect(self.on_scene_selection_changed)

        self.view = KGView(self.scene)
        self.view.viewChanged.connect(self.on_view_changed)

        splitter.addWidget(left)
        splitter.addWidget(self.view)
        splitter.setSizes([460, 1240])
        self.setCentralWidget(splitter)

        # build a visible graph immediately (no dot)
        self.gs.rebuild_indexes()
        if not self.gs.nodes:
            self._seed_demo_graph()

        self.refresh_tree()
        self.refresh_scene(full_rebuild=True)
        self.log(f"Ready. Project={self.current_project} Root={self.gs.root}")

    # ----------------- logging/persistence -----------------
    def log(self, msg: str) -> None:
        self.diag.append(f"[{now_iso()}] {msg}")

    def persist_db(self) -> None:
        try:
            self.gs.save(self.db_path)
        except Exception as e:
            self.log(f"DB save error: {e}")

    def persist_layout(self) -> None:
        try:
            save_layout(self.layout_path, self.layout_positions, self.view_state)
        except Exception as e:
            self.log(f"Layout save error: {e}")

    # ----------------- demo seed -----------------
    def _seed_demo_graph(self) -> None:
        m = Node(id="module:demo", type="Module", label="demo", meta={"module": "demo"})
        f1 = Node(id="sym:demo:func:alpha:1", type="Function", label="demo.alpha", meta={"module": "demo", "name": "alpha"})
        f2 = Node(id="sym:demo:func:beta:0", type="Function", label="demo.beta", meta={"module": "demo", "name": "beta"})
        e = Edge(id=make_edge_id("CALLS", f1.id, f2.id, extra="1|beta"), type="CALLS", src=f1.id, dst=f2.id,
                 meta={"lineno": 1, "callee_text": "beta", "confidence": 0.7})
        self.gs.upsert_node(m, owner_module_id=m.id)
        self.gs.upsert_node(f1, owner_module_id=m.id)
        self.gs.upsert_node(f2, owner_module_id=m.id)
        self.gs.upsert_edge(e, owner_module_id=m.id)
        self.gs.rebuild_indexes()

    # ----------------- UI refresh -----------------
    def update_stats(self) -> None:
        mods = len([n for n in self.gs.nodes.values() if n.type == "Module"])
        self.stats.setText(f"Nodes: {len(self.gs.nodes)} | Edges: {len(self.gs.edges)} | Modules: {mods}")

    def refresh_tree(self) -> None:
        self.tree.clear()
        modules = [n for n in self.gs.nodes.values() if n.type == "Module"]
        modules.sort(key=lambda n: n.label.lower())

        def funcs_for(modq: str) -> List[Node]:
            out = [n for n in self.gs.nodes.values() if n.type in ("Function", "Method") and n.meta.get("module") == modq]
            out.sort(key=lambda n: n.label.lower())
            return out

        def classes_for(modq: str) -> List[Node]:
            out = [n for n in self.gs.nodes.values() if n.type == "Class" and n.meta.get("module") == modq]
            out.sort(key=lambda n: n.label.lower())
            return out

        for m in modules:
            mid = m.id
            modq = m.meta.get("module") or m.label
            m_item = QTreeWidgetItem([m.label])
            m_item.setData(0, Qt.ItemDataRole.UserRole, {"kind": "module", "id": mid})
            self.tree.addTopLevelItem(m_item)

            cls = classes_for(modq)
            if cls:
                hdr = QTreeWidgetItem(["Classes"])
                hdr.setData(0, Qt.ItemDataRole.UserRole, {"kind": "header"})
                m_item.addChild(hdr)
                for c in cls:
                    ci = QTreeWidgetItem([c.meta.get("name") or c.label.split(".")[-1]])
                    ci.setData(0, Qt.ItemDataRole.UserRole, {"kind": "node", "id": c.id})
                    hdr.addChild(ci)

            fn = funcs_for(modq)
            if fn:
                hdr = QTreeWidgetItem(["Functions/Methods"])
                hdr.setData(0, Qt.ItemDataRole.UserRole, {"kind": "header"})
                m_item.addChild(hdr)
                for f in fn[:400]:
                    fi = QTreeWidgetItem([f.label])
                    fi.setData(0, Qt.ItemDataRole.UserRole, {"kind": "node", "id": f.id})
                    hdr.addChild(fi)

        self.tree.expandToDepth(2)

    # ----------------- layout (no black dot) -----------------
    def _ensure_positions_grid(self) -> None:
        modules = [n for n in self.gs.nodes.values() if n.type == "Module"]
        modules.sort(key=lambda n: n.label.lower())

        mx0, my0 = 100.0, 60.0
        mod_dx = 420.0
        for i, m in enumerate(modules):
            if m.id not in self.layout_positions:
                self.layout_positions[m.id] = {"x": mx0 + i * mod_dx, "y": my0}

        for i, m in enumerate(modules):
            modq = m.meta.get("module") or m.label
            base = self.layout_positions.get(m.id, {"x": mx0 + i * mod_dx, "y": my0})
            cx, cy = base["x"], base["y"] + 120.0

            kids = [n for n in self.gs.nodes.values()
                    if n.id != m.id and n.meta.get("module") == modq and n.type in ("Class", "Function", "Method", "UnresolvedSymbol")]
            kids.sort(key=lambda n: (n.type, n.label.lower()))

            cols = 2 if len(kids) > 16 else 1
            dx = 300.0
            dy = 74.0
            for k, n in enumerate(kids[:250]):
                if n.id in self.layout_positions:
                    continue
                r = k // cols
                c = k % cols
                self.layout_positions[n.id] = {"x": cx + c * dx, "y": cy + r * dy}

    # ----------------- FULL corrected refresh_scene -----------------
    def refresh_scene(self, full_rebuild: bool = False) -> None:
        """
        Rebuild scene items from GraphStore.

        Fixes:
          - Module group rectangles are movable and their positions persist (layout key: grp:<module_id>)
          - Nodes inside groups remain movable (you can rearrange within module box)
          - Edges stay behind everything for legibility and update when nodes/groups move
          - Group rect surrounds children and persists its top-left position once moved
        """
        self._ensure_positions_grid()

        # always do full rebuild for simplicity & correctness
        self._rebuilding_scene = True
        self.scene._on_node_moved = None
        self.scene._on_group_moved = None
        self.scene.clear()

        node_items: Dict[str, NodeItem] = {}
        edge_items: Dict[str, EdgeItem] = {}

        # --- module groups ---
        modules = [n for n in self.gs.nodes.values() if n.type == "Module"]
        modules.sort(key=lambda n: n.label.lower())

        groups: Dict[str, ModuleGroupItem] = {}

        # group geometry constants
        PAD = 40.0
        TITLE_H = 28.0
        MIN_W = 420.0
        MIN_H = 240.0

        # create group items first (pos will be set after we know where children are)
        for m in modules:
            modq = m.meta.get("module") or m.label
            g = ModuleGroupItem(m.id, modq, QRectF(0, 0, MIN_W, MIN_H))
            self.scene.addItem(g)
            groups[m.id] = g

        # helper: module id from module qualname
        def module_id_for_modq(modq: str) -> str:
            return f"module:{modq}"

        # --- create node items and parent them to their module group (except truly unassigned) ---
        # We temporarily place them using absolute scene coordinates; then we convert to group-local.
        for nid, n in self.gs.nodes.items():
            p = self.layout_positions.get(nid) or {"x": 100.0, "y": 100.0}
            w = 300.0 if n.type == "Module" else 280.0
            h = 70.0 if n.type == "Module" else 60.0
            rect = QRectF(0, 0, w, h)
            item = NodeItem(n, rect)

            # determine parent group
            parent_group: Optional[ModuleGroupItem] = None
            modq = (n.meta.get("module") or "").strip()
            if n.type == "Module":
                parent_group = groups.get(n.id)
            elif modq:
                parent_group = groups.get(module_id_for_modq(modq))

            if parent_group:
                item.setParentItem(parent_group)

            # for now, place at absolute position in SCENE coords
            # (if parented, this is interpreted as parent coords — we'll fix below after group pos is set)
            item.setPos(QPointF(p["x"], p["y"]))

            self.scene.addItem(item)
            node_items[nid] = item

        # --- compute group positions and sizes based on member nodes (using stored node positions) ---
        # Strategy:
        #   - If group has saved position grp:<mid>, use it as top-left.
        #   - Otherwise, derive top-left from the min of child absolute positions.
        #   - Then convert each child to group-local coords: child_local = child_abs - group_pos.
        for mid, g in groups.items():
            # nodes belonging to this module
            modq = g.modq
            child_ids = [nid for nid, n in self.gs.nodes.items()
                         if (n.type != "Module") and ((n.meta.get("module") or "") == modq)]
            # include the module node itself if present
            if mid in self.gs.nodes:
                child_ids.append(mid)

            # compute bounding from absolute layout_positions (authoritative)
            abs_rect: Optional[QRectF] = None
            for nid in child_ids:
                p = self.layout_positions.get(nid)
                if not p:
                    continue
                n = self.gs.nodes.get(nid)
                if not n:
                    continue
                w = 300.0 if n.type == "Module" else 280.0
                h = 70.0 if n.type == "Module" else 60.0
                r = QRectF(float(p["x"]), float(p["y"]), w, h)
                abs_rect = r if abs_rect is None else abs_rect.united(r)

            if abs_rect is None:
                # fallback: stick it near origin
                abs_rect = QRectF(100.0, 100.0, MIN_W, MIN_H)

            # choose group top-left
            grp_key = f"grp:{mid}"
            if grp_key in self.layout_positions:
                gp = self.layout_positions[grp_key]
                gx, gy = float(gp.get("x", abs_rect.x())), float(gp.get("y", abs_rect.y()))
            else:
                gx = abs_rect.left() - PAD
                gy = abs_rect.top() - (PAD + TITLE_H)

            # set group position (scene)
            g.setPos(QPointF(gx, gy))

            # convert children to group-local coords using absolute stored positions
            # (this is what makes nodes movable inside the module box reliably)
            max_right = 0.0
            max_bottom = 0.0
            min_left = 1e18
            min_top = 1e18

            for nid in child_ids:
                it = node_items.get(nid)
                if not it:
                    continue
                p = self.layout_positions.get(nid)
                if not p:
                    continue

                # local = abs - group_pos
                lx = float(p["x"]) - gx
                ly = float(p["y"]) - gy
                it.setPos(QPointF(lx, ly))

                # local rect extents
                br = it.boundingRect()
                min_left = min(min_left, lx)
                min_top = min(min_top, ly)
                max_right = max(max_right, lx + br.width())
                max_bottom = max(max_bottom, ly + br.height())

            # if everything was shifted negative (due to saved group pos), expand rect to still contain children
            if min_left == 1e18:
                min_left, min_top, max_right, max_bottom = 0.0, 0.0, MIN_W, MIN_H

            # determine group rect size to enclose children + padding
            w = max(MIN_W, max_right + PAD)
            h = max(MIN_H, max_bottom + PAD)

            # tighten frame around current children (and normalize children inside padding/title area)
            self._tighten_group_rect(g)

        # --- create edges ---
        for eid, e in self.gs.edges.items():
            if e.type != "CALLS":
                continue
            if e.src not in node_items or e.dst not in node_items:
                continue
            ei = EdgeItem(e, node_items[e.src], node_items[e.dst])
            self.scene.addItem(ei)
            edge_items[eid] = ei

        # initial edge paths
        for ei in edge_items.values():
            ei.update_path()

        # scene rect — add generous gutters so you can pan when zoomed in
        items_rect = self.scene.itemsBoundingRect()
        GUTTER_X = 2200.0
        GUTTER_Y = 900.0
        self.scene.setSceneRect(items_rect.adjusted(-GUTTER_X, -GUTTER_Y, GUTTER_X, GUTTER_Y))

        # apply saved view transform (or fit)
        sc = float(self.view_state.get("scale", 1.0) or 1.0)
        tx = float(self.view_state.get("tx", 0.0) or 0.0)
        ty = float(self.view_state.get("ty", 0.0) or 0.0)
        if sc != 0.0:
            self.view.setTransform(QTransform(sc, 0.0, 0.0, sc, tx, ty))
        else:
            self.on_fit()

        self.update_stats()

        # restore callbacks after the scene is stable
        self.scene._on_node_moved = self.on_node_moved
        self.scene._on_group_moved = self.on_group_moved
        self._rebuilding_scene = False

        self.persist_layout()
        self.persist_db()

    # ----------------- selection handling -----------------
    def on_scene_selection_changed(self) -> None:
        selected = self.scene.selectedItems()
        if not selected:
            return

        # prefer edges
        edges = [it for it in selected if isinstance(it, EdgeItem)]
        if edges:
            eitem: EdgeItem = edges[0]
            self.render_details_for_edge(eitem.edge)
            self.record_selection("edge", eitem.edge)
            return

        # then nodes
        nodes = [it for it in selected if isinstance(it, NodeItem)]
        if nodes:
            nitem: NodeItem = nodes[0]
            self.render_details_for_node(nitem.node.id)
            self.record_selection("node", nitem.node)
            return

        # groups (optional details)
        groups = [it for it in selected if isinstance(it, ModuleGroupItem)]
        if groups:
            g = groups[0]
            self.details.setPlainText(f"MODULE GROUP: {g.modq}\n{g.module_id}")
            return

    def render_details_for_node(self, nid: str) -> None:
        n = self.gs.nodes.get(nid)
        if not n:
            self.details.setPlainText(f"(missing node) {nid}")
            return

        lines = []
        lines.append(f"{n.type}: {n.label}")
        lines.append(f"id: {n.id}")

        for k in ("module", "class", "lineno", "arity", "file_path"):
            if k in n.meta and n.meta.get(k) is not None:
                lines.append(f"{k}: {n.meta.get(k)}")

        doc = (n.meta.get("doc") or "").strip()
        if doc:
            lines.append("")
            lines.append("doc:")
            lines.append(doc[:1200])

        inbound = []
        outbound = []
        for e in self.gs.edges.values():
            if e.type != "CALLS":
                continue
            if e.dst == nid:
                inbound.append(e)
            if e.src == nid:
                outbound.append(e)

        lines.append("")
        lines.append(f"Inbound CALLS: {len(inbound)}")
        for e in inbound[:80]:
            src_label = self.gs.nodes[e.src].label if e.src in self.gs.nodes else e.src
            lines.append(f"  <- {src_label}  (line {e.meta.get('lineno')}, conf {e.meta.get('confidence')})")

        lines.append("")
        lines.append(f"Outbound CALLS: {len(outbound)}")
        for e in outbound[:80]:
            dst_label = self.gs.nodes[e.dst].label if e.dst in self.gs.nodes else e.dst
            lines.append(f"  -> {dst_label}  (line {e.meta.get('lineno')}, conf {e.meta.get('confidence')})")

        self.details.setPlainText("\n".join(lines))

    def render_details_for_edge(self, e: Edge) -> None:
        src = self.gs.nodes.get(e.src)
        dst = self.gs.nodes.get(e.dst)
        caller = src.label if src else e.src
        callee = dst.label if dst else e.dst

        lines = []
        lines.append(f"EDGE: {e.type}")
        lines.append(f"id: {e.id}")
        lines.append("")
        lines.append("Function-level connection:")
        lines.append(f"  {caller}  ->  {callee}")
        if e.meta.get("lineno") is not None:
            lines.append(f"  line: {e.meta.get('lineno')}")
        if e.meta.get("confidence") is not None:
            lines.append(f"  confidence: {e.meta.get('confidence')}")
        if e.meta.get("callee_text"):
            lines.append(f"  callee_text: {e.meta.get('callee_text')}")
        if e.meta.get("argc") is not None:
            lines.append(f"  argc: {e.meta.get('argc')}")
        self.details.setPlainText("\n".join(lines))

    def _tighten_group_rect(self, group: ModuleGroupItem) -> None:
        """
        Shrink/expand the module group rectangle to tightly surround its NodeItem children.
        If children drift into negative/top-left space, shift them locally so the group
        can stay anchored at (0,0) with padding + title clearance.
        """
        # keep in sync with refresh_scene constants
        PAD = 40.0
        TITLE_H = 28.0
        MIN_W = 420.0
        MIN_H = 240.0

        # collect node children (ignore title text)
        kids = [it for it in group.childItems() if isinstance(it, NodeItem)]
        if not kids:
            group.prepareGeometryChange()
            group.setRect(QRectF(0, 0, MIN_W, MIN_H))
            group.title.setPos(8, 6)
            return

        # compute local bounds
        min_left = 1e18
        min_top = 1e18
        max_right = -1e18
        max_bottom = -1e18

        for it in kids:
            p = it.pos()  # group-local
            br = it.boundingRect()
            min_left = min(min_left, p.x())
            min_top = min(min_top, p.y())
            max_right = max(max_right, p.x() + br.width())
            max_bottom = max(max_bottom, p.y() + br.height())

        # desired interior origin (leave space for title)
        want_left = PAD
        want_top = PAD + TITLE_H

        # shift kids so content sits nicely inside the frame
        dx = (want_left - min_left) if min_left < want_left else 0.0
        dy = (want_top - min_top) if min_top < want_top else 0.0

        if abs(dx) > 0.01 or abs(dy) > 0.01:
            delta = QPointF(dx, dy)
            for it in kids:
                it.setPos(it.pos() + delta)

            # after shifting, recompute extents
            min_left = 1e18
            min_top = 1e18
            max_right = -1e18
            max_bottom = -1e18
            for it in kids:
                p = it.pos()
                br = it.boundingRect()
                min_left = min(min_left, p.x())
                min_top = min(min_top, p.y())
                max_right = max(max_right, p.x() + br.width())
                max_bottom = max(max_bottom, p.y() + br.height())

            # keep layout_positions coherent (store ABS scene coords)
            for it in kids:
                sp = it.scenePos()
                self.layout_positions[it.node.id] = {"x": float(sp.x()), "y": float(sp.y())}

        # compute tight rect size
        w = max(MIN_W, max_right + PAD)
        h = max(MIN_H, max_bottom + PAD)

        group.prepareGeometryChange()
        group.setRect(QRectF(0, 0, w, h))
        group.title.setPos(8, 6)


    # ----------------- movement & view persistence -----------------
    def on_node_moved(self, node_id: str, x: float, y: float) -> None:
        if getattr(self, "_rebuilding_scene", False):
            return
        self.layout_positions[node_id] = {"x": float(x), "y": float(y)}
        # If this node lives inside a module group, tighten that group's bounds.
        # (This makes the rectangle expand/shrink as you rearrange nodes.)
        moved_item = None
        for it in self.scene.items():
            if isinstance(it, NodeItem) and it.node.id == node_id:
                moved_item = it
                break

        if moved_item:
            pg = moved_item.parentItem()
            if isinstance(pg, ModuleGroupItem):
                self._tighten_group_rect(pg)
        self.persist_layout()

        # update edges
        for it in self.scene.items():
            if isinstance(it, EdgeItem):
                it.update_path()

    def on_group_moved(self, group: ModuleGroupItem) -> None:
        if getattr(self, "_rebuilding_scene", False):
            return
        # persist group top-left
        self.layout_positions[f"grp:{group.module_id}"] = {"x": float(group.scenePos().x()),
                                                           "y": float(group.scenePos().y())}
        # update layout_positions for all child nodes using their scene position
        for it in group.childItems():
            if isinstance(it, NodeItem):
                p = it.scenePos()
                self.layout_positions[it.node.id] = {"x": float(p.x()), "y": float(p.y())}

        self.persist_layout()

        # update edges
        for it in self.scene.items():
            if isinstance(it, EdgeItem):
                it.update_path()

    def on_view_changed(self, tx: float, ty: float, scale: float) -> None:
        self.view_state = {"tx": float(tx), "ty": float(ty), "scale": float(scale)}
        self.persist_layout()

    # ----------------- actions -----------------
    def on_fit(self) -> None:
        self.view.fitInView(
            self.scene.itemsBoundingRect().adjusted(-80, -80, 80, 80),
            Qt.AspectRatioMode.KeepAspectRatio
        )
        tr = self.view.transform()
        self.view_state = {"tx": tr.m31(), "ty": tr.m32(), "scale": tr.m11()}
        self.persist_layout()

    def on_save_all(self) -> None:
        self.persist_db()
        self.persist_layout()
        self.log("Saved db + layout.")

    def on_add_modules(self) -> None:
        files, _ = QFileDialog.getOpenFileNames(self, "Select Python module(s)", "", "Python Files (*.py)")
        if not files:
            return

        ok = 0
        err = 0
        for p in files:
            try:
                ingest_module(self.gs, p)
                ok += 1
            except Exception as e:
                err += 1
                self.log(f"Ingest error: {p} -> {e}")

        self.gs.rebuild_indexes()
        self.refresh_tree()
        self.refresh_scene(full_rebuild=True)
        self.log(f"Ingest done: ok={ok} err={err}")

    def on_remove_selected_module(self) -> None:
        item = self.tree.currentItem()
        if not item:
            self.log("Remove: no selection.")
            return
        data = item.data(0, Qt.ItemDataRole.UserRole) or {}
        if data.get("kind") != "module":
            self.log("Remove: select a module in the tree.")
            return
        mid = data.get("id")
        if not mid or mid not in self.gs.nodes:
            self.log("Remove: invalid selection.")
            return

        self.gs.remove_owner_module(mid)

        # purge layout for missing nodes
        for nid in list(self.layout_positions.keys()):
            if nid not in self.gs.nodes and not nid.startswith("grp:"):
                self.layout_positions.pop(nid, None)
        # purge the group box position key too
        self.layout_positions.pop(f"grp:{mid}", None)

        self.refresh_tree()
        self.refresh_scene(full_rebuild=True)
        self.persist_layout()
        self.log(f"Removed module: {mid}")

    def on_search_focus(self) -> None:
        q = (self.search.text() or "").strip()
        if not q:
            return
        qlow = q.lower()

        target: Optional[str] = None
        for n in self.gs.nodes.values():
            if qlow in n.label.lower():
                target = n.id
                break
        if not target:
            self.log(f"Search: not found: {q}")
            return

        for it in self.scene.items():
            if isinstance(it, NodeItem) and it.node.id == target:
                self.scene.clearSelection()
                it.setSelected(True)
                self.view.centerOn(it)
                self.render_details_for_node(target)
                self.record_selection("node", it.node)
                return

    def on_tree_clicked(self, item: QTreeWidgetItem, col: int) -> None:
        data = item.data(0, Qt.ItemDataRole.UserRole) or {}
        if data.get("kind") in ("header", None):
            return
        nid = data.get("id")
        if not nid:
            return
        if nid in self.gs.nodes:
            for it in self.scene.items():
                if isinstance(it, NodeItem) and it.node.id == nid:
                    self.scene.clearSelection()
                    it.setSelected(True)
                    self.view.centerOn(it)
                    self.render_details_for_node(nid)
                    self.record_selection("node", it.node)
                    return

    def on_capture_toggle(self) -> None:
        self.capture = self.chk_capture.isChecked()

    def record_selection(self, kind: str, obj: Any) -> None:
        if not self.capture:
            return
        rec: Dict[str, Any] = {"ts": now_iso(), "kind": kind}

        if kind == "node" and isinstance(obj, Node):
            rec["node"] = {"id": obj.id, "type": obj.type, "label": obj.label, "meta": obj.meta or {}}

        if kind == "edge" and isinstance(obj, Edge):
            src = self.gs.nodes.get(obj.src)
            dst = self.gs.nodes.get(obj.dst)
            rec["edge"] = {
                "id": obj.id,
                "type": obj.type,
                "source": obj.src,
                "target": obj.dst,
                "caller": src.label if src else obj.src,
                "callee": dst.label if dst else obj.dst,
                "meta": obj.meta or {},
            }

        self.selection_log.append(rec)
        if len(self.selection_log) > 2000:
            self.selection_log = self.selection_log[-2000:]
        self.log(f"Captured {kind}")

    def on_save_selections(self) -> None:
        path, _ = QFileDialog.getSaveFileName(self, "Save Selections", "selections.json", "JSON (*.json)")
        if not path:
            return
        data = {
            "schema": "nykg.hardreset.selections.v1",
            "saved_at": now_iso(),
            "build": NYKG_BUILD,
            "project": self.current_project,
            "root": self.gs.root,
            "selections": self.selection_log,
        }
        try:
            with open(path, "w", encoding="utf-8") as f:
                json.dump(data, f, indent=2)
            self.log(f"Saved selections -> {path} (n={len(self.selection_log)})")
        except Exception as e:
            self.log(f"Save selections error: {e}")

    def on_log_focus_chains(self) -> None:
        # write into workspace (no file dialog needed)
        wdir = workspace_dir(self.current_project)
        out_path = norm_path(os.path.join(wdir, f"focus_lineages_{now_stamp()}.json"))

        try:
            k = int((self.k_degree.text() or "8").strip())
        except Exception:
            k = 8
        try:
            ml = int((self.max_len.text() or "5").strip())
        except Exception:
            ml = 5

        try:
            payload = build_focus_lineage_log(
                self.gs,
                degree_k=max(1, k),
                max_len=max(2, ml),
                max_out_per_node=8,
                max_chains_per_start=25,
                max_total_chains=12000,
            )
            with open(out_path, "w", encoding="utf-8") as f:
                json.dump(payload, f, indent=2)
            self.log(f"FOCUS lineage log -> {out_path}")
            self.details.setPlainText(
                "FOCUS lineage log created:\n"
                f"{out_path}\n\n"
                f"chains_kept: {payload['stats']['chains_kept']}\n"
                f"hubs_n: {payload['stats']['hubs_n']}\n"
                f"cross_module_edges: {payload['stats']['cross_module_edges']}\n"
                f"params: {payload['params']}\n"
            )
        except Exception as e:
            self.log(f"FOCUS log error: {e}")

    # ----------------- project/workspace -----------------

    def on_export_module_links(self) -> None:
        """
        Export a simple module-to-module connectivity summary.
        Writes into the current workspace as a .txt file.
        """
        # Build module adjacency from CALLS edges
        def mod_of(nid: str) -> str:
            n = self.gs.nodes.get(nid)
            return (n.meta.get("module") if n else "") or ""

        # A -> B -> count
        counts_out: Dict[Tuple[str, str], int] = defaultdict(int)  # (src_mod, dst_mod) -> calls
        counts_in: Dict[Tuple[str, str], int] = defaultdict(int)  # (dst_mod, src_mod) -> calls (for inbound view)

        # ALL modules present in the graph (not just ones that appear in cross edges)
        modules = sorted(
            [(n.meta.get("module") or n.label) for n in self.gs.nodes.values() if n.type == "Module"],
            key=lambda s: s.lower()
        )

        for e in self.gs.edges.values():
            if e.type != "CALLS":
                continue
            ms = mod_of(e.src)
            mt = mod_of(e.dst)
            if not ms or not mt:
                continue
            if ms == mt:
                continue  # keep simple: cross-module only
            counts_out[(ms, mt)] += 1
            counts_in[(mt, ms)] += 1

        # Convert to adjacency dict for formatting
        out_adj: Dict[str, List[Tuple[str, int]]] = defaultdict(list)
        in_adj: Dict[str, List[Tuple[str, int]]] = defaultdict(list)

        for (ms, mt), c in counts_out.items():
            out_adj[ms].append((mt, int(c)))
        for (mt, ms), c in counts_in.items():
            in_adj[mt].append((ms, int(c)))

        for ms in modules:
            out_adj[ms].sort(key=lambda t: (t[1], t[0].lower()), reverse=True)
            in_adj[ms].sort(key=lambda t: (t[1], t[0].lower()), reverse=True)

        # Write into workspace (no dialog)
        wdir = workspace_dir(self.current_project)
        out_path = norm_path(os.path.join(wdir, f"module_links_{now_stamp()}.txt"))

        lines: List[str] = []
        lines.append(f"NyKG Module Links (simple)")
        lines.append(f"saved_at: {now_iso()}")
        lines.append(f"build: {NYKG_BUILD}")
        lines.append(f"project: {self.current_project}")
        lines.append(f"root: {self.gs.root}")
        lines.append("")

        if not counts_out and not counts_in:
            lines.append("(no cross-module CALLS edges found)")
        else:
            for ms in modules:
                outs = out_adj.get(ms) or []
                ins = in_adj.get(ms) or []

                lines.append(ms)

                if outs:
                    for (mt, c) in outs:
                        lines.append(f"  -> {mt} (calls: {c})")

                if ins:
                    for (srcm, c) in ins:
                        lines.append(f"  <- {srcm} (calls: {c})")

                if not outs and not ins:
                    lines.append("  (no cross-module links)")

                lines.append("")

        try:
            with open(out_path, "w", encoding="utf-8") as f:
                f.write("\n".join(lines).rstrip() + "\n")
            self.log(f"Module links -> {out_path}")
            self.details.setPlainText("Module links exported:\n" + out_path)
        except Exception as e:
            self.log(f"Module links export error: {e}")


    def _reload_current_project(self) -> None:
        self.db_path, self.layout_path, self.meta_path = workspace_paths(self.current_project)

        if os.path.exists(self.db_path):
            self.gs = GraphStore.load(self.db_path)
        else:
            self.gs = GraphStore(self.gs.root)

        meta = read_meta(self.meta_path)
        proj_root = meta.get("root") or self.gs.root
        self.gs.root = norm_path(proj_root)
        write_meta(self.meta_path, self.gs.root)

        lay = load_layout(self.layout_path)
        self.layout_positions = lay.get("positions") or {}
        self.view_state = lay.get("view") or {"tx": 0.0, "ty": 0.0, "scale": 1.0}

        self.gs.rebuild_indexes()
        if not self.gs.nodes:
            self._seed_demo_graph()

        self.refresh_tree()
        self.refresh_scene(full_rebuild=True)
        self.log(f"Switched project -> {self.current_project} (root={self.gs.root})")

    def on_project_changed(self, name: str) -> None:
        name = safe_name(name)
        if not name or name == self.current_project:
            return
        self.current_project = name
        self._reload_current_project()

    def on_project_new(self) -> None:
        name, ok = QInputDialog.getText(self, "New Project", "Project name:")
        if not ok:
            return
        name = safe_name(name)
        db, layout, meta = workspace_paths(name)
        if not os.path.exists(db):
            GraphStore(self.gs.root).save(db)
        if not os.path.exists(layout):
            save_layout(layout, {}, {"tx": 0.0, "ty": 0.0, "scale": 1.0})
        write_meta(meta, self.gs.root)
        if name not in [self.project_combo.itemText(i) for i in range(self.project_combo.count())]:
            self.project_combo.addItem(name)
        self.project_combo.setCurrentText(name)

    def on_project_rename(self) -> None:
        old = self.current_project
        name, ok = QInputDialog.getText(self, "Rename Project", "New name:", text=old)
        if not ok:
            return
        name = safe_name(name)
        if name == old:
            return
        old_dir = workspace_dir(old)
        new_dir = workspace_dir(name)
        if os.path.exists(new_dir):
            self.log(f"Rename blocked: '{name}' already exists.")
            return
        try:
            import shutil
            shutil.move(old_dir, new_dir)
        except Exception as e:
            self.log(f"Rename error: {e}")
            return
        self.current_project = name
        self.project_combo.blockSignals(True)
        self.project_combo.clear()
        self.project_combo.addItems(list_workspaces() or [self.current_project])
        self.project_combo.setCurrentText(self.current_project)
        self.project_combo.blockSignals(False)
        self._reload_current_project()

    def on_project_delete(self) -> None:
        allp = list_workspaces()
        if len(allp) <= 1:
            self.log("Delete blocked: at least one project must exist.")
            return
        name = self.current_project
        wdir = workspace_dir(name)
        try:
            import shutil
            shutil.rmtree(wdir)
        except Exception as e:
            self.log(f"Delete error: {e}")
            return
        remaining = list_workspaces()
        self.current_project = remaining[0]
        self.project_combo.blockSignals(True)
        self.project_combo.clear()
        self.project_combo.addItems(remaining)
        self.project_combo.setCurrentText(self.current_project)
        self.project_combo.blockSignals(False)
        self._reload_current_project()

    def closeEvent(self, event) -> None:
        try:
            self.persist_db()
        except Exception:
            pass
        try:
            self.persist_layout()
        except Exception:
            pass
        event.accept()

# -----------------------------
# main
# -----------------------------
def main() -> None:
    default_root = os.path.dirname(os.path.abspath(__file__))

    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=default_root, help="default project root (used for new projects)")
    ap.add_argument("--project", default="Default", help="workspace/project name (default: Default)")
    args = ap.parse_args()

    app = QApplication(sys.argv)
    w = MainWindow(args.root, args.project)
    w.show()
    sys.exit(app.exec())

if __name__ == "__main__":
    main()
