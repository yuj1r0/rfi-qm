#!/usr/bin/env python3
"""Verify FoliationQM module completeness, root/audit imports, forbidden constructs, and pinned toolchain."""
import json
import re
from pathlib import Path

root = Path(__file__).resolve().parents[1]
modules = json.loads((root / "docs/modules.json").read_text())
actual = {
    ".".join(p.relative_to(root).with_suffix("").parts)
    for p in (root / "FoliationQM").rglob("*.lean")
}
assert actual == set(modules), f"Module ledger mismatch: {actual ^ set(modules)}"

imports = set(
    re.findall(
        r"^(?:public )?import (FoliationQM\S*)$",
        (root / "FoliationQM.lean").read_text(),
        re.M,
    )
)
assert actual == imports, f"Root import mismatch: {actual ^ imports}"

audit_imports = set(
    re.findall(
        r"^import all (FoliationQM\S*)$",
        (root / "scripts/AxiomAudit.lean").read_text(),
        re.M,
    )
)
assert audit_imports == actual | {"FoliationQM"}, (
    f"Audit import mismatch: {audit_imports ^ (actual | {'FoliationQM'})}"
)

forbidden = re.compile(
    r"\b(sorry|admit|sorryAx|axiom|opaque|native_decide|unsafe|implemented_by)\b"
    r"|\+native|debug\.skipKernelTC|kernel\.trustLevel"
)
for p in sorted((root / "FoliationQM").rglob("*.lean")) + [root / "FoliationQM.lean"]:
    m = forbidden.search(p.read_text())
    assert not m, f"Forbidden construct {m.group(0)!r} in {p}"

assert (root / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.35.0"
manifest = json.loads((root / "lake-manifest.json").read_text())
mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
assert mathlib["rev"] == "56a005855ea17e0b0958f73ec801ae140b0a1679"
for pkg in manifest["packages"]:
    assert re.fullmatch(r"[a-f0-9]{40}", pkg["rev"]), f"Unpinned dependency: {pkg}"

print(
    f"LEAN CHECK PASS: {len(actual)} modules, root & axiom-audit imports match, "
    "zero forbidden constructs, pinned Lean 4.35.0 / Mathlib v4.35.0."
)
