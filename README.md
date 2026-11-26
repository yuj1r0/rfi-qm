# Relativistic Foliation Incompatibility and Quantum Mechanics (`rfi-qm`)

Companion repository for ***The Quantum Mechanical Wave Function from Relativistic Foliation Incompatibility*** (Tuomo Kiiskinen, Stanford University).

The paper proves an exact bidirectional equivalence between incompatible relativistic spacetime foliations—a timelike congruence carrying a periodic Compton proper clock ($\ell_C = \hbar/(mc)$) projected onto an observer's equal-time slice—and linear complex wave mechanics across scalar, spinorial ($\mathrm{Spin}^+(1,3)$ Dirac), multi-particle entangled, and curved-spacetime ($\xi = 1/6$) regimes, returning quantitatively to classical Einstein geodesics in the macroscopic WKB limit.

## Repository Layout

| Directory | Contents |
|---|---|
| [`paper/`](paper/) | Manuscript LaTeX source (`v18`), compiled PDF, and vector figure `showcase_v9.pdf`. |
| [`lean/`](lean/) | Machine-checked Lean 4 formalization (`FoliationQM`, `Lean 4.35.0` / `Mathlib v4.35.0`): **1,167** modules, **9,602** public theorems, **20,773** audited declarations, **0** proof holes (`sorry`-free), standard Mathlib axioms only (`propext`, `Classical.choice`, `Quot.sound`). |
| [`simulations/`](simulations/) | Purely real-variable polar Kähler lattice and relativistic Klein–Gordon benchmarks reproducing Table 2 and Figure 2 (free dispersion, double-slit interference, sub-barrier tunneling with quantized vortices, and $\gamma^{-3}$ boosted Klein–Gordon spreading). |

## Reproducing the Lean 4 Formalization

```bash
cd lean
lake exe cache get
lake build
lake env lean scripts/AxiomAudit.lean
python3 scripts/check_lean.py
```

See [`lean/docs/CAMPAIGN_REPORT.md`](lean/docs/CAMPAIGN_REPORT.md) for the complete target-by-target audit (note: section and theorem leading digits in the v13 campaign report shift by `+1` in the `v18` flat-numbered manuscript, e.g., `Lemma 5.3` → `Lemma 6.3`, `Theorem 5.7` → `Theorem 6.7`, `Conjecture 9.7` → `Conjecture 10.7`).

## Reproducing the Numerical Benchmarks

```bash
cd simulations
pip install -r requirements.txt
python3 simulate_foliation_qm_v10.py
```

Outputs regenerate `showcase_v9.(pdf|png|svg)` and `table2_v10_regenerated.md`.
