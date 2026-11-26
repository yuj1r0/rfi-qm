# FoliationQM: report on the Lean campaign and the manuscript changes

Written 2026-11-24. Manuscript: *The Quantum Mechanical Wave Function from
Relativistic Foliation Incompatibility*, v13 (LaTeX, SHA-256 `337a437a…259e`,
preserved unchanged in `../references/`). Line numbers below refer to that
file. Equation numbers are the v13 numbers.

This report has two parts. Part I describes the formalization: what was
proved, how it was checked, and what "proved" means for each claim. Part II
lists every change to the manuscript that came out of the campaign, with the
exact replacement text where a replacement was approved.

---

# Part I. The Lean campaign

## 1. Outcome

| | Final state |
|---|---|
| Manuscript targets recorded as proved | 69 of 69 |
| Lean modules | 1,167 (about 153,000 lines) |
| Handwritten public theorems | 9,602 |
| Declarations in the exhaustive axiom audit | 20,773 |
| Axioms used | `propext`, `Classical.choice`, `Quot.sound` only |
| Proof holes | 0 |
| Toolchain | Lean 4.35.0, Mathlib at tag `v4.35.0`, both pinned |

The 69 targets are the labelled theorems, lemmas, propositions, corollaries,
remarks and displayed equations selected as proof targets when the project
was set up. They are listed in section 4.

Sixty of the 69 are recorded as proved to the scope stated in their ledger
entry. Nine carry an explicit decision by the author, made on 2026-11-24:
four are proved against amended text, four rest on an external theorem that
is a stated hypothesis, and one is a conditional statement. Section 5 gives
the detail. No axiom was added for any of them.

## 2. What "proved" means here

- **Machine-checked.** Every theorem in the project is checked by the Lean
  kernel. The exhaustive audit lists the axioms each of the 20,773
  declarations depends on; none uses anything beyond the three standard
  axioms of Mathlib. There is no `axiom` declaration in the project and no
  unfinished proof.
- **Recorded against the manuscript.** A separate ledger,
  `docs/source_inventory.json`, records for each of the 69 targets what the
  manuscript states, what the Lean theorems establish, and any difference
  between the two. A target is "proved" when its entry has no open bridge.
- **Scope is stated per claim.** Many results are proved in flat coordinates,
  on a regular domain, or for supplied frames. That scope is written in the
  entry's `qualifications`. "Proved" never means "proved in more generality
  than the entry says".
- **Not covered.** The numerical experiments and benchmark figures of
  Section 2 are not Lean results. The ledger covers the discrete equations
  of that section (Eqs. 6–10), not the reported numbers.

## 3. How the campaign ran

**Phase 1, milestones 1–275.** The project was set up and carried to
milestone 275 by an earlier agent under a heavy per-milestone audit
procedure. At the handoff the state was 1,115 modules, 9,267 public theorems,
19,987 audited declarations, and 56 targets proved, 9 partial, 4 planned.

**Phase 2, blocks 276–321.** This phase used a cheaper audit regime agreed
with the author:

- per block: targeted build, a scan for forbidden constructs, a transitive
  axiom check of every declaration in the new module, the project
  consistency check, the full build, and one git commit;
- per chain of blocks: the exhaustive `scripts/validate.sh` (full build,
  axiom audit of every declaration, coverage rendering), run at each phase
  boundary;
- a written report at least every six blocks (`docs/progress-report-*.md`).

Phase 2 added 52 modules, 335 public theorems and 786 audited declarations,
and took the ledger from 56 / 9 / 4 to 69 / 0 / 0. Every exhaustive run
passed; one failed once in its final rendering step because of a mislabelled
ledger row (no Lean file involved) and passed after the label was corrected.

| Blocks | Subject | Outcome |
|---|---|---|
| 276–284 | Theorem 5.7(c): nodal sets of measure zero, weak derivatives, `H¹_loc` and the weak equation across an embedded codimension-two surface, in coordinates | Part (c) analysis in place |
| 285–289 | Theorem 5.7(b): the explicit degenerate vortex, winding of a non-degenerate transverse zero; Conjecture 9.7 first pass | Planned targets started |
| 290–295 | Sagnac quantization (Eq. 48); winding at a transverse zero; localized `H¹`; the polar spin-magnetization tensor; radial core asymptotics | Eq. 48 recorded as proved |
| 296–301 | Conjecture 9.7: covariant tidal density, its Euler–Lagrange equation, the normal-coordinate expansion; the finite-energy radial branch; waves and polar pairs modulo a constant phase | Eq. 154 recorded as proved |
| 302–304 | Axisymmetric reduction; the logarithmic cutoff (Eq. 50); master equation first pass | Eq. 50 recorded as proved |
| 305–310 | Theorem 5.7(c) on a smooth four-manifold with a Lorentzian metric atlas; statement (III) of the master equation from variation of the density alone | Section 1.1 recorded as proved |
| 311–316 | The cutoff estimates (Eqs. 51–52) for a general distance function | Recorded with an external-fact qualification |
| 317–320 | Remark 7.4: the polar form of the Dirac equation | Recorded against amended text |
| 321 | Theorem 5.7(b) in the distance to the nodal set of any metric | Part (b) covered as printed |

Block-by-block tables are in the eight progress reports,
`docs/progress-report-284.md` through `docs/progress-report-320.md`.

## 4. Coverage by manuscript item

"Decl." is the number of Lean declarations linked to the item in the ledger.
"Record" is `proved` unless one of the three qualifications of section 5
applies.

**Section 1. Introduction and master equation**

| Item | Title | Label | Line | Decl. | Record |
|---|---|---|---:|---:|---|
| Section 1.1 | The Master Equivalence Equation and Deductive Architecture | `sec:master_equation` | 72 | 28 | proved (earlier promotion, to confirm) |
| Eq. 1 |  | `eq:master_local_metric` | 79 | 19 | proved |
| Eq. 2 |  | `eq:master_variational_equivalence` | 92 | 332 | proved |

**Section 2. Numerical lattice equations**

| Item | Title | Label | Line | Decl. | Record |
|---|---|---|---:|---:|---|
| Eq. 6 |  | `eq:polar_kahler_lattice` | 209 | 164 | proved |
| Eq. 7 |  | `eq:polar_dR_dt` | 217 | 61 | proved |
| Eq. 8 |  | `eq:polar_dtau_dt` | 219 | 92 | proved |
| Eq. 9 |  | `eq:s1_staggered_velocity` | 223 | 65 | proved |
| Eq. 10 |  | `eq:s1_lattice_hamiltonian` | 232 | 21 | proved |

**Section 3. Geometric setup**

| Item | Title | Label | Line | Decl. | Record |
|---|---|---|---:|---:|---|
| Lemma 3.1 | Oblique Foliation Projection and the Simultaneity Wedge | `lem:simultaneity` | 344 | 29 | proved |

**Section 4. Quantum phase from contact geometry**

| Item | Title | Label | Line | Decl. | Record |
|---|---|---|---:|---:|---|
| Theorem 4.1 | Contact Mass-Shell Reeb Flow, Symplectic Capacity Invariance, and Fundamental Period $T_0 = 2\pi\hbar / (mc^2)$ | `thm:contact_period` | 385 | 331 | proved, external theorem |
| Eq. 24 |  | `eq:rotor_compton_evolution` | 418 | 150 | proved |
| Proposition 4.2 | Emergence of the de Broglie–Planck Phase Relation | `prop:debroglie` | 455 | 157 | proved |

**Section 5. Information geometry, Kähler linearization, nodal sets, ADM**

| Item | Title | Label | Line | Decl. | Record |
|---|---|---|---:|---:|---|
| Theorem 5.1 | Spatial-Slice KL Hessian from Orthogonal Circular Clock Projections and Covariant Clock-Field Quadratures | `thm:clock_sideband` | 482 | 473 | proved |
| Eq. 30 |  | `eq:s1_circle_variance` | 487 | 41 | proved |
| Eq. 31 |  | `eq:kl_fisher_expansion` | 492 | 223 | proved |
| Eq. 32 |  | `eq:sideband_averaged_lagrangian` | 502 | 39 | proved |
| Remark 5.2 | Role of the Three Constructions: Route I, Route II, and Cone-Completion Uniqueness | `rem:clock_unification_vs_stochastic` | 517 | 131 | proved |
| Lemma 5.3 | Fixed-Clock Smooth Cone-Completion and Linearization Uniqueness | `lem:uniqueness` | 545 | 404 | proved |
| Eq. 35 |  | `eq:lambda_metric` | 548 | 9 | proved |
| Eq. 36 |  | `eq:cone_angle` | 555 | 61 | proved |
| Eq. 37 |  | `eq:unique_params` | 560 | 272 | proved |
| Eq. 38 |  | `eq:nonlinear_defect` | 565 | 71 | proved |
| Remark 5.4 | Topological Compatibility and Degree-One Matching of the Clock Quantum | `rem:topological_hbar_lock` | 584 | 45 | proved |
| Theorem 5.5 | Kähler Linearization, the Born Rule, and the Klein–Gordon Equation | `thm:kahler` | 615 | 365 | proved |
| Corollary 5.6 | Non-Relativistic Limit and the Schrödinger Equation | `cor:schrodinger` | 649 | 156 | proved |
| Theorem 5.7 | Relativistic Sagnac–Wallstrom Global Equivalence Theorem | `thm:wallstrom` | 675 | 241 | proved, external theorem |
| Eq. 48 |  | `eq:sagnac_quant` | 685 | 12 | proved (earlier promotion, to confirm) |
| Eq. 50 |  | `eq:log_cutoff_wallstrom` | 704 | 60 | proved (earlier promotion, to confirm) |
| Eq. 51 |  | `eq:log_cutoff_l2_bound` | 709 | 129 | proved, external fact |
| Eq. 52 |  | `eq:weak_pde_cutoff_bound` | 714 | 64 | proved, external fact |
| Theorem 5.8 | ADM $3+1$ Hamiltonian Positivity, Dressed 4-Velocity Normalization, and Lorentz-Jacobian Measure Equivalence | `thm:adm_positivity` | 729 | 350 | proved, amended text |
| Eq. 56 |  | `eq:normal_log_rho` | 756 | 23 | proved |
| Eq. 57 |  | `eq:dilatation_coercivity_bound` | 764 | 323 | proved, amended text |
| Eq. 58 |  | `eq:spacelike_coercivity` | 769 | 73 | proved |
| Eq. 59 |  | `eq:dressed_mass_velocity` | 777 | 37 | proved |
| Eq. 60 |  | `eq:clock_vs_proper_oneform` | 785 | 20 | proved |
| Eq. 61 |  | `eq:noether_current` | 793 | 20 | proved |
| Eq. 62 |  | `eq:jacobian_density` | 798 | 29 | proved |

**Section 6. Uncertainty principle**

| Item | Title | Label | Line | Decl. | Record |
|---|---|---|---:|---:|---|
| Theorem 6.1 | Exact Heisenberg–Robertson Uncertainty Relation from Frame Fisher Information | `thm:uncertainty` | 857 | 235 | proved |
| Eq. 66 |  | `eq:p_var_decomp` | 860 | 148 | proved |
| Eq. 67 |  | `eq:heisenberg` | 865 | 42 | proved |
| Eq. 70 |  | `eq:p_fisher_bound` | 885 | 18 | proved |
| Eq. 72 |  | `eq:cramer_rao` | 898 | 125 | proved |

**Section 7. Spinor lift and Dirac factorization**

| Item | Title | Label | Line | Decl. | Record |
|---|---|---|---:|---:|---|
| Proposition 7.1 | 8-Parameter Hestenes–Takabayasi Polar Decomposition | `prop:takabayasi` | 942 | 3938 | proved |
| Eq. 77 |  | `eq:takabayasi_polar` | 945 | 258 | proved |
| Eq. 78 |  | `eq:scalar_pseudoscalar_bilinears` | 952 | 128 | proved |
| Eq. 80 |  | `eq:vector_axial_bilinears` | 964 | 156 | proved |
| Lemma 7.2 | Maurer–Cartan Spin Connection and Polar Covariant Derivative | `lem:maurer_cartan` | 989 | 437 | proved |
| Theorem 7.3 | Bidirectional Non-Abelian $SL(2,\mathbb{C})$ Spinor Lift and Dirac Equation Factorization | `thm:dirac_lift` | 1039 | 677 | proved, amended text |
| Eq. 92 |  | `eq:dirac_lagrangian_sym` | 1044 | 97 | proved |
| Eq. 93 |  | `eq:dirac_polar_lagrangian_main` | 1049 | 143 | proved |
| Eq. 101 |  | `eq:clifford_anticomm` | 1108 | 12 | proved |
| Eq. 105 |  | `eq:sigma_anticomm` | 1128 | 15 | proved |
| Eq. 107 |  | `eq:six_terms_omega` | 1142 | 7 | proved |
| Remark 7.4 | How the Osmotic Gradient $\frac{\hbar}{2}\partial_\mu\ln\rho$ Is Encoded in First-Order Dirac Dynamics via Gordon Decomposition | `rem:gordon_osmotic_bridge` | 1160 | 73 | proved, amended text |

**Section 8. Multi-particle and no-signaling**

| Item | Title | Label | Line | Decl. | Record |
|---|---|---|---:|---:|---|
| Proposition 8.1 | Exact Conditional Decomposition and Conditional Fisher Correlation Excess | `prop:fisher_excess` | 1199 | 162 | proved |
| Eq. 115 |  | `eq:fisher_excess_main` | 1210 | 113 | proved |
| Eq. 120 |  | `eq:score_zero` | 1243 | 58 | proved |
| Theorem 8.2 | Multi-Particle Kähler Linearization, Non-Local Quantum Potential, and Marginal No-Signaling | `thm:entanglement_nosignaling` | 1257 | 370 | proved |

**Section 9. Curved spacetime**

| Item | Title | Label | Line | Decl. | Record |
|---|---|---|---:|---:|---|
| Lemma 9.1 | Riemann Normal Coordinate Half-Density Expansion | `lem:rnc_half_density` | 1348 | 144 | proved |
| Theorem 9.2 | Geometric Curvature Coupling $\xi = 1/6$ Under DeWitt Symmetric Half-Density Ordering | `thm:conformal_coupling` | 1381 | 357 | proved |
| Proposition 9.4 | Exact Mass-Defect and Normalized Quantum-Force Identities | `prop:quantum_force_identity` | 1425 | 129 | proved |
| Eq. 143 |  | `eq:normalized_quantum_force` | 1438 | 55 | proved |
| Theorem 9.5 | Finite-Time Geodesic Concentration Under Controlled Quantum Force | `cor:macroscopic_geodesics` | 1450 | 287 | proved |
| Eq. 148 |  | `eq:wasserstein_concentration_bound` | 1479 | 126 | proved |
| Eq. 149 |  | `eq:q_w1_infinity_sufficient` | 1484 | 97 | proved |
| Remark 9.6 | Rates, Non-Compact Gaussian Tails, Monokinetic Velocity Spread, and Physical Scale Regimes | `rem:wkb_rates_tails` | 1511 | 100 | proved |
| Conjecture 9.7 | Compton Geodesic-Cell Tidal Dispersion Model | `thm:tidal_dispersion` | 1526 | 48 | proved, conditional |
| Eq. 154 |  | `eq:tidal_KG_eq` | 1538 | 38 | proved (earlier promotion, to confirm) |

## 5. The nine claims recorded by author decision

| Claim | Kind | What is proved | What is not machine-checked |
|---|---|---|---|
| Theorem 5.8 (`thm:adm_positivity`) and Eq. 57 (`eq:dilatation_coercivity_bound`) | Amended text | The conditional estimate on a region of the future-timelike domain, and the Gaussian example regionally for a short time | The printed claim that the bound holds for a free Gaussian whenever σ₀ > ℓ_C/√2; it has counterexamples |
| Theorem 7.3 (`thm:dirac_lift`) | Amended text | The exact identity for K₂ − ρm²c² and its limit as ∂β → 0 | The printed reduction as β → 0; it has counterexamples |
| Remark 7.4 (`rem:gordon_osmotic_bridge`) | Amended text | The polar form of the Dirac equation as two first-order conditions, the divergence form, the Fisher term on solutions | The printed attribution of the osmotic gradient to the transverse connection terms of Eq. 94 (`eq:canonical_P_L`) |
| Theorem 4.1 (`thm:contact_period`) | External theorem | Everything else in the theorem | Gromov's non-squeezing theorem (cited) |
| Eqs. 51–52 (`eq:log_cutoff_l2_bound`, `eq:weak_pde_cutoff_bound`) | External fact | The estimates for every distance function that is Lipschitz in the chart and bounded below by the coordinate distance to the nodal set | That the distance of a general smooth Riemannian metric has those two properties on compact subsets of a chart (standard) |
| Theorem 5.7 (`thm:wallstrom`) | External theorem | Parts (a), (b), and all of (c) that the manuscript argues itself; the continuation step given a regular solution | The global finite-energy Cauchy theorem (Bär–Tagne Wafo, Theorem 13 and Corollary 14, cited) |
| Conjecture 9.7 (`thm:tidal_dispersion`) | Conditional | Everything derived from the ansatz | The physical ansatz itself, which is the hypothesis |

For the external theorems the Lean side is uniform: the theorem enters as an
explicit hypothesis of the relevant Lean statement. For Theorem 5.7 that
hypothesis is "a field regular in every chart and almost everywhere equal to
the weak extension" in `MetricAtlasNodalWeakKG.atlas_continuation`.

### Four earlier promotions to confirm

During Phase 2 four targets were moved to "proved" in the course of proving,
each flagged in the report of its chain. They are not decisions of the
author yet.

| Claim | Report | Point to check |
|---|---|---|
| Eq. 48 (`eq:sagnac_quant`) | `progress-report-295.md` | The single-valued circle phase of hypothesis (ii) is a hypothesis in the Lean statement, as in the manuscript |
| Eq. 154 (`eq:tidal_KG_eq`) | `progress-report-301.md` | The covariant divergence is in divergence form; the variation is for \|ψ\| > 0 with the external tensor held fixed |
| Eq. 50 (`eq:log_cutoff_wallstrom`) | `progress-report-304.md` | The displayed cutoff is Lipschitz, not smooth; the manuscript's "up to smoothing the junctions" is not needed for the estimates |
| Section 1.1 (`sec:master_equation`) | `progress-report-310.md` | Proved for one positive density and one real clock; circle-valued clocks around nodes belong to Theorem 5.7 |

### Two readings recorded in the last blocks

- **Theorem 5.7(b).** The manuscript says the core is "governed by a radial
  equation" with bounded lower-order coefficient. The ledger takes that as a
  hypothesis. Deriving the radial equation from the wave operator for a
  general metric and curved nodal surface is recorded as not claimed by the
  source and not proved. For the flat axis the derivation is proved.
- **Remark 7.4.** The axial covector `A_μ` is defined with the Levi-Civita
  symbol in the frame. The coordinate form, equal for an
  orientation-preserving frame, is not derived.

## 6. Where things are

All paths are relative to the Lean project folder `FoliationQM/`.

| File | Content |
|---|---|
| `FoliationQM/*.lean` | The 1,167 modules |
| `docs/source_inventory.json` | The ledger: one entry per target, with statement, assumptions, qualifications and linked declarations |
| `docs/coverage.json`, `docs/SOURCE_MAP.md` | One row per public theorem, with the targets it serves |
| `docs/ERRATA.md` | Every manuscript issue recorded during the campaign, and the approved replacement texts |
| `docs/V13_CLAUSE_REVIEW.md` | Clause-by-clause review of Sections 5.8 and 7 with links to declarations |
| `docs/AXIOM_AUDIT.md`, `docs/axiom-audit.json` | The axioms of every declaration |
| `docs/progress-report-*.md` | Reports for blocks 276–321 |
| `scripts/validate.sh` | The exhaustive check; about 35 minutes |

To re-run the full check from the project folder:

```bash
./scripts/validate.sh
```

---

# Part II. Changes to the manuscript

The reference file has not been edited. The changes fall into four groups:

- **A.** Three replacements approved by the author. These are required for
  the ledger to match the printed text.
- **B.** Small edits that follow from A or from the last blocks. Suggested
  wording is mine and has not been approved.
- **C.** Issues recorded in the errata log earlier in the campaign. Each is a
  place where the printed sentence needs a qualifier or a precise reading.
- **D.** Places checked where no change is needed.

Adding the new displayed equations in A2 and A3 shifts the equation numbers
after them. The ledger keeps the v13 numbers.

## A. Approved replacements

### A1. Theorem 5.8(ii), lines 762–772

**Replace** the sentence beginning "Consequently, on any smooth subluminal
wavepacket on Σ_O", Eqs. 57–58, and the parenthesis "(which holds for a free
Gaussian wavepacket whenever σ₀ > ℓ_C/√2)".

**Why.** The parenthesis is false as printed. Width alone does not decide the
bound: at σ₀ = ℓ_C two free Klein–Gordon solutions with the same Gaussian
modulus give opposite outcomes. For the unboosted positive-frequency packet
the whole slice is never in the future-timelike domain: at every width that
domain meets the initial slice in a finite ball. The bound then persists on a
compact region only for a duration depending on the region.

**What changes.** The integrals are taken over a region `K` instead of the
whole slice, and a correct Gaussian sentence follows Eq. 58. The labels of
Eqs. 57 and 58 are kept.

```latex
Consequently, for any measurable region $K \subseteq \Sigma_{\mathcal{O}}(t) \cap \mathcal{U}_{\text{timelike}}$ with $\sup_{K} |\mathbf{v}_{\text{eff}}| \le v_{\max} < c$ on which the weighted squares below are integrable and which satisfies the non-circular dilatation bound
\begin{equation}
\label{eq:dilatation_coercivity_bound}
\left\| \nabla \cdot \mathbf{v}_{\text{eff}} + D_t \ln a \right\|_{L^2(K,\rho_{\text{inv}})} < (c - v_{\max}) \left\| \nabla \ln\rho_{\text{inv}} \right\|_{L^2(K,\rho_{\text{inv}})},
\end{equation}
the integrated osmotic 4-momentum norm over $K$ is strictly spacelike:
\begin{equation}
\label{eq:spacelike_coercivity}
\begin{aligned}
&\int_{K} d^3x \, \rho_{\text{inv}}(x) \, \eta^{\mu\nu} p_\mu^{\text{(info)}} p_\nu^{\text{(info)}} \\
&\qquad = \frac{\hbar^2}{4}\int_{K} d^3x \, \rho_{\text{inv}}(x)\Big[ (\partial_n \ln\rho_{\text{inv}})^2 - |\nabla \ln\rho_{\text{inv}}|^2 \Big] < 0.
\end{aligned}
\end{equation}
The bound is a genuine hypothesis and is not fixed by the packet width alone. For the unboosted positive-frequency Gaussian packet with $\rho_{\text{inv}}(0,\mathbf{x}) = \exp(-|\mathbf{x}|^2/2\sigma_0^2)$, at every width $\sigma_0 > 0$ the set $\Sigma_{\mathcal{O}}(0) \cap \mathcal{U}_{\text{timelike}}$ is an open ball $|\mathbf{x}| < r_*(\sigma_0)$ of finite radius, and for every compact $K$ of positive volume inside this ball there is $T(K) > 0$ such that for all $|t| \le T(K)$ one has $K \subset \mathcal{U}_{\text{timelike}}$, $\sup_K |\mathbf{v}_{\text{eff}}| \le c/2$, and Eq.~\eqref{eq:dilatation_coercivity_bound} holds on $K$ with $v_{\max} = c/2$. The duration $T(K)$ cannot be chosen uniformly as $K$ shrinks to the centre.
```

**Consistency.** In the proof, lines 818–824, the three `L²(ρ_inv)` norms
are then norms over `K`. Writing `L^2(K,\rho_{\text{inv}})` there is optional
but consistent.

### A2. Theorem 7.3(iii), line 1082

**Replace** the clause from "which in the irrotational-spin,
small-chiral-angle limit" up to "of $s^\nu$ and $u^\nu$". End Eq. 97
(`eq:sl2c_fisher_metric_main`) with a full stop and keep the sentence on
stationary variation that follows.

**Why.** The clause compares the frame-gradient form with the scalar
Lagrangian, but that form has neither the phase square ρ(∂S)² nor the mass
term. For a constant unit spinor K₂ is zero while the scalar integrand is
−m²c². And β → 0 is not enough: with β = ε·sin(x⁰/ε) the angle tends to zero
uniformly but the action on a fixed box differs by ℏ²π/4. What must vanish is
the gradient of β.

**What changes.** One new displayed identity (label
`eq:spinor_scalar_reduction`) and two sentences.

```latex
Where the spin-frame connection is irrotational ($da^{\text{(spin)}} = 0$, so that locally $a_\mu^{\text{(spin)}} = \partial_\mu S$), the mass-completed quadratic form satisfies the exact identity
\begin{equation}
\label{eq:spinor_scalar_reduction}
\begin{aligned}
\mathcal{K}_2 - \rho m^2 c^2 &= \rho\left[ (\partial_\mu S)(\partial^\mu S) - m^2 c^2 + \frac{\hbar^2}{4}(\partial_\mu \ln\rho)(\partial^\mu \ln\rho) \right] - \frac{\hbar^2}{4}\rho(\partial_\mu \beta)(\partial^\mu \beta) \\
&\quad - \frac{\hbar^2}{4}\rho \left( (D_\mu^{\text{FW}} s_\nu)(D_{\text{FW}}^\mu s^\nu) - \frac{1}{c^2}(\partial_\mu u_\nu)(\partial^\mu u^\nu) \right),
\end{aligned}
\end{equation}
whose first bracket is the integrand of the scalar action \eqref{eq:coupled_action}. Hence, for a family of regular spinor fields with convergent density, phase gradient and frame gradients and with vanishing chiral-angle gradient, $\partial_\mu \beta \to 0$, the form $\mathcal{K}_2 - \rho m^2 c^2$ converges pointwise to the scalar Hamilton--Jacobi--Fisher Lagrangian augmented by the limiting invariant quadratic gradients of $s^\nu$ and $u^\nu$, and its integral converges under an integrable majorant. Smallness of $\beta$ alone does not suffice.
```

### A3. Remark 7.4, line 1166

**Replace** the last two sentences of the remark, from "Substituting the
polar derivative" to the end. Keep the first half, with the Gordon
decomposition (Eq. 110).

**Why.** The printed text attributes the lock on the osmotic gradient to the
combination u₁^μ ω_{μ20} + u₂^μ ω_{μ01} of Eq. 94, with an ellipsis in place
of the computation. Carrying the computation out gives a different result:
the osmotic gradient is locked to the divergences of the four tetrad legs,
and the combination named in the remark fixes s^μ ∂_μ β instead.

**What changes.** The full magnetization tensor replaces the ellipsis; four
new displayed equations (labels `eq:polar_dirac_residual`,
`eq:polar_dirac_pair`, `eq:osmotic_frame_lock`, `eq:fisher_from_frame`).

**One point to note.** The axial covector `A_μ` is written with the
Levi-Civita symbol in the frame, which is the form proved. If you prefer the
coordinate form `½ ε_{μναβ} u_a^α u_b^β ω^{νab}` in print, it is equal for the
orientation-preserving frames of a rotor field, but that equality is not
formalized.

```latex
In polar variables the spin-magnetization tensor is $\bar{\psi}\sigma^{\mu\nu}\psi = \rho\left[\cos\beta\,(u_1^\mu u_2^\nu - u_2^\mu u_1^\nu) - \sin\beta\,(u_0^\mu u_3^\nu - u_3^\mu u_0^\nu)\right]$. The lock between the osmotic gradient and the frame is made explicit by the polar form of the Dirac equation itself. Substituting Eq.~\eqref{eq:d_psi_polar_main} into the Dirac operator gives, on $\rho > 0$, the exact identity
\begin{equation}
\label{eq:polar_dirac_residual}
(i\hbar\gamma^\mu\partial_\mu - mc)\psi = \frac{i\hbar}{2}\gamma^\mu\left( D_\mu^{(\rho)} + i D_\mu^{(\beta)}\gamma_5 \right)\psi,
\end{equation}
with the real covectors
\begin{equation}
\label{eq:polar_dirac_pair}
D_\mu^{(\rho)} \equiv \partial_\mu\ln\rho - T_\mu - \frac{2mc}{\hbar}\sin\beta\, s_\mu, \qquad
D_\mu^{(\beta)} \equiv \partial_\mu\beta - A_\mu - \frac{2mc}{\hbar}\cos\beta\, s_\mu,
\end{equation}
where $T_\mu \equiv u^a_{\ \mu}u_b^\nu\,\omega_{\nu a}^{\ \ \, b}$ is the trace and $A_\mu \equiv \frac{1}{2}\,u^d_{\ \mu}\,\eta_{de}\,\epsilon^{ecab}\,u_c^\nu\,\omega_{\nu ab}$ the axial part of the Maurer--Cartan connection ($\epsilon^{0123} = +1$). Hence the Dirac equation holds on $\rho > 0$ if and only if $D_\mu^{(\rho)} = 0$ and $D_\mu^{(\beta)} = 0$. Since $u_a^\mu T_\mu = -\partial_\mu u_a^\mu$, the first condition reads
\begin{equation}
\label{eq:osmotic_frame_lock}
\frac{\hbar}{2}\,u_a^\mu\partial_\mu\ln\rho = -\frac{\hbar}{2}\,\partial_\mu u_a^\mu - mc\,\sin\beta\,\delta_a^3
\quad\Longleftrightarrow\quad
\partial_\mu(\rho\, u_a^\mu) = -\frac{2mc}{\hbar}\,\rho\sin\beta\,\delta_a^3,
\end{equation}
so the osmotic gradient is locked to the divergences of the four tetrad legs. The transverse boost-precession combination of Eq.~\eqref{eq:canonical_P_L} enters the second condition instead, through $-u^\mu P_\mu(L) = \frac{\hbar c}{2}s^\mu A_\mu$, and fixes $s^\mu\partial_\mu\beta$. Squaring the first condition expresses the Fisher term of Eq.~\eqref{eq:spinor_quadratic_exact} on Dirac solutions as
\begin{equation}
\label{eq:fisher_from_frame}
\frac{\hbar^2}{4}\rho(\partial_\mu\ln\rho)(\partial^\mu\ln\rho) = \frac{\hbar^2}{4}\rho\,\eta^{ab}(\partial_\mu u_a^\mu)(\partial_\nu u_b^\nu) - \hbar mc\,\rho\sin\beta\,\partial_\mu s^\mu - m^2c^2\rho\sin^2\beta.
\end{equation}
```

## B. Suggested small edits (not yet approved)

| Where | Printed | Suggested | Reason |
|---|---|---|---|
| Remark 5.9, item 2, line 834 | Sign reversals of −∂_n S occur "outside the quasi-monochromatic regime" | Drop that phrase, or add "(this already occurs in the far tail of a positive-frequency Gaussian packet at every width)" | The Lean result behind A1: the rest Gaussian has a past-timelike current outside a finite ball at every width |
| Proof of Theorem 5.7(c), line 720 | The smooth solution ψ_sm is introduced with only the Bär–Tagne Wafo citation | Add a citation for existence of a smooth solution from smooth data (Bär, Ginoux and Pfäffle, *Wave Equations on Lorentzian Manifolds and Quantization*) | The cited Theorem 13 and Corollary 14 appear to concern finite-energy well-posedness; smooth existence appears to come from the earlier book. **Not verified against the paper verbatim; check before editing** |
| Walkthrough, line 145 | "Single-valued circle sections q … quantize circulation … and extend smoothly across codimension-2 nodal sets" | "… quantize circulation, and the field ψ = Rq extends smoothly across …" | A circle-valued phase with nonzero winding cannot extend through the node; the extension concerns ψ |
| Eq. 30, line 488 | The display ends "… δ^{ij} > 0" | End the display at δ^{ij} and say "which is positive definite" | The off-diagonal entries are zero, so "> 0" cannot be read entrywise |
| Proof of Theorem 5.8, lines 818–824 | Norms `L²(ρ_inv)` | `L²(K, ρ_inv)` | Consistency with A1 |

## C. Issues recorded in the errata log

These were recorded in `docs/ERRATA.md` during the campaign, most of them in
Phase 1. In each case the Lean theorems prove a precise version; the printed
sentence is broader or leaves a hypothesis implicit. No wording has been
drafted or approved for these. I have not re-examined each one in this
session; treat the list as a checklist.

### C1. Sentences that need an added hypothesis or a narrower claim

| Where | Issue |
|---|---|
| Corollary 5.6 (`cor:schrodinger`), line 649 | "Small boost", "slow phase" and "leading order" need an explicit family, a norm, and a bound on c⁻² ∂_t² Ψ. The exact factored equation is proved; convergence needs the quantitative statement |
| Remark 5.2, line 520 | "Raw Fisher functionals coincide as g → 1" needs a convergence mode that controls derivatives. Uniform convergence of positive smooth factors is not enough; there is an explicit counterexample on a fixed box |
| Remark 9.6, line 1517 | For a fixed period T₀ the set T₀·ℤ is not dense in ℝ. The proved statement is approximation by lattice points along a family with T₀ → 0. Also M(Δx)²/ℏ → ∞ alone does not give T₀ → 0 when widths vary |
| Theorem 9.5 and Eq. 149, lines 1450–1484 | The force estimate on a noncompact region needs uniform control of the inverse-metric raising operator; this does not follow from Lipschitz control of the geodesic right-hand side. Small q alone does not control ∇q |
| Eq. 8 and the energy statement near line 231 | With a positive regulator the displayed equation changes the Hamiltonian flow; the geometric energy is then not conserved. Exact conservation holds for the unregularized flow |
| Eq. 9, line 223 | At a replicated endpoint the site velocity can have a first-order spatial error; the second-order estimate is for interior sites |

### C2. Statements that are correct under a precise reading

| Where | Reading under which it is proved |
|---|---|
| Eq. 60 and line 791 | The clock form on the four-velocity gives the clock-time rate M_eff/m; M_eff c²/ℏ is the angular frequency, with signed phase derivative −M_eff c²/ℏ |
| Eq. 1 and Lemma 5.3 | The unweighted amplitude-phase metric is Euclidean; the density-normalized one is cylindrical and puts ρ = 0 at infinite distance. Coefficient matching must hold for all ρ > 0 and all increments |
| Eq. 38 (`eq:nonlinear_defect`) | "Vanishes identically iff" refers to the coefficient, or to vanishing for all admissible fields; one particular solution can have zero defect at other couplings |
| Lemma 3.1 and Proposition 4.2 | The equal-time shift is nonzero only for nonzero v·dx; the nonzero spatial-phase limit fixes a nonzero velocity as c grows |
| Theorem 5.8 | Positive amplitude does not imply timelike phase momentum; velocity, dressed mass and flux density are stated on the regular future-timelike domain |
| Theorem 6.1 | The momentum variance for Ψ ∈ H¹ is a quadratic-form norm; logarithmic derivatives need an almost-everywhere treatment of zeros |
| Proposition 7.1 | The regular domain is strict positivity of the scalar–pseudoscalar invariant; a nonzero spinor can have zero invariant density. Existence of a Spin structure is a separate question |
| Theorem 8.2 | Global unitary cancellation is distinct from constructing the propagators; current claims need their operator-domain hypotheses |
| Theorem 9.2 | The half-density ordering is an input. Covariance alone does not force the coefficient 1/6 |
| Conjecture 9.7 | Its label reads "theorem" in the source labels; it is a conjecture, and the amplitude variation holds on \|ψ\| > 0 |
| Remark 5.4 | Already corrected in v13: single-valuedness permits every positive integer k; degree one selects k = 1 |

## D. Checked, no change needed

- **Summary table, lines 1582–1594.** The rows for the ADM theorem and the
  Dirac lift remain accurate after A1–A3. The ADM row says the coercivity
  bound is proven "on 𝒰_timelike", which matches the regional wording of A1.
- **Abstract and walkthrough.** Neither states the Gaussian width claim, the
  scalar limit of the spinor theory, or the transverse-connection attribution.
  A1–A3 do not touch the headline claims.
- **Companion files.** The v11 supplement, the simulation script and the
  regenerated table do not repeat the three amended claims.
- **Benchmark attribution.** The errata log notes that the ray-L² error
  4.90 × 10⁻⁸ belongs to the double-slit benchmark. Lines 247 and 275 of v13
  already attribute it that way.
- **Theorem 5.7(c), cutoff.** "Up to smoothing the junctions" can stay; the
  estimates are proved for the displayed Lipschitz cutoff without smoothing.

## Checklist for editing the manuscript

1. Paste A1, A2 and A3.
2. Decide on the five small edits in B; check the citation in the second row
   against the paper first.
3. Go through C1 and decide which sentences to qualify.
4. Confirm or revert the four earlier promotions in section 5.
5. If the text of A1–A3 is changed while editing, tell the formalization side
   so that `docs/ERRATA.md` and the ledger stay in step with what is printed.
