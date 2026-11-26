# Source qualifications and open statement issues

The supplied references are preserved unchanged. These notes govern interpretation of the formalization targets; they are not claims that the full manuscript has been checked in Lean. Stable labels and exact source line numbers are recorded in `source_inventory.json`. Paths in that inventory are relative to the project root.

## Editorial qualifications already identified in the handoff

1. **Walkthrough Step 5 (`sec:walkthrough`).** The field extending smoothly across a nodal set is `psi = R q`. A circle-valued phase `q` with nonzero winding generally cannot extend continuously through the node. The detailed hypotheses of `thm:wallstrom` govern the extension.
2. **Abstract benchmark attribution.** The reported `4.90e-8` same-lattice ray-L2 error belongs to the double-slit benchmark. The tunneling figures are `1.87e-5` at `T=4.2` and `3.85e-5` at `T=9.0`. These are supplied numerical observations, not Lean results, and this source inspection did not repeat the experiments.
3. **Covariance (`eq:s1_circle_variance`).** The trailing `>0` cannot mean positivity of every matrix entry: off-diagonal entries are zero. The correct statement is positive definiteness of `(ellC^2/2) I` when `ellC>0`.

## Precise interpretations required by the specification

- **Clock time and angular phase (`eq:clock_vs_proper_oneform`, main line 791).** The clock form evaluated on the physical four-velocity gives the clock-time rate `M_eff/m`. The magnitude `M_eff c²/ℏ` in the prose is the angular frequency, with signed phase derivative `−M_eff c²/ℏ` in the displayed equation. Both rates follow from the same real phase.

- **Topological matching (`rem:topological_hbar_lock`).** V13 already contains the correction. Single-valuedness around an elementary physical-clock vortex permits every positive integer `k = hbar/hbar_eff`, hence `lambda = hbar^2/(4 k^2)`. The `k=2` choice has angle `4*pi`. Degree one or smooth Euclidean completion is an additional condition selecting `k=1`; there is no pending replacement fragment to apply.
- **Metric and cone (`eq:master_local_metric`, `lem:uniqueness`).** The unweighted two-dimensional amplitude-phase metric is Euclidean. Its density-normalized counterpart is cylindrical and places `rho=0` at infinite distance. A scalar angle equality does not prove smooth metric completion. Power-pullback coefficient matching must hold for all positive densities and all tangent increments; equality at `rho=1` alone is insufficient.
- **Nonlinear defect (`eq:nonlinear_defect`).** “Vanishes identically iff” refers to the coefficient, or to vanishing for all admissible fields. A particular constant-amplitude solution may have zero defect at other couplings.
- **Clock phase signs (Section 2 and startup numerical overview).** The full physical clock has `Phi=-omega0*tau_clock`. The manuscript's reduced lag is `delta_tau_lag=t-tau_clock=tildeS/(m*c^2)` and its reduced numerical phase is `+omega0*delta_tau_lag`. The startup's short example writes a minus sign with the unqualified symbol `delta_tau`; that symbol must denote a clock offset rather than this reduced lag, or the sign convention must be changed consistently. Generic real-phase edge identities avoid this naming ambiguity. Any later ODE instantiation must use the manuscript's explicitly defined lag convention.
- **Simultaneity (`lem:simultaneity`, `prop:debroglie`).** The equal-time shift is nonzero only for nonzero `v dot dx_space`; positive worldline proper time requires `dt>0`. The nonzero spatial-phase limit fixes nonzero velocity as `c` grows; the condition `|v|/c -> 0` alone also permits `v -> 0`.
- **Timelike interpretation (`thm:adm_positivity`).** Positive amplitude does not imply timelike phase momentum. Proper velocity, positive dressed mass, and positive current-flux density are stated only on the regular future-timelike domain. Quantized circulation belongs to the closed action-clock form, not generally to the weighted physical proper-time form.
- **Weak extension (`thm:wallstrom`).** Finite positive local auxiliary-metric energy, tubular cutoff construction, weak testing, and the full finite-energy Cauchy class are distinct requirements. Hyperbolic equations do not smooth arbitrary weak solutions. The special radial vortex asymptotic requires a bounded regular radial lower-order coefficient; the source's explicit degenerate-time vortex illustrates why winding alone is insufficient.
- **Uncertainty (`thm:uncertainty`).** The momentum variance for `Psi in H1` is a quadratic-form norm. An expectation of the square of an unbounded momentum operator would need a stronger domain. Logarithmic score/phase derivatives require an almost-everywhere treatment of zeros. Gaussian equality classification is a separate target.
- **Takabayasi decomposition (`prop:takabayasi`).** Strict positivity of the scalar-pseudoscalar invariant gives the regular domain. The four-pi angle and Spin rotor descend through the simultaneous sign relation. The quotient section is smooth; the unique half-open observable-angle representative is pointwise. The existence obstruction for an independent Spin structure is a separate problem. [Clause review](V13_CLAUSE_REVIEW.md)
- **Dirac lift scalar limit (`thm:dirac_lift`, part iii).** The massive scalar comparison uses K₂ − ρm²c². For the constant unit-density, constant-phase regular field, K₂ is zero and the scalar integrand is −m²c². Even a flat spin-axis connection and uniformly vanishing chiral angle can leave an action gap of ℏ²π/4 on an explicit finite box. The verified limit retains the surviving frame-gradient terms and requires control of the actual derivatives. [Clause review](V13_CLAUSE_REVIEW.md)
- **No-signaling (`thm:entanglement_nosignaling`).** Global unitary cancellation is distinct from construction/factorization of time-dependent propagators. Current and time-derivative claims need their function-space and operator-domain hypotheses. Finite partial trace is not an infinite-dimensional trace-class construction.
- **Curvature (`thm:conformal_coupling`).** The prescribed half-density ordering is an input. Neither a polynomial Hessian contraction nor covariance alone proves that every covariant scalar operator has curvature coefficient `1/6`.
- **Concentration (`cor:macroscopic_geodesics`).** This historical label names Theorem 9.5. Initial velocity concentration and integrated full spacetime force control are necessary hypotheses of the stated argument. Small `q` alone does not control `grad q`. First-moment concentration does not imply compact support in a shrinking worldtube.
- **Tidal model (`thm:tidal_dispersion`).** Despite its historical label, this is Conjecture 9.7. Conditional amplitude variation on `|psi|>0`, with external `u` held fixed, does not validate the physical smearing ansatz or extend its nonlinear equation through nodes.
- **Numerical evolution.** Signed-amplitude canonicalization and the geometric edge identity are exact for all real amplitudes, including zero. The regularization `1/R -> R/(R^2+epsilon_reg^2)` changes the exact complex ODE near nodes. A continuous-time norm identity does not establish exact RK4 or floating-point conservation. Natural rectangular lattice norm weights and trapezoidal comparison weights must remain distinct.

## Source assertions needing further specification

- **Free-Gaussian coercivity parenthetical (Theorem 5.8(ii), line 767).** At one Compton width, two globally smooth free KG solutions with the same Gaussian initial modulus and different normal data give opposite outcomes. For the unboosted positive-frequency preparation at every positive width, the strict inequality holds on the full initial future ball. Every prescribed compact positive-volume subset retains the bound over a region-dependent, two-sided laboratory interval. The boundary sphere has zero current at positive density, and the entire exterior is past-timelike. A common duration for all shrinking centered regions has a counterexample. [Verified Gaussian clauses](V13_CLAUSE_REVIEW.md)
- **Schrodinger limit (`cor:schrodinger`).** “Small boost,” “slow phase,” and “leading order” need an explicit family, norm/topology, and bound on `c^(-2)*partial_t^2 Psi`. The exact factored equation is a valid intermediate target; a convergence theorem needs the additional quantitative statement.
- **Gordon elimination (`rem:gordon_osmotic_bridge`).** The magnetization formula contains an ellipsis and the elimination of frame variables is described in prose. Expand these into explicit hypotheses and equations before assigning complete coverage.

The supplement's earlier repairs concerning positive local energy, logarithmic cutoff denominator, rotor orientation/rates, KL normalization, ADM mixed projector, and controlled WKB force are already reflected in v13. They should be preserved, not reapplied as edits to the references. No new manuscript theorem is marked disproved by this inventory pass.

## Verified regular-spinor domain boundary

`SpinorRegularity` checks the source's strict regularity requirement directly. The actual spinor `(1,0,1,0)` is nonzero and has Hermitian square `psi†psi=2`, while its scalar and pseudoscalar invariants both vanish, hence its invariant density is zero. This is a proved counterexample to replacing the source regular domain by nonzero spinors or positive Hermitian norm; it is not a correction to the source's stated strict domain. The forward polar ansatz has invariant density rho under the recorded matrix premises, without establishing reconstruction of every regular spinor.

## Milestone 149 — Sharp Gaussian slice coercivity, realized initial data, and Fourier reconstruction

The width σ₀>ℓ_C/√2 in Theorem 5.8(ii), line 767, specifies the initial spatial profile. Even at σ₀=ℓ_C, smooth Gaussian data compatible with the KG equation on the entire initial slice have either sign of the integrated osmotic square. Its sign also depends on the normal derivative. A positive-frequency preparation fixes the normal datum through a spatial Fourier multiplier and requires a separate domain check.

## Milestone 151 — Global free Gaussian waves with prescribed Cauchy data

The unrestricted interpretation of the Gaussian parenthetical in line 767 is disproved for a Gaussian initial modulus and freely specified second KG datum. For σ=ℓ_C and ω>0, the globally smooth free field with initial derivative (1/σ−iω)ψ fails the strict inequality on the entire future-timelike initial slice, whereas the field with initial derivative −iωψ satisfies it at the same width. A statement for a specified positive-frequency preparation needs its own time and domain conditions.

## Milestone 153 — The physical Gaussian current, its future domain and the exact osmotic integral

At σ₀=ℓ_C the unboosted positive-frequency rest packet has negative temporal current on an open set of positive volume, despite its strictly positive initial Gaussian modulus. Between that set and the center the full four-current is zero at positive density. Thus the whole initial observer slice does not belong to the regular future-timelike phase domain. At every positive width the complete initial future region satisfies the strict inequality with v_max=0. The integrated osmotic square is negative even over the full initial slice, by direct evaluation. Milestone 151 separately disproves width-only sufficiency for unrestricted second data. The conditional coercivity theorem and its verified regional instances retain their stated hypotheses.

## Milestone 159 — Physical current, regional coercivity and nonnodal zeros near the transition sphere

A precise regional version of the free-Gaussian parenthetical in line 767 is now available. Specify the unboosted positive-frequency spectrum and choose any compact positive-volume part of its initial future ball. There exists a positive laboratory duration for which Eqs. 57–58 hold throughout on that fixed set. At every sufficiently small positive time, sufficiently small centered coordinate balls instead have a positive restricted osmotic integral and violate Eq. 57. The original future-oriented whole-slice premise already fails on the initial observer slice at every finite width. Direct evaluation still gives a strictly negative whole-slice initial osmotic integral. Its sign at arbitrary later times is a separate question.

## Milestone 166 — Continuous-time energy balance and strict loss on a regularized solution

At positive regulator width, the displayed Eq. 8 changes the geometric Hamiltonian flow. In the checked two-site example, the initial derivative of the normalized geometric energy is −3ε²/((1+ε²)(4+ε²)), whereas rectangular mass remains constant. Line 231 reports saved-time benchmark variations. The exact conserved energy law applies to the unregularized flow on a regular chart and the raw Hermitian complex evolution.

## Milestone 170 — Interior site-velocity consistency and the sharp replicated-endpoint error

For Eq. 9, the second-order link estimate uses the physical edge midpoint. The interior centered velocity at fixed regulator approaches c²R²τ′/(R²+ε²). At a replicated endpoint an incoming or outgoing link is identically zero; even with a compatible zero continuum flux the resulting endpoint velocity can have first-order spatial error.

## Milestone 176 — Observer Fisher convergence and an exact fixed-box counterexample

The statement at v13 line 520 that raw Fisher functionals coincide as g tends to one requires a convergence mode controlling derivatives and integrals. Uniform convergence of positive smooth factors alone is insufficient even on a single bounded box. One sufficient hypothesis is uniform amplitude control and convergence to zero of the observer-weighted factor-score energy. The fixed-box example uses smooth prescribed polar phases and makes no Klein–Gordon claim for that oscillatory family.

## Milestone 218 — Uniform auxiliary-norm bounds for the actual coordinate quantum force

Uniform-force hypothesis clarification: on a noncompact chart, the force estimate needs uniform control of the inverse-metric raising operator in the chosen auxiliary norm. The proof does not infer this from uniform Lipschitz control of the geodesic right-hand side. The startup/supplement controlled-coefficient version is the target; the broader literal reading of v13 controls (1)–(3) is not established. Compact common regions with continuous nonsingular background supply the required inverse bound. This is a recorded scope qualification, not a claimed counterexample family of KG solutions.

## Milestone 219 — Actual gradient-supremum envelopes and the qualified force sufficient condition

The recorded eq:q_w1_infinity_sufficient target is now complete under its explicit startup/supplement uniform coefficient qualification. This label does not prove the unqualified literal reading of v13 controls (1)–(3) on arbitrary noncompact regions: inverse-raising and coordinate-time/ratio controls remain explicit, with compact inverse bounds separately derived in 218. The actual supremum is pointwise and is not replaced by an almost-everywhere representative. General moving-region measurability and finite interval integrability are explicit; the compact fixed-region case derives both. Actual uniform q-smallness produces normalization positivity eventually, not at every index. The constructed force envelope is a conclusion, not the inherited transport-context assumption A. The global macroscopic-geodesic and Wasserstein claims remain open.

## Milestone 231 — Actual good-set current concentration, Gaussian support and corrected scale limits

The physical-scale sentence in v13 rem:wkb_rates_tails (line1517) requires a precise interpretation. For every fixed positive period T0, the set T0*Z is not dense in R: the open interval (0,T0) contains no lattice point. The proved family statement is uniform approximation of every real x by the actual lattice point floor(x/T0_i)*T0_i, with error less than T0_i, under a genuine positive period family T0_i tending to zero.

Writing r_i=M_i*width_i^2/hbar_i, the condition r_i tending to infinity alone does not imply T0_i tending to zero when widths vary. The formal fixed-MassiveParameters example width_n=n+1 has diverging r_n and constant positive period. At common speed c, the exact identity T0_i*r_i=(2*pi/c^2)*width_i^2 shows that eventual bounded width is a sufficient additional condition; narrowing width is a stronger sufficient regime. Separately, r_i tending to infinity implies the scalar T/(2*r_i) tending to zero. That scalar limit is not an analytic estimate of KG wavepacket spreading, and no cosmological-duration spreading claim or empirical neutron/planet calculation is certified here. The preserved original source is unchanged; these qualifications delimit the formal analytical completion.

## Author-approved statement amendments (2026-11-24)

The author approved the replacement texts below on 2026-11-24. The ledger records `thm:adm_positivity`, `eq:dilatation_coercivity_bound`, `thm:dirac_lift` and `rem:gordon_osmotic_bridge` as proved against these amended statements. The preserved v13 reference is unchanged and still prints the earlier wording at the lines named; that earlier wording is not proved and has the counterexamples recorded above.

### Theorem 5.8(ii), v13 lines 762–772

Replaces the sentence beginning "Consequently, on any smooth subluminal wavepacket", Eqs. 57–58 and the Gaussian parenthesis. The integrals are taken over a region `K` and the Gaussian sentence follows Eq. 58.

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

Lean: `SpacelikeOsmoticIntegral.of_scalar_extremal`, `GaussianFutureCurrentGeometry.futureRegion_eq`, `GaussianCompactFutureTube.exists_tube`, `GaussianPrescribedRegion.interval`, `GaussianShrinkingBallFailure.no_common_interval`.

### Theorem 7.3(iii), v13 line 1082

Replaces the clause from "which in the irrotational-spin, small-chiral-angle limit" up to "of $s^\nu$ and $u^\nu$". Eq. `eq:sl2c_fisher_metric_main` ends with a full stop and the stationarity sentence that follows is kept.

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

Lean: `ScalarSpinDefect.density_of_primitive`, `ScalarFrameIntegralLimit.tendsto_density`, `ScalarFrameIntegralLimit.tendsto_integral`, `TwistedOscillationIntegral.not_tendsto_action`.

### Remark 7.4 (`rem:gordon_osmotic_bridge`), v13 line 1166

Approved by the author on 2026-11-24 and proved in blocks 317–320. Replaces the last two sentences of the remark, from "Substituting the polar derivative" to the end. The Gordon decomposition in the first half of the remark is kept.

One definition differs from the wording first shown to the author: the axial covector `A_μ` is written with the Levi-Civita symbol in the frame, which is the form proved. For an orientation-preserving frame it equals `½ ε_{μναβ} u_a^α u_b^β ω^{νab}`; that equality is not formalized.

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

Lean: `PolarSpinMagnetization` (tensor), `PolarDiracFieldEquations.diracField_polar_coordinate`, `PolarDiracFieldEquations.diracField_polar_eq_zero_iff`, `PolarDiracFieldEquations.covectors_eq_zero_iff`, `PolarDiracFieldEquations.canonicalContraction_eq_spin_pairing`, `TetradDivergenceLock.legDivergence_eq_neg_trace`, `TetradDivergenceLock.densityDefect_zero_iff_current`, `TetradDivergenceLock.dirac_solution_lock`.
