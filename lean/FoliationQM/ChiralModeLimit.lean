module
public import FoliationQM.ChiralEffectiveMass
public import FoliationQM.ScalarLocalTesting
public import FoliationQM.TwistedOscillationIntegral

/-!
# A sequence of stationary chiral modes with a bare Klein–Gordon limit

For the scalar-limit clause of v13 `thm:dirac_lift`, let the slope of the
timelike chiral angle be 1/(n+1). The regular finite-action mode of each
shifted mass approaches the original rest wave as the potential vanishes.
The scalar fields, the physical spinors, and their true spatial derivatives
converge uniformly on each compact spacetime set.
-/

@[expose] public section
noncomputable section
open scoped Topology ContDiff Matrix.Norms.Operator
namespace FoliationQM.ChiralModeLimit
open Filter Set TwistedScalarAngles TwistedScalarDensity ChiralEffectiveMass DiracMatrices
open TwistedOscillationIntegral RestPlaneWave

/-- The chiral field whose timelike slope tends to zero through positive values. -/
def angle (n : ℕ) : Covector → ℝ := linearAngle 0 (epsilon n)

/-- The unit-modulus exact rest mode at the corresponding shifted positive mass. -/
def scalar (p : MassiveParameters) (n : ℕ) : Covector → ℂ := mode p (epsilon n)

/-- The potential term in the forced field equation for this sequence. -/
def source (p : MassiveParameters) (n : ℕ) (x : Covector) : ℂ :=
  (potential p (angle n) x : ℂ) * scalar p n x

/-- Every approximant is relatively and finitely stationary, with zero ordinary action on any open region. -/
theorem stationary_sequence (p : MassiveParameters) (n : ℕ) {U : Set Covector} (hU : IsOpen U) :
    TwistedScalarStationarity.StationaryOn p (angle n) (scalar p n) U ∧
    TwistedScalarStationarity.FiniteStationary p (angle n) (scalar p n) U ∧
    TwistedScalarAction.action p (angle n) (scalar p n) U = 0 :=
  ⟨mode_stationary p _ hU, mode_finite p _ hU⟩

/-- Every physical approximant is a strictly regular spinor on all flat spacetime. -/
theorem regular_sequence (p : MassiveParameters) (n : ℕ) (x : Covector) :
    SpinorRegularity.Regular (TwistedScalarField.field (angle n) (scalar p n) x) := regular_mode p _ x

/-- No approximant solves the bare Klein–Gordon equation at any point. -/
theorem bare_ne_zero (p : MassiveParameters) (n : ℕ) (x : Covector) :
    FlatIntegrationByParts.kgOperator p (scalar p n) DiracFieldDensity.coordinateDirections x ≠ 0 :=
  scalar_residual_ne_zero p (epsilon_pos n).ne' x

private theorem shifted_zero (p : MassiveParameters) : shifted p 0 = p := by
  cases p with
  | mk c m h hc hm hh =>
    simp [shifted, Real.sqrt_sq hm.le]

private theorem joint_mode (p : MassiveParameters) (d : WithTop ℕ∞) :
    ContDiff ℝ d (fun q : ℝ × Covector => mode p q.1 q.2) := by
  have hM : ContDiff ℝ d (fun q : ℝ × Covector => (shifted p q.1).m) := by
    apply ContDiff.sqrt
    · exact contDiff_const.add (((contDiff_const.mul contDiff_fst).div_const _).pow 2)
    · exact fun q => (add_pos_of_pos_of_nonneg (sq_pos_of_pos p.m_pos) (sq_nonneg _)).ne'
  have ht : ContDiff ℝ d (fun q : ℝ × Covector => -((shifted p q.1).m * p.c) * q.2 0 / p.hbar) :=
    (((hM.mul contDiff_const).neg.mul ((contDiff_apply ℝ (fun _ : Fin 4 => ℝ) 0).comp contDiff_snd))).div_const p.hbar
  have he := ((Complex.ofRealCLM.contDiff.comp ht).mul (contDiff_const (c := Complex.I))).cexp
  simpa only [mode, restWave, ActionDensity.actionField, PolarDifferential.polarField, phase,
    restAction, Real.sqrt_one, Complex.ofReal_one, one_mul, Function.comp_apply, Complex.ofRealCLM_apply,
    show ∀ k, (shifted p k).c = p.c from fun _ => rfl, show ∀ k, (shifted p k).hbar = p.hbar from fun _ => rfl] using he

private theorem joint_spin (p : MassiveParameters) (d : WithTop ℕ∞) :
    ContDiff ℝ d (fun q : ℝ × Covector => TwistedScalarField.field (linearAngle 0 q.1) (mode p q.1) q.2) := by
  have hb : ContDiff ℝ d (fun q : ℝ × Covector => linearAngle 0 q.1 q.2) :=
    contDiff_fst.mul ((contDiff_apply ℝ (fun _ : Fin 4 => ℝ) 0).comp contDiff_snd)
  have hs := (joint_mode p d).smul ((MatrixDifferential.mulVecCLM restSpinor).contDiff.comp
    ((ChiralDifferential.contDiff_chiral d).comp hb))
  simp_rw [TwistedScalarField.field_eq_smul]
  exact hs

private theorem compact_uniform {Y : Type*} [PseudoMetricSpace Y] {H : ℝ × Covector → Y}
    (h : Continuous H) {K : Set Covector} (hK : IsCompact K) :
    TendstoUniformlyOn (fun n x => H (epsilon n, x)) (fun x => H (0, x)) atTop K := by
  have hcomp : IsCompact (Icc (0:ℝ) 1 ×ˢ K) := isCompact_Icc.prod hK
  have hu := hcomp.uniformContinuousOn_of_continuous h.continuousOn
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro δ hδ
  obtain ⟨r, hr, hd⟩ := Metric.uniformContinuousOn_iff.mp hu δ hδ
  have he : Tendsto epsilon atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  filter_upwards [he.eventually (gt_mem_nhds hr)] with n hn x hx
  have hle : epsilon n ≤ 1 := (div_le_one (by positivity : 0 < (n:ℝ)+1)).mpr (by linarith)
  apply hd (0,x) ⟨⟨le_rfl, zero_le_one⟩, hx⟩ (epsilon n,x) ⟨⟨(epsilon_pos n).le, hle⟩, hx⟩
  simpa [Prod.dist_eq, abs_of_pos (epsilon_pos n)] using And.intro hn hr

private theorem compact_uniform_fderiv {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {H : ℝ × Covector → Y} (h : ContDiff ℝ 1 H) {K : Set Covector} (hK : IsCompact K) :
    TendstoUniformlyOn (fun n x => fderiv ℝ (fun y => H (epsilon n, y)) x)
      (fun x => fderiv ℝ (fun y => H (0,y)) x) atTop K := by
  have he (k : ℝ) (x : Covector) : fderiv ℝ (fun y => H (k,y)) x =
      (fderiv ℝ H (k,x)).comp (ContinuousLinearMap.inr ℝ ℝ Covector) :=
    ((h.differentiable (by norm_num) (k,x)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right k x)).fderiv
  simp only [he]
  apply compact_uniform (H := fun q => (fderiv ℝ H q).comp (ContinuousLinearMap.inr ℝ ℝ Covector)) _ hK
  exact (h.continuous_fderiv (by norm_num)).clm_comp continuous_const

/-- On every compact spacetime set the exact scalar modes converge uniformly to the bare rest wave. -/
theorem uniform_scalar (p : MassiveParameters) {K : Set Covector} (hK : IsCompact K) :
    TendstoUniformlyOn (scalar p) (restWave p) atTop K := by
  change TendstoUniformlyOn (fun n x => restWave (shifted p (epsilon n)) x) _ _ _
  simpa only [mode, shifted_zero] using compact_uniform (joint_mode p 1).continuous hK

/-- The true Fréchet derivatives of the scalar modes also converge uniformly on compact sets. -/
theorem uniform_scalar_fderiv (p : MassiveParameters) {K : Set Covector} (hK : IsCompact K) :
    TendstoUniformlyOn (fun n x => fderiv ℝ (scalar p n) x) (fun x => fderiv ℝ (restWave p) x) atTop K := by
  simpa only [scalar, mode, shifted_zero] using compact_uniform_fderiv (joint_mode p 1) hK

/-- The potential-weighted mode has constant modulus ℏ² kₙ²/4 throughout spacetime. -/
theorem norm_source (p : MassiveParameters) (n : ℕ) (x : Covector) :
    ‖source p n x‖ = p.hbar^2/4 * (epsilon n)^2 := by
  have he := restWave_normSq (shifted p (epsilon n)) x
  change Complex.normSq (scalar p n x) = 1 at he
  rw [Complex.normSq_eq_norm_sq] at he
  have hnorm : ‖scalar p n x‖ = 1 := by nlinarith [norm_nonneg (scalar p n x)]
  rw [source, angle, potential_time, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity), hnorm, mul_one]

/-- The force term tends uniformly to zero on the whole of spacetime. -/
theorem uniform_source_global (p : MassiveParameters) :
    TendstoUniformly (source p) (fun _ => 0) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro δ hδ
  have he : Tendsto epsilon atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have ht : Tendsto (fun n => p.hbar^2/4*(epsilon n)^2) atTop (𝓝 0) := by simpa using (he.pow 2).const_mul (p.hbar^2 / 4)
  filter_upwards [ht.eventually (gt_mem_nhds hδ)] with n hn x
  simpa only [dist_zero_left, norm_source] using hn

private theorem field_zero (p : MassiveParameters) :
    TwistedScalarField.field (linearAngle 0 0) (mode p 0) = ScalarRestKinetic.lift (restWave p) := by
  funext x
  change TwistedScalarJet.value (0*x 0) (restWave (shifted p 0) x) = _
  rw [zero_mul, shifted_zero, TwistedScalarJet.value_zero]
  rfl

/-- The genuine twisted spinors converge uniformly on compact sets to the scalar rest wave on the rest-spinor line. -/
theorem uniform_spin (p : MassiveParameters) {K : Set Covector} (hK : IsCompact K) :
    TendstoUniformlyOn (fun n => TwistedScalarField.field (angle n) (scalar p n))
      (ScalarRestKinetic.lift (restWave p)) atTop K := by
  simpa only [angle, scalar, field_zero] using compact_uniform (joint_spin p 1).continuous hK

/-- The true first spacetime derivatives of the twisted spinor fields converge in operator norm uniformly on each compact set. -/
theorem uniform_spin_fderiv (p : MassiveParameters) {K : Set Covector} (hK : IsCompact K) :
    TendstoUniformlyOn (fun n x => fderiv ℝ (TwistedScalarField.field (angle n) (scalar p n)) x)
      (fun x => fderiv ℝ (ScalarRestKinetic.lift (restWave p)) x) atTop K := by
  simpa only [angle, scalar, field_zero] using compact_uniform_fderiv (joint_spin p 1) hK

/-- The exact modes converge in local L¹ on every region, with both sides integrable on each compact subset. -/
theorem scalar_localL1 (p : MassiveParameters) (U : Set Covector) :
    ScalarLocalTesting.LocalL1 U (scalar p) (restWave p) :=
  ScalarLocalTesting.of_locally_uniform (fun _ _ _ => (contDiff_restWave _ 1).continuous.continuousAt)
    (fun _ _ => (contDiff_restWave _ 1).continuous.continuousAt) (fun _ hK _ => uniform_scalar p hK)

/-- The potential-weighted modes converge to zero in local L¹ on any spacetime region. -/
theorem source_localL1 (p : MassiveParameters) (U : Set Covector) :
    ScalarLocalTesting.LocalL1 U (source p) (fun _ => 0) := by
  apply ScalarLocalTesting.of_locally_uniform _ (fun _ _ => continuousAt_const) (fun _ _ _ => (uniform_source_global p).tendstoUniformlyOn)
  intro n x _
  change ContinuousAt (fun y => (potential p (linearAngle 0 (epsilon n)) y : ℂ) * restWave (shifted p (epsilon n)) y) x
  simp_rw [potential_time]
  exact (contDiff_restWave _ 1).continuous.continuousAt.const_mul _

end FoliationQM.ChiralModeLimit
