module
public import FoliationQM.StationaryScalarLimit
public import FoliationQM.ChiralModeLimit

/-!
# Derivative control for the stationary scalar limit

For v13 `thm:dirac_lift`, a vanishing uniform bound on the four angle
derivatives on each compact interior set makes the potential times the
field tend to zero in local L¹. Combined with stationarity, this gives
the scalar equations in a smooth positive density/phase chart.
-/

@[expose] public section
noncomputable section
open scoped Topology ContDiff
namespace FoliationQM.ChiralSourceLimit
open MeasureTheory Filter ScalarLocalTesting StationaryScalarLimit TwistedScalarControl
open TwistedScalarAction TwistedScalarDensity ScalarSpinDefect DiracFieldDensity
open TwistedScalarStationarity

/-- On each compact subset of U the four actual chiral derivatives share a bound tending to zero. -/
def SmallGradients (U : Set Covector) (B : ℕ → Covector → ℝ) : Prop :=
  ∀ K : Set Covector, IsCompact K → K ⊆ U → ∃ a : ℕ → ℝ, Tendsto a atTop (𝓝 0) ∧
    ∀ n, ∀ x ∈ K, ∀ μ, |gradient (B n) x μ| ≤ a n

variable (p : MassiveParameters) {U : Set Covector} {B : ℕ → Covector → ℝ}
variable {Z : ℕ → Covector → ℂ} {z : Covector → ℂ}

/-- Local L¹ convergence of the scalar fields and local uniform derivative control imply local L¹
vanishing of the actual potential source, with no uniform bound on the scalar fields required. -/
theorem source_localL1 (hb : ∀ n, ∀ x ∈ U, ContDiffAt ℝ 1 (B n) x)
    (hZ : LocalL1 U Z z) (hsmall : SmallGradients U B) :
    LocalL1 U (fun n => source p (B n) (Z n)) (fun _ => 0) := by
  intro K hK hs
  obtain ⟨hi, hf, hdiff⟩ := hZ K hK hs
  obtain ⟨a, ha, hbound⟩ := hsmall K hK hs
  let b := fun n => p.hbar^2 * (a n)^2
  have hbabs (n : ℕ) : ∀ᵐ x ∂volume.restrict K, ‖(potential p (B n) x : ℂ)‖ ≤ b n := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    simpa only [Complex.norm_real, Real.norm_eq_abs] using abs_potential_le p _ x (hbound n x hx)
  have hpot (n : ℕ) : ContinuousOn (fun x => (potential p (B n) x : ℂ)) K :=
    fun x hx => Complex.continuous_ofReal.continuousAt.comp (continuousAt_potential p (hb n x (hs hx))) |>.continuousWithinAt
  refine ⟨fun n => (hi n).bdd_mul ((hpot n).aestronglyMeasurable hK.measurableSet) (hbabs n), integrableOn_zero, ?_⟩
  simp only [sub_zero]
  apply squeeze_zero (fun n => integral_nonneg (fun _ => norm_nonneg _))
    (g := fun n => b n * ((∫ x in K, ‖Z n x - z x‖) + ∫ x in K, ‖z x‖))
  · intro n
    have h1 : (∫ x in K, ‖source p (B n) (Z n) x‖) ≤ b n * ∫ x in K, ‖Z n x‖ := by
      rw [← integral_const_mul]
      apply integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) ((hi n).norm.const_mul _)
      filter_upwards [hbabs n] with x hx
      simpa only [source, norm_mul] using mul_le_mul_of_nonneg_right hx (norm_nonneg (Z n x))
    apply h1.trans (mul_le_mul_of_nonneg_left _ (by dsimp [b]; positivity))
    have hni : IntegrableOn (fun x => ‖Z n x - z x‖) K := ((hi n).sub hf).norm
    rw [← integral_add hni hf.norm]
    exact integral_mono_ae (hi n).norm (hni.add hf.norm)
      (Eventually.of_forall fun x => by have := norm_sub_norm_le (Z n x) (z x); linarith)
  · have hbt : Tendsto b atTop (𝓝 0) := by simpa [b] using (ha.pow 2).const_mul (p.hbar^2)
    simpa using hbt.mul (hdiff.add_const (∫ x in K, ‖z x‖))

/-- Small derivatives and local L¹ field convergence suffice to pass from the actual
stationary quadratic actions to the distributional scalar Klein–Gordon equation. -/
theorem weak_limit (hU : IsOpen U) (hb : ∀ n, ∀ x ∈ U, ContDiffAt ℝ 1 (B n) x)
    (hn : ∀ n, ∀ x ∈ U, ContDiffAt ℝ 2 (Z n) x) (hst : ∀ n, AffineStationary p (B n) (Z n) U)
    (hZ : LocalL1 U Z z) (hsmall : SmallGradients U B) :
    WeakEquation p z (fun _ => 0) U :=
  weak_of_stationary p hU hb hn hst hZ (source_localL1 p hb hZ hsmall)

/-- On a smooth strictly positive limiting chart the true relative scalar action is stationary. -/
theorem stationary_polar_limit {ρ S : Covector → ℝ} (hU : IsOpen U)
    (hb : ∀ n, ∀ x ∈ U, ContDiffAt ℝ 1 (B n) x) (hn : ∀ n, ∀ x ∈ U, ContDiffAt ℝ 2 (Z n) x)
    (hst : ∀ n, AffineStationary p (B n) (Z n) U)
    (hZ : LocalL1 U Z (ActionDensity.actionField p ρ S)) (hsmall : SmallGradients U B)
    (hr : ∀ x ∈ U, ContDiffAt ℝ ∞ ρ x) (hS : ∀ x ∈ U, ContDiffAt ℝ ∞ S x) (hp : ∀ x ∈ U, 0 < ρ x) :
    RelativePolarStationaryAction.RelativePolarStationaryOn p ρ S Madelung.coordinateVector U := by
  have hz : ∀ x ∈ U, ContDiffAt ℝ 2 (ActionDensity.actionField p ρ S) x := fun x hx =>
    (OpenPolarVariations.contDiffAt_actionField p (hr x hx) (hS x hx) (hp x hx)).of_le (by simp)
  exact (RelativePolarStationaryAction.relativePolarStationaryOn_iff_kgOperator p hU hr hS hp _).mpr
    (kg_limit p hU hb hn hst hZ (source_localL1 p hb hZ hsmall) hz)

/-- The Hamilton–Jacobi–Bohm and density-current equations therefore both hold
on the positive limiting chart. -/
theorem madelung_limit {ρ S : Covector → ℝ} (hU : IsOpen U)
    (hb : ∀ n, ∀ x ∈ U, ContDiffAt ℝ 1 (B n) x) (hn : ∀ n, ∀ x ∈ U, ContDiffAt ℝ 2 (Z n) x)
    (hst : ∀ n, AffineStationary p (B n) (Z n) U)
    (hZ : LocalL1 U Z (ActionDensity.actionField p ρ S)) (hsmall : SmallGradients U B)
    (hr : ∀ x ∈ U, ContDiffAt ℝ ∞ ρ x) (hS : ∀ x ∈ U, ContDiffAt ℝ ∞ S x) (hp : ∀ x ∈ U, 0 < ρ x) :
    ∀ x ∈ U, minkowski (gradient S x) (gradient S x) = p.m^2*p.c^2 +
      p.hbar^2 * PolarSecondDifferential.box (fun y => Real.sqrt (ρ y)) coordinateDirections x / Real.sqrt (ρ x) ∧
      PolarRegularity.densityCurrentDivergence ρ S coordinateDirections x = 0 :=
  (RelativePolarStationaryAction.relativePolarStationaryOn_iff_madelung p hU hr hS hp).mp
    (stationary_polar_limit p hU hb hn hst hZ hsmall hr hS hp)

/-- The shifted rest modes supply explicit finite stationary approximants with nonzero bare
residual, whose local L¹ limit satisfies the original scalar KG equation. -/
theorem shifted_modes_limit (p : MassiveParameters) {U : Set Covector} (hU : IsOpen U) :
    (∀ n, FiniteStationary p (ChiralModeLimit.angle n) (ChiralModeLimit.scalar p n) U) ∧
    (∀ n x, FlatIntegrationByParts.kgOperator p (ChiralModeLimit.scalar p n) coordinateDirections x ≠ 0) ∧
    WeakEquation p (RestPlaneWave.restWave p) (fun _ => 0) U ∧
    ∀ x ∈ U, FlatIntegrationByParts.kgOperator p (RestPlaneWave.restWave p) coordinateDirections x = 0 := by
  have hb (n : ℕ) (x : Covector) (_ : x ∈ U) : ContDiffAt ℝ 1 (ChiralModeLimit.angle n) x :=
    (TwistedScalarAngles.smooth_linearAngle 0 (TwistedOscillationIntegral.epsilon n) 1).contDiffAt
  have hz (n : ℕ) (x : Covector) (_ : x ∈ U) : ContDiffAt ℝ ∞ (ChiralModeLimit.scalar p n) x :=
    (RestPlaneWave.contDiff_restWave _ ∞).contDiffAt
  have he (n : ℕ) := (stationary_iff_force p hU (hb n) (hz n)).mp (ChiralModeLimit.stationary_sequence p n hU).1
  have hs (n : ℕ) := (affine_iff_force p hU (hb n) (fun x hx => (hz n x hx).of_le (by simp))).mpr (he n)
  have hZ := ChiralModeLimit.scalar_localL1 p U
  have hV := ChiralModeLimit.source_localL1 p U
  have hc (n : ℕ) (x : Covector) (hx : x ∈ U) := (hz n x hx).of_le (m := (2 : WithTop ℕ∞)) (by simp)
  exact ⟨fun n => (ChiralModeLimit.stationary_sequence p n hU).2.1, ChiralModeLimit.bare_ne_zero p,
    weak_of_stationary p hU hb hc hs hZ hV,
    kg_limit p hU hb hc hs hZ hV (fun _ _ => (RestPlaneWave.contDiff_restWave p 2).contDiffAt)⟩

end FoliationQM.ChiralSourceLimit
