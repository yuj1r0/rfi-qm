module

public import FoliationQM.GeneralCouplingFirstVariation

/-!
# The density variation for the dressed mass

For v13 `eq:dressed_mass_velocity` the phase stays fixed. On any positive
open chart, vanishing of all compact interior density variations of the
scalar action is equivalent to its Hamilton–Jacobi–Bohm equation.
The integrals use the change in density relative to the background.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.DressedMassDensityVariation

open MeasureTheory PolarSecondDifferential Madelung
open scoped ContDiff

/-- The phase differential in the flat spacetime coordinates with x⁰ = ct. -/
def phaseDifferential (S : Covector → ℝ) (x : Covector) : Covector :=
  fun i => directionalDerivative S (coordinateVector i) x

/-- The wave-operator correction with the positive amplitude R = √ρ. -/
def quantumCorrection (ρ : Covector → ℝ) (x : Covector) : ℝ :=
  box (fun y => Real.sqrt (ρ y)) coordinateVector x / Real.sqrt (ρ x)

/-- The scalar source action is stationary under compact changes of density
alone, with the action phase held fixed throughout the variation. -/
def DensityStationaryOn (p : MassiveParameters) (ρ S : Covector → ℝ) (U : Set Covector) : Prop :=
  ∀ a : Covector → ℝ, ContDiff ℝ ∞ a → HasCompactSupport a → tsupport a ⊆ U →
    HasDerivAt (fun t : ℝ => RelativePolarStationaryAction.relativeHydroAction p ρ S
      (fun x => ρ x + t * a x) S coordinateVector U) 0 0

private def residual (p : MassiveParameters) (ρ S : Covector → ℝ) (x : Covector) : ℝ :=
  minkowski (phaseDifferential S x) (phaseDifferential S x) -
    p.m ^ 2 * p.c ^ 2 - p.hbar ^ 2 * quantumCorrection ρ x

private theorem continuousAt_residual (p : MassiveParameters) {ρ S : Covector → ℝ} {x : Covector}
    (hρ : ContDiffAt ℝ 2 ρ x) (hs : ContDiffAt ℝ 2 S x) (hp : 0 < ρ x) :
    ContinuousAt (residual p ρ S) x := by
  have dir {f : Covector → ℝ} (hf : ContDiffAt ℝ 2 f x) (i : Fin 4) :
      ContDiffAt ℝ 1 (directionalDerivative f (coordinateVector i)) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
  have grad (i : Fin 4) : ContinuousAt (fun y => phaseDifferential S y i) x := (dir hs i).continuousAt
  have hr := hρ.sqrt (ne_of_gt hp)
  have second (i : Fin 4) : ContinuousAt
      (secondDirectionalDerivative (fun y => Real.sqrt (ρ y)) (coordinateVector i)) x :=
    ((dir hr i).fderiv_right (m := 0) (by norm_num)).continuousAt.clm_apply continuousAt_const
  have hbox := (((second 0).sub (second 1)).sub (second 2)).sub (second 3)
  have hq : ContinuousAt (quantumCorrection ρ) x :=
    hbox.div hr.continuousAt (ne_of_gt (Real.sqrt_pos.2 hp))
  have sq (i : Fin 4) := (grad i).mul (grad i)
  have hnorm := (((sq 0).sub (sq 1)).sub (sq 2)).sub (sq 3)
  exact (hnorm.sub continuousAt_const).sub (continuousAt_const.mul hq)

private theorem density_firstVariation (p : MassiveParameters)
    {ρ S a : Covector → ℝ} {U : Set Covector} (hU : IsOpen U)
    (hρ : ∀ x ∈ U, ContDiffAt ℝ ∞ ρ x) (hS : ∀ x ∈ U, ContDiffAt ℝ ∞ S x)
    (hp : ∀ x ∈ U, 0 < ρ x) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ U) :
    HasDerivAt (fun t : ℝ => RelativePolarStationaryAction.relativeHydroAction p ρ S
      (fun x => ρ x + t * a x) S coordinateVector U)
      (∫ x in U, a x * residual p ρ S x) 0 := by
  have hlam : 0 < p.hbar ^ 2 / 4 := div_pos (sq_pos_of_pos p.hbar_pos) (by norm_num)
  have h := GeneralCouplingFirstVariation.hasDerivAt_relativeHydroAction_affine_real p hlam hU
    hρ hS ha (contDiff_const (c := (0 : ℝ))) hp hc (HasCompactSupport.zero) hs
    (by simp) coordinateVector
  have hcoef : 4 * (p.hbar ^ 2 / 4) = p.hbar ^ 2 := by ring
  unfold residual phaseDifferential quantumCorrection
  simpa only [GeneralCouplingAction.relativeHydroAction_eq_effective p hlam,
    GeneralCouplingAction.effectiveParameters_canonical, mul_zero, add_zero, sub_zero,
    zero_mul, hcoef, mul_div_assoc]
    using h

/-- At positive density, compact density tests alone give the pointwise physical
Hamilton–Jacobi–Bohm equation, and that equation makes each such variation vanish. -/
theorem densityStationaryOn_iff_mass_shell (p : MassiveParameters)
    {ρ S : Covector → ℝ} {U : Set Covector} (hU : IsOpen U)
    (hρ : ∀ x ∈ U, ContDiffAt ℝ ∞ ρ x) (hS : ∀ x ∈ U, ContDiffAt ℝ ∞ S x)
    (hp : ∀ x ∈ U, 0 < ρ x) :
    DensityStationaryOn p ρ S U ↔ ∀ x ∈ U,
      minkowski (phaseDifferential S x) (phaseDifferential S x) =
        p.m ^ 2 * p.c ^ 2 + p.hbar ^ 2 * quantumCorrection ρ x := by
  constructor
  · intro h
    have cont : ContinuousOn (residual p ρ S) U := fun x hx =>
      (continuousAt_residual p ((hρ x hx).of_le (by simp)) ((hS x hx).of_le (by simp))
        (hp x hx)).continuousWithinAt
    have hz : ∀ x ∈ U, residual p ρ S x = 0 := by
      apply MeasureTheory.Measure.eqOn_open_of_ae_eq (μ := volume) _ hU cont continuousOn_const
      change ∀ᵐ x ∂volume.restrict U, residual p ρ S x = 0
      rw [ae_restrict_iff' hU.measurableSet]
      apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (cont.locallyIntegrableOn hU.measurableSet)
      intro a ha hc hs
      have hi := (density_firstVariation p hU hρ hS hp ha hc hs).unique (h a ha hc hs)
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        simp [image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht))])] at hi
      exact hi
    intro x hx
    simpa only [residual, sub_sub, sub_eq_zero] using hz x hx
  · intro h a ha hc hs
    have hzero : (∫ x in U, a x * residual p ρ S x) = 0 := by
      rw [setIntegral_congr_fun (g := fun _ => 0) hU.measurableSet]
      · simp
      · intro x hx
        change a x * (_ - _ - _) = 0
        rw [h x hx]
        ring
    exact hzero ▸ density_firstVariation p hU hρ hS hp ha hc hs

end FoliationQM.DressedMassDensityVariation
