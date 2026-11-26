module

public import FoliationQM.OsmoticSliceFields
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Spatial Fisher energy on a connected laboratory slice

For v13 `eq:spatial_fisher_pos`, the integral is taken in the Euclidean
three-dimensional observer slice. The rigidity result concerns variation
of density within that slice. Local C¹ regularity and positive density
suffice for zero finite energy to force a single constant on any
preconnected open domain.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.SpatialFisherEnergy

open Set Filter MeasureTheory LorentzCoordinates OsmoticSliceFields
open scoped ContDiff Topology

/-- Actual three coordinate derivatives of the intrinsic logarithmic density. -/
def score (r : Spatial → ℝ) (y : Spatial) : Spatial :=
  fun i => fderiv ℝ (fun z => Real.log (r z)) y (Pi.single i 1)

/-- Spatial Fisher contribution to the canonical energy density on a laboratory slice. -/
def fisherDensity (p : MassiveParameters) (r : Spatial → ℝ) (y : Spatial) : ℝ :=
  p.hbar^2/4 * r y * speedSq (score r y)

/-- Integrated spatial Fisher energy for three-dimensional Lebesgue measure. -/
def energy (p : MassiveParameters) (r : Spatial → ℝ) (U : Set Spatial) : ℝ :=
  ∫ y in U, fisherDensity p r y

/-- Tangent map of the fixed-time inclusion, with zero temporal component. -/
def sliceTangent : Spatial →L[ℝ] Covector :=
  ContinuousLinearMap.pi ![0, ContinuousLinearMap.proj 0, ContinuousLinearMap.proj 1, ContinuousLinearMap.proj 2]

/-- The Fréchet derivative of the affine spatial inclusion is the same tangent map everywhere. -/
theorem hasFDerivAt_slicePoint (t : ℝ) (y : Spatial) : HasFDerivAt (slicePoint t) sliceTangent y := by
  let fs : Fin 4 → Spatial → ℝ := ![(fun _ => t), (fun z => z 0), (fun z => z 1), (fun z => z 2)]
  have he : slicePoint t = fun z i => fs i z := by funext z i; fin_cases i <;> rfl
  rw [he]
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i <;> first | exact hasFDerivAt_const _ _ | exact hasFDerivAt_apply _ _

/-- The fixed-time inclusion of the spatial slice is smooth at every finite or infinite order. -/
theorem contDiff_slicePoint (t : ℝ) (n : WithTop ℕ∞) : ContDiff ℝ n (slicePoint t) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> first | exact contDiff_const | exact contDiff_apply ℝ (fun _ : Fin 3 => ℝ) _

/-- Each laboratory unit vector maps to its spatial coordinate vector in spacetime. -/
theorem sliceTangent_unit (i : Fin 3) :
    sliceTangent (Pi.single i 1) = Madelung.coordinateVector i.succ := by
  ext j
  fin_cases i <;> fin_cases j <;> norm_num [sliceTangent, Madelung.coordinateVector, Pi.single_apply]

/-- The true gradient of the slice restriction agrees with the three ambient logarithmic derivatives. -/
theorem score_slice (t : ℝ) {ρ : Covector → ℝ} {y : Spatial}
    (hρ : DifferentiableAt ℝ ρ (slicePoint t y)) (hp : 0 < ρ (slicePoint t y)) :
    score (ρ ∘ slicePoint t) y = spatialScore ρ (slicePoint t y) := by
  have hd := (hρ.hasFDerivAt.log hp.ne').comp y (hasFDerivAt_slicePoint t y)
  ext i
  change fderiv ℝ ((fun z => Real.log (ρ z)) ∘ slicePoint t) y (Pi.single i 1) = _
  rw [hd.fderiv, ContinuousLinearMap.comp_apply, sliceTangent_unit]
  change ((ρ (slicePoint t y))⁻¹ • fderiv ℝ ρ (slicePoint t y)) (Madelung.coordinateVector i.succ) =
    fderiv ℝ (fun z => Real.log (ρ z)) (slicePoint t y) (Madelung.coordinateVector i.succ)
  rw [(hρ.hasFDerivAt.log hp.ne').fderiv]

/-- The slice density is the canonical spatial term computed using the ambient coordinates. -/
theorem fisherDensity_slice (p : MassiveParameters) (t : ℝ) {ρ : Covector → ℝ} {y : Spatial}
    (hρ : DifferentiableAt ℝ ρ (slicePoint t y)) (hp : 0 < ρ (slicePoint t y)) :
    fisherDensity p (ρ ∘ slicePoint t) y =
      p.hbar^2/4 * ρ (slicePoint t y) * speedSq (spatialScore ρ (slicePoint t y)) := by
  rw [fisherDensity, score_slice t hρ hp]
  rfl

/-- The actual Lebesgue slice integral has the source factor ℏ²/4 outside the integral. -/
theorem energy_slice (p : MassiveParameters) (t : ℝ) {ρ : Covector → ℝ} {U : Set Spatial}
    (hU : MeasurableSet U) (hρ : ∀ y ∈ U, DifferentiableAt ℝ ρ (slicePoint t y))
    (hp : ∀ y ∈ U, 0 < ρ (slicePoint t y)) :
    energy p (ρ ∘ slicePoint t) U = p.hbar^2/4 *
      ∫ y in U, ρ (slicePoint t y) * speedSq (spatialScore ρ (slicePoint t y)) := by
  rw [energy, ← integral_const_mul]
  exact setIntegral_congr_fun hU fun y hy => (fisherDensity_slice p t (hρ y hy) (hp y hy)).trans (mul_assoc _ _ _)

/-- Spatial Fisher energy is nonnegative wherever the density is nonnegative. -/
theorem energy_nonneg (p : MassiveParameters) {r : Spatial → ℝ} {U : Set Spatial}
    (hU : MeasurableSet U) (hr : ∀ y ∈ U, 0 ≤ r y) : 0 ≤ energy p r U := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem hU] with y hy
  exact mul_nonneg (mul_nonneg (by positivity) (hr y hy)) (speedSq_nonneg _)

/-- The Fisher integrand is continuous at each positive C¹ density point. -/
theorem continuousAt_fisherDensity (p : MassiveParameters) {r : Spatial → ℝ} {y : Spatial}
    (hr : ContDiffAt ℝ 1 r y) (hp : 0 < r y) : ContinuousAt (fisherDensity p r) y := by
  have hd := ((hr.log hp.ne').fderiv_right (m := 0) (by norm_num)).continuousAt
  have hscore (i : Fin 3) : ContinuousAt (fun z => score r z i) y :=
    hd.clm_apply continuousAt_const
  have hs (i : Fin 3) := (hscore i).mul (hscore i)
  exact (continuousAt_const.mul hr.continuousAt).mul (((hs 0).add (hs 1)).add (hs 2))

private theorem score_eq_zero_iff (r : Spatial → ℝ) (y : Spatial) :
    score r y = 0 ↔ fderiv ℝ (fun z => Real.log (r z)) y = 0 := by
  constructor
  · intro h
    have hd (i : Fin 3) : fderiv ℝ (fun z => Real.log (r z)) y (Pi.single i 1) = 0 := congrFun h i
    ext v
    have hv : ∑ i : Fin 3, v i • Pi.single i (1 : ℝ) = v := by ext j; simp [Pi.single_apply]
    change fderiv ℝ (fun z => Real.log (r z)) y v = 0
    conv_lhs => rw [← hv]
    simp [hd]
  · intro h
    ext i
    simp [score, h]

/-- A density constant on an open slice region has zero spatial energy there. -/
theorem energy_zero_of_constant (p : MassiveParameters) {r : Spatial → ℝ} {U : Set Spatial}
    (hU : IsOpen U) {a : ℝ} (hr : ∀ y ∈ U, r y = a) : energy p r U = 0 := by
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro y hy
  have he : (fun z => Real.log (r z)) =ᶠ[𝓝 y] fun _ => Real.log a := by
    filter_upwards [hU.mem_nhds hy] with z hz
    rw [hr z hz]
  have hzero : score r y = 0 := (score_eq_zero_iff r y).mpr (by rw [he.fderiv_eq]; exact (hasFDerivAt_const (Real.log a) y).fderiv)
  simp [fisherDensity, hzero, speedSq, spatialDot]

/-- On a preconnected positive C¹ open slice with integrable Fisher density, zero energy
is equivalent to a single constant density on the whole region. -/
theorem energy_zero_iff (p : MassiveParameters) {r : Spatial → ℝ} {U : Set Spatial}
    (hU : IsOpen U) (hc : IsPreconnected U) (hr : ∀ y ∈ U, ContDiffAt ℝ 1 r y)
    (hp : ∀ y ∈ U, 0 < r y) (hi : IntegrableOn (fisherDensity p r) U) :
    energy p r U = 0 ↔ ∃ a, ∀ y ∈ U, r y = a := by
  constructor
  · intro he
    have hnn : 0 ≤ᵐ[volume.restrict U] fisherDensity p r := by
      filter_upwards [ae_restrict_mem hU.measurableSet] with y hy
      exact mul_nonneg (mul_nonneg (by positivity) (hp y hy).le) (speedSq_nonneg _)
    have hz := (setIntegral_eq_zero_iff_of_nonneg_ae hnn hi).mp he
    have hevery : EqOn (fisherDensity p r) 0 U :=
      Measure.eqOn_open_of_ae_eq hz hU
        (fun y hy => (continuousAt_fisherDensity p (hr y hy) (hp y hy)).continuousWithinAt) continuousOn_const
    have hd : EqOn (fderiv ℝ (fun z => Real.log (r z))) 0 U := by
      intro y hy
      have hf := hevery hy
      change (p.hbar^2/4 * r y) * speedSq (score r y) = 0 at hf
      have hcoef := mul_pos (div_pos (sq_pos_of_pos p.hbar_pos) (by norm_num : 0 < (4 : ℝ))) (hp y hy)
      have hs := (speedSq_eq_zero_iff _).mp ((mul_eq_zero.mp hf).resolve_left hcoef.ne')
      exact (score_eq_zero_iff r y).mp hs
    obtain ⟨a, ha⟩ := hU.exists_is_const_of_fderiv_eq_zero hc
      (fun y hy => (((hr y hy).log (hp y hy).ne').differentiableAt_one).differentiableWithinAt) hd
    exact ⟨Real.exp a, fun y hy => (Real.exp_log (hp y hy)).symm.trans (congrArg Real.exp (ha y hy))⟩
  · rintro ⟨a, ha⟩
    exact energy_zero_of_constant p hU ha

/-- Strict positivity of finite Fisher energy is equivalent to variation of the density
between two points of the same preconnected open spatial region. -/
theorem energy_pos_iff (p : MassiveParameters) {r : Spatial → ℝ} {U : Set Spatial}
    (hU : IsOpen U) (hc : IsPreconnected U) (hr : ∀ y ∈ U, ContDiffAt ℝ 1 r y)
    (hp : ∀ y ∈ U, 0 < r y) (hi : IntegrableOn (fisherDensity p r) U) :
    0 < energy p r U ↔ ∃ x ∈ U, ∃ y ∈ U, r x ≠ r y := by
  constructor
  · intro he
    by_contra! hall
    have ec : ∃ a, ∀ z ∈ U, r z = a := by
      rcases U.eq_empty_or_nonempty with hu | ⟨x, hx⟩
      · simp [hu]
      · exact ⟨r x, fun y hy => hall y hy x hx⟩
    exact he.ne' ((energy_zero_iff p hU hc hr hp hi).mpr ec)
  · rintro ⟨x, hx, y, hy, hne⟩
    refine (energy_nonneg p hU.measurableSet (fun z hz => (hp z hz).le)).lt_of_ne ?_
    intro hz
    obtain ⟨a, ha⟩ := (energy_zero_iff p hU hc hr hp hi).mp hz.symm
    exact hne ((ha x hx).trans (ha y hy).symm)

/-- The literal spatial term of the relativistic energy functional is strictly positive
exactly when the restricted density differs between two points of the slice domain. -/
theorem slice_energy_pos_iff (p : MassiveParameters) (t : ℝ) {ρ : Covector → ℝ} {U : Set Spatial}
    (hU : IsOpen U) (hc : IsPreconnected U) (hρ : ∀ y ∈ U, ContDiffAt ℝ 1 ρ (slicePoint t y))
    (hp : ∀ y ∈ U, 0 < ρ (slicePoint t y))
    (hi : IntegrableOn (fun y => ρ (slicePoint t y) * speedSq (spatialScore ρ (slicePoint t y))) U) :
    0 < p.hbar^2/4 * (∫ y in U, ρ (slicePoint t y) * speedSq (spatialScore ρ (slicePoint t y))) ↔
      ∃ x ∈ U, ∃ y ∈ U, ρ (slicePoint t x) ≠ ρ (slicePoint t y) := by
  have hd y hy := (hρ y hy).differentiableAt_one
  have hsi : IntegrableOn (fisherDensity p (ρ ∘ slicePoint t)) U := by
    apply IntegrableOn.congr_fun (hi.const_mul (p.hbar^2/4)) _ hU.measurableSet
    intro y hy
    rw [fisherDensity_slice p t (hd y hy) (hp y hy), mul_assoc]
  rw [← energy_slice p t hU.measurableSet hd hp]
  exact energy_pos_iff p hU hc (fun y hy => (hρ y hy).comp y (contDiff_slicePoint t 1).contDiffAt) hp hsi

end FoliationQM.SpatialFisherEnergy
