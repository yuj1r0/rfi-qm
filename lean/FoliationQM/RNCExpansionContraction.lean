module

public import FoliationQM.RNCHalfDensityJet
public import FoliationQM.RNCQuadraticRemainder
public import FoliationQM.PolarRegularity

/-!
# Recovering the normal-coordinate contraction from a cubic expansion

The remainder estimate in Lemma 9.1 identifies the two-jet of a locally C²
weight. This permits using an actual weight throughout the directional wave
operator when its coordinate expansion has the stated Ricci coefficient.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.RNCExpansionContraction

open Asymptotics Filter RNCHalfDensityJet
open scoped Topology

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {w : Coordinates n → ℝ}

/-- Subtracting the model reduces agreement of the three jets to vanishing of the remainder jet. -/
theorem remainder_jet_iff (hw : ContDiffAt ℝ 2 w 0) :
    ((w - weight A) 0 = 0 ∧ fderiv ℝ (w - weight A) 0 = 0 ∧
      fderiv ℝ (fderiv ℝ (w - weight A)) 0 = 0) ↔
    (w 0 = 1 ∧ fderiv ℝ w 0 = 0 ∧ fderiv ℝ (fderiv ℝ w) 0 = hessian A) := by
  have hd := PolarRegularity.eventually_differentiableAt_of_contDiffAt_two hw
  have he : fderiv ℝ (w - weight A) =ᶠ[𝓝 0] (fun y => fderiv ℝ w y - fderiv ℝ (weight A) y) := by
    filter_upwards [hd] with y hy using fderiv_sub hy (hasFDerivAt_weight A y).differentiableAt
  have hw' : ContDiffAt ℝ 1 (fderiv ℝ w) 0 := hw.fderiv_right (by norm_num)
  rw [Pi.sub_apply, weight_zero, sub_eq_zero, he.fderiv_eq, fderiv_fun_sub hw'.differentiableAt_one
    (hasFDerivAt_gradient A 0).differentiableAt, (hasFDerivAt_gradient A 0).fderiv, he.self_of_nhds]
  simp only [gradient_zero, sub_zero]
  apply and_congr_right' ∘ and_congr_right'
  constructor
  · intro hz
    ext u v
    have hv := congrArg (fun L : Coordinates n →L[ℝ] Coordinates n →L[ℝ] ℝ => L u v) hz
    simpa only [sub_apply, zero_apply, sub_eq_zero] using hv
  · intro heq
    rw [heq]
    ext u v
    simp only [sub_self, zero_apply]

/-- The value, gradient and bilinear Hessian are fixed by the cubic error estimate. -/
theorem jet_of_expansion (hw : ContDiffAt ℝ 2 w 0)
    (hr : (w - weight A) =O[𝓝 0] fun y => ‖y‖ ^ 3) :
    w 0 = 1 ∧ fderiv ℝ w 0 = 0 ∧ fderiv ℝ (fderiv ℝ w) 0 = hessian A :=
  (remainder_jet_iff hw).mp <| RNCQuadraticRemainder.zeroJet_of_isBigO_cubic
    (hw.sub (contDiff_weight A 2).contDiffAt) hr

/-- For a locally C³ weight the value, gradient and bilinear Hessian characterize the cubic expansion. -/
theorem expansion_iff_jet (hw : ContDiffAt ℝ 3 w 0) :
    ((w - weight A) =O[𝓝 0] fun y => ‖y‖ ^ 3) ↔
    (w 0 = 1 ∧ fderiv ℝ w 0 = 0 ∧ fderiv ℝ (fderiv ℝ w) 0 = hessian A) := by
  have hw₂ : ContDiffAt ℝ 2 w 0 := hw.of_le (by decide)
  refine ⟨jet_of_expansion hw₂, fun hj => ?_⟩
  obtain ⟨h₀, h₁, h₂⟩ := (remainder_jet_iff hw₂).mpr hj
  exact RNCQuadraticRemainder.isBigO_cubic_of_zeroJet (hw.sub (contDiff_weight A 3).contDiffAt) h₀ h₁ h₂

/-- The second directional derivative of the expanded weight is its Ricci quadratic form times −1/6. -/
theorem second_of_expansion (hw : ContDiffAt ℝ 2 w 0)
    (hr : (w - weight A) =O[𝓝 0] fun y => ‖y‖ ^ 3) (v : Coordinates n) :
    PolarSecondDifferential.secondDirectionalDerivative w v 0 = -(form A v v) / 6 := by
  have hw' : ContDiffAt ℝ 1 (fderiv ℝ w) 0 := hw.fderiv_right (by norm_num)
  have hd := (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp 0 hw'.differentiableAt_one.hasFDerivAt
  change fderiv ℝ ((ContinuousLinearMap.apply ℝ ℝ v) ∘ fderiv ℝ w) 0 v = _
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    (jet_of_expansion hw hr).2.2, hessian_apply]
  ring

/-- The actual signed coordinate wave operator at the RNC center is −Scal/6 whenever the v13 cubic expansion holds. -/
theorem box_of_expansion {w : Coordinates 4 → ℝ} {A : Matrix (Fin 4) (Fin 4) ℝ}
    (hw : ContDiffAt ℝ 2 w 0) (hr : (w - weight A) =O[𝓝 0] fun y => ‖y‖ ^ 3) :
    PolarSecondDifferential.box w (fun i => Pi.single i 1) 0 = -scalarCurvature A / 6 := by
  simp only [PolarSecondDifferential.box, second_of_expansion hw hr, form_basis, scalarCurvature]
  ring

end FoliationQM.RNCExpansionContraction
