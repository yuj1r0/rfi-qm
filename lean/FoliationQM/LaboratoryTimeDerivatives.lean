module

public import FoliationQM.CanonicalScalarEnergy

/-!
# Second derivatives in physical laboratory time

Source: v13 `cor:schrodinger`. The existing spacetime field uses the normal
coordinate x⁰ = ct. Pulling it back along an actual fixed-position laboratory
curve multiplies its second normal derivative by c². Neighborhood first
differentiability justifies differentiating the first-derivative identity.
No equation of motion or limiting approximation is assumed here.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.LaboratoryTimeDerivatives

open Filter LorentzCoordinates OsmoticSliceFields PolarSecondDifferential
open Madelung (coordinateVector)
open scoped Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The first laboratory-time derivative has a genuine derivative equal to c²
times the second normal-coordinate derivative. The first field derivative is
assumed on a neighborhood, so its identity can itself be differentiated. -/
theorem hasDerivAt_deriv_labTime (c : ℝ) {ψ : Covector → F}
    (y : Spatial) {τ : ℝ}
    (hψ : ∀ᶠ z in 𝓝 (slicePoint (c * τ) y), DifferentiableAt ℝ ψ z)
    (h₂ : DifferentiableAt ℝ (directionalDerivative ψ (coordinateVector 0))
      (slicePoint (c * τ) y)) :
    HasDerivAt (deriv (fun t => ψ (slicePoint (c * t) y)))
      ((c ^ 2) • secondDirectionalDerivative ψ (coordinateVector 0)
        (slicePoint (c * τ) y)) τ := by
  have hs : Continuous (fun t : ℝ => slicePoint (c * t) y) := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_const.mul continuous_id
    all_goals exact continuous_const
  have hg : deriv (fun t => ψ (slicePoint (c * t) y)) =ᶠ[𝓝 τ]
      (fun t => c • directionalDerivative ψ (coordinateVector 0)
        (slicePoint (c * t) y)) := by
    filter_upwards [hs.continuousAt.eventually hψ] with t ht
    exact (CanonicalScalarEnergy.labTime_derivative c y ht).deriv
  have hd := (CanonicalScalarEnergy.labTime_derivative c y h₂).fun_const_smul c
  have hd' : HasDerivAt
      (fun t => c • directionalDerivative ψ (coordinateVector 0)
        (slicePoint (c * t) y))
      ((c ^ 2) • secondDirectionalDerivative ψ (coordinateVector 0)
        (slicePoint (c * τ) y)) τ := by
    simpa only [Pi.smul_apply, secondDirectionalDerivative, directionalDerivative,
      smul_smul, pow_two] using hd
  exact hd'.congr_of_eventuallyEq hg

/-- Actual iterated laboratory-time derivatives realize the c² scaling of the
iterated normal directional derivative under local differentiability hypotheses. -/
theorem deriv_deriv_labTime (c : ℝ) {ψ : Covector → F}
    (y : Spatial) {τ : ℝ}
    (hψ : ∀ᶠ z in 𝓝 (slicePoint (c * τ) y), DifferentiableAt ℝ ψ z)
    (h₂ : DifferentiableAt ℝ (directionalDerivative ψ (coordinateVector 0))
      (slicePoint (c * τ) y)) :
    deriv (deriv (fun t => ψ (slicePoint (c * t) y))) τ =
      (c ^ 2) • secondDirectionalDerivative ψ (coordinateVector 0)
        (slicePoint (c * τ) y) :=
  (hasDerivAt_deriv_labTime c y hψ h₂).deriv

/-- A genuinely C² spacetime field supplies both local hypotheses, giving its
actual second physical-time derivative at every fixed spatial position. -/
theorem deriv_deriv_labTime_of_contDiff (c : ℝ) {ψ : Covector → F}
    (hψ : ContDiff ℝ 2 ψ) (y : Spatial) (τ : ℝ) :
    deriv (deriv (fun t => ψ (slicePoint (c * t) y))) τ =
      (c ^ 2) • secondDirectionalDerivative ψ (coordinateVector 0)
        (slicePoint (c * τ) y) := by
  apply deriv_deriv_labTime c y
  · exact Eventually.of_forall (hψ.differentiable (by norm_num))
  · exact ((hψ.fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiff_const).differentiable (by norm_num) _

end FoliationQM.LaboratoryTimeDerivatives
