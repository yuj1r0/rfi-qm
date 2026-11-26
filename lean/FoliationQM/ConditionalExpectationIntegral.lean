module

public import FoliationQM.TwoParticleMarginals

/-!
# Integration against the two-particle conditional density

The marginal and conditional in v13 are genuine spatial integrals.
These identities express weighted joint observables, including those
depending on one particle only, as iterated conditional expectations.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.ConditionalExpectationIntegral

open MeasureTheory LorentzCoordinates TwoParticleMarginals

variable {f : Spatial × Spatial → ℝ}

/-- An integrable joint observable has the same integral when first averaged
against the conditional density and then against the first marginal. -/
theorem weighted_fubini (h : Spatial × Spatial → ℝ)
    (hm : ∀ x, 0 < left f x)
    (hi : Integrable (fun z : Spatial × Spatial => f z * h z)) :
    (∫ z, f z * h z) = ∫ x, left f x * ∫ y, conditional f x y * h (x,y) := by
  change (∫ z, f z * h z ∂volume.prod volume) = _
  rw [integral_prod _ hi]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  change (∫ y, f (x,y) * h (x,y)) = left f x * ∫ y, conditional f x y * h (x,y)
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  calc
    f (x,y) * h (x,y) = (left f x * conditional f x y) * h (x,y) :=
      congrArg (· * h (x,y)) (factorization f x y (hm x))
    _ = _ := mul_assoc ..

/-- An observable depending only on the retained coordinate is integrated
exactly with its marginal. Fubini supplies integrability of the marginal
observable from integrability of the joint observable. -/
theorem marginal_observable (h : Spatial → ℝ)
    (hi : Integrable (fun z : Spatial × Spatial => f z * h z.1)) :
    Integrable (fun x => left f x * h x) ∧
      (∫ z : Spatial × Spatial, f z * h z.1) = ∫ x, left f x * h x := by
  have he (x : Spatial) : (∫ y : Spatial, f (x,y) * h x) = left f x * h x :=
    integral_mul_const _ _
  exact ⟨hi.integral_prod_left.congr (.of_forall he),
    (integral_prod _ hi).trans (integral_congr_ae (.of_forall he))⟩

/-- Conversely, integrability of a weighted marginal observable supplies
its joint integrability. This permits finite marginal energies to be used
inside the genuine joint integral. -/
theorem integrable_lift (h : Spatial → ℝ) (hf : Measurable f) (hh : Measurable h)
    (hp : ∀ z, 0 ≤ f z) (hfib : ∀ x, Integrable (fun y => f (x,y)))
    (hi : Integrable (fun x => left f x * h x)) :
    Integrable (fun z : Spatial × Spatial => f z * h z.1) := by
  apply (integrable_prod_iff (hf.mul (hh.comp measurable_fst)).aestronglyMeasurable).mpr
  refine ⟨.of_forall (fun x => (hfib x).mul_const (h x)), hi.norm.congr ?_⟩
  apply Filter.Eventually.of_forall
  intro x
  have hm : 0 ≤ left f x := integral_nonneg (fun y => hp (x,y))
  change ‖left f x * h x‖ = ∫ y, ‖f (x,y) * h x‖
  simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hm, abs_of_nonneg (hp _)]
  exact (integral_mul_const _ _).symm

end FoliationQM.ConditionalExpectationIntegral
