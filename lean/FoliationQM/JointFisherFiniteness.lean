module

public import FoliationQM.TwoParticleFisher

/-!
# Finite joint Fisher energy and its six coordinate terms

For v13 Proposition `prop:fisher_excess`, strict positivity of both
inverse-mass coefficients lets each weighted coordinate square be bounded
by the physical Fisher integrand up to a constant. Fubini then makes all
six coordinate fiber integrals finite simultaneously almost everywhere.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.JointFisherFiniteness

open MeasureTheory LorentzCoordinates MarginalDifferentiation JointScoreRegularity
open TwoParticleFisher ObserverGaussianFisher
open scoped BigOperators

variable {f : Spatial × Spatial → ℝ} {hbar m₁ m₂ : ℝ}

private theorem weighted_coordinates_iff (H : Regular f)
    (s : Fin 3 → Spatial × Spatial → ℝ) (hs : ∀ i, Continuous (s i)) :
    Integrable (fun z => f z * ∑ i, s i z ^ 2) ↔
      ∀ i, Integrable (fun z => f z * s i z ^ 2) := by
  constructor
  · intro hi i
    apply hi.mono' (H.smooth.continuous.mul ((hs i).pow 2)).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro z
    change ‖f z * s i z ^ 2‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (H.pos z).le (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (fun j _ => sq_nonneg (s j z)) (Finset.mem_univ i)) (H.pos z).le
  · intro hi
    simp only [Finset.mul_sum]
    exact integrable_finsetSum _ (fun i _ => hi i)

/-- Both full three-axis traces are integrable when the physical joint Fisher
density is integrable and its two source coefficients are strictly positive. -/
theorem traces (H : Regular f) (hh : 0 < hbar) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hJ : Integrable (jointDensity hbar m₁ m₂ f)) :
    Integrable (fun z : Spatial × Spatial => f z * ∑ i, firstScore f z.1 z.2 (axes i) ^ 2) ∧
    Integrable (fun z : Spatial × Spatial => f z * ∑ i, secondScore f z.1 z.2 (axes i) ^ 2) := by
  let t₁ := fun z : Spatial × Spatial => f z * ∑ i, firstScore f z.1 z.2 (axes i) ^ 2
  let t₂ := fun z : Spatial × Spatial => f z * ∑ i, secondScore f z.1 z.2 (axes i) ^ 2
  have hc₁ := coefficient_pos hh hm₁
  have hc₂ := coefficient_pos hh hm₂
  have hcont : Continuous t₁ :=
    H.smooth.continuous.mul (continuous_finsetSum _ fun i _ => (continuous_firstScore H (axes i)).pow 2)
  have hnon₁ (z) : 0 ≤ t₁ z := mul_nonneg (H.pos z).le (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hnon₂ (z) : 0 ≤ t₂ z := mul_nonneg (H.pos z).le (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hw := (integrable_add_iff_of_nonneg
    (f := fun z => coefficient hbar m₁ * t₁ z) (g := fun z => coefficient hbar m₂ * t₂ z)
    (continuous_const.mul hcont).aestronglyMeasurable
    (.of_forall fun z => mul_nonneg hc₁.le (hnon₁ z))
    (.of_forall fun z => mul_nonneg hc₂.le (hnon₂ z))).mp hJ
  exact ⟨(integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hc₁.ne') t₁).mp hw.1,
    (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hc₂.ne') t₂).mp hw.2⟩

/-- The six individual density-weighted coordinate score squares are globally integrable. -/
theorem coordinates (H : Regular f) (hh : 0 < hbar) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hJ : Integrable (jointDensity hbar m₁ m₂ f)) :
    (∀ i, Integrable (fun z : Spatial × Spatial => f z * firstScore f z.1 z.2 (axes i) ^ 2)) ∧
    (∀ i, Integrable (fun z : Spatial × Spatial => f z * secondScore f z.1 z.2 (axes i) ^ 2)) := by
  obtain ⟨h₁, h₂⟩ := traces H hh hm₁ hm₂ hJ
  exact ⟨(weighted_coordinates_iff H _ (fun i => continuous_firstScore H (axes i))).mp h₁,
    (weighted_coordinates_iff H _ (fun i => continuous_secondScore H (axes i))).mp h₂⟩

/-- For positive physical parameters, finiteness of the joint density integral
is equivalent to integrability of each of the six coordinate squares with the joint weight. -/
theorem joint_iff_coordinates (H : Regular f) (hh : 0 < hbar) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) :
    Integrable (jointDensity hbar m₁ m₂ f) ↔
    (∀ i, Integrable (fun z : Spatial × Spatial => f z * firstScore f z.1 z.2 (axes i) ^ 2)) ∧
    (∀ i, Integrable (fun z : Spatial × Spatial => f z * secondScore f z.1 z.2 (axes i) ^ 2)) := by
  refine ⟨coordinates H hh hm₁ hm₂, ?_⟩
  rintro ⟨h₁,h₂⟩
  have ht₁ := (weighted_coordinates_iff H _ (fun i => continuous_firstScore H (axes i))).mpr h₁
  have ht₂ := (weighted_coordinates_iff H _ (fun i => continuous_secondScore H (axes i))).mpr h₂
  exact (ht₁.const_mul (coefficient hbar m₁)).add (ht₂.const_mul (coefficient hbar m₂))

/-- Almost every first coordinate simultaneously admits all six finite fibers,
as required to apply the pointwise three-axis variance and conditional-energy identities. -/
theorem fiber_coordinates_ae (H : Regular f) (hh : 0 < hbar) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hJ : Integrable (jointDensity hbar m₁ m₂ f)) :
    ∀ᵐ x, (∀ i, Integrable (fun y => f (x,y) * firstScore f x y (axes i) ^ 2)) ∧
      (∀ i, Integrable (fun y => f (x,y) * secondScore f x y (axes i) ^ 2)) := by
  obtain ⟨h₁,h₂⟩ := coordinates H hh hm₁ hm₂ hJ
  exact (ae_all_iff.mpr (fun i => (h₁ i).prod_right_ae)).and
    (ae_all_iff.mpr (fun i => (h₂ i).prod_right_ae))

end FoliationQM.JointFisherFiniteness
