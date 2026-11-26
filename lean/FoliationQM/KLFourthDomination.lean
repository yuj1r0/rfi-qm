module

public import FoliationQM.KLDifferentiation
public import FoliationQM.IteratedLogDerivatives
public import Mathlib.Algebra.BigOperators.Pi

/-!
# Concrete higher weighted domination for translated KL

Sources: v13 `thm:clock_sideband`, `eq:kl_fisher_expansion`, and the
supplement's finite-displacement fourth-order refinement. The record extends
the already used first/second derivative envelopes by actual weighted third
and fourth log-derivative bounds on the same translation ball. Every bound
is a density assumption, independent of the desired KL Taylor estimate.
Genuine integrability of the higher multilinear fields and their evaluations
is then proved from C4 density regularity and those envelopes.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.KLFourthDomination

open MeasureTheory Metric IteratedLogDerivatives
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E]

/-- Source common weighted derivative envelopes through order four, with
no derivative of the KL integral or remainder bound as a field. -/
structure HigherDomination (f : E → ℝ) (μ : Measure E) (r : ℝ)
    extends KLDifferentiation.Domination f μ r where
  thirdBound : E → ℝ
  fourthBound : E → ℝ
  third_integrable : Integrable thirdBound μ
  fourth_integrable : Integrable fourthBound μ
  third_le : ∀ᵐ x ∂μ, ∀ a ∈ ball (0 : E) r,
    ‖weightedLogDerivative f 3 a x‖ ≤ thirdBound x
  fourth_le : ∀ᵐ x ∂μ, ∀ a ∈ ball (0 : E) r,
    ‖weightedLogDerivative f 4 a x‖ ≤ fourthBound x

/-- The actual spatial integral of the third multilinear translation
derivative field, including its negative density weight. -/
def thirdIntegral (f : E → ℝ) (μ : Measure E) (a : E) : E [×3]→L[ℝ] ℝ :=
  ∫ x, weightedLogDerivative f 3 a x ∂μ

/-- A common third-derivative envelope is nonnegative almost everywhere,
as follows by evaluating its genuine norm bound at zero translation. -/
theorem thirdBound_nonneg {f : E → ℝ} {μ : Measure E} {r : ℝ}
    (D : HigherDomination f μ r) : ∀ᵐ x ∂μ, 0 ≤ D.thirdBound x := by
  filter_upwards [D.third_le] with x hx
  exact (norm_nonneg _).trans (hx 0 (mem_ball_self D.radius_pos))

/-- The source fourth-derivative envelope is likewise nonnegative almost
everywhere; this is derived rather than inserted as another hypothesis. -/
theorem fourthBound_nonneg {f : E → ℝ} {μ : Measure E} {r : ℝ}
    (D : HigherDomination f μ r) : ∀ᵐ x ∂μ, 0 ≤ D.fourthBound x := by
  filter_upwards [D.fourth_le] with x hx
  exact (norm_nonneg _).trans (hx 0 (mem_ball_self D.radius_pos))

/-- The actual integrated third-derivative envelope is nonnegative. -/
theorem integral_thirdBound_nonneg {f : E → ℝ} {μ : Measure E} {r : ℝ}
    (D : HigherDomination f μ r) : 0 ≤ ∫ x, D.thirdBound x ∂μ :=
  integral_nonneg_of_ae (thirdBound_nonneg D)

/-- The actual integrated fourth-derivative envelope supplies a nonnegative
density-dependent remainder constant. -/
theorem integral_fourthBound_nonneg {f : E → ℝ} {μ : Measure E} {r : ℝ}
    (D : HigherDomination f μ r) : 0 ≤ ∫ x, D.fourthBound x ∂μ :=
  integral_nonneg_of_ae (fourthBound_nonneg D)

variable [BorelSpace E] [SecondCountableTopology E]

/-- C4 regularity and the source common third envelope imply genuine
integrability of the actual third multilinear derivative field. -/
theorem integrable_third {f : E → ℝ} (hf : ContDiff ℝ 4 f)
    (hpos : ∀ x, 0 < f x) {μ : Measure E} {r : ℝ}
    (D : HigherDomination f μ r) {a : E} (ha : a ∈ ball (0 : E) r) :
    Integrable (weightedLogDerivative f 3 a) μ :=
  integrable_weightedLogDerivative (hf.of_le (by norm_num)) hpos a D.third_integrable
    (D.third_le.mono fun _ hx => hx a ha)

/-- C4 regularity and the source common fourth envelope imply genuine
integrability of the actual fourth multilinear derivative field. -/
theorem integrable_fourth {f : E → ℝ} (hf : ContDiff ℝ 4 f)
    (hpos : ∀ x, 0 < f x) {μ : Measure E} {r : ℝ}
    (D : HigherDomination f μ r) {a : E} (ha : a ∈ ball (0 : E) r) :
    Integrable (weightedLogDerivative f 4 a) μ :=
  integrable_weightedLogDerivative hf hpos a D.fourth_integrable
    (D.fourth_le.mono fun _ hx => hx a ha)

/-- Every evaluation of the actual third derivative field is genuinely
integrable on the common translation ball. -/
theorem integrable_third_apply {f : E → ℝ} (hf : ContDiff ℝ 4 f)
    (hpos : ∀ x, 0 < f x) {μ : Measure E} {r : ℝ}
    (D : HigherDomination f μ r) {a : E} (ha : a ∈ ball (0 : E) r)
    (v : Fin 3 → E) : Integrable (fun x => weightedLogDerivative f 3 a x v) μ :=
  integrable_weightedLogDerivative_apply (integrable_third hf hpos D ha) v

/-- Every evaluation of the actual fourth derivative field is genuinely
integrable on the same ball. -/
theorem integrable_fourth_apply {f : E → ℝ} (hf : ContDiff ℝ 4 f)
    (hpos : ∀ x, 0 < f x) {μ : Measure E} {r : ℝ}
    (D : HigherDomination f μ r) {a : E} (ha : a ∈ ball (0 : E) r)
    (v : Fin 4 → E) : Integrable (fun x => weightedLogDerivative f 4 a x v) μ :=
  integrable_weightedLogDerivative_apply (integrable_fourth hf hpos D ha) v

/-- Evaluation of the actual integrated third multilinear derivative is
the genuine integral of its pointwise evaluations. -/
theorem thirdIntegral_apply {f : E → ℝ} (hf : ContDiff ℝ 4 f)
    (hpos : ∀ x, 0 < f x) {μ : Measure E} {r : ℝ}
    (D : HigherDomination f μ r) {a : E} (ha : a ∈ ball (0 : E) r)
    (v : Fin 3 → E) :
    thirdIntegral f μ a v = ∫ x, weightedLogDerivative f 3 a x v ∂μ :=
  integral_weightedLogDerivative_apply (integrable_third hf hpos D ha) v

/-- The integrated cubic coefficient is exactly minus the density-weighted
third log differential, with integrability supplied by the common envelope. -/
theorem thirdIntegral_apply_eq_log {f : E → ℝ} (hf : ContDiff ℝ 4 f)
    (hpos : ∀ x, 0 < f x) {μ : Measure E} {r : ℝ}
    (D : HigherDomination f μ r) {a : E} (ha : a ∈ ball (0 : E) r)
    (v : Fin 3 → E) :
    thirdIntegral f μ a v =
      -(∫ x, f x * iteratedFDeriv ℝ 3 (TranslatedKL.logDensity f) (x + a) v ∂μ) := by
  rw [thirdIntegral_apply hf hpos D ha]
  simp only [weightedLogDerivative_apply, neg_mul, integral_neg]

section SpatialComponents

local notation "V" => Fin 3 → ℝ

/-- A genuine multilinear spatial form expands in the coordinate basis,
with one independent laboratory-coordinate index for each argument. -/
theorem multilinear_apply_eq_sum {n : ℕ} (T : V [×n]→L[ℝ] ℝ) (v : Fin n → V) :
    T v = ∑ k : Fin n → Fin 3,
      (∏ j : Fin n, v j (k j)) * T (fun j => Pi.single (k j) 1) := by
  calc
    T v = T (fun j => ∑ i : Fin 3, v j i • Pi.single i 1) := by
      apply congrArg T
      funext j
      exact pi_eq_sum_univ' (v j)
    _ = ∑ k : Fin n → Fin 3, T (fun j => v j (k j) • Pi.single (k j) 1) :=
      T.map_sum (fun j i => v j i • Pi.single i 1)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      exact T.map_smul_univ (fun j => v j (k j)) (fun j => Pi.single (k j) 1)

/-- The actual multilinear operator norm is controlled by the finite sum
of absolute coordinate entries; the product norm is used only for this bound. -/
theorem norm_multilinear_le_sum_basis {n : ℕ} (T : V [×n]→L[ℝ] ℝ) :
    ‖T‖ ≤ ∑ k : Fin n → Fin 3, ‖T (fun j => Pi.single (k j) 1)‖ := by
  apply T.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro v
  rw [multilinear_apply_eq_sum]
  calc
    ‖∑ k : Fin n → Fin 3, (∏ j : Fin n, v j (k j)) *
        T (fun j => Pi.single (k j) 1)‖ ≤
      ∑ k : Fin n → Fin 3, ‖(∏ j : Fin n, v j (k j)) *
        T (fun j => Pi.single (k j) 1)‖ := norm_sum_le _ _
    _ = ∑ k : Fin n → Fin 3, (∏ j : Fin n, ‖v j (k j)‖) *
        ‖T (fun j => Pi.single (k j) 1)‖ := by simp only [norm_mul, norm_prod]
    _ ≤ ∑ k : Fin n → Fin 3, (∏ j : Fin n, ‖v j‖) *
        ‖T (fun j => Pi.single (k j) 1)‖ := by
      apply Finset.sum_le_sum
      intro k _
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => norm_le_pi_norm (v j) (k j))
    _ = (∑ k : Fin n → Fin 3, ‖T (fun j => Pi.single (k j) 1)‖) *
        ∏ j : Fin n, ‖v j‖ := by rw [← Finset.mul_sum, mul_comm]

/-- Common coordinatewise third/fourth derivative envelopes realize the
higher operator-envelope record using the same translation ball as orders one and two. -/
def of_component_bounds {f : V → ℝ} {μ : Measure V} {r : ℝ}
    (D : KLDifferentiation.Domination f μ r)
    (B₃ : (Fin 3 → Fin 3) → V → ℝ) (B₄ : (Fin 4 → Fin 3) → V → ℝ)
    (hB₃ : ∀ k, Integrable (B₃ k) μ) (hB₄ : ∀ k, Integrable (B₄ k) μ)
    (hthird : ∀ k, ∀ᵐ x ∂μ, ∀ a ∈ ball (0 : V) r,
      ‖weightedLogDerivative f 3 a x (fun j => Pi.single (k j) 1)‖ ≤ B₃ k x)
    (hfourth : ∀ k, ∀ᵐ x ∂μ, ∀ a ∈ ball (0 : V) r,
      ‖weightedLogDerivative f 4 a x (fun j => Pi.single (k j) 1)‖ ≤ B₄ k x) :
    HigherDomination f μ r where
  toDomination := D
  thirdBound x := ∑ k : Fin 3 → Fin 3, B₃ k x
  fourthBound x := ∑ k : Fin 4 → Fin 3, B₄ k x
  third_integrable := integrable_finsetSum _ (fun k _ => hB₃ k)
  fourth_integrable := integrable_finsetSum _ (fun k _ => hB₄ k)
  third_le := by
    have hall := ae_all_iff.mpr hthird
    filter_upwards [hall] with x hx
    intro a ha
    exact (norm_multilinear_le_sum_basis (weightedLogDerivative f 3 a x)).trans
      (Finset.sum_le_sum fun k _ => hx k a ha)
  fourth_le := by
    have hall := ae_all_iff.mpr hfourth
    filter_upwards [hall] with x hx
    intro a ha
    exact (norm_multilinear_le_sum_basis (weightedLogDerivative f 4 a x)).trans
      (Finset.sum_le_sum fun k _ => hx k a ha)

/-- Envelopes for the source's literal density-weighted mixed log partials
through orders three and four imply the same genuine higher domination. -/
def of_weighted_log_bounds {f : V → ℝ} {μ : Measure V} {r : ℝ}
    (D : KLDifferentiation.Domination f μ r)
    (B₃ : (Fin 3 → Fin 3) → V → ℝ) (B₄ : (Fin 4 → Fin 3) → V → ℝ)
    (hB₃ : ∀ k, Integrable (B₃ k) μ) (hB₄ : ∀ k, Integrable (B₄ k) μ)
    (hthird : ∀ k, ∀ᵐ x ∂μ, ∀ a ∈ ball (0 : V) r,
      |f x * iteratedFDeriv ℝ 3 (TranslatedKL.logDensity f) (x + a)
        (fun j => Pi.single (k j) 1)| ≤ B₃ k x)
    (hfourth : ∀ k, ∀ᵐ x ∂μ, ∀ a ∈ ball (0 : V) r,
      |f x * iteratedFDeriv ℝ 4 (TranslatedKL.logDensity f) (x + a)
        (fun j => Pi.single (k j) 1)| ≤ B₄ k x) :
    HigherDomination f μ r := by
  apply of_component_bounds D B₃ B₄ hB₃ hB₄
  · intro k
    filter_upwards [hthird k] with x hx
    intro a ha
    simpa only [weightedLogDerivative_apply, neg_mul, norm_neg, Real.norm_eq_abs] using hx a ha
  · intro k
    filter_upwards [hfourth k] with x hx
    intro a ha
    simpa only [weightedLogDerivative_apply, neg_mul, norm_neg, Real.norm_eq_abs] using hx a ha

end SpatialComponents

end FoliationQM.KLFourthDomination
