module

public import FoliationQM.FisherNormalization
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Normalized observer and invariant densities

V13 Remark 5.2 (line 520) and the audit supplement (lines 299–309)
compare the observer density gρ with the invariant modulus density ρ on
one spatial slice. Each normalizer is the actual mass of its own density
against the same measure. The normalized shapes detect the observer
factor precisely on the part of the slice carrying nonzero density.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.ObserverNormalizedShape

open Filter MeasureTheory Set

variable {E : Type*} [MeasurableSpace E]

/-- Total spatial mass with respect to the selected slice measure. -/
def mass (μ : Measure E) (ρ : E → ℝ) : ℝ := ∫ x, ρ x ∂μ

/-- The density normalized by its own total mass on the selected slice. -/
def shape (μ : Measure E) (ρ : E → ℝ) : E → ℝ :=
  FisherNormalization.normalizedDensity ρ (mass μ ρ)

/-- A shape formed from an integrable density of positive mass integrates to one. -/
theorem integral_shape (μ : Measure E) (ρ : E → ℝ) (hi : Integrable ρ μ)
    (hm : 0 < mass μ ρ) : (∫ x, shape μ ρ x ∂μ) = 1 :=
  FisherNormalization.integral_normalizedDensity hi hm rfl

/-- A spatially constant observer factor rescales the actual slice integral by that factor. -/
theorem mass_const_mul (μ : Measure E) (ρ : E → ℝ) (a : ℝ) :
    mass μ (fun x => a * ρ x) = a * mass μ ρ := integral_const_mul a ρ

/-- Separate mass normalization removes a positive constant observer factor pointwise. -/
theorem shape_const_mul (μ : Measure E) (ρ : E → ℝ) {a : ℝ} (ha : 0 < a)
    (hm : 0 < mass μ ρ) : shape μ (fun x => a * ρ x) = shape μ ρ := by
  funext x
  change a * ρ x / mass μ (fun y => a * ρ y) = ρ x / mass μ ρ
  rw [mass_const_mul]
  field_simp [ha.ne', hm.ne']

/-- A constant factor on the nonzero density set suffices for the integral scaling and
the equality of normalized shapes almost everywhere. -/
theorem mass_and_shape_of_const_on_support (μ : Measure E) (ρ g : E → ℝ)
    {a : ℝ} (ha : 0 < a) (hm : 0 < mass μ ρ)
    (hg : ∀ᵐ x ∂μ, ρ x ≠ 0 → g x = a) :
    mass μ (fun x => g x * ρ x) = a * mass μ ρ ∧
      shape μ (fun x => g x * ρ x) =ᵐ[μ] shape μ ρ := by
  have hp : (fun x => g x * ρ x) =ᵐ[μ] (fun x => a * ρ x) := by
    filter_upwards [hg] with x hx
    by_cases hz : ρ x = 0
    · simp [hz]
    · rw [hx hz]
  have he : mass μ (fun x => g x * ρ x) = mass μ (fun x => a * ρ x) := integral_congr_ae hp
  refine ⟨he.trans (mass_const_mul μ ρ a), ?_⟩
  rw [← shape_const_mul μ ρ ha hm]
  filter_upwards [hp] with x hx
  change g x * ρ x / _ = a * ρ x / _
  rw [he, hx]

/-- Equality of the two normalized shapes characterizes the observer factor as the
actual observer/invariant mass ratio wherever the invariant density is nonzero, almost everywhere. -/
theorem shape_ae_eq_iff_on_support (μ : Measure E) (ρ g : E → ℝ)
    (hm : 0 < mass μ ρ) (ho : 0 < mass μ (fun x => g x * ρ x)) :
    shape μ (fun x => g x * ρ x) =ᵐ[μ] shape μ ρ ↔
      ∀ᵐ x ∂μ, ρ x ≠ 0 → g x = mass μ (fun y => g y * ρ y) / mass μ ρ := by
  constructor
  · intro hs
    filter_upwards [hs] with x hx
    intro hn
    change g x * ρ x / _ = ρ x / _ at hx
    have he := (div_eq_div_iff ho.ne' hm.ne').mp hx
    apply (eq_div_iff hm.ne').2
    apply mul_left_cancel₀ hn
    linear_combination he
  · intro hg
    exact (mass_and_shape_of_const_on_support μ ρ g (div_pos ho hm) hm hg).2

/-- With positive invariant density almost everywhere, normalized shapes agree exactly
when the observer factor is a single positive constant almost everywhere. -/
theorem shape_ae_eq_iff_const (μ : Measure E) (ρ g : E → ℝ)
    (hp : ∀ᵐ x ∂μ, 0 < ρ x) (hm : 0 < mass μ ρ)
    (ho : 0 < mass μ (fun x => g x * ρ x)) :
    shape μ (fun x => g x * ρ x) =ᵐ[μ] shape μ ρ ↔
      ∃ a : ℝ, 0 < a ∧ g =ᵐ[μ] fun _ => a := by
  constructor
  · intro hs
    refine ⟨_, div_pos ho hm, ?_⟩
    filter_upwards [(shape_ae_eq_iff_on_support μ ρ g hm ho).mp hs, hp] with x hx hpos
    exact hx hpos.ne'
  · rintro ⟨a, ha, hg⟩
    exact (mass_and_shape_of_const_on_support μ ρ g ha hm (hg.mono fun _ he _ => he)).2

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E]

/-- On a connected open spatial slice a vanishing derivative of log g forces the
positive factor to equal its value at an anchor, thus giving the source shape identity. -/
theorem shape_of_log_derivative_zero (μ : Measure E) (ρ g : E → ℝ) {s : Set E} {x₀ : E}
    (hs : IsOpen s) (hc : IsPreconnected s) (h₀ : x₀ ∈ s)
    (hp : ∀ x ∈ s, 0 < g x) (hd : DifferentiableOn ℝ (fun x => Real.log (g x)) s)
    (hz : s.EqOn (fderiv ℝ (fun x => Real.log (g x))) 0)
    (hm : 0 < mass (μ.restrict s) ρ) :
    mass (μ.restrict s) (fun x => g x * ρ x) = g x₀ * mass (μ.restrict s) ρ ∧
      shape (μ.restrict s) (fun x => g x * ρ x) =ᵐ[μ.restrict s] shape (μ.restrict s) ρ := by
  apply mass_and_shape_of_const_on_support _ _ _ (hp x₀ h₀) hm
  filter_upwards [ae_restrict_mem (μ := μ) hs.measurableSet] with x hx
  intro _
  exact Real.log_injOn_pos (hp x hx) (hp x₀ h₀) (hs.is_const_of_fderiv_eq_zero hc hd hz hx h₀)

end FoliationQM.ObserverNormalizedShape
