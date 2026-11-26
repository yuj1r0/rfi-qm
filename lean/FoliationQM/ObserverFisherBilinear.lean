module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Signed mixed terms in the spatial Fisher functional

The product score in v13 Remark 5.2 (line 520 and supplement lines
299–309) contains signed products of two real directional scores beneath
a common nonnegative density. Finiteness of the weighted squares suffices
for their mixed integral and the sharp integral Cauchy–Schwarz bound.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.ObserverFisherBilinear

open MeasureTheory

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} {w a b : E → ℝ}

/-- Two square-integrable real scores with the same nonnegative weight have
an integrable signed mixed term. The weight may vanish on any measurable region. -/
theorem integrable_weighted_mul (hw : AEMeasurable w μ) (ha : AEMeasurable a μ)
    (hb : AEMeasurable b μ) (hpos : ∀ᵐ x ∂μ, 0 ≤ w x)
    (haa : Integrable (fun x => w x*(a x)^2) μ) (hbb : Integrable (fun x => w x*(b x)^2) μ) :
    Integrable (fun x => w x*a x*b x) μ := by
  apply (haa.add hbb).mono' ((hw.mul ha).mul hb).aestronglyMeasurable
  filter_upwards [hpos] with x hx
  change ‖w x*a x*b x‖ ≤ w x*(a x)^2 + w x*(b x)^2
  have hab : |a x| * |b x| ≤ (a x)^2 + (b x)^2 := by
    nlinarith [sq_nonneg (|a x| - |b x|), sq_abs (a x), sq_abs (b x),
      sq_nonneg (a x), sq_nonneg (b x)]
  simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hx, mul_assoc, mul_add] using
    mul_le_mul_of_nonneg_left hab hx

/-- A nonnegative scalar quadratic controls its signed mixed coefficient
by its diagonal coefficients. This includes the degenerate case C = 0. -/
theorem cross_sq_le_of_quadratic {A B C : ℝ}
    (h : ∀ t : ℝ, 0 ≤ A + 2*t*B + t^2*C) : B^2 ≤ A*C := by
  have hd : discrim C (2*B) A ≤ 0 :=
    discrim_le_zero fun t => by linarith only [h t]
  unfold discrim at hd
  nlinarith

/-- Under either sign of the cross integral, its square is bounded by
the product of the actual weighted square integrals with coefficient one. -/
theorem weighted_cauchy_sq (hw : AEMeasurable w μ) (ha : AEMeasurable a μ)
    (hb : AEMeasurable b μ) (hpos : ∀ᵐ x ∂μ, 0 ≤ w x)
    (haa : Integrable (fun x => w x*(a x)^2) μ) (hbb : Integrable (fun x => w x*(b x)^2) μ) :
    (∫ x, w x*a x*b x ∂μ)^2 ≤ (∫ x, w x*(a x)^2 ∂μ) * (∫ x, w x*(b x)^2 ∂μ) := by
  have hab := integrable_weighted_mul hw ha hb hpos haa hbb
  apply cross_sq_le_of_quadratic
  intro t
  have hsum : Integrable (fun x => w x*(a x)^2 + (2*t)*(w x*a x*b x)) μ :=
    haa.add (hab.const_mul (2*t))
  rw [← integral_const_mul (2*t), ← integral_const_mul (t^2),
    ← integral_add haa (hab.const_mul (2*t)), ← integral_add hsum (hbb.const_mul (t^2))]
  apply integral_nonneg_of_ae
  filter_upwards [hpos] with x hx
  calc
    0 ≤ w x * (a x + t*b x)^2 := mul_nonneg hx (sq_nonneg _)
    _ = _ := by ring

end FoliationQM.ObserverFisherBilinear
