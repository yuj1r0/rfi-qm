module

public import FoliationQM.ScoreCramerRao
public import Mathlib.Analysis.Real.Sqrt

/-!
# Heisenberg bounds and exact equality from actual finite score data

Sources: v13 `eq:heisenberg` and `thm:uncertainty`; component kinds C and D.
The centered score pairing and momentum decomposition are explicit inputs.
The source application derives them from one actual Sobolev representative.
No quantum observable is redefined here: `P` is a real scalar whose stated
decomposition is supplied by the actual first-derivative quadratic form.
The equality criterion requires positive Planck parameter and genuine L²
observables, and retains both independent almost-everywhere conditions.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.ActualHeisenbergDefect
open MeasureTheory CenteredL2Variance

variable {α : Type*} [MeasurableSpace α]
variable {μ : Measure α} [IsProbabilityMeasure μ] {X bulk score : α → ℝ}

omit [IsProbabilityMeasure μ] in
private theorem momentum_nonneg (hbar P : ℝ)
    (hdecomp : P = variance μ bulk + (hbar ^ 2 / 4) * (∫ x, score x ^ 2 ∂μ)) :
    0 ≤ P := by
  rw [hdecomp]
  exact add_nonneg (variance_nonneg μ bulk)
    (mul_nonneg (by positivity) (integral_nonneg fun _ => sq_nonneg _))

/-- The actual Heisenberg defect splits into bulk variance and the affine-score residual. -/
theorem defect_eq (hX : MemLp X 2 μ) (hs : MemLp score 2 μ)
    (hpair : (∫ x, centered μ X x * score x ∂μ) = -1) (hbar P : ℝ)
    (hdecomp : P = variance μ bulk + (hbar ^ 2 / 4) * (∫ x, score x ^ 2 ∂μ)) :
    variance μ X * P - hbar ^ 2 / 4 = variance μ X * variance μ bulk +
      (hbar ^ 2 / 4) * variance μ X *
        (∫ x, ScoreCramerRao.scoreResidual μ X score x ^ 2 ∂μ) := by
  calc
    _ = variance μ X * variance μ bulk + (hbar ^ 2 / 4) *
        (variance μ X * (∫ x, score x ^ 2 ∂μ) - 1) := by rw [hdecomp]; ring
    _ = _ := by rw [ScoreCramerRao.defect_eq_variance_mul_residual hX hs hpair]; ring

/-- The finite score pairing and actual momentum decomposition imply the squared lower bound. -/
theorem squared_bound (hX : MemLp X 2 μ) (hs : MemLp score 2 μ)
    (hpair : (∫ x, centered μ X x * score x ∂μ) = -1) (hbar P : ℝ)
    (hdecomp : P = variance μ bulk + (hbar ^ 2 / 4) * (∫ x, score x ^ 2 ∂μ)) :
    hbar ^ 2 / 4 ≤ variance μ X * P := by
  have hd := defect_eq hX hs hpair hbar P hdecomp
  have hb := mul_nonneg (variance_nonneg μ X) (variance_nonneg μ bulk)
  have hr : 0 ≤ (hbar ^ 2 / 4) * variance μ X *
      (∫ x, ScoreCramerRao.scoreResidual μ X score x ^ 2 ∂μ) :=
    mul_nonneg (mul_nonneg (by positivity) (variance_nonneg μ X))
      (integral_nonneg fun _ => sq_nonneg _)
  linarith

/-- Positive Planck parameter gives the literal product of nonnegative standard deviations. -/
theorem sqrt_bound (hX : MemLp X 2 μ) (hs : MemLp score 2 μ)
    (hpair : (∫ x, centered μ X x * score x ∂μ) = -1) (hbar P : ℝ)
    (hdecomp : P = variance μ bulk + (hbar ^ 2 / 4) * (∫ x, score x ^ 2 ∂μ))
    (hhbar : 0 < hbar) : hbar / 2 ≤ Real.sqrt (variance μ X) * Real.sqrt P := by
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (variance_nonneg μ X),
    Real.sq_sqrt (momentum_nonneg hbar P hdecomp),
    show (hbar / 2) ^ 2 = hbar ^ 2 / 4 by ring]
  exact squared_bound hX hs hpair hbar P hdecomp

omit [IsProbabilityMeasure μ] in
/-- Nonnegative square roots saturate exactly when their literal squared product saturates. -/
theorem sqrt_equality_iff_squared (X : α → ℝ) (hbar P : ℝ)
    (hdecomp : P = variance μ bulk + (hbar ^ 2 / 4) * (∫ x, score x ^ 2 ∂μ))
    (hhbar : 0 < hbar) :
    Real.sqrt (variance μ X) * Real.sqrt P = hbar / 2 ↔
      variance μ X * P = hbar ^ 2 / 4 := by
  calc
    _ ↔ (Real.sqrt (variance μ X) * Real.sqrt P) ^ 2 = (hbar / 2) ^ 2 :=
      (sq_eq_sq₀ (by positivity) (by positivity)).symm
    _ ↔ _ := by
      rw [mul_pow, Real.sq_sqrt (variance_nonneg μ X),
        Real.sq_sqrt (momentum_nonneg hbar P hdecomp),
        show (hbar / 2) ^ 2 = hbar ^ 2 / 4 by ring]

/-- Squared equality requires and follows from constant bulk and the actual affine-score law. -/
theorem squared_equality_iff (hX : MemLp X 2 μ) (hb : MemLp bulk 2 μ)
    (hs : MemLp score 2 μ) (hpair : (∫ x, centered μ X x * score x ∂μ) = -1)
    (hbar P : ℝ)
    (hdecomp : P = variance μ bulk + (hbar ^ 2 / 4) * (∫ x, score x ^ 2 ∂μ))
    (hhbar : 0 < hbar) :
    variance μ X * P = hbar ^ 2 / 4 ↔
      (∀ᵐ x ∂μ, bulk x = mean μ bulk) ∧
        (∀ᵐ x ∂μ, score x = -centered μ X x / variance μ X) := by
  have hV := ScoreCramerRao.variance_pos hX hs hpair
  have hk : 0 < hbar ^ 2 / 4 := by positivity
  constructor
  · intro heq
    have hd := defect_eq hX hs hpair hbar P hdecomp
    rw [heq, sub_self] at hd
    have hz := (add_eq_zero_iff_of_nonneg
      (mul_nonneg hV.le (variance_nonneg μ bulk))
      (mul_nonneg (mul_nonneg hk.le hV.le)
        (integral_nonneg fun x => sq_nonneg (ScoreCramerRao.scoreResidual μ X score x)))).mp
      hd.symm
    have hbulk : variance μ bulk = 0 := (mul_eq_zero.mp hz.1).resolve_left hV.ne'
    have hres : (∫ x, ScoreCramerRao.scoreResidual μ X score x ^ 2 ∂μ) = 0 :=
      (mul_eq_zero.mp hz.2).resolve_left (mul_pos hk hV).ne'
    have hscore := ScoreCramerRao.defect_eq_variance_mul_residual hX hs hpair
    rw [hres, mul_zero] at hscore
    exact ⟨(variance_eq_zero_iff μ hb).mp hbulk,
      (ScoreCramerRao.equality_iff hX hs hpair).mp (sub_eq_zero.mp hscore)⟩
  · rintro ⟨hbulk, hscore⟩
    have hB := (variance_eq_zero_iff μ hb).mpr hbulk
    have hF := (ScoreCramerRao.equality_iff hX hs hpair).mpr hscore
    calc
      _ = variance μ X * variance μ bulk + (hbar ^ 2 / 4) *
          (variance μ X * (∫ x, score x ^ 2 ∂μ)) := by rw [hdecomp]; ring
      _ = _ := by rw [hB, hF]; ring

/-- Literal Heisenberg saturation is equivalent to both genuine almost-everywhere conditions. -/
theorem equality_iff (hX : MemLp X 2 μ) (hb : MemLp bulk 2 μ)
    (hs : MemLp score 2 μ) (hpair : (∫ x, centered μ X x * score x ∂μ) = -1)
    (hbar P : ℝ)
    (hdecomp : P = variance μ bulk + (hbar ^ 2 / 4) * (∫ x, score x ^ 2 ∂μ))
    (hhbar : 0 < hbar) :
    Real.sqrt (variance μ X) * Real.sqrt P = hbar / 2 ↔
      (∀ᵐ x ∂μ, bulk x = mean μ bulk) ∧
        (∀ᵐ x ∂μ, score x = -centered μ X x / variance μ X) :=
  (sqrt_equality_iff_squared X hbar P hdecomp hhbar).trans
    (squared_equality_iff hX hb hs hpair hbar P hdecomp hhbar)

end FoliationQM.ActualHeisenbergDefect
