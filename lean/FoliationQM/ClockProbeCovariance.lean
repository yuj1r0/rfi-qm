module

public import FoliationQM.ClockCircleAverage
public import FoliationQM.ClockScales
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Algebra.Order.Star.Real

/-!
# Actual three-axis circular probe covariance

Sources: v13 `thm:clock_sideband`, `eq:s1_circle_variance`, and the covariance
contraction in `eq:kl_fisher_expansion`. Three independent coordinates are
modeled by normalized iterated genuine circle integrals. Their zero means
and covariance are calculated, not supplied as independence assumptions.
The stipulated radius is specialized to the derived Compton radius only
after proving the general covariance and its positive definiteness.
These moment and contraction identities do not assert a translated KL
Hessian, a remainder bound, or any Lorentzian positivity statement.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.ClockProbeCovariance

open MeasureTheory (volume)
open Matrix
open ClockCircleAverage

/-- The three independent physical clock phases, integrated in coordinate order. -/
def average3 (f : (Fin 3 → ℝ) → ℝ) : ℝ :=
  average (fun t0 => average (fun t1 => average (fun t2 => f ![t0, t1, t2])))

/-- Explicit integrability of all three stages of the iterated circle average. -/
def IteratedIntegrable (f : (Fin 3 → ℝ) → ℝ) : Prop :=
  (∀ t0 t1, IntervalIntegrable (fun t2 => f ![t0, t1, t2]) volume 0 (2 * Real.pi)) ∧
  (∀ t0, IntervalIntegrable (fun t1 => average (fun t2 => f ![t0, t1, t2]))
    volume 0 (2 * Real.pi)) ∧
  IntervalIntegrable (fun t0 => average (fun t1 => average (fun t2 => f ![t0, t1, t2])))
    volume 0 (2 * Real.pi)

/-- Constants retain their value under the normalized three-circle average. -/
theorem average3_const (c : ℝ) : average3 (fun _ => c) = c := by
  simp [average3, average_const]

/-- A real scalar factors out of the actual iterated integral. -/
theorem average3_const_mul (c : ℝ) (f : (Fin 3 → ℝ) → ℝ) :
    average3 (fun θ => c * f θ) = c * average3 f := by
  simp only [average3, average_const_mul]

/-- Separated coordinates factor by the actual three successive integrals.
This identity does not postulate their moments. -/
theorem average3_product (f0 f1 f2 : ℝ → ℝ) :
    average3 (fun θ => f0 (θ 0) * f1 (θ 1) * f2 (θ 2)) =
      average f0 * average f1 * average f2 := by
  simp only [average3, cons_val_zero, cons_val_one, cons_val_two, head_cons, tail_cons]
  simp only [average_const_mul, average_mul_const]

/-- Integrable separated factors give genuine integrability at every stage. -/
theorem iteratedIntegrable_product (f0 f1 f2 : ℝ → ℝ)
    (h0 : IntervalIntegrable f0 volume 0 (2 * Real.pi))
    (h1 : IntervalIntegrable f1 volume 0 (2 * Real.pi))
    (h2 : IntervalIntegrable f2 volume 0 (2 * Real.pi)) :
    IteratedIntegrable (fun θ => f0 (θ 0) * f1 (θ 1) * f2 (θ 2)) := by
  simp only [IteratedIntegrable, cons_val_zero, cons_val_one, cons_val_two, head_cons, tail_cons]
  constructor
  · intro t0 t1
    exact h2.const_mul (f0 t0 * f1 t1)
  constructor
  · intro t0
    simp_rw [average_const_mul]
    exact (h1.const_mul (f0 t0)).mul_const (average f2)
  · simp only [average_const_mul, average_mul_const]
    exact (h0.mul_const (average f1)).mul_const (average f2)

/-- The source displacement along each laboratory axis at stipulated radius ell. -/
def displacement (ell : ℝ) (θ : Fin 3 → ℝ) (i : Fin 3) : ℝ := ell * Real.cos (θ i)

/-- The actual mean of one coordinate of the three-axis probe. -/
def mean (ell : ℝ) (i : Fin 3) : ℝ := average3 (fun θ => displacement ell θ i)

/-- The actual centered covariance, formed from the actual iterated means. -/
def covariance (ell : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := fun i j =>
  average3 (fun θ => (displacement ell θ i - mean ell i) *
    (displacement ell θ j - mean ell j))

/-- Unshifted cosine has zero actual normalized circle mean. -/
theorem average_cos : average Real.cos = 0 := by
  simpa only [zero_add] using ClockCircleAverage.average_cos 0

/-- Unshifted squared cosine has actual normalized circle mean one half. -/
theorem average_cos_sq : average (fun t => Real.cos t ^ 2) = 1 / 2 := by
  simpa only [zero_add] using ClockCircleAverage.average_cos_sq 0

/-- Each physical coordinate cosine has zero mean under the actual product average. -/
theorem average3_cos_coordinate (i : Fin 3) :
    average3 (fun θ => Real.cos (θ i)) = 0 := by
  fin_cases i <;> simp [average3, average_const, average_cos]

/-- The actual two-coordinate cosine moments are the diagonal one-half matrix. -/
theorem average3_cos_product (i j : Fin 3) :
    average3 (fun θ => Real.cos (θ i) * Real.cos (θ j)) =
      (1 / 2 : ℝ) * if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [average3, average_const, average_const_mul, average_mul_const,
      average_cos, ← pow_two, average_cos_sq]

/-- Every stipulated three-axis displacement has its derived zero mean. -/
theorem mean_zero (ell : ℝ) (i : Fin 3) : mean ell i = 0 := by
  change average3 (fun θ => ell * Real.cos (θ i)) = 0
  rw [average3_const_mul, average3_cos_coordinate, mul_zero]

/-- Each probe mean uses genuinely integrable inner, middle, and outer sections. -/
theorem iteratedIntegrable_displacement (ell : ℝ) (i : Fin 3) :
    IteratedIntegrable (fun θ => displacement ell θ i) := by
  fin_cases i <;>
    simp only [IteratedIntegrable, displacement, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, cons_val_zero, cons_val_one, cons_val_two, head_cons, tail_cons,
      average_const, average_const_mul, average_cos, mul_zero]
  all_goals
    refine ⟨?_, ?_, ?_⟩
    · intro t0 t1
      exact Continuous.intervalIntegrable (by fun_prop) _ _
    · intro t0
      exact Continuous.intervalIntegrable (by fun_prop) _ _
    · exact Continuous.intervalIntegrable (by fun_prop) _ _

/-- Products of the source displacements have genuine iterated integrability. -/
theorem iteratedIntegrable_displacement_product (ell : ℝ) (i j : Fin 3) :
    IteratedIntegrable (fun θ => displacement ell θ i * displacement ell θ j) := by
  have he : (fun θ => displacement ell θ i * displacement ell θ j) =
      (fun θ => ell ^ 2 * (Real.cos (θ i) * Real.cos (θ j))) := by
    funext θ
    simp only [displacement]
    ring
  rw [he]
  fin_cases i <;> fin_cases j <;>
    simp only [IteratedIntegrable, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, cons_val_zero, cons_val_one, cons_val_two, head_cons, tail_cons,
      average_const, average_const_mul, average_mul_const, average_cos, mul_zero,
      ← pow_two, average_cos_sq]
  all_goals
    refine ⟨?_, ?_, ?_⟩
    · intro t0 t1
      exact Continuous.intervalIntegrable (by fun_prop) _ _
    · intro t0
      exact Continuous.intervalIntegrable (by fun_prop) _ _
    · exact Continuous.intervalIntegrable (by fun_prop) _ _

/-- The full source covariance is calculated from the actual centered moments. -/
theorem covariance_apply (ell : ℝ) (i j : Fin 3) :
    covariance ell i j = ell ^ 2 / 2 * if i = j then 1 else 0 := by
  simp only [covariance, mean_zero, sub_zero]
  have he : (fun θ => displacement ell θ i * displacement ell θ j) =
      (fun θ => ell ^ 2 * (Real.cos (θ i) * Real.cos (θ j))) := by
    funext θ
    simp only [displacement]
    ring
  rw [he, average3_const_mul, average3_cos_product]
  ring

/-- The centered covariance integrals also have genuine iterated integrability. -/
theorem iteratedIntegrable_centered_product (ell : ℝ) (i j : Fin 3) :
    IteratedIntegrable (fun θ => (displacement ell θ i - mean ell i) *
      (displacement ell θ j - mean ell j)) := by
  simpa only [mean_zero, sub_zero] using iteratedIntegrable_displacement_product ell i j

/-- The actual covariance matrix is precisely the source diagonal matrix. -/
theorem covariance_eq_diagonal (ell : ℝ) :
    covariance ell = Matrix.diagonal (fun _ => ell ^ 2 / 2) := by
  ext i j
  simp only [covariance_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

/-- Positive stipulated radius makes the actual three-dimensional covariance
positive definite, including all off-diagonal zero entries. -/
theorem covariance_posDef (ell : ℝ) (hell : 0 < ell) : (covariance ell).PosDef := by
  rw [covariance_eq_diagonal]
  exact Matrix.PosDef.diagonal (fun _ => div_pos (sq_pos_of_pos hell) (by norm_num))

/-- The spatial covariance contraction with any real matrix is half the
squared radius times its trace; symmetry is not needed for this algebra. -/
theorem covariance_contraction (ell : ℝ) (I : Matrix (Fin 3) (Fin 3) ℝ) :
    (∑ i, ∑ j, covariance ell i j * I i j) = ell ^ 2 / 2 * Matrix.trace I := by
  simp only [covariance_eq_diagonal, Matrix.diagonal_apply]
  simp [Matrix.trace, Finset.mul_sum]

/-- The derived Compton radius makes the actual covariance positive definite. -/
theorem compton_covariance_posDef (p : MassiveParameters) : (covariance p.ellC).PosDef :=
  covariance_posDef p.ellC (ClockScales.ellC_pos p)

/-- Substitution of the derived radius gives the literal source covariance entries. -/
theorem compton_covariance_apply (p : MassiveParameters) (i j : Fin 3) :
    covariance p.ellC i j = p.hbar ^ 2 / (2 * p.m ^ 2 * p.c ^ 2) *
      if i = j then 1 else 0 := by
  rw [covariance_apply]
  have hm := p.m_pos.ne'
  have hc := p.c_pos.ne'
  unfold MassiveParameters.ellC
  field_simp

/-- The source Hessian prefactor contracted with the actual probe covariance
is exactly hbar squared over four times spatial Fisher trace. This is a
coefficient identity, not a proof that any KL Hessian equals that matrix. -/
theorem compton_fisher_coefficient (p : MassiveParameters) (I : Matrix (Fin 3) (Fin 3) ℝ) :
    (p.m ^ 2 * p.c ^ 2 / 2) * (∑ i, ∑ j, covariance p.ellC i j * I i j) =
      p.hbar ^ 2 / 4 * Matrix.trace I := by
  rw [covariance_contraction]
  have hm := p.m_pos.ne'
  have hc := p.c_pos.ne'
  unfold MassiveParameters.ellC
  field_simp
  ring

end FoliationQM.ClockProbeCovariance
