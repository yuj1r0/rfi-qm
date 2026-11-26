module

public import FoliationQM.RNCMetricTaylor
public import FoliationQM.LorentzCayleySmooth

/-!
# The normal-coordinate expansion of the inverse metric

Source: v13 `eq:inverse_rnc` in the derivation of Conjecture 9.7
(`thm:tidal_dispersion`), "`g^{μν}(y) = η^{μν} + (1/3) R^{μ ν}_{ α β}(x₀)
y^α y^β + O(|y|³)`", component kinds B and C. For a three times continuously
differentiable metric in an orthonormal radial normal chart, every component
of the inverse metric is the Minkowski value plus one third of the curvature
quadratic form with the first and third indices raised by the Minkowski
signs, up to a cubic remainder.

The proof uses the covariant expansion `g = η - (1/3) Q + O(|y|³)`, with
`Q_{ij} = R_{iajb} y^a y^b`, and the exact identity
`g⁻¹ - P̃ = g⁻¹ [(1 - P P̃) - (g - P) P̃]` for `P = η - (1/3) Q` and
`P̃ = η + (1/3) η Q η`, where `1 - P P̃ = (1/9) (Q η)²` is quartic.

The curvature components are those of the metric at the centre. Averaging
the quadratic term over the geodesic cell is a separate algebraic statement;
the physical ansatz of the conjecture is not addressed.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.RNCInverseMetricTaylor

open Asymptotics Filter Matrix LorentzMatrixGroup RNCCoordinateConnection RNCNormalChart
open RNCNormalRiemann RNCMetricTaylor RealLorentzFrame
open scoped Topology Matrix.Norms.Operator

variable {g : Covector → Mat4}

/-- The curvature quadratic form `Q_{ij}(y) = R_{iajb} y^a y^b` at the centre. -/
def quadratic (g : Covector → Mat4) (y : Covector) : Mat4 :=
  Matrix.of fun i j => ∑ a, ∑ b, loweredRiemann g 0 i a j b * y a * y b

/-- A product of two coordinates is quadratically small. -/
theorem monomial_isBigO (a b : Fin 4) :
    (fun y : Covector => y a * y b) =O[𝓝 0] fun y => ‖y‖ ^ 2 := by
  refine IsBigO.of_bound 1 (Eventually.of_forall fun y => ?_)
  rw [one_mul, norm_mul, norm_pow, norm_norm, sq]
  exact mul_le_mul (norm_le_pi_norm y a) (norm_le_pi_norm y b) (norm_nonneg _) (norm_nonneg _)

/-- The curvature quadratic form is quadratically small. -/
theorem quadratic_isBigO (g : Covector → Mat4) (i j : Fin 4) :
    (fun y => quadratic g y i j) =O[𝓝 0] fun y => ‖y‖ ^ 2 := by
  simp only [quadratic, of_apply]
  refine IsBigO.fun_sum fun a _ => IsBigO.fun_sum fun b _ => ?_
  simpa only [mul_assoc] using (monomial_isBigO a b).const_mul_left (loweredRiemann g 0 i a j b)

/-- Entries of a product of matrix fields with entrywise bounds are bounded
by the product of the bounds. -/
theorem isBigO_mul_entry {A C : Covector → Mat4} {f k : Covector → ℝ}
    (hA : ∀ i l, (fun y => A y i l) =O[𝓝 0] f) (hC : ∀ l j, (fun y => C y l j) =O[𝓝 0] k)
    (i j : Fin 4) : (fun y => (A y * C y) i j) =O[𝓝 0] fun y => f y * k y := by
  simp only [Matrix.mul_apply]
  exact IsBigO.fun_sum fun l _ => (hA i l).mul (hC l j)

/-- The inverse metric in a normal chart is `η^{μν} + (1/3) R^{μ ν}_{α β} y^α y^β`
up to a cubic remainder, with indices raised by the Minkowski signs. -/
theorem inverse_expansion (h : IsNormal g) (hg : ContDiffAt ℝ 3 g 0) (i j : Fin 4) :
    (fun y => (g y)⁻¹ i j - (eta i j + (1 / 3 : ℝ) *
        ∑ a, ∑ b, sign i * sign j * loweredRiemann g 0 i a j b * y a * y b))
      =O[𝓝 0] fun y => ‖y‖ ^ 3 := by
  obtain ⟨Q, hQ⟩ : ∃ Q : Covector → Mat4, Q = quadratic g := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : Covector → Mat4, P = fun y => eta - (1 / 3 : ℝ) • Q y := ⟨_, rfl⟩
  obtain ⟨Pt, hPt⟩ : ∃ Pt : Covector → Mat4,
      Pt = fun y => eta + (1 / 3 : ℝ) • (eta * Q y * eta) := ⟨_, rfl⟩
  have hQO : ∀ i j, (fun y => Q y i j) =O[𝓝 0] fun y => ‖y‖ ^ 2 := fun i j => by
    rw [hQ]
    exact quadratic_isBigO g i j
  have hrem : ∀ i j, (fun y => (g y - P y) i j) =O[𝓝 0] fun y => ‖y‖ ^ 3 := fun i j => by
    have h1 := component_expansion h hg i j
    simpa only [hP, hQ, quadratic, Matrix.sub_apply, Matrix.smul_apply, of_apply, smul_eq_mul] using h1
  have hPtentry : ∀ y i j, Pt y i j = eta i j + (1 / 3 : ℝ) *
      ∑ a, ∑ b, sign i * sign j * loweredRiemann g 0 i a j b * y a * y b := by
    intro y i j
    have e : (eta * Q y * eta) i j = sign i * Q y i j * sign j := by
      simp only [eta, diagonal_mul, mul_diagonal]
    rw [hPt]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [e, hQ]
    simp only [quadratic, of_apply]
    congr 2
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have hPtO : ∀ i j, (fun y => Pt y i j) =O[𝓝 0] fun _ => (1 : ℝ) := fun i j => by
    have hc : Continuous fun y => Pt y i j := by
      simp only [hPtentry]
      fun_prop
    exact hc.continuousAt.isBigO_one ℝ
  have hinv : ∀ i j, (fun y => (g y)⁻¹ i j) =O[𝓝 0] fun _ => (1 : ℝ) := fun i j => by
    let L : Mat4 →L[ℝ] ℝ := (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap
    have hc : ContinuousAt (fun y => (g y)⁻¹) 0 :=
      ContinuousAt.comp (g := fun N : Mat4 => N⁻¹)
        (LorentzCayleySmooth.contDiffAt_inverse 0 (center_unit h)).continuousAt hg.continuousAt
    exact (L.continuous.continuousAt.comp hc).isBigO_one ℝ
  have hQη : ∀ i j, (fun y => (Q y * eta) i j) =O[𝓝 0] fun y => ‖y‖ ^ 2 := fun i j => by
    have e : (fun y => (Q y * eta) i j) = fun y => sign j * Q y i j := by
      funext y
      simp only [eta, mul_diagonal, mul_comm]
    rw [e]
    exact (hQO i j).const_mul_left (sign j)
  have hquart : (fun y : Covector => ‖y‖ ^ 2 * ‖y‖ ^ 2) =O[𝓝 0] fun y => ‖y‖ ^ 3 := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [Metric.ball_mem_nhds (0 : Covector) one_pos] with y hy
    have hy1 : ‖y‖ ≤ 1 := (mem_ball_zero_iff.mp hy).le
    have hy0 : 0 ≤ ‖y‖ := norm_nonneg y
    simp only [norm_mul, norm_pow, norm_norm, one_mul]
    nlinarith [mul_nonneg (pow_nonneg hy0 3) (sub_nonneg.mpr hy1)]
  have hZid : ∀ y, 1 - P y * Pt y = (1 / 9 : ℝ) • (Q y * eta * (Q y * eta)) := by
    intro y
    have h1 : eta * (eta * Q y * eta) = Q y * eta := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, eta_sq, Matrix.one_mul]
    simp only [hP, hPt, sub_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, eta_sq, h1,
      smul_smul, ← Matrix.mul_assoc]
    module
  have hZ : ∀ i j, (fun y => (1 - P y * Pt y) i j) =O[𝓝 0] fun y => ‖y‖ ^ 3 := fun i j => by
    have e : (fun y => (1 - P y * Pt y) i j) =
        fun y => (1 / 9 : ℝ) * (Q y * eta * (Q y * eta)) i j := by
      funext y
      rw [hZid y, Matrix.smul_apply, smul_eq_mul]
    rw [e]
    exact ((isBigO_mul_entry hQη hQη i j).const_mul_left (1 / 9)).trans hquart
  have hW : ∀ i j, (fun y => ((1 - P y * Pt y) - (g y - P y) * Pt y) i j) =O[𝓝 0]
      fun y => ‖y‖ ^ 3 := fun i j => by
    have h1 := isBigO_mul_entry hrem hPtO i j
    simp only [mul_one] at h1
    simpa only [Matrix.sub_apply] using (hZ i j).sub h1
  have hfin := isBigO_mul_entry hinv hW i j
  have hdet : ∀ᶠ y in 𝓝 (0 : Covector), (g y).det ≠ 0 := by
    have hc : ContinuousAt (fun y => (g y).det) 0 :=
      ContinuousAt.comp (g := fun N : Mat4 => N.det)
        (Continuous.matrix_det continuous_id).continuousAt hg.continuousAt
    exact hc.eventually_ne ((Matrix.isUnit_iff_isUnit_det _).mp (center_unit h)).ne_zero
  refine hfin.congr' ?_ (Eventually.of_forall fun y => one_mul _)
  filter_upwards [hdet] with y hy
  have hunit : IsUnit (g y).det := isUnit_iff_ne_zero.mpr hy
  have hW' : (1 - P y * Pt y) - (g y - P y) * Pt y = 1 - g y * Pt y := by
    rw [sub_mul]
    abel
  have hmat : (g y)⁻¹ * ((1 - P y * Pt y) - (g y - P y) * Pt y) = (g y)⁻¹ - Pt y := by
    rw [hW', mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hunit,
      Matrix.one_mul]
  rw [hmat, Matrix.sub_apply, hPtentry]

end FoliationQM.RNCInverseMetricTaylor
