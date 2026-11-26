module
public import FoliationQM.TwistedScalarAngles

/-!
# Quantitative chiral derivative control for the actual density

The four-coordinate bound gives a sufficient local control for the
scalar limit in v13 `thm:dirac_lift`. The spinor density of a fixed
differentiable scalar field then converges to its Klein–Gordon density.
-/

@[expose] public section
noncomputable section
open scoped Topology
namespace FoliationQM.TwistedScalarControl
open Filter RealLorentzFrame ScalarSpinDefect TwistedScalarDensity

/-- The absolute Lorentzian square is bounded by the sum of all four ordinary squares. -/
theorem abs_square_le (v : Covector) : |minkowski v v| ≤ ∑ μ, (v μ)^2 := by
  rw [← signed_square]
  calc
    _ ≤ ∑ μ, |sign μ * (v μ)^2| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro μ _
      have hs : |sign μ| = 1 := by unfold sign; split <;> norm_num
      rw [abs_mul, hs, one_mul, abs_of_nonneg (sq_nonneg _)]

/-- A bound on each true coordinate derivative bounds the potential with constant ℏ². -/
theorem abs_potential_le (p : MassiveParameters) (β : Covector → ℝ) (x : Covector) {M : ℝ}
    (hM : ∀ μ, |gradient β x μ| ≤ M) : |potential p β x| ≤ p.hbar ^ 2 * M ^ 2 := by
  have hb : (∑ μ, (gradient β x μ)^2) ≤ ∑ _μ : Fin 4, M^2 := by
    apply Finset.sum_le_sum
    intro μ _
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans (hM μ))).2 (hM μ)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] at hb
  unfold potential
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ p.hbar^2/4)]
  nlinarith [mul_le_mul_of_nonneg_left ((abs_square_le _).trans hb) (by positivity : 0 ≤ p.hbar^2/4)]

/-- The absolute density discrepancy of any differentiable field is bounded by its squared modulus
times ℏ² times the square of the common bound on the four angle derivatives. -/
theorem abs_density_sub_le (p : MassiveParameters) {β : Covector → ℝ} {z : Covector → ℂ} {x : Covector}
    (hβ : DifferentiableAt ℝ β x) (hz : DifferentiableAt ℝ z x) {M : ℝ} (hM : ∀ μ, |gradient β x μ| ≤ M) :
    |density p β z x - (ActionVariation.fieldPairing p z z DiracFieldDensity.coordinateDirections x).re| ≤
      p.hbar^2 * M^2 * Complex.normSq (z x) := by
  rw [density_eq_pairing p hβ hz]
  simp only [sub_sub_cancel_left, abs_neg, abs_mul, abs_of_nonneg (Complex.normSq_nonneg _)]
  exact mul_le_mul_of_nonneg_right (abs_potential_le p β x hM) (Complex.normSq_nonneg _)

/-- At each point, convergence of the actual gradient to zero gives convergence of the potential. -/
theorem tendsto_potential_zero (p : MassiveParameters) {ι : Type*} {l : Filter ι}
    {β : ι → Covector → ℝ} {x : Covector} (hg : Tendsto (fun i => gradient (β i) x) l (𝓝 0)) :
    Tendsto (fun i => potential p (β i) x) l (𝓝 0) := by
  have hc : Continuous (fun v : Covector => (p.hbar^2/4) * minkowski v v) := by unfold minkowski; fun_prop
  simpa [potential, minkowski, Function.comp_def] using (hc.tendsto (0 : Covector)).comp hg

/-- Derivative control gives pointwise density convergence on the actual chiral spinors,
including at zeros of the underlying fixed scalar field. -/
theorem tendsto_density (p : MassiveParameters) {ι : Type*} {l : Filter ι} {β : ι → Covector → ℝ}
    {z : Covector → ℂ} {x : Covector} (hz : DifferentiableAt ℝ z x)
    (hb : ∀ᶠ i in l, DifferentiableAt ℝ (β i) x) (hg : Tendsto (fun i => gradient (β i) x) l (𝓝 0)) :
    Tendsto (fun i => density p (β i) z x) l
      (𝓝 (ActionVariation.fieldPairing p z z DiracFieldDensity.coordinateDirections x).re) := by
  have he := (tendsto_potential_zero p hg).mul_const (Complex.normSq (z x))
  apply Tendsto.congr' (hb.mono (fun i hi => (density_eq_pairing p hi hz).symm))
  simpa using (tendsto_const_nhds (x := (ActionVariation.fieldPairing p z z DiracFieldDensity.coordinateDirections x).re)).sub he

end FoliationQM.TwistedScalarControl
