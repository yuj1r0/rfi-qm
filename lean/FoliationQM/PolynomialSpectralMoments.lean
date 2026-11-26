module

public import FoliationQM.FrequencyGraphFourier
public import FoliationQM.GaussianMassShellMoments

/-!
# Spatial polynomial moments and actual Fourier graph moments

Source: v13 `cor:schrodinger`, component kinds C and D. A single continuous
spectral amplitude with all moments of the actual three-dimensional square
sum supplies the genuine integrability required for both physical envelope
frequencies and the original massive shell. The graph uses the product norm;
no identification of its squared norm with the spatial square sum is made.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.PolynomialSpectralMoments

open MeasureTheory LorentzCoordinates GaussianKGMode GaussianMassShellMoments
open ReducedMassShellFrequency

/-- All natural moments of the actual sum of the three spatial frequency squares are integrable. -/
def PolynomialMoments (A : Spatial → ℂ) : Prop :=
  ∀ n : ℕ, Integrable (fun k => speedSq k ^ n * ‖A k‖)

private theorem zero_rate_bound (k : Spatial) : rate 0 k ≤ 1 + speedSq k := by
  change Real.sqrt (0 ^ 2 + speedSq k) ≤ 1 + speedSq k
  apply Real.sqrt_le_iff.mpr
  constructor
  · linarith [speedSq_nonneg k]
  · nlinarith [speedSq_nonneg k, sq_nonneg (speedSq k)]

private theorem rate_bound (μ : ℝ) (k : Spatial) :
    rate μ k ≤ (|μ| + 1) * (1 + speedSq k) := by
  have hz : 0 ≤ rate 0 k := Real.sqrt_nonneg _
  have ht : rate μ k ≤ |μ| + rate 0 k := by
    change Real.sqrt (μ ^ 2 + speedSq k) ≤ |μ| + rate 0 k
    apply Real.sqrt_le_iff.mpr
    refine ⟨add_nonneg (abs_nonneg μ) hz, ?_⟩
    nlinarith [rate_sq 0 k, sq_abs μ, mul_nonneg (abs_nonneg μ) hz]
  calc
    _ ≤ |μ| + (1 + speedSq k) := ht.trans (add_le_add (le_refl _) (zero_rate_bound k))
    _ ≤ (|μ| + 1) * (1 + speedSq k) := by
      nlinarith [mul_nonneg (abs_nonneg μ) (speedSq_nonneg k)]

/-- A continuous temporal frequency with a quadratic spatial bound has every genuine graph moment for the same polynomially integrable amplitude. -/
theorem graph_moments_of_bound {w : Spatial → ℝ} {A : Spatial → ℂ}
    (hw : Continuous w) (hA : Continuous A) (hpoly : PolynomialMoments A)
    {C : ℝ} (hC : 1 ≤ C) (hb : ∀ k, |w k| ≤ C * (1 + speedSq k)) :
    FrequencyGraphFourier.HasMoments w A := by
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC
  have hn (k : Spatial) : ‖FrequencyGraphFourier.graph w k‖ ≤ C * (1 + speedSq k) := by
    have hq : 0 ≤ 1 + speedSq k := by linarith [speedSq_nonneg k]
    have hs (i : Fin 3) : |k i| ≤ C * (1 + speedSq k) := by
      exact ((abs_component_le_rate 0 k i).trans (zero_rate_bound k)).trans
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hC hq)
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC0 hq)).mpr
    intro i
    fin_cases i
    · simpa [FrequencyGraphFourier.graph, assemble, Real.norm_eq_abs] using hb k
    · simpa [FrequencyGraphFourier.graph, assemble, Real.norm_eq_abs] using hs 0
    · simpa [FrequencyGraphFourier.graph, assemble, Real.norm_eq_abs] using hs 1
    · simpa [FrequencyGraphFourier.graph, assemble, Real.norm_eq_abs] using hs 2
  have hzero : Integrable (fun k => ‖A k‖) := by simpa using hpoly 0
  intro n
  apply ((hzero.add (hpoly n)).const_mul (C ^ n * 2 ^ (n - 1))).mono'
    (((FrequencyGraphFourier.continuous_graph hw).norm.pow n).mul hA.norm).aestronglyMeasurable
  refine ae_of_all _ fun k => ?_
  change ‖‖FrequencyGraphFourier.graph w k‖ ^ n * ‖A k‖‖ ≤
    (C ^ n * 2 ^ (n - 1)) * (‖A k‖ + speedSq k ^ n * ‖A k‖)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _))]
  calc
    _ ≤ (C * (1 + speedSq k)) ^ n * ‖A k‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hn k) n) (norm_nonneg _)
    _ = C ^ n * (1 + speedSq k) ^ n * ‖A k‖ := by rw [mul_pow]
    _ ≤ C ^ n * (2 ^ (n - 1) * (1 ^ n + speedSq k ^ n)) * ‖A k‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (add_pow_le (by norm_num) (speedSq_nonneg k) n)
          (pow_nonneg hC0 _)) (norm_nonneg _)
    _ = (C ^ n * 2 ^ (n - 1)) * (‖A k‖ + speedSq k ^ n * ‖A k‖) := by
      rw [one_pow]
      ring

/-- The actual reduced massive and Schrödinger frequencies both have all graph moments for one fixed polynomially integrable spectrum. -/
theorem reduced_nr_moments (p : MassiveParameters) {A : Spatial → ℂ}
    (hA : Continuous A) (hpoly : PolynomialMoments A) :
    FrequencyGraphFourier.HasMoments (reducedFrequency p) A ∧
      FrequencyGraphFourier.HasMoments (schrodingerFrequency p) A := by
  let W : ℝ := p.hbar / (2 * p.m)
  let C : ℝ := max 1 W
  have hW : 0 ≤ W := (div_pos p.hbar_pos (mul_pos (by norm_num) p.m_pos)).le
  have hC : 1 ≤ C := le_max_left _ _
  have he (k : Spatial) : schrodingerFrequency p k = W * speedSq k := by
    dsimp only [schrodingerFrequency, W]
    ring
  have hb (k : Spatial) : W * speedSq k ≤ C * (1 + speedSq k) := by
    have h := mul_le_mul_of_nonneg_right (le_max_right 1 W) (speedSq_nonneg k)
    change W * speedSq k ≤ C * speedSq k at h
    nlinarith
  constructor
  · apply graph_moments_of_bound (continuous_frequencies p).1 hA hpoly hC
    intro k
    rw [abs_of_nonneg (frequency_comparison p k).1]
    exact (frequency_comparison p k).2.1.trans ((he k).trans_le (hb k))
  · apply graph_moments_of_bound (continuous_frequencies p).2 hA hpoly hC
    intro k
    rw [he, abs_of_nonneg (mul_nonneg hW (speedSq_nonneg k))]
    exact hb k

/-- The same polynomial spectral data supplies the original massive-shell moments at every fixed mass frequency. -/
theorem massShell_moments (μ : ℝ) {A : Spatial → ℂ}
    (hA : Continuous A) (hpoly : PolynomialMoments A) : MassShellFourier.HasMoments μ A := by
  have hw : Continuous (rate μ) := by unfold rate speedSq spatialDot; fun_prop
  have hm := graph_moments_of_bound hw hA hpoly
    (show 1 ≤ |μ| + 1 by linarith [abs_nonneg μ])
    (fun k => by
      rw [abs_of_nonneg (show 0 ≤ rate μ k from Real.sqrt_nonneg _)]
      exact rate_bound μ k)
  exact hm

end FoliationQM.PolynomialSpectralMoments
