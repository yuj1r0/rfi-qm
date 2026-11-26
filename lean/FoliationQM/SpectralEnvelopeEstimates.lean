module

public import FoliationQM.ReducedPlaneWaveComparison
public import FoliationQM.PolynomialSpectralMoments

/-!
# Quantitative bounds for the actual spectral envelopes

Source: v13 `cor:schrodinger`, component kinds C and D. One fixed complex
spectrum supplies finite fourth and sixth spatial moments. The actual
integral and its true derivatives inherit the same-mode comparison bounds,
with genuine integrability on both sides of every integral comparison.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.SpectralEnvelopeEstimates

open MeasureTheory LorentzCoordinates PolarSecondDifferential
open ReducedMassShellFrequency PolynomialSpectralMoments
open FrequencyGraphFourier
open Madelung (coordinateVector)

/-- The actual moment of the spatial square sum against the modulus of one fixed spectrum. -/
def moment (A : Spatial → ℂ) (n : ℕ) : ℝ := ∫ k, speedSq k ^ n * ‖A k‖

private theorem first_kernel (w : Spatial → ℝ) (A : Spatial → ℂ)
    (i : Fin 4) (x : Covector) (k : Spatial) :
    directionalDerivative (ReducedPlaneWave.mode (w k) k) (coordinateVector i) x * A k =
      ReducedPlaneWave.mode (w k) k x * differentiated w i A k := by
  fin_cases i <;>
    simp [ReducedPlaneWave.directional_mode, differentiated, graph, assemble,
      coordinateVector, spatialDot] <;> ring

private theorem second_kernel (w : Spatial → ℝ) (A : Spatial → ℂ)
    (i : Fin 4) (x : Covector) (k : Spatial) :
    secondDirectionalDerivative (ReducedPlaneWave.mode (w k) k) (coordinateVector i) x * A k =
      ReducedPlaneWave.mode (w k) k x * differentiated w i (differentiated w i A) k := by
  fin_cases i <;>
    simp [ReducedPlaneWave.second_directional_mode, differentiated, graph, assemble,
      coordinateVector, spatialDot] <;> ring_nf <;>
    simp only [Complex.I_sq, mul_neg, mul_one]

private theorem first_integral {w : Spatial → ℝ} {A : Spatial → ℂ}
    (hw : Continuous w) (hA : Continuous A) (hm : HasMoments w A) (i : Fin 4) (x : Covector) :
    Integrable (fun k =>
      directionalDerivative (ReducedPlaneWave.mode (w k) k) (coordinateVector i) x * A k) ∧
      directionalDerivative (wave w A) (coordinateVector i) x =
        ∫ k, directionalDerivative (ReducedPlaneWave.mode (w k) k) (coordinateVector i) x * A k := by
  have hd := differentiated_data hw hA hm i
  have he := funext (first_kernel w A i x)
  refine ⟨?_, ?_⟩
  · rw [he]
    exact integrable_mode hw hd.1 hd.2 x
  · rw [first_coordinate hw hA hm i, he]
    rfl

private theorem second_integral {w : Spatial → ℝ} {A : Spatial → ℂ}
    (hw : Continuous w) (hA : Continuous A) (hm : HasMoments w A) (i : Fin 4) (x : Covector) :
    Integrable (fun k =>
      secondDirectionalDerivative (ReducedPlaneWave.mode (w k) k) (coordinateVector i) x * A k) ∧
      secondDirectionalDerivative (wave w A) (coordinateVector i) x =
        ∫ k, secondDirectionalDerivative (ReducedPlaneWave.mode (w k) k) (coordinateVector i) x * A k := by
  have hd := differentiated_data hw hA hm i
  have hd₂ := differentiated_data hw hd.1 hd.2 i
  have he := funext (second_kernel w A i x)
  refine ⟨?_, ?_⟩
  · rw [he]
    exact integrable_mode hw hd₂.1 hd₂.2 x
  · rw [second_coordinate hw hA hm i, he]
    rfl

private theorem integral_gap {f g : Spatial → ℂ} {b : Spatial → ℝ}
    (hf : Integrable f) (hg : Integrable g) (hb : Integrable b)
    (h : ∀ k, ‖f k - g k‖ ≤ b k) :
    ‖(∫ k, f k) - (∫ k, g k)‖ ≤ ∫ k, b k := by
  rw [← integral_sub hf hg]
  exact (norm_integral_le_integral_norm _).trans (integral_mono (hf.sub hg).norm hb h)

/-- On a fixed time slab, the actual reduced and Schrödinger waves differ by the fourth moment times the inverse-square speed factor. -/
theorem field_gap (p : MassiveParameters) {A : Spatial → ℂ}
    (hA : Continuous A) (hpoly : PolynomialMoments A) {T : ℝ} (hT : 0 ≤ T)
    {x : Covector} (hx : |x 0| ≤ T) :
    ‖wave (reducedFrequency p) A x - wave (schrodingerFrequency p) A x‖ ≤
      T * (p.hbar ^ 3 / (8 * p.m ^ 3)) * moment A 2 / p.c ^ 2 := by
  let C := p.hbar ^ 3 / (8 * p.m ^ 3)
  have hm := reduced_nr_moments p hA hpoly
  have hw := continuous_frequencies p
  have hf := integrable_mode hw.1 hA hm.1 x
  have hg := integrable_mode hw.2 hA hm.2 x
  have hb := (hpoly 2).const_mul (T * C / p.c ^ 2)
  change ‖(∫ k, ReducedPlaneWave.mode (reducedFrequency p k) k x * A k) -
    (∫ k, ReducedPlaneWave.mode (schrodingerFrequency p k) k x * A k)‖ ≤ _
  calc
    _ ≤ ∫ k, (T * C / p.c ^ 2) * (speedSq k ^ 2 * ‖A k‖) := by
      apply integral_gap hf hg hb
      intro k
      rw [← sub_mul, norm_mul]
      calc
        _ ≤ (|x 0| * C * speedSq k ^ 2 / p.c ^ 2) * ‖A k‖ :=
          mul_le_mul_of_nonneg_right (ReducedPlaneWaveComparison.field_gap p k x) (norm_nonneg _)
        _ ≤ (T * C * speedSq k ^ 2 / p.c ^ 2) * ‖A k‖ := by
          have hmpos := p.m_pos
          have hhpos := p.hbar_pos
          have hB : 0 ≤ C * speedSq k ^ 2 / p.c ^ 2 * ‖A k‖ := by
            dsimp [C]
            positivity
          convert mul_le_mul hx (le_refl _) hB hT using 1 <;> ring
        _ = (T * C / p.c ^ 2) * (speedSq k ^ 2 * ‖A k‖) := by ring
    _ = _ := by
      rw [integral_const_mul]
      change (T * C / p.c ^ 2) * moment A 2 = _
      dsimp [C]
      ring

/-- The actual first-time derivative error retains both frequency and phase contributions, controlled by the fourth and sixth moments. -/
theorem time_first_gap (p : MassiveParameters) {A : Spatial → ℂ}
    (hA : Continuous A) (hpoly : PolynomialMoments A) {T : ℝ} (hT : 0 ≤ T)
    {x : Covector} (hx : |x 0| ≤ T) :
    ‖directionalDerivative (wave (reducedFrequency p) A) (coordinateVector 0) x -
      directionalDerivative (wave (schrodingerFrequency p) A) (coordinateVector 0) x‖ ≤
      (p.hbar ^ 3 / (8 * p.m ^ 3)) *
        (moment A 2 + T * (p.hbar / (2 * p.m)) * moment A 3) / p.c ^ 2 := by
  let C := p.hbar ^ 3 / (8 * p.m ^ 3)
  let W := p.hbar / (2 * p.m)
  have hm := reduced_nr_moments p hA hpoly
  have hw := continuous_frequencies p
  have hf := first_integral hw.1 hA hm.1 0 x
  have hg := first_integral hw.2 hA hm.2 0 x
  have hb := ((hpoly 2).add ((hpoly 3).const_mul (T * W))).const_mul (C / p.c ^ 2)
  rw [hf.2, hg.2]
  calc
    _ ≤ ∫ k, (C / p.c ^ 2) *
        (speedSq k ^ 2 * ‖A k‖ + (T * W) * (speedSq k ^ 3 * ‖A k‖)) := by
      apply integral_gap hf.1 hg.1 hb
      intro k
      rw [← sub_mul, norm_mul]
      calc
        _ ≤ (C * (speedSq k ^ 2 + |x 0| * W * speedSq k ^ 3) / p.c ^ 2) * ‖A k‖ :=
          mul_le_mul_of_nonneg_right (ReducedPlaneWaveComparison.time_first_gap p k x) (norm_nonneg _)
        _ ≤ (C * (speedSq k ^ 2 + T * W * speedSq k ^ 3) / p.c ^ 2) * ‖A k‖ := by
          have hmpos := p.m_pos
          have hhpos := p.hbar_pos
          have hq := speedSq_nonneg k
          have hB : 0 ≤ C * W * speedSq k ^ 3 / p.c ^ 2 * ‖A k‖ := by
            dsimp [C, W]
            positivity
          have he := mul_le_mul hx (le_refl _) hB hT
          convert add_le_add_left he (C * speedSq k ^ 2 / p.c ^ 2 * ‖A k‖) using 1 <;> ring
        _ = _ := by
          change _ = C / p.c ^ 2 *
            (speedSq k ^ 2 * ‖A k‖ + T * W * (speedSq k ^ 3 * ‖A k‖))
          ring
    _ = _ := by
      rw [integral_const_mul, integral_add (hpoly 2) ((hpoly 3).const_mul (T * W)),
        integral_const_mul]
      change (C / p.c ^ 2) * (moment A 2 + (T * W) * moment A 3) = _
      dsimp [C, W]
      ring

/-- Each actual spatial second-derivative error is controlled by the sixth moment uniformly on a fixed time slab. -/
theorem spatial_second_gap (p : MassiveParameters) {A : Spatial → ℂ}
    (hA : Continuous A) (hpoly : PolynomialMoments A) {T : ℝ} (hT : 0 ≤ T)
    {x : Covector} (hx : |x 0| ≤ T) (i : Fin 3) :
    ‖secondDirectionalDerivative (wave (reducedFrequency p) A) (coordinateVector i.succ) x -
      secondDirectionalDerivative (wave (schrodingerFrequency p) A) (coordinateVector i.succ) x‖ ≤
      T * (p.hbar ^ 3 / (8 * p.m ^ 3)) * moment A 3 / p.c ^ 2 := by
  let C := p.hbar ^ 3 / (8 * p.m ^ 3)
  have hm := reduced_nr_moments p hA hpoly
  have hw := continuous_frequencies p
  have hf := second_integral hw.1 hA hm.1 i.succ x
  have hg := second_integral hw.2 hA hm.2 i.succ x
  have hb := (hpoly 3).const_mul (T * C / p.c ^ 2)
  rw [hf.2, hg.2]
  calc
    _ ≤ ∫ k, (T * C / p.c ^ 2) * (speedSq k ^ 3 * ‖A k‖) := by
      apply integral_gap hf.1 hg.1 hb
      intro k
      rw [← sub_mul, norm_mul]
      calc
        _ ≤ (|x 0| * C * speedSq k ^ 3 / p.c ^ 2) * ‖A k‖ :=
          mul_le_mul_of_nonneg_right (ReducedPlaneWaveComparison.spatial_second_gap p k x i)
            (norm_nonneg _)
        _ ≤ (T * C * speedSq k ^ 3 / p.c ^ 2) * ‖A k‖ := by
          have hmpos := p.m_pos
          have hhpos := p.hbar_pos
          have hq := speedSq_nonneg k
          have hB : 0 ≤ C * speedSq k ^ 3 / p.c ^ 2 * ‖A k‖ := by
            dsimp [C]
            positivity
          convert mul_le_mul hx (le_refl _) hB hT using 1 <;> ring
        _ = _ := by ring
    _ = _ := by
      rw [integral_const_mul]
      change (T * C / p.c ^ 2) * moment A 3 = _
      dsimp [C]
      ring

/-- A nonnegative fourth-moment constant bounds the actual second time derivative at every spacetime point, independently of the speed parameter. -/
theorem time_second_bound (p : MassiveParameters) {A : Spatial → ℂ}
    (hA : Continuous A) (hpoly : PolynomialMoments A) :
    0 ≤ (p.hbar / (2 * p.m)) ^ 2 * moment A 2 ∧
      ∀ x, ‖secondDirectionalDerivative (wave (reducedFrequency p) A) (coordinateVector 0) x‖ ≤
        (p.hbar / (2 * p.m)) ^ 2 * moment A 2 := by
  have hM : 0 ≤ moment A 2 :=
    integral_nonneg (fun k => mul_nonneg (sq_nonneg _) (norm_nonneg _))
  refine ⟨mul_nonneg (sq_nonneg _) hM, ?_⟩
  intro x
  have hm := (reduced_nr_moments p hA hpoly).1
  have hw := (continuous_frequencies p).1
  have hf := second_integral hw hA hm 0 x
  have hb := (hpoly 2).const_mul ((p.hbar / (2 * p.m)) ^ 2)
  rw [hf.2]
  calc
    _ ≤ ∫ k, ‖secondDirectionalDerivative (ReducedPlaneWave.mode (reducedFrequency p k) k)
        (coordinateVector 0) x * A k‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ k, (p.hbar / (2 * p.m)) ^ 2 * (speedSq k ^ 2 * ‖A k‖) := by
      apply integral_mono hf.1.norm hb
      intro k
      change ‖secondDirectionalDerivative (ReducedPlaneWave.mode (reducedFrequency p k) k)
        (coordinateVector 0) x * A k‖ ≤
          (p.hbar / (2 * p.m)) ^ 2 * (speedSq k ^ 2 * ‖A k‖)
      rw [norm_mul]
      calc
        _ ≤ ((p.hbar / (2 * p.m)) ^ 2 * speedSq k ^ 2) * ‖A k‖ :=
          mul_le_mul_of_nonneg_right (ReducedPlaneWaveComparison.time_second_bound p k x)
            (norm_nonneg _)
        _ = _ := by ring
    _ = _ := by rw [integral_const_mul]; rfl

end FoliationQM.SpectralEnvelopeEstimates
