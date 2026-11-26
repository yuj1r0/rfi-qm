module

public import FoliationQM.ObserverGaussianFisher
public import FoliationQM.ObserverFisherMatrix
public import FoliationQM.KLDomination
public import FoliationQM.TranslationFisherDefiniteness
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Quadratic form of the spatial translation Fisher matrix

In the three Cartesian translation directions in v13 Theorem 5.1, a pair of
coordinates contributes the measured product of the corresponding scores.
The matrix quadratic form is the integral of the squared directional score.
The statement uses the supplied slice measure throughout, so the precise
zero-direction criterion also applies on restricted regions.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.TranslationFisherMatrix

open LorentzCoordinates FisherNormalization ObserverGaussianFisher MeasureTheory

/-- The real translation Fisher matrix for the three laboratory axes. -/
def matrix (ρ : Spatial → ℝ) (μ : Measure Spatial) : Matrix (Fin 3) (Fin 3) ℝ :=
  fisherMatrix ρ axes μ

/-- The directional score is the coordinate-weighted sum of the three axis scores. -/
theorem score_coords (ρ : Spatial → ℝ) (x v : Spatial) :
    score ρ x v = ∑ i, v i * score ρ x (axes i) := by
  simpa only [score, axes, smul_eq_mul] using
    KLDomination.linear_apply_eq_sum (fderiv ℝ (fun y => Real.log (ρ y)) x) v

/-- Symmetry holds for every choice of the common slice measure. -/
theorem hermitian (ρ : Spatial → ℝ) (μ : Measure Spatial) : (matrix ρ μ).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simpa only [matrix, star_trivial] using ObserverFisherMatrix.entry_symm axes μ ρ j i

private theorem square_expansion (ρ : Spatial → ℝ) (v x : Spatial) :
    ρ x * (score ρ x v)^2 =
      ∑ i, ∑ j, (v i * v j) * matrixIntegrand ρ axes i j x := by
  rw [score_coords ρ x v, pow_two, Finset.sum_mul]
  simp only [Finset.mul_sum, matrixIntegrand]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

variable {ρ : Spatial → ℝ} {μ : Measure Spatial}

/-- Finite weighted coordinate squares imply integrability of each real mixed entry. -/
theorem integrable_entry (hw : AEMeasurable ρ μ) (hp : ∀ᵐ x ∂μ, 0 ≤ ρ x)
    (hs : ∀ i, AEMeasurable (fun x => score ρ x (axes i)) μ)
    (hf : ∀ i, Integrable (fun x => ρ x*(score ρ x (axes i))^2) μ) (i j : Fin 3) :
    Integrable (matrixIntegrand ρ axes i j) μ :=
  ObserverFisherBilinear.integrable_weighted_mul hw (hs i) (hs j) hp (hf i) (hf j)

/-- Every directional weighted score square is integrable under coordinatewise finite Fisher information. -/
theorem integrable_directional (hw : AEMeasurable ρ μ) (hp : ∀ᵐ x ∂μ, 0 ≤ ρ x)
    (hs : ∀ i, AEMeasurable (fun x => score ρ x (axes i)) μ)
    (hf : ∀ i, Integrable (fun x => ρ x*(score ρ x (axes i))^2) μ) (v : Spatial) :
    Integrable (fun x => ρ x*(score ρ x v)^2) μ := by
  simp_rw [square_expansion ρ v]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (integrable_entry hw hp hs hf i j).const_mul (v i * v j)

/-- The full Fisher quadratic form evaluated on v is the actual integrated directional score square. -/
theorem quadratic_eq (hw : AEMeasurable ρ μ) (hp : ∀ᵐ x ∂μ, 0 ≤ ρ x)
    (hs : ∀ i, AEMeasurable (fun x => score ρ x (axes i)) μ)
    (hf : ∀ i, Integrable (fun x => ρ x*(score ρ x (axes i))^2) μ) (v : Spatial) :
    dotProduct v ((matrix ρ μ).mulVec v) = ∫ x, ρ x*(score ρ x v)^2 ∂μ := by
  have he (i j : Fin 3) : Integrable (fun x => (v i * v j) * matrixIntegrand ρ axes i j x) μ :=
    (integrable_entry hw hp hs hf i j).const_mul _
  simp_rw [square_expansion ρ v, integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => he i j)),
    integral_finsetSum _ (fun j _ => he _ j), integral_const_mul]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, matrix, fisherMatrix]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Nonnegative density gives a positive semidefinite matrix on any measured domain. -/
theorem posSemidef (hw : AEMeasurable ρ μ) (hp : ∀ᵐ x ∂μ, 0 ≤ ρ x)
    (hs : ∀ i, AEMeasurable (fun x => score ρ x (axes i)) μ)
    (hf : ∀ i, Integrable (fun x => ρ x*(score ρ x (axes i))^2) μ) :
    (matrix ρ μ).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨hermitian .., fun v => ?_⟩
  rw [star_trivial, quadratic_eq hw hp hs hf]
  exact integral_nonneg_of_ae (hp.mono fun x hx => mul_nonneg hx (sq_nonneg _))

/-- The null directions on an arbitrary measured region are exactly those whose score
vanishes almost everywhere at the points of nonzero density in that region. -/
theorem quadratic_eq_zero_iff (hw : AEMeasurable ρ μ) (hp : ∀ᵐ x ∂μ, 0 ≤ ρ x)
    (hs : ∀ i, AEMeasurable (fun x => score ρ x (axes i)) μ)
    (hf : ∀ i, Integrable (fun x => ρ x*(score ρ x (axes i))^2) μ) (v : Spatial) :
    dotProduct v ((matrix ρ μ).mulVec v) = 0 ↔ ∀ᵐ x ∂μ, ρ x ≠ 0 → score ρ x v = 0 := by
  rw [quadratic_eq hw hp hs hf, integral_eq_zero_iff_of_nonneg_ae
    (hp.mono fun x hx => mul_nonneg hx (sq_nonneg _)) (integrable_directional hw hp hs hf v)]
  apply Filter.eventually_congr
  filter_upwards with x
  change ρ x * (score ρ x v)^2 = 0 ↔ _
  by_cases hz : ρ x = 0 <;> simp [hz]

/-- On a measured region the matrix is positive definite precisely when each
nonzero direction has nonvanishing score somewhere in the measure-theoretic
sense that its score fails to vanish almost everywhere on the nonzero density set. -/
theorem posDef_iff (hw : AEMeasurable ρ μ) (hp : ∀ᵐ x ∂μ, 0 ≤ ρ x)
    (hs : ∀ i, AEMeasurable (fun x => score ρ x (axes i)) μ)
    (hf : ∀ i, Integrable (fun x => ρ x*(score ρ x (axes i))^2) μ) :
    (matrix ρ μ).PosDef ↔ ∀ v : Spatial, v ≠ 0 → ¬(∀ᵐ x ∂μ, ρ x ≠ 0 → score ρ x v = 0) := by
  rw [Matrix.posDef_iff_dotProduct_mulVec, and_iff_right (hermitian ρ μ)]
  constructor
  · intro h v hv hz
    have hpos := h hv
    rw [star_trivial] at hpos
    exact hpos.ne' ((quadratic_eq_zero_iff hw hp hs hf v).2 hz)
  · intro h v hv
    have hnonneg := (posSemidef hw hp hs hf).dotProduct_mulVec_nonneg v
    rw [star_trivial] at hnonneg ⊢
    exact lt_of_le_of_ne hnonneg (fun hz => h v hv ((quadratic_eq_zero_iff hw hp hs hf v).1 hz.symm))

/-- For a strictly positive C¹ integrable density on all of ℝ³, finiteness of the
three coordinate Fisher squares implies positive definiteness of the translation matrix. -/
theorem posDef_volume (hr : ContDiff ℝ 1 ρ) (hp : ∀ x, 0 < ρ x) (hm : Integrable ρ)
    (hf : ∀ i, Integrable (fun x => ρ x*(score ρ x (axes i))^2)) :
    (matrix ρ volume).PosDef := by
  have hn : ∀ᵐ x ∂volume, 0 ≤ ρ x := Filter.Eventually.of_forall fun x => (hp x).le
  have hs (i : Fin 3) : AEMeasurable (fun x => score ρ x (axes i)) volume :=
    (((hr.log fun x => (hp x).ne').continuous_fderiv (by norm_num)).clm_apply
      (g := fun _ => axes i) continuous_const).aemeasurable
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨hermitian .., fun {v} hv => ?_⟩
  rw [star_trivial, quadratic_eq hm.aemeasurable hn hs hf]
  exact TranslationFisherDefiniteness.directional_pos_of_ne_zero hr hp hm
    (integrable_directional hm.aemeasurable hn hs hf v) hv

end FoliationQM.TranslationFisherMatrix
