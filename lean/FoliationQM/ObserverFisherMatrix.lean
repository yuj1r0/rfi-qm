module

public import FoliationQM.ObserverFisherBilinear
public import FoliationQM.ObserverFisherProduct

/-!
# Fisher matrix of the observer-weighted density

V13 Remark 5.2 and supplement lines 298–310 use the spatial score of the
product density gρ. Each matrix entry contains the two diagonal score
tensors and two signed mixed tensors, all integrated against the observed
weight. Finiteness of the component squares suffices for all four terms.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.ObserverFisherMatrix

open MeasureTheory FisherNormalization ObserverFisherBilinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ} {g ρ : E → ℝ}

/-- The matrix integrand of the product density splits into four terms in
any pair of supplied directions, including both orders of the mixed scores. -/
theorem matrixIntegrand_mul (v : Fin n → E) (i j : Fin n) {x : E}
    (hg : DifferentiableAt ℝ g x) (hr : DifferentiableAt ℝ ρ x)
    (hgp : 0 < g x) (hrp : 0 < ρ x) :
    matrixIntegrand (fun y => g y * ρ y) v i j x =
      g x * ρ x * score ρ x (v i) * score ρ x (v j) +
      g x * ρ x * score ρ x (v i) * score g x (v j) +
      g x * ρ x * score g x (v i) * score ρ x (v j) +
      g x * ρ x * score g x (v i) * score g x (v j) := by
  simp only [matrixIntegrand, ObserverFisherProduct.score_mul hg hr hgp hrp]
  ring

variable [MeasurableSpace E] (v : Fin n → E) (μ : Measure E)
variable (h : ∀ᵐ x ∂μ, DifferentiableAt ℝ g x ∧ DifferentiableAt ℝ ρ x ∧
  0 < g x ∧ 0 < ρ x)
variable (hw : AEMeasurable (fun x => g x * ρ x) μ)
variable (hrm : ∀ i, AEMeasurable (fun x => score ρ x (v i)) μ)
variable (hgm : ∀ i, AEMeasurable (fun x => score g x (v i)) μ)
variable (hrr : ∀ i, Integrable (fun x => g x * ρ x * (score ρ x (v i)) ^ 2) μ)
variable (hgg : ∀ i, Integrable (fun x => g x * ρ x * (score g x (v i)) ^ 2) μ)

include h hw hrm hgm hrr hgg in
/-- The actual observed Fisher matrix is finite entrywise and equals the
four integrated score products. Integrability of each signed product
follows from the two corresponding weighted square integrals. -/
theorem entry_expansion (i j : Fin n) :
    Integrable (matrixIntegrand (fun x => g x * ρ x) v i j) μ ∧
    fisherMatrix (fun x => g x * ρ x) v μ i j =
      (∫ x, g x * ρ x * score ρ x (v i) * score ρ x (v j) ∂μ) +
      (∫ x, g x * ρ x * score ρ x (v i) * score g x (v j) ∂μ) +
      (∫ x, g x * ρ x * score g x (v i) * score ρ x (v j) ∂μ) +
      (∫ x, g x * ρ x * score g x (v i) * score g x (v j) ∂μ) := by
  have hp : ∀ᵐ x ∂μ, 0 ≤ g x * ρ x :=
    h.mono fun _ hx => (mul_pos hx.2.2.1 hx.2.2.2).le
  have h₁ := integrable_weighted_mul hw (hrm i) (hrm j) hp (hrr i) (hrr j)
  have h₂ := integrable_weighted_mul hw (hrm i) (hgm j) hp (hrr i) (hgg j)
  have h₃ := integrable_weighted_mul hw (hgm i) (hrm j) hp (hgg i) (hrr j)
  have h₄ := integrable_weighted_mul hw (hgm i) (hgm j) hp (hgg i) (hgg j)
  have he : matrixIntegrand (fun y => g y * ρ y) v i j =ᵐ[μ] fun x =>
      g x * ρ x * score ρ x (v i) * score ρ x (v j) +
      g x * ρ x * score ρ x (v i) * score g x (v j) +
      g x * ρ x * score g x (v i) * score ρ x (v j) +
      g x * ρ x * score g x (v i) * score g x (v j) := by
    filter_upwards [h] with x hx
    exact matrixIntegrand_mul v i j hx.1 hx.2.1 hx.2.2.1 hx.2.2.2
  refine ⟨(((h₁.add h₂).add h₃).add h₄).congr he.symm, ?_⟩
  have h₁₂₃₄ := integral_add ((h₁.add h₂).add h₃) h₄
  have h₁₂₃ := integral_add (h₁.add h₂) h₃
  simp only [Pi.add_apply] at h₁₂₃₄ h₁₂₃
  rw [fisherMatrix, integral_congr_ae he, h₁₂₃₄, h₁₂₃, integral_add h₁ h₂]

include h hw hrm hgm hrr hgg in
/-- On the diagonal the two mixed entries coincide, producing twice the
signed cross integral between the intrinsic and observer-factor scores. -/
theorem diagonal_expansion (i : Fin n) :
    Integrable (matrixIntegrand (fun x => g x * ρ x) v i i) μ ∧
    fisherMatrix (fun x => g x * ρ x) v μ i i =
      (∫ x, g x * ρ x * (score ρ x (v i)) ^ 2 ∂μ) +
      2 * (∫ x, g x * ρ x * score ρ x (v i) * score g x (v i) ∂μ) +
      (∫ x, g x * ρ x * (score g x (v i)) ^ 2 ∂μ) := by
  obtain ⟨hi, he⟩ := entry_expansion v μ h hw hrm hgm hrr hgg i i
  have hm : (∫ x, g x * ρ x * score g x (v i) * score ρ x (v i) ∂μ) =
      ∫ x, g x * ρ x * score ρ x (v i) * score g x (v i) ∂μ := by
    apply integral_congr_ae
    filter_upwards with x
    ring
  refine ⟨hi, ?_⟩
  rw [he, hm]
  simp only [pow_two, ← mul_assoc]
  ring

/-- Interchanging the two supplied directions leaves the observed Fisher
matrix entry unchanged for any density. -/
theorem entry_symm (density : E → ℝ) (i j : Fin n) :
    fisherMatrix density v μ i j = fisherMatrix density v μ j i := by
  apply integral_congr_ae
  filter_upwards with x
  unfold matrixIntegrand
  ring

end FoliationQM.ObserverFisherMatrix
