module

public import FoliationQM.ObserverFisherProduct
public import FoliationQM.ObserverFisherBilinear
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The cross term in the observed Fisher trace

In v13 Remark 5.2(a) each spatial score has the same observed weight gρ.
The trace expansion includes a signed cross term. Its magnitude is bounded
by the geometric mean of the two finite weighted score energies.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.ObserverFisherTrace

open MeasureTheory FisherNormalization ObserverFisherBilinear
open scoped BigOperators

variable {E : Type*} [MeasurableSpace E] {n : ℕ}

/-- Sum of the weighted integrals of the squared coordinate scores. -/
def squareEnergy (μ : Measure E) (w : E → ℝ) (a : Fin n → E → ℝ) : ℝ :=
  ∑ i, ∫ x, w x * a i x ^ 2 ∂μ

/-- Sum of the signed weighted integrals pairing corresponding score components. -/
def crossTerm (μ : Measure E) (w : E → ℝ) (a b : Fin n → E → ℝ) : ℝ :=
  ∑ i, ∫ x, w x * a i x * b i x ∂μ

/-- A nonnegative measure weight gives a nonnegative sum of score squares. -/
theorem squareEnergy_nonneg {μ : Measure E} {w : E → ℝ} (hw : ∀ᵐ x ∂μ, 0 ≤ w x)
    (a : Fin n → E → ℝ) : 0 ≤ squareEnergy μ w a :=
  Finset.sum_nonneg fun i _ => integral_nonneg_of_ae (hw.mono fun x hx =>
    mul_nonneg hx (sq_nonneg (a i x)))

/-- The total signed score cross term satisfies Cauchy–Schwarz, including when
either weighted energy vanishes. -/
theorem crossTerm_sq_le {μ : Measure E} {w : E → ℝ} {a b : Fin n → E → ℝ}
    (hw : AEMeasurable w μ) (hw₀ : ∀ᵐ x ∂μ, 0 ≤ w x)
    (ha : ∀ i, AEMeasurable (a i) μ) (hb : ∀ i, AEMeasurable (b i) μ)
    (hia : ∀ i, Integrable (fun x => w x * a i x ^ 2) μ)
    (hib : ∀ i, Integrable (fun x => w x * b i x ^ 2) μ) :
    crossTerm μ w a b ^ 2 ≤ squareEnergy μ w a * squareEnergy μ w b :=
  Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun i _ => integral_nonneg_of_ae (hw₀.mono fun x hx => mul_nonneg hx (sq_nonneg (a i x))))
    (fun i _ => integral_nonneg_of_ae (hw₀.mono fun x hx => mul_nonneg hx (sq_nonneg (b i x))))
    (fun i _ => weighted_cauchy_sq hw (ha i) (hb i) hw₀ (hia i) (hib i))

/-- Two finite diagonal energies control integrability of the full squared sum.
Its integral retains the signed cross term with coefficient two. -/
theorem integral_square_sum {μ : Measure E} {w : E → ℝ} {a b : Fin n → E → ℝ}
    (hw : AEMeasurable w μ) (hw₀ : ∀ᵐ x ∂μ, 0 ≤ w x)
    (ha : ∀ i, AEMeasurable (a i) μ) (hb : ∀ i, AEMeasurable (b i) μ)
    (hia : ∀ i, Integrable (fun x => w x * a i x ^ 2) μ)
    (hib : ∀ i, Integrable (fun x => w x * b i x ^ 2) μ) :
    Integrable (fun x => w x * ∑ i, (a i x + b i x) ^ 2) μ ∧
      (∫ x, w x * ∑ i, (a i x + b i x) ^ 2 ∂μ) =
        squareEnergy μ w a + 2 * crossTerm μ w a b + squareEnergy μ w b := by
  have hc i := integrable_weighted_mul hw (ha i) (hb i) hw₀ (hia i) (hib i)
  let term (i : Fin n) (x : E) :=
    w x * a i x ^ 2 + 2 * (w x * a i x * b i x) + w x * b i x ^ 2
  have ht (i : Fin n) : Integrable (term i) μ := ((hia i).add ((hc i).const_mul 2)).add (hib i)
  have he : (fun x => w x * ∑ i, (a i x + b i x) ^ 2) = fun x => ∑ i, term i x := by
    funext x
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [term]
    ring
  rw [he]
  refine ⟨integrable_finsetSum _ (fun i _ => ht i), ?_⟩
  rw [integral_finsetSum _ (fun i _ => ht i)]
  have heach (i : Fin n) : (∫ x, term i x ∂μ) = (∫ x, w x * a i x ^ 2 ∂μ) +
      2 * (∫ x, w x * a i x * b i x ∂μ) + (∫ x, w x * b i x ^ 2 ∂μ) := by
    unfold term
    have hs : Integrable (fun x => w x * a i x ^ 2 + 2 * (w x * a i x * b i x)) μ :=
      (hia i).add ((hc i).const_mul 2)
    rw [integral_add hs (hib i),
      integral_add (hia i) ((hc i).const_mul 2), integral_const_mul]
  simp only [heach, Finset.sum_add_distrib, squareEnergy, crossTerm, Finset.mul_sum]

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Finite weighted diagonal energies of the actual log-density and log-factor
scores give the full integrated Fisher trace expansion of the observed density. -/
theorem fisherTrace_expansion {μ : Measure E} {g ρ : E → ℝ} (v : Fin n → E)
    (h : ∀ᵐ x ∂μ, DifferentiableAt ℝ g x ∧ DifferentiableAt ℝ ρ x ∧ 0 < g x ∧ 0 < ρ x)
    (hw : AEMeasurable (fun x => g x * ρ x) μ)
    (ha : ∀ i, AEMeasurable (fun x => score ρ x (v i)) μ)
    (hb : ∀ i, AEMeasurable (fun x => score g x (v i)) μ)
    (hia : ∀ i, Integrable (fun x => g x * ρ x * score ρ x (v i) ^ 2) μ)
    (hib : ∀ i, Integrable (fun x => g x * ρ x * score g x (v i) ^ 2) μ) :
    let w := fun x => g x * ρ x
    let a := fun i x => score ρ x (v i)
    let b := fun i x => score g x (v i)
    Integrable (traceIntegrand (fun x => g x * ρ x) v) μ ∧
      fisherTrace (fun x => g x * ρ x) v μ =
        squareEnergy μ w a + 2 * crossTerm μ w a b + squareEnergy μ w b := by
  have hw₀ := h.mono (fun _ hx => (mul_pos hx.2.2.1 hx.2.2.2).le)
  obtain ⟨hi, he⟩ := integral_square_sum hw hw₀ ha hb hia hib
  obtain ⟨hi', he'⟩ := ObserverFisherProduct.fisherTrace_mul v μ h hi
  exact ⟨hi', he'.trans he⟩

end FoliationQM.ObserverFisherTrace
