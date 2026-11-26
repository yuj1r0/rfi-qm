module

public import FoliationQM.ObserverFisherTrace
public import FoliationQM.ObserverWeightStability

/-!
# Quantitative change of Fisher information under an observer factor

For Remark 5.2(a), the raw spatial Fisher change splits into an amplitude
error, a signed score cross term, and the energy of the factor's own score.
The bound applies on a fixed measure, including the spatial volume on an
unbounded slice whenever the indicated square energies are finite.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.ObserverFisherStability

open MeasureTheory FisherNormalization ObserverFisherTrace
open scoped BigOperators

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {μ : Measure E} {g ρ : E → ℝ} {n : ℕ}

/-- A finite homogeneous Fisher trace is the sum of its actual coordinate square integrals. -/
theorem fisherTrace_eq_squareEnergy (v : Fin n → E)
    (hi : ∀ i, Integrable (fun x => ρ x * score ρ x (v i) ^ 2) μ) :
    fisherTrace ρ v μ = squareEnergy μ ρ (fun i x => score ρ x (v i)) := by
  unfold fisherTrace traceIntegrand squareEnergy
  simp only [Finset.mul_sum]
  exact integral_finsetSum _ (fun i _ => hi i)

/-- The signed cross term in the exact expansion gives a two-sided absolute error estimate. -/
theorem expansion_error {A C B F I δ : ℝ}
    (he : F = A + 2 * C + B) (hc : C ^ 2 ≤ A * B)
    (hB : 0 ≤ B) (hA : |A - I| ≤ δ * I) :
    |F - I| ≤ δ * I + 2 * Real.sqrt (A * B) + B := by
  have hm := Real.abs_le_sqrt hc
  rw [he, show A + 2*C + B - I = (A-I + 2*C) + B by ring]
  calc
    _ ≤ |A-I + 2*C| + |B| := abs_add_le ..
    _ ≤ |A-I| + |2*C| + |B| := add_le_add_left (abs_add_le ..) _
    _ ≤ _ := by rw [abs_mul, abs_of_nonneg hB]; norm_num; linarith

/-- A uniform amplitude error δ and the finite weighted energy B of the
factor score control the entire observed trace. The intrinsic weighted
diagonal energies after changing observer are derived from the original ones. -/
theorem fisherTrace_error (v : Fin n → E) {δ : ℝ}
    (h : ∀ᵐ x ∂μ, DifferentiableAt ℝ g x ∧ DifferentiableAt ℝ ρ x ∧ 0 < g x ∧ 0 < ρ x)
    (hg : AEMeasurable g μ) (hr : AEMeasurable ρ μ)
    (hδ : ∀ᵐ x ∂μ, |g x - 1| ≤ δ)
    (ha : ∀ i, AEMeasurable (fun x => score ρ x (v i)) μ)
    (hb : ∀ i, AEMeasurable (fun x => score g x (v i)) μ)
    (hi : ∀ i, Integrable (fun x => ρ x * score ρ x (v i) ^ 2) μ)
    (hb' : ∀ i, Integrable (fun x => g x * ρ x * score g x (v i) ^ 2) μ) :
    let I := fisherTrace ρ v μ
    let B := squareEnergy μ (fun x => g x * ρ x) (fun i x => score g x (v i))
    Integrable (traceIntegrand (fun x => g x * ρ x) v) μ ∧
      |fisherTrace (fun x => g x * ρ x) v μ - I| ≤ δ * I + 2 * Real.sqrt (((1+δ)*I)*B) + B := by
  let a := fun i x => score ρ x (v i)
  let b := fun i x => score g x (v i)
  let w := fun x => g x * ρ x
  have hp : ∀ᵐ x ∂μ, 0 ≤ w x := h.mono fun _ hx => (mul_pos hx.2.2.1 hx.2.2.2).le
  have hbase := ObserverWeightStability.squareEnergy_stability (a := a) hg hδ
    (h.mono fun _ hx => hx.2.2.2.le) hi
  have hx := fisherTrace_expansion v h (hg.mul hr) ha hb hbase.1 hb'
  have hcross := crossTerm_sq_le (hg.mul hr) hp ha hb hbase.1 hb'
  have hB := squareEnergy_nonneg hp b
  dsimp only
  rw [fisherTrace_eq_squareEnergy v hi]
  refine ⟨hx.1, (expansion_error hx.2 hcross hB hbase.2.1).trans ?_⟩
  gcongr
  exact hbase.2.2

end FoliationQM.ObserverFisherStability
