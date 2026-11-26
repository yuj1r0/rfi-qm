module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic

/-!
# Fisher information on a finite statistical model

For the information-geometric distinction in v13 Remark 5.2(b), a
perturbation of a positive probability vector has Fisher square ∑ uᵢ²/pᵢ.
A stochastic map preserves total mass and sends tangent vectors to tangent
vectors. Its contraction inequality becomes equality if a stochastic map
recovers both the base distribution and its perturbation.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.StatisticalFisherMetric

open scoped BigOperators

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The Fisher square of an infinitesimal change of weights at a positive law. -/
def square (p u : ι → ℝ) : ℝ := ∑ i, u i ^ 2 / p i

/-- The image of signed masses under a transition matrix, with the output
index first and the input index second. -/
def push (K : κ → ι → ℝ) (u : ι → ℝ) (j : κ) : ℝ := ∑ i, K j i * u i

/-- A column-stochastic matrix preserves mass, including zero total mass
for directions tangent to the probability simplex. -/
theorem mass_push (K : κ → ι → ℝ) (hk : ∀ i, ∑ j, K j i = 1) (u : ι → ℝ) :
    ∑ j, push K u j = ∑ i, u i := by
  unfold push
  calc
    ∑ j, ∑ i, K j i * u i = ∑ i, ∑ j, K j i * u i := Finset.sum_comm
    _ = _ := by simp only [← Finset.sum_mul, hk, one_mul]

/-- At a positive base distribution the Fisher square vanishes exactly for
the zero perturbation, in particular on the zero-sum tangent space. -/
theorem square_eq_zero_iff (p u : ι → ℝ) (hp : ∀ i, 0 < p i) :
    square p u = 0 ↔ u = 0 := by
  constructor
  · intro h
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ Finset.univ) =>
      div_nonneg (sq_nonneg (u i)) (hp i).le)).mp h
    funext i
    have he := (div_eq_zero_iff.mp (hz i (Finset.mem_univ _))).resolve_right (hp i).ne'
    simpa using he
  · rintro rfl
    simp [square]

/-- Every nonzero statistical tangent at a positive probability vector has
strictly positive Fisher square. -/
theorem square_pos (p u : ι → ℝ) (hp : ∀ i, 0 < p i) (hu : u ≠ 0) : 0 < square p u :=
  lt_of_le_of_ne (Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (hp i).le)
    (fun h => hu ((square_eq_zero_iff p u hp).mp h.symm))

/-- A stochastic channel contracts Fisher information wherever its input and
output base weights are positive. The bound applies also to signed tangents. -/
theorem square_push_le (K : κ → ι → ℝ) (hK : ∀ j i, 0 ≤ K j i) (hk : ∀ i, ∑ j, K j i = 1)
    (p u : ι → ℝ) (hp : ∀ i, 0 < p i) (hout : ∀ j, 0 < push K p j) :
    square (push K p) (push K u) ≤ square p u := by
  have hrow (j : κ) : push K u j ^ 2 / push K p j ≤ ∑ i, K j i * (u i ^ 2 / p i) := by
    apply (div_le_iff₀ (hout j)).2
    rw [mul_comm]
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (fun i _ => mul_nonneg (hK j i) (hp i).le)
      (fun i _ => mul_nonneg (hK j i) (div_nonneg (sq_nonneg _) (hp i).le))
    intro i _
    apply le_of_eq
    field_simp [(hp i).ne']
  exact (Finset.sum_le_sum fun j _ => hrow j).trans_eq (mass_push K hk (fun i => u i ^ 2 / p i))

/-- If a stochastic recovery channel recovers both the base law and its tangent,
information is preserved exactly by the forward channel. -/
theorem square_push_eq_of_recovery (K : κ → ι → ℝ) (L : ι → κ → ℝ)
    (hK : ∀ j i, 0 ≤ K j i) (hk : ∀ i, ∑ j, K j i = 1)
    (hL : ∀ i j, 0 ≤ L i j) (hl : ∀ j, ∑ i, L i j = 1)
    (p u : ι → ℝ) (hp : ∀ i, 0 < p i) (hout : ∀ j, 0 < push K p j)
    (hrp : push L (push K p) = p) (hru : push L (push K u) = u) :
    square (push K p) (push K u) = square p u := by
  apply le_antisymm (square_push_le K hK hk p u hp hout)
  have h := square_push_le L hL hl (push K p) (push K u) hout (by rwa [hrp])
  rwa [hrp, hru] at h

end FoliationQM.StatisticalFisherMetric
