module

public import FoliationQM.Conventions
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

/-!
# Continuous-time norm conservation on finite polar lattices

Source: v13 Section 2, `eq:polar_dR_dt` and its conserved-norm paragraph;
`simulate_foliation_qm_v9.py`, `polar_kahler_rhs` and
`normalized_ray_L2_error`. The finite graph carries explicit node mass weights
and symmetric real couplings. A closed graph has no external edges, so every
oriented edge has its reverse and the total current cancels.

These are exact real semidiscrete statements, including a derivative theorem
for actual time-dependent amplitudes satisfying the amplitude ODE. They are
not claims about RK4, floating-point arithmetic, energy conservation, or the
full regularized polar/Schrödinger correspondence. No clock ODE is assumed:
the amplitude norm calculation works for arbitrary phases at each time.
-/

namespace FoliationQM.LatticeConservation

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- Total oriented flux on a finite closed graph is zero when each reverse
edge carries the negative current. -/
theorem sum_antisymmetric_current_eq_zero (J : ι → ι → ℝ)
    (hJ : ∀ i j, J j i = -J i j) : (∑ i, ∑ j, J i j) = 0 := by
  have h : (∑ i, ∑ j, J i j) = -(∑ i, ∑ j, J i j) := by
    calc
      (∑ i, ∑ j, J i j) = ∑ j, ∑ i, J i j := Finset.sum_comm
      _ = ∑ j, ∑ i, -J j i := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro i _
        exact hJ j i
      _ = -(∑ j, ∑ i, J j i) := by simp only [Finset.sum_neg_distrib]
  linarith

/-- Oriented polar current, with the factor two from differentiating `R²`.
The symmetric coupling contains all spatial and physical scale factors. -/
noncomputable def edgeCurrent (κ : ι → ι → ℝ) (R φ : ι → ℝ) (i j : ι) : ℝ :=
  2 * κ i j * R i * R j * Real.sin (φ j - φ i)

omit [Fintype ι] in
/-- Polar currents are antisymmetric for arbitrary signed amplitudes. -/
theorem edgeCurrent_antisymmetric (κ : ι → ι → ℝ) (R φ : ι → ℝ)
    (hκ : ∀ i j, κ j i = κ i j) (i j : ι) :
    edgeCurrent κ R φ j i = -edgeCurrent κ R φ i j := by
  rw [edgeCurrent, edgeCurrent, hκ i j, show φ i - φ j = -(φ j - φ i) by ring,
    Real.sin_neg]
  ring

/-- Closed finite-graph polar currents cancel exactly. -/
theorem sum_edgeCurrent_eq_zero (κ : ι → ι → ℝ) (R φ : ι → ℝ)
    (hκ : ∀ i j, κ j i = κ i j) :
    (∑ i, ∑ j, edgeCurrent κ R φ i j) = 0 :=
  sum_antisymmetric_current_eq_zero _ (edgeCurrent_antisymmetric κ R φ hκ)

/-- Amplitude ODE with explicit node mass weights. To conserve a chosen
weighted norm, the inverse weights occur in the dynamics as written here. -/
noncomputable def amplitudeRHS (μ : ι → ℝ) (κ : ι → ι → ℝ)
    (R φ : ι → ℝ) (i : ι) : ℝ :=
  -(∑ j, κ i j * R j * Real.sin (φ j - φ i)) / μ i

/-- Local weighted continuity equation for the actual amplitude RHS. -/
theorem weighted_node_balance (μ : ι → ℝ) (κ : ι → ι → ℝ)
    (R φ : ι → ℝ) (i : ι) (hμ : μ i ≠ 0) :
    μ i * (2 * R i * amplitudeRHS μ κ R φ i) =
      -(∑ j, edgeCurrent κ R φ i j) := by
  unfold amplitudeRHS edgeCurrent
  have : (∑ j, 2 * κ i j * R i * R j * Real.sin (φ j - φ i)) =
      2 * R i * ∑ j, κ i j * R j * Real.sin (φ j - φ i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [this]
  field_simp [hμ]

/-- Exact weighted semidiscrete mass law. Positivity gives a physical norm;
the cancellation itself needs only nonzero mass weights. -/
theorem weighted_mass_rate_eq_zero (μ : ι → ℝ) (κ : ι → ι → ℝ)
    (R φ : ι → ℝ) (hμ : ∀ i, μ i ≠ 0) (hκ : ∀ i j, κ j i = κ i j) :
    (∑ i, μ i * (2 * R i * amplitudeRHS μ κ R φ i)) = 0 := by
  simp_rw [weighted_node_balance μ κ R φ _ (hμ _)]
  rw [Finset.sum_neg_distrib, sum_edgeCurrent_eq_zero κ R φ hκ, neg_zero]

/-- Weighted squared amplitude norm; this is the mass functional whose
derivative is proved below. -/
noncomputable def weightedMass (μ R : ι → ℝ) : ℝ := ∑ i, μ i * R i ^ 2

/-- Actual differentiation of the finite weighted squared norm. -/
theorem hasDerivAt_weightedMass (μ : ι → ℝ) (R : ℝ → ι → ℝ)
    (Rdot : ι → ℝ) (t : ℝ)
    (hR : ∀ i, HasDerivAt (fun s => R s i) (Rdot i) t) :
    HasDerivAt (fun s => weightedMass μ (R s))
      (∑ i, μ i * (2 * R t i * Rdot i)) t := by
  unfold weightedMass
  apply HasDerivAt.fun_sum
  intro i _
  convert ((hR i).pow 2).const_mul (μ i) using 1
  simp

/-- The derivative of the weighted mass of an actual solution is zero.
This assumes the amplitude equation at `t`, not the desired norm law. -/
theorem hasDerivAt_weightedMass_zero_of_amplitudeODE
    (μ : ι → ℝ) (κ : ι → ι → ℝ) (R φ : ℝ → ι → ℝ) (t : ℝ)
    (hμ : ∀ i, μ i ≠ 0) (hκ : ∀ i j, κ j i = κ i j)
    (hR : ∀ i, HasDerivAt (fun s => R s i)
      (amplitudeRHS μ κ (R t) (φ t) i) t) :
    HasDerivAt (fun s => weightedMass μ (R s)) 0 t := by
  convert hasDerivAt_weightedMass μ R _ t hR using 1
  exact (weighted_mass_rate_eq_zero μ κ (R t) (φ t) hμ hκ).symm

/-- Replicate the final endpoint, exactly as `R_plus[-1] = R[-1]` and
`tau_plus[-1] = tau[-1]` in the source implementation. -/
def nextNode {n : ℕ} (i : Fin n) : Fin n :=
  if h : i.val + 1 < n then ⟨i.val + 1, h⟩ else i

/-- Replicate the initial endpoint, exactly as `R_minus[0] = R[0]` and
`tau_minus[0] = tau[0]` in the source implementation. -/
def prevNode {n : ℕ} (i : Fin n) : Fin n :=
  ⟨i.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩

/-- The symmetric nearest-neighbor path coupling. There is no edge between
the two endpoints and hence no periodic wraparound. -/
noncomputable def pathCoupling {n : ℕ} (a : ℝ) (i j : Fin n) : ℝ :=
  (if i.val + 1 = j.val then a else 0) +
    (if j.val + 1 = i.val then a else 0)

/-- The path coupling is symmetric, including the boundary rows. -/
theorem pathCoupling_symmetric {n : ℕ} (a : ℝ) (i j : Fin n) :
    pathCoupling a j i = pathCoupling a i j := by
  unfold pathCoupling
  exact add_comm _ _

private theorem sum_forward {n : ℕ} (a : ℝ) (f : Fin n → ℝ) (i : Fin n)
    (hf : f i = 0) :
    (∑ j, (if i.val + 1 = j.val then a else 0) * f j) = a * f (nextNode i) := by
  classical
  unfold nextNode
  split_ifs with h
  · let k : Fin n := ⟨i.val + 1, h⟩
    rw [Finset.sum_eq_single k]
    · simp [k]
    · intro j _ hj
      have hj' : i.val + 1 ≠ j.val := by
        intro heq
        apply hj
        exact Fin.ext heq.symm
      simp [hj']
    · simp
  · have hnone : ∀ j : Fin n, i.val + 1 ≠ j.val := by
      intro j heq
      exact h (heq ▸ j.isLt)
    simp [hnone, hf]

private theorem sum_backward {n : ℕ} (a : ℝ) (f : Fin n → ℝ) (i : Fin n)
    (hf : f i = 0) :
    (∑ j, (if j.val + 1 = i.val then a else 0) * f j) = a * f (prevNode i) := by
  classical
  by_cases hi : i.val = 0
  · have hp : prevNode i = i := by apply Fin.ext; simp [prevNode, hi]
    simp [hi, hp, hf]
  · rw [Finset.sum_eq_single (prevNode i)]
    · have hp : (prevNode i).val + 1 = i.val := by simp [prevNode]; omega
      simp [hp]
    · intro j _ hj
      have hj' : j.val + 1 ≠ i.val := by
        intro heq
        apply hj
        apply Fin.ext
        simp only [prevNode]
        omega
      simp [hj']
    · simp

/-- The source's clamped-endpoint amplitude equation, with phase
`φ = (c / ellC) * delta_tau`, exactly as in the Python RHS. This definition
has no `epsilon_reg` because the amplitude equation contains no such term. -/
noncomputable def sourceAmplitudeRHS {n : ℕ} (ellC c dx : ℝ)
    (R φ : Fin n → ℝ) (i : Fin n) : ℝ :=
  -(ellC * c / (2 * dx ^ 2)) *
    (R (nextNode i) * Real.sin (φ (nextNode i) - φ i) -
      R (prevNode i) * Real.sin (φ i - φ (prevNode i)))

/-- Explicit bridge to the source's lag-clock differences. Section 2 and
the Python code use the positive phase convention `(c / ellC) * delta_tau`;
this theorem does not silently identify that lag clock with a clock carrying
the opposite phase convention elsewhere in the manuscript. -/
theorem sourceAmplitudeRHS_clock {n : ℕ} (ellC c dx : ℝ)
    (R τ : Fin n → ℝ) (i : Fin n) :
    sourceAmplitudeRHS ellC c dx R (fun j => (c / ellC) * τ j) i =
      -(ellC * c / (2 * dx ^ 2)) *
        (R (nextNode i) * Real.sin ((c / ellC) * (τ (nextNode i) - τ i)) -
          R (prevNode i) * Real.sin ((c / ellC) * (τ i - τ (prevNode i)))) := by
  simp only [sourceAmplitudeRHS, mul_sub]

/-- Boundary-replicated source RHS is exactly the closed-path graph RHS.
Endpoint self-terms vanish by `sin 0 = 0`; no boundary flux is dropped by
an extra unproved assumption. -/
theorem sourceAmplitudeRHS_eq_graph {n : ℕ} (ellC c dx : ℝ)
    (R φ : Fin n → ℝ) (i : Fin n) :
    sourceAmplitudeRHS ellC c dx R φ i =
      amplitudeRHS (fun _ => 1) (pathCoupling (ellC * c / (2 * dx ^ 2))) R φ i := by
  unfold amplitudeRHS pathCoupling
  simp only [div_one, add_mul, Finset.sum_add_distrib]
  have hf : R i * Real.sin (φ i - φ i) = 0 := by simp
  simp_rw [mul_assoc]
  rw [sum_forward _ (fun j => R j * Real.sin (φ j - φ i)) i hf,
    sum_backward _ (fun j => R j * Real.sin (φ j - φ i)) i hf]
  unfold sourceAmplitudeRHS
  rw [show φ (prevNode i) - φ i = -(φ i - φ (prevNode i)) by ring, Real.sin_neg]
  ring

/-- Exact semidiscrete norm-rate law for the source's replicated-endpoint
Neumann path, including arbitrary signed and zero amplitudes. -/
theorem source_mass_rate_eq_zero {n : ℕ} (ellC c dx : ℝ) (R φ : Fin n → ℝ) :
    (∑ i, 2 * R i * sourceAmplitudeRHS ellC c dx R φ i) = 0 := by
  simp_rw [sourceAmplitudeRHS_eq_graph]
  simpa using weighted_mass_rate_eq_zero (fun _ : Fin n => 1)
    (pathCoupling (ellC * c / (2 * dx ^ 2))) R φ (by intro i; norm_num)
    (pathCoupling_symmetric _)

/-- The source raw lattice mass uses rectangular weights `dx`, including
the endpoints. The trapezoidal ray-distance normalization is a different
functional and is not asserted to be conserved here. -/
noncomputable def sourceMass {n : ℕ} (dx : ℝ) (R : Fin n → ℝ) : ℝ :=
  dx * ∑ i, R i ^ 2

/-- Exact derivative-zero norm theorem for a time-dependent amplitude
solution of the source boundary-replicated ODE, with its actual `dx` weights. -/
theorem hasDerivAt_sourceMass_zero {n : ℕ} (ellC c dx : ℝ)
    (R φ : ℝ → Fin n → ℝ) (t : ℝ)
    (hR : ∀ i, HasDerivAt (fun s => R s i)
      (sourceAmplitudeRHS ellC c dx (R t) (φ t) i) t) :
    HasDerivAt (fun s => sourceMass dx (R s)) 0 t := by
  have h := hasDerivAt_weightedMass (fun _ : Fin n => 1) R _ t hR
  simp only [one_mul, source_mass_rate_eq_zero] at h
  simpa [sourceMass, weightedMass] using h.const_mul dx

/-- Actual conservation between any two real times for a globally defined
amplitude solution, with positive physical grid spacing. The all-time ODE
hypothesis includes actual derivatives at every node and time; no existence
or global extension theorem for this ODE is claimed. -/
theorem sourceMass_eq_of_amplitudeODE {n : ℕ} (ellC c dx : ℝ) (_hdx : 0 < dx)
    (R φ : ℝ → Fin n → ℝ)
    (hR : ∀ t i, HasDerivAt (fun s => R s i)
      (sourceAmplitudeRHS ellC c dx (R t) (φ t) i) t) (t₀ t₁ : ℝ) :
    sourceMass dx (R t₁) = sourceMass dx (R t₀) := by
  have hmass : ∀ t, HasDerivAt (fun s => sourceMass dx (R s)) 0 t :=
    fun t => hasDerivAt_sourceMass_zero ellC c dx R φ t (hR t)
  exact is_const_of_deriv_eq_zero (fun t => (hmass t).differentiableAt)
    (fun t => (hmass t).deriv) t₁ t₀

end FoliationQM.LatticeConservation
