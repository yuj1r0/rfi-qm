module

public import FoliationQM.HilbertGeneratorCancellation
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Uniqueness of strong Schrödinger evolution on a time-dependent domain

For the factorization step in v13 `thm:entanglement_nosignaling`, two
candidate wave evolutions agree when they obey the same symmetric
Hamiltonian and coincide at one time. Differentiating their squared
distance proves uniqueness even for unbounded operators with
time-dependent linear domains. Strong differentiability within a closed
time interval suffices at its endpoints.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.StrongSchrodingerUniqueness

open HilbertGeneratorCancellation Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A trajectory in the instantaneous operator domain with the stated strong time derivative. -/
structure Strong (hbar : ℝ) (H : ℝ → E →ₗ.[ℂ] E) (u : ℝ → E) : Prop where
  mem : ∀ t, u t ∈ (H t).domain
  derivative : ∀ t, HasDerivAt u (generator hbar (H t) ⟨u t, mem t⟩) t

/-- The interval version requires only differentiation within the given set of times. -/
structure StrongOn (hbar : ℝ) (H : ℝ → E →ₗ.[ℂ] E) (u : ℝ → E) (s : Set ℝ) : Prop where
  mem : ∀ t ∈ s, u t ∈ (H t).domain
  derivative : ∀ t (ht : t ∈ s), HasDerivWithinAt u (generator hbar (H t) ⟨u t, mem t ht⟩) s t

variable {hbar : ℝ} {H : ℝ → E →ₗ.[ℂ] E} {u v : ℝ → E} {s : Set ℝ}

/-- A global strong solution restricts to a solution on each time set. -/
theorem Strong.onSet (hu : Strong hbar H u) (s : Set ℝ) : StrongOn hbar H u s :=
  ⟨fun t _ => hu.mem t, fun t _ => (hu.derivative t).hasDerivWithinAt⟩

/-- The difference of two strong solutions remains in each linear domain and obeys the same equation. -/
theorem StrongOn.sub (hu : StrongOn hbar H u s) (hv : StrongOn hbar H v s) :
    StrongOn hbar H (fun t => u t - v t) s where
  mem t ht := (H t).domain.sub_mem (hu.mem t ht) (hv.mem t ht)
  derivative t ht := by
    apply ((hu.derivative t ht).sub (hv.derivative t ht)).congr_deriv
    change generator hbar (H t) ⟨u t, hu.mem t ht⟩ - generator hbar (H t) ⟨v t, hv.mem t ht⟩ =
      generator hbar (H t) (⟨u t, hu.mem t ht⟩ - ⟨v t, hv.mem t ht⟩)
    rw [generator, generator, generator, (H t).map_sub, smul_sub]

/-- The full complex overlap is constant between any two times of a convex interval. -/
theorem inner_eq_on (hs : Convex ℝ s) (hsym : ∀ t ∈ s, (H t).IsFormalAdjoint (H t))
    (hu : StrongOn hbar H u s) (hv : StrongOn hbar H v s) {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    inner ℂ (u b) (v b) = inner ℂ (u a) (v a) := by
  have hd (t : ℝ) (ht : t ∈ s) : HasDerivWithinAt (fun z => inner ℂ (u z) (v z)) 0 s t :=
    ((hu.derivative t ht).inner ℂ (hv.derivative t ht)).congr_deriv
      (remote_gram_zero hbar (H t) (hsym t ht) ⟨u t, hu.mem t ht⟩ ⟨v t, hv.mem t ht⟩)
  have he := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (C := 0) hd (fun _ _ => by simp) hs ha hb
  simpa [sub_eq_zero] using he

/-- The squared Hilbert distance of two strong solutions is conserved on a convex interval. -/
theorem norm_sub_sq_eq_on (hs : Convex ℝ s) (hsym : ∀ t ∈ s, (H t).IsFormalAdjoint (H t))
    (hu : StrongOn hbar H u s) (hv : StrongOn hbar H v s) {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    ‖u b - v b‖ ^ 2 = ‖u a - v a‖ ^ 2 := by
  have hw := hu.sub hv
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) _).trans <|
    (congrArg Complex.re (inner_eq_on hs hsym hw hw ha hb)).trans
      (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm

/-- Global strong solutions with the same value at an arbitrary initial time agree for all times. -/
theorem eq_of_strong (hsym : ∀ t, (H t).IsFormalAdjoint (H t))
    (hu : Strong hbar H u) (hv : Strong hbar H v) {s : ℝ} (h₀ : u s = v s) : u = v := by
  funext t
  have he := norm_sub_sq_eq_on convex_univ (fun z _ => hsym z) (hu.onSet univ) (hv.onSet univ)
    (mem_univ s) (mem_univ t)
  simpa [h₀, sub_eq_zero] using he

/-- On a closed time interval it suffices to prescribe the value at its left endpoint. -/
theorem eqOn_Icc_of_strong {a b : ℝ} (hsym : ∀ t ∈ Icc a b, (H t).IsFormalAdjoint (H t))
    (hu : StrongOn hbar H u (Icc a b)) (hv : StrongOn hbar H v (Icc a b)) (h₀ : u a = v a) :
    EqOn u v (Icc a b) := by
  intro t ht
  have he := norm_sub_sq_eq_on (convex_Icc a b) hsym hu hv (left_mem_Icc.mpr (ht.1.trans ht.2)) ht
  simpa [h₀, sub_eq_zero] using he

/-- In a Hilbert space genuine self-adjointness of each time-dependent partial operator
implies uniqueness of its global strong evolution trajectories. -/
theorem eq_of_selfAdjoint [CompleteSpace E] (hH : ∀ t, IsSelfAdjoint (H t))
    (hu : Strong hbar H u) (hv : Strong hbar H v) {s : ℝ} (h₀ : u s = v s) : u = v :=
  eq_of_strong (fun t => formalAdjoint_of_selfAdjoint (hH t)) hu hv h₀

end FoliationQM.StrongSchrodingerUniqueness
