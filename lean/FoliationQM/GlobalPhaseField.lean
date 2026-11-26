module

public import FoliationQM.Conventions
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Global phase fields and their local real lifts

Source: v13 `rem:topological_hbar_lock`. The phase is an actual circle-valued
map on an arbitrary space. A real action lift is assumed only on the set where
it is used; no global real lift is required. Continuity of a supplied phase
is an input. These results do not reconstruct a phase from a closed one-form
or extend a winding phase through a node.
-/
@[expose] public section

namespace FoliationQM.GlobalPhaseField

variable {X : Type*}

/-- The global auxiliary field with the physical circle phase raised to an
integer power. This definition does not choose a real phase lift. -/
noncomputable def field (ρ : X → ℝ) (q : X → Circle) (k : ℕ) (x : X) : ℂ :=
  (Real.sqrt (ρ x) : ℂ) * (q x ^ k : Circle)

/-- The global field retains its Born density under every phase power. -/
theorem field_normSq (ρ : X → ℝ) (q : X → Circle) (k : ℕ) (x : X)
    (hρ : 0 ≤ ρ x) : Complex.normSq (field ρ q k x) = ρ x := by
  rw [field, Complex.normSq_mul, Circle.normSq_coe, mul_one]
  simpa only [Complex.normSq_ofReal, ← pow_two] using Real.sq_sqrt hρ

/-- A continuous supplied circle phase and density give a continuous global
field. No real phase lift is needed for this assertion. -/
theorem continuous_field [TopologicalSpace X] (ρ : X → ℝ) (q : X → Circle)
    (k : ℕ) (hρ : Continuous ρ) (hq : Continuous q) : Continuous (field ρ q k) := by
  unfold field
  exact (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp hρ)).mul
    (continuous_subtype_val.comp (hq.pow k))

/-- On any set with a supplied local real lift, the global field is exactly
the amplitude times the phase of the integer-multiplied lift. -/
theorem field_eq_local_phase (ρ : X → ℝ) (q : X → Circle) (Φ : X → ℝ)
    (k : ℕ) {U : Set X} (hq : ∀ x ∈ U, q x = Circle.exp (Φ x)) :
    ∀ x ∈ U, field ρ q k x = (Real.sqrt (ρ x) : ℂ) * phase (k * Φ x) := by
  intro x hx
  rw [field, hq x hx, ← Circle.exp_natCast_mul]
  rfl

/-- When the positive clock ratio is an integer, a local physical action lift
represents the global powered phase using the effective clock quantum. -/
theorem field_eq_effective_phase (ρ : X → ℝ) (q : X → Circle) (S : X → ℝ)
    (hbar heff : ℝ) (hh : 0 < hbar) (he : 0 < heff) (k : ℕ) (hratio : hbar / heff = k)
    {U : Set X} (hq : ∀ x ∈ U, q x = Circle.exp (S x / hbar)) :
    ∀ x ∈ U, field ρ q k x = (Real.sqrt (ρ x) : ℂ) * phase (S x / heff) := by
  intro x hx
  rw [field_eq_local_phase ρ q (fun x => S x / hbar) k hq x hx]
  congr 2
  rw [← hratio]
  field_simp [ne_of_gt hh, ne_of_gt he]

/-- Distinct choices of a local action lift of the same circle phase give the
same effective complex field at integer clock ratio. -/
theorem effective_phase_independent_of_lift (ρ : X → ℝ) (q : X → Circle)
    (S T : X → ℝ) (hbar heff : ℝ) (hh : 0 < hbar) (he : 0 < heff) (k : ℕ)
    (hratio : hbar / heff = k) {U : Set X}
    (hS : ∀ x ∈ U, q x = Circle.exp (S x / hbar))
    (hT : ∀ x ∈ U, q x = Circle.exp (T x / hbar)) :
    ∀ x ∈ U, (Real.sqrt (ρ x) : ℂ) * phase (S x / heff) =
      (Real.sqrt (ρ x) : ℂ) * phase (T x / heff) := by
  intro x hx
  exact (field_eq_effective_phase ρ q S hbar heff hh he k hratio hS x hx).symm.trans
    (field_eq_effective_phase ρ q T hbar heff hh he k hratio hT x hx)

end FoliationQM.GlobalPhaseField
