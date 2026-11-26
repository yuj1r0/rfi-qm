module
public import Mathlib.Algebra.Group.Commute.Basic
public import Mathlib.Tactic.Group

/-!
# Ordered transition defects and central corrections

Source scope: the transition-lifting component of the actual Spin/Lorentz
interpretation in v13 `prop:takabayasi`. These group identities isolate
the algebra needed for genuine chart i to chart j transitions. No cocycle
law is assumed for the proposed lifts. The quadruple law requires only
the displayed defect to commute with the indicated transition; the
correction formula requires only its displayed pairwise commutation.
The actual Clifford application proves those conditions from its central
physical sign kernel on the appropriate overlaps.
-/

@[expose] public section
namespace FoliationQM.CentralTransitionDefect

variable {G ι : Type*} [Group G]

/-- The failure of proposed chart i to j to k group transitions to satisfy their ordered cocycle law. -/
def defect (t : ι → ι → G) (i j k : ι) : G := t j k * t i j * (t i k)⁻¹

/-- Multiplying a transition defect by the direct transition recovers the ordered two-step transition. -/
theorem defect_mul_transition (t : ι → ι → G) (i j k : ι) :
    defect t i j k * t i k = t j k * t i j := by
  simp only [defect, inv_mul_cancel_right]

/-- A displayed transition defect vanishes exactly when the corresponding ordered cocycle equation holds. -/
theorem defect_eq_one_iff (t : ι → ι → G) (i j k : ι) :
    defect t i j k = 1 ↔ t j k * t i j = t i k := by
  exact mul_inv_eq_one

/-- Associativity gives the conjugated quadruple identity for arbitrary proposed group transitions, with no cocycle premise. -/
theorem defect_quadruple_conjugation (t : ι → ι → G) (i j k l : ι) :
    defect t j k l * defect t i j l =
      t k l * defect t i j k * (t k l)⁻¹ * defect t i k l := by
  simp only [defect]
  group

/-- A central displayed defect satisfies the actual ordered two-cocycle equation on four indices. -/
theorem defect_quadruple (t : ι → ι → G) (i j k l : ι)
    (h : Commute (defect t i j k) (t k l)) :
    defect t j k l * defect t i j l = defect t i j k * defect t i k l := by
  rw [defect_quadruple_conjugation, ← h.eq, mul_inv_cancel_right]

/-- Pair coefficients act on proposed transitions by left multiplication in the original chart-change order. -/
def corrected (t b : ι → ι → G) (i j : ι) : G := b i j * t i j

/-- A commuting pair coefficient changes the literal triple defect by the explicit central-cochain expression. -/
theorem defect_corrected (t b : ι → ι → G) (i j k : ι)
    (h : Commute (b i j) (t j k)) :
    defect (corrected t b) i j k =
      b j k * b i j * defect t i j k * (b i k)⁻¹ := by
  change (b j k * t j k) * (b i j * t i j) * (b i k * t i k)⁻¹ = _
  calc
    _ = b j k * (t j k * b i j) * t i j * (t i k)⁻¹ * (b i k)⁻¹ := by group
    _ = b j k * b i j * defect t i j k * (b i k)⁻¹ := by
      rw [← h.eq]
      simp only [defect]
      group

/-- The corrected transitions satisfy their triple equation exactly when the explicit central defect is removed by the pair coefficients. -/
theorem corrected_comp_iff (t b : ι → ι → G) (i j k : ι)
    (h : Commute (b i j) (t j k)) :
    corrected t b j k * corrected t b i j = corrected t b i k ↔
      b j k * b i j * defect t i j k = b i k := by
  rw [← defect_eq_one_iff, defect_corrected t b i j k h, mul_inv_eq_one]

/-- Successive pair corrections compose pointwise in the same left-action order. -/
theorem corrected_corrected (t b c : ι → ι → G) :
    corrected (corrected t b) c = corrected t (fun i j => c i j * b i j) := by
  funext i j
  exact (mul_assoc _ _ _).symm

/-- The literal difference between any target transitions and the proposed transitions is a pair correction that reconstructs the target exactly. -/
theorem corrected_difference (t u : ι → ι → G) :
    corrected t (fun i j => u i j * (t i j)⁻¹) = u := by
  funext i j
  exact inv_mul_cancel_right _ _

end FoliationQM.CentralTransitionDefect
