module

public import FoliationQM.DressedVelocity
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/-!
# The shell-restricted Reeb equations in explicit canonical coordinates

Source: v13 `thm:contact_period`, part (i). Position components are raised
coordinates and momentum components are lowered coordinates. The canonical
pairing is the ordinary coordinate contraction; raising momentum uses the
explicit (+---) metric. The tangent predicate is the linearized shell
constraint. The exterior-derivative realization of the canonical two-form
is supplied separately; the contraction is restricted to shell tangents.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.ContactReeb

open scoped BigOperators

/-- Ambient canonical position and lowered-momentum coordinates. -/
abbrev Ambient := Covector × Covector

/-- Ordinary coordinate contraction between a covector and vector. -/
def pairing (p q : Covector) : ℝ := ∑ i : Fin 4, p i * q i

/-- Index raising in the fixed (+---) coordinates. -/
def sharp (p : Covector) : Covector := fun i => if i = 0 then p i else -p i

/-- The ambient Liouville one-form evaluated on an actual coordinate tangent. -/
def alpha (z v : Ambient) : ℝ := -pairing z.2 v.1

/-- The canonical alternating two-form in the source sign convention. -/
def canonicalTwo (v w : Ambient) : ℝ := pairing v.1 w.2 - pairing w.1 v.2

/-- The positive-energy fixed-mass momentum shell. -/
def OnShell (m c : ℝ) (p : Covector) : Prop :=
  minkowski p p = m ^ 2 * c ^ 2 ∧ 0 < p 0

/-- The linearized mass-shell constraint on the momentum component. -/
def Tangent (p : Covector) (v : Ambient) : Prop := minkowski p v.2 = 0

/-- The source Reeb candidate has raised position component and zero momentum component. -/
def reeb (m c : ℝ) (p : Covector) : Ambient :=
  (fun i => -sharp p i / (m ^ 2 * c ^ 2), 0)

/-- Ordinary coordinate contraction is symmetric as a real bilinear expression. -/
theorem pairing_comm (p q : Covector) : pairing p q = pairing q p := by
  simp only [pairing, mul_comm]

/-- Coordinate contraction is additive in its first argument. -/
theorem pairing_add_left (p q v : Covector) : pairing (p + q) v = pairing p v + pairing q v := by
  simp [pairing, add_mul, Finset.sum_add_distrib]

/-- Coordinate contraction is additive in its second argument. -/
theorem pairing_add_right (p v w : Covector) : pairing p (v + w) = pairing p v + pairing p w := by
  simp [pairing, mul_add, Finset.sum_add_distrib]

/-- Coordinate contraction is homogeneous in its first argument. -/
theorem pairing_smul_left (a : ℝ) (p q : Covector) : pairing (a • p) q = a * pairing p q := by
  simp [pairing, mul_assoc, Finset.mul_sum]

/-- Coordinate contraction is homogeneous in its second argument. -/
theorem pairing_smul_right (a : ℝ) (p q : Covector) : pairing p (a • q) = a * pairing p q := by
  rw [pairing_comm, pairing_smul_left, pairing_comm q p]

/-- The zero first vector has zero coordinate pairing. -/
theorem pairing_zero_left (p : Covector) : pairing 0 p = 0 := by simp [pairing]

/-- The zero second vector has zero coordinate pairing. -/
theorem pairing_zero_right (p : Covector) : pairing p 0 = 0 := by simp [pairing]

/-- Pairing with a coordinate covector extracts the corresponding component. -/
theorem pairing_single_left (p : Covector) (i : Fin 4) : pairing (Pi.single i 1) p = p i := by
  simp [pairing, Pi.single_apply]

/-- Pairing with a coordinate vector extracts the corresponding component. -/
theorem pairing_single_right (p : Covector) (i : Fin 4) : pairing p (Pi.single i 1) = p i := by
  rw [pairing_comm, pairing_single_left]

/-- Raising twice restores the original coordinates. -/
theorem sharp_sharp (p : Covector) : sharp (sharp p) = p := by
  funext i
  by_cases hi : i = 0 <;> simp [sharp, hi]

/-- Raising a momentum before the ordinary contraction gives the explicit Minkowski form. -/
theorem pairing_sharp_left (p q : Covector) : pairing (sharp p) q = minkowski p q := by
  simp [pairing, sharp, minkowski, Fin.sum_univ_succ]
  ring

/-- Raising the second argument gives the same explicit Minkowski contraction. -/
theorem pairing_sharp_right (p q : Covector) : pairing p (sharp q) = minkowski p q := by
  simp [pairing, sharp, minkowski, Fin.sum_univ_succ]
  ring

/-- Raising both arguments preserves the Minkowski bilinear form. -/
theorem minkowski_sharp (p q : Covector) : minkowski (sharp p) (sharp q) = minkowski p q := by
  simp [minkowski, sharp]

/-- The canonical two-form is alternating, with its source orientation. -/
theorem canonicalTwo_self (v : Ambient) : canonicalTwo v v = 0 := by simp [canonicalTwo]

/-- Interchanging tangent vectors reverses the canonical two-form. -/
theorem canonicalTwo_swap (v w : Ambient) : canonicalTwo v w = -canonicalTwo w v := by
  simp only [canonicalTwo]
  ring

/-- Every pure position displacement satisfies the linearized shell condition. -/
theorem tangent_position (p dx : Covector) : Tangent p (dx, 0) := by
  simp [Tangent, minkowski]

/-- The Reeb candidate is tangent to the mass shell because its momentum is constant. -/
theorem reeb_tangent (m c : ℝ) (p : Covector) : Tangent p (reeb m c p) :=
  tangent_position p _

/-- The Liouville evaluation of the Reeb candidate is the mass-shell ratio. -/
theorem alpha_reeb (z : Ambient) (m c : ℝ) :
    alpha z (reeb m c z.2) = minkowski z.2 z.2 / (m ^ 2 * c ^ 2) := by
  simp [alpha, reeb, pairing, sharp, minkowski, Fin.sum_univ_succ]
  ring

/-- On the massive shell the actual Liouville evaluation is exactly one. -/
theorem alpha_reeb_eq_one {m c : ℝ} (hm : 0 < m) (hc : 0 < c)
    {z : Ambient} (hs : OnShell m c z.2) : alpha z (reeb m c z.2) = 1 := by
  rw [alpha_reeb, hs.1]
  exact div_self (mul_ne_zero (pow_ne_zero _ hm.ne') (pow_ne_zero _ hc.ne'))

/-- The ambient Reeb contraction retains the momentum differential; it is
not identically zero before imposing the shell tangent constraint. -/
theorem canonicalTwo_reeb (m c : ℝ) (p : Covector) (v : Ambient) :
    canonicalTwo (reeb m c p) v = -(minkowski p v.2) / (m ^ 2 * c ^ 2) := by
  simp [canonicalTwo, reeb, pairing, sharp, minkowski, Fin.sum_univ_succ]
  ring

/-- Restriction to actual linearized shell tangents makes the Reeb contraction vanish. -/
theorem canonicalTwo_reeb_tangent (m c : ℝ) (p : Covector) (v : Ambient)
    (hv : Tangent p v) : canonicalTwo (reeb m c p) v = 0 := by
  rw [canonicalTwo_reeb, hv]
  simp

/-- Nondegeneracy in pure-position test directions forces a characteristic
vector's momentum component to vanish. -/
theorem characteristic_momentum_zero {p : Covector} {w : Ambient}
    (hw : ∀ v : Ambient, Tangent p v → canonicalTwo w v = 0) : w.2 = 0 := by
  funext i
  have h := hw (Pi.single i 1, 0) (tangent_position p _)
  simpa only [canonicalTwo, pairing_zero_right, pairing_single_left, zero_sub,
    neg_eq_zero, Pi.zero_apply] using h

/-- A coordinate covector with arbitrary coefficient gives the corresponding
scaled coordinate contraction. -/
theorem pairing_single_value_right (p : Covector) (i : Fin 4) (a : ℝ) :
    pairing p (Pi.single i a) = p i * a := by
  simp [pairing, Pi.single_apply]

/-- Each spatial momentum direction has its unique compensating energy
component on a positive-energy shell. -/
def shellMomentumDirection (p : Covector) (i : Fin 3) : Covector :=
  Pi.single 0 (p i.succ / p 0) + Pi.single i.succ 1

/-- The compensated momentum direction satisfies the actual linearized
mass-shell equation when the energy coordinate is nonzero. -/
theorem shellMomentumDirection_tangent {p : Covector} (hp : p 0 ≠ 0) (i : Fin 3) :
    Tangent p (0, shellMomentumDirection p i) := by
  change minkowski p (shellMomentumDirection p i) = 0
  rw [← pairing_sharp_left, shellMomentumDirection, pairing_add_right,
    pairing_single_value_right, pairing_single_value_right]
  simp only [sharp, ite_true, Fin.succ_ne_zero, ite_false, mul_one]
  field_simp
  ring

/-- Every shell characteristic direction has spatial position components
fixed by its time component and the raised momentum. -/
theorem characteristic_position_succ {p : Covector} (hp : p 0 ≠ 0) {w : Ambient}
    (hw : ∀ v : Ambient, Tangent p v → canonicalTwo w v = 0) (i : Fin 3) :
    w.1 i.succ = -(w.1 0) * p i.succ / p 0 := by
  have h := hw (0, shellMomentumDirection p i) (shellMomentumDirection_tangent hp i)
  simp only [canonicalTwo, pairing_zero_left, sub_zero] at h
  change pairing w.1 (shellMomentumDirection p i) = 0 at h
  rw [shellMomentumDirection, pairing_add_right,
    pairing_single_value_right, pairing_single_value_right, mul_one] at h
  calc
    w.1 i.succ = -(w.1 0 * (p i.succ / p 0)) := by linarith
    _ = _ := by ring

/-- The kernel of the restricted canonical two-form consists precisely of
the raised-momentum line in the position variables. -/
theorem characteristic_eq_smul {p : Covector} (hp : p 0 ≠ 0) {w : Ambient}
    (hw : ∀ v : Ambient, Tangent p v → canonicalTwo w v = 0) :
    w = ((w.1 0 / p 0) • sharp p, 0) := by
  apply Prod.ext
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Pi.smul_apply, smul_eq_mul, sharp, ite_true]
      field_simp
    · rw [characteristic_position_succ hp hw j]
      simp only [Pi.smul_apply, smul_eq_mul, sharp, Fin.succ_ne_zero, ite_false]
      ring
  · exact characteristic_momentum_zero hw

/-- The raised-momentum line really is the kernel on the constrained shell
tangents, including the zero direction. -/
theorem characteristic_smul (p : Covector) (a : ℝ) (v : Ambient) (hv : Tangent p v) :
    canonicalTwo (a • sharp p, 0) v = 0 := by
  rw [canonicalTwo, pairing_zero_right, sub_zero, pairing_smul_left, pairing_sharp_left, hv]
  exact mul_zero a

/-- The normalized Reeb vector is unique among all ambient tangent candidates
whose canonical contraction vanishes on the complete shell tangent space. -/
theorem reeb_unique {m c : ℝ} (hm : 0 < m) (hc : 0 < c) {z w : Ambient}
    (hs : OnShell m c z.2) (hα : alpha z w = 1)
    (hw : ∀ v : Ambient, Tangent z.2 v → canonicalTwo w v = 0) :
    w = reeb m c z.2 := by
  have hline := characteristic_eq_smul hs.2.ne' hw
  have hnorm : -(w.1 0 / z.2 0) * (m ^ 2 * c ^ 2) = 1 := by
    have hα' := hα
    rw [hline] at hα'
    simpa only [alpha, pairing_smul_right, pairing_sharp_right, hs.1, neg_mul] using hα'
  have hden : m ^ 2 * c ^ 2 ≠ 0 := mul_ne_zero (pow_ne_zero _ hm.ne') (pow_ne_zero _ hc.ne')
  have hscale : w.1 0 / z.2 0 = -(1 / (m ^ 2 * c ^ 2)) := by
    apply (eq_neg_iff_add_eq_zero).mpr
    apply (mul_right_cancel₀ hden)
    field_simp at hnorm ⊢
    linarith
  rw [hline]
  apply Prod.ext
  · funext i
    simp only [Pi.smul_apply, smul_eq_mul, reeb, hscale]
    ring
  · rfl

/-- The two defining restricted equations characterize exactly the source
Reeb vector on the massive positive-energy shell. -/
theorem reeb_characterization {m c : ℝ} (hm : 0 < m) (hc : 0 < c) {z w : Ambient}
    (hs : OnShell m c z.2) :
    (alpha z w = 1 ∧ ∀ v : Ambient, Tangent z.2 v → canonicalTwo w v = 0) ↔
      w = reeb m c z.2 := by
  constructor
  · intro h
    exact reeb_unique hm hc hs h.1 h.2
  · rintro rfl
    exact ⟨alpha_reeb_eq_one hm hc hs, fun v hv => canonicalTwo_reeb_tangent m c z.2 v hv⟩

end FoliationQM.ContactReeb
