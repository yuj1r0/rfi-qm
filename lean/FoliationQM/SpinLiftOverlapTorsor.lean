module
public import FoliationQM.SpinLiftSignDifference

/-!
# Sign differences and twists on a fixed cover

Source scope: the Spin-frame component of v13 `prop:takabayasi`.
Once a genuine lift is chosen, the transition values of every other
lift on the pair overlaps are parametrized uniquely by a sign cocycle
on those overlaps. This comparison precedes taking chartwise gauges.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.SpinLiftOverlapTorsor
open SpinLiftSignDifference SpinSignOneCocycle

variable {E H B ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace B] [ChartedSpace H B] {n : WithTop ℕ∞}
  {D : CliffordSpinLorentzTransitions.Data I B ι n}

/-- Two genuine lifts have the same transition values on the cover if they agree on every pair overlap. -/
def Agree (P Q : Lift D) : Prop :=
  ∀ i j x, x ∈ D.domain i → x ∈ D.domain j → P.transition i j x = Q.transition i j x

/-- Agreement of actual lift transitions is an equivalence relation. -/
theorem agree_equivalence : Equivalence (Agree (D := D)) :=
  ⟨fun _ _ _ _ _ _ => rfl, fun h i j x hi hj => (h i j x hi hj).symm,
    fun h k i j x hi hj => (h i j x hi hj).trans (k i j x hi hj)⟩

/-- Signs and lifts may both be replaced by representatives equal on the true pair overlaps before twisting. -/
theorem twist_congr {P Q : Lift D} {z w : Cocycle I D.domain n}
    (hp : Agree P Q) (hz : OverlapEq z w) : Agree (twist P z) (twist Q w) := by
  intro i j x hi hj
  rw [twist_transition, twist_transition, hp i j x hi hj, hz i j x hi hj]

/-- The transition ratio of lifts depends only on their actual pair-overlap values. -/
theorem difference_congr {P Q P' Q' : Lift D} (hp : Agree P P') (hq : Agree Q Q') :
    OverlapEq (difference P Q) (difference P' Q') := by
  intro i j x hi hj
  apply Subtype.ext
  rw [difference_val _ _ i j x hi hj, difference_val _ _ i j x hi hj,
    hp i j x hi hj, hq i j x hi hj]

/-- Twisting by the physical ratio from P to Q recovers Q on every actual overlap. -/
theorem twist_difference (P Q : Lift D) : Agree (twist P (difference P Q)) Q := by
  intro i j x hi hj
  rw [twist_transition, difference_val _ _ i j x hi hj, inv_mul_cancel_right]

/-- Taking the difference from the reference lift recovers the twisting sign on each actual overlap. -/
theorem difference_twist (P : Lift D) (z : Cocycle I D.domain n) :
    OverlapEq (difference P (twist P z)) z := by
  intro i j x hi hj
  apply Subtype.ext
  rw [difference_val _ _ i j x hi hj, twist_transition, mul_inv_cancel_right]

/-- Consecutive differences compose pointwise in the physical order through the intermediate lift. -/
theorem difference_comp (P Q T : Lift D) :
    OverlapEq (mul (difference Q T) (difference P Q)) (difference P T) := by
  intro i j x hi hj
  apply Subtype.ext
  change ((difference Q T).val.value i j x).val * ((difference P Q).val.value i j x).val = _
  rw [difference_val _ _ i j x hi hj, difference_val _ _ i j x hi hj,
    difference_val _ _ i j x hi hj, mul_assoc, inv_mul_cancel_left]

/-- The unit sign leaves lift transitions unchanged on the cover. -/
theorem twist_unit (P : Lift D) : Agree (twist P (unit I D.domain n)) P :=
  fun _ _ _ _ _ => one_mul _

/-- Two successive twists act by the product of their ordered pair signs. -/
theorem twist_mul (P : Lift D) (z w : Cocycle I D.domain n) :
    Agree (twist (twist P z) w) (twist P (mul w z)) :=
  fun _ _ _ _ _ => (mul_assoc _ _ _).symm

/-- Genuine lifts modulo equality of transition values on actual overlaps. -/
def LiftValues (D : CliffordSpinLorentzTransitions.Data I B ι n) :=
  Quotient (⟨Agree, agree_equivalence⟩ : Setoid (Lift D))

/-- Degree-one signs modulo equality of values on actual overlaps. -/
def SignValues (I : ModelWithCorners ℝ E H) (U : ι → TopologicalSpace.Opens B) (n : WithTop ℕ∞) :=
  Quotient (⟨OverlapEq, overlapEq_equivalence⟩ : Setoid (Cocycle I U n))

/-- A reference lift identifies overlap sign cocycles bijectively with the overlap values of genuine lifts. -/
def basedEquiv (P : Lift D) : SignValues I D.domain n ≃ LiftValues D where
  toFun := Quotient.map (twist P) (fun _ _ hz => twist_congr (agree_equivalence.refl P) hz)
  invFun := Quotient.map (difference P) (fun _ _ hq => difference_congr (agree_equivalence.refl P) hq)
  left_inv q := Quotient.inductionOn q fun z => Quotient.sound (difference_twist P z)
  right_inv q := Quotient.inductionOn q fun Q => Quotient.sound (twist_difference P Q)

end FoliationQM.SpinLiftOverlapTorsor
