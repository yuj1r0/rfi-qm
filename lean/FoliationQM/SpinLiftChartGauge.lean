module
public import FoliationQM.SpinSignHOne
public import FoliationQM.SpinLiftOverlapTorsor

/-!
# Changing the chart signs of genuine Spin lifts

The global Spin-frame component of v13 `prop:takabayasi` compares genuine
lifts over a fixed Lorentz atlas. A chart sign changes each lifted
transition by its smooth sign coboundary on the actual pair overlap.
The class of the physical transition ratio detects this relation.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.SpinLiftChartGauge
open SpinLiftSignDifference SpinSignOneCocycle SpinLiftOverlapTorsor SpinSignHOne

variable {E H B ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace B] [ChartedSpace H B] {n : WithTop ℕ∞}
  {D : CliffordSpinLorentzTransitions.Data I B ι n}

/-- A smooth sign on each chart identifies two genuine lifts when its coboundary multiplies the first transitions into the second on all pair overlaps. -/
def GaugeEq (P Q : Lift D) : Prop :=
  ∃ a : ZeroCochain I D.domain n, ∀ i j x, x ∈ D.domain i → x ∈ D.domain j →
    Q.transition i j x = ((coboundary a).val.value i j x).val * P.transition i j x

/-- Two genuine Spin lifts differ by chart signs exactly when their physical difference has unit degree-one class. -/
theorem gaugeEq_iff_difference (P Q : Lift D) :
    GaugeEq P Q ↔ classOf (difference P Q) = 1 := by
  rw [classOf_eq_one_iff]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    intro i j x hi hj
    apply Subtype.ext
    rw [difference_val P Q i j x hi hj, ha i j x hi hj, mul_inv_cancel_right]
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    intro i j x hi hj
    have he := congrArg Subtype.val (ha i j x hi hj)
    exact (twist_difference P Q i j x hi hj).symm.trans (congrArg (· * P.transition i j x) he)

/-- Difference classes compose through an intermediate physical lift in the transition order. -/
theorem differenceClass_comp (P Q T : Lift D) :
    classOf (difference Q T) * classOf (difference P Q) = classOf (difference P T) :=
  (classOf_mul (difference Q T) (difference P Q)).symm.trans
    (classOf_eq_of_overlap (difference_comp P Q T))

/-- Relative to any reference lift, two lifts are identified by chart signs exactly when their difference classes from that reference coincide. -/
theorem gaugeEq_iff_based (P Q T : Lift D) :
    GaugeEq Q T ↔ classOf (difference P Q) = classOf (difference P T) := by
  rw [gaugeEq_iff_difference]
  have he := differenceClass_comp P Q T
  constructor
  · intro h
    rwa [h, one_mul] at he
  · intro h
    apply mul_right_cancel (b := classOf (difference P Q))
    rw [he, one_mul, h]

/-- Smooth chartwise changes of sign define an equivalence relation on lifts of fixed Lorentz transitions. -/
theorem gaugeEq_equivalence : Equivalence (GaugeEq (D := D)) where
  refl P := (gaugeEq_iff_based P P P).mpr rfl
  symm {P Q} h := (gaugeEq_iff_based P Q P).mpr ((gaugeEq_iff_based P P Q).mp h).symm
  trans {P Q T} h k := (gaugeEq_iff_based P P T).mpr
    (((gaugeEq_iff_based P P Q).mp h).trans ((gaugeEq_iff_based P Q T).mp k))

/-- Lifts with equal transition values on every actual pair overlap have the same gauge class. -/
theorem gaugeEq_of_agree {P Q : Lift D} (h : Agree P Q) : GaugeEq P Q :=
  (gaugeEq_iff_based P P Q).mpr
    (classOf_eq_of_overlap (difference_congr (agree_equivalence.refl P) h))

/-- Twisting a lift multiplies its relative difference class by the twisting sign class. -/
theorem differenceClass_twist (P Q : Lift D) (z : Cocycle I D.domain n) :
    classOf (difference P (twist Q z)) = classOf z * classOf (difference P Q) := by
  rw [← differenceClass_comp P Q (twist Q z), classOf_eq_of_overlap (difference_twist Q z)]

/-- Twisting respects both gauge equivalence of genuine lifts and chartwise coboundary equivalence of sign cocycles. -/
theorem twist_gauge_congr {P Q : Lift D} {z w : Cocycle I D.domain n}
    (hp : GaugeEq P Q) (hz : GaugeRelated z w) : GaugeEq (twist P z) (twist Q w) := by
  apply (gaugeEq_iff_based P _ _).mpr
  rw [differenceClass_twist, differenceClass_twist, (classOf_eq_iff z w).mpr hz,
    (gaugeEq_iff_based P P Q).mp hp]

/-- The setoid of genuine lifts related by a smooth chart sign on the original cover. -/
def gaugeSetoid (D : CliffordSpinLorentzTransitions.Data I B ι n) : Setoid (Lift D) :=
  ⟨GaugeEq, gaugeEq_equivalence⟩

/-- Genuine lifts of the fixed Lorentz transitions modulo smooth chart signs. -/
def LiftClass (D : CliffordSpinLorentzTransitions.Data I B ι n) := Quotient (gaugeSetoid D)

/-- The fixed-cover gauge class represented by a genuine Spin lift. -/
def liftClass (P : Lift D) : LiftClass D := Quotient.mk _ P

/-- Two representatives define the same lift class exactly when they are related by a smooth chartwise sign change. -/
theorem liftClass_eq_iff (P Q : Lift D) : liftClass P = liftClass Q ↔ GaugeEq P Q := Quotient.eq

end FoliationQM.SpinLiftChartGauge
