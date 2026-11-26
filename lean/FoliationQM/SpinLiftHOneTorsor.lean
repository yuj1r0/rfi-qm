module
public import FoliationQM.SpinLiftChartGauge
public import Mathlib.Algebra.Torsor.Defs

/-!
# The degree-one sign action on classes of Spin lifts

Source scope: the geometric Spin-frame component of v13 `prop:takabayasi`.
Twist and transition ratio descend to the quotient by smooth chartwise
signs. Their inverse identities give simple transitivity on the set of
lift classes whenever a genuine lift exists.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.SpinLiftHOneTorsor
open SpinSignOneCocycle SpinSignHOne SpinLiftSignDifference SpinLiftChartGauge SpinLiftOverlapTorsor

variable {E H B ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace B] [ChartedSpace H B] {n : WithTop ℕ∞}
  {D : CliffordSpinLorentzTransitions.Data I B ι n}

/-- Twisting lift classes by sign cohomology classes uses representatives on the original cover. -/
def act (c : H1 I D.domain n) (p : LiftClass D) : LiftClass D :=
  Quotient.liftOn₂ c p (fun z P => liftClass (twist P z))
    (fun _ _ _ _ hz hp => (liftClass_eq_iff _ _).mpr (twist_gauge_congr hp hz))

/-- The action on representatives is the class of the actual twisted Spin transitions. -/
theorem act_classOf (z : Cocycle I D.domain n) (P : Lift D) :
    act (classOf z) (liftClass P) = liftClass (twist P z) := rfl

/-- Changing either lift by chartwise signs preserves the cohomology class of its transition ratio. -/
theorem differenceClass_congr {P Q P' Q' : Lift D} (hp : GaugeEq P P') (hq : GaugeEq Q Q') :
    classOf (difference P Q) = classOf (difference P' Q') := by
  have h := differenceClass_comp P P' Q'
  rw [(gaugeEq_iff_difference P P').mp hp, mul_one] at h
  exact ((gaugeEq_iff_based P Q Q').mp hq).trans h.symm

/-- The displacement from one lift class to another is the class of their pointwise physical transition ratio. -/
def displacement (p q : LiftClass D) : H1 I D.domain n :=
  Quotient.liftOn₂ p q (fun P Q => classOf (difference P Q))
    (fun _ _ _ _ hp hq => differenceClass_congr hp hq)

/-- On two actual lifts the displacement computes their degree-one sign class. -/
theorem displacement_liftClass (P Q : Lift D) :
    displacement (liftClass P) (liftClass Q) = classOf (difference P Q) := rfl

/-- Twisting by the displacement between two lift classes sends the first class to the second. -/
theorem act_displacement (p q : LiftClass D) : act (displacement p q) p = q :=
  Quotient.inductionOn₂ p q fun P Q => (liftClass_eq_iff _ _).mpr
    (gaugeEq_of_agree (twist_difference P Q))

/-- The displacement of a twist is its original cohomology class. -/
theorem displacement_act (c : H1 I D.domain n) (p : LiftClass D) : displacement p (act c p) = c :=
  Quotient.inductionOn₂ c p fun z P => classOf_eq_of_overlap (difference_twist P z)

/-- The neutral cohomology class fixes every lift class. -/
theorem act_one (p : LiftClass D) : act 1 p = p := by
  rw [← classOf_unit I D.domain n]
  exact Quotient.inductionOn p fun P => (liftClass_eq_iff _ _).mpr (gaugeEq_of_agree (twist_unit P))

/-- Multiplication in degree-one sign cohomology corresponds to successive twists. -/
theorem act_mul (c d : H1 I D.domain n) (p : LiftClass D) :
    act (c * d) p = act c (act d p) := by
  obtain ⟨z, rfl⟩ := classOf_surjective c
  obtain ⟨w, rfl⟩ := classOf_surjective d
  rw [← classOf_mul]
  exact Quotient.inductionOn p fun P => ((liftClass_eq_iff _ _).mpr
    (gaugeEq_of_agree (twist_mul P w z))).symm

/-- Exactly one degree-one sign class carries any specified lift class to any other. -/
theorem existsUnique_act (p q : LiftClass D) : ∃! c : H1 I D.domain n, act c p = q := by
  refine ⟨displacement p q, act_displacement p q, ?_⟩
  intro c hc
  rw [← hc, displacement_act]

/-- The only cohomology class fixing a specified lift class is the neutral one. -/
theorem act_eq_self_iff (c : H1 I D.domain n) (p : LiftClass D) : act c p = p ↔ c = 1 := by
  constructor
  · intro h
    calc
      c = displacement p (act c p) := (displacement_act c p).symm
      _ = displacement p (act 1 p) := by rw [h, act_one]
      _ = 1 := displacement_act 1 p
  · rintro rfl
    exact act_one p

/-- Choosing a lift class gives an explicit bijection from sign cohomology to all gauge classes of lifts. -/
def basedEquiv (p : LiftClass D) : H1 I D.domain n ≃ LiftClass D where
  toFun c := act c p
  invFun := displacement p
  left_inv c := displacement_act c p
  right_inv q := act_displacement p q

/-- For Lorentz data admitting a genuine lift, its gauge classes form a torsor for the fixed-cover degree-one sign group. -/
@[instance_reducible] def torsor (h : Nonempty (Lift D)) : Torsor (H1 I D.domain n) (LiftClass D) where
  smul := act
  one_smul := act_one
  mul_smul := act_mul
  sdiv q p := displacement p q
  nonempty := h.map liftClass
  sdiv_smul' q p := act_displacement p q
  smul_sdiv' := displacement_act

end FoliationQM.SpinLiftHOneTorsor
