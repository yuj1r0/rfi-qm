module
public import FoliationQM.SpinHOneDescent
public import FoliationQM.SpinLiftHOneTorsor

/-!
# Restricting genuine lift classes and their physical differences

Source scope: the Spin-frame component of v13 `prop:takabayasi`.
The difference measured from the restricted physical transitions is
the restriction of the original sign class. Descent of chart signs
then makes the map on lift classes injective.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.SpinLiftClassRestriction
open CliffordSpinCoverRefinement SpinSignOneCocycle SpinSignHOne SpinHOneRestriction
open SpinLiftSignDifference SpinLiftChartGauge

variable {E H B ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace B] [ChartedSpace H B] {n : WithTop ℕ∞}
  {D : CliffordSpinLorentzTransitions.Data I B ι n}

/-- A genuine lift restricts to another genuine lift using the parent Spin transitions on the smaller chart domains. -/
def restrictLift (R : Refinement D.domain κ) (P : Lift D) : Lift (lorentzData D R) where
  toPairLifts := pairLifts P.toPairLifts R
  comp a b c x ha hb hc := P.comp _ _ _ x (R.subset a ha) (R.subset b hb) (R.subset c hc)

/-- The physical transition ratio of restricted lifts agrees with the restricted ratio on every refined overlap. -/
theorem restrict_difference (R : Refinement D.domain κ) (P Q : Lift D) :
    OverlapEq (restrictCocycle R (difference P Q))
      (difference (restrictLift R P) (restrictLift R Q)) := by
  intro a b x ha hb
  apply Subtype.ext
  change ((difference P Q).val.value (R.parent a) (R.parent b) x).val = _
  rw [difference_val P Q _ _ x (R.subset a ha) (R.subset b hb),
    difference_val (restrictLift R P) (restrictLift R Q) a b x ha hb]
  rfl

/-- Restriction of degree-one cohomology sends the difference of two lifts to the difference computed from their restricted transitions. -/
theorem restrict_differenceClass (R : Refinement D.domain κ) (P Q : Lift D) :
    restrictHom R (classOf (difference P Q)) = classOf (difference (restrictLift R P) (restrictLift R Q)) :=
  (restrictHom_classOf R _).trans (classOf_eq_of_overlap (restrict_difference R P Q))

/-- Two lifts become chart-gauge equivalent on a refinement exactly when they were equivalent on the original cover. -/
theorem gaugeEq_restrict_iff (R : Refinement D.domain κ) (P Q : Lift D) :
    GaugeEq (restrictLift R P) (restrictLift R Q) ↔ GaugeEq P Q := by
  rw [gaugeEq_iff_difference, gaugeEq_iff_difference, ← restrict_differenceClass]
  exact SpinHOneDescent.restrictHom_eq_one_iff R _

/-- The map on lift classes induced by restriction of genuine Spin transitions. -/
def restrictClass (R : Refinement D.domain κ) : LiftClass D → LiftClass (lorentzData D R) :=
  Quotient.map (restrictLift R) (fun P Q h => (gaugeEq_restrict_iff R P Q).mpr h)

/-- The restricted geometric transition class is represented by the original lift restricted to the selected parent charts. -/
theorem restrictClass_liftClass (R : Refinement D.domain κ) (P : Lift D) :
    restrictClass R (liftClass P) = liftClass (restrictLift R P) := rfl

/-- Restriction is injective on chart-gauge classes of genuine lifts of the given Lorentz transitions. -/
theorem restrictClass_injective (R : Refinement D.domain κ) : Function.Injective (restrictClass R) := by
  intro p q
  refine Quotient.inductionOn₂ p q ?_
  intro P Q he
  exact (liftClass_eq_iff P Q).mpr ((gaugeEq_restrict_iff R P Q).mp ((liftClass_eq_iff _ _).mp he))

/-- Restricting a twist is the twist of the restricted lift by the restricted sign class. -/
theorem restrictClass_act (R : Refinement D.domain κ) (c : H1 I D.domain n) (p : LiftClass D) :
    restrictClass R (SpinLiftHOneTorsor.act c p) =
      SpinLiftHOneTorsor.act (restrictHom R c) (restrictClass R p) := by
  obtain ⟨z, rfl⟩ := classOf_surjective c
  refine Quotient.inductionOn p ?_
  intro P
  apply (liftClass_eq_iff (restrictLift R (twist P z)) (twist (restrictLift R P) (restrictCocycle R z))).mpr
  exact gaugeEq_of_agree (fun _ _ _ _ _ => rfl)

end FoliationQM.SpinLiftClassRestriction
