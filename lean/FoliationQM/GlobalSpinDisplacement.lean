module
public import FoliationQM.SpinAllCoverHOne
public import FoliationQM.SmoothSpinRelativeClass

/-!
# The global relative sign of independently charted Spin lifts

For the Spin-frame component of v13 `prop:takabayasi`, the relative
sign of two lifts defines an element of the all-cover group. Three
lifts can be measured on the same smaller target charts. Their
transition ratios compose there, so the global difference depends
only on the physical isomorphism classes.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GlobalSpinDisplacement
open CliffordSpinLorentzSmooth LorentzMatrixGroup GeometricSpinObstruction
open SpinSignHOne SpinLiftSignDifference SpinLiftIsomorphism SpinAllCoverHOne
open CliffordSpinCoverRefinement RefinedGeometricPrincipalAtlas JointSpinAdaptation
open SmoothSpinRelativeClass

universe u
variable {E H EP HP : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  {B : Type u} [TopologicalSpace B] [ChartedSpace H B] {I : ModelWithCorners ℝ E H}
  {P ι : Type*} [TopologicalSpace P] [ChartedSpace HP P] {KP : ModelWithCorners ℝ EP HP}
  {proj : P → B} {L : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι}
  {n : WithTop ℕ∞} (LM : GeometricPrincipalSmoothAtlas.Data I lorentzModel KP L n)

/-- The sign comparing the two physical lifts, included into cohomology over all covers. -/
def relative (A T : SmoothLift I KP L n) : GlobalH1 I B n :=
  ofCover _ (common LM A T).covers (relativeClass LM A T)

/-- Compute the same global sign from the canonical adaptations on any smaller family
with the prescribed Lorentz parents. -/
theorem relative_on (A T : SmoothLift I KP L n) (R : Refinement (domains L) B)
    (hp : ∀ i, R.parent i = targetChart L i)
    (hA : ∀ i, (R.domain i : Set B) ⊆ neighborhood LM A i)
    (hT : ∀ i, (R.domain i : Set B) ⊆ neighborhood LM T i) :
    relative LM A T = ofCover R.domain R.covers
      (classOf (difference (transitions (restrictedSmoothAtlas LM R) (adaptOn LM A R hp hA))
        (transitions (restrictedSmoothAtlas LM R) (adaptOn LM T R hp hT)))) := by
  let S : Refinement (common LM A T).domain B :=
    ⟨id, R.domain, R.covers, fun i _ hx => ⟨hA i hx, hT i hx⟩⟩
  unfold relative
  rw [← ofCover_restrict (common LM A T).covers S]
  apply congrArg (ofCover R.domain R.covers)
  apply classOf_eq_of_overlap
  intro i j x hi hj
  apply Subtype.ext
  change ((difference (transitions _ (leftLift LM A T))
    (transitions _ (rightLift LM A T))).val.value i j x).val = _
  rw [difference_val _ _ i j x (S.subset i hi) (S.subset j hj), difference_val _ _ i j x hi hj]
  rfl

/-- Global neutrality detects smooth isomorphisms of the original Spin maps. -/
theorem nonempty_iff_relative_one (A T : SmoothLift I KP L n) :
    Nonempty (SmoothBetween A T) ↔ relative LM A T = 1 :=
  (nonempty_iff_relative_unit LM A T).trans (ofCover_eq_one_iff _ _ _).symm

/-- Comparing any physical lift with itself gives the neutral global class. -/
theorem relative_self (A : SmoothLift I KP L n) : relative LM A A = 1 :=
  (nonempty_iff_relative_one LM A A).mp (iso_equivalence.refl A)

/-- The global signs compose when a third independently charted lift is inserted. -/
theorem relative_comp (A T S : SmoothLift I KP L n) :
    relative LM T S * relative LM A T = relative LM A S := by
  let R : Refinement (domains L) B :=
    { parent := targetChart L
      domain i := (common LM A T).domain i ⊓ neighborhood LM S i
      covers x := ⟨x, mem_common LM A T x, mem_neighborhood LM S x⟩
      subset i _ hx := (common LM A T).subset i hx.1 }
  have hA (i) : (R.domain i : Set B) ⊆ neighborhood LM A i := fun _ hx => hx.1.1
  have hT (i) : (R.domain i : Set B) ⊆ neighborhood LM T i := fun _ hx => hx.1.2
  have hS (i) : (R.domain i : Set B) ⊆ neighborhood LM S i := fun _ hx => hx.2
  rw [relative_on LM T S R (fun _ => rfl) hT hS,
      relative_on LM A T R (fun _ => rfl) hA hT,
      relative_on LM A S R (fun _ => rfl) hA hS, ← map_mul]
  exact congrArg (ofCover R.domain R.covers) (SpinLiftChartGauge.differenceClass_comp _ _ _)

/-- Reversing the comparison inverts its global class. -/
theorem relative_symm (A T : SmoothLift I KP L n) : relative LM T A = (relative LM A T)⁻¹ :=
  eq_inv_of_mul_eq_one_left ((relative_comp LM A T A).trans (relative_self LM A))

/-- Physical isomorphisms in either argument preserve the global relative sign. -/
theorem relative_congr {A A' T T' : SmoothLift I KP L n}
    (hA : Nonempty (SmoothBetween A A')) (hT : Nonempty (SmoothBetween T T')) :
    relative LM A T = relative LM A' T' := by
  have h₁ := relative_comp LM A A' T'
  have h₂ := relative_comp LM A T T'
  rw [(nonempty_iff_relative_one LM _ _).mp hA, mul_one] at h₁
  rw [(nonempty_iff_relative_one LM _ _).mp hT, one_mul] at h₂
  exact h₂.trans h₁.symm

/-- The displacement of smooth physical isomorphism classes over the original target. -/
def displacement (p q : PhysicalClass I KP L n) : GlobalH1 I B n :=
  Quotient.liftOn₂ p q (relative LM) (fun _ _ _ _ h k => relative_congr LM h k)

/-- Displacement is the global sign extracted from any two representatives. -/
theorem displacement_physicalClass (A T : SmoothLift I KP L n) :
    displacement LM (physicalClass A) (physicalClass T) = relative LM A T := rfl

/-- A unit displacement is equivalent to equality of the physical classes. -/
theorem displacement_one_iff (p q : PhysicalClass I KP L n) :
    displacement LM p q = 1 ↔ p = q := by
  refine Quotient.inductionOn₂ p q ?_
  intro A T
  exact (ofCover_eq_one_iff _ _ (relativeClass LM A T)).trans (physicalClass_eq_iff LM A T).symm

/-- Differences of physical classes compose in the all-cover group. -/
theorem displacement_comp (p q r : PhysicalClass I KP L n) :
    displacement LM q r * displacement LM p q = displacement LM p r :=
  Quotient.inductionOn₃ p q r (relative_comp LM)

/-- Differences from a fixed smooth physical class distinguish all other classes. -/
theorem based_injective (p : PhysicalClass I KP L n) : Function.Injective (displacement LM p) := by
  intro q r h
  apply (displacement_one_iff LM q r).mp
  apply mul_right_cancel (b := displacement LM p q)
  rw [displacement_comp, one_mul, h]

end FoliationQM.GlobalSpinDisplacement
