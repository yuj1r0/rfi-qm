module
public import FoliationQM.SignCommonRefinement
public import FoliationQM.SpinObstructionRestriction

/-!
# Comparing sign obstruction classes after further refinement

Source scope: a geometric Spin-frame component of v13 `prop:takabayasi`.
Two classes on a given open cover eventually agree when some refinement,
indexed by points of the base, gives equal fixed-cover restrictions. The
common refinement and change-of-parent formula compare such witnesses with
any other refinement, regardless of the universe of its index type. For the
physical obstruction, eventual neutrality detects a genuine Clifford Spin
cocycle over some refinement.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.SignEventualObstruction
open CliffordSpinCoverRefinement SignCommonRefinement SignClassRestriction SpinSignCohomology

variable {E H B ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace B] [ChartedSpace H B] {U : ι → TopologicalSpace.Opens B} {n : WithTop ℕ∞}

/-- Two classes agree eventually when a base-point-indexed open refinement gives equal restrictions. -/
def EventuallyEqual (c d : ObstructionClass I U n) : Prop :=
  ∃ R : Refinement U B, restrictClass R c = restrictClass R d

/-- A class vanishes after refinement when it eventually agrees with the original neutral class. -/
def Vanishes (c : ObstructionClass I U n) : Prop := EventuallyEqual c (neutralClass I U n)

/-- Equality on a refinement with indices in any universe supplies a point-indexed refinement witnessing eventual equality. -/
theorem eventuallyEqual_of_any_refinement (R : Refinement U κ) {c d : ObstructionClass I U n}
    (h : restrictClass R c = restrictClass R d) : EventuallyEqual c d := by
  refine ⟨SignCommonRefinement.narrow R, ?_⟩
  exact (restrictClass_narrow R c).symm.trans <|
    (congrArg (restrictClass (pointCover R.domain R.covers)) h).trans (restrictClass_narrow R d)

/-- For a covering open family, every class eventually agrees with itself. -/
theorem eventuallyEqual_refl (hU : ∀ x : B, ∃ i, x ∈ U i) (c : ObstructionClass I U n) :
    EventuallyEqual c c := ⟨pointCover U hU, rfl⟩

/-- Eventual equality is symmetric on the same witnessing refinement. -/
theorem eventuallyEqual_symm {c d : ObstructionClass I U n} (h : EventuallyEqual c d) :
    EventuallyEqual d c := by
  obtain ⟨R, hR⟩ := h
  exact ⟨R, hR.symm⟩

/-- Restriction along any specified refinement preserves and reflects eventual equality of the original classes. -/
theorem eventuallyEqual_iff_refine (R : Refinement U κ) (c d : ObstructionClass I U n) :
    EventuallyEqual c d ↔ EventuallyEqual (restrictClass R c) (restrictClass R d) := by
  constructor
  · rintro ⟨S, hS⟩
    refine ⟨SignCommonRefinement.left R S, ?_⟩
    exact (restrictClass_common R S c).trans <|
      (congrArg (restrictClass (SignCommonRefinement.right R S)) hS).trans
        (restrictClass_common R S d).symm
  · rintro ⟨T, hT⟩
    refine ⟨SpinRefinementComposition.compose R T, ?_⟩
    exact (restrictClass_compose R T c).symm.trans (hT.trans (restrictClass_compose R T d))

/-- Common refinement makes eventual equality transitive even when the two equalities have different witnesses. -/
theorem eventuallyEqual_trans {c d e : ObstructionClass I U n}
    (h₁ : EventuallyEqual c d) (h₂ : EventuallyEqual d e) : EventuallyEqual c e := by
  obtain ⟨R, hR⟩ := h₁
  apply (eventuallyEqual_iff_refine R c e).mpr
  rw [hR]
  exact (eventuallyEqual_iff_refine R d e).mp h₂

/-- A neutral restriction on any open refinement witnesses eventual vanishing, regardless of the index universe. -/
theorem of_any_refinement (R : Refinement U κ) {c : ObstructionClass I U n}
    (h : restrictClass R c = neutralClass I R.domain n) : Vanishes c :=
  eventuallyEqual_of_any_refinement R (h.trans (restrictClass_neutral R).symm)

/-- The obstruction vanishes after further refinement exactly when its restriction along any one refinement does. -/
theorem vanishes_iff_refine (R : Refinement U κ) (c : ObstructionClass I U n) :
    Vanishes c ↔ Vanishes (restrictClass R c) :=
  eventuallyEqual_iff_refine R c (neutralClass I U n)

/-- Equivalence of fixed-cover classes under equality on a common further refinement. -/
def eventualSetoid (I : ModelWithCorners ℝ E H) (U : ι → TopologicalSpace.Opens B)
    (n : WithTop ℕ∞) (hU : ∀ x : B, ∃ i, x ∈ U i) : Setoid (ObstructionClass I U n) where
  r := EventuallyEqual
  iseqv := ⟨eventuallyEqual_refl hU, fun h => eventuallyEqual_symm h,
    fun h₁ h₂ => eventuallyEqual_trans h₁ h₂⟩

/-- Classes represented on the original cover, identified whenever they agree after some refinement. -/
def StableClass (I : ModelWithCorners ℝ E H) (U : ι → TopologicalSpace.Opens B)
    (n : WithTop ℕ∞) (hU : ∀ x : B, ∃ i, x ∈ U i) := Quotient (eventualSetoid I U n hU)

/-- The stable class represented by a class on this covering family. -/
def stableClass (hU : ∀ x : B, ∃ i, x ∈ U i) (c : ObstructionClass I U n) :
    StableClass I U n hU := Quotient.mk _ c

/-- Two classes from this cover have equal stable images exactly when a point-indexed open refinement identifies them. -/
theorem stableClass_eq_iff (hU : ∀ x : B, ∃ i, x ∈ U i) (c d : ObstructionClass I U n) :
    stableClass hU c = stableClass hU d ↔ EventuallyEqual c d := Quotient.eq

/-- The stable image of a fixed-cover class equals the neutral image exactly when the class vanishes after refinement. -/
theorem stableClass_neutral_iff (hU : ∀ x : B, ∃ i, x ∈ U i) (c : ObstructionClass I U n) :
    stableClass hU c = stableClass hU (neutralClass I U n) ↔ Vanishes c :=
  stableClass_eq_iff hU c _

/-- Restrict the stable classes represented on a covered family to the stable classes represented on a refined family. -/
def stableRestrict (hU : ∀ x : B, ∃ i, x ∈ U i) (R : Refinement U κ) (s : StableClass I U n hU) :
    StableClass I R.domain n R.covers :=
  Quotient.liftOn s (fun c => stableClass R.covers (restrictClass R c))
    (fun c d h => (stableClass_eq_iff R.covers _ _).mpr ((eventuallyEqual_iff_refine R c d).mp h))

/-- Restricting a stable class restricts its given fixed-cover representative. -/
theorem stableRestrict_stableClass (hU : ∀ x : B, ∃ i, x ∈ U i) (R : Refinement U κ)
    (c : ObstructionClass I U n) :
    stableRestrict hU R (stableClass hU c) = stableClass R.covers (restrictClass R c) := rfl

/-- Stable classes represented on the original cover embed into the stable classes represented after any refinement. -/
theorem stableRestrict_injective (hU : ∀ x : B, ∃ i, x ∈ U i) (R : Refinement U κ) :
    Function.Injective (stableRestrict (I := I) (n := n) hU R) := by
  intro a b
  induction a using Quotient.inductionOn with
  | h c =>
    induction b using Quotient.inductionOn with
    | h d =>
      intro heq
      exact (stableClass_eq_iff hU c d).mpr <| (eventuallyEqual_iff_refine R c d).mpr <|
        (stableClass_eq_iff R.covers _ _).mp heq

open CliffordSpinTransitionLifts CliffordSpinCocycleCorrection SpinSignDefectRepresentative

/-- The physical obstruction of normalized pair lifts vanishes after refinement exactly when some actual refined Lorentz cocycle admits a genuine Spin cocycle lift. -/
theorem vanishes_iff_exists_refinement_lift {D : CliffordSpinLorentzTransitions.Data I B ι n}
    (P : PairLifts D) : Vanishes (classOf (representative P)) ↔
      ∃ R : Refinement D.domain B, HasSpinCocycleLift (lorentzData D R) := by
  constructor
  · rintro ⟨R, hR⟩
    exact ⟨R, (SpinObstructionRestriction.restrict_neutral_iff_lift R P).mp hR⟩
  · rintro ⟨R, hR⟩
    exact ⟨R, (SpinObstructionRestriction.restrict_neutral_iff_lift R P).mpr hR⟩

end FoliationQM.SignEventualObstruction
