module
public import FoliationQM.SignRefinementPrism

/-!
# Comparing two restrictions on a common open refinement

Source scope: the Spin obstruction component of v13 `prop:takabayasi`
(A/C/D, component only). Choose one containing open in each refined
cover for each base point. Their intersection covers that point and is
a domain for both further restrictions. The prism theorem identifies the
two resulting class maps because they differ only in the assignment of
original chart indices to these same intersections.
-/

@[expose] public section
noncomputable section
open Set
namespace FoliationQM.SignCommonRefinement
open CliffordSpinCoverRefinement SpinRefinementComposition SignRefinementPrism
open SpinSignCohomology SignClassRestriction

variable {B ι κ τ : Type*} [TopologicalSpace B] {U : ι → TopologicalSpace.Opens B}

/-- Choose a member containing each base point, obtaining a refinement indexed by the base itself. -/
def pointCover (U : ι → TopologicalSpace.Opens B) (hU : ∀ x : B, ∃ i, x ∈ U i) :
    Refinement U B where
  parent x := Classical.choose (hU x)
  domain x := U (Classical.choose (hU x))
  covers x := ⟨x, Classical.choose_spec (hU x)⟩
  subset _ := Subset.rfl

/-- Each open in the point-indexed refinement is its chosen original cover member. -/
theorem pointCover_domain (U : ι → TopologicalSpace.Opens B)
    (hU : ∀ x : B, ∃ i, x ∈ U i) (x : B) :
    (pointCover U hU).domain x = U ((pointCover U hU).parent x) := rfl

/-- The original point belongs to the open indexed by that point. -/
theorem pointCover_mem (U : ι → TopologicalSpace.Opens B)
    (hU : ∀ x : B, ∃ i, x ∈ U i) (x : B) : x ∈ (pointCover U hU).domain x :=
  Classical.choose_spec (hU x)

/-- Any refinement has a further refinement indexed by base points, composed back to its original cover. -/
def narrow (R : Refinement U κ) : Refinement U B :=
  compose R (pointCover R.domain R.covers)

/-- The further point-indexed refinement of any refinement retains its anchor point in each chosen domain. -/
theorem narrow_mem (R : Refinement U κ) (x : B) : x ∈ (narrow R).domain x :=
  pointCover_mem R.domain R.covers x

/-- At a base point, intersect the chosen containing opens from two refinements of the same cover. -/
def commonDomain (R : Refinement U κ) (S : Refinement U τ) (x : B) : TopologicalSpace.Opens B :=
  (pointCover R.domain R.covers).domain x ⊓ (pointCover S.domain S.covers).domain x

/-- Each intersection contains its indexing point, so the common opens cover the whole base. -/
theorem mem_commonDomain (R : Refinement U κ) (S : Refinement U τ) (x : B) :
    x ∈ commonDomain R S x :=
  ⟨pointCover_mem R.domain R.covers x, pointCover_mem S.domain S.covers x⟩

/-- The common intersection lies in its first chosen refined chart. -/
theorem commonDomain_subset_left (R : Refinement U κ) (S : Refinement U τ) (x : B) :
    (commonDomain R S x : Set B) ⊆ R.domain ((pointCover R.domain R.covers).parent x) :=
  fun _ hy => hy.1

/-- The common intersection lies in its second chosen refined chart. -/
theorem commonDomain_subset_right (R : Refinement U κ) (S : Refinement U τ) (x : B) :
    (commonDomain R S x : Set B) ⊆ S.domain ((pointCover S.domain S.covers).parent x) :=
  fun _ hy => hy.2

/-- The common opens form a refinement of the first refined cover, through its chosen containing chart. -/
def left (R : Refinement U κ) (S : Refinement U τ) : Refinement R.domain B where
  parent := (pointCover R.domain R.covers).parent
  domain := commonDomain R S
  covers x := ⟨x, mem_commonDomain R S x⟩
  subset := commonDomain_subset_left R S

/-- The same common opens form a refinement of the second refined cover, through its chosen containing chart. -/
def right (R : Refinement U κ) (S : Refinement U τ) : Refinement S.domain B where
  parent := (pointCover S.domain S.covers).parent
  domain := commonDomain R S
  covers x := ⟨x, mem_commonDomain R S x⟩
  subset := commonDomain_subset_right R S

/-- Both routes to the common refinement use the identical family of open subsets of the base. -/
theorem common_domain_eq (R : Refinement U κ) (S : Refinement U τ) :
    (left R S).domain = (right R S).domain := rfl

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [ChartedSpace H B] {n : WithTop ℕ∞}

/-- Restriction along the point-indexed narrowing factors through the arbitrary original refinement. -/
theorem restrictClass_narrow (R : Refinement U κ) (c : ObstructionClass I U n) :
    restrictClass (pointCover R.domain R.covers) (restrictClass R c) =
      restrictClass (narrow R) c :=
  restrictClass_compose R (pointCover R.domain R.covers) c

/-- The two composite parent assignments on the common intersections induce the same restriction of every obstruction class. -/
theorem restrictClass_common_compose (R : Refinement U κ) (S : Refinement U τ)
    (c : ObstructionClass I U n) :
    restrictClass (compose R (left R S)) c = restrictClass (compose S (right R S)) c :=
  restrictClass_reparent (compose R (left R S)) (compose S (right R S)).parent
    (compose S (right R S)).subset c

/-- A class restricted along either refinement and then to the constructed common cover gives the same class there. -/
theorem restrictClass_common (R : Refinement U κ) (S : Refinement U τ)
    (c : ObstructionClass I U n) :
    restrictClass (left R S) (restrictClass R c) =
      restrictClass (right R S) (restrictClass S c) := by
  rw [restrictClass_compose, restrictClass_compose]
  exact restrictClass_common_compose R S c

end FoliationQM.SignCommonRefinement
