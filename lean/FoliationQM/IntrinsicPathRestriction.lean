module
public import FoliationQM.IntrinsicPathCocycle
public import FoliationQM.ModTwoRestriction

/-!
# Restricting the independent path obstruction to an open refinement

For the geometric component of v13 `prop:takabayasi`, continuous
transition data and their actual joint path families restrict to every
open refinement. The native path-kernel coefficient on a true refined
triple is the original parent coefficient. Consequently its locally
constant mod-two cohomology class is the actual restriction homomorphism.
Neither physical Spin lifts nor a characteristic-class comparison enter
this argument.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.IntrinsicPathRestriction
open PathTransitionData BasedPathGroup CliffordSpinCoverRefinement

variable {G B ι κ : Type*} [TopologicalSpace G] [Group G]
  [TopologicalSpace B]

/-- Restrict the actual continuous transition functions to their designated parent charts. -/
def data (D : Data G B ι) (R : Refinement D.domain κ) : Data G B κ where
  domain := R.domain
  covers := R.covers
  transition a b := D.transition (R.parent a) (R.parent b)
  continuous_transition a b := (D.continuous_transition _ _).mono
    (fun _ h => ⟨R.subset a h.1, R.subset b h.2⟩)
  identity a x ha := D.identity (R.parent a) x (R.subset a ha)
  comp a b c x ha hb hc := D.comp _ _ _ x
    (R.subset a ha) (R.subset b hb) (R.subset c hc)

variable {D : Data G B ι}

/-- The refined transition data have precisely the supplied new open domains. -/
theorem data_domain (R : Refinement D.domain κ) : (data D R).domain = R.domain := rfl

/-- The new transitions are exactly the original parent transitions. -/
theorem data_transition (R : Refinement D.domain κ) (a b : κ) (x : B) :
    (data D R).transition a b x = D.transition (R.parent a) (R.parent b) x := rfl

/-- Inclusion of a refined pair overlap into its original pair overlap is continuous. -/
def pairMap (R : Refinement D.domain κ) (a b : κ) :
    C(↥(pairOverlap (data D R) a b), ↥(pairOverlap D (R.parent a) (R.parent b))) :=
  ⟨fun x => ⟨x.val, R.subset a x.property.1, R.subset b x.property.2⟩,
    continuous_subtype_val.subtype_mk _⟩

/-- Restrict the jointly continuous paths by the actual overlap inclusion. -/
def family (P : Family D) (R : Refinement D.domain κ) : Family (data D R) where
  homotopy a b := (P.homotopy (R.parent a) (R.parent b)).comp
    ⟨fun z => (z.1, pairMap R a b z.2),
      continuous_fst.prodMk ((pairMap R a b).continuous.comp continuous_snd)⟩
  source a b x := P.source _ _ (pairMap R a b x)
  target a b x := P.target _ _ (pairMap R a b x)
  diagonal a t x := P.diagonal _ t (pairMap R a a x)

/-- The entire refined path family is the original joint map on parent overlaps. -/
theorem family_apply (P : Family D) (R : Refinement D.domain κ)
    (a b : κ) (t : unitInterval) (x : pairOverlap (data D R) a b) :
    (family P R).homotopy a b (t, x) =
      P.homotopy (R.parent a) (R.parent b) (t, pairMap R a b x) := rfl

variable [IsTopologicalGroup G]

/-- Restriction preserves the actual continuous based path at every point of the refined overlap. -/
theorem family_basedPath (P : Family D) (R : Refinement D.domain κ)
    (a b : κ) (x : B) (ha : x ∈ R.domain a) (hb : x ∈ R.domain b) :
    basedPath (family P R) a b x ha hb =
      basedPath P (R.parent a) (R.parent b) x (R.subset a ha) (R.subset b hb) := rfl

/-- Restriction also preserves the intrinsic path class, without choosing any external lift. -/
theorem family_lift (P : Family D) (R : Refinement D.domain κ)
    (a b : κ) (x : B) (ha : x ∈ R.domain a) (hb : x ∈ R.domain b) :
    lift (family P R) a b x ha hb =
      lift P (R.parent a) (R.parent b) x (R.subset a ha) (R.subset b hb) := rfl

/-- The intrinsic triple kernel element on a refined overlap is the original parent defect. -/
theorem family_defect (P : Family D) (R : Refinement D.domain κ)
    (a b c : κ) (x : B) (ha : x ∈ R.domain a) (hb : x ∈ R.domain b)
    (hc : x ∈ R.domain c) :
    IntrinsicPathCocycle.defect (family P R) a b c x ha hb hc =
      IntrinsicPathCocycle.defect P (R.parent a) (R.parent b) (R.parent c) x
        (R.subset a ha) (R.subset b hb) (R.subset c hc) := rfl

/-- Every intrinsic mod-two coefficient is unchanged on the actual refined triple. -/
theorem family_coefficient (e : (projection (G := G)).ker →* Multiplicative (ZMod 2))
    (P : Family D) (R : Refinement D.domain κ)
    (a b c : κ) (x : B) (ha : x ∈ R.domain a) (hb : x ∈ R.domain b)
    (hc : x ∈ R.domain c) :
    IntrinsicPathCocycle.coefficient e (family P R) a b c x ha hb hc =
      IntrinsicPathCocycle.coefficient e P (R.parent a) (R.parent b) (R.parent c) x
        (R.subset a ha) (R.subset b hb) (R.subset c hc) := rfl

variable [LocallyPathConnectedSpace B]

/-- The independently constructed Cech class restricts by the native mod-two restriction homomorphism. -/
theorem class_restrict (e : (projection (G := G)).ker →* Multiplicative (ZMod 2))
    (P : Family D) (R : Refinement D.domain κ) :
    ModTwoCohomology.classOf (IntrinsicPathCocycle.cocycle e (family P R)) =
      ModTwoRestriction.restrictHom R (ModTwoCohomology.classOf (IntrinsicPathCocycle.cocycle e P)) := by
  rw [ModTwoRestriction.restrictHom_classOf]
  apply ModTwoCohomology.classOf_eq_of_eqOn
  intro a b c x ha hb hc
  rw [ModTwoRestriction.restrictTwo_value, IntrinsicPathCocycle.cocycle_value e (family P R) a b c x ha hb hc,
    IntrinsicPathCocycle.cocycle_value e P _ _ _ x (R.subset a ha) (R.subset b hb) (R.subset c hc)]
  exact family_coefficient e P R a b c x ha hb hc

end FoliationQM.IntrinsicPathRestriction
