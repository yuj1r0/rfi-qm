module
public import FoliationQM.ModTwoPullback
public import FoliationQM.ModTwoRestriction

/-!
# Pullback and refinement of the mod-two Čech classes

For the geometric frame component of v13 `prop:takabayasi`, a continuous
map pulls an open refinement back by taking inverse images of its domains.
Its retained parent map selects the same coefficients and mixed-parent
prism. The resulting square of fixed-cover cohomology homomorphisms commutes.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.ModTwoPullbackRefinement
open ModTwoCohomology ModTwoPullback ModTwoRestriction CliffordSpinCoverRefinement

variable {B X Y ι κ τ : Type*} [TopologicalSpace B] [TopologicalSpace X]
  [TopologicalSpace Y] {U : ι → TopologicalSpace.Opens B}

/-- Pull a cover refinement back to the source of a continuous map. -/
def refinement (f : C(X, B)) (R : Refinement U κ) : Refinement (domain f U) κ where
  parent := R.parent
  domain := domain f R.domain
  covers := covers f R.covers
  subset a _ hx := R.subset a hx

/-- The pulled-back refinement retains the original parent assignment. -/
theorem refinement_parent (f : C(X, B)) (R : Refinement U κ) :
    (refinement f R).parent = R.parent := rfl

/-- Its chart domains are exactly the preimages of the original refined opens. -/
theorem refinement_domain (f : C(X, B)) (R : Refinement U κ) :
    (refinement f R).domain = domain f R.domain := rfl

/-- The identity cover refinement pulls back to the identity of the preimage cover. -/
theorem refinement_identity (f : C(X, B)) (hU : ∀ x : B, ∃ i, x ∈ U i) :
    refinement f (SpinRefinementComposition.identity U hU) =
      SpinRefinementComposition.identity (domain f U) (covers f hU) := rfl

/-- Pulling back a composite of refinements gives the composite of the pulled-back refinements. -/
theorem refinement_compose (f : C(X, B)) (R : Refinement U κ) (S : Refinement R.domain τ) :
    refinement f (SpinRefinementComposition.compose R S) =
      SpinRefinementComposition.compose (refinement f R) (refinement f S) := rfl

/-- Pulling a refinement back along the identity base map retains the original refinement. -/
theorem refinement_idMap (R : Refinement U κ) : refinement (ContinuousMap.id B) R = R := rfl

/-- Successive pullbacks of a refinement agree with pullback along the composite base map. -/
theorem refinement_compMap (f : C(X, B)) (g : C(Y, X)) (R : Refinement U κ) :
    refinement g (refinement f R) = refinement (f.comp g) R := rfl

/-- An alternative parent remains a containing parent on the preimage of its original domain. -/
theorem refinement_reparent (f : C(X, B)) (R : Refinement U κ)
    (q : κ → ι) (hq : ∀ a, (R.domain a : Set B) ⊆ U (q a)) :
    refinement f (reparent R q hq) =
      reparent (refinement f R) q (fun a _ hx => hq a hx) := rfl

/-- Pullback and restriction agree on the entire normalized pair cochain. -/
theorem one_restrict (f : C(X, B)) (R : Refinement U κ) (b : OneCochain U) :
    one f (restrictOne R b) = restrictOne (refinement f R) (one f b) := rfl

/-- Pullback and restriction agree on the entire normalized triple cocycle. -/
theorem two_restrict (f : C(X, B)) (R : Refinement U κ) (z : TwoCocycle U) :
    two f (restrictTwo R z) = restrictTwo (refinement f R) (two f z) := rfl

/-- The mixed-parent correction cochain pulls back to the prism for the preimage refinement. -/
theorem one_prism (f : C(X, B)) (R : Refinement U κ) (q : κ → ι)
    (hq : ∀ a, (R.domain a : Set B) ⊆ U (q a)) (z : TwoCocycle U) :
    one f (prism R q hq z) =
      prism (refinement f R) q (fun a _ hx => hq a hx) (two f z) := rfl

/-- Restricting a cohomology class and pulling back commute for arbitrary cover indices. -/
theorem hom_restrict (f : C(X, B)) (R : Refinement U κ) (c : H2 U) :
    hom f R.domain (restrictHom R c) = restrictHom (refinement f R) (hom f U c) := by
  obtain ⟨z, rfl⟩ := classOf_surjective c
  exact congrArg classOf (two_restrict f R z)

/-- The naturality square is an equality of the full additive homomorphisms. -/
theorem hom_square (f : C(X, B)) (R : Refinement U κ) :
    (hom f R.domain).comp (restrictHom R) = (restrictHom (refinement f R)).comp (hom f U) :=
  AddMonoidHom.ext (hom_restrict f R)

end FoliationQM.ModTwoPullbackRefinement
