module
public import FoliationQM.ModTwoPullbackRefinement
public import FoliationQM.ModTwoAllCover

/-!
# Continuous pullback on all-cover mod-two cohomology

For the geometric frame component of v13 `prop:takabayasi`, preimages of
open covers and composition of locally constant coefficients give a
contravariant additive map. Its value on every indexed representative
is the class of the pulled cocycle on that cover's actual preimage.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.ModTwoGlobalPullback
open ModTwoAllCover ModTwoCohomology

variable {X B Y ι : Type*} [TopologicalSpace X] [TopologicalSpace B] [TopologicalSpace Y]

/-- Pull a fixed-cover class to its preimage cover and include the class over the new base. -/
def onCover (f : C(X, B)) (U : ι → TopologicalSpace.Opens B) (hU : ∀ b : B, ∃ i, b ∈ U i) :
    H2 U →+ GlobalH2 X :=
  (ofCover (ModTwoPullback.domain f U) (ModTwoPullback.covers f hU)).comp (ModTwoPullback.hom f U)

/-- Restricting the chosen representative before pulling it back gives the same global class. -/
theorem onCover_restrict (f : C(X, B)) (U : ι → TopologicalSpace.Opens B) (hU : ∀ b : B, ∃ i, b ∈ U i)
    {κ : Type*} (R : CliffordSpinCoverRefinement.Refinement U κ) (c : H2 U) :
    onCover f R.domain R.covers (ModTwoRestriction.restrictHom R c) = onCover f U hU c := by
  unfold onCover
  simp only [AddMonoidHom.comp_apply, ModTwoPullbackRefinement.hom_restrict]
  exact ofCover_restrict (ModTwoPullback.covers f hU) (ModTwoPullbackRefinement.refinement f R) _

/-- Continuous maps act contravariantly on the native all-cover degree-two group. -/
def pull (f : C(X, B)) : GlobalH2 B →+ GlobalH2 X :=
  descend (fun P => onCover f P.domain P.covers)
    (fun P _ h c => onCover_restrict f P.domain P.covers (SpinHOneDirected.refine h) c)

/-- Evaluation on a point-indexed neighborhood cover. -/
theorem pull_ofPoint (f : C(X, B)) (P : SpinHOneDirected.Cover B) (c : H2 P.domain) :
    pull f (ofPoint P c) = onCover f P.domain P.covers c := rfl

/-- Evaluation on representatives indexed in any universe uses the actual preimage domains. -/
theorem pull_ofCover (f : C(X, B)) (U : ι → TopologicalSpace.Opens B) (hU : ∀ b : B, ∃ i, b ∈ U i)
    (c : H2 U) : pull f (ofCover U hU c) =
    ofCover (ModTwoPullback.domain f U) (ModTwoPullback.covers f hU) (ModTwoPullback.hom f U c) :=
  onCover_restrict f U hU (SignCommonRefinement.pointCover U hU) c

/-- Pullback along the identity fixes every all-cover class. -/
theorem pull_id (c : GlobalH2 B) : pull (.id B) c = c := by
  obtain ⟨P, z, rfl⟩ := exists_representative c
  rw [← ofCover_point P, pull_ofCover, ModTwoPullback.hom_id]
  rfl

/-- The pullback of a composite is the successive pullback in reverse order. -/
theorem pull_comp (f : C(X, B)) (g : C(Y, X)) (c : GlobalH2 B) :
    pull g (pull f c) = pull (f.comp g) c := by
  obtain ⟨P, z, rfl⟩ := exists_representative c
  rw [← ofCover_point P, pull_ofCover, pull_ofCover, pull_ofCover, ModTwoPullback.hom_comp]
  rfl

/-- A homeomorphism induces an additive equivalence on the all-cover groups. -/
def homeomorphEquiv (e : X ≃ₜ B) : GlobalH2 B ≃+ GlobalH2 X where
  toFun := pull (e : C(X, B))
  map_add' := map_add _
  invFun := pull (e.symm : C(B, X))
  left_inv c := by
    rw [pull_comp, show (e : C(X, B)).comp (e.symm : C(B, X)) = .id B by ext b; exact e.apply_symm_apply b, pull_id]
  right_inv c := by
    rw [pull_comp, show (e.symm : C(B, X)).comp (e : C(X, B)) = .id X by ext x; exact e.symm_apply_apply x, pull_id]

/-- In particular, changing the base by a homeomorphism detects vanishing in both directions. -/
theorem homeomorph_zero_iff (e : X ≃ₜ B) (c : GlobalH2 B) : pull (e : C(X, B)) c = 0 ↔ c = 0 :=
  (homeomorphEquiv e).map_eq_zero_iff

end FoliationQM.ModTwoGlobalPullback
