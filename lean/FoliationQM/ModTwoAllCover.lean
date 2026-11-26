module
public import FoliationQM.ModTwoRestriction
public import FoliationQM.SpinHOneDirected

/-!
# Locally constant mod-two degree-two cohomology over all covers

For the geometric Spin-frame component of v13 `prop:takabayasi`, this
additive group is a directed limit of the independently defined locally
constant mod-two cocycles. Its definition uses only the base topology.
Equality means equality on a further refinement; no injectivity of
fixed-cover degree-two maps is asserted. A comparison with Clifford
coefficients is a separate theorem, not part of this definition.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.ModTwoAllCover
open CliffordSpinCoverRefinement SpinHOneDirected SpinRefinementComposition
open ModTwoCohomology ModTwoRestriction

variable {B ι κ : Type*} [TopologicalSpace B]

/-- Restriction of mod-two classes along pointwise shrinking of neighborhoods. -/
def transition (P Q : Cover B) (h : P ≤ Q) : H2 P.domain →+ H2 Q.domain :=
  restrictHom (refine h)

instance : DirectedSystem (fun P : Cover B => H2 P.domain)
    (fun _ _ h => (transition _ _ h : _ → _)) where
  map_self P x := restrictHom_identity P.covers x
  map_map _ _ _ h k x := restrictHom_compose (refine h) (refine k) x

/-- The all-cover degree-two group of independent locally constant mod-two coefficients. -/
abbrev GlobalH2 (B : Type*) [TopologicalSpace B] :=
  DirectLimit (fun P : Cover B => H2 P.domain) transition

/-- Include a mod-two class on a point-indexed neighborhood cover in the direct limit. -/
def ofPoint (P : Cover B) : H2 P.domain →+ GlobalH2 B where
  toFun c := ⟦⟨P, c⟩⟧
  map_zero' := (DirectLimit.zero_def P).symm
  map_add' _ _ := (DirectLimit.add_def ..).symm

/-- Pointwise restriction preserves the global mod-two class. -/
theorem ofPoint_transition {P Q : Cover B} (h : P ≤ Q) (c : H2 P.domain) :
    ofPoint Q (transition P Q h c) = ofPoint P c :=
  DirectLimit.mk_apply (F := fun P : Cover B => H2 P.domain) (f := transition) P Q c h

/-- Every global mod-two class has a representative on one point-indexed cover. -/
theorem exists_representative (g : GlobalH2 B) :
    ∃ (P : Cover B) (c : H2 P.domain), g = ofPoint P c :=
  DirectLimit.exists_eq_mk transition g

/-- The canonical additive map from a cover whose indices may lie in any universe. -/
def ofCover (U : ι → TopologicalSpace.Opens B) (hU : ∀ x : B, ∃ i, x ∈ U i) :
    H2 U →+ GlobalH2 B :=
  (ofPoint (anchor U hU)).comp (restrictHom (SignCommonRefinement.pointCover U hU))

/-- Every containing-parent assignment on point neighborhoods computes the same global class. -/
theorem ofPoint_restrict {U : ι → TopologicalSpace.Opens B} (hU : ∀ x : B, ∃ i, x ∈ U i)
    (P : Cover B) (p : B → ι) (hp : ∀ x, P.domain x ≤ U (p x)) (c : H2 U) :
    ofPoint P (restrictHom (P.asRefinement p hp) c) = ofCover U hU c := by
  let A := anchor U hU
  let R := SignCommonRefinement.pointCover U hU
  let l := le_common_left P A
  let r := le_common_right P A
  change _ = ofPoint A (restrictHom R c)
  apply (ofPoint_transition l (restrictHom (P.asRefinement p hp) c)).symm.trans
  apply Eq.trans _ (ofPoint_transition r (restrictHom R c))
  apply congrArg (ofPoint (common P A))
  change restrictHom (refine l) (restrictHom (P.asRefinement p hp) c) =
    restrictHom (refine r) (restrictHom R c)
  apply (restrictHom_compose (P.asRefinement p hp) (refine l) c).trans
  apply Eq.trans _ (restrictHom_compose R (refine r) c).symm
  exact restrictHom_reparent (compose (P.asRefinement p hp) (refine l))
    (compose R (refine r)).parent (compose R (refine r)).subset c

/-- On a point-indexed cover the arbitrary-cover map is the original direct-limit inclusion. -/
theorem ofCover_point (P : Cover B) (c : H2 P.domain) :
    ofCover P.domain P.covers c = ofPoint P c := by
  have h := ofPoint_restrict P.covers P id (fun _ => le_rfl) c
  rw [show restrictHom (P.asRefinement id (fun _ => le_rfl)) c = c from
    restrictHom_identity P.covers c] at h
  exact h.symm

/-- Every indexed open refinement preserves its represented global mod-two class. -/
theorem ofCover_restrict {U : ι → TopologicalSpace.Opens B} (hU : ∀ x : B, ∃ i, x ∈ U i)
    (R : Refinement U κ) (c : H2 U) :
    ofCover R.domain R.covers (restrictHom R c) = ofCover U hU c := by
  let A := anchor R.domain R.covers
  let T := SignCommonRefinement.pointCover R.domain R.covers
  change ofPoint A (restrictHom T (restrictHom R c)) = _
  rw [restrictHom_compose]
  exact ofPoint_restrict hU A (compose R T).parent (compose R T).subset c

/-- Equality of two classes from one cover is exactly equality after a further open refinement. -/
theorem ofCover_eq_iff (U : ι → TopologicalSpace.Opens B) (hU : ∀ x : B, ∃ i, x ∈ U i)
    (c d : H2 U) : ofCover U hU c = ofCover U hU d ↔
      ∃ R : Refinement U B, restrictHom R c = restrictHom R d := by
  constructor
  · intro h
    obtain ⟨W, hc, hd, he⟩ := Quotient.exact h
    let R := SignCommonRefinement.pointCover U hU
    refine ⟨compose R (refine hc), ?_⟩
    exact (restrictHom_compose R (refine hc) c).symm.trans
      (he.trans (restrictHom_compose R (refine hd) d))
  · rintro ⟨R, hR⟩
    exact (ofCover_restrict hU R c).symm.trans
      ((congrArg (ofCover R.domain R.covers) hR).trans (ofCover_restrict hU R d))

/-- A global mod-two class is zero precisely when it becomes zero on some refinement. -/
theorem ofCover_eq_zero_iff (U : ι → TopologicalSpace.Opens B) (hU : ∀ x : B, ∃ i, x ∈ U i)
    (c : H2 U) : ofCover U hU c = 0 ↔ ∃ R : Refinement U B, restrictHom R c = 0 := by
  rw [← map_zero (ofCover U hU), ofCover_eq_iff]
  simp only [map_zero]

/-- Compatible additive maps on the neighborhood covers extend to global mod-two cohomology. -/
def descend {M : Type*} [AddMonoid M] (g : ∀ P : Cover B, H2 P.domain →+ M)
    (hg : ∀ P Q h c, g Q (transition P Q h c) = g P c) : GlobalH2 B →+ M where
  toFun := DirectLimit.lift _ (fun P c => g P c) (fun P Q h c => (hg P Q h c).symm)
  map_zero' := DirectLimit.lift_zero g _
  map_add' := DirectLimit.lift_add g _

/-- The extended homomorphism evaluates to the specified map on every cover representative. -/
theorem descend_ofPoint {M : Type*} [AddMonoid M] (g : ∀ P : Cover B, H2 P.domain →+ M)
    (hg : ∀ P Q h c, g Q (transition P Q h c) = g P c) (P : Cover B) (c : H2 P.domain) :
    descend g hg (ofPoint P c) = g P c := rfl

end FoliationQM.ModTwoAllCover
