module
public import FoliationQM.SpinHOneDirected

/-!
# The all-cover group of smooth Clifford signs

For the Spin-frame component of v13 `prop:takabayasi`, take the direct
limit over the point-indexed neighborhoods. Sending every open cover
into this group is independent of the chosen containing charts and
commutes with arbitrary refinements. Equality can be tested on any
single specified common open refinement.
-/

@[expose] public section
noncomputable section
open Set
namespace FoliationQM.SpinAllCoverHOne
open CliffordSpinCoverRefinement SpinHOneRestriction SpinHOneDirected SpinSignHOne
open SpinRefinementComposition

variable {E H B ι κ τ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace B] [ChartedSpace H B] {n : WithTop ℕ∞}

/-- Degree-one smooth sign cohomology of the base, as a direct limit over neighborhoods. -/
abbrev GlobalH1 (I : ModelWithCorners ℝ E H) (B : Type*) [TopologicalSpace B] [ChartedSpace H B]
    (n : WithTop ℕ∞) := DirectLimit (fun P : Cover B => H1 I P.domain n) (transition I n)

/-- The canonical group homomorphism from any point-indexed family. -/
def ofPoint (P : Cover B) : H1 I P.domain n →* GlobalH1 I B n where
  toFun c := ⟦⟨P, c⟩⟧
  map_one' := (DirectLimit.one_def P).symm
  map_mul' _ _ := (DirectLimit.mul_def ..).symm

/-- Representatives related by an identity-parent shrinking give the same global class. -/
theorem ofPoint_transition {P Q : Cover B} (h : P ≤ Q) (c : H1 I P.domain n) :
    ofPoint Q (transition I n P Q h c) = ofPoint P c :=
  DirectLimit.mk_apply (F := fun P : Cover B => H1 I P.domain n) (f := transition I n) P Q c h

/-- The direct limit retains all information in each point-indexed group. -/
theorem ofPoint_injective (P : Cover B) : Function.Injective (ofPoint (I := I) (n := n) P) :=
  DirectLimit.mk_injective (transition I n) (fun _ _ h => transition_injective h) P

/-- Every global class is represented by a sign class on a single point-indexed cover. -/
theorem exists_representative (g : GlobalH1 I B n) :
    ∃ (P : Cover B) (c : H1 I P.domain n), g = ofPoint P c :=
  DirectLimit.exists_eq_mk (transition I n) g

/-- Include the first sign cohomology of an arbitrarily indexed open cover in global cohomology. -/
def ofCover (U : ι → TopologicalSpace.Opens B) (hU : ∀ x : B, ∃ i, x ∈ U i) :
    H1 I U n →* GlobalH1 I B n :=
  (ofPoint (anchor U hU)).comp (restrictHom (SignCommonRefinement.pointCover U hU))

/-- Every assignment of parents to an anchored refinement computes the same global class. -/
theorem ofPoint_restrict {U : ι → TopologicalSpace.Opens B} (hU : ∀ x : B, ∃ i, x ∈ U i)
    (P : Cover B) (p : B → ι) (hp : ∀ x, P.domain x ≤ U (p x)) (c : H1 I U n) :
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

/-- Applying the arbitrary-cover inclusion to point-indexed neighborhoods recovers their direct-limit map. -/
theorem ofCover_point (P : Cover B) (c : H1 I P.domain n) :
    ofCover P.domain P.covers c = ofPoint P c := by
  have h := ofPoint_restrict P.covers P id (fun _ => le_rfl) c
  rw [show restrictHom (P.asRefinement id (fun _ => le_rfl)) c = c from
    restrictHom_identity P.covers c] at h
  exact h.symm

/-- Restricting along any open refinement preserves the image in global cohomology. -/
theorem ofCover_restrict {U : ι → TopologicalSpace.Opens B} (hU : ∀ x : B, ∃ i, x ∈ U i)
    (R : Refinement U κ) (c : H1 I U n) :
    ofCover R.domain R.covers (restrictHom R c) = ofCover U hU c := by
  let A := anchor R.domain R.covers
  let T := SignCommonRefinement.pointCover R.domain R.covers
  change ofPoint A (restrictHom T (restrictHom R c)) = _
  rw [restrictHom_compose]
  exact ofPoint_restrict hU A (compose R T).parent (compose R T).subset c

/-- The canonical homomorphism embeds every fixed-cover group. -/
theorem ofCover_injective (U : ι → TopologicalSpace.Opens B)
    (hU : ∀ x : B, ∃ i, x ∈ U i) : Function.Injective (ofCover (I := I) (n := n) U hU) :=
  (ofPoint_injective _).comp (SpinHOneDescent.restrictHom_injective _)

/-- Global neutrality is already detected on the presenting open cover. -/
theorem ofCover_eq_one_iff (U : ι → TopologicalSpace.Opens B) (hU : ∀ x : B, ∃ i, x ∈ U i)
    (c : H1 I U n) : ofCover U hU c = 1 ↔ c = 1 := by
  rw [← map_one (ofCover (I := I) (n := n) U hU), (ofCover_injective U hU).eq_iff]

/-- Two classes are equal globally exactly when they agree on the given common refinement,
with independent choices of parents and any universe of refined indices. -/
theorem ofCover_eq_iff_common {U : ι → TopologicalSpace.Opens B} {V : κ → TopologicalSpace.Opens B}
    (hU : ∀ x : B, ∃ i, x ∈ U i) (hV : ∀ x : B, ∃ j, x ∈ V j)
    (W : τ → TopologicalSpace.Opens B) (hW : ∀ x : B, ∃ a, x ∈ W a)
    (p : τ → ι) (q : τ → κ) (hp : ∀ a, W a ≤ U (p a)) (hq : ∀ a, W a ≤ V (q a))
    (c : H1 I U n) (d : H1 I V n) :
    ofCover U hU c = ofCover V hV d ↔
      restrictHom (⟨p, W, hW, hp⟩ : Refinement U τ) c =
        restrictHom (⟨q, W, hW, hq⟩ : Refinement V τ) d := by
  let R : Refinement U τ := ⟨p, W, hW, hp⟩
  let S : Refinement V τ := ⟨q, W, hW, hq⟩
  rw [← ofCover_restrict hU R c, ← ofCover_restrict hV S d]
  exact (ofCover_injective W hW).eq_iff

end FoliationQM.SpinAllCoverHOne
