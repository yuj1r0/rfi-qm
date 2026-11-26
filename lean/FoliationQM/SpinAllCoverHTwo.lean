module
public import FoliationQM.SpinHTwoDirected

/-!
# The all-cover degree-two group of smooth Clifford signs

For the Spin-frame component of v13 `prop:takabayasi`, the direct limit
identifies two fixed-cover obstruction classes exactly when some further
refinement identifies them. The induced maps from all open covers
therefore extend the previously defined eventual obstruction relation.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.SpinAllCoverHTwo
open CliffordSpinCoverRefinement SpinSignCohomology SpinSignHTwo SignClassRestriction
open SpinHOneDirected SpinRefinementComposition SignEventualObstruction

variable {E H B ι κ τ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace B] [ChartedSpace H B] {n : WithTop ℕ∞}

/-- Degree-two smooth sign cohomology of the base, formed from all point-indexed neighborhoods. -/
abbrev GlobalH2 (I : ModelWithCorners ℝ E H) (B : Type*) [TopologicalSpace B] [ChartedSpace H B]
    (n : WithTop ℕ∞) := DirectLimit (fun P : Cover B => ObstructionClass I P.domain n)
      (SpinHTwoDirected.transition I n)

/-- The canonical homomorphism from a single point-indexed degree-two group. -/
def ofPoint (P : Cover B) : ObstructionClass I P.domain n →* GlobalH2 I B n where
  toFun c := ⟦⟨P, c⟩⟧
  map_one' := (DirectLimit.one_def P).symm
  map_mul' _ _ := (DirectLimit.mul_def ..).symm

/-- The global class is preserved by every pointwise shrinking. -/
theorem ofPoint_transition {P Q : Cover B} (h : P ≤ Q) (c : ObstructionClass I P.domain n) :
    ofPoint Q (SpinHTwoDirected.transition I n P Q h c) = ofPoint P c :=
  DirectLimit.mk_apply (F := fun P : Cover B => ObstructionClass I P.domain n)
    (f := SpinHTwoDirected.transition I n) P Q c h

/-- Every global degree-two class has a representative on one family of point neighborhoods. -/
theorem exists_representative (g : GlobalH2 I B n) :
    ∃ (P : Cover B) (c : ObstructionClass I P.domain n), g = ofPoint P c :=
  DirectLimit.exists_eq_mk (SpinHTwoDirected.transition I n) g

/-- The canonical group homomorphism from a cover with indices in any universe. -/
def ofCover (U : ι → TopologicalSpace.Opens B) (hU : ∀ x : B, ∃ i, x ∈ U i) :
    ObstructionClass I U n →* GlobalH2 I B n :=
  (ofPoint (anchor U hU)).comp (restrictHom (SignCommonRefinement.pointCover U hU))

/-- Every containing-parent assignment to an anchored refinement computes the same global class. -/
theorem ofPoint_restrict {U : ι → TopologicalSpace.Opens B} (hU : ∀ x : B, ∃ i, x ∈ U i)
    (P : Cover B) (p : B → ι) (hp : ∀ x, P.domain x ≤ U (p x)) (c : ObstructionClass I U n) :
    ofPoint P (restrictClass (P.asRefinement p hp) c) = ofCover U hU c := by
  let A := anchor U hU
  let R := SignCommonRefinement.pointCover U hU
  let l := le_common_left P A
  let r := le_common_right P A
  change _ = ofPoint A (restrictClass R c)
  apply (ofPoint_transition l (restrictClass (P.asRefinement p hp) c)).symm.trans
  apply Eq.trans _ (ofPoint_transition r (restrictClass R c))
  apply congrArg (ofPoint (common P A))
  change restrictClass (refine l) (restrictClass (P.asRefinement p hp) c) =
    restrictClass (refine r) (restrictClass R c)
  apply (restrictClass_compose (P.asRefinement p hp) (refine l) c).trans
  apply Eq.trans _ (restrictClass_compose R (refine r) c).symm
  exact SignRefinementPrism.restrictClass_reparent (compose (P.asRefinement p hp) (refine l))
    (compose R (refine r)).parent (compose R (refine r)).subset c

/-- On an anchored cover the arbitrary-cover homomorphism is its direct-limit component map. -/
theorem ofCover_point (P : Cover B) (c : ObstructionClass I P.domain n) :
    ofCover P.domain P.covers c = ofPoint P c := by
  have h := ofPoint_restrict P.covers P id (fun _ => le_rfl) c
  rw [show restrictClass (P.asRefinement id (fun _ => le_rfl)) c = c from
    restrictClass_identity P.covers c] at h
  exact h.symm

/-- Restricting a representative along any open refinement preserves its global degree-two class. -/
theorem ofCover_restrict {U : ι → TopologicalSpace.Opens B} (hU : ∀ x : B, ∃ i, x ∈ U i)
    (R : Refinement U κ) (c : ObstructionClass I U n) :
    ofCover R.domain R.covers (restrictClass R c) = ofCover U hU c := by
  let A := anchor R.domain R.covers
  let T := SignCommonRefinement.pointCover R.domain R.covers
  change ofPoint A (restrictClass T (restrictClass R c)) = _
  rw [restrictClass_compose]
  exact ofPoint_restrict hU A (compose R T).parent (compose R T).subset c

/-- Equality of two classes from one cover in global degree two is exactly equality after some further refinement. -/
theorem ofCover_eq_iff_eventuallyEqual (U : ι → TopologicalSpace.Opens B)
    (hU : ∀ x : B, ∃ i, x ∈ U i) (c d : ObstructionClass I U n) :
    ofCover U hU c = ofCover U hU d ↔ EventuallyEqual c d := by
  constructor
  · intro h
    obtain ⟨W, hc, hd, he⟩ := Quotient.exact h
    let R := SignCommonRefinement.pointCover U hU
    refine ⟨compose R (refine hc), ?_⟩
    exact (restrictClass_compose R (refine hc) c).symm.trans
      (he.trans (restrictClass_compose R (refine hd) d))
  · rintro ⟨R, hR⟩
    exact (ofCover_restrict hU R c).symm.trans
      ((congrArg (ofCover R.domain R.covers) hR).trans (ofCover_restrict hU R d))

/-- A presented degree-two class is globally neutral precisely when its old eventual obstruction vanishes. -/
theorem ofCover_eq_one_iff (U : ι → TopologicalSpace.Opens B) (hU : ∀ x : B, ∃ i, x ∈ U i)
    (c : ObstructionClass I U n) : ofCover U hU c = 1 ↔ Vanishes c := by
  rw [← map_one (ofCover (I := I) (n := n) U hU)]
  exact ofCover_eq_iff_eventuallyEqual U hU c (neutralClass I U n)

/-- On any specified common refinement, equality of global classes is equivalent to eventual equality of their restrictions. -/
theorem ofCover_eq_iff_common {U : ι → TopologicalSpace.Opens B} {V : κ → TopologicalSpace.Opens B}
    (hU : ∀ x : B, ∃ i, x ∈ U i) (hV : ∀ x : B, ∃ j, x ∈ V j)
    (W : τ → TopologicalSpace.Opens B) (hW : ∀ x : B, ∃ a, x ∈ W a)
    (p : τ → ι) (q : τ → κ) (hp : ∀ a, W a ≤ U (p a)) (hq : ∀ a, W a ≤ V (q a))
    (c : ObstructionClass I U n) (d : ObstructionClass I V n) :
    ofCover U hU c = ofCover V hV d ↔
      EventuallyEqual (restrictClass (⟨p, W, hW, hp⟩ : Refinement U τ) c)
        (restrictClass (⟨q, W, hW, hq⟩ : Refinement V τ) d) := by
  let R : Refinement U τ := ⟨p, W, hW, hp⟩
  let S : Refinement V τ := ⟨q, W, hW, hq⟩
  rw [← ofCover_restrict hU R c, ← ofCover_restrict hV S d]
  exact ofCover_eq_iff_eventuallyEqual W hW _ _

/-- Stable classes already represented on one cover embed in all-cover degree-two cohomology. -/
def stableEmbedding (U : ι → TopologicalSpace.Opens B) (hU : ∀ x : B, ∃ i, x ∈ U i) :
    StableClass I U n hU ↪ GlobalH2 I B n where
  toFun := Quotient.lift (ofCover U hU) (fun _ _ h => (ofCover_eq_iff_eventuallyEqual U hU _ _).mpr h)
  inj' := by
    intro c d
    refine Quotient.inductionOn₂ c d ?_
    intro c d h
    exact Quotient.sound ((ofCover_eq_iff_eventuallyEqual U hU c d).mp h)

/-- The stable embedding sends a fixed-cover representative to its canonical global image. -/
theorem stableEmbedding_stableClass (U : ι → TopologicalSpace.Opens B)
    (hU : ∀ x : B, ∃ i, x ∈ U i) (c : ObstructionClass I U n) :
    stableEmbedding U hU (stableClass hU c) = ofCover U hU c := rfl

/-- Restriction of the old stable classes commutes with their embeddings in global degree two. -/
theorem stableEmbedding_restrict (U : ι → TopologicalSpace.Opens B)
    (hU : ∀ x : B, ∃ i, x ∈ U i) (R : Refinement U κ) (s : StableClass I U n hU) :
    stableEmbedding R.domain R.covers (stableRestrict hU R s) = stableEmbedding U hU s :=
  Quotient.inductionOn s (fun c => ofCover_restrict hU R c)

end FoliationQM.SpinAllCoverHTwo
