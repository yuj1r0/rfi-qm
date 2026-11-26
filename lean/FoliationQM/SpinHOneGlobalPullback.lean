module
public import FoliationQM.SpinHOnePullbackRefinement
public import FoliationQM.SpinHOneUniversal

/-!
# Smooth pullback on the all-cover group of physical signs

For the geometric frame component of v13 `prop:takabayasi`, preimages
of open covers and composition with a smooth base map define the pullback
on global degree-one sign classes. Refinement compatibility makes this
independent of the chosen representative cover.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace FoliationQM.SpinHOneGlobalPullback
open SpinAllCoverHOne SpinHOneUniversal SpinSignHOne

variable {X B Y ι EX EB EY HX HB HY : Type*}
  [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  [NormedAddCommGroup EY] [NormedSpace ℝ EY] [TopologicalSpace HY]
  [TopologicalSpace X] [ChartedSpace HX X] [TopologicalSpace B] [ChartedSpace HB B]
  [TopologicalSpace Y] [ChartedSpace HY Y]
  {IX : ModelWithCorners ℝ EX HX} {IB : ModelWithCorners ℝ EB HB} {IY : ModelWithCorners ℝ EY HY}
  {n : WithTop ℕ∞}

/-- Pull a fixed-cover class to its preimage cover and include the class over the new base. -/
def onCover (f : C(X, B)) (hf : ContMDiff IX IB n f) (U : ι → TopologicalSpace.Opens B) (hU : ∀ b : B, ∃ i, b ∈ U i) :
    H1 IB U n →* GlobalH1 IX X n :=
  (ofCover (ModTwoPullback.domain f U) (ModTwoPullback.covers f hU)).comp (SpinHOnePullback.hom f hf U)

/-- Restricting the chosen representative before pulling it back gives the same global class. -/
theorem onCover_restrict (f : C(X, B)) (hf : ContMDiff IX IB n f) (U : ι → TopologicalSpace.Opens B) (hU : ∀ b : B, ∃ i, b ∈ U i)
    {κ : Type*} (R : CliffordSpinCoverRefinement.Refinement U κ) (c : H1 IB U n) :
    onCover f hf R.domain R.covers (SpinHOneRestriction.restrictHom R c) = onCover f hf U hU c := by
  unfold onCover
  simp only [MonoidHom.comp_apply, SpinHOnePullbackRefinement.hom_restrict]
  exact ofCover_restrict (ModTwoPullback.covers f hU) (ModTwoPullbackRefinement.refinement f R) _

/-- Smooth maps act contravariantly on the native all-cover degree-one group. -/
def pull (f : C(X, B)) (hf : ContMDiff IX IB n f) : GlobalH1 IB B n →* GlobalH1 IX X n :=
  descend (fun P => onCover f hf P.domain P.covers)
    (fun P _ h c => onCover_restrict f hf P.domain P.covers (SpinHOneDirected.refine h) c)

/-- Evaluation on a point-indexed neighborhood cover. -/
theorem pull_ofPoint (f : C(X, B)) (hf : ContMDiff IX IB n f) (P : SpinHOneDirected.Cover B) (c : H1 IB P.domain n) :
    pull f hf (ofPoint P c) = onCover f hf P.domain P.covers c := rfl

/-- Evaluation on representatives indexed in any universe uses the actual preimage domains. -/
theorem pull_ofCover (f : C(X, B)) (hf : ContMDiff IX IB n f) (U : ι → TopologicalSpace.Opens B) (hU : ∀ b : B, ∃ i, b ∈ U i)
    (c : H1 IB U n) : pull f hf (ofCover U hU c) =
    ofCover (ModTwoPullback.domain f U) (ModTwoPullback.covers f hU) (SpinHOnePullback.hom f hf U c) :=
  onCover_restrict f hf U hU (SignCommonRefinement.pointCover U hU) c

/-- Pullback along the identity fixes every all-cover class. -/
theorem pull_id (c : GlobalH1 IB B n) : pull (.id B) contMDiff_id c = c := by
  obtain ⟨P, z, rfl⟩ := exists_representative c
  rw [← ofCover_point P, pull_ofCover, SpinHOnePullback.hom_id]
  rfl

/-- The pullback of a composite is the successive pullback in reverse order. -/
theorem pull_comp (f : C(X, B)) (hf : ContMDiff IX IB n f) (g : C(Y, X)) (hg : ContMDiff IY IX n g) (c : GlobalH1 IB B n) :
    pull g hg (pull f hf c) = pull (f.comp g) (hf.comp hg) c := by
  obtain ⟨P, z, rfl⟩ := exists_representative c
  rw [← ofCover_point P, pull_ofCover, pull_ofCover, pull_ofCover, SpinHOnePullback.hom_comp]
  rfl

end FoliationQM.SpinHOneGlobalPullback
