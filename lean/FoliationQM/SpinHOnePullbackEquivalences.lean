module
public import FoliationQM.SpinHOneGlobalPullback
public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Reversible base changes and split pullback of global signs

For the geometric frame component of v13 `prop:takabayasi`, pulling
back along a diffeomorphism gives a multiplicative equivalence on
all-cover degree-one signs. A smooth section of a base map supplies a
left inverse on those sign classes.
-/

@[expose] public section
noncomputable section
open scoped Manifold
set_option backward.isDefEq.respectTransparency false
namespace FoliationQM.SpinHOnePullbackEquivalences
open SpinAllCoverHOne SpinHOneGlobalPullback

variable {X B EX EB HX HB : Type*}
  [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  [TopologicalSpace X] [ChartedSpace HX X] [TopologicalSpace B] [ChartedSpace HB B]
  {IX : ModelWithCorners ℝ EX HX} {IB : ModelWithCorners ℝ EB HB} {n : WithTop ℕ∞}

/-- A smooth diffeomorphism gives an equivalence of all-cover sign groups by actual pullback. -/
def diffeomorphEquiv (e : Diffeomorph IX IB X B n) : GlobalH1 IB B n ≃* GlobalH1 IX X n where
  toFun := pull (e.toHomeomorph : C(X, B)) e.contMDiff
  map_mul' := map_mul _
  invFun := pull (e.symm.toHomeomorph : C(B, X)) e.symm.contMDiff
  left_inv c := by
    rw [pull_comp]
    have he : (e.toHomeomorph : C(X, B)).comp (e.symm.toHomeomorph : C(B, X)) = .id B :=
      ContinuousMap.ext e.apply_symm_apply
    simpa only [he] using pull_id (IB := IB) c
  right_inv c := by
    rw [pull_comp]
    have he : (e.symm.toHomeomorph : C(B, X)).comp (e.toHomeomorph : C(X, B)) = .id X :=
      ContinuousMap.ext e.symm_apply_apply
    simpa only [he] using pull_id (IB := IX) c

/-- Pullback along a smooth section is a left inverse to pullback along its base map. -/
theorem section_leftInverse (f : C(X, B)) (hf : ContMDiff IX IB n f)
    (s : C(B, X)) (hs : ContMDiff IB IX n s) (hr : Function.RightInverse s f) :
    Function.LeftInverse (pull s hs) (pull f hf) := by
  intro c
  rw [pull_comp]
  have he : f.comp s = .id B := ContinuousMap.ext hr
  simpa only [he] using pull_id (IB := IB) c

/-- Consequently a smooth right inverse makes pullback injective on all degree-one classes. -/
theorem pull_injective (f : C(X, B)) (hf : ContMDiff IX IB n f)
    (s : C(B, X)) (hs : ContMDiff IB IX n s) (hr : Function.RightInverse s f) :
    Function.Injective (pull f hf) := (section_leftInverse f hf s hs hr).injective

end FoliationQM.SpinHOnePullbackEquivalences
