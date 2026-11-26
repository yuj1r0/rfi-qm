module
public import FoliationQM.SpinHOneGlobalPullback

/-!
# Locally constant base maps kill global degree-one Spin signs

For the frame component of v13 `prop:takabayasi`, choose a containing
chart at each image point of a locally constant base map. The original
transition sign from this chart to any other chart through the image
point is a locally constant chart gauge on the new base. Its coboundary
is the pulled cocycle on every true pair overlap.
-/

@[expose] public section
noncomputable section
open scoped Manifold
namespace FoliationQM.SpinHOneLocallyConstantPullback
open CliffordSpinLorentzSmooth SpinSignOneCocycle SpinSignHOne SpinAllCoverHOne SpinHOneGlobalPullback

variable {B X ι EX EB HX HB : Type*}
  [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  [TopologicalSpace X] [ChartedSpace HX X] [TopologicalSpace B] [ChartedSpace HB B]
  {IX : ModelWithCorners ℝ EX HX} {IB : ModelWithCorners ℝ EB HB} {n : WithTop ℕ∞}

/-- A locally constant map between charted spaces agrees locally with a constant at every point
and is smooth at every specified order. -/
theorem contMDiff_of_isLocallyConstant {g : X → B} (h : IsLocallyConstant g) : ContMDiff IX IB n g :=
  fun x => (contMDiffAt_const (c := g x)).congr_of_eventuallyEq (h.eventually_eq x)

variable {U : ι → TopologicalSpace.Opens B}
  (f : C(X, B)) (hf : ContMDiff IX IB n f) (hloc : IsLocallyConstant (f : X → B))

/-- Choose the sign of the transition from a containing chart at the image point to chart i.
The whole coefficient is locally constant on the new base. -/
def chartGauge (hU : ∀ b, ∃ i, b ∈ U i) (z : Cocycle IB U n) :
    ZeroCochain IX (ModTwoPullback.domain f U) n where
  value i x := z.val.value (hU (f x)).choose i (f x)
  smooth_value i := (contMDiff_of_isLocallyConstant
    (hloc.comp (fun b => (z.val.value (hU b).choose i b).val))).contMDiffOn

/-- The chart-gauge coefficient is the literal original Clifford sign at the image point. -/
theorem chartGauge_value (hU : ∀ b, ∃ i, b ∈ U i) (z : Cocycle IB U n) (i : ι) (x : X) :
    (chartGauge (IX := IX) f hloc hU z).value i x = z.val.value (hU (f x)).choose i (f x) := rfl

/-- The triple law through the chosen chart identifies the pulled pair signs with the chartwise coboundary. -/
theorem cocycle_coboundary (hU : ∀ b, ∃ i, b ∈ U i) (z : Cocycle IB U n) :
    OverlapEq (SpinHOnePullback.cocycle f hf z) (coboundary (chartGauge f hloc hU z)) := by
  intro i j x hi hj
  let a := (hU (f x)).choose
  change z.val.value i j (f x) = z.val.value a j (f x) * (z.val.value a i (f x))⁻¹
  exact eq_mul_inv_iff_mul_eq.mpr (z.property a i j (f x) (hU (f x)).choose_spec hi hj)

include hloc in
/-- Each smooth sign class on a fixed open cover pulls back to the identity. -/
theorem hom_eq_one (U : ι → TopologicalSpace.Opens B) (hU : ∀ b, ∃ i, b ∈ U i) (c : H1 IB U n) :
    SpinHOnePullback.hom f hf U c = 1 := by
  obtain ⟨z, rfl⟩ := classOf_surjective c
  exact (classOf_eq_one_iff _).mpr ⟨chartGauge f hloc hU z, cocycle_coboundary f hf hloc hU z⟩

include hloc in
/-- Pullback along a locally constant map sends every all-cover H¹ class to the group identity. -/
theorem pull_eq_one (c : GlobalH1 IB B n) : pull f hf c = 1 := by
  obtain ⟨P, d, rfl⟩ := exists_representative c
  rw [← ofCover_point P, pull_ofCover, hom_eq_one f hf hloc P.domain P.covers, map_one]

include hloc in
/-- The all-cover homomorphism itself is trivial along any locally constant map. -/
theorem pull_eq_one_hom : pull f hf = 1 :=
  MonoidHom.ext (pull_eq_one f hf hloc)

/-- A constant base map kills fixed-cover sign cohomology. -/
theorem hom_const (b : B) (U : ι → TopologicalSpace.Opens B) (hU : ∀ y, ∃ i, y ∈ U i) (c : H1 IB U n) :
    SpinHOnePullback.hom (ContinuousMap.const X b) (contMDiff_const (I := IX)) U c = 1 :=
  hom_eq_one _ _ (IsLocallyConstant.of_constant _ (fun _ _ => rfl)) U hU c

/-- A constant base map kills every native global smooth Spin sign class. -/
theorem pull_const (b : B) (c : GlobalH1 IB B n) :
    pull (ContinuousMap.const X b) (contMDiff_const (I := IX)) c = 1 :=
  pull_eq_one _ _ (IsLocallyConstant.of_constant _ (fun _ _ => rfl)) c

/-- On a discrete charted base, evaluating pullback along the identity makes every smooth sign class trivial. -/
theorem eq_one_of_discrete [DiscreteTopology B] (c : GlobalH1 IB B n) : c = 1 :=
  (pull_id c).symm.trans (pull_eq_one (ContinuousMap.id B) (contMDiff_id (I := IB))
    ((IsLocallyConstant.iff_continuous _).mpr continuous_id) c)

end FoliationQM.SpinHOneLocallyConstantPullback
