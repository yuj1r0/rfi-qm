module
public import FoliationQM.SpinHOneLocallyConstantPullback
public import FoliationQM.SpinPullbackDisplacement
public import FoliationQM.SmoothSpinHOneTorsor

/-!
# Physical Spin classes along a locally constant base map

For the Spin-frame classification in v13 `prop:takabayasi`, locally
constant base change kills the displacement between any two original
smooth lifts. Their pulled lifts are physically isomorphic. If a reference
class exists, the image consists of its pulled class and reaches every
target class exactly when the global degree-one group of the new base
is trivial.
-/

@[expose] public section
noncomputable section
open scoped Manifold
namespace FoliationQM.LocallyConstantSpinPullback
open CliffordSpinLorentzSmooth LorentzMatrixGroup GeometricSpinObstruction SmoothSpinRelativeClass
open SpinAllCoverHOne GlobalSpinDisplacement SmoothSpinHOneTorsor SpinPullbackClasses
open SmoothPrincipalPullback SmoothPullbackChartedSpace

universe u
variable {X B : Type u} {T ι EX EB ET HX HB HT : Type*}
  [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  [NormedAddCommGroup ET] [NormedSpace ℝ ET] [TopologicalSpace HT]
  [TopologicalSpace X] [ChartedSpace HX X] [TopologicalSpace B] [ChartedSpace HB B]
  [TopologicalSpace T] [ChartedSpace HT T] {proj : T → B}
  {IX : ModelWithCorners ℝ EX HX} {IB : ModelWithCorners ℝ EB HB} {K : ModelWithCorners ℝ ET HT}
  {n : WithTop ℕ∞} {L : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι}
  [IsManifold IX n X] (f : C(X, B)) (hf : ContMDiff IX IB n f)
  (LM : GeometricPrincipalSmoothAtlas.Data IB lorentzModel K L n) (hloc : IsLocallyConstant (f : X → B))

include hloc

/-- Any two original lifts give physically isomorphic smooth lifts after locally constant base change. -/
theorem nonempty_between (S U : SmoothLift IB K L n) :
    letI := chartedSpace HX LorentzManifold.Model f L
    Nonempty (SmoothBetween (GeometricSpinPullback.lift f hf LM S) (GeometricSpinPullback.lift f hf LM U)) :=
  (SpinPullbackDisplacement.nonempty_iff f hf LM S U).mpr
    (SpinHOneLocallyConstantPullback.pull_eq_one f hf hloc (relative LM S U))

/-- Every pair of original physical classes has the same pulled class. -/
theorem classMap_eq (p q : PhysicalClass IB K L n) : classMap f hf LM p = classMap f hf LM q := by
  let := chartedSpace HX LorentzManifold.Model f L
  exact (displacement_one_iff (smoothAtlas f hf LM) _ _).mp
    ((SpinPullbackDisplacement.displacement_pullback f hf LM p q).trans
      (SpinHOneLocallyConstantPullback.pull_eq_one f hf hloc (displacement LM p q)))

/-- With a reference class, the image consists exactly of that class's pullback. -/
theorem range_classMap (p : PhysicalClass IB K L n) :
    Set.range (classMap f hf LM) = {classMap f hf LM p} := by
  ext q
  constructor
  · rintro ⟨r, rfl⟩
    exact classMap_eq f hf LM hloc r p
  · intro h
    exact ⟨p, (Set.mem_singleton_iff.mp h).symm⟩

/-- Locally constant pullback is injective precisely when at most one original physical class exists. -/
theorem classMap_injective_iff :
    Function.Injective (classMap f hf LM) ↔ Subsingleton (PhysicalClass IB K L n) :=
  ⟨fun h => ⟨fun p q => h (classMap_eq f hf LM hloc p q)⟩, fun h _ _ _ => h.elim _ _⟩

/-- Given an original reference, locally constant pullback is surjective precisely when the
new base's global sign group is trivial. -/
theorem classMap_surjective_iff (p : PhysicalClass IB K L n) :
    Function.Surjective (classMap f hf LM) ↔ Subsingleton (GlobalH1 IX X n) := by
  let := chartedSpace HX LorentzManifold.Model f L
  let FM := smoothAtlas f hf LM
  constructor
  · intro h
    let e := basedEquiv FM (classMap f hf LM p)
    constructor
    intro g k
    obtain ⟨r, hr⟩ := h (e g)
    obtain ⟨t, ht⟩ := h (e k)
    exact e.injective (hr.symm.trans ((classMap_eq f hf LM hloc r t).trans ht))
  · intro h q
    exact ⟨p, (displacement_one_iff FM _ _).mp (h.elim _ _)⟩

/-- Bijectivity for locally constant base change requires both uniqueness of the original
physical class and triviality of the new base's degree-one sign group. -/
theorem classMap_bijective_iff (p : PhysicalClass IB K L n) :
    Function.Bijective (classMap f hf LM) ↔
      Subsingleton (PhysicalClass IB K L n) ∧ Subsingleton (GlobalH1 IX X n) :=
  and_congr (classMap_injective_iff f hf LM hloc) (classMap_surjective_iff f hf LM hloc p)

omit hloc in
/-- In particular, every constant base map sends two original lift classes to the same class. -/
theorem classMap_const (b : B) (p q : PhysicalClass IB K L n) :
    classMap (ContinuousMap.const X b) (contMDiff_const (I := IX)) LM p =
      classMap (ContinuousMap.const X b) (contMDiff_const (I := IX)) LM q :=
  classMap_eq (ContinuousMap.const X b) contMDiff_const LM (IsLocallyConstant.const b) p q

end FoliationQM.LocallyConstantSpinPullback
