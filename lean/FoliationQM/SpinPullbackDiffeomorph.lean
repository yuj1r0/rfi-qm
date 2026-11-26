module
public import FoliationQM.SpinPullbackImage
public import FoliationQM.SpinPullbackDescent
public import FoliationQM.SpinHOnePullbackEquivalences

/-!
# Physical Spin classes under a diffeomorphism of bases

For the frame component of v13 `prop:takabayasi`, a diffeomorphism
pulls physical classes bijectively to the actual Lorentz fiber product.
The inverse is the geometric recovery along the inverse base map. To
prove surjectivity, each given target class supplies its own recovered
reference; no global inhabitedness assumption is needed.
-/

@[expose] public section
noncomputable section
open scoped Manifold
namespace FoliationQM.SpinPullbackDiffeomorph
open CliffordSpinLorentzSmooth LorentzMatrixGroup GeometricSpinObstruction SmoothSpinRelativeClass
open SpinPullbackClasses SpinPullbackDescent SpinHOneGlobalPullback SmoothPullbackChartedSpace

universe u
variable {X B : Type u} {T ι EX EB ET HX HB HT : Type*}
  [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  [NormedAddCommGroup ET] [NormedSpace ℝ ET] [TopologicalSpace HT]
  [TopologicalSpace X] [ChartedSpace HX X] [TopologicalSpace B] [ChartedSpace HB B]
  [TopologicalSpace T] [ChartedSpace HT T]
  {IX : ModelWithCorners ℝ EX HX} {IB : ModelWithCorners ℝ EB HB}
  {K : ModelWithCorners ℝ ET HT} {n : WithTop ℕ∞} {proj : T → B}
  {L : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι}
  [IsManifold IX n X] [IsManifold IB n B] (e : Diffeomorph IX IB X B n)
  (LM : GeometricPrincipalSmoothAtlas.Data IB lorentzModel K L n)

/-- Smooth base diffeomorphisms give actual equivalences on physical classes, even for empty lift spaces. -/
def equiv : PhysicalClass IB K L n ≃
    ConstructedPullbackSpinCriterion.Classes IX n (e.toHomeomorph : C(X, B)) L := by
  let f : C(X, B) := e.toHomeomorph
  let s : C(B, X) := e.symm.toHomeomorph
  have hr : Function.RightInverse s f := e.apply_symm_apply
  let c := classMap f e.contMDiff LM
  let r := recover LM f s e.contMDiff e.symm.contMDiff hr
  have left : Function.LeftInverse r c := recover_leftInverse LM f s e.contMDiff e.symm.contMDiff hr
  have surj : Function.Surjective c := fun q =>
    ((SpinPullbackImage.classMap_surjective_iff f e.contMDiff LM (r q)).mpr
      (SpinHOnePullbackEquivalences.diffeomorphEquiv e).surjective) q
  refine ⟨c, r, left, ?_⟩
  intro q
  obtain ⟨p, rfl⟩ := surj q
  exact congrArg c (left p)

/-- The forward equivalence is the geometric pullback on physical classes. -/
theorem equiv_apply (p : PhysicalClass IB K L n) :
    equiv e LM p = classMap (e.toHomeomorph : C(X, B)) e.contMDiff LM p := rfl

/-- Its inverse really is pullback along the inverse map followed by the geometric target identifications. -/
theorem equiv_symm_apply (q : ConstructedPullbackSpinCriterion.Classes IX n (e.toHomeomorph : C(X, B)) L) :
    (equiv e LM).symm q = recover LM (e.toHomeomorph : C(X, B)) (e.symm.toHomeomorph : C(B, X))
      e.contMDiff e.symm.contMDiff e.apply_symm_apply q := rfl

/-- The physical equivalence intertwines twists through the corresponding degree-one group equivalence. -/
theorem equiv_act (g : SpinAllCoverHOne.GlobalH1 IB B n) (p : PhysicalClass IB K L n) :
    letI := chartedSpace HX LorentzManifold.Model (e.toHomeomorph : C(X, B)) L
    equiv e LM (SmoothSpinHOneTorsor.act LM g p) = SmoothSpinHOneTorsor.act
      (SmoothPrincipalPullback.smoothAtlas (e.toHomeomorph : C(X, B)) e.contMDiff LM)
      (SpinHOnePullbackEquivalences.diffeomorphEquiv e g) (equiv e LM p) :=
  SpinPullbackTorsor.classMap_act (e.toHomeomorph : C(X, B)) e.contMDiff LM g p

include LM in
/-- A smooth lift exists on the original space exactly when one exists on the actual diffeomorphic pullback. -/
theorem nonempty_lift_iff : Nonempty (SmoothLift IB K L n) ↔
    Nonempty (ConstructedPullbackSpinCriterion.Lift IX n (e.toHomeomorph : C(X, B)) L) := by
  let := chartedSpace HX LorentzManifold.Model (e.toHomeomorph : C(X, B)) L
  constructor
  · exact Nonempty.map (GeometricSpinPullback.lift (e.toHomeomorph : C(X, B)) e.contMDiff LM)
  · rintro ⟨U⟩
    exact Quotient.inductionOn ((equiv e LM).symm (physicalClass U)) (fun S => ⟨S⟩)

end FoliationQM.SpinPullbackDiffeomorph
