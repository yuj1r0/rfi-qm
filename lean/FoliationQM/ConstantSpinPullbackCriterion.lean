module
public import FoliationQM.LocallyConstantSpinPullback
public import FoliationQM.ConstructedPullbackSpinCriterion
public import FoliationQM.ModTwoConstantPullback

/-!
# Existence, uniqueness and descent for constant pullback

For the Spin-frame component of v13 `prop:takabayasi`, a presented
Lorentz target pulled back along a constant map has zero native
all-cover degree-two obstruction. Its smooth Spin lifts therefore exist.
Surjectivity on their physical classes requires both an original lift
and trivial degree one on the new base. This separates existence on the
actual pulled space from descent of all its lifts.
-/

@[expose] public section
noncomputable section
open scoped Manifold
namespace FoliationQM.ConstantSpinPullbackCriterion
open CliffordSpinLorentzSmooth LorentzMatrixGroup GeometricSpinObstruction
open SpinAllCoverHOne SmoothSpinRelativeClass SmoothPullbackChartedSpace
open SpinPullbackClasses PresentedLorentzBundle

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
  [IsManifold IX n X] [LocallyPathConnectedSpace X] [LocallyPathConnectedSpace B]
  (b : B) (LM : GeometricPrincipalSmoothAtlas.Data IB lorentzModel K L n)
  (P : HasPresentation proj L.right)

include LM P in
/-- A constant pullback of a presented Lorentz space has a physical smooth lift without requiring an original one. -/
theorem nonempty_lift : Nonempty (ConstructedPullbackSpinCriterion.Lift IX n (.const X b) L) :=
  (ConstructedPullbackSpinCriterion.nonempty_iff (.const X b) (contMDiff_const (I := IX)) LM P).mpr
    (ModTwoConstantPullback.pull_const b _)

include LM P in
/-- Exactly one target physical class exists precisely when the first sign group of the new base is trivial. -/
theorem unique_iff : (∃! _q : ConstructedPullbackSpinCriterion.Classes IX n (.const X b) L, True) ↔
    Subsingleton (GlobalH1 IX X n) :=
  (ConstructedPullbackSpinCriterion.unique_iff (.const X b) (contMDiff_const (I := IX)) LM P).trans
    ⟨And.right, fun h => ⟨ModTwoConstantPullback.pull_const b _, h⟩⟩

include P in
/-- Every target class descends along a constant map exactly when an original lift exists and the new base has trivial degree one. -/
theorem surjective_iff : Function.Surjective (classMap (.const X b) (contMDiff_const (I := IX)) LM) ↔
    Nonempty (SmoothLift IB K L n) ∧ Subsingleton (GlobalH1 IX X n) := by
  let := chartedSpace HX LorentzManifold.Model (ContinuousMap.const X b) L
  constructor
  · intro h
    obtain ⟨U⟩ := nonempty_lift (X := X) (IX := IX) b LM P
    obtain ⟨p, _⟩ := h (physicalClass U)
    exact ⟨Quotient.inductionOn p (fun S => ⟨S⟩),
      (LocallyConstantSpinPullback.classMap_surjective_iff (.const X b) contMDiff_const LM
        (IsLocallyConstant.const b) p).mp h⟩
  · rintro ⟨⟨S⟩, h⟩
    exact (LocallyConstantSpinPullback.classMap_surjective_iff (.const X b) contMDiff_const LM
      (IsLocallyConstant.const b) (physicalClass S)).mpr h

end FoliationQM.ConstantSpinPullbackCriterion
