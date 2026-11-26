module
public import FoliationQM.ParacompactCartesianObstruction
public import FoliationQM.PresentedSpinCriterion

/-!
# Smooth Spin lifts of a Cartesian Lorentz target

For the frame-bundle component of v13 `prop:takabayasi`, a smooth atlas on
the new base is identified equivariantly over that base with the geometric
fiber product of an original Lorentz atlas. The pulled native obstruction
detects smooth lift existence on the new target. A continuous section
also detects existence on an independently smooth original target.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CartesianSpinLiftCriterion
open LorentzMatrixGroup CliffordSpinLorentzSmooth GeometricSpinObstruction
open GeometricPrincipalPullback ModTwoGlobalPullback ParacompactBundleObstruction
open SpinAllCoverHOne SmoothSpinRelativeClass

variable {X B T U ι κ EX HX EU HU : Type*} [TopologicalSpace B] [TopologicalSpace T]
  [ParacompactSpace B] [NormalSpace B] [LocallyPathConnectedSpace B]
  [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  [NormedAddCommGroup EU] [NormedSpace ℝ EU] [TopologicalSpace HU]
  [TopologicalSpace X] [ChartedSpace HX X] [TopologicalSpace U] [ChartedSpace HU U]
  [LocallyPathConnectedSpace X] {I : ModelWithCorners ℝ EX HX} {K : ModelWithCorners ℝ EU HU}
  {n : WithTop ℕ∞} [IsManifold I n X] {proj : T → B} {q : U → X}
  (A : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι)
  {C : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) q κ}
  (CM : GeometricPrincipalSmoothAtlas.Data I lorentzModel K C n)
  (f : C(X, B)) (e : U ≃ₜ Total f proj) (hq : ∀ u, q u = projection f proj (e u))
  (he : ∀ u g, e (C.right u g) = (atlas f A).right (e u) g)

include A CM f e hq he

/-- A genuine smooth Spin lift into the specified Cartesian atlas exists exactly when the
pullback of the original ordinary atlas's native obstruction vanishes. -/
theorem nonempty_iff : Nonempty (SmoothLift I K C n) ↔ pull f (obstruction A) = 0 := by
  rw [← ParacompactCartesianObstruction.inherited A C f e hq he]
  exact PresentedSpinCriterion.nonempty_iff CM (ParacompactCartesianObstruction.hasPresentation A C f e hq he)

/-- A vanishing pulled class supplies the torsor of physical Spin classes on the new target. -/
@[instance_reducible] def torsor_of_zero (hz : pull f (obstruction A) = 0) :
    Torsor (GlobalH1 I X n) (PhysicalClass I K C n) :=
  SmoothSpinHOneTorsor.torsor CM ((nonempty_iff A CM f e hq he).mpr hz)

/-- A unique physical class requires precisely vanishing of the pulled obstruction
and triviality of the degree-one sign group on the new base. -/
theorem unique_iff : (∃! _c : PhysicalClass I K C n, True) ↔
    pull f (obstruction A) = 0 ∧ Subsingleton (GlobalH1 I X n) :=
  (GlobalSpinClassificationCriterion.unique_iff CM).trans
    (and_congr (nonempty_iff A CM f e hq he) Iff.rfl)

/-- A constant base map supplies a smooth lift on the new target. -/
theorem nonempty_of_constant (b : B) (hf : ∀ x, f x = b) : Nonempty (SmoothLift I K C n) := by
  apply (nonempty_iff A CM f e hq he).mpr
  rw [show f = ContinuousMap.const X b from ContinuousMap.ext hf, ModTwoConstantPullback.pull_const]

/-- For a constant base map the new target has exactly one physical class precisely
when its degree-one sign group is trivial. -/
theorem unique_iff_of_constant (b : B) (hf : ∀ x, f x = b) :
    (∃! _c : PhysicalClass I K C n, True) ↔ Subsingleton (GlobalH1 I X n) := by
  rw [unique_iff A CM f e hq he]
  have hz := (nonempty_iff A CM f e hq he).mp (nonempty_of_constant A CM f e hq he b hf)
  exact ⟨And.right, fun h => ⟨hz, h⟩⟩

/-- When the base map has a continuous section, the original native obstruction
vanishes exactly when a smooth lift exists on the new target. -/
theorem nonempty_iff_of_section (s : C(B, X)) (hs : Function.RightInverse s f) :
    Nonempty (SmoothLift I K C n) ↔ obstruction A = 0 := by
  rw [nonempty_iff A CM f e hq he]
  constructor
  · intro h
    rw [← ParacompactObstructionPullback.section_pull f s hs (obstruction A), h, map_zero]
  · intro h
    rw [h, map_zero]

variable {EB HB ET HT : Type*}
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  [NormedAddCommGroup ET] [NormedSpace ℝ ET] [TopologicalSpace HT]
  [ChartedSpace HB B] [ChartedSpace HT T]
  {IB : ModelWithCorners ℝ EB HB} {KT : ModelWithCorners ℝ ET HT}
  {m : WithTop ℕ∞} [IsManifold IB m B]
  (AM : GeometricPrincipalSmoothAtlas.Data IB lorentzModel KT A m)

include AM

/-- Smooth lift existence on the original target implies existence on the new target
at its own smoothness order. -/
theorem nonempty_of_original (h : Nonempty (SmoothLift IB KT A m)) : Nonempty (SmoothLift I K C n) := by
  have hz : obstruction A = 0 :=
    (PresentedSpinCriterion.nonempty_iff AM (ParacompactLorentzPresentation.hasPresentation A)).mp h
  apply (nonempty_iff A CM f e hq he).mpr
  rw [hz, map_zero]

/-- With a continuous section, the existence of genuine smooth lifts on the two
independently smooth targets is equivalent. Their smoothness orders may differ. -/
theorem split_nonempty_iff (s : C(B, X)) (hs : Function.RightInverse s f) :
    Nonempty (SmoothLift I K C n) ↔ Nonempty (SmoothLift IB KT A m) :=
  (nonempty_iff_of_section A CM f e hq he s hs).trans
    (PresentedSpinCriterion.nonempty_iff AM (ParacompactLorentzPresentation.hasPresentation A)).symm

/-- With a continuous section the new physical class is unique precisely when
an original smooth lift exists and degree one on the new base is trivial. -/
theorem split_unique_iff (s : C(B, X)) (hs : Function.RightInverse s f) :
    (∃! _c : PhysicalClass I K C n, True) ↔
      Nonempty (SmoothLift IB KT A m) ∧ Subsingleton (GlobalH1 I X n) :=
  (GlobalSpinClassificationCriterion.unique_iff CM).trans
    (and_congr (split_nonempty_iff A CM f e hq he AM s hs) Iff.rfl)

end FoliationQM.CartesianSpinLiftCriterion
