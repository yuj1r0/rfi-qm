module
public import FoliationQM.GlobalSpinOriginalCover
public import FoliationQM.SmoothSpinHOneTorsor

/-!
# Which physical Spin classes are represented on one given atlas?

For the global Spin-frame component of v13 `prop:takabayasi`, a chosen
adapted lift identifies the image of this atlas in the physical classes.
A new class admits a representative adapted to this same atlas exactly
when its global displacement comes from the atlas's own sign group.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GlobalSpinAdaptedImage
open CliffordSpinLorentzSmooth LorentzMatrixGroup RefinedGeometricPrincipalAtlas
open SpinSignHOne SpinLiftIsomorphism SpinLiftSignDifference SmoothSpinRelativeClass
open SpinAllCoverHOne GlobalSpinDisplacement SpinGeometricLiftClasses

universe u
variable {E H EP HP : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  {B : Type u} [TopologicalSpace B] [ChartedSpace H B] {I : ModelWithCorners ℝ E H}
  {P ι : Type*} [TopologicalSpace P] [ChartedSpace HP P] {KP : ModelWithCorners ℝ EP HP}
  {proj : P → B} {L : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι}
  {n : WithTop ℕ∞} (LM : GeometricPrincipalSmoothAtlas.Data I lorentzModel KP L n) [IsManifold I n B]

/-- On classes represented by adapted lifts, their global displacement is the image of their fixed-cover displacement. -/
theorem displacement_adapted (p q : GeometricClass LM) :
    displacement LM (adaptedEmbedding LM p) (adaptedEmbedding LM q) =
    ofCover (domains L) L.covers
      (SpinLiftHOneTorsor.displacement (transitionEquiv LM p) (transitionEquiv LM q)) :=
  Quotient.inductionOn₂ p q (GlobalSpinOriginalCover.displacement_forget LM)

/-- The global action of a fixed-cover sign recovers the geometric twist constructed on that cover. -/
theorem act_ofCover (A : GeometricSpinStructure.Lift I L n) (c : H1 I (domains L) n) :
    SmoothSpinHOneTorsor.act LM (ofCover (domains L) L.covers c)
      (physicalClass (forgetAdaptation LM A)) = basedEmbedding LM A c := by
  apply (SmoothSpinHOneTorsor.act_eq_iff LM _ _ _).mpr
  change displacement LM (adaptedEmbedding LM (geometricClass LM A))
    (adaptedEmbedding LM (SpinGeometricLiftClasses.basedEquiv LM A c)) = _
  rw [displacement_adapted]
  apply congrArg (ofCover (domains L) L.covers)
  change SpinLiftHOneTorsor.displacement (SpinLiftChartGauge.liftClass (transitions LM A))
    (transitionEquiv LM ((transitionEquiv LM).symm _)) = c
  rw [Equiv.apply_symm_apply]
  exact SpinLiftHOneTorsor.displacement_act (D := AdaptedGeometricSpinLift.lorentzData LM) c _

/-- A physical class is represented on the specified atlas exactly when its displacement from
the adapted reference belongs to the image of that cover's degree-one group. -/
theorem mem_adaptedImage_iff (A : GeometricSpinStructure.Lift I L n) (q : PhysicalClass I KP L n) :
    q ∈ Set.range (adaptedEmbedding LM) ↔
    displacement LM (physicalClass (forgetAdaptation LM A)) q ∈
      Set.range (ofCover (I := I) (n := n) (domains L) L.covers) := by
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨_, (displacement_adapted LM (geometricClass LM A) r).symm⟩
  · rintro ⟨c, hc⟩
    refine ⟨SpinGeometricLiftClasses.basedEquiv LM A c, ?_⟩
    exact (act_ofCover LM A c).symm.trans ((SmoothSpinHOneTorsor.act_eq_iff LM _ _ _).mpr hc.symm)

end FoliationQM.GlobalSpinAdaptedImage
