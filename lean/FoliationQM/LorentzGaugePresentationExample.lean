module
public import FoliationQM.GlobalGaugePathCriterion
public import FoliationQM.GlobalGaugePresentation
public import FoliationQM.LorentzIdentityHomotopyObstruction
public import FoliationQM.SmoothGlobalLorentzGaugeAtlas
public import FoliationQM.ParacompactSpinLiftCriterion

/-!
# A smoothly Spin product bundle whose two global charts have no path family

For the frame-bundle component of v13 `prop:takabayasi`, take the base to
be the proper future Lorentz group, with its identity as the second gauge.
The full-overlap transition is noncontractible. Nevertheless an anchored
refinement has normalized paths, the native obstruction vanishes, and the
smooth target admits a genuine Spin lift.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LorentzGaugePresentationExample
open LorentzMatrixGroup CliffordSpinLorentzSmooth PrincipalAtlasCrossGauge PathTransitionData
open GeometricSpinObstruction RefinedGeometricPrincipalAtlas CliffordSpinCoverRefinement
open GlobalLorentzGaugeAtlas

/-- Any smooth gauge on the product inherits a genuine physical lift from its zero native class. -/
theorem lift_of_smooth_gauge {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B] {I : ModelWithCorners ℝ E H}
    {n : WithTop ℕ∞} [IsManifold I n B] [LocallyPathConnectedSpace B]
    (k : C(B, ProperFutureLorentz)) (hk : ContMDiff I lorentzModel n k) :
    Nonempty (SmoothLift I (I.prod lorentzModel) (atlas k) n) :=
  (PresentedSpinCriterion.nonempty_iff (SmoothGlobalLorentzGaugeAtlas.smoothAtlas k hk)
    (GlobalGaugePresentation.hasPresentation k)).mpr (GlobalGaugePresentation.native_zero k)

/-- The atlas with identity transition on the full Lorentz base. -/
abbrev identityAtlas := atlas (ContinuousMap.id ProperFutureLorentz)

/-- A normalized family on these original charts would contract the identity of the Lorentz group. -/
theorem no_original_family : ¬ Nonempty (Family (data identityAtlas)) :=
  fun h => LorentzIdentityHomotopyObstruction.id_not_nullhomotopic
    ((GlobalGaugePathCriterion.family_iff_nullhomotopic _).mp h)

/-- Two pairs of global charts with the same projection and action can give opposite
answers to the fixed-cover path question. -/
theorem two_atlases_on_same_product :
    let unitGauge := ContinuousMap.const ProperFutureLorentz (1 : ProperFutureLorentz)
    (atlas unitGauge).right = identityAtlas.right ∧ Nonempty (Family (data (atlas unitGauge))) ∧
      ¬ Nonempty (Family (data identityAtlas)) :=
  ⟨rfl, (GlobalGaugePathCriterion.family_iff_nullhomotopic _).mpr
    (ContinuousMap.nullhomotopic_of_constant _), no_original_family⟩

/-- There is an anchored refinement of those very same charts with a normalized joint family. -/
theorem refined_family : ∃ R : Refinement (domains identityAtlas) ProperFutureLorentz,
    (∀ x, x ∈ R.domain x) ∧ Nonempty (Family (data (restrictedAtlas identityAtlas R))) :=
  ⟨GlobalGaugePresentation.refinement _, GlobalGaugePresentation.mem_refinement _,
    ⟨GlobalGaugePresentation.refinedFamily _⟩⟩

/-- The canonical class of the two-chart atlas computed on its actual Lorentz base is zero. -/
theorem zero_obstruction : ParacompactBundleObstruction.obstruction identityAtlas = 0 :=
  GlobalGaugePresentation.canonical_zero _

/-- The independent physical target on the original charts has a smooth Spin lift at every order. -/
theorem smooth_lift (n : WithTop ℕ∞) :
    Nonempty (SmoothLift lorentzModel (lorentzModel.prod lorentzModel) identityAtlas n) :=
  lift_of_smooth_gauge _ (contMDiff_id (I := lorentzModel))

/-- Failure of normalized paths on an atlas coexists with a smooth physical lift of that same atlas. -/
theorem fixed_cover_failure_with_lift (n : WithTop ℕ∞) :
    (¬ Nonempty (Family (data identityAtlas))) ∧
      ParacompactBundleObstruction.obstruction identityAtlas = 0 ∧
      Nonempty (SmoothLift lorentzModel (lorentzModel.prod lorentzModel) identityAtlas n) :=
  ⟨no_original_family, zero_obstruction, smooth_lift n⟩

end FoliationQM.LorentzGaugePresentationExample
