module
public import FoliationQM.ConstantSpinPullbackCriterion
public import FoliationQM.PuncturedPlaneAtlasObstruction
public import FoliationQM.PuncturedPlaneGlobalSpinAction

/-!
# Constant base change on the punctured plane

For the geometric frame component of v13 `prop:takabayasi`, the two
exhibited original Spin lifts have different physical classes. A constant
self-map identifies their pullbacks. Twisting the pulled reference by the
same negative-edge sign on the new plane gives a specific target class
outside the image, despite the vanishing pulled degree-two obstruction.
-/

@[expose] public section
noncomputable section
open scoped Manifold
namespace FoliationQM.PuncturedPlaneConstantSpinPullback
open PuncturedPlaneSignCover PuncturedPlaneGlobalSign CliffordSpinLorentzSmooth
open SmoothSpinRelativeClass SmoothSpinHOneTorsor SpinPullbackClasses
open PuncturedPlaneGeometricSpin (atlas smoothAtlas)
open PuncturedPlaneRelativeSpin (reference twisted)

/-- The physical classes of the geometric Lorentz target on the punctured plane. -/
abbrev Original (n : WithTop ℕ∞) := PhysicalClass model (model.prod lorentzModel) (atlas n) n

/-- The physical classes on its actual Lorentz fiber product over the constant self-map. -/
abbrev Target (b : Plane) (n : WithTop ℕ∞) :=
  ConstructedPullbackSpinCriterion.Classes model n (.const Plane b) (atlas n)

/-- Pullback of physical classes along the self-map with value `b`. -/
def baseChange (b : Plane) (n : WithTop ℕ∞) : Original n → Target b n :=
  classMap (.const Plane b) (contMDiff_const (I := model)) (smoothAtlas n)

variable (b : Plane) (n : WithTop ℕ∞)

/-- The negative edge has order two before pullback and lies in the kernel of this degree-one map. -/
theorem lost_order_two : orderOf (sign n) = 2 ∧ sign n ∈
    (SpinHOneGlobalPullback.pull (.const Plane b) (contMDiff_const (I := model))).ker :=
  ⟨sign_orderOf n, SpinHOneLocallyConstantPullback.pull_const (IX := model) b (sign n)⟩

/-- The distinct reference and twisted physical classes have equal pullbacks. -/
theorem collapse : baseChange b n (physicalClass (twisted n)) = baseChange b n (physicalClass (reference n)) :=
  LocallyConstantSpinPullback.classMap_eq (.const Plane b) (contMDiff_const (I := model))
    (smoothAtlas n) (IsLocallyConstant.const b) _ _

/-- The two actual pulled geometric lifts are smoothly physically isomorphic. -/
theorem pulled_isomorphic :
    letI := SmoothPullbackChartedSpace.chartedSpace Ambient LorentzManifold.Model (.const Plane b) (atlas n)
    Nonempty (SmoothBetween
      (GeometricSpinPullback.lift (.const Plane b) (contMDiff_const (I := model)) (smoothAtlas n) (twisted n))
      (GeometricSpinPullback.lift (.const Plane b) contMDiff_const (smoothAtlas n) (reference n))) :=
  Quotient.exact (collapse b n)

/-- Pullback along any constant self-map of this plane fails to distinguish all original classes. -/
theorem not_injective : ¬ Function.Injective (baseChange b n) :=
  fun h => PuncturedPlaneRelativeSpin.physicalClass_ne n (h (collapse b n))

/-- An explicit target class is obtained by twisting the pulled reference by the new plane's negative edge. -/
def missed : Target b n :=
  letI := SmoothPullbackChartedSpace.chartedSpace Ambient LorentzManifold.Model (.const Plane b) (atlas n)
  act (SmoothPrincipalPullback.smoothAtlas (.const Plane b) (contMDiff_const (I := model)) (smoothAtlas n))
    (sign n) (baseChange b n (physicalClass (reference n)))

/-- No original physical class maps to the displayed negative-edge twist of the pulled reference. -/
theorem missed_notMem_range : missed b n ∉ Set.range (baseChange b n) := by
  let := SmoothPullbackChartedSpace.chartedSpace Ambient LorentzManifold.Model (.const Plane b) (atlas n)
  rintro ⟨p, hp⟩
  have he : missed b n = baseChange b n (physicalClass (reference n)) := hp.symm.trans
    (LocallyConstantSpinPullback.classMap_eq (.const Plane b) (contMDiff_const (I := model)) (smoothAtlas n)
      (IsLocallyConstant.const b) p (physicalClass (reference n)))
  exact sign_ne_one n ((act_eq_self_iff (SmoothPrincipalPullback.smoothAtlas (.const Plane b)
    (contMDiff_const (I := model)) (smoothAtlas n)) (sign n) _).mp he)

/-- Pullback along the constant self-map also fails to attain all target classes. -/
theorem not_surjective : ¬ Function.Surjective (baseChange b n) := fun h => missed_notMem_range b n (h _)

/-- The actual Lorentz fiber product has zero native obstruction while the displayed physical class fails to descend. -/
theorem zero_obstruction_and_missed :
    letI : LocallyPathConnectedSpace Plane := punctured.isOpen.locallyPathConnectedSpace
    PresentedLorentzBundle.obstruction (PresentedBundlePullback.hasPresentation (.const Plane b)
      (PuncturedPlaneAtlasObstruction.witness n)) = 0 ∧ missed b n ∉ Set.range (baseChange b n) :=
  letI : LocallyPathConnectedSpace Plane := punctured.isOpen.locallyPathConnectedSpace
  ⟨PresentedBundlePullback.constant_zero b (PuncturedPlaneAtlasObstruction.witness n), missed_notMem_range b n⟩

end FoliationQM.PuncturedPlaneConstantSpinPullback
