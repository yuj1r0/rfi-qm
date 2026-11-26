module
public import FoliationQM.SpinHOneSectionSplit
public import FoliationQM.SpinPullbackTorsor

/-!
# Physical Spin coordinates for a smooth section of the base map

For the smooth Spin classification in v13 `prop:takabayasi`, use the pulled
reference class to measure displacement on the new base. Restriction to the
section and its complementary kernel sign split that displacement. The inverse
twists the pullback of an original class by the kernel sign, independently
of the reference used to read the coordinates.
-/

@[expose] public section
noncomputable section
open scoped Manifold
namespace FoliationQM.SpinPullbackBasedSectionSplit
open CliffordSpinLorentzSmooth LorentzMatrixGroup SmoothSpinRelativeClass GlobalSpinDisplacement
open SmoothSpinHOneTorsor SpinHOneGlobalPullback SpinPullbackClasses
open SmoothPullbackChartedSpace SmoothPrincipalPullback

universe u
variable {X B : Type u} {T ι EX EB ET HX HB HT : Type*}
  [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  [NormedAddCommGroup ET] [NormedSpace ℝ ET] [TopologicalSpace HT]
  [TopologicalSpace X] [ChartedSpace HX X] [TopologicalSpace B] [ChartedSpace HB B]
  [TopologicalSpace T] [ChartedSpace HT T]
  {IX : ModelWithCorners ℝ EX HX} {IB : ModelWithCorners ℝ EB HB} {K : ModelWithCorners ℝ ET HT}
  {n : WithTop ℕ∞} {proj : T → B} {L : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι}
  [IsManifold IX n X] [IsManifold IB n B] (f : C(X, B)) (hf : ContMDiff IX IB n f)
  (s : C(B, X)) (hs : ContMDiff IB IX n s) (hr : Function.RightInverse s f)
  (LM : GeometricPrincipalSmoothAtlas.Data IB lorentzModel K L n)

/-- A reference class identifies the new physical classes with original classes and section kernel signs. -/
def equiv (p : PhysicalClass IB K L n) :
    ConstructedPullbackSpinCriterion.Classes IX n f L ≃ PhysicalClass IB K L n × (pull s hs).ker :=
  letI := chartedSpace HX LorentzManifold.Model f L
  ((basedEquiv (smoothAtlas f hf LM) (classMap f hf LM p)).symm.trans
    (SpinHOneSectionSplit.equiv f hf s hs hr).toEquiv).trans
      (Equiv.prodCongr (basedEquiv LM p) (Equiv.refl _))

/-- The first class coordinate is the original reference twisted by the restricted displacement. -/
theorem equiv_fst (p : PhysicalClass IB K L n) (q : ConstructedPullbackSpinCriterion.Classes IX n f L) :
    letI := chartedSpace HX LorentzManifold.Model f L
    (equiv f hf s hs hr LM p q).1 =
      act LM (pull s hs (displacement (smoothAtlas f hf LM) (classMap f hf LM p) q)) p := rfl

/-- The second coordinate is the complementary section-kernel part of the same displacement. -/
theorem equiv_snd (p : PhysicalClass IB K L n) (q : ConstructedPullbackSpinCriterion.Classes IX n f L) :
    letI := chartedSpace HX LorentzManifold.Model f L
    (equiv f hf s hs hr LM p q).2 = SpinHOneSectionSplit.residual f hf s hs hr
      (displacement (smoothAtlas f hf LM) (classMap f hf LM p) q) := rfl

/-- The inverse twists the pulled physical class by the given kernel sign. -/
theorem equiv_symm_pair (p c : PhysicalClass IB K L n) (k : (pull s hs).ker) :
    letI := chartedSpace HX LorentzManifold.Model f L
    (equiv f hf s hs hr LM p).symm (c, k) = act (smoothAtlas f hf LM) k.val (classMap f hf LM c) := by
  let := chartedSpace HX LorentzManifold.Model f L
  let FM := smoothAtlas f hf LM
  change act FM ((SpinHOneSectionSplit.equiv f hf s hs hr).symm (displacement LM p c, k))
      (classMap f hf LM p) = _
  rw [SpinHOneSectionSplit.equiv_symm_apply_ker_first, act_mul]
  exact congrArg (act FM k.val) (SpinPullbackTorsor.classMap_in_coordinates f hf LM p c).symm

/-- Pulled classes have their original class as first coordinate and the neutral residual sign. -/
theorem equiv_classMap (p c : PhysicalClass IB K L n) :
    equiv f hf s hs hr LM p (classMap f hf LM c) = (c, 1) := by
  let := chartedSpace HX LorentzManifold.Model f L
  apply (equiv f hf s hs hr LM p).symm.injective
  rw [Equiv.symm_apply_apply, equiv_symm_pair]
  exact (act_one (smoothAtlas f hf LM) _).symm

/-- Changing the original reference class preserves the full physical coordinate equivalence. -/
theorem equiv_independent (p r : PhysicalClass IB K L n) :
    equiv f hf s hs hr LM p = equiv f hf s hs hr LM r := by
  let := chartedSpace HX LorentzManifold.Model f L
  have h : (equiv f hf s hs hr LM p).symm = (equiv f hf s hs hr LM r).symm := by
    ext ⟨c, k⟩
    exact (equiv_symm_pair f hf s hs hr LM p c k).trans (equiv_symm_pair f hf s hs hr LM r c k).symm
  exact congrArg Equiv.symm h

end FoliationQM.SpinPullbackBasedSectionSplit
