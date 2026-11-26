module
public import FoliationQM.SpinPullbackBasedSectionSplit
public import FoliationQM.SpinPullbackDescent

/-!
# A reference-free decomposition of split physical pullback

For the Spin-frame component of v13 `prop:takabayasi`, a smooth section
of the base map splits the physical class space on the pulled Lorentz
bundle as original classes times the kernel of restriction along the
section. Each given target class supplies a recovered class for computing
its coordinates. The inverse twists the pullback of the original class
by exactly the specified kernel sign, independently of the reference.
-/

@[expose] public section
noncomputable section
open scoped Manifold
namespace FoliationQM.SpinPullbackSectionSplit
open CliffordSpinLorentzSmooth LorentzMatrixGroup SmoothSpinRelativeClass SmoothSpinHOneTorsor
open SpinPullbackClasses SpinPullbackDescent SpinHOneGlobalPullback SmoothPullbackChartedSpace SmoothPrincipalPullback

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
  [IsManifold IX n X] [IsManifold IB n B] (f : C(X, B)) (hf : ContMDiff IX IB n f)
  (s : C(B, X)) (hs : ContMDiff IB IX n s) (hr : Function.RightInverse s f)
  (LM : GeometricPrincipalSmoothAtlas.Data IB lorentzModel K L n)

/-- Twist the pullback of the given original class by a sign that vanishes on the section. -/
def assemble (c : PhysicalClass IB K L n) (k : (pull s hs).ker) :
    ConstructedPullbackSpinCriterion.Classes IX n f L :=
  letI := chartedSpace HX LorentzManifold.Model f L
  act (smoothAtlas f hf LM) k.val (classMap f hf LM c)

/-- Split the physical pullback into an original class and a kernel sign without choosing a global reference. -/
def equiv : ConstructedPullbackSpinCriterion.Classes IX n f L ≃ PhysicalClass IB K L n × (pull s hs).ker := by
  let := chartedSpace HX LorentzManifold.Model f L
  let p := recover LM f s hf hs hr
  let E := SpinPullbackBasedSectionSplit.equiv f hf s hs hr LM
  let a (v : PhysicalClass IB K L n × (pull s hs).ker) := assemble f hf s hs LM v.1 v.2
  have inv (b) (v) : (E b).symm v = a v := by
    obtain ⟨c, k⟩ := v
    exact SpinPullbackBasedSectionSplit.equiv_symm_pair f hf s hs hr LM b c k
  exact
    { toFun := fun q => E (p q) q
      invFun := a
      left_inv := fun q => (inv (p q) _).symm.trans ((E (p q)).symm_apply_apply q)
      right_inv := fun v => (congrArg (E (p (a v))) (inv (p (a v)) v).symm).trans
        ((E (p (a v))).apply_symm_apply v) }

/-- The inverse split map is the literal twist of the physical pullback by its residual sign. -/
theorem equiv_symm_pair (c : PhysicalClass IB K L n) (k : (pull s hs).ker) :
    (equiv f hf s hs hr LM).symm (c, k) = assemble f hf s hs LM c k := rfl

/-- Computing the split with any supplied original reference recovers the same equivalence. -/
theorem equiv_eq_based (p : PhysicalClass IB K L n) :
    equiv f hf s hs hr LM = SpinPullbackBasedSectionSplit.equiv f hf s hs hr LM p := by
  have h : (equiv f hf s hs hr LM).symm = (SpinPullbackBasedSectionSplit.equiv f hf s hs hr LM p).symm := by
    ext ⟨c, k⟩
    exact (SpinPullbackBasedSectionSplit.equiv_symm_pair f hf s hs hr LM p c k).symm
  exact congrArg Equiv.symm h

/-- Splitting the twist of a pulled original class recovers both inputs. -/
theorem equiv_assemble (c : PhysicalClass IB K L n) (k : (pull s hs).ker) :
    equiv f hf s hs hr LM (assemble f hf s hs LM c k) = (c, k) :=
  (equiv f hf s hs hr LM).apply_symm_apply (c, k)

/-- Actual pullback embeds as the pairs with neutral residual sign. -/
theorem equiv_classMap (c : PhysicalClass IB K L n) :
    equiv f hf s hs hr LM (classMap f hf LM c) = (c, 1) := by
  let := chartedSpace HX LorentzManifold.Model f L
  exact (congrArg (equiv f hf s hs hr LM)
    (act_one (smoothAtlas f hf LM) (classMap f hf LM c)).symm).trans (equiv_assemble f hf s hs hr LM c 1)

end FoliationQM.SpinPullbackSectionSplit
