module
public import FoliationQM.SpinPullbackImage
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The quotient of degree one parametrizes the physical pullback image

For the Spin-frame component of v13 `prop:takabayasi`, a reference
physical class identifies the attainable pulled classes with the image
of the H¹ homomorphism. The first isomorphism theorem then identifies
them with the original sign group modulo the signs lost under pullback.
-/

@[expose] public section
noncomputable section
open scoped Manifold
namespace FoliationQM.SpinPullbackImageQuotient
open CliffordSpinLorentzSmooth LorentzMatrixGroup GeometricSpinObstruction
open SmoothSpinRelativeClass SmoothSpinHOneTorsor SpinAllCoverHOne GlobalSpinDisplacement
open SpinPullbackClasses SpinHOneGlobalPullback SmoothPullbackChartedSpace SmoothPrincipalPullback

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
  (LM : GeometricPrincipalSmoothAtlas.Data IB lorentzModel K L n) (p : PhysicalClass IB K L n)

/-- Starting at the pulled reference identifies the range of degree one with the actual image on physical classes. -/
def rangeEquiv : (pull f hf).range ≃ Set.range (classMap f hf LM) := by
  let := chartedSpace HX LorentzManifold.Model f L
  exact
    { toFun := fun g => ⟨act (smoothAtlas f hf LM) g.val (classMap f hf LM p), by
        obtain ⟨h, hh⟩ := g.property
        exact ⟨act LM h p, (SpinPullbackTorsor.classMap_act f hf LM h p).trans
          (congrArg (fun t => act (smoothAtlas f hf LM) t (classMap f hf LM p)) hh)⟩⟩
      invFun := fun q => ⟨displacement (smoothAtlas f hf LM) (classMap f hf LM p) q.val,
        (SpinPullbackImage.mem_range_iff f hf LM p q.val).mp q.property⟩
      left_inv := fun g => Subtype.ext (displacement_act (smoothAtlas f hf LM) g.val (classMap f hf LM p))
      right_inv := fun q => Subtype.ext (act_displacement (smoothAtlas f hf LM) (classMap f hf LM p) q.val) }

/-- The inverse image coordinate is measured by physical displacement from the pulled reference. -/
theorem rangeEquiv_symm_apply (q : Set.range (classMap f hf LM)) :
    letI := chartedSpace HX LorentzManifold.Model f L
    ((rangeEquiv f hf LM p).symm q).val =
      displacement (smoothAtlas f hf LM) (classMap f hf LM p) q.val := rfl

/-- The group of original signs modulo the pullback kernel is equivalent to the attainable physical classes. -/
def quotientEquiv : GlobalH1 IB B n ⧸ (pull f hf).ker ≃ Set.range (classMap f hf LM) :=
  (QuotientGroup.quotientKerEquivRange (pull f hf)).toEquiv.trans (rangeEquiv f hf LM p)

/-- The coset of a sign maps to the physical pullback of its twist of the reference. -/
theorem quotientEquiv_mk (g : GlobalH1 IB B n) :
    (quotientEquiv f hf LM p (QuotientGroup.mk g)).val = classMap f hf LM (act LM g p) :=
  (SpinPullbackTorsor.classMap_act f hf LM g p).symm

/-- The neutral coset corresponds to the image of the given reference class itself. -/
theorem quotientEquiv_one : (quotientEquiv f hf LM p 1).val = classMap f hf LM p := by
  exact (quotientEquiv_mk f hf LM p 1).trans (congrArg (classMap f hf LM) (act_one LM p))

end FoliationQM.SpinPullbackImageQuotient
