module
public import FoliationQM.SpinPullbackDisplacement
public import FoliationQM.SmoothSpinHOneTorsor
public import Mathlib.GroupTheory.GroupAction.Hom

/-!
# Pullback of the degree-one action on physical Spin classes

For the smooth Spin classification supporting v13 `prop:takabayasi`,
pullback intertwines twisting a physical class with pulling the sign
to the new base. A reference lift and its pullback give commuting
classification maps in both directions.
-/

@[expose] public section
noncomputable section
open scoped Manifold
namespace FoliationQM.SpinPullbackTorsor
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
  {IX : ModelWithCorners ℝ EX HX} {IB : ModelWithCorners ℝ EB HB} {K : ModelWithCorners ℝ ET HT}
  {n : WithTop ℕ∞} {proj : T → B} {L : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι}
  [IsManifold IX n X] [IsManifold IB n B] (f : C(X, B)) (hf : ContMDiff IX IB n f)
  (LM : GeometricPrincipalSmoothAtlas.Data IB lorentzModel K L n)

/-- Pulling a twisted physical class back gives the twist of its pullback by the pulled sign. -/
theorem classMap_act (g : GlobalH1 IB B n) (p : PhysicalClass IB K L n) :
    letI := chartedSpace HX LorentzManifold.Model f L
    classMap f hf LM (act LM g p) =
      act (smoothAtlas f hf LM) (pull f hf g) (classMap f hf LM p) := by
  let := chartedSpace HX LorentzManifold.Model f L
  apply ((act_eq_iff (smoothAtlas f hf LM) _ _ _).mpr ?_).symm
  exact (SpinPullbackDisplacement.displacement_pullback f hf LM p (act LM g p)).trans
    (congrArg (pull f hf) (displacement_act LM g p))

/-- Classifying with a reference and then pulling back agrees with first pulling the sign back. -/
theorem basedEquiv_natural (p : PhysicalClass IB K L n) :
    letI := chartedSpace HX LorentzManifold.Model f L
    classMap f hf LM ∘ basedEquiv LM p =
      basedEquiv (smoothAtlas f hf LM) (classMap f hf LM p) ∘ pull f hf :=
  funext (fun g => classMap_act f hf LM g p)

/-- Measuring the class relative to the pulled reference gives the pullback of its old coordinate. -/
theorem basedEquiv_symm_natural (p : PhysicalClass IB K L n) :
    letI := chartedSpace HX LorentzManifold.Model f L
    (basedEquiv (smoothAtlas f hf LM) (classMap f hf LM p)).symm ∘ classMap f hf LM =
      pull f hf ∘ (basedEquiv LM p).symm :=
  funext (fun q => SpinPullbackDisplacement.displacement_pullback f hf LM p q)

/-- Any chosen reference expresses the pulled class directly in terms of the original displacement. -/
theorem classMap_in_coordinates (p q : PhysicalClass IB K L n) :
    letI := chartedSpace HX LorentzManifold.Model f L
    classMap f hf LM q =
      basedEquiv (smoothAtlas f hf LM) (classMap f hf LM p) (pull f hf (displacement LM p q)) := by
  let := chartedSpace HX LorentzManifold.Model f L
  exact (congrArg (classMap f hf LM) (act_displacement LM p q)).symm.trans
    (classMap_act f hf LM (displacement LM p q) p)

/-- An inhabited Spin lift space makes the pullback an equivariant map of the two actual torsors. -/
def torsorHom (h : Nonempty (SmoothLift IB K L n)) :
    letI := chartedSpace HX LorentzManifold.Model f L
    letI := torsor LM h
    letI := torsor (smoothAtlas f hf LM) (h.map (GeometricSpinPullback.lift f hf LM))
    MulActionHom (pull f hf) (PhysicalClass IB K L n) (ConstructedPullbackSpinCriterion.Classes IX n f L) := by
  let := chartedSpace HX LorentzManifold.Model f L
  let := torsor LM h
  let := torsor (smoothAtlas f hf LM) (h.map (GeometricSpinPullback.lift f hf LM))
  exact ⟨classMap f hf LM, classMap_act f hf LM⟩

/-- The bundled torsor map evaluates to the physical class of the pulled lift. -/
theorem torsorHom_apply (h : Nonempty (SmoothLift IB K L n)) (p : PhysicalClass IB K L n) :
    letI := chartedSpace HX LorentzManifold.Model f L
    letI := torsor LM h
    letI := torsor (smoothAtlas f hf LM) (h.map (GeometricSpinPullback.lift f hf LM))
    torsorHom f hf LM h p = classMap f hf LM p := rfl

end FoliationQM.SpinPullbackTorsor
