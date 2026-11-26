module
public import FoliationQM.SpinPullbackSectionDescent

/-!
# Recovering the physical coordinates by restricting along the section

For the frame component of v13 `prop:takabayasi`, the first coordinate
of the split physical pullback is its geometric recovery along the section.
The second is measured by the displacement from the pullback of that
recovered class. Geometric recovery therefore carries physical twists
and relative displacements to their restrictions along the section.
-/

@[expose] public section
noncomputable section
open scoped Manifold
namespace FoliationQM.SpinPullbackSectionRecovery
open CliffordSpinLorentzSmooth LorentzMatrixGroup SmoothSpinRelativeClass GlobalSpinDisplacement
open SmoothSpinHOneTorsor SpinAllCoverHOne SpinPullbackClasses SpinPullbackDescent
open GeometricPrincipalPullback SmoothPrincipalPullback SmoothPullbackChartedSpace
open SpinHOneGlobalPullback SpinPullbackSectionSplit

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

/-- The target identifications in geometric recovery preserve and reflect equality of the classes pulled
along the section. -/
theorem section_eq_iff (q r : ConstructedPullbackSpinCriterion.Classes IX n f L) :
    letI := chartedSpace HX LorentzManifold.Model f L
    classMap s hs (smoothAtlas f hf LM) q = classMap s hs (smoothAtlas f hf LM) r ↔
      recover LM f s hf hs hr q = recover LM f s hf hs hr r := by
  let := chartedSpace HX LorentzManifold.Model f L
  let := chartedSpace HB LorentzManifold.Model s (atlas f L)
  let := chartedSpace HB LorentzManifold.Model (f.comp s) L
  let E := (SpinPullbackTargetComparisons.composeIso f s hf hs LM).classEquiv (I := IB)
  let D := identifyId LM (f.comp s) (ContinuousMap.ext hr)
  change classMap s hs (smoothAtlas f hf LM) q = classMap s hs (smoothAtlas f hf LM) r ↔
    D (E (classMap s hs (smoothAtlas f hf LM) q)) = D (E (classMap s hs (smoothAtlas f hf LM) r))
  exact ⟨fun h => congrArg (fun c => D (E c)) h, fun h => E.injective (D.injective h)⟩

/-- The displacement from the pullback of the geometrically recovered class restricts to one on the section. -/
theorem section_displacement_one (q : ConstructedPullbackSpinCriterion.Classes IX n f L) :
    letI := chartedSpace HX LorentzManifold.Model f L
    pull s hs (displacement (smoothAtlas f hf LM) (classMap f hf LM (recover LM f s hf hs hr q)) q) = 1 := by
  let := chartedSpace HX LorentzManifold.Model f L
  let := chartedSpace HB LorentzManifold.Model s (atlas f L)
  let FM := smoothAtlas f hf LM
  let p := recover LM f s hf hs hr q
  have h := (section_eq_iff f hf s hs hr LM (classMap f hf LM p) q).mpr
    (recover_leftInverse LM f s hf hs hr p)
  exact (SpinPullbackDisplacement.displacement_pullback s hs FM (classMap f hf LM p) q).symm.trans
    ((displacement_one_iff (smoothAtlas s hs FM) _ _).mpr h)

/-- The first coordinate of the physical splitting equals geometric recovery along the smooth section. -/
theorem equiv_fst_eq_recover (q : ConstructedPullbackSpinCriterion.Classes IX n f L) :
    (equiv f hf s hs hr LM q).1 = recover LM f s hf hs hr q := by
  let := chartedSpace HX LorentzManifold.Model f L
  let p := recover LM f s hf hs hr q
  rw [equiv_eq_based f hf s hs hr LM p, SpinPullbackBasedSectionSplit.equiv_fst,
    section_displacement_one f hf s hs hr LM q, act_one]

/-- The second coordinate is precisely the physical displacement from the pullback of the recovered original class. -/
theorem equiv_snd_val (q : ConstructedPullbackSpinCriterion.Classes IX n f L) :
    letI := chartedSpace HX LorentzManifold.Model f L
    (equiv f hf s hs hr LM q).2.val =
      displacement (smoothAtlas f hf LM) (classMap f hf LM (recover LM f s hf hs hr q)) q := by
  let := chartedSpace HX LorentzManifold.Model f L
  let p := recover LM f s hf hs hr q
  rw [equiv_eq_based f hf s hs hr LM p, SpinPullbackBasedSectionSplit.equiv_snd,
    SpinHOneSectionSplit.residual_val, section_displacement_one f hf s hs hr LM q, map_one, div_one]

/-- Recovery of a class assembled from an original class and a section-kernel sign returns that original class. -/
theorem recover_assemble (p : PhysicalClass IB K L n) (k : (pull s hs).ker) :
    recover LM f s hf hs hr (assemble f hf s hs LM p k) = p :=
  (equiv_fst_eq_recover f hf s hs hr LM _).symm.trans (congrArg Prod.fst (equiv_assemble f hf s hs hr LM p k))

/-- Geometric recovery carries every physical twist to the twist by the restriction of its sign. -/
theorem recover_act (h : GlobalH1 IX X n) (q : ConstructedPullbackSpinCriterion.Classes IX n f L) :
    letI := chartedSpace HX LorentzManifold.Model f L
    recover LM f s hf hs hr (act (smoothAtlas f hf LM) h q) =
      act LM (pull s hs h) (recover LM f s hf hs hr q) := by
  let := chartedSpace HX LorentzManifold.Model f L
  exact (equiv_fst_eq_recover f hf s hs hr LM _).symm.trans
    ((congrArg Prod.fst (SpinPullbackSectionDescent.equiv_act f hf s hs hr LM h q)).trans
      (congrArg (act LM (pull s hs h)) (equiv_fst_eq_recover f hf s hs hr LM q)))

/-- Recovery carries displacement between arbitrary target classes to the original-base displacement
given by restriction along the section. -/
theorem recover_displacement (q r : ConstructedPullbackSpinCriterion.Classes IX n f L) :
    letI := chartedSpace HX LorentzManifold.Model f L
    displacement LM (recover LM f s hf hs hr q) (recover LM f s hf hs hr r) =
      pull s hs (displacement (smoothAtlas f hf LM) q r) := by
  let := chartedSpace HX LorentzManifold.Model f L
  let FM := smoothAtlas f hf LM
  let h := displacement FM q r
  have he : recover LM f s hf hs hr r = act LM (pull s hs h) (recover LM f s hf hs hr q) :=
    (congrArg (recover LM f s hf hs hr) (act_displacement FM q r)).symm.trans
      (recover_act f hf s hs hr LM h q)
  exact (congrArg (displacement LM (recover LM f s hf hs hr q)) he).trans (displacement_act LM _ _)

end FoliationQM.SpinPullbackSectionRecovery
