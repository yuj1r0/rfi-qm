module
public import FoliationQM.SpinPullbackSectionSplit

/-!
# Descent and signs for a smooth section

For v13 `prop:takabayasi`, the residual sign in the section split detects
exactly which physical Spin classes descend. The split also determines
how any further global twist changes the two coordinates, using the
restriction and residual of its degree-one class.
-/

@[expose] public section
noncomputable section
open scoped Manifold
namespace FoliationQM.SpinPullbackSectionDescent
open CliffordSpinLorentzSmooth LorentzMatrixGroup SmoothSpinRelativeClass SmoothSpinHOneTorsor
open SpinAllCoverHOne SpinPullbackClasses SpinHOneGlobalPullback SmoothPullbackChartedSpace SmoothPrincipalPullback
open SpinPullbackSectionSplit

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

/-- Reconstruct each physical class from its original-class coordinate and its section-kernel coordinate. -/
theorem reconstruct (q : ConstructedPullbackSpinCriterion.Classes IX n f L) :
    assemble f hf s hs LM (equiv f hf s hs hr LM q).1 (equiv f hf s hs hr LM q).2 = q :=
  (equiv f hf s hs hr LM).symm_apply_apply q

include hr in
/-- Every target physical class has a unique expression as a kernel twist of an actual pulled class. -/
theorem existsUnique_assemble (q : ConstructedPullbackSpinCriterion.Classes IX n f L) :
    ∃! v : PhysicalClass IB K L n × (pull s hs).ker, assemble f hf s hs LM v.1 v.2 = q := by
  let E := equiv f hf s hs hr LM
  exact ⟨E q, E.symm_apply_apply q, fun v hv => E.symm.injective (hv.trans (E.symm_apply_apply q).symm)⟩

/-- A target physical class descends exactly when its residual sign is the identity of the section kernel. -/
theorem mem_range_iff (q : ConstructedPullbackSpinCriterion.Classes IX n f L) :
    q ∈ Set.range (classMap f hf LM) ↔ (equiv f hf s hs hr LM q).2 = 1 := by
  let := chartedSpace HX LorentzManifold.Model f L
  constructor
  · rintro ⟨c, rfl⟩
    exact congrArg Prod.snd (equiv_classMap f hf s hs hr LM c)
  · intro h
    let c := (equiv f hf s hs hr LM q).1
    refine ⟨c, ?_⟩
    calc
      classMap f hf LM c = assemble f hf s hs LM c 1 := (act_one _ _).symm
      _ = assemble f hf s hs LM c (equiv f hf s hs hr LM q).2 := by rw [h]
      _ = q := reconstruct f hf s hs hr LM q

/-- The original-class coordinate retracts the physical pullback map. -/
theorem first_leftInverse : Function.LeftInverse
    (fun q => (equiv f hf s hs hr LM q).1) (classMap f hf LM) :=
  fun c => congrArg Prod.fst (equiv_classMap f hf s hs hr LM c)

/-- A twist changes the original class by its section restriction and multiplies the residual by its kernel component. -/
theorem equiv_act (h : GlobalH1 IX X n) (q : ConstructedPullbackSpinCriterion.Classes IX n f L) :
    letI := chartedSpace HX LorentzManifold.Model f L
    equiv f hf s hs hr LM (act (smoothAtlas f hf LM) h q) =
      (act LM (pull s hs h) (equiv f hf s hs hr LM q).1,
        SpinHOneSectionSplit.residual f hf s hs hr h * (equiv f hf s hs hr LM q).2) := by
  let := chartedSpace HX LorentzManifold.Model f L
  let E := equiv f hf s hs hr LM
  let c := (E q).1
  let k := (E q).2
  let a := SpinHOneSectionSplit.residual f hf s hs hr h
  let b := pull s hs h
  let FM := smoothAtlas f hf LM
  have hq : q = act FM k.val (classMap f hf LM c) := (reconstruct f hf s hs hr LM q).symm
  have ha : pull f hf b * a.val = h := (SpinHOneSectionSplit.equiv f hf s hs hr).symm_apply_apply h
  apply E.symm.injective
  change E.symm (E (act FM h q)) = assemble f hf s hs LM (act LM b c) (a * k)
  rw [E.symm_apply_apply, hq]
  change act FM h (act FM k.val (classMap f hf LM c)) =
    act FM (a.val * k.val) (classMap f hf LM (act LM b c))
  rw [SpinPullbackTorsor.classMap_act, ← act_mul, ← act_mul]
  apply congrArg (fun g => act FM g (classMap f hf LM c))
  calc
    h * k.val = (pull f hf b * a.val) * k.val := by rw [ha]
    _ = a.val * k.val * pull f hf b := by ac_rfl

end FoliationQM.SpinPullbackSectionDescent
