module
public import FoliationQM.GlobalSpinPresentationFormula

/-!
# Realizing all-cover sign classes by geometric twists

For the global Spin-frame component of v13 `prop:takabayasi`, intersect
the adapted charts of a reference Spin lift with the charts presenting a
sign cocycle. Twist the actual Spin transitions there, realize their
principal bundle, and use the resulting physical map to the original
Lorentz space. Its relative sign recovers the specified global class.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GlobalSpinRealization
open CliffordSpinLorentzSmooth LorentzMatrixGroup GeometricSpinObstruction SpinLiftIsomorphism
open CliffordSpinCoverRefinement RefinedGeometricPrincipalAtlas JointSpinAdaptation
open SpinAllCoverHOne SpinSignHOne SpinSignOneCocycle SpinLiftSignDifference
open SpinHOneRestriction GlobalSpinDisplacement SmoothSpinRelativeClass

universe u
variable {E H EP HP : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  {B : Type u} [TopologicalSpace B] [ChartedSpace H B] {I : ModelWithCorners ℝ E H}
  {P ι : Type*} [TopologicalSpace P] [ChartedSpace HP P] {KP : ModelWithCorners ℝ EP HP}
  {proj : P → B} {L : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι}
  {n : WithTop ℕ∞} (LM : GeometricPrincipalSmoothAtlas.Data I lorentzModel KP L n)
  (A : SmoothLift I KP L n) (C : SpinHOneDirected.Cover B)

/-- Intersect each adapted neighborhood of the reference lift with the corresponding sign domain. -/
def support : SpinHOneDirected.Cover B :=
  ⟨fun i => neighborhood LM A i ⊓ C.domain i, fun i => ⟨mem_neighborhood LM A i, C.mem i⟩⟩

/-- These common neighborhoods refine the Lorentz atlas with its aligned target parents. -/
def targetRefinement : Refinement (domains L) B :=
  (support LM A C).asRefinement (targetChart L) (fun _ _ hx => hx.1.1.2)

/-- The same neighborhoods refine the cover presenting the sign through the identity parents. -/
def signRefinement : Refinement C.domain B :=
  (support LM A C).asRefinement id (fun _ => inf_le_right)

/-- The actual reference lift in the smaller, jointly adapted charts. -/
def adapted : GeometricSpinStructure.Lift I (restrictedAtlas L (targetRefinement LM A C)) n :=
  adaptOn LM A (targetRefinement LM A C) (fun _ => rfl) (fun _ _ hx => hx.1)

variable [IsManifold I n B]

/-- Realize the twist of the extracted reference Spin transitions by the restricted sign cocycle. -/
def twisted (z : Cocycle I C.domain n) : SmoothLift I KP L n :=
  let R := targetRefinement LM A C
  let M := restrictedSmoothAtlas LM R
  ofRefined LM R (realize M (twist (transitions M (adapted LM A C))
    (restrictCocycle (signRefinement LM A C) z)))

/-- The smooth lift obtained from the twisted principal bundle has exactly the requested global sign. -/
theorem relative_twisted (z : Cocycle I C.domain n) :
    relative LM A (twisted LM A C z) = ofPoint C (classOf z) := by
  let R := targetRefinement LM A C
  let S := signRefinement LM A C
  let M := restrictedSmoothAtlas LM R
  let G := adapted LM A C
  let F := transitions M G
  let w := restrictCocycle S z
  let T := realize M (twist F w)
  have same : Nonempty (SmoothBetween A (ofRefined LM R G)) :=
    ⟨⟨Diffeomorph.refl _ _ _, fun _ _ => rfl, fun _ => rfl⟩⟩
  have hd : classOf (difference F (transitions M T)) = classOf w :=
    ((SpinLiftChartGauge.gaugeEq_iff_based F _ _).mp
      (SpinLiftChartGauge.gaugeEq_of_agree (transitions_realize M (twist F w)))).trans
        (classOf_eq_of_overlap (SpinLiftOverlapTorsor.difference_twist F w))
  change relative LM A (ofRefined LM R T) = _
  apply (relative_congr LM same (iso_equivalence.refl _)).trans
  apply (GlobalSpinPresentationFormula.relative_ofRefined LM R (fun _ => rfl) (support LM A C).mem G T).trans
  apply (congrArg (ofCover R.domain R.covers) hd).trans
  exact (ofCover_restrict C.covers S (classOf z)).trans (ofCover_point C (classOf z))

variable {κ : Type*} (U : κ → TopologicalSpace.Opens B) (hU : ∀ x : B, ∃ i, x ∈ U i)

/-- Realize the geometric twist even when the input cover uses an unrelated index type or universe. -/
def twistedFromCover (z : Cocycle I U n) : SmoothLift I KP L n :=
  twisted LM A (SpinHOneDirected.anchor U hU)
    (restrictCocycle (SignCommonRefinement.pointCover U hU) z)

/-- The displacement of the twist from any supplied open cover is its canonical all-cover image. -/
theorem relative_twistedFromCover (z : Cocycle I U n) :
    relative LM A (twistedFromCover LM A U hU z) = ofCover U hU (classOf z) :=
  relative_twisted LM A (SpinHOneDirected.anchor U hU)
    (restrictCocycle (SignCommonRefinement.pointCover U hU) z)

/-- Every all-cover class occurs as the geometric displacement of a smooth lift from the given reference. -/
theorem exists_relative (g : GlobalH1 I B n) :
    ∃ T : SmoothLift I KP L n, relative LM A T = g := by
  obtain ⟨C, c, rfl⟩ := exists_representative g
  obtain ⟨z, rfl⟩ := classOf_surjective c
  exact ⟨twisted LM A C z, relative_twisted LM A C z⟩

/-- Displacement from any physical isomorphism class surjects onto the global sign group. -/
theorem surjective (p : PhysicalClass I KP L n) : Function.Surjective (displacement LM p) := by
  refine Quotient.inductionOn p ?_
  intro A g
  obtain ⟨T, hT⟩ := exists_relative LM A g
  exact ⟨physicalClass T, hT⟩

end FoliationQM.GlobalSpinRealization
