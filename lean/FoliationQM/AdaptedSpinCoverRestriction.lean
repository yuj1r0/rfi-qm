module
public import FoliationQM.SmoothSpinRelativeClass

/-!
# Restricting an adapted Spin structure together with its Lorentz atlas

For the geometric component of v13 `prop:takabayasi`, shrinking both
sets of principal charts retains the physical total spaces and maps.
The extracted Spin transitions are precisely the parent transitions.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace FoliationQM.AdaptedSpinCoverRestriction
open CliffordSpinCoverRefinement RefinedGeometricPrincipalAtlas
open CliffordSpinLorentzSmooth LorentzMatrixGroup SpinLiftIsomorphism

universe u
variable {E H EP HP : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  {B : Type u} [TopologicalSpace B] [ChartedSpace H B] {I : ModelWithCorners ℝ E H}
  {P ι κ : Type*} [TopologicalSpace P] [ChartedSpace HP P] {KP : ModelWithCorners ℝ EP HP}
  {proj : P → B} {L : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι}
  {n : WithTop ℕ∞}

/-- Restrict an adapted Spin atlas and its target to the same smaller opens with the same parents. -/
def restrict (A : GeometricSpinStructure.Lift I L n) (R : Refinement (domains L) κ) :
    GeometricSpinStructure.Lift I (restrictedAtlas L R) n :=
  let S : Refinement (domains A.atlas) κ :=
    { parent := R.parent, domain := R.domain, covers := R.covers
      subset := fun i x hx => by
        change x ∈ (A.atlas.triv (R.parent i)).baseSet
        rw [A.adapted.domain_eq]
        exact R.subset i hx }
  { Carrier := A.Carrier
    proj := A.proj
    atlas := restrictedAtlas A.atlas S
    smoothAtlas := restrictedSmoothAtlas A.smoothAtlas S
    map := { toFun := A.map, continuous_toFun := A.map.continuous_toFun,
             proj := A.map.proj, equivariant := A.map.equivariant }
    adapted := { domain_eq := fun _ => rfl
                 unit := fun i x hx => A.adapted.unit (R.parent i) x (R.subset i hx) } }

variable (LM : GeometricPrincipalSmoothAtlas.Data I lorentzModel KP L n)

/-- Extraction after simultaneous restriction gives the restriction of the original Spin transitions. -/
theorem transition_agree (A : GeometricSpinStructure.Lift I L n) (R : Refinement (domains L) κ) :
    SpinLiftOverlapTorsor.Agree (transitions (restrictedSmoothAtlas LM R) (restrict A R))
      (SpinLiftClassRestriction.restrictLift (D := AdaptedGeometricSpinLift.lorentzData LM) R (transitions LM A)) :=
  fun _ _ _ _ _ => rfl

/-- Reindexing the two lifts preserves the cohomology class of the physical transition ratio. -/
theorem difference_restrict (A T : GeometricSpinStructure.Lift I L n) (R : Refinement (domains L) κ) :
    SpinSignHOne.classOf (SpinLiftSignDifference.difference
      (transitions (restrictedSmoothAtlas LM R) (restrict A R))
      (transitions (restrictedSmoothAtlas LM R) (restrict T R))) =
    SpinHOneRestriction.restrictHom R (SpinSignHOne.classOf
      (SpinLiftSignDifference.difference (transitions LM A) (transitions LM T))) :=
  (SpinSignHOne.classOf_eq_of_overlap (SpinLiftOverlapTorsor.difference_congr
    (transition_agree LM A R) (transition_agree LM T R))).trans
      (SpinLiftClassRestriction.restrict_differenceClass (D := AdaptedGeometricSpinLift.lorentzData LM) R (transitions LM A) (transitions LM T)).symm

end FoliationQM.AdaptedSpinCoverRestriction
