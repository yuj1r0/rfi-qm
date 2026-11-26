module
public import FoliationQM.JointSpinAdaptation
public import FoliationQM.SpinLiftClassRestriction
public import FoliationQM.SpinGeometricLiftClasses

/-!
# The relative sign class of independently charted smooth Spin lifts

Source scope: the geometric Spin-frame component of v13 `prop:takabayasi`.
A common adapted cover permits comparison of two smooth lifts over the
same physical Lorentz bundle. The isomorphism test uses their original
maps and principal actions. It can be performed on any further refinement.
-/

@[expose] public section
noncomputable section
open scoped Manifold
namespace FoliationQM.SmoothSpinRelativeClass
open CliffordSpinLorentzSmooth LorentzMatrixGroup GeometricSpinObstruction SpinLiftIsomorphism
open SpinSignHOne SpinLiftSignDifference RefinedGeometricPrincipalAtlas JointSpinAdaptation

universe u
variable {E H EP HP : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  {B : Type u} [TopologicalSpace B] [ChartedSpace H B] {I : ModelWithCorners ℝ E H}
  {P ι : Type*} [TopologicalSpace P] [ChartedSpace HP P] {KP : ModelWithCorners ℝ EP HP}
  {proj : P → B} {L : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι}
  {n : WithTop ℕ∞}

/-- Smooth physical isomorphisms use the original carriers, Spin actions and Lorentz maps, for independently indexed source atlases. -/
abbrev SmoothBetween (A T : SmoothLift I KP L n) :=
  PhysicalIso (I.prod spinModel) (I.prod spinModel) n A.map T.map A.atlas.right T.atlas.right

/-- Physical isomorphism of independently charted smooth Spin structures is an equivalence relation. -/
theorem iso_equivalence : Equivalence (fun A T : SmoothLift I KP L n => Nonempty (SmoothBetween A T)) where
  refl A := ⟨{ diffeo := Diffeomorph.refl _ _ _, equivariant := fun _ _ => rfl, over := fun _ => rfl }⟩
  symm {A T} := by
    rintro ⟨f⟩
    refine ⟨{ diffeo := f.diffeo.symm, equivariant := ?_, over := ?_ }⟩
    · intro q g
      apply f.diffeo.injective
      change f.diffeo (f.diffeo.symm (T.atlas.right q g)) = f.diffeo (A.atlas.right (f.diffeo.symm q) g)
      rw [f.equivariant, f.diffeo.apply_symm_apply, f.diffeo.apply_symm_apply]
    · intro q
      rw [← f.over, f.diffeo.apply_symm_apply]
  trans {A T S} := by
    rintro ⟨f⟩ ⟨g⟩
    refine ⟨{ diffeo := f.diffeo.trans g.diffeo, equivariant := ?_, over := ?_ }⟩
    · intro q s
      exact (congrArg g.diffeo (f.equivariant q s)).trans (g.equivariant _ _)
    · intro q
      exact (g.over (f.diffeo q)).trans (f.over q)

/-- Isomorphism classes of smooth geometric Spin lifts over the fixed original Lorentz space. -/
def PhysicalClass (I : ModelWithCorners ℝ E H) (KP : ModelWithCorners ℝ EP HP)
    (L : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι) (n : WithTop ℕ∞) :=
  Quotient (⟨fun A T => Nonempty (SmoothBetween A T), iso_equivalence⟩ : Setoid (SmoothLift I KP L n))

/-- The class of an independently charted smooth geometric lift. -/
def physicalClass (A : SmoothLift I KP L n) : PhysicalClass I KP L n := Quotient.mk _ A

variable (LM : GeometricPrincipalSmoothAtlas.Data I lorentzModel KP L n)

/-- The degree-one relative sign of two smooth Spin lifts, computed on their constructed common adapted cover. -/
def relativeClass (A T : SmoothLift I KP L n) : H1 I (common LM A T).domain n :=
  let M := restrictedSmoothAtlas LM (common LM A T)
  classOf (difference (transitions M (leftLift LM A T)) (transitions M (rightLift LM A T)))

/-- The computed relative class is neutral exactly when the original smooth Spin lifts are physically isomorphic. -/
theorem nonempty_iff_relative_unit (A T : SmoothLift I KP L n) :
    Nonempty (SmoothBetween A T) ↔ relativeClass LM A T = 1 :=
  SpinGeometricLiftClasses.nonempty_between_iff_neutral
    (restrictedSmoothAtlas LM (common LM A T)) (leftLift LM A T) (rightLift LM A T)

/-- Comparing the relative sign on any further open refinement detects the same physical isomorphisms. -/
theorem nonempty_iff_refined_relative_unit {κ : Type*} (A T : SmoothLift I KP L n)
    (R : CliffordSpinCoverRefinement.Refinement (common LM A T).domain κ) :
    Nonempty (SmoothBetween A T) ↔ SpinHOneRestriction.restrictHom R (relativeClass LM A T) = 1 :=
  (nonempty_iff_relative_unit LM A T).trans (SpinHOneDescent.restrictHom_eq_one_iff R _).symm

/-- The relative class tests equality in the quotient of independently charted geometric Spin structures by physical isomorphism. -/
theorem physicalClass_eq_iff (A T : SmoothLift I KP L n) :
    physicalClass A = physicalClass T ↔ relativeClass LM A T = 1 :=
  Quotient.eq.trans (nonempty_iff_relative_unit LM A T)

/-- Regard an adapted structure as an independently charted lift using a point-indexed restriction of its source charts. -/
def forgetAdaptation (A : GeometricSpinStructure.Lift I L n) : SmoothLift I KP L n :=
  let R := SignCommonRefinement.pointCover (domains A.atlas) A.atlas.covers
  { Carrier := A.Carrier
    Index := B
    proj := A.proj
    atlas := restrictedAtlas A.atlas R
    smoothAtlas := restrictedSmoothAtlas A.smoothAtlas R
    map := { toFun := A.map, continuous_toFun := A.map.continuous_toFun,
             proj := A.map.proj, equivariant := A.map.equivariant }
    smooth_map := A.contMDiff LM }

/-- Classes represented on a specified adapted cover inject into physical isomorphism classes of all smooth lifts over the target. -/
def adaptedEmbedding : SpinGeometricLiftClasses.GeometricClass LM ↪ PhysicalClass I KP L n where
  toFun := Quotient.map (forgetAdaptation LM) (fun _ _ h => h)
  inj' := by
    intro p q
    refine Quotient.inductionOn₂ p q ?_
    intro A T h
    exact Quotient.sound (Quotient.exact h : Nonempty (Between A T))

/-- A reference adapted lift embeds the sign group on its cover into isomorphism classes of independently charted smooth lifts over the same Lorentz target. -/
def basedEmbedding [IsManifold I n B] (A : GeometricSpinStructure.Lift I L n) :
    H1 I (domains L) n ↪ PhysicalClass I KP L n :=
  (SpinGeometricLiftClasses.basedEquiv LM A).toEmbedding.trans (adaptedEmbedding LM)

end FoliationQM.SmoothSpinRelativeClass
