module
public import FoliationQM.GlobalSpinClassificationCriterion
public import FoliationQM.PuncturedPlaneGlobalSign

/-!
# Uniqueness and multiplicity of smooth Spin lifts on specified bases

For the Spin-frame component of v13 `prop:takabayasi`, singleton
neighborhoods on a discrete base detect every global sign and have only
neutral overlap classes. On the punctured plane the explicit global sign
instead gives a second physical class for every target admitting a lift.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.SpinClassificationExamples
open SpinAllCoverHOne SpinSignHOne SpinHOneDirected GlobalSpinClassificationCriterion

section Discrete
universe u
variable {E H EP HP : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  {B : Type u} [TopologicalSpace B] [DiscreteTopology B] [ChartedSpace H B] {I : ModelWithCorners ℝ E H}
  {P ι : Type*} [TopologicalSpace P] [ChartedSpace HP P] {KP : ModelWithCorners ℝ EP HP}
  {proj : P → B} {L : GeometricPrincipalAtlas.Data (G := LorentzMatrixGroup.ProperFutureLorentz) proj ι}
  {n : WithTop ℕ∞}

/-- A discrete base has trivial all-cover degree-one sign cohomology. -/
theorem discrete_subsingleton : Subsingleton (GlobalH1 I B n) := by
  let D : Cover B := ⟨fun i => ⟨{i}, isOpen_discrete _⟩, fun _ => rfl⟩
  have hD (c : H1 I D.domain n) : c = 1 := by
    obtain ⟨z, rfl⟩ := classOf_surjective c
    rw [← classOf_unit I D.domain n]
    apply classOf_eq_of_overlap
    intro i j x hi hj
    have he : i = j := (Set.mem_singleton_iff.mp hi).symm.trans (Set.mem_singleton_iff.mp hj)
    rw [← he]
    exact z.val.identity i x hi
  have neutral (g : GlobalH1 I B n) : g = 1 := by
    obtain ⟨C, c, rfl⟩ := exists_representative g
    have h : C ≤ D := fun i _ hx => (Set.mem_singleton_iff.mp hx).symm ▸ C.mem i
    rw [← ofPoint_transition h, hD (transition I n C D h c), map_one]
  exact ⟨fun g k => (neutral g).trans (neutral k).symm⟩

/-- On a discrete base, existence of a smooth lift gives precisely one physical class. -/
theorem discrete_unique_iff [IsManifold I n B]
    (LM : GeometricPrincipalSmoothAtlas.Data I CliffordSpinLorentzSmooth.lorentzModel KP L n) :
    (∃! _p : SmoothSpinRelativeClass.PhysicalClass I KP L n, True) ↔
    Nonempty (GeometricSpinObstruction.SmoothLift I KP L n) := by
  rw [unique_iff LM]
  exact ⟨And.left, fun h => ⟨h, discrete_subsingleton⟩⟩

end Discrete

section Plane
open PuncturedPlaneSignCover SmoothSpinRelativeClass SmoothSpinHOneTorsor GeometricSpinObstruction
variable {EP HP P ι : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  [TopologicalSpace HP] [TopologicalSpace P] [ChartedSpace HP P]
  {KP : ModelWithCorners ℝ EP HP} {proj : P → Plane}
  {L : GeometricPrincipalAtlas.Data (G := LorentzMatrixGroup.ProperFutureLorentz) proj ι}
  {n : WithTop ℕ∞} (LM : GeometricPrincipalSmoothAtlas.Data model CliffordSpinLorentzSmooth.lorentzModel KP L n)

include LM

/-- Every physical class over any punctured-plane Lorentz target has a distinct partner. -/
theorem plane_distinct_partner (p : PhysicalClass model KP L n) :
    ∃ q : PhysicalClass model KP L n, q ≠ p :=
  ⟨act LM (PuncturedPlaneGlobalSign.sign n) p, fun h =>
    PuncturedPlaneGlobalSign.sign_ne_one n ((act_eq_self_iff LM _ p).mp h)⟩

/-- A punctured-plane Lorentz target has at least two physical classes exactly when it admits a smooth Spin lift. -/
theorem plane_nontrivial_iff : Nontrivial (PhysicalClass model KP L n) ↔
    Nonempty (SmoothLift model KP L n) := by
  constructor
  · rintro ⟨⟨p, _, _⟩⟩
    exact nonempty_physical_iff.mp ⟨p⟩
  · rintro ⟨A⟩
    obtain ⟨q, hq⟩ := plane_distinct_partner LM (physicalClass A)
    exact ⟨⟨q, physicalClass A, hq⟩⟩

end Plane
end FoliationQM.SpinClassificationExamples
