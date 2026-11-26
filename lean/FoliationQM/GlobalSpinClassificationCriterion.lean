module
public import FoliationQM.SmoothSpinHOneTorsor

/-!
# Existence and uniqueness of physical Spin classes

For the geometric Spin-frame component of v13 `prop:takabayasi`, the
degree-two defect of supplied pair lifts tests existence. Once a lift
exists, the all-cover degree-one sign group tests uniqueness. This also
gives a criterion in terms of chart coboundaries on anchored covers.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GlobalSpinClassificationCriterion
open CliffordSpinLorentzSmooth LorentzMatrixGroup GeometricSpinObstruction
open CliffordSpinCoverRefinement CliffordSpinCocycleCorrection CliffordSpinTransitionLifts
open SpinAllCoverHOne SmoothSpinRelativeClass SignEventualObstruction

universe u
variable {E H EP HP : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  {B : Type u} [TopologicalSpace B] [ChartedSpace H B] {I : ModelWithCorners ℝ E H}
  {P ι : Type*} [TopologicalSpace P] [ChartedSpace HP P] {KP : ModelWithCorners ℝ EP HP}
  {proj : P → B} {L : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι}
  {n : WithTop ℕ∞}

/-- The physical quotient is inhabited exactly when the original Lorentz target admits a smooth lift. -/
theorem nonempty_physical_iff :
    Nonempty (PhysicalClass I KP L n) ↔ Nonempty (SmoothLift I KP L n) :=
  nonempty_quotient_iff _

/-- All global signs are neutral precisely when all classes are neutral on each cofinal anchored cover. -/
theorem subsingleton_iff_anchored : Subsingleton (GlobalH1 I B n) ↔
    ∀ C : SpinHOneDirected.Cover B, Subsingleton (SpinSignHOne.H1 I C.domain n) := by
  constructor
  · intro h C
    exact ⟨fun a b => ofPoint_injective C (h.elim (ofPoint C a) (ofPoint C b))⟩
  · intro h
    have neutral (g : GlobalH1 I B n) : g = 1 := by
      obtain ⟨C, c, rfl⟩ := exists_representative g
      rw [(h C).elim c 1, map_one]
    exact ⟨fun g k => (neutral g).trans (neutral k).symm⟩

/-- Global degree one is trivial exactly when every normalized smooth sign cocycle on an
anchored cover is a chart coboundary on the actual pair intersections of that cover. -/
theorem subsingleton_iff_coboundaries : Subsingleton (GlobalH1 I B n) ↔
    ∀ (C : SpinHOneDirected.Cover B) (z : SpinSignOneCocycle.Cocycle I C.domain n),
      ∃ a : SpinSignHOne.ZeroCochain I C.domain n,
        SpinSignOneCocycle.OverlapEq z (SpinSignHOne.coboundary a) := by
  rw [subsingleton_iff_anchored]
  constructor
  · intro h C z
    exact (SpinSignHOne.classOf_eq_one_iff z).mp ((h C).elim _ _)
  · intro h C
    have neutral (c : SpinSignHOne.H1 I C.domain n) : c = 1 := by
      obtain ⟨z, rfl⟩ := SpinSignHOne.classOf_surjective c
      exact (SpinSignHOne.classOf_eq_one_iff z).mpr (h C z)
    exact ⟨fun c d => (neutral c).trans (neutral d).symm⟩

variable (LM : GeometricPrincipalSmoothAtlas.Data I lorentzModel KP L n) [hB : IsManifold I n B]

/-- A witness of existence permits a choice of origin for the global classification. -/
def equiv_of_nonempty (h : Nonempty (SmoothLift I KP L n)) :
    GlobalH1 I B n ≃ PhysicalClass I KP L n :=
  SmoothSpinHOneTorsor.basedEquiv LM (physicalClass h.some)

/-- A genuine lifted Lorentz cocycle on one refinement makes the physical classes an all-cover torsor. -/
@[instance_reducible] def torsor_of_refinement
    (R : Refinement (AdaptedGeometricSpinLift.lorentzData LM).domain B)
    (hR : HasSpinCocycleLift (lorentzData (AdaptedGeometricSpinLift.lorentzData LM) R)) :
    Torsor (GlobalH1 I B n) (PhysicalClass I KP L n) :=
  SmoothSpinHOneTorsor.torsor LM ((nonempty_iff_refinement_lift LM).mpr ⟨R, hR⟩)

/-- Eventual neutrality of the degree-two defect supplies existence for the physical degree-one torsor. -/
@[instance_reducible] def torsor_of_vanishes (S : PairLifts (AdaptedGeometricSpinLift.lorentzData LM))
    (h : Vanishes (SpinSignCohomology.classOf (SpinSignDefectRepresentative.representative S))) :
    Torsor (GlobalH1 I B n) (PhysicalClass I KP L n) :=
  SmoothSpinHOneTorsor.torsor LM ((nonempty_iff_vanishes LM S).mpr h)

/-- Failure of the eventual obstruction test leaves the physical quotient empty. -/
theorem isEmpty_iff_not_vanishes (S : PairLifts (AdaptedGeometricSpinLift.lorentzData LM)) :
    IsEmpty (PhysicalClass I KP L n) ↔
    ¬ Vanishes (SpinSignCohomology.classOf (SpinSignDefectRepresentative.representative S)) := by
  rw [← nonempty_iff_vanishes LM S, ← nonempty_physical_iff]
  exact not_nonempty_iff.symm

include LM hB in
/-- Exactly one physical class exists precisely when a smooth lift exists and global degree one is trivial. -/
theorem unique_iff : (∃! _p : PhysicalClass I KP L n, True) ↔
    Nonempty (SmoothLift I KP L n) ∧ Subsingleton (GlobalH1 I B n) := by
  constructor
  · rintro ⟨p, _, hp⟩
    refine ⟨nonempty_physical_iff.mp ⟨p⟩, (SmoothSpinHOneTorsor.basedEquiv LM p).subsingleton_congr.mpr ?_⟩
    exact ⟨fun q r => (hp q trivial).trans (hp r trivial).symm⟩
  · rintro ⟨h, he⟩
    let p := physicalClass h.some
    have hs := (SmoothSpinHOneTorsor.basedEquiv LM p).subsingleton_congr.mp he
    exact ⟨p, trivial, fun q _ => hs.elim q p⟩

/-- For supplied normalized pair lifts, uniqueness is equivalent to eventual degree-two neutrality
together with degree-one triviality on every anchored cover. -/
theorem unique_iff_anchored (S : PairLifts (AdaptedGeometricSpinLift.lorentzData LM)) :
    (∃! _p : PhysicalClass I KP L n, True) ↔
    Vanishes (SpinSignCohomology.classOf (SpinSignDefectRepresentative.representative S)) ∧
      ∀ C : SpinHOneDirected.Cover B, Subsingleton (SpinSignHOne.H1 I C.domain n) :=
  (unique_iff LM).trans (and_congr (nonempty_iff_vanishes LM S) subsingleton_iff_anchored)

end FoliationQM.GlobalSpinClassificationCriterion
