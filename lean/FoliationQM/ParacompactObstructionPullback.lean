module
public import FoliationQM.ParacompactBundleObstruction
public import FoliationQM.PresentedBundlePullback

/-!
# Pulling back the native obstruction of an ordinary Lorentz atlas

For the frame-bundle component of v13 `prop:takabayasi`, the obstruction
on the actual fiber product is the pullback in all-cover mod-two degree two.
A continuous section recovers every original class. Restricting a target
atlas to that section and pulling it back tests descent of its degree-two class.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.ParacompactObstructionPullback
open LorentzMatrixGroup ModTwoAllCover ModTwoGlobalPullback
open ParacompactBundleObstruction (obstruction)
open GeometricPrincipalPullback (atlas)

variable {B X Y : Type*} [TopologicalSpace B] [TopologicalSpace X] [TopologicalSpace Y]

/-- Restriction along a continuous section recovers any all-cover degree-two class. -/
theorem section_pull (f : C(X, B)) (s : C(B, X)) (hs : Function.RightInverse s f)
    (c : GlobalH2 B) : pull s (pull f c) = c := by
  rw [pull_comp, show f.comp s = .id B from ContinuousMap.ext hs, pull_id]

/-- A degree-two class on the new base descends exactly when reconstructing it from
its restriction to a continuous section gives the same class. -/
theorem mem_range_iff (f : C(X, B)) (s : C(B, X)) (hs : Function.RightInverse s f)
    (c : GlobalH2 X) : c ∈ Set.range (pull f) ↔ pull f (pull s c) = c := by
  constructor
  · rintro ⟨d, rfl⟩
    rw [section_pull f s hs d]
  · exact fun h => ⟨pull s c, h⟩

variable {T ι : Type*} [TopologicalSpace T] {proj : T → B}
  [ParacompactSpace B] [NormalSpace B] [LocallyPathConnectedSpace B]
  [LocallyPathConnectedSpace X]
  (A : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι)

/-- The presentation inherited by the actual fiber product computes its class on
any locally path connected new base. -/
theorem inherited_natural (f : C(X, B)) :
    PresentedLorentzBundle.obstruction (PresentedBundlePullback.hasPresentation f
      (ParacompactLorentzPresentation.hasPresentation A)) = pull f (obstruction A) :=
  PresentedBundlePullback.obstruction_natural f _

/-- The section determines whether the inherited obstruction vanishes, even if
the new base is not furnished with an independent shrinking. -/
theorem inherited_zero_iff_of_section (f : C(X, B)) (s : C(B, X)) (hs : Function.RightInverse s f) :
    PresentedLorentzBundle.obstruction (PresentedBundlePullback.hasPresentation f
      (ParacompactLorentzPresentation.hasPresentation A)) = 0 ↔ obstruction A = 0 := by
  rw [inherited_natural]
  constructor
  · intro h
    rw [← section_pull f s hs (obstruction A), h, map_zero]
  · intro h
    rw [h, map_zero]

variable [ParacompactSpace X] [NormalSpace X]

/-- Constructing a presentation anew on the actual fiber-product atlas gives
the pullback of the canonical obstruction of the original atlas. -/
theorem natural (f : C(X, B)) : obstruction (atlas f A) = pull f (obstruction A) :=
  PresentedBundlePullback.obstruction_of_right_eq f (ParacompactLorentzPresentation.hasPresentation A)
    (ParacompactLorentzPresentation.hasPresentation (atlas f A))
    (PresentedBundlePullback.atlas_right f _ A rfl)

/-- Successive and direct geometric fiber products yield the same native class. -/
theorem iterated [ParacompactSpace Y] [NormalSpace Y] [LocallyPathConnectedSpace Y]
    (f : C(X, B)) (g : C(Y, X)) :
    obstruction (atlas g (atlas f A)) = obstruction (atlas (f.comp g) A) := by
  rw [natural, natural, natural, pull_comp]

/-- The obstruction on the actual fiber product along a constant map vanishes. -/
theorem const_zero (b : B) : obstruction (atlas (ContinuousMap.const X b) A) = 0 := by
  rw [natural, ModTwoConstantPullback.pull_const]

/-- The actual geometric pullback along the section recovers the obstruction of A. -/
theorem section_recovers (f : C(X, B)) (s : C(B, X)) (hs : Function.RightInverse s f) :
    obstruction (atlas s (atlas f A)) = obstruction A := by
  rw [natural, natural, section_pull f s hs]

/-- A continuous base change with a section preserves and detects vanishing
of the canonical obstruction. -/
theorem zero_iff_of_section (f : C(X, B)) (s : C(B, X)) (hs : Function.RightInverse s f) :
    obstruction (atlas f A) = 0 ↔ obstruction A = 0 := by
  rw [natural, ← inherited_natural A f]
  exact inherited_zero_iff_of_section A f s hs

/-- The native class of an atlas on the new base comes from the original base
exactly when geometric restriction to the section and pullback reproduce that class. -/
theorem class_mem_range_iff {projX : T → X}
    (D : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) projX ι)
    (f : C(X, B)) (s : C(B, X)) (hs : Function.RightInverse s f) :
    obstruction D ∈ Set.range (pull f) ↔ obstruction (atlas f (atlas s D)) = obstruction D := by
  rw [natural, natural]
  exact mem_range_iff f s hs (obstruction D)

end FoliationQM.ParacompactObstructionPullback
