module
public import FoliationQM.IntrinsicPathRestriction
public import FoliationQM.IntrinsicPathChoice
public import FoliationQM.ModTwoAllCover

/-!
# The independently constructed global path obstruction

For the geometric component of v13 `prop:takabayasi`, the actual
intrinsic path-kernel cocycle represents a class in normalized locally
constant mod-two Cech cohomology over all covers. Path choices and open
refinement preserve that class by intrinsic homotopy and group algebra.
The existence of joint path families and local path connectedness remain
explicit. This is a class of the presented transitions; no conventional
real-bundle Stiefel-Whitney class or arbitrary-atlas invariance is asserted.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GlobalIntrinsicPathObstruction
open PathTransitionData BasedPathGroup CliffordSpinCoverRefinement

variable {G B ι κ : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [TopologicalSpace B] [LocallyPathConnectedSpace B] {D : Data G B ι}

/-- The global class of the genuine path-kernel coefficients, defined without any physical Spin lift. -/
def obstruction (e : (projection (G := G)).ker →* Multiplicative (ZMod 2))
    (P : Family D) : ModTwoAllCover.GlobalH2 B :=
  ModTwoAllCover.ofCover D.domain D.covers
    (ModTwoCohomology.classOf (IntrinsicPathCocycle.cocycle e P))

/-- Changing jointly continuous normalized transition paths preserves the independently constructed global class. -/
theorem independent (e : (projection (G := G)).ker →* Multiplicative (ZMod 2))
    (P Q : Family D) : obstruction e P = obstruction e Q :=
  congrArg (ModTwoAllCover.ofCover D.domain D.covers)
    (IntrinsicPathChoice.class_independent e P Q)

/-- Restricting the original joint paths to an open refinement preserves their global class. -/
theorem restrict (e : (projection (G := G)).ker →* Multiplicative (ZMod 2))
    (P : Family D) (R : Refinement D.domain κ) :
    obstruction e (IntrinsicPathRestriction.family P R) = obstruction e P := by
  unfold obstruction
  rw [IntrinsicPathRestriction.class_restrict]
  exact ModTwoAllCover.ofCover_restrict D.covers R _

/-- Any joint path family for the restricted transitions computes the same global class. -/
theorem refine (e : (projection (G := G)).ker →* Multiplicative (ZMod 2))
    (P : Family D) (R : Refinement D.domain κ)
    (Q : Family (IntrinsicPathRestriction.data D R)) : obstruction e Q = obstruction e P :=
  (independent e Q (IntrinsicPathRestriction.family P R)).trans (restrict e P R)

/-- Vanishing of the global class means precisely a zero native class after further open refinement. -/
theorem zero_iff_refinement (e : (projection (G := G)).ker →* Multiplicative (ZMod 2))
    (P : Family D) : obstruction e P = 0 ↔
      ∃ R : Refinement D.domain B,
        ModTwoCohomology.classOf (IntrinsicPathCocycle.cocycle e (IntrinsicPathRestriction.family P R)) = 0 := by
  unfold obstruction
  rw [ModTwoAllCover.ofCover_eq_zero_iff]
  exact exists_congr (fun R => by rw [IntrinsicPathRestriction.class_restrict]; rfl)

/-- A fixed-cover zero class already gives a zero all-cover class. -/
theorem zero_of_fixed (e : (projection (G := G)).ker →* Multiplicative (ZMod 2))
    (P : Family D) (h : ModTwoCohomology.classOf (IntrinsicPathCocycle.cocycle e P) = 0) :
    obstruction e P = 0 := by
  unfold obstruction
  rw [h, map_zero]

/-- If every intrinsic triple defect is trivial, the global class is zero without pair correction. -/
theorem zero_of_defects (e : (projection (G := G)).ker →* Multiplicative (ZMod 2))
    (P : Family D)
    (h : ∀ i j k x (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) (hk : x ∈ D.domain k),
      IntrinsicPathCocycle.defect P i j k x hi hj hk = 1) : obstruction e P = 0 := by
  apply zero_of_fixed e P
  change ModTwoCohomology.classOf (IntrinsicPathCocycle.cocycle e P) =
    ModTwoCohomology.classOf (0 : ModTwoCohomology.TwoCocycle D.domain)
  apply ModTwoCohomology.classOf_eq_of_eqOn
  intro i j k x hi hj hk
  change (IntrinsicPathCocycle.cocycle e P).value i j k x = 0
  rw [IntrinsicPathCocycle.cocycle_value e P i j k x hi hj hk]
  simp only [IntrinsicPathCocycle.coefficient, h i j k x hi hj hk, map_one]
  rfl

end FoliationQM.GlobalIntrinsicPathObstruction
