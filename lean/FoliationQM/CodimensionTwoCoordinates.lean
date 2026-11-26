module

public import FoliationQM.ProductTubeCoordinates
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Normalizing a real codimension-two splitting

Source: v13 `thm:wallstrom` Part(c), component kind A. An actual continuous
linear splitting with a complex tangential plane forces the complementary
space to have real dimension two. Its normalization retains the original
four-coordinate ambient model. No isometry or metric-distance claim is made.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.CodimensionTwoCoordinates

open RealLorentzFrame
open scoped Matrix

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- An actual splitting of four real coordinates into a complex plane and a complement forces that complement to be finite dimensional of real dimension two. -/
theorem complement_dimension (L : (ℂ × F) ≃L[ℝ] Covector) :
    FiniteDimensional ℝ F ∧ Module.finrank ℝ F = 2 := by
  have hF : FiniteDimensional ℝ F :=
    FiniteDimensional.of_injective
      (L.toLinearEquiv.toLinearMap.comp (LinearMap.inr ℝ ℂ F))
      (L.injective.comp (LinearMap.inr_injective (R := ℝ) (M := ℂ) (M₂ := F)))
  have := hF
  refine ⟨hF, ?_⟩
  have hd := L.toLinearEquiv.finrank_eq
  change Module.finrank ℝ (ℂ × F) = Module.finrank ℝ (Fin 4 → ℝ) at hd
  simp only [Module.finrank_prod, Complex.finrank_real_complex,
    Module.finrank_fin_fun] at hd
  omega

/-- The ambient coordinates can be normalized so the complement vanishes exactly on the last-two-zero plane, with the original complex tangential coordinates fixed literally. -/
theorem exists_normalization (L : (ℂ × F) ≃L[ℝ] Covector) :
    ∃ A : Covector ≃L[ℝ] Covector,
      (∀ v, ((A v) 2 = 0 ∧ (A v) 3 = 0) ↔ (L.symm v).2 = 0) ∧
      (∀ z : ℂ, A (L (z, 0)) = ![z.re, z.im, 0, 0]) := by
  obtain ⟨hF, hd⟩ := complement_dimension L
  have := hF
  let e : F ≃L[ℝ] ℂ := ContinuousLinearEquiv.ofFinrankEq
    (hd.trans Complex.finrank_real_complex.symm)
  let A : Covector ≃L[ℝ] Covector := L.symm.trans
    (((ContinuousLinearEquiv.refl ℝ ℂ).prodCongr e).trans
      ((WithLp.prodContinuousLinearEquiv 2 ℝ ℂ ℂ).symm.trans
        ProductTubeCoordinates.coordinates.symm))
  have hformula (v : Covector) : A v =
      ![(L.symm v).1.re, (L.symm v).1.im,
        (e (L.symm v).2).re, (e (L.symm v).2).im] := by
    exact ProductTubeCoordinates.coordinates_symm_apply
      (WithLp.toLp 2 ((L.symm v).1, e (L.symm v).2))
  refine ⟨A, ?_, ?_⟩
  · intro v
    rw [hformula]
    change ((e (L.symm v).2).re = 0 ∧ (e (L.symm v).2).im = 0) ↔ _
    constructor
    · intro h
      apply e.injective
      apply Complex.ext
      · simpa using h.1
      · simpa using h.2
    · intro h
      simp [h]
  · intro z
    simp [hformula]

end FoliationQM.CodimensionTwoCoordinates
