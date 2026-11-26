module

public import FoliationQM.RNCCoordinateConnection
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.Topology.Algebra.Module.Equiv.Pi
public import Mathlib.Topology.Algebra.Module.Equiv.Prod

/-!
# Actual real coordinates for the Euclidean product tube

Source: v13 `eq:log_cutoff_wallstrom` and `eq:log_cutoff_l2_bound`, component
kinds C and D. Four real coordinates are regrouped into the two genuine complex
planes, with exact canonical volume preservation. The source coordinate space
retains its supremum norm; the target has the Euclidean product norm. The unit
coordinate directions are identified explicitly, without an isometry claim.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.ProductTubeCoordinates

open MeasureTheory RealLorentzFrame RNCCoordinateConnection

local notation "Space" => WithLp 2 (ℂ × ℂ)

/-- The actual continuous real-linear equivalence regrouping four real coordinates into tangential and normal complex planes. -/
def coordinates : Covector ≃L[ℝ] Space :=
  (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin 4 => ℝ)
    (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4)).symm.trans
  ((ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin 2) (Fin 2) (fun _ => ℝ)).trans
    ((Complex.basisOneI.equivFun.toContinuousLinearEquiv.symm.prodCongr
      Complex.basisOneI.equivFun.toContinuousLinearEquiv.symm).trans
      (WithLp.prodContinuousLinearEquiv 2 ℝ ℂ ℂ).symm))

/-- The forward coordinate map has the literal complex components x₀+i x₁ and x₂+i x₃. -/
theorem coordinates_apply (x : Covector) :
    coordinates x = WithLp.toLp 2
      ((x 0 : ℂ) + (x 1 : ℂ) * Complex.I, (x 2 : ℂ) + (x 3 : ℂ) * Complex.I) := by
  rfl

/-- The inverse coordinate map returns the real and imaginary parts of the same two complex coordinates. -/
theorem coordinates_symm_apply (y : Space) :
    coordinates.symm y = ![y.fst.re, y.fst.im, y.snd.re, y.snd.im] := by
  apply coordinates.injective
  rw [coordinates.apply_symm_apply, coordinates_apply]
  apply WithLp.ofLp_injective 2
  ext <;> simp

/-- The same continuous linear coordinate map preserves the actual canonical four-dimensional volume measure. -/
theorem volume_preserving : MeasurePreserving coordinates volume volume := by
  let e : Covector ≃ᵐ Space :=
    (MeasurableEquiv.piCongrLeft (fun _ : Fin 4 => ℝ)
      (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4)).symm.trans
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 2 ⊕ Fin 2 => ℝ)).trans
      ((Complex.measurableEquivPi.symm.prodCongr Complex.measurableEquivPi.symm).trans
        (MeasurableEquiv.toLp 2 (ℂ × ℂ))))
  have hp : MeasurePreserving
      (Complex.measurableEquivPi.symm.prodCongr Complex.measurableEquivPi.symm)
      volume volume :=
    Complex.volume_preserving_equiv_pi.symm.prod Complex.volume_preserving_equiv_pi.symm
  have he : MeasurePreserving e volume volume :=
    (volume_measurePreserving_piCongrLeft (fun _ : Fin 4 => ℝ)
      (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4)).symm.trans
      ((volume_measurePreserving_sumPiEquivProdPi
        (fun _ : Fin 2 ⊕ Fin 2 => ℝ)).trans
        (hp.trans (WithLp.volume_preserving_toLp ℂ ℂ)))
  exact he

/-- The four existing coordinate axes map to the two complex unit bases; each image has actual Euclidean product norm one. -/
theorem coordinate_axes :
    coordinates (axis 0) = WithLp.toLp 2 ((1 : ℂ), (0 : ℂ)) ∧
    coordinates (axis 1) = WithLp.toLp 2 (Complex.I, (0 : ℂ)) ∧
    coordinates (axis 2) = WithLp.toLp 2 ((0 : ℂ), (1 : ℂ)) ∧
    coordinates (axis 3) = WithLp.toLp 2 ((0 : ℂ), Complex.I) ∧
    ∀ i : Fin 4, ‖coordinates (axis i)‖ = 1 := by
  have h0 : coordinates (axis 0) = WithLp.toLp 2 ((1 : ℂ), (0 : ℂ)) := by
    simp [coordinates_apply, axis]
  have h1 : coordinates (axis 1) = WithLp.toLp 2 (Complex.I, (0 : ℂ)) := by
    simp [coordinates_apply, axis]
  have h2 : coordinates (axis 2) = WithLp.toLp 2 ((0 : ℂ), (1 : ℂ)) := by
    simp [coordinates_apply, axis]
  have h3 : coordinates (axis 3) = WithLp.toLp 2 ((0 : ℂ), Complex.I) := by
    simp [coordinates_apply, axis]
  refine ⟨h0, h1, h2, h3, ?_⟩
  intro i
  fin_cases i <;> simp [h0, h1, h2, h3]

/-- The actual zero-normal-coordinate axis pulls back to precisely the last two real coordinates being zero. -/
theorem axis_preimage :
    coordinates ⁻¹' {y : Space | y.snd = 0} = {x : Covector | x 2 = 0 ∧ x 3 = 0} := by
  ext x
  change (coordinates x).snd = 0 ↔ _
  rw [coordinates_apply]
  change (x 2 : ℂ) + (x 3 : ℂ) * Complex.I = 0 ↔ _
  simp [Complex.ext_iff]

end FoliationQM.ProductTubeCoordinates
