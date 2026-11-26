module
public import FoliationQM.SourcePolarProductQuotient
public import FoliationQM.ChiralAngleManifold
public import FoliationQM.SpecialLinearManifold
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The intrinsic seven-dimensional angle and matrix datum

Sources: the density-separated frame factor in v13 `prop:takabayasi`
and `eq:takabayasi_polar`. The existing `FrameDatum` retains its natural
product topology and the product of the independently established
four-pi-angle and determinant-one matrix atlases. The real model has
one angle coordinate and six matrix coordinates.

The actual simultaneous two-pi shift and matrix negation is a smooth
fixed-point-free involution for this intrinsic atlas. Smoothness into
the product is characterized by the actual angle coordinate and actual
ambient matrix coordinate, with within-set and pointwise versions.
A further global criterion uses the actual complex half-angle phase.
No quotient manifold, global real angle, or abstract Spin-group
identification is defined by these foundational statements.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Operator Manifold ContDiff
open Function Set Topology
namespace FoliationQM.FrameDatumManifold
open SourcePolarProductQuotient SourcePolarDatum PolarAmplitudeTopology
open ChiralAngleCircle ChiralAngleManifold SpinorMatrix

/-- The real normed model is the product of the one-dimensional angle and six-dimensional determinant-one matrix models. -/
abbrev Model := AngleModel × SpecialLinearCharts.Model
/-- The actual chart codomain is the tagged product of the two intrinsic factor chart spaces. -/
abbrev ChartModel := ModelProd AngleModel SpecialLinearCharts.Model
/-- The frame datum model with corners is exactly the product of its independently specified factor models. -/
abbrev model : ModelWithCorners ℝ Model ChartModel :=
  (𝓡 1).prod 𝓘(ℝ, SpecialLinearCharts.Model)

/-- The existing natural angle-matrix product with its intrinsic product atlas is a real manifold to every differentiability order. -/
theorem isManifold_frame (n : WithTop ℕ∞) : IsManifold model n FrameDatum := inferInstance

/-- Every preferred frame-datum chart is literally the product of the preferred angle and determinant-one matrix charts. -/
theorem chartAt_eq (p : FrameDatum) :
    chartAt ChartModel p = (chartAt AngleModel p.1).prod
      (chartAt SpecialLinearCharts.Model p.2) := rfl

/-- The intrinsic frame-datum model has seven real dimensions: one angle and six matrix coordinates. -/
theorem model_finrank : Module.finrank ℝ Model = 7 := by
  simp [Model, Module.finrank_prod, SpecialLinearManifold.model_finrank]

/-- The existing frame sign operation is literally the two-pi angle shift and negation of the actual determinant-one matrix. -/
theorem frameShift_eq (p : FrameDatum) :
    frameShift p = (p.1 + ((2 * Real.pi : ℝ) : Angle),
      ⟨-(p.2 : Mat2), by simp [Matrix.det_neg, p.2.property]⟩) := rfl

/-- The actual angle-matrix sign involution has no fixed point, by the already verified source sign freeness. -/
theorem frameShift_ne_self (p : FrameDatum) : frameShift p ≠ p := by
  intro h
  apply shiftNeg_ne_self ((⟨1, by norm_num⟩ : PositiveDensity), p)
  rw [shiftNeg_pair, h]

/-- The actual two-pi angle shift and matrix negation is smooth directly from its intrinsic factor maps. -/
theorem contMDiff_frameShift (n : WithTop ℕ∞) : ContMDiff model model n frameShift := by
  have hm : ContMDiff 𝓘(ℝ, SpecialLinearCharts.Model) 𝓘(ℝ, SpecialLinearCharts.Model) n
      (fun A : SpecialLinearMatrix =>
        (⟨-(A : Mat2), by simp [Matrix.det_neg, A.property]⟩ : SpecialLinearMatrix)) := by
    apply SpecialLinearManifold.contMDiff_iff_value.mpr
    exact (SpecialLinearManifold.contMDiff_value n).neg
  exact ((contMDiff_shift_two_pi n).comp contMDiff_fst).prodMk (hm.comp contMDiff_snd)

/-- The actual free sign involution is a genuine diffeomorphism of the intrinsic frame-datum manifold. -/
def frameShiftDiffeomorph (n : WithTop ℕ∞) :
    Diffeomorph model model FrameDatum FrameDatum n where
  toFun := frameShift
  invFun := frameShift
  left_inv := frameShift_involutive
  right_inv := frameShift_involutive
  contMDiff_toFun := contMDiff_frameShift n
  contMDiff_invFun := contMDiff_frameShift n

/-- The bundled frame sign diffeomorphism is exactly the existing literal sign operation. -/
theorem frameShiftDiffeomorph_apply (n : WithTop ℕ∞) (p : FrameDatum) :
    frameShiftDiffeomorph n p = frameShift p := rfl

/-- The inverse of the actual bundled frame sign diffeomorphism is the same diffeomorphism. -/
theorem frameShiftDiffeomorph_symm (n : WithTop ℕ∞) :
    (frameShiftDiffeomorph n).symm = frameShiftDiffeomorph n := by
  apply Diffeomorph.ext
  intro p
  rfl

section GeneralSource
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  {n : WithTop ℕ∞} {f : M → FrameDatum} {s : Set M} {x : M}

/-- For an arbitrary charted source and source set, intrinsic frame-datum smoothness is equivalent to smoothness of its actual angle and ambient matrix coordinates. -/
theorem contMDiffWithinAt_iff_coordinates :
    ContMDiffWithinAt I model n f s x ↔
      ContMDiffWithinAt I (𝓡 1) n (fun y => (f y).1) s x ∧
      ContMDiffWithinAt I 𝓘(ℝ, Mat2) n (fun y => ((f y).2 : Mat2)) s x := by
  rw [contMDiffWithinAt_prod_iff]
  exact and_congr Iff.rfl SpecialLinearManifold.contMDiffWithinAt_iff_value

/-- For an arbitrary charted source, intrinsic frame-datum smoothness at a point is equivalent to actual angle and ambient matrix coordinate smoothness there. -/
theorem contMDiffAt_iff_coordinates :
    ContMDiffAt I model n f x ↔
      ContMDiffAt I (𝓡 1) n (fun y => (f y).1) x ∧
      ContMDiffAt I 𝓘(ℝ, Mat2) n (fun y => ((f y).2 : Mat2)) x :=
  contMDiffWithinAt_iff_coordinates

/-- For an arbitrary charted source, intrinsic frame-datum smoothness on any set is equivalent to actual angle and ambient matrix coordinate smoothness on that set. -/
theorem contMDiffOn_iff_coordinates :
    ContMDiffOn I model n f s ↔
      ContMDiffOn I (𝓡 1) n (fun y => (f y).1) s ∧
      ContMDiffOn I 𝓘(ℝ, Mat2) n (fun y => ((f y).2 : Mat2)) s := by
  rw [contMDiffOn_prod_iff]
  exact and_congr Iff.rfl SpecialLinearManifold.contMDiffOn_iff_value

/-- For an arbitrary charted source, global intrinsic frame-datum smoothness is equivalent to actual angle and ambient matrix coordinate smoothness. -/
theorem contMDiff_iff_coordinates :
    ContMDiff I model n f ↔
      ContMDiff I (𝓡 1) n (fun y => (f y).1) ∧
      ContMDiff I 𝓘(ℝ, Mat2) n (fun y => ((f y).2 : Mat2)) := by
  rw [contMDiff_prod_iff]
  exact and_congr Iff.rfl SpecialLinearManifold.contMDiff_iff_value

/-- On a real manifold, global frame-datum smoothness is equivalent to smoothness of its actual complex half-angle phase and actual ambient matrix; no real argument is chosen. -/
theorem contMDiff_iff_phase_matrix [IsManifold I n M] :
    ContMDiff I model n f ↔
      ContMDiff I 𝓘(ℝ, ℂ) n (fun y => (phaseEquiv (f y).1 : ℂ)) ∧
      ContMDiff I 𝓘(ℝ, Mat2) n (fun y => ((f y).2 : Mat2)) := by
  rw [contMDiff_iff_coordinates]
  exact and_congr ChiralAngleManifold.contMDiff_iff_complexPhase Iff.rfl

end GeneralSource
end FoliationQM.FrameDatumManifold
