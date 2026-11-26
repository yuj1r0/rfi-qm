module
public import FoliationQM.SpinLorentzCayleyLinear
public import FoliationQM.SpecialLinearRicci
public import FoliationQM.SpinLorentzPolarCompatibility
public import FoliationQM.LorentzCayleyDifferential

/-!
# Actual physical Spin-to-Lorentz Jacobian in independent Cayley coordinates

Source scope: the compatible Spin and Lorentz frame identification in v13
`prop:takabayasi` and `eq:tetrad_rotor_map`.  The rational special-linear
chart, physical Lorentz representation, inverse Cayley expression, and
six literal matrix entries define the actual coordinate map.  Its real
Frechet derivative at identity is proved from the rational matrix
inverse rule and the already verified physical frame derivative.  The
six-coordinate continuous-linear equivalence supplies the resulting
Jacobian with its exact metric signs and Cayley factor one half.

All pivot and denominator conditions are verified at the actual base
point.  No derivative identity, local inverse regularity, or rank
conclusion is supplied as a hypothesis.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Operator
open Set Filter Topology
namespace FoliationQM.SpinLorentzCayleyDerivative
open SpinLorentzCayleyLinear SpinorMatrix SpecialLinearCharts
open LorentzMatrixGroup LorentzCayleyAlgebra LorentzCayleyCoordinates
open SpinLorentzAction SpinLorentzPolarCompatibility

/-- The actual physical Lorentz matrix in six independent inverse Cayley coordinates after rational special-linear reconstruction. -/
def F (z : SourceModel) : TargetModel :=
  coordinatesOf (inverseCayley (lorentzMatrix (matrixA z)))

/-- The actual coordinate map sends the source identity coordinate to the target origin. -/
theorem F_basePoint : F basePoint = 0 := by
  simp only [F, matrixA_basePoint, lorentzMatrix_one, inverseCayley_one, map_zero]

/-- Rational special-linear reconstruction is smooth to every order at the actual nonzero identity pivot. -/
theorem contDiffAt_matrixA (n : WithTop ℕ∞) : ContDiffAt ℝ n matrixA basePoint :=
  (contDiffOn_matrixA n).contDiffAt
    ((isOpen_ne.preimage (continuous_apply 0)).mem_nhds basePoint_zero_ne)

private def coordinate (i : Fin 3) : SourceModel →L[ℝ] ℂ := ContinuousLinearMap.proj i

private theorem hasFDerivAt_lastEntry :
    HasFDerivAt (fun z : SourceModel => (1 + z 1 * z 2) / z 0)
      (-coordinate 0) basePoint := by
  have hn : HasFDerivAt (fun z : SourceModel => 1 + z 1 * z 2) (0 : SourceModel →L[ℝ] ℂ) basePoint := by
    convert! (((coordinate 1).hasFDerivAt (x := basePoint)).mul
      ((coordinate 2).hasFDerivAt (x := basePoint))).const_add (1 : ℂ) using 1
    ext v
    simp [coordinate, basePoint]
  have hi : HasFDerivAt (fun z : SourceModel => (z 0)⁻¹) (-coordinate 0) basePoint := by
    convert! (hasFDerivAt_inv' (𝕜 := ℝ) basePoint_zero_ne).comp basePoint
      ((coordinate 0).hasFDerivAt (x := basePoint)) using 1
    ext v
    simp [coordinate, basePoint, ContinuousLinearMap.mulLeftRight_apply]
  convert! hn.mul hi using 1
  ext z
  simp [basePoint]

/-- The actual rational special-linear chart derivative is the literal trace-zero matrix assembled from the three complex increments. -/
theorem fderiv_matrixA : fderiv ℝ matrixA basePoint = tangentMatrix := by
  have hm := (contDiffAt_matrixA 1).differentiableAt (by norm_num)
  ext v i j
  have he := congrArg (fun D : SourceModel →L[ℝ] ℂ => D v)
    (((SpecialLinearTangent.entryCLM i j).hasFDerivAt.comp basePoint hm.hasFDerivAt).fderiv)
  change fderiv ℝ (fun z => matrixA z i j) basePoint v =
    fderiv ℝ matrixA basePoint v i j at he
  rw [← he]
  fin_cases i <;> fin_cases j
  · change fderiv ℝ (fun z : SourceModel => z 0) basePoint v = v 0
    exact congrArg (fun D : SourceModel →L[ℝ] ℂ => D v)
      ((coordinate 0).hasFDerivAt (x := basePoint)).fderiv
  · change fderiv ℝ (fun z : SourceModel => z 1) basePoint v = v 1
    exact congrArg (fun D : SourceModel →L[ℝ] ℂ => D v)
      ((coordinate 1).hasFDerivAt (x := basePoint)).fderiv
  · change fderiv ℝ (fun z : SourceModel => z 2) basePoint v = v 2
    exact congrArg (fun D : SourceModel →L[ℝ] ℂ => D v)
      ((coordinate 2).hasFDerivAt (x := basePoint)).fderiv
  · change fderiv ℝ (fun z : SourceModel => (1 + z 1 * z 2) / z 0) basePoint v = -v 0
    exact congrArg (fun D : SourceModel →L[ℝ] ℂ => D v) hasFDerivAt_lastEntry.fderiv

/-- Rational special-linear reconstruction has the proved trace-zero continuous-linear Frechet derivative at identity. -/
theorem hasFDerivAt_matrixA : HasFDerivAt matrixA tangentMatrix basePoint := by
  rw [← fderiv_matrixA]
  exact ((contDiffAt_matrixA 1).differentiableAt (by norm_num)).hasFDerivAt

/-- The rational chart has determinant one on a genuine neighborhood of its identity base point. -/
theorem eventually_matrixA_det : ∀ᶠ z in 𝓝 basePoint, (matrixA z).det = 1 := by
  have hp : ∀ᶠ z : SourceModel in 𝓝 basePoint, z 0 ≠ 0 :=
    (isOpen_ne.preimage (continuous_apply 0)).mem_nhds basePoint_zero_ne
  exact hp.mono fun _ hz => matrixA_det hz

private theorem frame_derivative_apply (v : SourceModel) (a mu : Fin 4) :
    fderiv ℝ (fun z => SpecialLinearFrame.frame (matrixA z)) basePoint v a mu =
      SpecialLinearLieAlgebra.omega (tangentMatrix v) mu a * RealLorentzFrame.sign a := by
  have hm := hasFDerivAt_matrixA.differentiableAt
  have hf : DifferentiableAt ℝ (fun z => SpecialLinearFrame.frame (matrixA z)) basePoint :=
    differentiableAt_pi.mpr (fun a => SpecialLinearRicci.differentiableAt_frame_row hm a)
  have he := congrArg (fun D : SourceModel →L[ℝ] FoliationQM.Covector => D v mu)
    (fderiv_apply hf a)
  change fderiv ℝ (fun z => SpecialLinearFrame.frame (matrixA z) a) basePoint v mu =
    fderiv ℝ (fun z => SpecialLinearFrame.frame (matrixA z)) basePoint v a mu at he
  rw [← he, SpecialLinearRicci.fderiv_frame_row hm eventually_matrixA_det]
  have hframe : SpecialLinearFrame.frame (1 : Mat2) = (1 : Mat4) :=
    SpecialLinearFrameLaws.frame_one
  simp only [SpecialLinearConnection.bodyOmega, SpecialLinearTangent.body2,
    matrixA_basePoint, fderiv_matrixA, inv_one, Matrix.one_mul, hframe]
  simp [Matrix.one_apply]

/-- The physical Lorentz matrix has the proved actual derivative twice the independent skew-matrix assembly of the explicit six-coordinate Jacobian. -/
theorem hasFDerivAt_lorentzMatrix_matrixA :
    HasFDerivAt (fun z => lorentzMatrix (matrixA z))
      ((2 : ℝ) • matrixOf.comp jacobian.toContinuousLinearMap) basePoint := by
  have hm := hasFDerivAt_matrixA.differentiableAt
  have hf : DifferentiableAt ℝ (fun z => SpecialLinearFrame.frame (matrixA z)) basePoint :=
    differentiableAt_pi.mpr (fun a => SpecialLinearRicci.differentiableAt_frame_row hm a)
  have h := physicalFrameCLM.hasFDerivAt.comp basePoint hf.hasFDerivAt
  have he : physicalFrameCLM.comp
      (fderiv ℝ (fun z => SpecialLinearFrame.frame (matrixA z)) basePoint) =
        (2 : ℝ) • matrixOf.comp jacobian.toContinuousLinearMap := by
    ext v mu a
    change RealLorentzFrame.sign mu * RealLorentzFrame.sign a *
      (fderiv ℝ (fun z => SpecialLinearFrame.frame (matrixA z)) basePoint v a mu) =
        2 * matrixOf (jacobian v) mu a
    rw [frame_derivative_apply]
    fin_cases mu <;> fin_cases a <;>
      simp [RealLorentzFrame.sign, SpecialLinearLieAlgebra.omega,
        tangentMatrix_apply, matrixOf_apply, jacobian_apply] <;> ring
  rw [he] at h
  simpa only [Function.comp_def, physicalFrameCLM_frame] using h

/-- The actual physical coordinate map is smooth to every order, including analytic order, at the verified identity pivot and denominator. -/
theorem contDiffAt_F (n : WithTop ℕ∞) : ContDiffAt ℝ n F basePoint := by
  have hu : IsUnit ((1 : Mat4) + 1) :=
    (LorentzCayleyDomain.mem_source_iff (1 : ProperFutureLorentz)).mp
      LorentzCayleyDomain.one_mem_source
  have hl : ContDiffAt ℝ n (fun z => lorentzMatrix (matrixA z)) basePoint :=
    (contDiff_lorentzMatrix n).contDiffAt.comp basePoint (contDiffAt_matrixA n)
  have hc : ContDiffAt ℝ n inverseCayley (lorentzMatrix (matrixA basePoint)) := by
    rw [matrixA_basePoint, lorentzMatrix_one]
    exact LorentzCayleySmooth.contDiffAt_inverseCayley n hu
  have hi : ContDiffAt ℝ n (fun z : SourceModel =>
      inverseCayley (lorentzMatrix (matrixA z))) basePoint :=
    hc.comp (f := fun z : SourceModel => lorentzMatrix (matrixA z)) basePoint hl
  exact coordinatesOf.contDiff.contDiffAt.comp
    (f := fun z : SourceModel => inverseCayley (lorentzMatrix (matrixA z))) basePoint hi

/-- The actual physical Spin-to-Lorentz coordinate map has the explicit invertible real Frechet Jacobian at identity. -/
theorem hasFDerivAt_F : HasFDerivAt F jacobian.toContinuousLinearMap basePoint := by
  have hc : HasFDerivAt inverseCayley
      ((1/2 : ℝ) • ContinuousLinearMap.id ℝ Mat4) (lorentzMatrix (matrixA basePoint)) := by
    rw [matrixA_basePoint, lorentzMatrix_one]
    exact LorentzCayleyDifferential.hasFDerivAt_inverseCayley_one
  have h := coordinatesOf.hasFDerivAt.comp basePoint
    (hc.comp basePoint hasFDerivAt_lorentzMatrix_matrixA)
  convert! h using 1
  ext v : 1
  change jacobian v = coordinatesOf ((1/2 : ℝ) • ((2 : ℝ) • matrixOf (jacobian v)))
  rw [smul_smul]
  norm_num [coordinatesOf_matrixOf]

/-- The actual coordinate derivative equals the independently proved continuous-linear equivalence, with no rank hypothesis. -/
theorem fderiv_F : fderiv ℝ F basePoint = jacobian.toContinuousLinearMap :=
  hasFDerivAt_F.fderiv

end FoliationQM.SpinLorentzCayleyDerivative
