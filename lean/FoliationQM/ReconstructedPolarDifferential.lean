module
public import FoliationQM.PolarSpinorDifferential
public import FoliationQM.SpinorMatrixSmooth
public import FoliationQM.LocalPolarFields
/-!
# Actual derivatives of locally reconstructed regular spinor fields

Sources: v13 `prop:takabayasi`, `eq:takabayasi_polar` and the differential
identities in `lem:maurer_cartan`. Local equality with actual determinant-one
matrix polar fields transfers the established real Frechet product rule to
the original spinor field. Final existence theorems construct these local
factors from C1 regularity alone, using the two-chart cover. Invertibility,
gamma5 commutation and local Dirac
isometry are derived from the actual matrix representation.

The source signs are retained: the positive half-log and chiral terms occur
in both the column and adjoint-row derivative, while the actual spatial
matrix connection changes sign. Lorentz-generator coefficient extraction,
abstract Spin/frame classification and variational implications remain
separate from this actual differential reconstruction.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
open Filter Topology
namespace FoliationQM.ReconstructedPolarDifferential
open DiracMatrices DiracAdjoint SpinorMatrix SpecialLinearSpin
open PolarSpinorBilinears PolarSpinorDifferential MatrixDifferential MaurerCartanDifferential
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- Actual local polar equality gives the original spinor field a genuine factored Frechet derivative; matrix invertibility and gamma5 commutation follow from determinant one. -/
theorem hasFDerivAt_of_local_polar {psi : E → Spinor} {rho beta : E → ℝ}
    {A : E → Mat2} {x : E}
    (hrho : DifferentiableAt ℝ rho x) (hbeta : DifferentiableAt ℝ beta x)
    (hA : DifferentiableAt ℝ A x) (hpos : 0 < rho x) (hdet : (A x).det = 1)
    (heq : psi =ᶠ[𝓝 x] polarField rho beta (fun y => spin (A y))) :
    HasFDerivAt psi
      ((mulVecCLM (psi x)).comp (polarConnection rho beta (fun y => spin (A y)) x)) x := by
  have hL : DifferentiableAt ℝ (fun y => spin (A y)) x :=
    SpinorMatrixSmooth.spinCLM.differentiableAt.comp x hA
  have h := hasFDerivAt_polarField_factored hrho hbeta hL hpos
    (spin_isUnit (A x) hdet) (Filter.Eventually.of_forall (fun y => spin_gamma5_commute (A y)))
  rw [← heq.eq_of_nhds] at h
  exact h.congr_of_eventuallyEq heq

/-- The original field directional derivative has the actual half-log, chiral and spatial connection terms whenever its local determinant-one polar representation is differentiable. -/
theorem fderiv_of_local_polar {psi : E → Spinor} {rho beta : E → ℝ}
    {A : E → Mat2} {x : E}
    (hrho : DifferentiableAt ℝ rho x) (hbeta : DifferentiableAt ℝ beta x)
    (hA : DifferentiableAt ℝ A x) (hpos : 0 < rho x) (hdet : (A x).det = 1)
    (heq : psi =ᶠ[𝓝 x] polarField rho beta (fun y => spin (A y))) (v : E) :
    fderiv ℝ psi x v =
      (((fderiv ℝ (fun y => Real.log (rho y)) x v / 2 : ℝ) : ℂ) • (1 : Mat) +
        (Complex.I*(fderiv ℝ beta x v : ℂ)/2) • gamma5 +
        spatial (fun y => spin (A y)) x v).mulVec (psi x) := by
  rw [(hasFDerivAt_of_local_polar hrho hbeta hA hpos hdet heq).fderiv]
  change (polarConnection rho beta (fun y => spin (A y)) x v).mulVec (psi x) = _
  rw [polarConnection_apply]

/-- The actual original Dirac-adjoint field has the same half-log and chiral signs and the opposite spatial connection sign, with local isometry derived from determinant one. -/
theorem fderiv_adjoint_of_local_polar {psi : E → Spinor} {rho beta : E → ℝ}
    {A : E → Mat2} {x : E}
    (hrho : DifferentiableAt ℝ rho x) (hbeta : DifferentiableAt ℝ beta x)
    (hA : DifferentiableAt ℝ A x) (hpos : 0 < rho x)
    (hdet : ∀ᶠ y in 𝓝 x, (A y).det = 1)
    (heq : psi =ᶠ[𝓝 x] polarField rho beta (fun y => spin (A y))) (v : E) :
    fderiv ℝ (fun y => spinorAdjoint (psi y)) x v =
      Matrix.vecMul (spinorAdjoint (psi x))
        (((fderiv ℝ (fun y => Real.log (rho y)) x v / 2 : ℝ) : ℂ) • (1 : Mat) +
          (Complex.I*(fderiv ℝ beta x v : ℂ)/2) • gamma5 -
          spatial (fun y => spin (A y)) x v) := by
  have hL : DifferentiableAt ℝ (fun y => spin (A y)) x :=
    SpinorMatrixSmooth.spinCLM.differentiableAt.comp x hA
  have hiso : ∀ᶠ y in 𝓝 x, diracAdjoint (spin (A y))*spin (A y)=1 :=
    hdet.mono (fun y hy => spin_dirac_isometry (A y) hy)
  have hh := fderiv_adjointField_source hrho hbeta hL hpos
    (spin_isUnit (A x) hdet.self_of_nhds)
    (Filter.Eventually.of_forall (fun y => spin_gamma5_commute (A y))) hiso v
  have ha : (fun y => spinorAdjoint (psi y)) =ᶠ[𝓝 x]
      adjointField rho beta (fun y => spin (A y)) :=
    heq.mono (fun y hy => congrArg spinorAdjoint hy)
  rw [ha.fderiv_eq, ha.eq_of_nhds]
  exact hh
open SpinorRegularity LocalPolarFields

/-- Every C1 spinor field at a strict regular value has constructed local smooth polar factors whose actual connection gives its genuine full Frechet derivative, without supplied polar data. -/
theorem exists_reconstructed_connection {psi : E → Spinor} {x : E}
    (hpsi : ContDiffAt ℝ 1 psi x) (hreg : Regular (psi x)) :
    ∃ (beta : E → ℝ) (A : E → Mat2),
      ContDiffAt ℝ 1 beta x ∧ ContDiffAt ℝ 1 A x ∧
      (∀ᶠ y in 𝓝 x, 0 < invariantDensity (psi y) ∧ (A y).det = 1 ∧
        psi y = polarSpinor (invariantDensity (psi y)) (beta y) (spin (A y))) ∧
      HasFDerivAt psi ((mulVecCLM (psi x)).comp
        (polarConnection (fun y => invariantDensity (psi y)) beta (fun y => spin (A y)) x)) x := by
  obtain ⟨beta, A, hrho, hbeta, hA, _hL, hevent⟩ := exists_local_polar_fields 1 hpsi hreg
  refine ⟨beta, A, hbeta, hA, hevent, ?_⟩
  have heq : psi =ᶠ[𝓝 x] polarField (fun y => invariantDensity (psi y)) beta (fun y => spin (A y)) :=
    hevent.mono (fun _ hy => hy.2.2)
  exact hasFDerivAt_of_local_polar hrho.differentiableAt_one hbeta.differentiableAt_one
    hA.differentiableAt_one hreg hevent.self_of_nhds.2.1 heq

/-- Every C1 regular original spinor field admits constructed local factors giving both its actual source-signed column derivative and Dirac-adjoint derivative with the same fields. -/
theorem exists_reconstructed_derivative_and_adjoint {psi : E → Spinor} {x : E}
    (hpsi : ContDiffAt ℝ 1 psi x) (hreg : Regular (psi x)) :
    ∃ (beta : E → ℝ) (A : E → Mat2),
      ContDiffAt ℝ 1 beta x ∧ ContDiffAt ℝ 1 A x ∧
      (∀ᶠ y in 𝓝 x, 0 < invariantDensity (psi y) ∧ (A y).det = 1 ∧
        psi y = polarSpinor (invariantDensity (psi y)) (beta y) (spin (A y))) ∧
      (∀ v : E, fderiv ℝ psi x v =
        (((fderiv ℝ (fun y => Real.log (invariantDensity (psi y))) x v / 2 : ℝ) : ℂ) • (1 : Mat) +
          (Complex.I*(fderiv ℝ beta x v : ℂ)/2) • gamma5 +
          spatial (fun y => spin (A y)) x v).mulVec (psi x)) ∧
      (∀ v : E, fderiv ℝ (fun y => spinorAdjoint (psi y)) x v =
        Matrix.vecMul (spinorAdjoint (psi x))
          (((fderiv ℝ (fun y => Real.log (invariantDensity (psi y))) x v / 2 : ℝ) : ℂ) • (1 : Mat) +
            (Complex.I*(fderiv ℝ beta x v : ℂ)/2) • gamma5 -
            spatial (fun y => spin (A y)) x v)) := by
  obtain ⟨beta, A, hrho, hbeta, hA, _hL, hevent⟩ := exists_local_polar_fields 1 hpsi hreg
  have heq : psi =ᶠ[𝓝 x] polarField (fun y => invariantDensity (psi y)) beta (fun y => spin (A y)) :=
    hevent.mono (fun _ hy => hy.2.2)
  have hdet : ∀ᶠ y in 𝓝 x, (A y).det = 1 := hevent.mono (fun _ hy => hy.2.1)
  refine ⟨beta, A, hbeta, hA, hevent, ?_, ?_⟩
  · intro v
    exact fderiv_of_local_polar hrho.differentiableAt_one hbeta.differentiableAt_one
      hA.differentiableAt_one hreg hdet.self_of_nhds heq v
  · intro v
    exact fderiv_adjoint_of_local_polar hrho.differentiableAt_one hbeta.differentiableAt_one
      hA.differentiableAt_one hreg hdet heq v

end FoliationQM.ReconstructedPolarDifferential
