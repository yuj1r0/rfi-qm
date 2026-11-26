module
public import FoliationQM.RotatedPolarChart

/-!
# Constructed local smooth polar fields around every regular spinor

Source: v13 `eq:takabayasi_polar` and the local reconstruction component of
`prop:takabayasi`. The principal and rotated determinant branches cover
the strict invariant regular domain. Their actual inverse functions give
an open smooth coordinate choice around every regular spinor. Composing
one such choice with an actual smooth spinor field gives local angle and
determinant-one matrix fields, with the original field reconstructed on
a neighborhood and its actual invariant density retained.

The final theorem writes the reconstruction with the genuine matrix
exponential. No polar coordinates, reconstruction equality, or derivative
identity are supplied as premises. This is a local result in the concrete
determinant-one representation; it does not assert a global real angle,
a global smooth quotient-bundle identification, or an abstract Spin or
Lorentz-frame classification.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator Topology
namespace FoliationQM.LocalPolarFields
open DiracMatrices SpinorMatrix SpinorRegularity SpecialLinearSpin
open PolarSpinorBilinears SpinorMatrixSmooth PrincipalPolarSmooth RegularPolarReconstruction
open RotatedPolarChart ChiralMatrix

/-- The strict scalar-pseudoscalar regular spinor domain is open, by the actual determinant criterion. -/
theorem regularDomain_isOpen : IsOpen {psi : Spinor | Regular psi} := by
  have h : IsOpen {psi : Spinor | Matrix.det (toMatrix psi) ≠ 0} :=
    isOpen_ne.preimage (contDiff_spinorDet 0).continuous
  simpa only [det_ne_zero_iff_regular] using h

/-- Every regular spinor has an open neighborhood with actual smooth polar inverse functions and exact reconstruction by determinant-one matrix representatives. -/
theorem exists_open_polar_chart (n : WithTop ℕ∞) {psi : Spinor}
    (hreg : Regular psi) :
    ∃ (U : Set Spinor) (beta : Spinor → ℝ) (A : Spinor → Mat2),
      IsOpen U ∧ psi ∈ U ∧ ContDiffOn ℝ n invariantDensity U ∧
      ContDiffOn ℝ n beta U ∧ ContDiffOn ℝ n A U ∧
      ContDiffOn ℝ n (fun q => spin (A q)) U ∧
      ∀ q ∈ U, 0 < invariantDensity q ∧ Matrix.det (A q) = 1 ∧
        q = polarSpinor (invariantDensity q) (beta q) (spin (A q)) := by
  rcases regular_two_chart_cover hreg with hp | hr
  · refine ⟨PrincipalDomain, determinantPhase, normalizedMatrix, principalDomain_isOpen,
      hp, ?_, contDiffOn_determinantPhase n, contDiffOn_normalizedMatrix n,
      contDiffOn_reconstructedSpin n, ?_⟩
    · intro q hq
      exact (contDiffAt_invariantDensity n (principalDomain_regular hq)).contDiffWithinAt
    · intro q hq
      have hqr := principalDomain_regular hq
      exact ⟨hqr, normalizedMatrix_det hqr, regular_reconstruction hqr⟩
  · refine ⟨RotatedDomain, rotatedPhase, rotatedMatrix, rotatedDomain_isOpen,
      hr, ?_, ?_, ?_, ?_, ?_⟩
    · intro q hq
      exact (contDiffAt_invariantDensity n (rotatedDomain_regular hq)).contDiffWithinAt
    · intro q hq
      exact (contDiffAt_rotatedPhase n hq).contDiffWithinAt
    · intro q hq
      exact (contDiffAt_rotatedMatrix n hq).contDiffWithinAt
    · intro q hq
      exact (contDiffAt_rotatedSpin n hq).contDiffWithinAt
    · intro q hq
      exact ⟨rotatedDomain_regular hq, rotatedMatrix_det hq, rotated_reconstruction hq⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every actual smooth spinor field at a regular value has locally reconstructing smooth angle and determinant-one matrix fields, with its actual invariant density and spin representative smooth to the same order. -/
theorem exists_local_polar_fields (n : WithTop ℕ∞) {psi : E → Spinor} {x : E}
    (hpsi : ContDiffAt ℝ n psi x) (hreg : Regular (psi x)) :
    ∃ (beta : E → ℝ) (A : E → Mat2),
      ContDiffAt ℝ n (fun y => invariantDensity (psi y)) x ∧
      ContDiffAt ℝ n beta x ∧ ContDiffAt ℝ n A x ∧
      ContDiffAt ℝ n (fun y => spin (A y)) x ∧
      ∀ᶠ y in 𝓝 x, 0 < invariantDensity (psi y) ∧ Matrix.det (A y) = 1 ∧
        psi y = polarSpinor (invariantDensity (psi y)) (beta y) (spin (A y)) := by
  obtain ⟨U, beta, A, hU, hxU, hrho, hbeta, hA, hL, hrecon⟩ := exists_open_polar_chart n hreg
  have hneigh : U ∈ 𝓝 (psi x) := hU.mem_nhds hxU
  refine ⟨fun y => beta (psi y), fun y => A (psi y),
    (hrho.contDiffAt hneigh).comp x hpsi, (hbeta.contDiffAt hneigh).comp x hpsi,
    (hA.contDiffAt hneigh).comp x hpsi, (hL.contDiffAt hneigh).comp x hpsi, ?_⟩
  have hevent : ∀ᶠ y in 𝓝 x, psi y ∈ U := hpsi.continuousAt.tendsto.eventually hneigh
  filter_upwards [hevent] with y hy
  exact hrecon (psi y) hy

/-- The constructed local polar fields reconstruct the actual spinor field using the genuine chiral matrix exponential and the actual invariant square-root density. -/
theorem exists_local_polar_fields_exponential (n : WithTop ℕ∞) {psi : E → Spinor} {x : E}
    (hpsi : ContDiffAt ℝ n psi x) (hreg : Regular (psi x)) :
    ∃ (beta : E → ℝ) (A : E → Mat2),
      ContDiffAt ℝ n (fun y => invariantDensity (psi y)) x ∧
      ContDiffAt ℝ n beta x ∧ ContDiffAt ℝ n A x ∧
      ContDiffAt ℝ n (fun y => spin (A y)) x ∧
      ∀ᶠ y in 𝓝 x, 0 < invariantDensity (psi y) ∧ Matrix.det (A y) = 1 ∧
        psi y = (Real.sqrt (invariantDensity (psi y)) : ℂ) •
          ((NormedSpace.exp ((Complex.I * (beta y : ℂ) / 2) • gamma5) *
            spin (A y)).mulVec restSpinor) := by
  obtain ⟨beta, A, hrho, hbeta, hA, hL, hevent⟩ := exists_local_polar_fields n hpsi hreg
  refine ⟨beta, A, hrho, hbeta, hA, hL, ?_⟩
  simpa only [exp_chiral, polarSpinor] using hevent

end FoliationQM.LocalPolarFields
