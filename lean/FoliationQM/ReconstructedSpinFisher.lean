module
public import FoliationQM.ReconstructedFrameConnection
public import FoliationQM.SpecialLinearKinetic
/-!
# Actual spin Fisher identity for original regular spinor fields

Sources: v13 `eq:spinor_quadratic_exact`, `eq:sl2c_fisher_metric_main`,
and the forward quadratic identities in `thm:dirac_lift`. The neutralized
kinetic expression uses genuine Frechet derivatives of the original spinor
field. Local equality transfers those derivatives from the reconstructed
polar field. The canonical frame reconstructed from the original spinor
is locally the actual frame of its constructed determinant-one matrix;
therefore its actual spin and velocity derivatives, Fermi--Walker
projection, and spin Fisher density agree with the established quantities.

The final theorem starts with a C1 spinor field at a strictly regular value
and constructs the needed local angle and determinant-one matrix fields.
It retains the original invariant density and canonical reconstructed
frame. The complete complex identity and its faithful real form hold with
the explicit nonzero-c hypothesis and Lorentzian signs. The final result assumes no polar factors, frame, connection expansion,
or derivative identity. Positivity of the Lorentzian quadratic expression,
phase equations, and dynamics are outside these kinematic identities.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
open Filter Topology
namespace FoliationQM.ReconstructedSpinFisher
open DiracMatrices SpinorMatrix SpecialLinearSpin SpinorRegularity
open PolarSpinorBilinears PolarSpinorDifferential NeutralizedSpinorKinetic
open PolarVectorGeometry VelocitySpinKinetic SpinFisherDensity
open ReconstructedFrameGeometry ReconstructedFrameConnection SpecialLinearConnection
open CanonicalDiracContraction RealLorentzFrame

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Eventual equality of actual spinor fields identifies their genuine Frechet derivatives and hence their complete complex neutralized kinetic expressions. -/
theorem fieldKinetic_congr {psi chi : E → Spinor} {x : E}
    (he : psi =ᶠ[𝓝 x] chi) (hbar beta : ℝ) (directions : Fin 4 → E) :
    fieldKinetic hbar beta psi x directions = fieldKinetic hbar beta chi x directions := by
  simp only [fieldKinetic, he.fderiv_eq]

/-- Eventual equality of actual real frame fields identifies the physical spin derivatives and their actual Fermi--Walker projections. -/
theorem fwSpinDerivative_congr {u w : E → Fin 4 → Covector} {x : E}
    (he : u =ᶠ[𝓝 x] w) (c : ℝ) (v : E) :
    fwSpinDerivative c u x v = fwSpinDerivative c w x v := by
  have hs : (fun y => spinVector (u y)) =ᶠ[𝓝 x] (fun y => spinVector (w y)) :=
    he.mono (fun _ hy => congrArg spinVector hy)
  simp only [fwSpinDerivative, he.eq_of_nhds, hs.fderiv_eq]

/-- Eventual equality of actual frame fields identifies the source spin Fisher density through genuine velocity and projected-spin derivative congruence. -/
theorem spinFisherDensity_congr_frame {u w : E → Fin 4 → Covector} {x : E}
    (he : u =ᶠ[𝓝 x] w) (rho beta : E → ℝ) (directions : Fin 4 → E) (hbar c : ℝ) :
    spinFisherDensity rho beta u x directions hbar c =
      spinFisherDensity rho beta w x directions hbar c := by
  have hv : (fun y => velocity c (u y)) =ᶠ[𝓝 x] (fun y => velocity c (w y)) :=
    he.mono (fun _ hy => congrArg (velocity c) hy)
  simp only [spinFisherDensity, fwSpinDerivative_congr he, hv.fderiv_eq]

/-- A genuine local determinant-one polar representation transfers the full complex kinetic identity to the original spinor and its canonical reconstructed frame. -/
theorem fieldKinetic_of_local_polar {psi : E → Spinor} {rho beta : E → ℝ}
    {A : E → Mat2} {x : E}
    (hrho : DifferentiableAt ℝ rho x) (hbeta : DifferentiableAt ℝ beta x)
    (hA : DifferentiableAt ℝ A x)
    (he : ∀ᶠ y in 𝓝 x, 0 < rho y ∧ (A y).det = 1 ∧
      psi y = polarSpinor (rho y) (beta y) (spin (A y)))
    (directions : Fin 4 → E) (hbar c : ℝ) (hc : c ≠ 0) :
    fieldKinetic hbar (beta x) psi x directions =
      ((rho x * (∑ mu, sign mu *
          (spinCoefficient hbar (fun nu => bodyOmega A x (directions nu)) mu)^2) +
        spinFisherDensity rho beta (fun y => reconstructedFrame (psi y))
          x directions hbar c : ℝ) : ℂ) := by
  have hdet : ∀ᶠ y in 𝓝 x, (A y).det = 1 := he.mono (fun _ hy => hy.2.1)
  have hpsi : psi =ᶠ[𝓝 x] polarField rho beta (fun y => spin (A y)) :=
    he.mono (fun _ hy => hy.2.2)
  rw [fieldKinetic_congr hpsi hbar (beta x) directions,
    SpecialLinearKinetic.fieldKinetic_eq_spinFisher hrho hbeta hA
      he.self_of_nhds.1 hdet directions hbar c hc,
    ← spinFisherDensity_congr_frame (eventually_frame_of_local_polar he) rho beta
      directions hbar c]

/-- The faithful real kinetic expression of the original locally reconstructed field equals its actual spin-connection square plus canonical spin Fisher density. -/
theorem fieldKineticRe_of_local_polar {psi : E → Spinor} {rho beta : E → ℝ}
    {A : E → Mat2} {x : E}
    (hrho : DifferentiableAt ℝ rho x) (hbeta : DifferentiableAt ℝ beta x)
    (hA : DifferentiableAt ℝ A x)
    (he : ∀ᶠ y in 𝓝 x, 0 < rho y ∧ (A y).det = 1 ∧
      psi y = polarSpinor (rho y) (beta y) (spin (A y)))
    (directions : Fin 4 → E) (hbar c : ℝ) (hc : c ≠ 0) :
    fieldKineticRe hbar (beta x) psi x directions =
      rho x * (∑ mu, sign mu *
          (spinCoefficient hbar (fun nu => bodyOmega A x (directions nu)) mu)^2) +
        spinFisherDensity rho beta (fun y => reconstructedFrame (psi y))
          x directions hbar c := by
  exact congrArg Complex.re (fieldKinetic_of_local_polar hrho hbeta hA he directions hbar c hc)

/-- Every C1 spinor field at a strict regular value has constructed local polar fields giving the complete complex and faithful real spin Fisher identities for the original derivatives and canonical reconstructed frame. -/
theorem exists_reconstructed_spinFisher {psi : E → Spinor} {x : E}
    (hpsi : ContDiffAt ℝ 1 psi x) (hreg : Regular (psi x))
    (directions : Fin 4 → E) (hbar c : ℝ) (hc : c ≠ 0) :
    ∃ (beta : E → ℝ) (A : E → Mat2),
      ContDiffAt ℝ 1 beta x ∧ ContDiffAt ℝ 1 A x ∧
      (∀ᶠ y in 𝓝 x, 0 < invariantDensity (psi y) ∧ (A y).det = 1 ∧
        psi y = polarSpinor (invariantDensity (psi y)) (beta y) (spin (A y))) ∧
      fieldKinetic hbar (beta x) psi x directions =
        ((invariantDensity (psi x) * (∑ mu, sign mu *
            (spinCoefficient hbar (fun nu => bodyOmega A x (directions nu)) mu)^2) +
          spinFisherDensity (fun y => invariantDensity (psi y)) beta
            (fun y => reconstructedFrame (psi y)) x directions hbar c : ℝ) : ℂ) ∧
      fieldKineticRe hbar (beta x) psi x directions =
        invariantDensity (psi x) * (∑ mu, sign mu *
            (spinCoefficient hbar (fun nu => bodyOmega A x (directions nu)) mu)^2) +
          spinFisherDensity (fun y => invariantDensity (psi y)) beta
            (fun y => reconstructedFrame (psi y)) x directions hbar c := by
  obtain ⟨beta, A, hrho, hbeta, hA, _hL, he⟩ :=
    LocalPolarFields.exists_local_polar_fields 1 hpsi hreg
  exact ⟨beta, A, hbeta, hA, he,
    fieldKinetic_of_local_polar hrho.differentiableAt_one hbeta.differentiableAt_one
      hA.differentiableAt_one he directions hbar c hc,
    fieldKineticRe_of_local_polar hrho.differentiableAt_one hbeta.differentiableAt_one
      hA.differentiableAt_one he directions hbar c hc⟩

end FoliationQM.ReconstructedSpinFisher
