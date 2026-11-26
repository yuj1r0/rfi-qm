module
public import FoliationQM.DiracCompactDivergence
public import FoliationQM.DiracVariationFlux
public import FoliationQM.OpenPolarVariations

/-!
# Compact support for the actual Dirac variation flux

For v13 `thm:dirac_lift`, each flux component is supported in the compact
interior test support. Local C¹ regularity of the two fields there makes
the component globally C¹, so its directional derivative has zero integral
on the domain with the stipulated flat volume.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.DiracFluxSupport
open DiracMatrices DiracFieldDensity DiracVariationFlux Set Function MeasureTheory

variable (hbar c : ℝ) {U : Set Covector} {ψ η : Covector → Spinor}

/-- Each component of the actual boundary flux vanishes wherever the test field is zero. -/
theorem flux_eq_zero_of_test_zero {x : Covector} (hη : η x = 0) (μ : Fin 4) :
    flux hbar c ψ η μ x = 0 := by
  simp [flux, hη, DiracAdjoint.bilinear]

/-- Taking the closure of supports retains the containment in the test's topological support. -/
theorem tsupport_flux_subset (ψ η : Covector → Spinor) (μ : Fin 4) :
    tsupport (flux hbar c ψ η μ) ⊆ tsupport η := by
  apply closure_minimal _ (isClosed_tsupport η)
  intro x hx
  by_contra hn
  exact hx (flux_eq_zero_of_test_zero hbar c (image_eq_zero_of_notMem_tsupport hn) μ)

/-- A compact test gives compact flux components for any background field. -/
theorem flux_compact (ψ η : Covector → Spinor) (hc : HasCompactSupport η) (μ : Fin 4) :
    HasCompactSupport (flux hbar c ψ η μ) :=
  hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_flux_subset hbar c ψ η μ)

variable (hψ : ∀ x ∈ U, ContDiffAt ℝ 1 ψ x) (hη : ∀ x ∈ U, ContDiffAt ℝ 1 η x)
  (hc : HasCompactSupport η) (hs : tsupport η ⊆ U)

include hψ hη hs in
/-- Interior regularity suffices for a globally C¹ flux, since the flux is locally zero
off the closed test support. -/
theorem flux_contDiff (μ : Fin 4) : ContDiff ℝ 1 (flux hbar c ψ η μ) :=
  OpenPolarVariations.contDiff_of_tsupport_subset
    (fun x hx => contDiffAt_flux hbar c ψ η μ (hψ x hx) (hη x hx))
    ((tsupport_flux_subset hbar c ψ η μ).trans hs)

include hψ hη hc hs in
/-- The actual direction derivative in the matching spacetime coordinate is integrable
on the whole coordinate space. -/
theorem integrable_flux_deriv (μ : Fin 4) :
    Integrable (fun x => fderiv ℝ (flux hbar c ψ η μ) x (coordinateDirections μ)) :=
  DiracCompactDivergence.integrable_deriv (flux_contDiff hbar c hψ hη hs μ)
    (flux_compact hbar c ψ η hc μ) (coordinateDirections μ)

include hψ hη hc hs in
/-- The integral on the spacetime domain of each actual flux derivative is zero. -/
theorem integral_flux_deriv_zero (μ : Fin 4) :
    (∫ x in U, fderiv ℝ (flux hbar c ψ η μ) x (coordinateDirections μ)) = 0 :=
  DiracCompactDivergence.setIntegral_deriv_zero (flux_contDiff hbar c hψ hη hs μ)
    (flux_compact hbar c ψ η hc μ) ((tsupport_flux_subset hbar c ψ η μ).trans hs) (coordinateDirections μ)

end FoliationQM.DiracFluxSupport
