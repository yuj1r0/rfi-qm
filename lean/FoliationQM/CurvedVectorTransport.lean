module

public import FoliationQM.CurvedCovariantDerivative

/-!
# Covariant transport of genuine coordinate vector fields

Differentiating the actual vector transport germ produces the second
derivative of the coordinate change. The proven Koszul transformation law
cancels precisely that term, giving covariant derivative and acceleration
transport without assuming either tensor identity.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedVectorTransport

open LorentzMatrixGroup RNCCoordinateVolumeChange CurvedScalarAtlasOverlap
  CurvedCovariantDerivative
open scoped Topology Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false

variable {g : Covector → Mat4} {φ W W' : Covector → Covector} {x : Covector}

/-- Differentiating an actual vector transport germ retains the true second derivative of the chart map. -/
theorem transport_derivative (hφ : ContDiffAt ℝ 2 φ x)
    (hW' : DifferentiableAt ℝ W' x) (hW : DifferentiableAt ℝ W (φ x))
    (he : (fun y => fderiv ℝ φ y (W' y)) =ᶠ[𝓝 x] W ∘ φ) (v : Covector) :
    fderiv ℝ φ x (fderiv ℝ W' x v) + fderiv ℝ (fderiv ℝ φ) x v (W' x) =
      fderiv ℝ W (φ x) (fderiv ℝ φ x v) := by
  have hl := (hφ.fderiv_right (m := 1) (by decide)).differentiableAt_one.hasFDerivAt.clm_apply hW'.hasFDerivAt
  have hr := hW.hasFDerivAt.comp x (hφ.differentiableAt (by decide)).hasFDerivAt
  have H := congrArg (fun L : Covector →L[ℝ] Covector => L v)
    (hl.unique (hr.congr_of_eventuallyEq he))
  simpa only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply] using H

/-- The actual covariant derivative transforms by the coordinate derivative when the vector fields agree as transported germs. -/
theorem covDeriv_pullback (hφ : ContDiffAt ℝ 2 φ x) (hg : DifferentiableAt ℝ g (φ x))
    (hs : (g (φ x)).IsSymm) (hu : IsUnit (g (φ x)).det)
    (hJ : IsUnit (jacobianMatrix (fderiv ℝ φ x)).det)
    (hW' : DifferentiableAt ℝ W' x) (hW : DifferentiableAt ℝ W (φ x))
    (he : (fun y => fderiv ℝ φ y (W' y)) =ᶠ[𝓝 x] W ∘ φ) (v : Covector) :
    fderiv ℝ φ x (covDeriv (pullMetric g φ (fderiv ℝ φ)) W' x v) =
      covDeriv g W (φ x) (fderiv ℝ φ x v) := by
  have he₀ : fderiv ℝ φ x (W' x) = W (φ x) := he.self_of_nhds
  simp only [covDeriv, map_add]
  rw [connection_pullback hφ hg hs hu hJ, ← add_assoc, transport_derivative hφ hW' hW he,
    he₀]

/-- Differentiation along the actual transported velocity gives coordinate covariance of its covariant acceleration. -/
theorem acceleration_pullback (hφ : ContDiffAt ℝ 2 φ x) (hg : DifferentiableAt ℝ g (φ x))
    (hs : (g (φ x)).IsSymm) (hu : IsUnit (g (φ x)).det)
    (hJ : IsUnit (jacobianMatrix (fderiv ℝ φ x)).det)
    (hW' : DifferentiableAt ℝ W' x) (hW : DifferentiableAt ℝ W (φ x))
    (he : (fun y => fderiv ℝ φ y (W' y)) =ᶠ[𝓝 x] W ∘ φ) :
    fderiv ℝ φ x (acceleration (pullMetric g φ (fderiv ℝ φ)) W' x) = acceleration g W (φ x) := by
  have he₀ : fderiv ℝ φ x (W' x) = W (φ x) := he.self_of_nhds
  change fderiv ℝ φ x (covDeriv (pullMetric g φ (fderiv ℝ φ)) W' x (W' x)) =
    covDeriv g W (φ x) (W (φ x))
  rw [covDeriv_pullback hφ hg hs hu hJ hW' hW he, he₀]

end FoliationQM.CurvedVectorTransport
