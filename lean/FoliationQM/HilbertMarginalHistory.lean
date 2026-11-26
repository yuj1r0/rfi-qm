module

public import FoliationQM.HilbertFiberObservables
public import FoliationQM.LorentzCoordinates

/-!
# Time histories of the retained Hilbert-space observables

The remote unitary may vary at every time. Equality of the resulting
observable histories transfers any time derivative that exists, without
differentiating an operator-valued propagator.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.HilbertMarginalHistory

open LorentzCoordinates HilbertFiberObservables

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Apply a supplied time-dependent remote unitary to the fiber at each retained position. -/
def evolved (U : ℝ → H ≃ₗᵢ[ℂ] H) (F : ℝ → Spatial → H) (t : ℝ) (x : Spatial) : H :=
  U t (F t x)

/-- Every two-point reduced kernel has the same full time history under remote evolution. -/
theorem kernel_history (U : ℝ → H ≃ₗᵢ[ℂ] H) (F : ℝ → Spatial → H) (x y : Spatial) :
    (fun t => kernel (evolved U F t) x y) = fun t => kernel (F t) x y :=
  funext fun t => kernel_isometry (U t).toLinearIsometry (F t) x y

/-- The Born density at a fixed first position has the same full time history. -/
theorem density_history (U : ℝ → H ≃ₗᵢ[ℂ] H) (F : ℝ → Spatial → H) (x : Spatial) :
    (fun t => density (evolved U F t) x) = fun t => density (F t) x :=
  funext fun t => density_isometry (U t).toLinearIsometry (F t) x

variable [NormedSpace ℝ H] [IsScalarTower ℝ ℂ H]

/-- At a retained position with differentiable spatial fibers the directional current
history is independent of the entire choice of the remote unitary family. -/
theorem current_history (U : ℝ → H ≃ₗᵢ[ℂ] H) (F : ℝ → Spatial → H) (hbar m : ℝ)
    (x v : Spatial) (hF : ∀ t, DifferentiableAt ℝ (F t) x) :
    (fun t => current hbar m (evolved U F t) x v) = fun t => current hbar m (F t) x v :=
  funext fun t => current_isometry (U t).toLinearIsometry hbar m (F t) (hF t) v

/-- Existence and value of the two physical time derivatives transfer from the
undressed observable histories to those with the remote propagation. -/
theorem time_derivatives (U : ℝ → H ≃ₗᵢ[ℂ] H) (F : ℝ → Spatial → H) (hbar m : ℝ)
    (x v : Spatial) (hF : ∀ t, DifferentiableAt ℝ (F t) x) {t r j : ℝ}
    (hr : HasDerivAt (fun s => density (F s) x) r t)
    (hj : HasDerivAt (fun s => current hbar m (F s) x v) j t) :
    HasDerivAt (fun s => density (evolved U F s) x) r t ∧
      HasDerivAt (fun s => current hbar m (evolved U F s) x v) j t := by
  rw [density_history, current_history U F hbar m x v hF]
  exact ⟨hr,hj⟩

end FoliationQM.HilbertMarginalHistory
