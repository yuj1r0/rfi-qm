module

public import FoliationQM.RNCLorentzContraction
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Lorentz normalization of the metric jet

In v13 Lemma 9.1, a normal-coordinate metric is Minkowskian at the center.
Left multiplication by the constant inverse Minkowski matrix sends this
value to the identity. Its determinant is the negative of the metric
determinant, and its Hessian trace is the signed trace of the metric Hessian.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.RNCMetricNormalization

open LorentzMatrixGroup RealLorentzFrame
open scoped Matrix.Norms.Operator ContDiff

variable {E : Type*} {g : E → Mat4} {x : E}

/-- The normalized matrix field raises the first metric index with the center's inverse Minkowski matrix. -/
def normalize (g : E → Mat4) (x : E) : Mat4 := eta * g x

/-- Left multiplication by the inverse Minkowski metric is continuous and real linear. -/
def raiseIndex : Mat4 →L[ℝ] Mat4 := ContinuousLinearMap.mul ℝ Mat4 eta

/-- The normalized matrix determinant is the negative of the original Lorentz metric determinant. -/
theorem det_normalize (g : E → Mat4) (x : E) : (normalize g x).det = -(g x).det := by
  simp [normalize, Matrix.det_mul, eta_det]

/-- At a Minkowskian center the normalized metric matrix is the identity. -/
theorem normalize_center [Zero E] (h₀ : g 0 = eta) : normalize g 0 = 1 := by
  simpa only [normalize, h₀] using eta_sq

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Normalization preserves local coordinate regularity of every order. -/
theorem contDiffAt_normalize {n : WithTop ℕ∞} (hg : ContDiffAt ℝ n g x) :
    ContDiffAt ℝ n (normalize g) x :=
  raiseIndex.contDiff.contDiffAt.comp x hg

/-- The actual derivative of normalization is left multiplication applied to the field derivative. -/
theorem fderiv_normalize (hg : DifferentiableAt ℝ g x) :
    fderiv ℝ (normalize g) x = raiseIndex.comp (fderiv ℝ g x) :=
  (raiseIndex.hasFDerivAt.comp x hg.hasFDerivAt).fderiv

/-- The actual first metric variation has its first index raised by the fixed metric. -/
theorem fderiv_normalize_apply (hg : DifferentiableAt ℝ g x) (v : E) :
    fderiv ℝ (normalize g) x v = eta * fderiv ℝ g x v := by
  rw [fderiv_normalize hg]
  rfl

/-- Vanishing of the unnormalized first metric jet implies vanishing after normalization. -/
theorem fderiv_normalize_zero (hg : DifferentiableAt ℝ g x) (h₁ : fderiv ℝ g x = 0) :
    fderiv ℝ (normalize g) x = 0 := by
  rw [fderiv_normalize hg, h₁, ContinuousLinearMap.comp_zero]

/-- A continuous linear observable commutes with the actual mixed Hessian of a local C² field. -/
private theorem hessian_comp_linear {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : E → F}
    (L : F →L[ℝ] G) (hf : ContDiffAt ℝ 2 f x) (u v : E) :
    fderiv ℝ (fderiv ℝ (L ∘ f)) x u v = L (fderiv ℝ (fderiv ℝ f) x u v) := by
  have h := congrArg (fun A => A ![u, v])
    (L.iteratedFDeriv_comp_left hf (i := 2) (by simp))
  simpa only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using h

/-- Both directional slots of the actual Hessian commute with raising the first metric index. -/
theorem hessian_normalize_apply (hg : ContDiffAt ℝ 2 g x) (u v : E) :
    fderiv ℝ (fderiv ℝ (normalize g)) x u v = eta * fderiv ℝ (fderiv ℝ g) x u v :=
  hessian_comp_linear raiseIndex hg u v

/-- The trace of the normalized Hessian equals contraction of the metric Hessian with the inverse Minkowski metric. -/
theorem trace_hessian_normalize (hg : ContDiffAt ℝ 2 g x) (u v : E) :
    (fderiv ℝ (fderiv ℝ (normalize g)) x u v).trace =
      RNCLorentzContraction.contract (fderiv ℝ (fderiv ℝ g) x u v) := by
  rw [hessian_normalize_apply hg, RNCLorentzContraction.contract]

/-- Differentiating a metric component twice evaluates the matrix Hessian at that same component. -/
theorem hessian_entry (hg : ContDiffAt ℝ 2 g x) (u v : E) (i j : Fin 4) :
    fderiv ℝ (fderiv ℝ (fun y => g y i j)) x u v = (fderiv ℝ (fderiv ℝ g) x u v) i j :=
  hessian_comp_linear (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap hg u v

/-- The normalized Hessian trace is the time-component Hessian minus the three spatial-component Hessians. -/
theorem trace_hessian_normalize_entries (hg : ContDiffAt ℝ 2 g x) (u v : E) :
    (fderiv ℝ (fderiv ℝ (normalize g)) x u v).trace =
      fderiv ℝ (fderiv ℝ (fun y => g y 0 0)) x u v -
      fderiv ℝ (fderiv ℝ (fun y => g y 1 1)) x u v -
      fderiv ℝ (fderiv ℝ (fun y => g y 2 2)) x u v -
      fderiv ℝ (fderiv ℝ (fun y => g y 3 3)) x u v := by
  simp only [trace_hessian_normalize hg, RNCLorentzContraction.contract_diagonal, hessian_entry hg]

end FoliationQM.RNCMetricNormalization
