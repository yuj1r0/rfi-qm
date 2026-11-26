module

public import FoliationQM.MassShellChart
public import Mathlib.Analysis.Calculus.FDeriv.ContinuousAlternatingMap

/-!
# Genuine pullback forms on positive-energy shell coordinates

Source: v13 `thm:contact_period`. These are actual continuous alternating
forms pulled back using Mathlib's Frechet derivative of the square-root shell
chart. The exterior derivative is computed by Mathlib's pullback naturality
theorem. Every pointwise conclusion only assumes positive energy, including
positive-energy massless points. The conjugate coordinate pair proves that
the restricted differential itself is nonzero, independently of whether the
seven-dimensional contact volume vanishes.
-/

@[expose] public section

noncomputable section
namespace FoliationQM.MassShellForms
open ContactReeb MassShellChart

/-- The actual Liouville one-form pulled back by the derivative of the mass-shell chart. -/
def pullback (m c : ℝ) (q : Space) : Space [⋀^Fin 1]→L[ℝ] ℝ :=
  (LiouvilleDifferential.liouville (chart m c q)).compContinuousLinearMap
    (fderiv ℝ (chart m c) q)

/-- The actual pulled-back Liouville form has the source seven-coordinate expression. -/
theorem pullback_apply {m c : ℝ} {q : Space} (hE : 0 < energy m c q)
    (v : Fin 1 → Space) : pullback m c q v =
    -(energy m c q * (v 0) 0 + q 2 * (v 0) 1 + q 4 * (v 0) 3 + q 6 * (v 0) 5) := by
  change LiouvilleDifferential.liouville (chart m c q)
    (fun i => fderiv ℝ (chart m c) q (v i)) = _
  rw [LiouvilleDifferential.liouville_apply, fderiv_chart hE, chartDerivative_apply]
  simp [alpha, pairing, chart, position, Fin.sum_univ_succ]
  ring

/-- The genuine Liouville pullback is differentiable at every positive-energy point. -/
theorem differentiableAt_pullback {m c : ℝ} {q : Space} (hE : 0 < energy m c q) :
    DifferentiableAt ℝ (pullback m c) q := by
  have hf := contDiffAt_chart hE
  have hdf : DifferentiableAt ℝ (fderiv ℝ (chart m c)) q :=
    (hf.fderiv_right (m := 1) (by simp)).differentiableAt (by norm_num)
  exact ((LiouvilleDifferential.hasFDerivAt_liouville _).differentiableAt.comp q
    (hasFDerivAt_chart hE).differentiableAt).continuousAlternatingMapCompContinuousLinearMap hdf

/-- The actual exterior derivative is the canonical ambient two-form pulled back by the chart derivative. -/
theorem extDeriv_pullback {m c : ℝ} {q : Space} (hE : 0 < energy m c q) :
    extDeriv (pullback m c) q =
    LiouvilleDifferential.canonicalForm.compContinuousLinearMap (chartDerivative m c q) := by
  unfold pullback
  rw [_root_.extDeriv_pullback (LiouvilleDifferential.hasFDerivAt_liouville _).differentiableAt
    (contDiffAt_chart hE) (by simp)]
  rw [LiouvilleDifferential.extDeriv_liouville, fderiv_chart hE]

/-- Evaluate the genuine shell exterior derivative by the canonical bilinear pairing. -/
theorem extDeriv_pullback_apply {m c : ℝ} {q : Space} (hE : 0 < energy m c q)
    (v : Fin 2 → Space) : extDeriv (pullback m c) q v =
    canonicalTwo (chartDerivative m c q (v 0)) (chartDerivative m c q (v 1)) := by
  rw [extDeriv_pullback hE]
  exact LiouvilleDifferential.canonicalForm_apply _

/-- The actual exterior derivative has the explicit seven-coordinate shell formula. -/
theorem extDeriv_pullback_coordinates {m c : ℝ} {q : Space} (hE : 0 < energy m c q)
    (v : Fin 2 → Space) : extDeriv (pullback m c) q v =
    ((v 0) 0 * (q 2*(v 1) 2 + q 4*(v 1) 4 + q 6*(v 1) 6) -
      (v 1) 0 * (q 2*(v 0) 2 + q 4*(v 0) 4 + q 6*(v 0) 6)) / energy m c q +
      ((v 0) 1*(v 1) 2-(v 1) 1*(v 0) 2) +
      ((v 0) 3*(v 1) 4-(v 1) 3*(v 0) 4) +
      ((v 0) 5*(v 1) 6-(v 1) 5*(v 0) 6) := by
  rw [extDeriv_pullback_apply hE, chartDerivative_apply, chartDerivative_apply]
  simp [canonicalTwo, pairing, position, Fin.sum_univ_succ]
  ring

/-- The actual shell exterior derivative evaluates to one on the first conjugate coordinate pair. -/
theorem extDeriv_pullback_conjugate_pair {m c : ℝ} {q : Space} (hE : 0 < energy m c q) :
    extDeriv (pullback m c) q ![Pi.single 1 1, Pi.single 2 1] = 1 := by
  rw [extDeriv_pullback_coordinates hE]
  norm_num

/-- The actual shell exterior derivative is nonzero at every positive-energy point. -/
theorem extDeriv_pullback_ne_zero {m c : ℝ} {q : Space} (hE : 0 < energy m c q) :
    extDeriv (pullback m c) q ≠ 0 := by
  intro hz
  have h := extDeriv_pullback_conjugate_pair hE
  rw [hz] at h
  norm_num at h

end FoliationQM.MassShellForms
