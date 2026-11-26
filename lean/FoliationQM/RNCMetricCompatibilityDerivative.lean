module

public import FoliationQM.RNCNormalChart

/-!
# Differentiated metric compatibility in normal coordinates

Metric compatibility holds on a neighborhood of the chart center. Differentiating
it there expresses every metric Hessian entry in terms of first derivatives of
Christoffel symbols and the value of the metric. At the center, lowering an
index simply multiplies its component by the appropriate Lorentzian sign.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.RNCMetricCompatibilityDerivative

open LorentzMatrixGroup RealLorentzFrame RNCCoordinateConnection RNCNormalChart Filter
open scoped Matrix.Norms.Operator BigOperators Topology

variable {g : Covector → Mat4}

/-- Local invertibility and symmetry give metric compatibility on a neighborhood of the center. -/
theorem compatibility_germ (h : IsNormal g) (hg : ContDiffAt ℝ 2 g 0) (b i j : Fin 4) :
    (fun y => dG g y (axis b) i j) =ᶠ[𝓝 0] fun y =>
      (∑ r, g y j r * christoffel g y r b i) + ∑ r, g y i r * christoffel g y r b j := by
  have hu : ∀ᶠ y in 𝓝 0, IsUnit (g y) :=
    hg.continuousAt.eventually (Units.isOpen.mem_nhds (center_unit h))
  filter_upwards [hu, PolarRegularity.eventually_differentiableAt_of_contDiffAt_two hg,
    eventually_eventually_nhds.2 h.symmetric] with y hy hd hs
  exact metric_compatibility hy (dG_isSymm hd hs) b i j

set_option backward.isDefEq.respectTransparency false in
/-- The Hessian of each matrix entry is the sum of two lowered connection derivatives. -/
theorem hessian_metric_compatibility (h : IsNormal g) (hg : ContDiffAt ℝ 2 g 0)
    (a b i j : Fin 4) :
    (fderiv ℝ (fderiv ℝ g) 0 (axis a) (axis b)) i j =
      (∑ r, eta j r * fderiv ℝ (fun y => christoffel g y r b i) 0 (axis a)) +
      ∑ r, eta i r * fderiv ℝ (fun y => christoffel g y r b j) 0 (axis a) := by
  let entry (k l : Fin 4) : Mat4 →L[ℝ] ℝ := (Matrix.entryLinearMap ℝ ℝ k l).toContinuousLinearMap
  have hd := hg.differentiableAt (by decide)
  have hprod (k r l : Fin 4) :
      HasFDerivAt (fun y => g y k r * christoffel g y r b l)
        (eta k r • fderiv ℝ (fun y => christoffel g y r b l) 0) 0 := by
    have he : HasFDerivAt (fun y => g y k r) ((entry k r).comp (fderiv ℝ g 0)) 0 :=
      (entry k r).hasFDerivAt.comp 0 hd.hasFDerivAt
    have hc := (contDiffAt_christoffel hg (center_unit h) r b l).differentiableAt_one.hasFDerivAt
    simpa only [h.metric_center, connection_zero h hd, zero_smul, add_zero] using he.fun_mul hc
  have hsum (k l : Fin 4) :
      HasFDerivAt (fun y => ∑ r, g y k r * christoffel g y r b l)
        (∑ r, eta k r • fderiv ℝ (fun y => christoffel g y r b l) 0) 0 :=
    HasFDerivAt.fun_sum fun r _ => hprod k r l
  have hright := ((hsum j i).fun_add (hsum i j)).congr_of_eventuallyEq (compatibility_germ h hg b i j)
  let L : (Covector →L[ℝ] Mat4) →L[ℝ] ℝ :=
    (entry i j).comp (ContinuousLinearMap.apply ℝ Mat4 (axis b))
  have hleft : HasFDerivAt (fun y => dG g y (axis b) i j)
      (L.comp (fderiv ℝ (fderiv ℝ g) 0)) 0 :=
    L.hasFDerivAt.comp 0 ((hg.fderiv_right (m := 1) (by decide)).differentiableAt_one.hasFDerivAt)
  have hv := congrArg (fun T : Covector →L[ℝ] ℝ => T (axis a)) (hleft.unique hright)
  change (L.comp (fderiv ℝ (fderiv ℝ g) 0)) (axis a) = _
  simpa only [add_apply, sum_apply, smul_apply, smul_eq_mul] using hv

/-- In the orthonormal frame, each lowered index contributes its single diagonal sign. -/
theorem hessian_metric_entries (h : IsNormal g) (hg : ContDiffAt ℝ 2 g 0) (a b i j : Fin 4) :
    (fderiv ℝ (fderiv ℝ g) 0 (axis a) (axis b)) i j =
      sign j * fderiv ℝ (fun y => christoffel g y j b i) 0 (axis a) +
      sign i * fderiv ℝ (fun y => christoffel g y i b j) 0 (axis a) := by
  rw [hessian_metric_compatibility h hg]
  simp [eta, Matrix.diagonal_apply, ite_mul]

/-- Diagonal metric Hessian entries are twice the corresponding lowered connection derivative. -/
theorem hessian_metric_diagonal (h : IsNormal g) (hg : ContDiffAt ℝ 2 g 0) (a b i : Fin 4) :
    (fderiv ℝ (fderiv ℝ g) 0 (axis a) (axis b)) i i =
      2 * sign i * fderiv ℝ (fun y => christoffel g y i b i) 0 (axis a) := by
  rw [hessian_metric_entries h hg]
  ring

end FoliationQM.RNCMetricCompatibilityDerivative
