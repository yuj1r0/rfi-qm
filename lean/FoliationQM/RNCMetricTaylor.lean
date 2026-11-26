module

public import FoliationQM.RNCNormalRiemann
public import FoliationQM.RNCRicciHalfDensity

/-!
# The cubic remainder in the normal-coordinate metric expansion

The free metric indices in v13 Eq. `rnc_g` are retained throughout.
Agreement of the full two-jet of each component with its curvature
polynomial gives the uniform cubic bound for a locally C³ metric.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.RNCMetricTaylor

open LorentzMatrixGroup RealLorentzFrame RNCCoordinateConnection RNCNormalChart RNCNormalRiemann
open RNCHalfDensityJet Asymptotics
open scoped Matrix.Norms.Operator BigOperators Topology
set_option backward.isDefEq.respectTransparency false

variable {g : Covector → Mat4}

/-- Each component has its orthonormal-frame value, with vanishing first derivative. -/
theorem component_value_gradient (h : IsNormal g) (hg : DifferentiableAt ℝ g 0) (i j : Fin 4) :
    g 0 i j = eta i j ∧ fderiv ℝ (fun y => g y i j) 0 = 0 := by
  let L : Mat4 →L[ℝ] ℝ := (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap
  refine ⟨by rw [h.metric_center], ?_⟩
  change fderiv ℝ (L ∘ g) 0 = 0
  rw [(L.hasFDerivAt.comp 0 hg.hasFDerivAt).fderiv, metric_gradient_zero h hg,
    ContinuousLinearMap.comp_zero]

/-- As a bilinear map, the component Hessian is the symmetrized curvature form.
The factor four converts the half-density polynomial normalization −1/12 to −1/3. -/
theorem component_hessian (h : IsNormal g) (hg : ContDiffAt ℝ 2 g 0) (i j : Fin 4) :
    fderiv ℝ (fderiv ℝ (fun y => g y i j)) 0 =
      hessian (fun a b => 4 * loweredRiemann g 0 i a j b) := by
  apply RNCRicciHalfDensity.bilinear_ext_axis
  intro a b
  rw [RNCMetricNormalization.hessian_entry hg, hessian_metric_riemann h hg, hessian_apply]
  simp only [axis, form_basis]
  ring

/-- Evaluation on two arbitrary directions gives the unspecialized mixed curvature formula. -/
theorem component_hessian_apply (h : IsNormal g) (hg : ContDiffAt ℝ 2 g 0)
    (i j : Fin 4) (u v : Covector) :
    fderiv ℝ (fderiv ℝ (fun y => g y i j)) 0 u v =
      -((∑ a, ∑ b, loweredRiemann g 0 i a j b * u a * v b) +
        ∑ a, ∑ b, loweredRiemann g 0 i a j b * v a * u b) / 3 := by
  rw [component_hessian h hg, hessian_apply, form_apply, form_apply]
  simp only [mul_assoc, ← Finset.mul_sum]
  ring

/-- Every covariant metric component has the v13 curvature polynomial with a uniform cubic remainder. -/
theorem component_expansion (h : IsNormal g) (hg : ContDiffAt ℝ 3 g 0) (i j : Fin 4) :
    (fun y => g y i j - (eta i j - (1/3 : ℝ) * ∑ a, ∑ b, loweredRiemann g 0 i a j b * y a * y b))
      =O[𝓝 0] fun y => ‖y‖ ^ 3 := by
  let L : Mat4 →L[ℝ] ℝ := (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap
  let w (y : Covector) := g y i j + (1 - eta i j)
  let A : Mat4 := fun a b => 4 * loweredRiemann g 0 i a j b
  have hw : ContDiffAt ℝ 3 w 0 := (L.contDiff.contDiffAt.comp 0 hg).add contDiffAt_const
  have hdw : fderiv ℝ w = fderiv ℝ (fun y => g y i j) :=
    funext fun _ => fderiv_add_const (1 - eta i j)
  have hj := component_value_gradient h (hg.differentiableAt (by decide)) i j
  have hr : (w - weight A) =O[𝓝 0] fun y => ‖y‖ ^ 3 := by
    apply (RNCExpansionContraction.expansion_iff_jet hw).mpr
    refine ⟨by simp [w, hj.1], by rw [hdw, hj.2], ?_⟩
    rw [hdw]
    exact component_hessian h (hg.of_le (by decide)) i j
  apply hr.congr_left
  intro y
  simp only [Pi.sub_apply, w, weight_eq, A, mul_assoc, ← Finset.mul_sum]
  ring

end FoliationQM.RNCMetricTaylor
