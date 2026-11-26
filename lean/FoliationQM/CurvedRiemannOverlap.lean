module

public import FoliationQM.CurvedConnectionComponents

/-!
# Riemann curvature on nonlinear chart overlaps

Differentiating the Levi-Civita transformation law on a neighborhood
produces the chart Hessian and third derivative. Their symmetric terms
cancel in the antisymmetrized curvature of the two coordinate connections.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedRiemannOverlap

open LorentzMatrixGroup RNCCoordinateVolumeChange CurvedScalarAtlasOverlap CurvedConnectionComponents
open ContinuousLinearMap Filter
open scoped Topology Matrix.Norms.Operator

variable {φ : Covector → Covector} {g : Covector → Mat4} {x : Covector}

/-- A C³ coordinate change preserves the C² regularity required to compute curvature. -/
theorem contDiffAt_pullMetric (hφ : ContDiffAt ℝ 3 φ x) (hg : ContDiffAt ℝ 2 g (φ x)) :
    ContDiffAt ℝ 2 (pullMetric g φ (fderiv ℝ φ)) x := by
  let J (y : Covector) := jacobianMatrix (fderiv ℝ φ y)
  have hd : ContDiffAt ℝ 2 J x := jacobianMap.contDiff.contDiffAt.comp x (hφ.fderiv_right (by decide))
  let transpose : Mat4 →L[ℝ] Mat4 :=
    (Matrix.transposeLinearEquiv (Fin 4) (Fin 4) ℝ ℝ).toLinearMap.toContinuousLinearMap
  exact ((transpose.contDiff.contDiffAt.comp x hd).mul (hg.comp x (hφ.of_le (by decide)))).mul hd

/-- The connection transformation holds as a germ, so its two sides can be differentiated. -/
theorem connection_pullback_germ (hφ : ContDiffAt ℝ 3 φ x) (hg : ContDiffAt ℝ 2 g (φ x))
    (hs : ∀ᶠ y in 𝓝 (φ x), (g y).IsSymm) (hu : IsUnit (g (φ x)).det)
    (hJ : IsUnit (jacobianMatrix (fderiv ℝ φ x)).det) (u v : Covector) :
    (fun y => fderiv ℝ φ y (connection (pullMetric g φ (fderiv ℝ φ)) y u v)) =ᶠ[𝓝 x]
      fun y => fderiv ℝ (fderiv ℝ φ) y u v +
        connection g (φ y) (fderiv ℝ φ y u) (fderiv ℝ φ y v) := by
  have hG : ∀ᶠ y in 𝓝 (φ x), IsUnit (g y) :=
    hg.continuousAt.eventually (Units.isOpen.mem_nhds ((g (φ x)).isUnit_iff_isUnit_det.mpr hu))
  have hC : ContinuousAt (fun y => jacobianMatrix (fderiv ℝ φ y)) x :=
    jacobianMap.continuous.continuousAt.comp ((hφ.fderiv_right (m := 2) (by decide)).continuousAt)
  have hI : ∀ᶠ y in 𝓝 x, IsUnit (jacobianMatrix (fderiv ℝ φ y)) :=
    hC.eventually (Units.isOpen.mem_nhds ((jacobianMatrix (fderiv ℝ φ x)).isUnit_iff_isUnit_det.mpr hJ))
  filter_upwards [hφ.eventually (by norm_num), hφ.continuousAt.eventually (hg.eventually (by norm_num)),
    hφ.continuousAt.eventually hs, hφ.continuousAt.eventually hG, hI] with y hyφ hyg hys hyu hyJ
  exact connection_pullback (hyφ.of_le (by decide)) (hyg.differentiableAt (by decide)) hys
    ((g (φ y)).isUnit_iff_isUnit_det.mp hyu) ((jacobianMatrix (fderiv ℝ φ y)).isUnit_iff_isUnit_det.mp hyJ) u v

set_option backward.isDefEq.respectTransparency false in
/-- The differentiated connection law includes the three derivatives of the transition
and the derivatives of the target connection and its two vector arguments. -/
theorem connection_pullback_derivative (hφ : ContDiffAt ℝ 3 φ x) (hg : ContDiffAt ℝ 2 g (φ x))
    (hs : ∀ᶠ y in 𝓝 (φ x), (g y).IsSymm) (hu : IsUnit (g (φ x)).det)
    (hJ : IsUnit (jacobianMatrix (fderiv ℝ φ x)).det) (a b c : Covector) :
    let J := fderiv ℝ φ
    let H := fderiv ℝ J
    let C := connectionBilin g (φ x)
    let gp := pullMetric g φ J
    J x (fderiv ℝ (fun y => connection gp y b c) x a) =
      fderiv ℝ H x a b c + fderiv ℝ (connectionBilin g) (φ x) (J x a) (J x b) (J x c) +
      C (H x a b) (J x c) + C (J x b) (H x a c) - H x a (connection gp x b c) := by
  let J := fderiv ℝ φ
  let H := fderiv ℝ J
  let gp := pullMetric g φ J
  let P := connectionBilin gp
  let C := connectionBilin g
  have hJ₂ : ContDiffAt ℝ 2 J x := hφ.fderiv_right (by decide)
  have hH₁ : ContDiffAt ℝ 1 H x := hJ₂.fderiv_right (by decide)
  have hU : IsUnit (gp x) := by
    apply (gp x).isUnit_iff_isUnit_det.mpr
    rw [show gp x = pullMatrix (jacobianMatrix (J x)) (g (φ x)) by rfl, det_pullMatrix]
    exact (hJ.pow 2).mul hu
  have hP := (contDiffAt_connectionBilin (contDiffAt_pullMetric hφ hg) hU).differentiableAt_one
  have hC := (contDiffAt_connectionBilin hg ((g (φ x)).isUnit_iff_isUnit_det.mpr hu)).differentiableAt_one
  let evalBC := (apply ℝ Covector c).comp (apply ℝ (Covector →L[ℝ] Covector) b)
  have hPc : DifferentiableAt ℝ (fun y => P y b c) x :=
    ((contDiffAt_connectionBilin (contDiffAt_pullMetric hφ hg) hU).clm_apply
      (contDiffAt_const (c := b))).clm_apply (contDiffAt_const (c := c)) |>.differentiableAt_one
  have hleft := hJ₂.differentiableAt (by decide) |>.hasFDerivAt.clm_apply hPc.hasFDerivAt
  have hThird := evalBC.hasFDerivAt.comp x hH₁.differentiableAt_one.hasFDerivAt
  let D (p : Covector) := (apply ℝ Covector p).comp (H x)
  have hD (p : Covector) : HasFDerivAt (fun y => J y p) (D p) x :=
    (apply ℝ Covector p).hasFDerivAt.comp x (hJ₂.differentiableAt (by decide)).hasFDerivAt
  let dC := (fderiv ℝ C (φ x)).comp (J x)
  have hA : HasFDerivAt (fun y => C (φ y)) dC x :=
    hC.hasFDerivAt.comp x (hφ.differentiableAt (by decide)).hasFDerivAt
  have hB : HasFDerivAt (fun y => C (φ y) (J y b)) ((C (φ x)).comp (D b) + dC.flip (J x b)) x :=
    hA.clm_apply (hD b)
  have hright := hThird.add (hB.clm_apply (hD c))
  have h := congrArg (fun L : Covector →L[ℝ] Covector => L a) (hleft.fderiv.symm.trans
    ((connection_pullback_germ hφ hg hs hu hJ b c).fderiv_eq.trans hright.fderiv))
  change J x (fderiv ℝ (fun y => connection gp y b c) x a) + H x a (connection gp x b c) =
    fderiv ℝ H x a b c + (C (φ x) (J x b) (H x a c) +
      (C (φ x) (H x a b) (J x c) + fderiv ℝ C (φ x) (J x a) (J x b) (J x c))) at h
  dsimp only
  rw [eq_sub_iff_add_eq, h]
  abel

/-- The actual Riemann curvature transforms tensorially under a regular nonlinear chart change.
The transition's second and third derivatives cancel without any curvature covariance assumption. -/
theorem curvature_pullback (hφ : ContDiffAt ℝ 3 φ x) (hg : ContDiffAt ℝ 2 g (φ x))
    (hs : ∀ᶠ y in 𝓝 (φ x), (g y).IsSymm) (hu : IsUnit (g (φ x)).det)
    (hJ : IsUnit (jacobianMatrix (fderiv ℝ φ x)).det) (u v w : Covector) :
    fderiv ℝ φ x (curvature (pullMetric g φ (fderiv ℝ φ)) x u v w) =
      curvature g (φ x) (fderiv ℝ φ x u) (fderiv ℝ φ x v) (fderiv ℝ φ x w) := by
  let J := fderiv ℝ φ
  let H := fderiv ℝ J
  let gp := pullMetric g φ J
  let P := connectionBilin gp x
  let C := connectionBilin g (φ x)
  have h₂ : ContDiffAt ℝ 2 φ x := hφ.of_le (by decide)
  have hH : H x v w = H x w v := h₂.isSymmSndFDerivAt (by simp) v w
  have hH₃ : fderiv ℝ H x v w u = fderiv ℝ H x w v u := congrArg (fun L : Covector →L[ℝ] Covector => L u)
    ((hφ.fderiv_right (m := 2) (by decide)).isSymmSndFDerivAt (by simp) v w)
  have hΓ := connection_pullback h₂ (hg.differentiableAt (by decide)) hs.self_of_nhds hu hJ
  have hd := connection_pullback_derivative hφ hg hs hu hJ
  have hT := connection_derivative hg ((g (φ x)).isUnit_iff_isUnit_det.mpr hu)
  change J x (curvature gp x u v w) = _
  simp only [curvature, map_sub, map_add]
  rw [hd v w u, hd w v u, hΓ v (connection gp x w u), hΓ w (connection gp x v u),
    hΓ w u, hΓ v u]
  simp only [hT]
  simp only [← connectionBilin_apply, map_add]
  dsimp only [J, H] at hH hH₃
  dsimp only [J, H, gp]
  rw [hH, hH₃]
  abel

end FoliationQM.CurvedRiemannOverlap
