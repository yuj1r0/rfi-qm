module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The actual spatial differential of a smooth flow

The spatial differential is the restriction of the joint derivative to
label directions. A genuine time ODE on a label neighborhood can therefore
be differentiated in labels. Symmetry of the actual second derivative
gives its time evolution, with velocity differential acting after the
spatial flow differential. Local inverse and initial identities are also
differentiated as neighborhood identities.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.SpatialFlowDifferential

open scoped Topology
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual joint derivative restricted to spatial label directions. -/
def spatialDifferential (Phi : ℝ × E → E) (p : ℝ × E) : E →L[ℝ] E :=
  (fderiv ℝ Phi p).comp (ContinuousLinearMap.inr ℝ ℝ E)

variable {Phi : ℝ × E → E} {b : ℝ → E → E} {t : ℝ} {a : E} {p : ℝ × E}

/-- The restricted joint derivative is a derivative of the actual spatial slice. -/
theorem hasFDerivAt_spatial_slice (hPhi : DifferentiableAt ℝ Phi (t, a)) :
    HasFDerivAt (fun z => Phi (t, z)) (spatialDifferential Phi (t, a)) a := by
  exact hPhi.hasFDerivAt.comp a (hasFDerivAt_prodMk_right t a)

/-- The spatial differential agrees with the actual derivative of the label slice. -/
theorem spatialDifferential_eq_fderiv (hPhi : DifferentiableAt ℝ Phi (t, a)) :
    spatialDifferential Phi (t, a) = fderiv ℝ (fun z => Phi (t, z)) a :=
  (hasFDerivAt_spatial_slice hPhi).fderiv.symm

/-- A twice continuously differentiable flow has a continuously differentiable spatial differential. -/
theorem contDiffAt_spatialDifferential (hPhi : ContDiffAt ℝ 2 Phi p) :
    ContDiffAt ℝ 1 (spatialDifferential Phi) p := by
  let preS : ((ℝ × E) →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
    (ContinuousLinearMap.compL ℝ E (ℝ × E) E).flip
      (ContinuousLinearMap.inr ℝ ℝ E)
  exact preS.contDiff.contDiffAt.comp p (hPhi.fderiv_right (m := 1) (by norm_num))

/-- The actual ODE on a label neighborhood determines the time derivative of the spatial differential. -/
theorem hasDerivAt_spatialDifferential
    (hPhi : ContDiffAt ℝ 2 Phi (t, a))
    (hb : DifferentiableAt ℝ (b t) (Phi (t, a)))
    (hODE : ∀ᶠ z in 𝓝 a,
      HasDerivAt (fun τ => Phi (τ, z)) (b t (Phi (t, z))) t) :
    HasDerivAt (fun τ => spatialDifferential Phi (τ, a))
      ((fderiv ℝ (b t) (Phi (t, a))).comp (spatialDifferential Phi (t, a))) t := by
  let D := fderiv ℝ Phi
  let H := fderiv ℝ D (t, a)
  let inS := ContinuousLinearMap.inr ℝ ℝ E
  let evT := ContinuousLinearMap.apply ℝ E ((1 : ℝ), (0 : E))
  let preS : ((ℝ × E) →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
    (ContinuousLinearMap.compL ℝ E (ℝ × E) E).flip inS
  have hD : DifferentiableAt ℝ D (t, a) :=
    (hPhi.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have hnear : ∀ᶠ z in 𝓝 a, ContDiffAt ℝ 2 Phi (t, z) :=
    (continuousAt_const.prodMk continuousAt_id).eventually (hPhi.eventually (by simp))
  have htime : (fun z => D (t, z) (1, 0)) =ᶠ[𝓝 a]
      (fun z => b t (Phi (t, z))) := by
    filter_upwards [hnear, hODE] with z hz hzt
    have hd := ((hz.differentiableAt (by norm_num)).hasFDerivAt.comp t
      (hasFDerivAt_prodMk_left t z)).hasDerivAt
    exact hd.unique hzt
  have hleft : HasFDerivAt (fun z => D (t, z) (1, 0))
      (evT.comp (H.comp inS)) a :=
    evT.hasFDerivAt.comp a (hD.hasFDerivAt.comp a (hasFDerivAt_prodMk_right t a))
  have hright := hb.hasFDerivAt.comp a
    (hasFDerivAt_spatial_slice (hPhi.differentiableAt (by norm_num)))
  have hmixed : evT.comp (H.comp inS) =
      (fderiv ℝ (b t) (Phi (t, a))).comp (spatialDifferential Phi (t, a)) := by
    rw [← hleft.fderiv, ← hright.fderiv]
    exact htime.fderiv_eq
  have ht := ((preS.hasFDerivAt.comp (t, a) hD.hasFDerivAt).comp t
    (hasFDerivAt_prodMk_left t a)).hasDerivAt
  have hv : preS (H (1, 0)) =
      (fderiv ℝ (b t) (Phi (t, a))).comp (spatialDifferential Phi (t, a)) := by
    rw [← hmixed]
    ext v
    exact hPhi.isSymmSndFDerivAt (by simp) (1, 0) (0, v)
  have ht' : HasDerivAt (fun τ => spatialDifferential Phi (τ, a))
      (preS (H (1, 0))) t := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply] using! ht
  rw [hv] at ht'
  exact ht'

/-- A genuine differentiable local left inverse gives a left inverse of the actual spatial differential. -/
theorem derivative_left_inverse {psi : E → E}
    (hPhi : DifferentiableAt ℝ Phi (t, a))
    (hpsi : DifferentiableAt ℝ psi (Phi (t, a)))
    (hleft : (fun z => psi (Phi (t, z))) =ᶠ[𝓝 a] id) :
    (fderiv ℝ psi (Phi (t, a))).comp (spatialDifferential Phi (t, a)) =
      ContinuousLinearMap.id ℝ E := by
  have hc := hpsi.hasFDerivAt.comp a (hasFDerivAt_spatial_slice hPhi)
  exact hc.unique ((hasFDerivAt_id a).congr_of_eventuallyEq hleft)

/-- A genuine zero-time label identity gives the identity spatial differential. -/
theorem spatialDifferential_zero (hPhi : DifferentiableAt ℝ Phi (0, a))
    (hzero : (fun z => Phi (0, z)) =ᶠ[𝓝 a] id) :
    spatialDifferential Phi (0, a) = ContinuousLinearMap.id ℝ E := by
  exact (hasFDerivAt_spatial_slice hPhi).unique
    ((hasFDerivAt_id a).congr_of_eventuallyEq hzero)

end FoliationQM.SpatialFlowDifferential
