module

public import FoliationQM.ActionVariation
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Differentiating the quadratic density along smooth field curves

Sources: v13 `thm:kahler` and `eq:KG_action`. The curve parameter is real.
All spatial and parameter derivatives are actual real Fréchet derivatives.
The mixed-derivative step follows from the symmetry of the second derivative;
it is not an assumption on an independent jet.
-/
@[expose] public section

namespace FoliationQM.SmoothActionDensity

open ActionVariation PolarSecondDifferential
open scoped Topology ComplexConjugate ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A spatial field obtained by fixing the real curve parameter. -/
def slice (Ψ : ℝ × E → ℂ) (t : ℝ) (x : E) : ℂ := Ψ (t, x)

/-- The actual parameter velocity, defined by the total differential. -/
noncomputable def velocity (Ψ : ℝ × E → ℂ) (t : ℝ) (x : E) : ℂ :=
  fderiv ℝ Ψ (t, x) (1, 0)

/-- The genuine spatial derivative of a slice is the corresponding total derivative. -/
theorem directionalDerivative_slice {Ψ : ℝ × E → ℂ} {t : ℝ} {x : E}
    (hΨ : DifferentiableAt ℝ Ψ (t, x)) (v : E) :
    directionalDerivative (slice Ψ t) v x = fderiv ℝ Ψ (t, x) (0, v) := by
  have hd := hΨ.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)
  change fderiv ℝ (Ψ ∘ fun y => (t, y)) x v = _
  rw [hd.fderiv]
  rfl

/-- The parameter derivative of a slice is the actual velocity. -/
theorem hasDerivAt_slice_time {Ψ : ℝ × E → ℂ} {t : ℝ} {x : E}
    (hΨ : DifferentiableAt ℝ Ψ (t, x)) :
    HasDerivAt (fun r => slice Ψ r x) (velocity Ψ t x) t := by
  exact (hΨ.hasFDerivAt.comp t (hasFDerivAt_prodMk_left t x)).hasDerivAt

/-- Local joint smoothness implies local spatial smoothness. -/
theorem contDiffAt_slice {Ψ : ℝ × E → ℂ} {t : ℝ} {x : E}
    (hΨ : ContDiffAt ℝ ∞ Ψ (t, x)) : ContDiffAt ℝ ∞ (slice Ψ t) x :=
  hΨ.comp x (contDiffAt_const.prodMk contDiffAt_id)

/-- Applying a smooth total differential to a constant vector remains smooth. -/
theorem contDiffAt_jointDirectional {Ψ : ℝ × E → ℂ} {z : ℝ × E}
    (hΨ : ContDiffAt ℝ ∞ Ψ z) (v : ℝ × E) :
    ContDiffAt ℝ ∞ (fun w => fderiv ℝ Ψ w v) z :=
  (hΨ.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const

/-- The velocity is jointly smooth near a point of joint smoothness. -/
theorem contDiffAt_jointVelocity {Ψ : ℝ × E → ℂ} {z : ℝ × E}
    (hΨ : ContDiffAt ℝ ∞ Ψ z) :
    ContDiffAt ℝ ∞ (fun w => velocity Ψ w.1 w.2) z :=
  contDiffAt_jointDirectional hΨ (1, 0)

/-- The actual velocity is locally smooth as a spatial field. -/
theorem contDiffAt_velocity {Ψ : ℝ × E → ℂ} {t : ℝ} {x : E}
    (hΨ : ContDiffAt ℝ ∞ Ψ (t, x)) : ContDiffAt ℝ ∞ (velocity Ψ t) x :=
  (contDiffAt_jointVelocity hΨ).comp x (contDiffAt_const.prodMk contDiffAt_id)

/-- Evaluating the differentiated total differential at a constant vector. -/
theorem fderiv_jointDirectional {Ψ : ℝ × E → ℂ} {z : ℝ × E}
    (hΨ : ContDiffAt ℝ ∞ Ψ z) (v w : ℝ × E) :
    fderiv ℝ (fun y => fderiv ℝ Ψ y v) z w =
      fderiv ℝ (fderiv ℝ Ψ) z w v := by
  have hd := ((hΨ.fderiv_right (m := ∞) (by simp)).differentiableAt
    (by simp)).hasFDerivAt.clm_apply (hasFDerivAt_const v z)
  rw [hd.fderiv]
  simp

/-- Schwarz symmetry identifies the parameter derivative of the spatial
field derivative with the spatial derivative of the actual velocity. -/
theorem hasDerivAt_directionalDerivative_slice {Ψ : ℝ × E → ℂ} {t : ℝ} {x : E}
    (hΨ : ContDiffAt ℝ ∞ Ψ (t, x)) (v : E) :
    HasDerivAt (fun r => directionalDerivative (slice Ψ r) v x)
      (directionalDerivative (velocity Ψ t) v x) t := by
  have hevent : ∀ᶠ y in 𝓝 (t, x), DifferentiableAt ℝ Ψ y :=
    ((hΨ.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)).mono
      (fun _ h => h.differentiableAt (by norm_num))
  have heq : (fun r => directionalDerivative (slice Ψ r) v x) =ᶠ[𝓝 t]
      (fun r => fderiv ℝ Ψ (r, x) (0, v)) := by
    filter_upwards [((continuousAt_id.prodMk continuousAt_const).tendsto.eventually hevent)]
      with r hr
    exact directionalDerivative_slice hr v
  have hraw := (((contDiffAt_jointDirectional hΨ (0, v)).differentiableAt
    (by simp)).hasFDerivAt.comp t (hasFDerivAt_prodMk_left t x)).hasDerivAt
  have hvelocity : directionalDerivative (velocity Ψ t) v x =
      fderiv ℝ (fderiv ℝ Ψ) (t, x) (0, v) (1, 0) := by
    change directionalDerivative (slice (fun w => velocity Ψ w.1 w.2) t) v x = _
    rw [directionalDerivative_slice ((contDiffAt_jointVelocity hΨ).differentiableAt (by simp))]
    exact fderiv_jointDirectional hΨ (1, 0) (0, v)
  refine (hraw.congr_deriv ?_).congr_of_eventuallyEq heq
  change fderiv ℝ (fun w => fderiv ℝ Ψ w (0, v)) (t, x) (1, 0) = _
  rw [fderiv_jointDirectional hΨ, hvelocity]
  exact hΨ.isSymmSndFDerivAt (by simp) _ _

/-- Differentiation of the diagonal Hermitian quadratic form along arbitrary
actual differentiable curves of its field value and four spatial derivatives. -/
theorem hasDerivAt_pairing_self (p : MassiveParameters) {u : ℝ → ℂ}
    {du : Fin 4 → ℝ → ℂ} {v : ℂ} {dv : Fin 4 → ℂ} {t : ℝ}
    (hu : HasDerivAt u v t) (hdu : ∀ i, HasDerivAt (du i) (dv i) t) :
    HasDerivAt (fun r => (pairing p (u r) (u r)
      (fun i => du i r) (fun i => du i r)).re)
      (2 * (pairing p v (u t) dv (fun i => du i t)).re) t := by
  have hc {f : ℝ → ℂ} {f' : ℂ} (hf : HasDerivAt f f' t) :
      HasDerivAt (fun r => conj (f r) * f r)
        (conj f' * f t + conj (f t) * f') t := by
    exact (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hf).mul hf
  have hd := ((((hc (hdu 0)).sub (hc (hdu 1))).sub (hc (hdu 2))).sub
    (hc (hdu 3))).const_mul ((p.hbar : ℂ) ^ 2) |>.sub
      ((hc hu).const_mul ((p.m : ℂ) ^ 2 * (p.c : ℂ) ^ 2))
  have hd' : HasDerivAt (fun r => pairing p (u r) (u r)
      (fun i => du i r) (fun i => du i r))
      (pairing p v (u t) dv (fun i => du i t) +
        pairing p (u t) v (fun i => du i t) dv) t := by
    convert hd using 1
    · funext r
      simp only [pairing, kineticPairing, Pi.sub_apply]
      ring
    · simp only [pairing, kineticPairing]
      ring
  have hsym := congrArg Complex.re (pairing_conj p v (u t) dv (fun i => du i t))
  simp only [Complex.conj_re] at hsym
  simpa only [Function.comp_def, Complex.reCLM_apply, Complex.add_re, ← hsym, two_mul]
    using Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hd' 

/-- The real quadratic density of a smooth family has the expected first
variation, with the actual spatial derivative of its actual parameter velocity. -/
theorem hasDerivAt_density (p : MassiveParameters) {Ψ : ℝ × E → ℂ}
    {t : ℝ} {x : E} (hΨ : ContDiffAt ℝ ∞ Ψ (t, x)) (e : Fin 4 → E) :
    HasDerivAt (fun r => (fieldPairing p (slice Ψ r) (slice Ψ r) e x).re)
      (2 * (fieldPairing p (velocity Ψ t) (slice Ψ t) e x).re) t :=
  hasDerivAt_pairing_self p (hasDerivAt_slice_time (hΨ.differentiableAt (by simp)))
    (fun i => hasDerivAt_directionalDerivative_slice hΨ (e i))

/-- Local joint smoothness of the spatial directional derivative, including
its dependence on the curve parameter. -/
theorem contDiffAt_spatialDirectional {Ψ : ℝ × E → ℂ} {z : ℝ × E}
    (hΨ : ContDiffAt ℝ ∞ Ψ z) (v : E) :
    ContDiffAt ℝ ∞ (fun w => directionalDerivative (slice Ψ w.1) v w.2) z := by
  have hevent : ∀ᶠ y in 𝓝 z, DifferentiableAt ℝ Ψ y :=
    ((hΨ.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)).mono
      (fun _ h => h.differentiableAt (by norm_num))
  apply (contDiffAt_jointDirectional hΨ (0, v)).congr_of_eventuallyEq
  filter_upwards [hevent] with y hy
  exact directionalDerivative_slice hy v

/-- Joint continuity of the genuine polarized density for two locally smooth
field curves. -/
theorem continuousAt_fieldPairing (p : MassiveParameters) {Ψ Χ : ℝ × E → ℂ}
    {z : ℝ × E} (hΨ : ContDiffAt ℝ ∞ Ψ z) (hΧ : ContDiffAt ℝ ∞ Χ z)
    (e : Fin 4 → E) :
    ContinuousAt (fun w => fieldPairing p (slice Ψ w.1) (slice Χ w.1) e w.2) z := by
  have h (i : Fin 4) := (contDiffAt_spatialDirectional hΨ (e i)).continuousAt.star.mul
    (contDiffAt_spatialDirectional hΧ (e i)).continuousAt
  exact ((((h 0).sub (h 1)).sub (h 2)).sub (h 3)).const_mul _ |>.sub
    ((hΨ.continuousAt.star.const_mul _).mul hΧ.continuousAt)

/-- Joint continuity of the quadratic real action density. -/
theorem continuousAt_density (p : MassiveParameters) {Ψ : ℝ × E → ℂ}
    {z : ℝ × E} (hΨ : ContDiffAt ℝ ∞ Ψ z) (e : Fin 4 → E) :
    ContinuousAt (fun w => (fieldPairing p (slice Ψ w.1) (slice Ψ w.1) e w.2).re) z :=
  Complex.continuous_re.continuousAt.comp (continuousAt_fieldPairing p hΨ hΨ e)

/-- Joint continuity of the proved parameter derivative of the density. -/
theorem continuousAt_densityDerivative (p : MassiveParameters) {Ψ : ℝ × E → ℂ}
    {z : ℝ × E} (hΨ : ContDiffAt ℝ ∞ Ψ z) (e : Fin 4 → E) :
    ContinuousAt (fun w => 2 *
      (fieldPairing p (velocity Ψ w.1) (slice Ψ w.1) e w.2).re) z :=
  (Complex.continuous_re.continuousAt.comp
    (continuousAt_fieldPairing p (contDiffAt_jointVelocity hΨ) hΨ e)).const_mul 2

end FoliationQM.SmoothActionDensity
