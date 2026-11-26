module

public import FoliationQM.PolarDifferential
public import FoliationQM.PolarSecondJet

/-!
# Actual second derivatives of local polar fields

Source: v13 `thm:kahler` and `eq:nonlinear_defect`. Derivatives are real
Fréchet derivatives. First differentiability is required on a neighborhood,
so the first derivative formula can itself be differentiated. The four
directions in the contraction are constant; coordinate directions represent
the flat metric with signature (+---) and coordinate x⁰ = ct.
-/
@[expose] public section

namespace FoliationQM.PolarSecondDifferential

open scoped Topology
open MasterMetricAndCone

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Actual directional derivative along a constant vector. -/
noncomputable def directionalDerivative (f : E → F) (v : E) (x : E) : F :=
  fderiv ℝ f x v

/-- Actual second derivative along a constant vector. -/
noncomputable def secondDirectionalDerivative (f : E → F) (v : E) (x : E) : F :=
  directionalDerivative (directionalDerivative f v) v x

/-- The explicit flat (+---) contraction of four actual second derivatives. -/
noncomputable def box (f : E → F) (e : Fin 4 → E) (x : E) : F :=
  secondDirectionalDerivative f (e 0) x - secondDirectionalDerivative f (e 1) x -
    secondDirectionalDerivative f (e 2) x - secondDirectionalDerivative f (e 3) x

/-- Polar wave field with a real amplitude and local real phase. -/
noncomputable def amplitudeField (R Φ : E → ℝ) (x : E) : ℂ :=
  (R x : ℂ) * phase (Φ x)

/-- First derivative of the amplitude-phase field, with actual source derivatives. -/
theorem directionalDerivative_amplitudeField {R Φ : E → ℝ} {x : E}
    (hR : DifferentiableAt ℝ R x) (hΦ : DifferentiableAt ℝ Φ x) (v : E) :
    directionalDerivative (amplitudeField R Φ) v x =
      amplitudeTangent (R x) (Φ x)
        (directionalDerivative R v x) (directionalDerivative Φ v x) := by
  have hRc := Complex.ofRealCLM.hasFDerivAt.comp x hR.hasFDerivAt
  have hΦc := Complex.ofRealCLM.hasFDerivAt.comp x hΦ.hasFDerivAt
  have he := (hΦc.mul_const Complex.I).cexp
  have hd : HasFDerivAt (amplitudeField R Φ) _ x := hRc.mul he
  unfold directionalDerivative
  rw [hd.fderiv]
  simp only [amplitudeTangent, phase, add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, Function.comp_apply, smul_eq_mul]
  ring

/-- Second derivative realization of the polar second jet. The neighborhood
assumptions justify differentiating the first derivative formula. -/
theorem secondDirectionalDerivative_amplitudeField {R Φ : E → ℝ} {x : E} (v : E)
    (hR : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ R y)
    (hΦ : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ Φ y)
    (hR2 : DifferentiableAt ℝ (directionalDerivative R v) x)
    (hΦ2 : DifferentiableAt ℝ (directionalDerivative Φ v) x) :
    secondDirectionalDerivative (amplitudeField R Φ) v x =
      PolarSecondJet.polarSecondTangent (R x) (Φ x)
        (directionalDerivative R v x) (directionalDerivative Φ v x)
        (secondDirectionalDerivative R v x) (secondDirectionalDerivative Φ v x) := by
  have heq : directionalDerivative (amplitudeField R Φ) v =ᶠ[𝓝 x]
      (fun y => phase (Φ y) * (((directionalDerivative R v y : ℝ) : ℂ) +
        Complex.I * (R y : ℂ) * ((directionalDerivative Φ v y : ℝ) : ℂ))) := by
    filter_upwards [hR, hΦ] with y hyR hyΦ
    exact directionalDerivative_amplitudeField hyR hyΦ v
  have hRc := Complex.ofRealCLM.hasFDerivAt.comp x hR.self_of_nhds.hasFDerivAt
  have hΦc := Complex.ofRealCLM.hasFDerivAt.comp x hΦ.self_of_nhds.hasFDerivAt
  have hdRc := Complex.ofRealCLM.hasFDerivAt.comp x hR2.hasFDerivAt
  have hdΦc := Complex.ofRealCLM.hasFDerivAt.comp x hΦ2.hasFDerivAt
  have he := (hΦc.mul_const Complex.I).cexp
  have hd : HasFDerivAt (fun y => phase (Φ y) *
      (((directionalDerivative R v y : ℝ) : ℂ) +
        Complex.I * (R y : ℂ) * ((directionalDerivative Φ v y : ℝ) : ℂ))) _ x :=
    he.mul (hdRc.add ((hRc.const_mul Complex.I).mul hdΦc))
  change (fderiv ℝ (directionalDerivative (amplitudeField R Φ) v) x) v = _
  rw [heq.fderiv_eq, hd.fderiv]
  simp only [PolarSecondJet.polarSecondTangent, phase, add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, Function.comp_apply, smul_eq_mul,
    secondDirectionalDerivative, directionalDerivative]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- Constant action-phase scaling for an actual first derivative. -/
theorem directionalDerivative_div_const {S : E → ℝ} {x : E}
    (hS : DifferentiableAt ℝ S x) (k : ℝ) (v : E) :
    directionalDerivative (fun y => S y / k) v x = directionalDerivative S v x / k := by
  have hd : HasFDerivAt (fun y => S y / k) (k⁻¹ • fderiv ℝ S x) x := by
    simpa only [div_eq_mul_inv, mul_comm] using hS.hasFDerivAt.const_mul k⁻¹
  unfold directionalDerivative
  rw [hd.fderiv]
  simp only [smul_apply, smul_eq_mul, div_eq_mul_inv]
  ring

/-- The first directional derivative of a scaled field is differentiable,
with the corresponding scaled genuine second differential. -/
theorem hasFDerivAt_directionalDerivative_div_const {S : E → ℝ} {x : E}
    (hS : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ S y) (k : ℝ) (v : E)
    (hS2 : DifferentiableAt ℝ (directionalDerivative S v) x) :
    HasFDerivAt (directionalDerivative (fun y => S y / k) v)
      (k⁻¹ • fderiv ℝ (directionalDerivative S v) x) x := by
  have heq : directionalDerivative (fun y => S y / k) v =ᶠ[𝓝 x]
      (fun y => k⁻¹ * directionalDerivative S v y) := by
    filter_upwards [hS] with y hy
    rw [directionalDerivative_div_const hy, div_eq_mul_inv, mul_comm]
  exact (hS2.hasFDerivAt.const_mul k⁻¹).congr_of_eventuallyEq heq

/-- Constant action-phase scaling for actual second directional derivatives. -/
theorem secondDirectionalDerivative_div_const {S : E → ℝ} {x : E}
    (hS : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ S y) (k : ℝ) (v : E)
    (hS2 : DifferentiableAt ℝ (directionalDerivative S v) x) :
    secondDirectionalDerivative (fun y => S y / k) v x =
      secondDirectionalDerivative S v x / k := by
  change (fderiv ℝ (directionalDerivative (fun y => S y / k) v) x) v = _
  rw [(hasFDerivAt_directionalDerivative_div_const hS k v hS2).fderiv]
  simp only [smul_apply, smul_eq_mul, secondDirectionalDerivative,
    directionalDerivative, div_eq_mul_inv]
  ring

/-- The actual flat wave operator on the action-phase field realizes its
second jet. In coordinate directions this is the local spacetime identity. -/
theorem box_actionField (p : MassiveParameters) {R S : E → ℝ} {x : E}
    (e : Fin 4 → E)
    (hR : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ R y)
    (hS : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ S y)
    (hR2 : ∀ μ, DifferentiableAt ℝ (directionalDerivative R (e μ)) x)
    (hS2 : ∀ μ, DifferentiableAt ℝ (directionalDerivative S (e μ)) x) :
    box (amplitudeField R (fun y => S y / p.hbar)) e x =
      PolarSecondJet.boxJet p (R x) (S x)
        (fun μ => directionalDerivative R (e μ) x)
        (fun μ => directionalDerivative S (e μ) x) (box R e x) (box S e x) := by
  have hΦ : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ (fun z => S z / p.hbar) y := by
    filter_upwards [hS] with y hy
    simpa only [div_eq_mul_inv, mul_comm] using hy.const_mul p.hbar⁻¹
  have hΦ2 (μ : Fin 4) :=
    (hasFDerivAt_directionalDerivative_div_const hS p.hbar (e μ) (hS2 μ)).differentiableAt
  have hd (μ : Fin 4) := secondDirectionalDerivative_amplitudeField
    (e μ) hR hΦ (hR2 μ) (hΦ2 μ)
  have hs (μ : Fin 4) := secondDirectionalDerivative_div_const hS p.hbar (e μ) (hS2 μ)
  simp only [directionalDerivative_div_const hS.self_of_nhds, hs] at hd
  unfold box
  rw [hd 0, hd 1, hd 2, hd 3]
  exact PolarSecondJet.polarSecondTangent_minkowski p (R x) (S x)
    (fun μ => directionalDerivative R (e μ) x)
    (fun μ => directionalDerivative S (e μ) x)
    (fun μ => secondDirectionalDerivative R (e μ) x)
    (fun μ => secondDirectionalDerivative S (e μ) x)

end FoliationQM.PolarSecondDifferential
