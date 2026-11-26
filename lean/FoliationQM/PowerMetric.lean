module

public import FoliationQM.PolarDifferential
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Fixed-phase power pullback and parameter uniqueness

Sources: v13 `lem:uniqueness`, `eq:lambda_metric`, `eq:unique_params`.
The map is the actual `Real.rpow` amplitude times the complex exponential of
the unchanged real phase. Its real Fréchet derivative determines the pullback
quadratic form. Equality with the source metric for every positive density and
every tangent increment selects the square root and Fisher coefficient.

The phase here is a real local lift. Keeping its coefficient equal to one
implements the fixed-clock formula; no circle-map degree, metric completion,
or smoothness at a nodal origin is asserted.
-/
@[expose] public section

namespace FoliationQM.PowerMetric

open MasterMetricAndCone PolarDifferential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The power-amplitude map with the physical phase left unchanged. -/
noncomputable def powerField (α : ℝ) (ρ Φ : E → ℝ) (x : E) : ℂ :=
  (Real.rpow (ρ x) α : ℂ) * phase (Φ x)

/-- Tangent obtained from the derivative of the real power amplitude. -/
noncomputable def powerTangent (α ρ Φ dρ dΦ : ℝ) : ℂ :=
  amplitudeTangent (Real.rpow ρ α) Φ (α * Real.rpow ρ (α - 1) * dρ) dΦ

/-- Continuous real-linear differential of the power-amplitude field. -/
noncomputable def powerDifferential (α ρ Φ : ℝ)
    (dρ dΦ : E →L[ℝ] ℝ) : E →L[ℝ] ℂ :=
  (Real.rpow ρ α : ℂ) • (phase Φ • (Complex.I • (Complex.ofRealCLM.comp dΦ))) +
    phase Φ • (Complex.ofRealCLM.comp ((α * Real.rpow ρ (α - 1)) • dρ))

/-- Evaluation of the genuine continuous linear map gives the explicit tangent. -/
theorem powerDifferential_apply (α ρ Φ : ℝ) (dρ dΦ : E →L[ℝ] ℝ) (v : E) :
    powerDifferential α ρ Φ dρ dΦ v = powerTangent α ρ Φ (dρ v) (dΦ v) := by
  simp only [powerDifferential, powerTangent, amplitudeTangent, add_apply,
    smul_apply, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
    smul_eq_mul, Complex.ofReal_mul]
  ring

/-- Chain and product rules prove the actual Fréchet derivative at positive density. -/
theorem hasFDerivAt_powerField (α : ℝ) {ρ Φ : E → ℝ}
    {dρ dΦ : E →L[ℝ] ℝ} {x : E}
    (hρ : HasFDerivAt ρ dρ x) (hΦ : HasFDerivAt Φ dΦ x) (hpos : 0 < ρ x) :
    HasFDerivAt (powerField α ρ Φ)
      (powerDifferential α (ρ x) (Φ x) dρ dΦ) x := by
  have hR := Complex.ofRealCLM.hasFDerivAt.comp x
    (hρ.rpow_const (p := α) (Or.inl (ne_of_gt hpos)))
  have hΦc := Complex.ofRealCLM.hasFDerivAt.comp x hΦ
  exact hR.mul ((hΦc.mul_const Complex.I).cexp)

/-- Actual Fréchet derivative evaluated on an arbitrary source tangent. -/
theorem fderiv_powerField_apply (α : ℝ) {ρ Φ : E → ℝ} {x : E}
    (hρ : DifferentiableAt ℝ ρ x) (hΦ : DifferentiableAt ℝ Φ x) (hpos : 0 < ρ x)
    (v : E) :
    fderiv ℝ (powerField α ρ Φ) x v =
      powerTangent α (ρ x) (Φ x) (fderiv ℝ ρ x v) (fderiv ℝ Φ x v) := by
  rw [(hasFDerivAt_powerField α hρ.hasFDerivAt hΦ.hasFDerivAt hpos).fderiv]
  exact powerDifferential_apply _ _ _ _ _ v

/-- The radial and angular coefficients of the power tangent's Euclidean metric. -/
theorem powerTangent_normSq (α ρ Φ dρ dΦ : ℝ) (hρ : 0 < ρ) :
    Complex.normSq (powerTangent α ρ Φ dρ dΦ) =
      α ^ 2 * Real.rpow ρ (2 * α - 2) * dρ ^ 2 +
        Real.rpow ρ (2 * α) * dΦ ^ 2 := by
  rw [powerTangent, amplitudeTangent_normSq]
  have hrad : (Real.rpow ρ (α - 1)) ^ 2 = Real.rpow ρ (2 * α - 2) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_mul_natCast hρ.le]
    congr 1
    ring
  have hang : (Real.rpow ρ α) ^ 2 = Real.rpow ρ (2 * α) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_mul_natCast hρ.le]
    congr 1
    ring
  simp only [mul_pow, hrad, hang]

/-- The coefficient identity is a pullback by actual differentiable source fields. -/
theorem fderiv_powerField_normSq (α : ℝ) {ρ Φ : E → ℝ} {x : E}
    (hρ : DifferentiableAt ℝ ρ x) (hΦ : DifferentiableAt ℝ Φ x) (hpos : 0 < ρ x)
    (v : E) :
    Complex.normSq (fderiv ℝ (powerField α ρ Φ) x v) =
      α ^ 2 * Real.rpow (ρ x) (2 * α - 2) * (fderiv ℝ ρ x v) ^ 2 +
        Real.rpow (ρ x) (2 * α) * (fderiv ℝ Φ x v) ^ 2 := by
  rw [fderiv_powerField_apply α hρ hΦ hpos]
  exact powerTangent_normSq _ _ _ _ _ hpos

/-- Equality for every positive density and every tangent selects both parameters.
The proof tests an angular increment at density two and a radial increment at
density one; equality for one chosen field would not suffice. Positivity of the
coupling is not needed for this implication or its converse. -/
theorem powerTangent_metric_iff (α hbar coupling : ℝ) (hh : 0 < hbar) :
    (∀ ρ : ℝ, 0 < ρ → ∀ Φ dρ dΦ : ℝ,
      Complex.normSq (powerTangent α ρ Φ dρ dΦ) =
        coupling / (hbar ^ 2 * ρ) * dρ ^ 2 + ρ * dΦ ^ 2) ↔
      α = 1 / 2 ∧ coupling = hbar ^ 2 / 4 := by
  constructor
  · intro h
    have hang := h 2 (by norm_num) 0 0 1
    rw [powerTangent_normSq _ _ _ _ _ (by norm_num)] at hang
    norm_num at hang
    have ha : 2 * α = 1 :=
      (Real.rpow_right_inj (by norm_num : (0 : ℝ) < 2)
        (by norm_num : (2 : ℝ) ≠ 1)).1 (by simpa using hang)
    have hrad := h 1 (by norm_num) 0 1 0
    rw [powerTangent_normSq _ _ _ _ _ (by norm_num)] at hrad
    norm_num at hrad
    have hmul := (eq_div_iff (pow_ne_zero 2 (ne_of_gt hh))).1 hrad
    have ha' : α = 1 / 2 := by linarith
    refine ⟨ha', ?_⟩
    rw [ha'] at hmul
    nlinarith [hmul]
  · rintro ⟨rfl, rfl⟩ ρ hρ Φ dρ dΦ
    rw [powerTangent_normSq _ _ _ _ _ hρ]
    norm_num [Real.rpow_neg_one]
    field_simp [ne_of_gt hh, ne_of_gt hρ]
    simp

/-- Actual derivative of the coordinate map `ρ^α exp(i Φ)` on the positive chart. -/
theorem fderiv_powerMap_normSq (α ρ Φ dρ dΦ : ℝ) (hρ : 0 < ρ) :
    Complex.normSq
      (fderiv ℝ (powerField α (Prod.fst : ℝ × ℝ → ℝ) Prod.snd) (ρ, Φ) (dρ, dΦ)) =
      α ^ 2 * Real.rpow ρ (2 * α - 2) * dρ ^ 2 +
        Real.rpow ρ (2 * α) * dΦ ^ 2 := by
  simpa only [hasFDerivAt_fst.fderiv, hasFDerivAt_snd.fderiv,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd'] using
    fderiv_powerField_normSq α (x := (ρ, Φ))
    differentiableAt_fst differentiableAt_snd hρ (dρ, dΦ)

/-- Fixed-clock parameter uniqueness stated directly for the actual coordinate
map's Fréchet derivative, with the source's positive-coupling assumptions. -/
theorem powerMap_metric_iff (α hbar coupling : ℝ) (hh : 0 < hbar)
    (_hcoupling : 0 < coupling) :
    (∀ ρ : ℝ, 0 < ρ → ∀ Φ dρ dΦ : ℝ,
      Complex.normSq
        (fderiv ℝ (powerField α (Prod.fst : ℝ × ℝ → ℝ) Prod.snd) (ρ, Φ) (dρ, dΦ)) =
          coupling / (hbar ^ 2 * ρ) * dρ ^ 2 + ρ * dΦ ^ 2) ↔
      α = 1 / 2 ∧ coupling = hbar ^ 2 / 4 := by
  have heq : ∀ ρ : ℝ, 0 < ρ → ∀ Φ dρ dΦ : ℝ,
      Complex.normSq
        (fderiv ℝ (powerField α (Prod.fst : ℝ × ℝ → ℝ) Prod.snd) (ρ, Φ) (dρ, dΦ)) =
      Complex.normSq (powerTangent α ρ Φ dρ dΦ) := by
    intro ρ hρ Φ dρ dΦ
    rw [fderiv_powerMap_normSq _ _ _ _ _ hρ, powerTangent_normSq _ _ _ _ _ hρ]
  constructor
  · intro h
    apply (powerTangent_metric_iff α hbar coupling hh).1
    intro ρ hρ Φ dρ dΦ
    rw [← heq ρ hρ Φ dρ dΦ]
    exact h ρ hρ Φ dρ dΦ
  · intro h ρ hρ Φ dρ dΦ
    rw [heq ρ hρ Φ dρ dΦ]
    exact (powerTangent_metric_iff α hbar coupling hh).2 h ρ hρ Φ dρ dΦ

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The selected power field is exactly the already formalized square-root field. -/
theorem powerField_half_eq_polarField (ρ Φ : E → ℝ) :
    powerField (1 / 2) ρ Φ = polarField ρ Φ := by
  funext x
  simp only [powerField, polarField, Real.sqrt_eq_rpow, Real.rpow_eq_pow]

end FoliationQM.PowerMetric
