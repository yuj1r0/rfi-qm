module

public import FoliationQM.WeightedPolarEnergyL2
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The admissible polar pair of a smooth wave

Source: v13 `thm:wallstrom` Part(c), the converse "any smooth solution `ψ`
defines an admissible pair `ρ_inv = |ψ|²`, `α_clock = -(ħ/mc²) Im(dψ/ψ)`
satisfying `eq:positive_h_energy` on `Ω`", component kinds B and C. Away from
its zeros a differentiable complex field has differentiable modulus
`R = |ψ|` and unit phase `q = ψ/|ψ|`, the phase satisfies the clock
differential relation with `α = -ω⁻¹ Im(dψ/ψ)`, and `ψ = R q`. The positive
polar energy of the pair equals `|ψ|² + |dψ|²_H` pointwise off the zeros. For
a continuously differentiable field and a continuous positive-definite
auxiliary metric on a compact set, that energy is integrable for the
auxiliary volume on the compact set off the zero set.

No hypothesis on the zero set, equation or timelike character of the phase
gradient is used. Closedness of the clock form, circulation quantization and
the bijection modulo constant phase are separate.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.NodalPolarConverse

open MeasureTheory Set LorentzMatrixGroup RNCCoordinateConnection AuxiliaryMetricEnergy
open CirclePolarEnergy RealLorentzFrame
open scoped ContDiff Topology Matrix.Norms.Operator ComplexConjugate

section Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ψ : E → ℂ} {x : E}
  {D : E →L[ℝ] ℂ} {w : ℝ}

/-- The modulus of a complex field. -/
def amplitude (ψ : E → ℂ) (y : E) : ℝ := ‖ψ y‖

/-- The unit phase of a complex field; its value at a zero is irrelevant. -/
def unitPhase (ψ : E → ℂ) (y : E) : ℂ := (‖ψ y‖)⁻¹ • ψ y

/-- The differential of the modulus at a nonzero value `z` with differential `D`. -/
def amplitudeDeriv (z : ℂ) (D : E →L[ℝ] ℂ) : E →L[ℝ] ℝ :=
  ‖z‖ • Complex.reCLM.comp (z⁻¹ • D)

/-- The clock form `-w⁻¹ Im(dψ/ψ)` at a nonzero value `z` with differential `D`. -/
def clockDeriv (w : ℝ) (z : ℂ) (D : E →L[ℝ] ℂ) : E →L[ℝ] ℝ :=
  (-w⁻¹) • Complex.imCLM.comp (z⁻¹ • D)

/-- The modulus differential applied to a direction. -/
theorem amplitudeDeriv_apply (z : ℂ) (D : E →L[ℝ] ℂ) (v : E) :
    amplitudeDeriv z D v = ‖z‖ * (z⁻¹ * D v).re := by
  simp [amplitudeDeriv]

/-- The clock form applied to a direction. -/
theorem clockDeriv_apply (w : ℝ) (z : ℂ) (D : E →L[ℝ] ℂ) (v : E) :
    clockDeriv w z D v = -w⁻¹ * (z⁻¹ * D v).im := by
  simp [clockDeriv]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The field is the product of its modulus and unit phase everywhere. -/
theorem field_eq (ψ : E → ℂ) : field (amplitude ψ) (unitPhase ψ) = ψ := by
  funext y
  by_cases h : ψ y = 0
  · simp [field, amplitude, unitPhase, h]
  · have hn : ‖ψ y‖ ≠ 0 := norm_ne_zero_iff.mpr h
    simp only [field, amplitude, unitPhase, smul_smul, mul_inv_cancel₀ hn, one_smul]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The phase has unit modulus away from the zeros. -/
theorem norm_unitPhase (h : ψ x ≠ 0) : ‖unitPhase ψ x‖ = 1 := by
  have hn : ‖ψ x‖ ≠ 0 := norm_ne_zero_iff.mpr h
  simp only [unitPhase, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]

private theorem inv_mul_eq (z w : ℂ) :
    z⁻¹ * w = ((‖z‖ ^ 2)⁻¹ : ℝ) • (conj z * w) := by
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, Complex.real_smul]
  ring

/-- The modulus is differentiable away from the zeros, with differential
`|ψ| Re(dψ/ψ)`. -/
theorem hasFDerivAt_amplitude (hD : HasFDerivAt ψ D x) (h : ψ x ≠ 0) :
    HasFDerivAt (amplitude ψ) (amplitudeDeriv (ψ x) D) x := by
  have hn : ‖ψ x‖ ≠ 0 := norm_ne_zero_iff.mpr h
  have h2 : HasFDerivAt (fun y => ‖ψ y‖ ^ 2) (2 • (innerSL ℝ (ψ x)).comp D) x := hD.norm_sq
  have h3 := h2.sqrt (pow_ne_zero 2 hn)
  have hfun : (fun y => √(‖ψ y‖ ^ 2)) = amplitude ψ :=
    funext fun y => Real.sqrt_sq (norm_nonneg _)
  rw [hfun, Real.sqrt_sq (norm_nonneg _)] at h3
  have hE : amplitudeDeriv (ψ x) D =
      (1 / (2 * ‖ψ x‖)) • (2 • (innerSL ℝ (ψ x)).comp D) := by
    ext v
    rw [amplitudeDeriv_apply, inv_mul_eq]
    simp only [Complex.smul_re, smul_eq_mul, smul_apply,
      ContinuousLinearMap.comp_apply, innerSL_apply_apply, Complex.inner, nsmul_eq_mul,
      Nat.cast_ofNat]
    field_simp
  rw [hE]
  exact h3

/-- The unit phase satisfies the clock differential relation away from the zeros. -/
theorem hasFDerivAt_unitPhase (hw : w ≠ 0) (hD : HasFDerivAt ψ D x) (h : ψ x ≠ 0) :
    HasFDerivAt (unitPhase ψ)
      ((clockDeriv w (ψ x) D).smulRight (-Complex.I * (w : ℂ) * unitPhase ψ x)) x := by
  have hn : ‖ψ x‖ ≠ 0 := norm_ne_zero_iff.mpr h
  have hA := hasFDerivAt_amplitude hD h
  have hinv : HasFDerivAt (fun y => (amplitude ψ y)⁻¹)
      (-(amplitude ψ x ^ 2)⁻¹ • amplitudeDeriv (ψ x) D) x :=
    (hasDerivAt_inv (show amplitude ψ x ≠ 0 from hn)).comp_hasFDerivAt x hA
  have hq := hinv.fun_smul hD
  have hE : (clockDeriv w (ψ x) D).smulRight (-Complex.I * (w : ℂ) * unitPhase ψ x) =
      (amplitude ψ x)⁻¹ • D +
        (-(amplitude ψ x ^ 2)⁻¹ • amplitudeDeriv (ψ x) D).smulRight (ψ x) := by
    ext v
    have hDv : D v = ψ x * ((ψ x)⁻¹ * D v) := by rw [mul_inv_cancel_left₀ h]
    simp only [ContinuousLinearMap.smulRight_apply, add_apply,
      smul_apply, clockDeriv_apply, amplitudeDeriv_apply, unitPhase,
      amplitude, Complex.real_smul, smul_eq_mul]
    generalize (ψ x)⁻¹ * D v = c at hDv ⊢
    rw [hDv]
    obtain ⟨a, b, rfl⟩ : ∃ a b : ℝ, c = a + b * Complex.I :=
      ⟨c.re, c.im, (Complex.re_add_im c).symm⟩
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      sub_zero, add_zero, zero_add]
    push_cast
    have hnc : (‖ψ x‖ : ℂ) ≠ 0 := by exact_mod_cast hn
    have hwc : (w : ℂ) ≠ 0 := by exact_mod_cast hw
    field_simp
    ring
  rw [hE]
  exact hq

end Pointwise

variable {ψ : Covector → ℂ} {K : Set Covector} {H : Covector → Mat4} {w : ℝ} {x : Covector}

/-- The positive polar energy density of the pair defined by a field. -/
def polarEnergy (w : ℝ) (H : Covector → Mat4) (ψ : Covector → ℂ) (x : Covector) : ℝ :=
  (amplitude ψ x) ^ 2 +
    realEnergy (H x) (fun i => amplitudeDeriv (ψ x) (fderiv ℝ ψ x) (axis i)) +
    w ^ 2 * (amplitude ψ x) ^ 2 *
      realEnergy (H x) (fun i => clockDeriv w (ψ x) (fderiv ℝ ψ x) (axis i))

/-- Off the zeros the polar energy is the field energy `|ψ|² + |dψ|²_H`. -/
theorem polarEnergy_eq (hw : w ≠ 0) (hd : DifferentiableAt ℝ ψ x) (h : ψ x ≠ 0) :
    polarEnergy w H ψ x =
      ‖ψ x‖ ^ 2 + complexEnergy (H x) (fun i => fderiv ℝ ψ x (axis i)) := by
  have hs := (energy_split (H x) (hasFDerivAt_amplitude hd.hasFDerivAt h)
    (hasFDerivAt_unitPhase hw hd.hasFDerivAt h) (norm_unitPhase h)).2
  rw [field_eq] at hs
  rw [polarEnergy, hs]
  simp only [amplitude]
  ring

/-- For a continuously differentiable field and a continuous positive-definite
auxiliary metric on a compact set, the polar energy is integrable for the
auxiliary volume on the compact set off the zero set of the field. -/
theorem integrable_polarEnergy (hw : w ≠ 0) (hψ : ContDiff ℝ 1 ψ) (hK : IsCompact K)
    (hH : ContinuousOn H K) (hpos : ∀ x ∈ K, (H x).PosDef) :
    Integrable (polarEnergy w H ψ)
      ((volume.restrict (K \ {x | ψ x = 0})).withDensity
        (fun x => ENNReal.ofReal (density (H x)))) := by
  have hS : MeasurableSet (K \ {x | ψ x = 0}) :=
    hK.measurableSet.diff (isClosed_eq hψ.continuous continuous_const).measurableSet
  have hinv : ContinuousOn (fun x => (H x)⁻¹) K := by
    have hfun : (fun x => (H x)⁻¹) = fun x => ((H x).det)⁻¹ • (H x).adjugate := by
      funext x
      rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rw [hfun]
    exact ((continuous_id.matrix_det.comp_continuousOn hH).inv₀
      fun x hx => (hpos x hx).det_pos.ne').smul
      (continuous_id.matrix_adjugate.comp_continuousOn hH)
  have hdψ (i : Fin 4) : Continuous fun x => fderiv ℝ ψ x (axis i) :=
    (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  let G : Covector → ℝ := fun x =>
    ‖ψ x‖ ^ 2 + complexEnergy (H x) (fun i => fderiv ℝ ψ x (axis i))
  have hG : ContinuousOn G K := by
    refine (hψ.continuous.norm.pow 2).continuousOn.add ?_
    simp only [complexEnergy_eq_sum]
    refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
    exact ((continuous_id.matrix_elem i j).comp_continuousOn hinv).mul
      (Complex.continuous_re.comp ((hdψ i).star.mul (hdψ j))).continuousOn
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hG
  have heq : ∀ x ∈ K \ {x | ψ x = 0}, polarEnergy w H ψ x = G x := fun x hx =>
    polarEnergy_eq hw (hψ.differentiable one_ne_zero x) hx.2
  have hdens : ContinuousOn (fun x => density (H x)) K :=
    (continuous_id.matrix_det.comp_continuousOn hH).sqrt
  have hfin : IsFiniteMeasure ((volume.restrict (K \ {x | ψ x = 0})).withDensity
      (fun x => ENNReal.ofReal (density (H x)))) :=
    isFiniteMeasure_withDensity_ofReal
      ((hdens.integrableOn_compact hK).mono_set sdiff_subset).hasFiniteIntegral
  have hac := withDensity_absolutelyContinuous (volume.restrict (K \ {x | ψ x = 0}))
    (fun x => ENNReal.ofReal (density (H x)))
  have hae : polarEnergy w H ψ =ᵐ[volume.restrict (K \ {x | ψ x = 0})] G :=
    (ae_restrict_mem hS).mono heq
  have hmeas : AEStronglyMeasurable (polarEnergy w H ψ)
      (volume.restrict (K \ {x | ψ x = 0})) :=
    ((hG.aestronglyMeasurable hK.measurableSet).mono_measure
      (Measure.restrict_mono_set volume sdiff_subset)).congr hae.symm
  refine Integrable.of_bound (hmeas.mono_ac hac) C (hac.ae_le ?_)
  filter_upwards [ae_restrict_mem hS] with x hx
  rw [heq x hx]
  exact hC x hx.1

/-- A continuously differentiable field with zero set `N` defines an admissible
polar pair on every compact set off `N`: positive differentiable amplitude,
unit phase with the clock differential relation, the field as their product,
and integrable positive auxiliary-metric polar energy. -/
theorem admissible_pair (hw : w ≠ 0) (hψ : ContDiff ℝ 1 ψ) (hK : IsCompact K)
    (hH : ContinuousOn H K) (hpos : ∀ x ∈ K, (H x).PosDef) {N : Set Covector}
    (hzero : ∀ x, ψ x = 0 ↔ x ∈ N) :
    (∀ x ∈ K \ N, 0 < amplitude ψ x ∧
      HasFDerivAt (amplitude ψ) (amplitudeDeriv (ψ x) (fderiv ℝ ψ x)) x ∧
      HasFDerivAt (unitPhase ψ) ((clockDeriv w (ψ x) (fderiv ℝ ψ x)).smulRight
        (-Complex.I * (w : ℂ) * unitPhase ψ x)) x ∧
      ‖unitPhase ψ x‖ = 1) ∧
    field (amplitude ψ) (unitPhase ψ) = ψ ∧
    Integrable (polarEnergy w H ψ)
      ((volume.restrict (K \ N)).withDensity (fun x => ENNReal.ofReal (density (H x)))) := by
  have hN : N = {x | ψ x = 0} := by
    ext x
    exact (hzero x).symm
  refine ⟨fun x hx => ?_, field_eq ψ, hN ▸ integrable_polarEnergy hw hψ hK hH hpos⟩
  have hne : ψ x ≠ 0 := fun h => hx.2 ((hzero x).mp h)
  have hd := (hψ.differentiable one_ne_zero x).hasFDerivAt
  exact ⟨norm_pos_iff.mpr hne, hasFDerivAt_amplitude hd hne, hasFDerivAt_unitPhase hw hd hne,
    norm_unitPhase hne⟩

end FoliationQM.NodalPolarConverse
