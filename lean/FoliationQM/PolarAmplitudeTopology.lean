module
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Natural topology of the nonzero polar amplitude

Sources: v13 `prop:takabayasi` and `eq:takabayasi_polar`. A nonzero
complex amplitude has positive density equal to its squared norm and a
unit-circle phase. Their inverse is the positive square root of the density
times that phase. Both directions use the ordinary subtype and product
topologies inherited from the real and complex fields.

The exact homeomorphism and antipodal sign law are established directly.
No global real angle is selected, and no smooth manifold or abstract spin
group classification is asserted.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.PolarAmplitudeTopology

/-- Nonzero complex amplitudes with the natural complex-subspace topology. -/
abbrev NonzeroComplex := {t : ℂ // t ≠ 0}

/-- Positive real densities with the natural real-subspace topology. -/
abbrev PositiveDensity := {rho : ℝ // 0 < rho}

/-- The actual unit phase of a nonzero complex amplitude. -/
def phase (t : NonzeroComplex) : Circle :=
  ⟨(t : ℂ) / (‖(t : ℂ)‖ : ℂ), mem_sphere_zero_iff_norm.mpr (by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact div_self (norm_ne_zero_iff.mpr t.property))⟩

/-- The natural positive-density and unit-phase coordinates of an actual nonzero amplitude. -/
def coordinates (t : NonzeroComplex) : PositiveDensity × Circle :=
  (⟨‖(t : ℂ)‖^2, sq_pos_of_pos (norm_pos_iff.mpr t.property)⟩, phase t)

/-- The nonzero complex amplitude reconstructed from positive density and unit phase. -/
def amplitude (p : PositiveDensity × Circle) : NonzeroComplex :=
  ⟨(Real.sqrt (p.1 : ℝ) : ℂ) * (p.2 : ℂ),
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.2 p.1.property)))
      p.2.coe_ne_zero⟩

/-- The normalized phase is exactly the amplitude divided by its actual positive norm. -/
theorem phase_coe (t : NonzeroComplex) :
    (phase t : ℂ) = (t : ℂ) / (‖(t : ℂ)‖ : ℂ) := rfl

/-- The density coordinate is the actual squared complex norm. -/
theorem coordinates_density (t : NonzeroComplex) :
    ((coordinates t).1 : ℝ) = ‖(t : ℂ)‖^2 := rfl

/-- Reconstructed amplitudes have exactly the positive square-root norm. -/
theorem norm_amplitude (p : PositiveDensity × Circle) :
    ‖(amplitude p : ℂ)‖ = Real.sqrt (p.1 : ℝ) := by
  simp [amplitude, Complex.norm_real, Real.norm_eq_abs, Real.sqrt_nonneg]

/-- Reconstructed amplitudes have exactly the prescribed positive density. -/
theorem norm_amplitude_sq (p : PositiveDensity × Circle) :
    ‖(amplitude p : ℂ)‖^2 = (p.1 : ℝ) := by
  rw [norm_amplitude, Real.sq_sqrt p.1.property.le]

/-- Reconstructing an amplitude from its actual norm and phase recovers the amplitude. -/
theorem amplitude_coordinates (t : NonzeroComplex) : amplitude (coordinates t) = t := by
  apply Subtype.ext
  change (Real.sqrt (‖(t : ℂ)‖^2) : ℂ) * ((t : ℂ) / (‖(t : ℂ)‖ : ℂ)) = t
  rw [Real.sqrt_sq (norm_nonneg _), ← mul_div_assoc]
  exact mul_div_cancel_left₀ (t : ℂ) (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr t.property))

/-- Extracting density and phase from the actual reconstructed amplitude recovers both input coordinates. -/
theorem coordinates_amplitude (p : PositiveDensity × Circle) : coordinates (amplitude p) = p := by
  apply Prod.ext
  · apply Subtype.ext
    exact norm_amplitude_sq p
  · apply Circle.ext
    change (phase (amplitude p) : ℂ) = (p.2 : ℂ)
    rw [phase_coe, norm_amplitude]
    change ((Real.sqrt (p.1 : ℝ) : ℂ) * (p.2 : ℂ)) / (Real.sqrt (p.1 : ℝ) : ℂ) = p.2
    exact mul_div_cancel_left₀ (p.2 : ℂ)
      (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.2 p.1.property)))

/-- Unit-phase normalization is continuous on the natural nonzero-complex subspace. -/
theorem continuous_phase : Continuous phase := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val.div (Complex.continuous_ofReal.comp continuous_subtype_val.norm)
    (fun t => Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr t.property))

/-- The actual squared-norm and unit-phase coordinate map is continuous in the natural product topology. -/
theorem continuous_coordinates : Continuous coordinates := by
  exact ((continuous_subtype_val.norm.pow 2).subtype_mk _).prodMk continuous_phase

/-- Reconstruction from positive density and unit phase is continuous in their natural product topology. -/
theorem continuous_amplitude : Continuous amplitude := by
  apply Continuous.subtype_mk
  exact (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp
    (continuous_subtype_val.comp continuous_fst))).mul (continuous_subtype_val.comp continuous_snd)

/-- The actual polar amplitude is homeomorphic to positive density times the unit circle, with ordinary subtype and product topologies. -/
def amplitudeHomeomorph : NonzeroComplex ≃ₜ PositiveDensity × Circle where
  toFun := coordinates
  invFun := amplitude
  left_inv := amplitude_coordinates
  right_inv := coordinates_amplitude
  continuous_toFun := continuous_coordinates
  continuous_invFun := continuous_amplitude

/-- Negation preserves nonzero amplitude and uses the actual complex additive inverse. -/
def negate (t : NonzeroComplex) : NonzeroComplex := ⟨-(t : ℂ), neg_ne_zero.mpr t.property⟩

/-- Complex amplitude negation changes its unit phase to the antipode. -/
theorem phase_negate (t : NonzeroComplex) : phase (negate t) = -phase t := by
  apply Circle.ext
  simp [phase_coe, negate, neg_div]

/-- Complex amplitude negation preserves positive density and negates only the unit-circle coordinate. -/
theorem coordinates_negate (t : NonzeroComplex) :
    coordinates (negate t) = ((coordinates t).1, -(coordinates t).2) := by
  apply Prod.ext
  · apply Subtype.ext
    simp [coordinates, negate]
  · exact phase_negate t

/-- Antipodal unit phase reconstructs exactly the negative complex amplitude at the same density. -/
theorem amplitude_antipode (rho : PositiveDensity) (z : Circle) :
    amplitude (rho, -z) = negate (amplitude (rho, z)) := by
  apply Subtype.ext
  simp [amplitude, negate]

end FoliationQM.PolarAmplitudeTopology
