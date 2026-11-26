module

public import FoliationQM.ClockPhaseUniqueness

/-!
# The correspondence between waves and polar pairs modulo a constant phase

Source: v13 `thm:wallstrom` Part(c), "establishing a global bijection modulo
constant `U(1)` phase on each connected component of `Ω`", with Part(a),
component kinds B and C. On the complement of the nodal set, the map sending
a non-vanishing differentiable wave `ψ` to its polar pair, the modulus `|ψ|`
and the clock form `-ω⁻¹ Im(dψ/ψ)`, has the following properties.

* It is onto the pairs that carry a unit phase: for a positive differentiable
  amplitude `R` and a unit phase `q` with the clock differential relation for
  `α`, the wave `R q` does not vanish, has modulus `R` and has clock form `α`.
* Its fibres are the constant-phase orbits: on an open connected set two
  non-vanishing differentiable waves have the same polar pair exactly when
  one is a constant unit multiple of the other.
* A wave is recovered from its own pair: `ψ = |ψ| · (ψ/|ψ|)`, and `ψ/|ψ|` is a
  unit phase with the clock differential relation for the clock form of `ψ`.

Together these give the bijection between waves modulo constant phase and
polar pairs with a single-valued phase, on each open connected subset of the
nodal complement. The single-valued phase is the source's hypothesis; the
equation, the energy bound and the continuation across the nodal set are
treated separately and are not part of this correspondence.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.PolarWaveBijection

open Set NodalPolarConverse CirclePolarEnergy ClockPhaseUniqueness
open scoped Topology ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {R : E → ℝ} {q : E → ℂ}
  {dR α : E →L[ℝ] ℝ} {w : ℝ} {x : E}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The wave reconstructed from a positive amplitude and a unit phase has
that amplitude as its modulus. -/
theorem amplitude_field (hR : 0 < R x) (hq : ‖q x‖ = 1) : amplitude (field R q) x = R x := by
  simp only [amplitude, field, norm_smul, hq, mul_one, Real.norm_of_nonneg hR.le]

/-- The wave reconstructed from an amplitude and a unit phase with the clock
differential relation has the given clock form. -/
theorem clockDeriv_field (hw : w ≠ 0) (hRpos : 0 < R x) (hunit : ‖q x‖ = 1)
    (hR : HasFDerivAt R dR x)
    (hq : HasFDerivAt q (α.smulRight (-Complex.I * (w : ℂ) * q x)) x) :
    clockDeriv w (field R q x) (fderiv ℝ (field R q) x) = α := by
  have hF := hasFDerivAt_field hR hq
  have hq0 : q x ≠ 0 := fun h => by
    rw [h, norm_zero] at hunit
    exact zero_ne_one hunit
  have hR0 : (R x : ℂ) ≠ 0 := by exact_mod_cast hRpos.ne'
  have hwc : (w : ℂ) ≠ 0 := by exact_mod_cast hw
  ext v
  rw [clockDeriv_apply, hF.fderiv]
  simp only [field, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    Complex.real_smul]
  have e : ((R x : ℂ) * q x)⁻¹ * ((R x : ℂ) * ((α v : ℂ) * (-Complex.I * (w : ℂ) * q x)) +
      (dR v : ℂ) * q x) = -Complex.I * ((w * α v : ℝ) : ℂ) + ((dR v / R x : ℝ) : ℂ) := by
    push_cast
    field_simp
  rw [e]
  simp only [Complex.add_im, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  field_simp
  ring

/-- Surjectivity onto pairs with a unit phase: the reconstructed wave is
differentiable and non-vanishing with the prescribed modulus and clock form. -/
theorem reconstructed_pair (hw : w ≠ 0) (hRpos : 0 < R x) (hunit : ‖q x‖ = 1)
    (hR : HasFDerivAt R dR x)
    (hq : HasFDerivAt q (α.smulRight (-Complex.I * (w : ℂ) * q x)) x) :
    DifferentiableAt ℝ (field R q) x ∧ field R q x ≠ 0 ∧ amplitude (field R q) x = R x ∧
      clockDeriv w (field R q x) (fderiv ℝ (field R q) x) = α :=
  ⟨(hasFDerivAt_field hR hq).differentiableAt, field_ne_zero hRpos hunit,
    amplitude_field hRpos hunit, clockDeriv_field hw hRpos hunit hR hq⟩

/-- The fibres of the polar map are the constant-phase orbits: on an open
connected set two non-vanishing differentiable waves have equal modulus and
equal clock form exactly when they differ by a constant unit phase. -/
theorem same_pair_iff {C : Set E} {ψ₁ ψ₂ : E → ℂ} (hw : w ≠ 0) (hC : IsOpen C)
    (hconn : IsPreconnected C)
    (hd₁ : ∀ x ∈ C, DifferentiableAt ℝ ψ₁ x) (hd₂ : ∀ x ∈ C, DifferentiableAt ℝ ψ₂ x)
    (hn₁ : ∀ x ∈ C, ψ₁ x ≠ 0) (hn₂ : ∀ x ∈ C, ψ₂ x ≠ 0) :
    ((∀ x ∈ C, amplitude ψ₂ x = amplitude ψ₁ x) ∧
      ∀ x ∈ C, clockDeriv w (ψ₂ x) (fderiv ℝ ψ₂ x) = clockDeriv w (ψ₁ x) (fderiv ℝ ψ₁ x)) ↔
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ x ∈ C, ψ₂ x = c * ψ₁ x := by
  constructor
  · rintro ⟨hmod, hclock⟩
    obtain ⟨c, hc, h⟩ := wave_unique hw hC hconn hd₁ hd₂ hn₁ hn₂ hmod hclock
    by_cases hne : C.Nonempty
    · exact ⟨c, hc hne, h⟩
    · exact ⟨1, norm_one, fun x hx => absurd ⟨x, hx⟩ hne⟩
  · rintro ⟨c, hc, h⟩
    refine ⟨fun x hx => by simp only [amplitude, h x hx, norm_mul, hc, one_mul],
      fun x hx => ?_⟩
    have hev : ψ₂ =ᶠ[𝓝 x] fun y => c * ψ₁ y := Filter.eventuallyEq_of_mem (hC.mem_nhds hx) h
    rw [hev.fderiv_eq, h x hx]
    exact (modulus_clock_of_phase_multiple c hc (hd₁ x hx)).2

/-- A non-vanishing differentiable wave is recovered from its own polar pair:
its unit phase has the clock differential relation for its clock form, and
the product of modulus and unit phase is the wave. -/
theorem wave_of_own_pair {ψ : E → ℂ} (hw : w ≠ 0) (hd : DifferentiableAt ℝ ψ x)
    (hne : ψ x ≠ 0) :
    0 < amplitude ψ x ∧ ‖unitPhase ψ x‖ = 1 ∧
      HasFDerivAt (unitPhase ψ) ((clockDeriv w (ψ x) (fderiv ℝ ψ x)).smulRight
        (-Complex.I * (w : ℂ) * unitPhase ψ x)) x ∧
      field (amplitude ψ) (unitPhase ψ) = ψ :=
  ⟨norm_pos_iff.mpr hne, norm_unitPhase hne, hasFDerivAt_unitPhase hw hd.hasFDerivAt hne,
    field_eq ψ⟩

end FoliationQM.PolarWaveBijection
