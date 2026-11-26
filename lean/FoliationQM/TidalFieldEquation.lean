module

public import FoliationQM.TidalAmplitudeVariation
public import FoliationQM.TidalCoefficient
public import FoliationQM.NodalPolarConverse

/-!
# The tidal correction to the field equation

Source: v13 `thm:tidal_dispersion` (Conjecture 9.7) and `eq:tidal_KG_eq`,
component kinds A, B and C. The modulus of a non-vanishing complex value has
derivative `Re(ψ̄ δψ)/|ψ|` along a complex direction, which is the source's
`δ|ψ| = (ψ/2|ψ|) δψ* + c.c.`. For a twice continuously differentiable field
non-vanishing on a set and a compactly supported complex variation supported
there, the first variation of the tidal functional in the induced amplitude
direction is `-2 Re ∫ δψ̄ (ψ/|ψ|) ∂_j(T^{ji} ∂_i |ψ|)`, so its derivative with
respect to `ψ*` is `-(ψ/|ψ|) ∂_j(T^{ji} ∂_i |ψ|)`. Adding this, with the tidal
coefficient, to `-ħ² √(-g)` times the Klein–Gordon operator and dividing by
`-ħ² √(-g)` gives the displayed correction with coefficient `+ħ²/(12m²c⁴)`.

The variation is taken along the affine amplitude curve `|ψ| + t a` in the
direction `a = Re(ψ̄ η)/|ψ|` induced by `η`; the functional is not
differentiated along the curve `|ψ + t η|` itself. The external velocity is
held fixed. Nothing here supports the physical ansatz of the conjecture or
extends through zeros of the field.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.TidalFieldEquation

open MeasureTheory Set LorentzMatrixGroup RNCCoordinateConnection RealLorentzFrame
open TidalAmplitudeVariation TidalCoefficient
open scoped Topology ComplexConjugate

/-- The modulus of a non-vanishing complex value varies along a complex
direction at the rate `Re(z̄ w)/|z|`. -/
theorem hasDerivAt_norm_line {z w : ℂ} (hz : z ≠ 0) :
    HasDerivAt (fun t : ℝ => ‖z + (t : ℂ) * w‖) ((conj z * w).re / ‖z‖) 0 := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hline : HasDerivAt (fun t : ℝ => z + (t : ℂ) * w) w 0 :=
    (((hasDerivAt_id' (0 : ℝ)).ofReal_comp.mul_const w).const_add z).congr_deriv (by simp)
  have h0 : z + ((0 : ℝ) : ℂ) * w = z := by simp
  have hF := (NodalPolarConverse.hasFDerivAt_amplitude hline.hasFDerivAt
    (by rw [h0]; exact hz)).hasDerivAt
  refine hF.congr_deriv ?_
  rw [NodalPolarConverse.amplitudeDeriv_apply, h0, ContinuousLinearMap.toSpanSingleton_apply,
    one_smul, Complex.inv_def, Complex.normSq_eq_norm_sq]
  have h1 : conj z * (((‖z‖ ^ 2)⁻¹ : ℝ) : ℂ) * w = (((‖z‖ ^ 2)⁻¹ : ℝ) : ℂ) * (conj z * w) := by
    ring
  rw [h1, Complex.re_ofReal_mul]
  field_simp

/-- The amplitude direction `Re(ψ̄ η)/|ψ|` induced by a complex variation `η`. -/
def amplitudeDirection (ψ η : Covector → ℂ) (x : Covector) : ℝ :=
  (conj (ψ x) * η x).re / ‖ψ x‖

/-- Pairing the amplitude direction with a real quantity is the real part of
the pairing of `η̄` with `ψ/|ψ|` times that quantity. -/
theorem amplitudeDirection_mul (ψ η : Covector → ℂ) (x : Covector) (D : ℝ) :
    amplitudeDirection ψ η x * D =
      (conj (η x) * (ψ x / (‖ψ x‖ : ℂ) * (D : ℂ))).re := by
  have h1 : conj (η x) * (ψ x / (‖ψ x‖ : ℂ) * (D : ℂ)) =
      ((D / ‖ψ x‖ : ℝ) : ℂ) * (conj (η x) * ψ x) := by
    push_cast
    ring
  have h2 : (conj (η x) * ψ x).re = (conj (ψ x) * η x).re := by
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  rw [h1, Complex.re_ofReal_mul, h2, amplitudeDirection]
  ring

variable {T : Covector → Mat4} {ψ η : Covector → ℂ} {U : Set Covector}

/-- The first variation of the tidal functional in the amplitude direction
induced by a compactly supported complex variation is
`-2 Re ∫ η̄ (ψ/|ψ|) ∂_j(T^{ji} ∂_i |ψ|)`. -/
theorem first_variation_complex (hsym : ∀ x ∈ U, (T x).IsSymm)
    (hT : ∀ i j, ∀ x ∈ U, ContDiffAt ℝ 1 (fun y => T y i j) x)
    (hψ : ∀ x ∈ U, ContDiffAt ℝ 2 ψ x) (hne : ∀ x ∈ U, ψ x ≠ 0)
    (hη : ContDiff ℝ 1 η) (hc : HasCompactSupport η) (hs : tsupport η ⊆ U) :
    HasDerivAt (fun t : ℝ => ∫ x,
        (tidalDensity T (fun y => ‖ψ y‖ + t * amplitudeDirection ψ η y) x -
          tidalDensity T (fun y => ‖ψ y‖) x))
      (-2 * ∫ x, (conj (η x) * (ψ x / (‖ψ x‖ : ℂ) *
        (tidalDivergence T (fun y => ‖ψ y‖) x : ℂ))).re) 0 := by
  have hsupp : Function.support (amplitudeDirection ψ η) ⊆ Function.support η := by
    intro x hx hηx
    exact hx (by simp [amplitudeDirection, hηx])
  have hts : tsupport (amplitudeDirection ψ η) ⊆ tsupport η := closure_mono hsupp
  have hca : HasCompactSupport (amplitudeDirection ψ η) := hc.mono hsupp
  have ha : ContDiff ℝ 1 (amplitudeDirection ψ η) := by
    refine contDiff_iff_contDiffAt.2 fun x => ?_
    by_cases hx : x ∈ tsupport η
    · have hψ1 : ContDiffAt ℝ 1 ψ x := (hψ x (hs hx)).of_le (by norm_num)
      have hnum : ContDiffAt ℝ 1 (fun y => (conj (ψ y) * η y).re) x :=
        Complex.reCLM.contDiff.contDiffAt.comp x
          ((Complex.conjCLE.contDiff.contDiffAt.comp x hψ1).mul hη.contDiffAt)
      exact hnum.div (hψ1.norm ℝ (hne x (hs hx))) (norm_ne_zero_iff.mpr (hne x (hs hx)))
    · have hz : amplitudeDirection ψ η =ᶠ[𝓝 x] fun _ => 0 :=
        (notMem_tsupport_iff_eventuallyEq.mp hx).mono fun y hy => by
          simp [amplitudeDirection, hy]
      exact contDiffAt_const.congr_of_eventuallyEq hz
  have h := first_variation hsym hT (R := fun y => ‖ψ y‖)
    (fun x hx => (hψ x hx).norm ℝ (hne x hx)) ha hca (hts.trans hs)
  have hfun : (fun x => amplitudeDirection ψ η x * tidalDivergence T (fun y => ‖ψ y‖) x) =
      fun x => (conj (η x) * (ψ x / (‖ψ x‖ : ℂ) *
        (tidalDivergence T (fun y => ‖ψ y‖) x : ℂ))).re :=
    funext fun x => amplitudeDirection_mul ψ η x _
  rw [hfun] at h
  exact h

/-- The coefficient of the correction: `κ/ħ² = ħ²/(12m²c⁴)`. -/
theorem kappa_div (p : MassiveParameters) :
    kappa p / p.hbar ^ 2 = p.hbar ^ 2 / (12 * p.m ^ 2 * p.c ^ 4) := by
  have hh := p.hbar_pos.ne'
  have hm := p.m_pos.ne'
  have hc := p.c_pos.ne'
  simp only [kappa]
  field_simp

/-- Adding the tidal variation to `-ħ² √(-g)` times the Klein–Gordon operator
and dividing by `-ħ² √(-g)` gives the corrected equation with coefficient
`+ħ²/(12m²c⁴)`. Here `K` is the value of the Klein–Gordon operator and `W` the
value of `(ψ/|ψ|) ∇_μ(B^{μν} ∇_ν |ψ|)`. -/
theorem tidal_equation_iff (p : MassiveParameters) {vol : ℝ} (hvol : vol ≠ 0) (K W : ℂ) :
    -((p.hbar ^ 2 * vol : ℝ) : ℂ) * K - ((kappa p * vol : ℝ) : ℂ) * W = 0 ↔
      K + ((p.hbar ^ 2 / (12 * p.m ^ 2 * p.c ^ 4) : ℝ) : ℂ) * W = 0 := by
  have hh : (p.hbar : ℂ) ≠ 0 := by exact_mod_cast p.hbar_pos.ne'
  have hv : (vol : ℂ) ≠ 0 := by exact_mod_cast hvol
  have hk : ((kappa p * vol : ℝ) : ℂ) =
      ((p.hbar ^ 2 * vol : ℝ) : ℂ) * ((p.hbar ^ 2 / (12 * p.m ^ 2 * p.c ^ 4) : ℝ) : ℂ) := by
    rw [← kappa_div]
    push_cast
    field_simp
  have hne : ((p.hbar ^ 2 * vol : ℝ) : ℂ) ≠ 0 := by
    push_cast
    exact mul_ne_zero (pow_ne_zero 2 hh) hv
  rw [hk]
  constructor
  · intro h
    have h' : -((p.hbar ^ 2 * vol : ℝ) : ℂ) *
        (K + ((p.hbar ^ 2 / (12 * p.m ^ 2 * p.c ^ 4) : ℝ) : ℂ) * W) = 0 := by
      linear_combination h
    exact (mul_eq_zero.mp h').resolve_left (neg_ne_zero.mpr hne)
  · intro h
    linear_combination -((p.hbar ^ 2 * vol : ℝ) : ℂ) * h

end FoliationQM.TidalFieldEquation
