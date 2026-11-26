module

public import FoliationQM.WaveDensityMeasure
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Complex.RealDeriv

/-!
# Actual derivatives of supplied local polar phases

Sources: v13 eq:p_var_decomp and thm:uncertainty, component kinds C and D.
An actual differentiable amplitude and action phase, related to the wave on
a genuine neighborhood, determine its canonical bulk momentum. The amplitude
derivative is retained and cancels only from the imaginary quotient component.
The literal square-root density specialization derives that amplitude
derivative from the actual wave derivative.

For a supplied phase on the positive-density set, continuity of the wave
provides the required neighborhoods. Actual almost-everywhere differentiability
then identifies its derivative with bulk momentum under the density measure.
No regularity of a global principal argument or derivative at a node is asserted.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.SuppliedPolarPhase

open MeasureTheory Filter WaveScoreAlgebra WaveDensityMeasure
open scoped Topology

/-- A genuine differentiable amplitude-phase germ identifies the actual bulk
momentum with the supplied phase derivative, without discarding amplitude variation. -/
theorem bulk_eq_phase_derivative_of_amplitude
    {u : ℝ → ℂ} {A S : ℝ → ℝ} {x a s hbar : ℝ} {z : ℂ}
    (hu : HasDerivAt u z x) (hA : HasDerivAt A a x) (hS : HasDerivAt S s x)
    (hA0 : A x ≠ 0) (hh : hbar ≠ 0)
    (hpolar : u =ᶠ[𝓝 x] (fun y => (A y : ℂ) *
      Complex.exp (Complex.I * ((S y / hbar : ℝ) : ℂ)))) :
    bulk hbar (u x) z = s := by
  let e : ℂ := Complex.exp (Complex.I * ((S x / hbar : ℝ) : ℂ))
  have he : e ≠ 0 := Complex.exp_ne_zero _
  have hAc : (A x : ℂ) ≠ 0 := by exact_mod_cast hA0
  have hphase := ((hS.div_const hbar).ofReal_comp.const_mul Complex.I).cexp
  have hz : z = (a : ℂ) * e + (A x : ℂ) *
      (e * (Complex.I * ((s / hbar : ℝ) : ℂ))) :=
    hu.unique ((hA.ofReal_comp.mul hphase).congr_of_eventuallyEq hpolar)
  have hvalue : u x = (A x : ℂ) * e := hpolar.self_of_nhds
  have hquot : z / u x = ((a / A x : ℝ) : ℂ) +
      Complex.I * ((s / hbar : ℝ) : ℂ) := by
    have ha : ((a / A x : ℝ) : ℂ) = (a : ℂ) / (A x : ℂ) := Complex.ofReal_div _ _
    rw [hz, hvalue, ha]
    field_simp [hAc, he]
  rw [bulk, phaseRate_eq_im_div, hquot]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, zero_mul, one_mul, zero_add]
  field_simp [hh]

/-- The literal square-root wave density supplies its own actual amplitude
derivative, so every compatible differentiable polar germ has the canonical bulk derivative. -/
theorem bulk_eq_phase_derivative_of_density
    {u : ℝ → ℂ} {S : ℝ → ℝ} {x s hbar : ℝ} {z : ℂ}
    (hu : HasDerivAt u z x) (hS : HasDerivAt S s x)
    (hpos : 0 < density (u x)) (hh : hbar ≠ 0)
    (hpolar : u =ᶠ[𝓝 x] (fun y => (Real.sqrt (density (u y)) : ℂ) *
      Complex.exp (Complex.I * ((S y / hbar : ℝ) : ℂ)))) :
    bulk hbar (u x) z = s :=
  bulk_eq_phase_derivative_of_amplitude hu
    ((hasDerivAt_density hu).sqrt hpos.ne') hS
    (Real.sqrt_pos.mpr hpos).ne' hh hpolar

/-- A genuinely compatible supplied phase has its actual derivative equal to
bulk momentum almost everywhere for the wave-density measure. -/
theorem ae_deriv_eq_bulk {u g : ℝ → ℂ} {S : ℝ → ℝ} {hbar : ℝ}
    (hu : Continuous u) (hd : ∀ᵐ x ∂volume, HasDerivAt u (g x) x)
    (hS : ∀ᵐ x ∂volume, 0 < density (u x) → DifferentiableAt ℝ S x)
    (hh : hbar ≠ 0)
    (hpolar : ∀ x, 0 < density (u x) →
      u x = (Real.sqrt (density (u x)) : ℂ) *
        Complex.exp (Complex.I * ((S x / hbar : ℝ) : ℂ))) :
    deriv S =ᵐ[densityMeasure u] (fun x => bulk hbar (u x) (g x)) := by
  apply (ae_iff_positive hu _).mpr
  have hopen : IsOpen {x : ℝ | 0 < density (u x)} :=
    isOpen_lt continuous_const (hu.norm.pow 2)
  filter_upwards [hd, hS] with x hdx hSx hpos
  have hpositive : ∀ᶠ y in 𝓝 x, 0 < density (u y) := hopen.mem_nhds hpos
  have hgerm : u =ᶠ[𝓝 x] (fun y => (Real.sqrt (density (u y)) : ℂ) *
      Complex.exp (Complex.I * ((S y / hbar : ℝ) : ℂ))) := by
    filter_upwards [hpositive] with y hy
    exact hpolar y hy
  exact (bulk_eq_phase_derivative_of_density hdx (hSx hpos).hasDerivAt
    hpos hh hgerm).symm

end FoliationQM.SuppliedPolarPhase
