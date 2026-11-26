module

public import FoliationQM.SobolevDensity
public import FoliationQM.WaveDensityMeasure
public import FoliationQM.FullLineACIntegral

/-!
# Actual whole-line score integration by parts

Sources: v13 eq:cramer_rao, thm:uncertainty and eq:p_var_decomp,
component kinds C and D. Genuine local absolute continuity, actual
almost-everywhere derivatives and finite L² wave/derivative moments derive
the density boundary limits and score mean. The separately supplied position
L² moment gives the position-density boundary limit and centered score pairing.
Neither boundary behavior nor an integration-by-parts identity is assumed.

All classical derivatives concern the actual continuous AC representative.
The stronger unnormalized pairing equals minus its actual mass. A subsequent
source H¹ specialization supplies normalization and the genuine representative.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.WaveScoreIntegrationByParts
open MeasureTheory Filter WaveScoreAlgebra WaveDensityMeasure SobolevDensity
open scoped Topology

variable {u v : ℝ → ℂ}

/-- Actual AC and L² wave data force the density to vanish at both ends of the line. -/
theorem density_boundary
    (hAC : ∀ a b : ℝ, AbsolutelyContinuousOnInterval u a b)
    (hd : ∀ᵐ x, HasDerivAt u (v x) x)
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume) :
    Tendsto (fun x => density (u x)) atTop (𝓝 0) ∧
      Tendsto (fun x => density (u x)) atBot (𝓝 0) := by
  have hA := fun a b => absolutelyContinuousOnInterval_density (hAC a b)
  exact ⟨FullLineACIntegral.tendsto_zero_atTop hA (ae_hasDerivAt_density hd)
      (integrable_density hu) (integrable_densityDerivative hu hv),
    FullLineACIntegral.tendsto_zero_atBot hA (ae_hasDerivAt_density hd)
      (integrable_density hu) (integrable_densityDerivative hu hv)⟩

/-- The actual integrable density derivative has zero whole-line integral. -/
theorem integral_densityDerivative
    (hAC : ∀ a b : ℝ, AbsolutelyContinuousOnInterval u a b)
    (hd : ∀ᵐ x, HasDerivAt u (v x) x)
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume) :
    (∫ x, densityDerivative (u x) (v x)) = 0 :=
  FullLineACIntegral.integral_eq_zero
    (fun a b => absolutelyContinuousOnInterval_density (hAC a b))
    (ae_hasDerivAt_density hd) (integrable_density hu)
    (integrable_densityDerivative hu hv)

/-- The separate position moment forces the actual position-density boundary terms to vanish. -/
theorem position_density_boundary
    (hAC : ∀ a b : ℝ, AbsolutelyContinuousOnInterval u a b)
    (hd : ∀ᵐ x, HasDerivAt u (v x) x)
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume)
    (hxu : MemLp (fun x : ℝ => (x : ℂ) * u x) 2 volume) :
    Tendsto (fun x => x * density (u x)) atTop (𝓝 0) ∧
      Tendsto (fun x => x * density (u x)) atBot (𝓝 0) := by
  have hA := fun a b => absolutelyContinuousOnInterval_position_density (hAC a b)
  exact ⟨FullLineACIntegral.tendsto_zero_atTop hA (ae_hasDerivAt_position_density hd)
      (integrable_position_density hu hxu) (integrable_position_density_derivative hu hxu hv),
    FullLineACIntegral.tendsto_zero_atBot hA (ae_hasDerivAt_position_density hd)
      (integrable_position_density hu hxu) (integrable_position_density_derivative hu hxu hv)⟩

/-- Actual product differentiation and full-line integration give minus the true density mass. -/
theorem integral_position_densityDerivative
    (hAC : ∀ a b : ℝ, AbsolutelyContinuousOnInterval u a b)
    (hd : ∀ᵐ x, HasDerivAt u (v x) x)
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume)
    (hxu : MemLp (fun x : ℝ => (x : ℂ) * u x) 2 volume) :
    (∫ x, x * densityDerivative (u x) (v x)) = -(∫ x, density (u x)) := by
  have hz := FullLineACIntegral.integral_eq_zero
    (fun a b => absolutelyContinuousOnInterval_position_density (hAC a b))
    (ae_hasDerivAt_position_density hd) (integrable_position_density hu hxu)
    (integrable_position_density_derivative hu hxu hv)
  rw [integral_add (integrable_density hu) (integrable_position_densityDerivative hxu hv)] at hz
  linarith

/-- The canonical score has a genuine first moment even before unit normalization. -/
theorem integrable_score (hc : Continuous u)
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume) :
    Integrable (fun x => score (u x) (v x)) (densityMeasure u) := by
  apply (integrable_iff_weighted hc).mpr
  simpa only [smul_eq_mul, density_mul_score] using integrable_densityDerivative hu hv

/-- The actual weighted score mean vanishes by the derived density integral identity. -/
theorem integral_score (hc : Continuous u)
    (hAC : ∀ a b : ℝ, AbsolutelyContinuousOnInterval u a b)
    (hd : ∀ᵐ x, HasDerivAt u (v x) x)
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume) :
    (∫ x, score (u x) (v x) ∂densityMeasure u) = 0 := by
  rw [(integrable_and_integral_transport hc (integrable_score hc hu hv)).2]
  simpa only [smul_eq_mul, density_mul_score] using integral_densityDerivative hAC hd hu hv

private theorem integrable_shifted_densityDerivative
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume)
    (hxu : MemLp (fun x : ℝ => (x : ℂ) * u x) 2 volume) (a : ℝ) :
    Integrable (fun x => (x - a) * densityDerivative (u x) (v x)) volume := by
  apply ((integrable_position_densityDerivative hxu hv).sub
    ((integrable_densityDerivative hu hv).const_mul a)).congr
  exact Eventually.of_forall fun x => by
    simp only [Pi.sub_apply]
    ring

private theorem density_mul_shifted_score (x a : ℝ) :
    density (u x) * ((x - a) * score (u x) (v x)) =
      (x - a) * densityDerivative (u x) (v x) := by
  rw [mul_left_comm, density_mul_score]

/-- The actual shifted score pairing is integrable for every real center. -/
theorem integrable_shifted_score (hc : Continuous u)
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume)
    (hxu : MemLp (fun x : ℝ => (x : ℂ) * u x) 2 volume) (a : ℝ) :
    Integrable (fun x => (x - a) * score (u x) (v x)) (densityMeasure u) := by
  apply (integrable_iff_weighted hc).mpr
  simpa only [smul_eq_mul, density_mul_shifted_score] using
    integrable_shifted_densityDerivative hu hv hxu a

/-- For every actual center, the finite weighted score pairing is minus the true total mass. -/
theorem integral_shifted_score (hc : Continuous u)
    (hAC : ∀ a b : ℝ, AbsolutelyContinuousOnInterval u a b)
    (hd : ∀ᵐ x, HasDerivAt u (v x) x)
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume)
    (hxu : MemLp (fun x : ℝ => (x : ℂ) * u x) 2 volume) (a : ℝ) :
    (∫ x, (x - a) * score (u x) (v x) ∂densityMeasure u) =
      -(∫ x, density (u x)) := by
  calc
    (∫ x, (x - a) * score (u x) (v x) ∂densityMeasure u) =
        ∫ x, (x - a) * densityDerivative (u x) (v x) := by
      simpa only [smul_eq_mul, density_mul_shifted_score] using
        (integrable_and_integral_transport hc (integrable_shifted_score hc hu hv hxu a)).2
    _ = ∫ x, (x * densityDerivative (u x) (v x) -
        a * densityDerivative (u x) (v x)) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by ring
    _ = -(∫ x, density (u x)) := by
      rw [integral_sub (integrable_position_densityDerivative hxu hv)
        ((integrable_densityDerivative hu hv).const_mul a), integral_const_mul,
        integral_position_densityDerivative hAC hd hu hv hxu,
        integral_densityDerivative hAC hd hu hv, mul_zero, sub_zero]

/-- The true logarithmic density derivative has zero mean on the actual density measure. -/
theorem integral_log_derivative (hc : Continuous u)
    (hAC : ∀ a b : ℝ, AbsolutelyContinuousOnInterval u a b)
    (hd : ∀ᵐ x, HasDerivAt u (v x) x)
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume) :
    (∫ x, deriv (fun y => Real.log (density (u y))) x ∂densityMeasure u) = 0 := by
  calc
    (∫ x, deriv (fun y => Real.log (density (u y))) x ∂densityMeasure u) =
        ∫ x, score (u x) (v x) ∂densityMeasure u :=
      integral_congr_ae (ae_log_derivative_eq_score hc hd)
    _ = 0 := integral_score hc hAC hd hu hv

/-- Actual logarithmic differentiation gives the shifted integration-by-parts identity. -/
theorem integral_shifted_log_derivative (hc : Continuous u)
    (hAC : ∀ a b : ℝ, AbsolutelyContinuousOnInterval u a b)
    (hd : ∀ᵐ x, HasDerivAt u (v x) x)
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume)
    (hxu : MemLp (fun x : ℝ => (x : ℂ) * u x) 2 volume) (a : ℝ) :
    (∫ x, (x - a) * deriv (fun y => Real.log (density (u y))) x ∂densityMeasure u) =
      -(∫ x, density (u x)) := by
  calc
    (∫ x, (x - a) * deriv (fun y => Real.log (density (u y))) x ∂densityMeasure u) =
        ∫ x, (x - a) * score (u x) (v x) ∂densityMeasure u := by
      apply integral_congr_ae
      filter_upwards [ae_log_derivative_eq_score hc hd] with x hx
      rw [hx]
    _ = -(∫ x, density (u x)) := integral_shifted_score hc hAC hd hu hv hxu a

end FoliationQM.WaveScoreIntegrationByParts
