module

public import FoliationQM.TwoBodyDensityVariation
public import FoliationQM.TwoBodyPhaseVariation

/-!
# Variations of the printed two-particle action

Finite classical and Fisher spacetime integrals identify each absolute
action with its iterated time-slice form. The phase direction preserves
both integrability conditions for every parameter. In the density
direction they hold throughout a neighborhood of zero.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.TwoBodySourceVariations

open MeasureTheory TwoBodyCoordinates TwoBodyActionDensity TwoBodyActions
open TwoBodySchrodingerResidual TwoBodyPolarContinuity
open scoped Topology

/-- Separate integrability of the classical and Fisher terms suffices for their signed sum. -/
theorem integrable_density {h m₁ m₂ : ℝ} {V ρ S : Point → ℝ}
    (hc : Integrable (classicalDensity m₁ m₂ V ρ S)) (hf : Integrable (fisherL h m₁ m₂ ρ)) :
    Integrable (densityL h m₁ m₂ V ρ S) := by
  apply (hc.add hf).neg.congr
  filter_upwards with p
  change -(classicalDensity m₁ m₂ V ρ S p + fisherL h m₁ m₂ ρ p) = _
  unfold classicalDensity densityL
  ring

/-- The integrated relative density is the difference of two finite printed time-slice actions. -/
theorem relative_eq_source_sub (h m₁ m₂ : ℝ) (V : Point → ℝ) {ρ₀ ρ₁ S₀ S₁ : Point → ℝ}
    (hr₀ : Differentiable ℝ ρ₀) (hp₀ : ∀ p, 0 < ρ₀ p)
    (hr₁ : Differentiable ℝ ρ₁) (hp₁ : ∀ p, 0 < ρ₁ p)
    (hc₀ : Integrable (classicalDensity m₁ m₂ V ρ₀ S₀)) (hf₀ : Integrable (fisherL h m₁ m₂ ρ₀))
    (hc₁ : Integrable (classicalDensity m₁ m₂ V ρ₁ S₁)) (hf₁ : Integrable (fisherL h m₁ m₂ ρ₁)) :
    relative (densityL h m₁ m₂ V ρ₀ S₀) (densityL h m₁ m₂ V ρ₁ S₁) =
      sourceAction h m₁ m₂ V ρ₁ S₁ - sourceAction h m₁ m₂ V ρ₀ S₀ := by
  rw [relative_eq_sub (integrable_density hc₀ hf₀) (integrable_density hc₁ hf₁),
    ← integral_densityL h m₁ m₂ V ρ₀ S₀ hr₀ hp₀ hc₀ hf₀,
    ← integral_densityL h m₁ m₂ V ρ₁ S₁ hr₁ hp₁ hc₁ hf₁]

private theorem absolute_of_relative {A L : ℝ → ℝ} {v c : ℝ}
    (hd : HasDerivAt L v 0) (he : L =ᶠ[𝓝 0] fun t => A t-c) :
    HasDerivAt A v 0 := by
  apply (hd.add_const c).congr_of_eventuallyEq
  filter_upwards [he] with t ht
  rw [ht, sub_add_cancel]

/-- Varying phase in the finite time-slice action gives the tested continuity residual. -/
theorem phase (h m₁ m₂ : ℝ) {V ρ S b : Point → ℝ} (hρ : ContDiff ℝ 1 ρ)
    (hp : ∀ p, 0 < ρ p) (hS : ContDiff ℝ 2 S) (hb : ContDiff ℝ 1 b) (hc : HasCompactSupport b)
    (hC : Integrable (classicalDensity m₁ m₂ V ρ S)) (hF : Integrable (fisherL h m₁ m₂ ρ)) :
    HasDerivAt (fun s => sourceAction h m₁ m₂ V ρ (fun z => S z + s*b z))
      (∫ p, b p * continuity m₁ m₂ ρ S p) 0 := by
  apply absolute_of_relative (TwoBodyPhaseVariation.hasDerivAt_relative h m₁ m₂ V hρ hS hb hc)
    (c := sourceAction h m₁ m₂ V ρ S)
  filter_upwards with s
  have hd := hρ.differentiable (by norm_num)
  exact relative_eq_source_sub h m₁ m₂ V hd hp hd hp hC hF
    (TwoBodyPhaseVariation.integrable_classical_perturbed m₁ m₂ V hρ hS hb hc hC s) hF

/-- Varying density in the finite time-slice action gives the negative tested Hamilton–Jacobi residual. -/
theorem density (h m₁ m₂ : ℝ) {V ρ S a : Point → ℝ} (hV : Continuous V)
    (hρ : ContDiff ℝ 2 ρ) (hp : ∀ p, 0 < ρ p) (hS : ContDiff ℝ 1 S)
    (ha : ContDiff ℝ 1 a) (hc : HasCompactSupport a)
    (hC : Integrable (classicalDensity m₁ m₂ V ρ S)) (hF : Integrable (fisherL h m₁ m₂ ρ)) :
    HasDerivAt (fun s => sourceAction h m₁ m₂ V (fun z => ρ z + s*a z) S)
      (-(∫ p, a p * hamiltonJacobi h m₁ m₂ V (fun z => √(ρ z)) S p)) 0 := by
  apply absolute_of_relative (TwoBodyDensityVariation.hasDerivAt_relative h m₁ m₂ hV hρ hp hS ha hc)
    (c := sourceAction h m₁ m₂ V ρ S)
  obtain ⟨ε,hε,hpos⟩ := CompactPerturbation.exists_pos_affine hρ.continuous hp ha.continuous hc
  have he : ∀ᶠ s : ℝ in 𝓝 0, |s| < ε := by
    simpa only [Real.dist_eq, sub_zero] using
      (Metric.eventually_nhds_iff_ball.mpr ⟨ε, hε, fun _ hs => hs⟩ :
        ∀ᶠ s in 𝓝 (0 : ℝ), dist s 0 < ε)
  filter_upwards [he, TwoBodyFisherVariation.integrable_fisher_change h m₁ m₂
    (hρ.of_le (by norm_num)) hp ha hc] with s hs hi
  have hf : Integrable (fisherL h m₁ m₂ (fun z => ρ z + s*a z)) := by
    apply (hi.add hF).congr
    filter_upwards with p
    exact sub_add_cancel _ _
  exact relative_eq_source_sub h m₁ m₂ V (hρ.differentiable (by norm_num)) hp
    ((hρ.differentiable (by norm_num)).add ((ha.differentiable (by norm_num)).const_mul s))
    (hpos s hs) hC hF (TwoBodyDensityVariation.integrable_classical_perturbed m₁ m₂ hV hS
      ha.continuous hc hC s) hf

end FoliationQM.TwoBodySourceVariations
