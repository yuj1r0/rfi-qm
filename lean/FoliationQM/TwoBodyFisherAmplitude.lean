module

public import FoliationQM.TwoBodyCoordinates
public import FoliationQM.TwoParticleFisher

/-!
# Two-particle Fisher energy in density and amplitude coordinates

On a fixed physical-time slice, the six spatial derivatives in v13
`eq:fisher_2p_main` give exactly the two inverse-mass-weighted squared
amplitude gradients in `eq:2p_HJF_action`. The pointwise identities hold
at positive density. The integrated identities also hold with positivity
and differentiability almost everywhere on the slice.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.TwoBodyFisherAmplitude

open MeasureTheory LorentzCoordinates ObserverGaussianFisher TwoBodyCoordinates
open TwoParticleFisher JointScoreRegularity FisherNormalization
open scoped BigOperators

/-- Restrict a joint spacetime field to the two positions at one common time. -/
def slice (t : ℝ) (ρ : Point → ℝ) (z : Spatial × Spatial) : ℝ := ρ ((t,z.1),z.2)

/-- The six density derivatives with the source's physical Fisher weights. -/
def rawDensity (hbar m₁ m₂ : ℝ) (ρ : Point → ℝ) (p : Point) : ℝ :=
  coefficient hbar m₁ * (∑ i, (D₁ i ρ p)^2 / ρ p) +
  coefficient hbar m₂ * (∑ i, (D₂ i ρ p)^2 / ρ p)

/-- Spatial amplitude-gradient energy density on joint spacetime. -/
def amplitudeDensity (hbar m₁ m₂ : ℝ) (R : Point → ℝ) (p : Point) : ℝ :=
  hbar^2 / (2*m₁) * (∑ i, (D₁ i R p)^2) +
  hbar^2 / (2*m₂) * (∑ i, (D₂ i R p)^2)

variable {t : ℝ} {x y : Spatial} {ρ R : Point → ℝ} {p : Point}

/-- At positive density, the score of the first fixed-time fiber uses its physical derivative. -/
theorem firstScore_slice (hρ : DifferentiableAt ℝ ρ ((t,x),y)) (hp : 0 < ρ ((t,x),y))
    (i : Fin 3) : firstScore (slice t ρ) x y (axes i) = D₁ i ρ ((t,x),y) / ρ ((t,x),y) := by
  have h : DifferentiableAt ℝ (fun u : Spatial => ρ ((t,u),y)) x :=
    hρ.comp x (by fun_prop)
  exact (score_eq h hp (axes i)).trans (congrArg (· / ρ ((t,x),y)) (left_fderiv hρ (axes i)))

/-- The remote fiber score uses the second-particle spatial derivative at fixed time. -/
theorem secondScore_slice (hρ : DifferentiableAt ℝ ρ ((t,x),y)) (hp : 0 < ρ ((t,x),y))
    (i : Fin 3) : secondScore (slice t ρ) x y (axes i) = D₂ i ρ ((t,x),y) / ρ ((t,x),y) := by
  have h : DifferentiableAt ℝ (fun u : Spatial => ρ ((t,x),u)) y :=
    hρ.comp y (by fun_prop)
  exact (score_eq h hp (axes i)).trans (congrArg (· / ρ ((t,x),y)) (remote_fderiv hρ (axes i)))

/-- The existing score-based physical integrand agrees with the raw ratio of density gradients. -/
theorem jointDensity_eq_raw (hbar m₁ m₂ : ℝ) (hρ : DifferentiableAt ℝ ρ ((t,x),y))
    (hp : 0 < ρ ((t,x),y)) :
    jointDensity hbar m₁ m₂ (slice t ρ) (x,y) = rawDensity hbar m₁ m₂ ρ ((t,x),y) := by
  have scalar (a : ℝ) : ρ ((t,x),y) * (a / ρ ((t,x),y))^2 = a^2 / ρ ((t,x),y) := by
    field_simp
  simp only [jointDensity, firstScore_slice hρ hp, secondScore_slice hρ hp, slice,
    Finset.mul_sum, scalar, rawDensity]

private theorem weighted_four (hbar m : ℝ) (u : Fin 3 → ℝ) :
    coefficient hbar m * (∑ i, 4 * u i) = hbar^2 / (2*m) * (∑ i, u i) := by
  rw [← Finset.mul_sum]
  simp only [coefficient, div_eq_mul_inv, mul_inv_rev]
  ring

private theorem square_density_direction (v : Point) (hR : DifferentiableAt ℝ R p)
    (hn : R p ≠ 0) : (D v (fun q => R q ^ 2) p)^2 / (R p)^2 = 4 * (D v R p)^2 := by
  simp only [D, pow_two, fderiv_fun_mul hR hR, add_apply,
    smul_apply, smul_eq_mul]
  field_simp
  ring

/-- Away from amplitude zeros the physical density-gradient penalty is the amplitude-gradient
energy. The amplitude may have either sign. -/
theorem rawDensity_sq_eq_amplitude (hbar m₁ m₂ : ℝ) (hR : DifferentiableAt ℝ R p)
    (hn : R p ≠ 0) :
    rawDensity hbar m₁ m₂ (fun q => R q ^ 2) p = amplitudeDensity hbar m₁ m₂ R p := by
  simp only [rawDensity, D₁, D₂, square_density_direction _ hR hn, weighted_four, amplitudeDensity]

/-- The Fisher integrand of the squared amplitude equals its kinetic gradient energy. -/
theorem jointDensity_sq_eq_amplitude (hbar m₁ m₂ : ℝ) (hR : DifferentiableAt ℝ R ((t,x),y))
    (hn : R ((t,x),y) ≠ 0) :
    jointDensity hbar m₁ m₂ (slice t (fun q => R q ^ 2)) (x,y) =
      amplitudeDensity hbar m₁ m₂ R ((t,x),y) :=
  (jointDensity_eq_raw hbar m₁ m₂ (hR.pow 2) (sq_pos_of_ne_zero hn)).trans
    (rawDensity_sq_eq_amplitude hbar m₁ m₂ hR hn)

private theorem sqrt_density_direction (v : Point) (hρ : DifferentiableAt ℝ ρ p)
    (hp : 0 < ρ p) :
    (D v ρ p)^2 / ρ p = 4 * (D v (fun q => √(ρ q)) p)^2 := by
  simp only [D, fderiv_sqrt hρ hp.ne', smul_apply, smul_eq_mul]
  have hs := Real.sq_sqrt hp.le
  field_simp [hp.ne', (Real.sqrt_pos.2 hp).ne']
  nlinarith only [congrArg (· * (fderiv ℝ ρ p v)^2) hs]

/-- Recovering the positive square root from the density gives the same local gradient penalty. -/
theorem rawDensity_eq_sqrt (hbar m₁ m₂ : ℝ) (hρ : DifferentiableAt ℝ ρ p)
    (hp : 0 < ρ p) :
    rawDensity hbar m₁ m₂ ρ p = amplitudeDensity hbar m₁ m₂ (fun q => √(ρ q)) p := by
  simp only [rawDensity, D₁, D₂, sqrt_density_direction _ hρ hp, weighted_four, amplitudeDensity]

/-- The physical Fisher integrand is the kinetic gradient energy of the positive square root. -/
theorem jointDensity_eq_sqrt (hbar m₁ m₂ : ℝ) (hρ : DifferentiableAt ℝ ρ ((t,x),y))
    (hp : 0 < ρ ((t,x),y)) :
    jointDensity hbar m₁ m₂ (slice t ρ) (x,y) =
      amplitudeDensity hbar m₁ m₂ (fun q => √(ρ q)) ((t,x),y) :=
  (jointDensity_eq_raw hbar m₁ m₂ hρ hp).trans (rawDensity_eq_sqrt hbar m₁ m₂ hρ hp)

/-- The score, raw density-gradient and square-root integrands have the same integrability
on a physical-time slice when density and regularity conditions hold almost everywhere. -/
theorem integrable_slice_iff (hbar m₁ m₂ t : ℝ) (ρ : Point → ℝ)
    (h : ∀ᵐ z : Spatial × Spatial, DifferentiableAt ℝ ρ ((t,z.1),z.2) ∧ 0 < slice t ρ z) :
    (Integrable (jointDensity hbar m₁ m₂ (slice t ρ)) ↔
      Integrable (slice t (rawDensity hbar m₁ m₂ ρ))) ∧
    (Integrable (jointDensity hbar m₁ m₂ (slice t ρ)) ↔
      Integrable (slice t (amplitudeDensity hbar m₁ m₂ (fun q => √(ρ q))))) :=
  ⟨integrable_congr (h.mono fun _ hz => jointDensity_eq_raw _ _ _ hz.1 hz.2),
    integrable_congr (h.mono fun _ hz => jointDensity_eq_sqrt _ _ _ hz.1 hz.2)⟩

/-- Integration over the configuration slice recovers the joint Fisher energy in both forms. -/
theorem jointEnergy_eq_raw_and_sqrt (hbar m₁ m₂ t : ℝ) (ρ : Point → ℝ)
    (h : ∀ᵐ z : Spatial × Spatial, DifferentiableAt ℝ ρ ((t,z.1),z.2) ∧ 0 < slice t ρ z)
    (hi : Integrable (jointDensity hbar m₁ m₂ (slice t ρ))) :
    jointEnergy hbar m₁ m₂ (slice t ρ) = ∫ z, slice t (rawDensity hbar m₁ m₂ ρ) z ∧
    jointEnergy hbar m₁ m₂ (slice t ρ) =
      ∫ z, slice t (amplitudeDensity hbar m₁ m₂ (fun q => √(ρ q))) z := by
  have _ := (integrable_slice_iff hbar m₁ m₂ t ρ h).1.mp hi
  have _ := (integrable_slice_iff hbar m₁ m₂ t ρ h).2.mp hi
  exact ⟨integral_congr_ae (h.mono fun _ hz => jointDensity_eq_raw _ _ _ hz.1 hz.2),
    integral_congr_ae (h.mono fun _ hz => jointDensity_eq_sqrt _ _ _ hz.1 hz.2)⟩

/-- A differentiable nonzero amplitude almost everywhere yields the same finite physical
energy directly from its gradient. -/
theorem jointEnergy_sq_eq_amplitude (hbar m₁ m₂ t : ℝ) (R : Point → ℝ)
    (h : ∀ᵐ z : Spatial × Spatial, DifferentiableAt ℝ R ((t,z.1),z.2) ∧ slice t R z ≠ 0)
    (hi : Integrable (slice t (amplitudeDensity hbar m₁ m₂ R))) :
    Integrable (jointDensity hbar m₁ m₂ (slice t (fun q => R q ^ 2))) ∧
    jointEnergy hbar m₁ m₂ (slice t (fun q => R q ^ 2)) = ∫ z, slice t (amplitudeDensity hbar m₁ m₂ R) z := by
  have he : jointDensity hbar m₁ m₂ (slice t (fun q => R q ^ 2)) =ᵐ[volume]
      slice t (amplitudeDensity hbar m₁ m₂ R) :=
    h.mono fun _ hz => jointDensity_sq_eq_amplitude _ _ _ hz.1 hz.2
  exact ⟨(integrable_congr he).mpr hi, integral_congr_ae he⟩

end FoliationQM.TwoBodyFisherAmplitude
