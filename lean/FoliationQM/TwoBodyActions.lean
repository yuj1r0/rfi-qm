module

public import FoliationQM.TwoBodyActionDensity

/-!
# The two-body Hamilton–Jacobi–Fisher and quadratic actions

Fubini converts seven-dimensional spacetime integration into time
integration of six-dimensional spatial slices. This identifies the
printed action, including the previously defined physical joint Fisher
functional, with the quadratic Schrödinger action on positive charts.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.TwoBodyActions

open MeasureTheory LorentzCoordinates TwoBodyCoordinates TwoBodyActionDensity
open TwoBodyPolarWave TwoBodyFisherAmplitude TwoParticleFisher
open scoped BigOperators

/-- The non-Fisher part inside the negative sign of the printed polar action. -/
def classicalDensity (m₁ m₂ : ℝ) (V ρ S : Point → ℝ) (p : Point) : ℝ :=
  ρ p * (Dt S p + (∑ j : Index, (D (axis j) S p)^2 / (2 * mass m₁ m₂ j)) + V p)

/-- The v13 action as an integral in time of its classical and physical Fisher slice integrals. -/
def sourceAction (h m₁ m₂ : ℝ) (V ρ S : Point → ℝ) : ℝ :=
  -(∫ t, (∫ z : Spatial × Spatial, classicalDensity m₁ m₂ V ρ S ((t,z.1),z.2)) +
    jointEnergy h m₁ m₂ (slice t ρ))

/-- The quadratic Schrödinger action of a complex configuration-space wave. -/
def quadraticAction (h m₁ m₂ : ℝ) (V : Point → ℝ) (ψ : Point → ℂ) : ℝ :=
  ∫ p, complexL h m₁ m₂ V ψ p

/-- A finite relative action integrates the change in the Lagrangian density. -/
def relative (L₀ L₁ : Point → ℝ) : ℝ := ∫ p, L₁ p - L₀ p

/-- For integrable absolute densities the relative action equals their difference. -/
theorem relative_eq_sub {L₀ L₁ : Point → ℝ} (h₀ : Integrable L₀) (h₁ : Integrable L₁) :
    relative L₀ L₁ = (∫ p, L₁ p) - ∫ p, L₀ p := integral_sub h₁ h₀

/-- An integrable spacetime density has the iterated time and two-particle slice integral. -/
theorem integral_slices {L : Point → ℝ} (hi : Integrable L) :
    (∫ p, L p) = ∫ t, ∫ z : Spatial × Spatial, L ((t,z.1),z.2) := by
  have ha := (volume_preserving_prodAssoc (α₁ := ℝ) (β₁ := Spatial) (γ₁ := Spatial)).symm
  exact (ha.integral_comp' L).symm.trans
    (integral_prod _ (ha.integrable_comp_of_integrable hi))

/-- The integrated nonlinear spacetime density equals the printed time-slice action
when the classical and Fisher contributions are separately integrable. -/
theorem integral_densityL (h m₁ m₂ : ℝ) (V ρ S : Point → ℝ)
    (hρ : Differentiable ℝ ρ) (hp : ∀ p, 0 < ρ p)
    (hc : Integrable (classicalDensity m₁ m₂ V ρ S)) (hf : Integrable (fisherL h m₁ m₂ ρ)) :
    (∫ p, densityL h m₁ m₂ V ρ S p) = sourceAction h m₁ m₂ V ρ S := by
  let C := classicalDensity m₁ m₂ V ρ S
  let F := fisherL h m₁ m₂ ρ
  have ha := (volume_preserving_prodAssoc (α₁ := ℝ) (β₁ := Spatial) (γ₁ := Spatial)).symm
  have hc' : Integrable (fun z : ℝ × Spatial × Spatial => C ((z.1,z.2.1),z.2.2)) :=
    ha.integrable_comp_of_integrable hc
  have hf' : Integrable (fun z : ℝ × Spatial × Spatial => F ((z.1,z.2.1),z.2.2)) :=
    ha.integrable_comp_of_integrable hf
  have hs (t : ℝ) : (∫ z : Spatial × Spatial, F ((t,z.1),z.2)) = jointEnergy h m₁ m₂ (slice t ρ) := by
    apply integral_congr_ae
    filter_upwards with z
    change fisherL h m₁ m₂ ρ ((t,z.1),z.2) = jointDensity h m₁ m₂ (slice t ρ) z
    rcases z with ⟨x,y⟩
    rw [fisherL_eq_rawDensity, jointDensity_eq_raw h m₁ m₂ (hρ _) (hp _)]
  have hl (p : Point) : densityL h m₁ m₂ V ρ S p = -(C p + F p) := by
    unfold C F classicalDensity densityL
    ring
  simp only [hl, integral_neg]
  unfold sourceAction
  congr 1
  have hiC : Integrable C := hc
  have hiF : Integrable F := hf
  rw [integral_add hiC hiF, integral_slices hiC, integral_slices hiF,
    ← integral_add hc'.integral_prod_left hf'.integral_prod_left]
  exact integral_congr_ae (.of_forall fun t => congrArg (_ + ·) (hs t))

/-- Finite absolute classical and Fisher contributions give an absolutely
integrable quadratic density after the polar substitution. -/
theorem quadratic_integrable {h : ℝ} (hh : h ≠ 0) (m₁ m₂ : ℝ) (V ρ S : Point → ℝ)
    (hρ : Differentiable ℝ ρ) (hS : Differentiable ℝ S) (hp : ∀ p, 0 < ρ p)
    (hc : Integrable (classicalDensity m₁ m₂ V ρ S)) (hf : Integrable (fisherL h m₁ m₂ ρ)) :
    Integrable (complexL h m₁ m₂ V (wave h (fun p => Real.sqrt (ρ p)) S)) := by
  apply (hc.add hf).neg.congr
  filter_upwards with p
  rw [complexL_sqrt hh m₁ m₂ V (hρ p) (hS p) (hp p)]
  change -(classicalDensity m₁ m₂ V ρ S p + fisherL h m₁ m₂ ρ p) = _
  unfold classicalDensity densityL
  ring

/-- On a positive differentiable density chart the actual quadratic action is
the source Hamilton–Jacobi–Fisher action with both particle masses. -/
theorem quadratic_eq_source {h : ℝ} (hh : h ≠ 0) (m₁ m₂ : ℝ) (V ρ S : Point → ℝ)
    (hρ : Differentiable ℝ ρ) (hS : Differentiable ℝ S) (hp : ∀ p, 0 < ρ p)
    (hc : Integrable (classicalDensity m₁ m₂ V ρ S)) (hf : Integrable (fisherL h m₁ m₂ ρ)) :
    quadraticAction h m₁ m₂ V (wave h (fun p => Real.sqrt (ρ p)) S) = sourceAction h m₁ m₂ V ρ S := by
  unfold quadraticAction
  simp only [fun p => complexL_sqrt hh m₁ m₂ V (hρ p) (hS p) (hp p)]
  exact integral_densityL h m₁ m₂ V ρ S hρ hp hc hf

/-- Two positive charts have equal relative polar and quadratic actions even when the
individual background actions lack global spacetime integrability. -/
theorem relative_quadratic_eq {h : ℝ} (hh : h ≠ 0) (m₁ m₂ : ℝ) (V : Point → ℝ)
    {ρ₀ ρ₁ S₀ S₁ : Point → ℝ} (hr₀ : Differentiable ℝ ρ₀) (hr₁ : Differentiable ℝ ρ₁)
    (hs₀ : Differentiable ℝ S₀) (hs₁ : Differentiable ℝ S₁)
    (hp₀ : ∀ p, 0 < ρ₀ p) (hp₁ : ∀ p, 0 < ρ₁ p) :
    relative (complexL h m₁ m₂ V (wave h (fun p => Real.sqrt (ρ₀ p)) S₀))
        (complexL h m₁ m₂ V (wave h (fun p => Real.sqrt (ρ₁ p)) S₁)) =
      relative (densityL h m₁ m₂ V ρ₀ S₀) (densityL h m₁ m₂ V ρ₁ S₁) := by
  unfold relative
  exact integral_congr_ae (.of_forall fun p => congrArg₂ (· - ·)
    (complexL_sqrt hh m₁ m₂ V (hr₁ p) (hs₁ p) (hp₁ p))
    (complexL_sqrt hh m₁ m₂ V (hr₀ p) (hs₀ p) (hp₀ p)))

end FoliationQM.TwoBodyActions
