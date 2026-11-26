module

public import FoliationQM.LatticeSchrodingerResidual
public import FoliationQM.LatticeRegularizedFlow

/-!
# Reconstructing the complex lattice equation from signed polar curves

The physical lag phase in v13 lines 203–229 gives the complex Neumann
Schrödinger velocity along each solution of the unregularized polar equations
at nonzero amplitude. For nonzero regularization width the reconstructed
velocity also includes the explicit site residual, including at nodes.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LatticeSchrodingerReconstruction

open LatticeComplexEnergy LatticeConservation LatticeLagHamiltonian
open LatticeClockRegularization LatticeSchrodingerResidual LatticeRegularizedFlow

/-- Complex tangent for signed amplitude and physical lag velocities at one site. -/
def lagTangent (p : MassiveParameters) (r φ dR dτ : ℝ) : ℂ :=
  phase φ * ((dR : ℂ) + Complex.I * ((r * (p.c / p.ellC) * dτ : ℝ) : ℂ))

/-- The amplitude and lag velocities are uniquely recoverable from their complex
tangent when the signed amplitude at the site is nonzero. -/
theorem tangent_injective (p : MassiveParameters) (r φ : ℝ) (hr : r ≠ 0)
    {a b c d : ℝ} (ht : lagTangent p r φ a b = lagTangent p r φ c d) : a = c ∧ b = d := by
  have hphase : phase φ ≠ 0 := Complex.exp_ne_zero _
  have hz := mul_left_cancel₀ hphase ht
  have ha := congrArg Complex.re hz
  have hb := congrArg Complex.im hz
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero, add_zero] at ha
  simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, one_mul, zero_add] at hb
  exact ⟨ha, mul_left_cancel₀ (mul_ne_zero hr (div_ne_zero p.c_pos.ne' (ClockScales.ellC_pos p).ne')) hb⟩

/-- Differential of the actual signed wave along an arbitrary amplitude and lag path. -/
theorem wave_lag_path {n : ℕ} (p : MassiveParameters) (R τ : ℝ → Fin n → ℝ) (t : ℝ) (i : Fin n)
    {dR dτ : ℝ} (hR : HasDerivAt (fun s => R s i) dR t)
    (hτ : HasDerivAt (fun s => τ s i) dτ t) :
    HasDerivAt (fun s => wave (R s) (lagPhase p (τ s)) i)
      (lagTangent p (R t i) (lagPhase p (τ t) i) dR dτ) t := by
  simpa only [lagTangent, mul_assoc] using LatticePolarVariation.wave_path R
    (fun s => lagPhase p (τ s)) t i hR (hτ.const_mul (p.c / p.ellC))

/-- Along a polar solution the complex derivative is the linear Schrödinger
velocity plus the computed defect whenever the source denominator is nonzero. -/
theorem wave_site_with_residual {n : ℕ} (p : MassiveParameters) (h ε : ℝ)
    (R τ : ℝ → Fin n → ℝ) (V : Fin n → ℝ) (t : ℝ) (i : Fin n) (hn : R t i ≠ 0 ∨ ε ≠ 0)
    (hR : HasDerivAt (fun s => R s i) (sourceAmplitudeRHS p.ellC p.c h (R t) (lagPhase p (τ t)) i) t)
    (hτ : HasDerivAt (fun s => τ s i) (lagRate p h ε (R t) (lagPhase p (τ t)) V i) t) :
    HasDerivAt (fun s => wave (R s) (lagPhase p (τ s)) i)
      (schrodinger p h V (wave (R t) (lagPhase p (τ t))) i +
        residual p h ε (R t) (lagPhase p (τ t)) i) t :=
  (wave_lag_path p R τ t i hR hτ).congr_deriv (velocity_split p h ε (R t) (lagPhase p (τ t)) V i hn)

/-- Every regularized integral curve with nonzero denominator at each site
reconstructs a differentiable complex profile with the calculated residual. -/
theorem wave_path_with_residual {n : ℕ} (p : MassiveParameters) (h ε : ℝ) (V : Fin n → ℝ)
    (γ : ℝ → State n) (t : ℝ) (hn : ∀ i, (γ t).1 i ≠ 0 ∨ ε ≠ 0)
    (hγ : HasDerivAt γ (field p h ε V (γ t)) t) :
    HasDerivAt (fun s => wave (γ s).1 (lagPhase p (γ s).2))
      (schrodinger p h V (wave (γ t).1 (lagPhase p (γ t).2)) +
        residual p h ε (γ t).1 (lagPhase p (γ t).2)) t := by
  obtain ⟨hR, hτ⟩ := component_rates p h ε V γ t hγ
  exact hasDerivAt_pi.mpr fun i => wave_site_with_residual p h ε (fun s => (γ s).1)
    (fun s => (γ s).2) V t i (hn i) (hR i) (hτ i)

/-- At zero width the complex wave satisfies the exact site equation wherever
the signed amplitude is nonzero. -/
theorem wave_site_exact {n : ℕ} (p : MassiveParameters) (h : ℝ) (R τ : ℝ → Fin n → ℝ)
    (V : Fin n → ℝ) (t : ℝ) (i : Fin n) (hi : R t i ≠ 0)
    (hR : HasDerivAt (fun s => R s i) (sourceAmplitudeRHS p.ellC p.c h (R t) (lagPhase p (τ t)) i) t)
    (hτ : HasDerivAt (fun s => τ s i) (lagRate p h 0 (R t) (lagPhase p (τ t)) V i) t) :
    HasDerivAt (fun s => wave (R s) (lagPhase p (τ s)) i)
      (schrodinger p h V (wave (R t) (lagPhase p (τ t))) i) t := by
  simpa only [residual_zero_width, add_zero] using
    wave_site_with_residual p h 0 R τ V t i (Or.inl hi) hR hτ

/-- On a nonzero signed chart the exact complex site equation is equivalent
to both of the unregularized polar site equations for the actual curve. -/
theorem site_iff {n : ℕ} (p : MassiveParameters) (h : ℝ) (R τ : ℝ → Fin n → ℝ)
    (V : Fin n → ℝ) (t : ℝ) (i : Fin n) (hi : R t i ≠ 0)
    (hR : DifferentiableAt ℝ (fun s => R s i) t) (hτ : DifferentiableAt ℝ (fun s => τ s i) t) :
    HasDerivAt (fun s => wave (R s) (lagPhase p (τ s)) i)
        (schrodinger p h V (wave (R t) (lagPhase p (τ t))) i) t ↔
      HasDerivAt (fun s => R s i) (sourceAmplitudeRHS p.ellC p.c h (R t) (lagPhase p (τ t)) i) t ∧
      HasDerivAt (fun s => τ s i) (lagRate p h 0 (R t) (lagPhase p (τ t)) V i) t := by
  constructor
  · intro hz
    have hactual := wave_lag_path p R τ t i hR.hasDerivAt hτ.hasDerivAt
    have hsource := velocity_split p h 0 (R t) (lagPhase p (τ t)) V i (Or.inl hi)
    rw [residual_zero_width, add_zero] at hsource
    have rates := tangent_injective p (R t i) (lagPhase p (τ t) i) hi
      ((hactual.unique hz).trans hsource.symm)
    exact ⟨hR.hasDerivAt.congr_deriv rates.1, hτ.hasDerivAt.congr_deriv rates.2⟩
  · rintro ⟨ha, hb⟩
    exact wave_site_exact p h R τ V t i hi ha hb

end FoliationQM.LatticeSchrodingerReconstruction
