module

public import FoliationQM.PlaneRotor
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Actual real derivatives of the Dirac plane-rotor evolution

Source: v13 `thm:contact_period` (iii), `eq:rotor_compton_evolution`,
and the plane-rotation case of `lem:maurer_cartan`. The angular parameter
of `PlaneRotor.rotor` is half the tetrad angle, so the evolution uses omega*t/2.
Real differentiation of the explicit sine and cosine matrix gives the source
ODE, for any initial complex matrix and any real angular rate.

All matrix calculus in this module uses Mathlib's genuine L-infinity operator
normed-algebra structure, activated by `Matrix.Norms.Operator`. Dependent
calculus modules must activate the same scope. Matrix exponentiation and ODE
uniqueness are proved separately; no derivative identity is assumed here.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator

namespace FoliationQM.RotorEvolution
open DiracMatrices PlaneRotor

/-- The actual matrix evolution from an arbitrary initial matrix at fixed tetrad angular rate. -/
def evolution (L0 : Mat) (omega t : ℝ) : Mat := L0 * rotor (omega * t / 2)

/-- The explicit plane rotor commutes with its fixed Clifford generator. -/
theorem rotor_generator_commute (theta : ℝ) : Commute (rotor theta) planeGenerator := by
  change rotor theta * planeGenerator = planeGenerator * rotor theta
  simp [rotor, add_mul, mul_add]

/-- Actual real differentiation of the sine-cosine rotor gives right multiplication by its generator. -/
theorem hasDerivAt_rotor (theta : ℝ) :
    HasDerivAt rotor (rotor theta * planeGenerator) theta := by
  have hc := (Real.hasDerivAt_cos theta).ofReal_comp.smul_const (1 : Mat)
  have hs := (Real.hasDerivAt_sin theta).ofReal_comp.smul_const planeGenerator
  have hd : HasDerivAt rotor
      ((-(Real.sin theta : ℂ)) • (1 : Mat) + (Real.cos theta : ℂ) • planeGenerator) theta := by
    simpa only [rotor, Complex.ofReal_neg] using! hc.add hs
  convert hd using 1
  simp [rotor, add_mul, generator_sq]
  module

/-- Mathlib's actual real derivative of the rotor equals its generator product. -/
theorem deriv_rotor (theta : ℝ) : deriv rotor theta = rotor theta * planeGenerator :=
  (hasDerivAt_rotor theta).deriv

/-- The explicit rotor is differentiable over real half-angles everywhere. -/
theorem differentiable_rotor : Differentiable ℝ rotor :=
  fun theta => (hasDerivAt_rotor theta).differentiableAt

/-- The explicit plane rotor is smooth in its real half-angle to every differentiability order. -/
theorem contDiff_rotor (n : WithTop ℕ∞) : ContDiff ℝ n rotor := by
  have hc : ContDiff ℝ n (fun theta : ℝ => (Real.cos theta : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp Real.contDiff_cos
  have hs : ContDiff ℝ n (fun theta : ℝ => (Real.sin theta : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp Real.contDiff_sin
  exact (hc.smul contDiff_const).add (hs.smul contDiff_const)

/-- The half-angle reparametrization has the actual chain-rule derivative omega/2 times the rotor generator product. -/
theorem hasDerivAt_scaled_rotor (omega t : ℝ) :
    HasDerivAt (fun s : ℝ => rotor (omega * s / 2))
      (((omega / 2 : ℝ) : ℂ) • (rotor (omega * t / 2) * planeGenerator)) t := by
  have hangle : HasDerivAt (fun s : ℝ => omega * s / 2) (omega / 2) t := by
    simpa using ((hasDerivAt_id t).const_mul omega).div_const 2
  have hr := (hasDerivAt_rotor (omega * t / 2)).scomp t hangle
  rw [← IsScalarTower.algebraMap_smul ℂ (omega / 2)
    (rotor (omega * t / 2) * planeGenerator)] at hr
  simpa only [Function.comp_def] using! hr

/-- The actual evolved matrix derivative satisfies the source generator-form ODE. -/
theorem hasDerivAt_evolution (L0 : Mat) (omega t : ℝ) :
    HasDerivAt (evolution L0 omega)
      (((omega / 2 : ℝ) : ℂ) • (evolution L0 omega t * planeGenerator)) t := by
  have h := (hasDerivAt_scaled_rotor omega t).const_mul L0
  simpa only [evolution, mul_smul_comm, mul_assoc] using! h

/-- Mathlib's actual derivative of the evolution is the source generator product with half angular rate. -/
theorem deriv_evolution (L0 : Mat) (omega t : ℝ) :
    deriv (evolution L0 omega) t =
      (((omega / 2 : ℝ) : ℂ) • (evolution L0 omega t * planeGenerator)) :=
  (hasDerivAt_evolution L0 omega t).deriv

/-- Every arbitrary-initial-matrix rotor evolution is real differentiable at every time. -/
theorem differentiable_evolution (L0 : Mat) (omega : ℝ) :
    Differentiable ℝ (evolution L0 omega) :=
  fun t => (hasDerivAt_evolution L0 omega t).differentiableAt

/-- The explicit evolution is smooth in real time for any initial matrix and real angular rate. -/
theorem contDiff_evolution (L0 : Mat) (omega : ℝ) (n : WithTop ℕ∞) :
    ContDiff ℝ n (evolution L0 omega) := by
  have hangle : ContDiff ℝ n (fun t : ℝ => omega * t / 2) :=
    (contDiff_const.mul contDiff_id).div_const 2
  exact contDiff_const.mul ((contDiff_rotor n).comp hangle)

/-- The evolved matrix equals its supplied initial matrix at time zero. -/
theorem initial_evolution (L0 : Mat) (omega : ℝ) : evolution L0 omega 0 = L0 := by
  simp [evolution]

/-- The generator ODE coefficient agrees exactly with the source negative-i sigma12 convention. -/
theorem generator_rhs_eq_sigma_rhs (L : Mat) (omega : ℝ) :
    (((omega / 2 : ℝ) : ℂ) • (L * planeGenerator)) =
      (-Complex.I * (omega : ℂ) / 2) • (L * sigma 1 2) := by
  rw [← neg_I_smul_sigma12, mul_smul_comm, smul_smul]
  congr 1
  push_cast
  ring

/-- The actual evolved derivative satisfies the source ODE dL/dt = -(i/2) omega L sigma12. -/
theorem hasDerivAt_evolution_sigma (L0 : Mat) (omega t : ℝ) :
    HasDerivAt (evolution L0 omega)
      ((-Complex.I * (omega : ℂ) / 2) • (evolution L0 omega t * sigma 1 2)) t := by
  simpa only [generator_rhs_eq_sigma_rhs] using hasDerivAt_evolution L0 omega t

/-- Mathlib's actual derivative satisfies the source negative-i sigma12 equation. -/
theorem deriv_evolution_sigma (L0 : Mat) (omega t : ℝ) :
    deriv (evolution L0 omega) t =
      (-Complex.I * (omega : ℂ) / 2) • (evolution L0 omega t * sigma 1 2) :=
  (hasDerivAt_evolution_sigma L0 omega t).deriv

/-- Zero tetrad angular rate leaves every initial matrix constant. -/
theorem evolution_zero_rate (L0 : Mat) (t : ℝ) : evolution L0 0 t = L0 := by
  simp [evolution]

/-- The actual evolution preserves matrix invertibility when the initial matrix is a unit. -/
theorem evolution_isUnit {L0 : Mat} (hL0 : IsUnit L0) (omega t : ℝ) :
    IsUnit (evolution L0 omega t) :=
  hL0.mul (rotor_isUnit (omega * t / 2))

end FoliationQM.RotorEvolution
