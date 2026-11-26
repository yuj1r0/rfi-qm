module

public import FoliationQM.ReducedMassShellFrequency
public import FoliationQM.MassShellFourier
public import FoliationQM.RestEnvelopeRemainder

/-!
# Actual plane waves after removing the rest frequency

Source: v13 `cor:schrodinger`, component kinds C and D. The zeroth
coordinate is physical time. A single exponential with arbitrary real
frequency supplies genuine derivatives, the actual mass-shell envelope,
and the finite-speed Schrödinger residual.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.ReducedPlaneWave

open LorentzCoordinates PolarSecondDifferential ReducedMassShellFrequency
open RestEnvelopeKG RestEnvelopeRemainder LaboratoryKG
open Madelung (coordinateVector)
open scoped ContDiff

/-- The actual angular plane wave at real temporal frequency w in physical time. -/
def mode (w : ℝ) (k : Spatial) (x : Covector) : ℂ :=
  Complex.exp (Complex.I * (spatialDot k (fun i => x i.succ) - w * x 0 : ℝ))

/-- Every real-frequency plane mode is jointly smooth on spacetime. -/
theorem contDiff_mode (w : ℝ) (k : Spatial) : ContDiff ℝ ∞ (mode w k) := by
  have hθ : ContDiff ℝ ∞ (fun x : Covector =>
      spatialDot k (fun i => x i.succ) - w * x 0) := by
    unfold spatialDot
    fun_prop
  exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hθ)).cexp

/-- A real-frequency plane mode has unit modulus everywhere. -/
theorem norm_mode (w : ℝ) (k : Spatial) (x : Covector) : ‖mode w k x‖ = 1 := by
  rw [mode, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I]

/-- The true derivative in any constant direction has its actual linear phase multiplier. -/
theorem directional_mode (w : ℝ) (k : Spatial) (x v : Covector) :
    directionalDerivative (mode w k) v x =
      Complex.I * (spatialDot k (fun i => v i.succ) - w * v 0 : ℝ) * mode w k x := by
  have hθ : HasFDerivAt (fun y : Covector =>
      spatialDot k (fun i => y i.succ) - w * y 0)
      (k 0 • (ContinuousLinearMap.proj (1 : Fin 4) : Covector →L[ℝ] ℝ) +
        k 1 • ContinuousLinearMap.proj (2 : Fin 4) +
        k 2 • ContinuousLinearMap.proj (3 : Fin 4) -
        w • ContinuousLinearMap.proj (0 : Fin 4)) x :=
    (((hasFDerivAt_apply 1 x).const_mul (k 0)).add
      ((hasFDerivAt_apply 2 x).const_mul (k 1))).add
      ((hasFDerivAt_apply 3 x).const_mul (k 2)) |>.sub
      ((hasFDerivAt_apply 0 x).const_mul w)
  have he := ((Complex.ofRealCLM.hasFDerivAt.comp x hθ).const_mul Complex.I).cexp
  change HasFDerivAt (mode w k) _ x at he
  change fderiv ℝ (mode w k) x v = _
  rw [he.fderiv]
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    add_apply, sub_apply, smul_apply, Complex.ofRealCLM_apply, smul_eq_mul,
    mode, spatialDot]
  push_cast
  ring

/-- Differentiating the first derivative as a function gives the true second directional derivative. -/
theorem second_directional_mode (w : ℝ) (k : Spatial) (x v : Covector) :
    secondDirectionalDerivative (mode w k) v x =
      -((spatialDot k (fun i => v i.succ) - w * v 0 : ℝ) : ℂ) ^ 2 * mode w k x := by
  let a : ℂ := Complex.I * (spatialDot k (fun i => v i.succ) - w * v 0 : ℝ)
  have heq : directionalDerivative (mode w k) v = fun y => a * mode w k y :=
    funext fun y => directional_mode w k y v
  have hd := ((contDiff_mode w k).differentiable (by simp) x).hasFDerivAt.const_mul a
  change (fderiv ℝ (directionalDerivative (mode w k) v) x) v = _
  rw [heq, hd.fderiv]
  simp only [smul_apply, smul_eq_mul]
  change a * directionalDerivative (mode w k) v x = _
  rw [directional_mode]
  dsimp [a]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- The rest envelope of the original normal-coordinate mass-shell mode is this same reduced plane wave. -/
theorem envelope_mode (p : MassiveParameters) (k : Spatial) :
    envelope p (MassShellFourier.mode (p.m * p.c / p.hbar) k) =
      mode (reducedFrequency p k) k := by
  funext x
  simp only [envelope, RestEnvelopeDifferential.carrierField,
    RestPhaseDerivatives.carrier, phase, LaboratoryCoordinates.pullback,
    MassShellFourier.mode, mode]
  rw [← Complex.exp_neg, ← Complex.exp_add]
  congr 1
  simp [LaboratoryCoordinates.toNormal_apply, reducedFrequency]
  ring

/-- Actual time and spatial derivatives give the physical Schrödinger multiplier for any real frequency. -/
theorem residual_mode (p : MassiveParameters) (w : ℝ) (k : Spatial) (x : Covector) :
    schrodingerResidual p (mode w k) x =
      (p.hbar : ℂ) * ((w - schrodingerFrequency p k : ℝ) : ℂ) * mode w k x := by
  simp only [schrodingerResidual, directional_mode, spatialLaplacian,
    second_directional_mode, Fin.sum_univ_three]
  simp only [spatialDot, coordinateVector, Pi.single_apply, Fin.succ]
  norm_num
  simp only [schrodingerFrequency, speedSq, spatialDot]
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- The actual reduced mode retains its temporal remainder and quantified residual; the limiting-frequency mode solves the Schrödinger equation. -/
theorem physical_residuals (p : MassiveParameters) (k : Spatial) (x : Covector) :
    schrodingerResidual p (mode (reducedFrequency p k) k) x =
        (temporalCoefficient p : ℂ) *
          secondDirectionalDerivative (mode (reducedFrequency p k) k) (coordinateVector 0) x ∧
      schrodingerResidual p (mode (schrodingerFrequency p k) k) x = 0 ∧
      ‖schrodingerResidual p (mode (reducedFrequency p k) k) x‖ =
        p.hbar * (schrodingerFrequency p k - reducedFrequency p k) ∧
      ‖schrodingerResidual p (mode (reducedFrequency p k) k) x‖ ≤
        p.hbar ^ 4 * (speedSq k) ^ 2 / (8 * p.m ^ 3 * p.c ^ 2) := by
  have hc := frequency_comparison p k
  have hn : ‖schrodingerResidual p (mode (reducedFrequency p k) k) x‖ =
      p.hbar * (schrodingerFrequency p k - reducedFrequency p k) := by
    simp only [residual_mode, norm_mul, norm_mode, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
    rw [abs_of_pos p.hbar_pos, abs_of_nonpos (sub_nonpos.mpr hc.2.1)]
    ring
  have ht : secondDirectionalDerivative (mode (reducedFrequency p k) k)
      (coordinateVector 0) x =
      -(reducedFrequency p k : ℂ) ^ 2 * mode (reducedFrequency p k) k x := by
    simpa [coordinateVector, spatialDot] using
      second_directional_mode (reducedFrequency p k) k x (coordinateVector 0)
  have hg := congrArg (fun r : ℝ => (r : ℂ)) (gap_identity p k)
  push_cast at hg
  refine ⟨?_, ?_, hn, ?_⟩
  · rw [residual_mode, ht]
    simp only [temporalCoefficient]
    push_cast
    calc
      _ = -(p.hbar : ℂ) *
          ((schrodingerFrequency p k : ℂ) - (reducedFrequency p k : ℂ)) *
            mode (reducedFrequency p k) k x := by ring
      _ = _ := by rw [hg]; ring
  · simp only [residual_mode, sub_self, Complex.ofReal_zero, mul_zero, zero_mul]
  · rw [hn]
    calc
      _ ≤ p.hbar * (p.hbar ^ 3 * (speedSq k) ^ 2 /
          (8 * p.m ^ 3 * p.c ^ 2)) :=
        mul_le_mul_of_nonneg_left hc.2.2 p.hbar_pos.le
      _ = _ := by ring

end FoliationQM.ReducedPlaneWave
