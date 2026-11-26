module
public import FoliationQM.ActionDensity
public import FoliationQM.PolarSpinorBilinears
public import FoliationQM.RotorEvolution
public import FoliationQM.LorentzConnectionCurvature
public import FoliationQM.SpecialLinearConnection

/-!
# The scalar action phase as a plane-rotor spin connection

For the irrotational sector of v13 `thm:dirac_lift`, the rotor of half-angle
−S/ℏ acts on the reference spinor by the scalar factor exp(iS/ℏ). Its body
Maurer–Cartan field has only the two antisymmetric spatial-plane entries.
With the source normalization −ℏω₁₂/2, the spin connection equals dS.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator Topology
namespace FoliationQM.ScalarPlanePhase
open DiracMatrices PlaneRotor RotorEvolution RotorExponential MaurerCartanDifferential
open CliffordCommutators LorentzCoefficientUniqueness LorentzConnectionCurvature

variable {E : Type*}

/-- The physical matrix rotor at the half-angle chosen for the scalar action phase. -/
def phaseRotor (p : MassiveParameters) (S : E → ℝ) (x : E) : Mat :=
  rotor (-(S x / p.hbar))

/-- The spatial-plane rotor in the two-by-two special-linear representation. -/
def planeMatrix (θ : ℝ) : SpinorMatrix.Mat2 :=
  (Real.cos θ : ℂ) • 1 + (Real.sin θ : ℂ) • !![-Complex.I, 0; 0, Complex.I]

/-- Each member of the scalar plane family has determinant one. -/
theorem det_planeMatrix (θ : ℝ) : (planeMatrix θ).det = 1 := by
  rw [Matrix.det_fin_two]
  simp [planeMatrix, -Complex.ofReal_sin, -Complex.ofReal_cos]
  have h : ((Real.cos θ : ℂ)^2 + (Real.sin θ : ℂ)^2) = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq θ
  linear_combination (norm := ring) h - (Real.sin θ : ℂ)^2 * Complex.I_mul_I

/-- The determinant-one matrix realizes precisely the original Dirac plane rotor. -/
theorem spin_planeMatrix (θ : ℝ) : SpecialLinearSpin.spin (planeMatrix θ) = rotor θ := by
  rw [rotor_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeMatrix, SpecialLinearSpin.spin, SpecialLinearSpin.weylDual,
      Matrix.diagonal, -Complex.ofReal_cos, -Complex.ofReal_sin] <;> ring

/-- The special-linear matrix varies smoothly with its real half-angle. -/
theorem contDiff_planeMatrix (n : WithTop ℕ∞) : ContDiff ℝ n planeMatrix := by
  have hc := (Complex.ofRealCLM.contDiff (n := n)).comp Real.contDiff_cos
  have hs := (Complex.ofRealCLM.contDiff (n := n)).comp Real.contDiff_sin
  exact (hc.smul contDiff_const).add (hs.smul contDiff_const)

/-- The amplitude times this rotor acting on the rest spinor is the scalar wave
embedded along that spinor. The chiral angle of this realization is zero. -/
theorem polarSpinor_eq_actionField (p : MassiveParameters) (ρ S : E → ℝ) (x : E) :
    PolarSpinorBilinears.polarSpinor (ρ x) 0 (phaseRotor p S x) =
      ActionDensity.actionField p ρ S x • restSpinor := by
  rw [PolarSpinorBilinears.polarSpinor, ChiralMatrix.chiral_zero, one_mul, phaseRotor,
    rotor_mulVec_restSpinor, smul_smul, ActionDensity.actionField, PolarDifferential.polarField, phase]
  rw [Complex.ofReal_neg]
  ring_nf

/-- Only the 12 and 21 entries of the plane-rotation coefficients are nonzero.
Their factor two converts the half-angle rate to the tetrad angle rate. -/
def planeCoefficients (rate : ℝ) (a b : Fin 4) : ℝ :=
  if a = 1 ∧ b = 2 then 2*rate else if a = 2 ∧ b = 1 then -(2*rate) else 0

/-- The plane coefficients are antisymmetric in the two Lorentz indices. -/
theorem planeCoefficients_antisymmetric (rate : ℝ) (a b : Fin 4) :
    planeCoefficients rate a b = -planeCoefficients rate b a := by
  fin_cases a <;> fin_cases b <;> simp [planeCoefficients]

/-- The physical ordered generator of the two plane entries is the half-angle
rate times the fixed Clifford matrix γ¹γ². -/
theorem generator_planeCoefficients (rate : ℝ) :
    generator (planeCoefficients rate) = (rate : ℂ) • planeGenerator := by
  simp [generator, planeCoefficients, Fin.sum_univ_succ, sigma_swap 1 2, sigma12_eq_I_smul_generator,
    smul_smul]
  rw [← neg_smul, ← add_smul, ← IsScalarTower.algebraMap_smul ℂ rate]
  rw [show algebraMap ℝ ℂ rate = (rate : ℂ) from rfl]
  congr 1
  linear_combination (norm := ring) -(rate : ℂ) * Complex.I_mul_I

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual coefficients from the action phase, in each spacetime direction. -/
def coefficients (p : MassiveParameters) (S : E → ℝ) (x v : E) : Fin 4 → Fin 4 → ℝ :=
  planeCoefficients (-(fderiv ℝ S x v / p.hbar))

/-- The inverse rotor times its actual derivative is its half-angle derivative
times the concrete spatial Clifford generator. -/
theorem body_phaseRotor (p : MassiveParameters) {S : E → ℝ} {x : E}
    (hS : DifferentiableAt ℝ S x) (v : E) :
    body (phaseRotor p S) x v = ((-(fderiv ℝ S x v / p.hbar) : ℝ) : ℂ) • planeGenerator := by
  let θ := fun y => -(S y / p.hbar)
  have hquot : DifferentiableAt ℝ (fun y => S y / p.hbar) x := by
    simpa only [div_eq_mul_inv, mul_comm] using hS.const_mul p.hbar⁻¹
  have hθ : DifferentiableAt ℝ θ x := hquot.neg
  have ht : fderiv ℝ θ x v = -(fderiv ℝ S x v / p.hbar) := by
    rw [show θ = -(fun y => S y / p.hbar) from rfl, fderiv_neg]
    exact congrArg Neg.neg (ActionDensity.fderiv_action_phase_apply p hS v)
  have hd := (hasDerivAt_rotor (θ x)).hasFDerivAt.comp x hθ.hasFDerivAt
  change (rotor (θ x))⁻¹ * fderiv ℝ (rotor ∘ θ) x v = _
  have hv : fderiv ℝ (rotor ∘ θ) x v = (fderiv ℝ θ x v) • (rotor (θ x) * planeGenerator) := by
    exact congrArg (fun L : E →L[ℝ] Mat => L v) hd.fderiv
  rw [hv]
  rw [ht, ← IsScalarTower.algebraMap_smul ℂ, mul_smul_comm, ← mul_assoc, rotor_inv_mul, one_mul]
  rfl

/-- The actual body has exactly the ordered Lorentz generator with these coefficients. -/
theorem body_eq_generator (p : MassiveParameters) {S : E → ℝ} {x : E}
    (hS : DifferentiableAt ℝ S x) (v : E) :
    body (phaseRotor p S) x v = generator (coefficients p S x v) := by
  rw [body_phaseRotor p hS, coefficients, generator_planeCoefficients]

/-- Any antisymmetric representation of the true body gives exactly the displayed coefficients. -/
theorem coefficients_unique (p : MassiveParameters) {S : E → ℝ} {x : E}
    (hS : DifferentiableAt ℝ S x) (v : E) (ω : Fin 4 → Fin 4 → ℝ)
    (hω : ∀ a b, ω a b = -ω b a) (he : body (phaseRotor p S) x v = generator ω) :
    ω = coefficients p S x v :=
  (generator_eq_iff hω (planeCoefficients_antisymmetric _)).mp (he.symm.trans (body_eq_generator p hS v))

/-- The existing coefficient extraction from the determinant-one rotor gives
the same plane entries, using actual two-by-two matrix derivatives. -/
theorem bodyOmega_planeMatrix (p : MassiveParameters) {S : E → ℝ} {x : E}
    (hS : DifferentiableAt ℝ S x) (v : E) :
    SpecialLinearConnection.bodyOmega (fun y => planeMatrix (-(S y / p.hbar))) x v = coefficients p S x v := by
  have hquot : DifferentiableAt ℝ (fun y => S y / p.hbar) x := by
    simpa only [div_eq_mul_inv, mul_comm] using hS.const_mul p.hbar⁻¹
  have hm := ((contDiff_planeMatrix 1).differentiable (by norm_num) _).comp x hquot.neg
  symm
  apply SpecialLinearConnection.body_generator_unique hm
    (Filter.Eventually.of_forall (fun y => det_planeMatrix (-(S y / p.hbar)))) v (planeCoefficients_antisymmetric _)
  simp only [Function.comp_def, Pi.neg_apply, spin_planeMatrix]
  exact body_eq_generator p hS v

/-- The physical scalar spin connection is exactly the positive action-phase differential. -/
theorem spinConnection_eq_fderiv (p : MassiveParameters) (S : E → ℝ) (x v : E) :
    spinConnection p.hbar (coefficients p S) x v = fderiv ℝ S x v := by
  simp only [spinConnection, coefficients, planeCoefficients, ↓reduceIte, and_self, mul_neg]
  field_simp [p.hbar_pos.ne']

/-- Direct extraction from the two-by-two matrix body gives the genuine phase differential. -/
theorem spinConnection_bodyOmega (p : MassiveParameters) {S : E → ℝ} {x : E}
    (hS : DifferentiableAt ℝ S x) (v : E) :
    spinConnection p.hbar (SpecialLinearConnection.bodyOmega (fun y => planeMatrix (-(S y / p.hbar)))) x v =
      fderiv ℝ S x v := by
  unfold spinConnection
  rw [bodyOmega_planeMatrix p hS v]
  exact spinConnection_eq_fderiv p S x v

/-- For a C² action phase its rotor spin connection has vanishing alternating derivative. -/
theorem spinConnection_closed (p : MassiveParameters) {S : E → ℝ} {x : E} (hS : ContDiffAt ℝ 2 S x) (v w : E) :
    let ω := SpecialLinearConnection.bodyOmega (fun y => planeMatrix (-(S y / p.hbar)))
    fderiv ℝ (fun y => spinConnection p.hbar ω y w) x v -
      fderiv ℝ (fun y => spinConnection p.hbar ω y v) x w = 0 := by
  dsimp only
  have he (a : E) :
      (fun y => spinConnection p.hbar (SpecialLinearConnection.bodyOmega (fun z => planeMatrix (-(S z / p.hbar)))) y a)
        =ᶠ[𝓝 x] (fun y => fderiv ℝ S y a) :=
    (hS.eventually (by norm_num)).mono (fun y hy => spinConnection_bodyOmega p (hy.differentiableAt (by norm_num)) a)
  have eval (a b : E) :
      fderiv ℝ (fun y => fderiv ℝ S y a) x b = fderiv ℝ (fderiv ℝ S) x b a := by
    have he := ((hS.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt.clm_apply (hasFDerivAt_const a x)
    rw [he.fderiv]
    simp
  rw [(he w).fderiv_eq, (he v).fderiv_eq, eval, eval, sub_eq_zero]
  exact hS.isSymmSndFDerivAt (by norm_num) _ _

end FoliationQM.ScalarPlanePhase
