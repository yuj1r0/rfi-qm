module

public import FoliationQM.GeneralCouplingStationarity

/-!
# A nonconstant positive-density general-coupling solution

Source: v13 `eq:nonlinear_defect`. A real spatial exponential supplies an
actual smooth nonconstant solution of the generalized real equations for
positive coupling. It also distinguishes the nonlinear equation from the
physical-clock linear KG equation away from the canonical coupling.
-/
@[expose] public section

namespace FoliationQM.GeneralCouplingExample

open PolarSecondDifferential PolarRegularity
open scoped ContDiff

/-- Spatial exponential rate selected by the positive coupling. -/
noncomputable def rate (p : MassiveParameters) (lam : ℝ) : ℝ :=
  p.m * p.c / (2 * Real.sqrt lam)

/-- A strictly positive spatial amplitude with nonzero curvature. -/
noncomputable def amplitude (p : MassiveParameters) (lam : ℝ) (x : Covector) : ℝ :=
  Real.exp (rate p lam * x 1)

/-- The density is the square of the exponential amplitude. -/
noncomputable def density (p : MassiveParameters) (lam : ℝ) (x : Covector) : ℝ :=
  amplitude p lam x ^ 2

/-- The rate is strictly positive for the supplied massive parameters. -/
theorem rate_pos (p : MassiveParameters) {lam : ℝ} (hlam : 0 < lam) :
    0 < rate p lam := by
  unfold rate
  exact div_pos (mul_pos p.m_pos p.c_pos) (mul_pos (by norm_num) (Real.sqrt_pos.2 hlam))

/-- This rate solves the generalized zero-phase mass-shell relation. -/
theorem four_mul_rate_sq (p : MassiveParameters) {lam : ℝ} (hlam : 0 < lam) :
    4 * lam * rate p lam ^ 2 = p.m ^ 2 * p.c ^ 2 := by
  have hs : Real.sqrt lam ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hlam)
  unfold rate
  field_simp
  rw [Real.sq_sqrt hlam.le]
  ring

/-- The amplitude is smooth to every order. -/
theorem contDiff_amplitude (p : MassiveParameters) (lam : ℝ) (n : WithTop ℕ∞) :
    ContDiff ℝ n (amplitude p lam) :=
  (contDiff_const.mul (contDiff_apply ℝ (fun _ : Fin 4 => ℝ) 1)).exp

/-- Exponential amplitude never vanishes. -/
theorem amplitude_pos (p : MassiveParameters) (lam : ℝ) (x : Covector) :
    0 < amplitude p lam x := Real.exp_pos _

/-- The density is smooth to every order. -/
theorem contDiff_density (p : MassiveParameters) (lam : ℝ) (n : WithTop ℕ∞) :
    ContDiff ℝ n (density p lam) := (contDiff_amplitude p lam n).pow 2

/-- The density defines a positive chart on all spacetime. -/
theorem density_pos (p : MassiveParameters) (lam : ℝ) (x : Covector) :
    0 < density p lam x := sq_pos_of_pos (amplitude_pos p lam x)

/-- The positive square-root density is the actual exponential amplitude. -/
theorem sqrt_density (p : MassiveParameters) (lam : ℝ) (x : Covector) :
    Real.sqrt (density p lam x) = amplitude p lam x :=
  Real.sqrt_sq (le_of_lt (amplitude_pos p lam x))

/-- Actual first derivative along any constant spacetime vector. -/
theorem directionalDerivative_amplitude (p : MassiveParameters) (lam : ℝ)
    (x v : Covector) :
    directionalDerivative (amplitude p lam) v x =
      amplitude p lam x * (rate p lam * v 1) := by
  have hd : HasFDerivAt (amplitude p lam) _ x :=
    ((hasFDerivAt_apply 1 x).const_mul (rate p lam)).exp
  rw [directionalDerivative, hd.fderiv]
  simp only [smul_apply, smul_eq_mul, ContinuousLinearMap.proj_apply, amplitude]

/-- A nonzero spatial first derivative certifies the amplitude is not locally constant. -/
theorem directionalDerivative_amplitude_ne_zero (p : MassiveParameters) {lam : ℝ}
    (hlam : 0 < lam) (x : Covector) :
    directionalDerivative (amplitude p lam) (Madelung.coordinateVector 1) x ≠ 0 := by
  rw [directionalDerivative_amplitude]
  norm_num [Madelung.coordinateVector, Pi.single_apply]
  exact ⟨ne_of_gt (amplitude_pos p lam x), ne_of_gt (rate_pos p hlam)⟩

/-- Actual repeated derivative, rather than an independent second-jet input. -/
theorem secondDirectionalDerivative_amplitude (p : MassiveParameters) (lam : ℝ)
    (x v : Covector) :
    secondDirectionalDerivative (amplitude p lam) v x =
      amplitude p lam x * (rate p lam * v 1) ^ 2 := by
  have heq : directionalDerivative (amplitude p lam) v =
      fun y => amplitude p lam y * (rate p lam * v 1) :=
    funext (fun y => directionalDerivative_amplitude p lam y v)
  have hd := (((contDiff_amplitude p lam 1).differentiable (by norm_num) x).hasFDerivAt).mul_const
    (rate p lam * v 1)
  rw [secondDirectionalDerivative, heq, directionalDerivative, hd.fderiv]
  simp only [smul_apply, smul_eq_mul]
  change (rate p lam * v 1) * directionalDerivative (amplitude p lam) v x = _
  rw [directionalDerivative_amplitude]
  ring

/-- The spacelike exponential has strictly negative wave-operator curvature. -/
theorem box_amplitude (p : MassiveParameters) (lam : ℝ) (x : Covector) :
    box (amplitude p lam) Madelung.coordinateVector x =
      -(rate p lam ^ 2) * amplitude p lam x := by
  simp only [box, secondDirectionalDerivative_amplitude]
  norm_num [Madelung.coordinateVector, Pi.single_apply]
  ring

/-- Actual generalized Hamilton-Jacobi and continuity equations for the
positive exponential density with zero phase. -/
theorem generalized_madelung (p : MassiveParameters) {lam : ℝ} (hlam : 0 < lam)
    (x : Covector) :
    minkowski
      (fun i => directionalDerivative (fun _ : Covector => (0 : ℝ))
        (Madelung.coordinateVector i) x)
      (fun i => directionalDerivative (fun _ : Covector => (0 : ℝ))
        (Madelung.coordinateVector i) x) =
      p.m ^ 2 * p.c ^ 2 + 4 * lam *
        box (fun y => Real.sqrt (density p lam y)) Madelung.coordinateVector x /
          Real.sqrt (density p lam x) ∧
    densityCurrentDivergence (density p lam) (fun _ => 0) Madelung.coordinateVector x = 0 := by
  have heq : (fun y => Real.sqrt (density p lam y)) = amplitude p lam :=
    funext (sqrt_density p lam)
  rw [heq, box_amplitude, sqrt_density]
  constructor
  · have ha : amplitude p lam x ≠ 0 := ne_of_gt (amplitude_pos p lam x)
    simp only [directionalDerivative, fderiv_fun_const, Pi.zero_apply, zero_apply,
      minkowski, mul_zero, sub_self]
    field_simp
    nlinarith [four_mul_rate_sq p hlam]
  · have hc (i : Fin 4) : densityCurrent (density p lam) (fun _ => 0)
        Madelung.coordinateVector i = (fun _ => 0) := by
      funext y
      simp [densityCurrent, directionalDerivative]
    simp only [densityCurrentDivergence, hc, directionalDerivative, fderiv_fun_const,
      Pi.zero_apply, zero_apply, sub_self]

/-- The nonconstant density is stationary for the actual general-coupling
relative source action on every open subset, without a finite-action premise. -/
theorem relativeStationaryOn (p : MassiveParameters) {lam : ℝ} (hlam : 0 < lam)
    {U : Set Covector} (hU : IsOpen U) :
    GeneralCouplingStationarity.RelativeStationaryOn p lam (density p lam) (fun _ => 0)
      Madelung.coordinateVector U := by
  apply (GeneralCouplingStationarity.relativeStationaryOn_iff_madelung p lam hlam hU
    (fun _ _ => (contDiff_density p lam ∞).contDiffAt) (fun _ _ => contDiffAt_const)
    (fun x _ => density_pos p lam x) Madelung.coordinateVector).mpr
  intro x _
  obtain ⟨hHJ, hcont⟩ := generalized_madelung p hlam x
  exact ⟨by linarith, hcont⟩

/-- For this nonconstant solution the physical-clock linear KG equation
holds at a point exactly at the canonical coupling. -/
theorem physical_kg_iff_canonical (p : MassiveParameters) {lam : ℝ} (hlam : 0 < lam)
    (x : Covector) :
    box (ActionDensity.actionField p (density p lam) (fun _ => 0))
        Madelung.coordinateVector x +
      (((p.m ^ 2 * p.c ^ 2 / p.hbar ^ 2 : ℝ) : ℂ) *
        ActionDensity.actionField p (density p lam) (fun _ => 0) x) = 0 ↔
      lam = p.hbar ^ 2 / 4 := by
  rw [kg_eq_zero_iff_madelung_density p
    (contDiff_density p lam 2).contDiffAt contDiffAt_const (density_pos p lam x)]
  have heq : (fun y => Real.sqrt (density p lam y)) = amplitude p lam :=
    funext (sqrt_density p lam)
  have hratio : box (fun y => Real.sqrt (density p lam y)) Madelung.coordinateVector x /
      Real.sqrt (density p lam x) = -(rate p lam ^ 2) := by
    rw [heq, box_amplitude, sqrt_density]
    exact mul_div_cancel_right₀ _ (ne_of_gt (amplitude_pos p lam x))
  rw [mul_div_assoc, hratio]
  have hcont := (generalized_madelung p hlam x).2
  simp only [hcont, and_true, directionalDerivative, fderiv_fun_const, Pi.zero_apply,
    zero_apply, minkowski, mul_zero, sub_self]
  have hscale := four_mul_rate_sq p hlam
  have hk : rate p lam ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt (rate_pos p hlam))
  constructor
  · intro h
    have hc : (4 * lam) * rate p lam ^ 2 = p.hbar ^ 2 * rate p lam ^ 2 := by
      rw [hscale]
      nlinarith
    have hc' := mul_right_cancel₀ hk hc
    linarith
  · intro h
    rw [h] at hscale ⊢
    nlinarith

/-- Away from the canonical coupling the actual physical KG residual is
nonzero at every point, so the nonlinear family is not a vacuous reformulation. -/
theorem physical_kg_ne_zero (p : MassiveParameters) {lam : ℝ} (hlam : 0 < lam)
    (hneq : lam ≠ p.hbar ^ 2 / 4) (x : Covector) :
    box (ActionDensity.actionField p (density p lam) (fun _ => 0))
        Madelung.coordinateVector x +
      (((p.m ^ 2 * p.c ^ 2 / p.hbar ^ 2 : ℝ) : ℂ) *
        ActionDensity.actionField p (density p lam) (fun _ => 0) x) ≠ 0 :=
  mt (physical_kg_iff_canonical p hlam x).mp hneq

/-- The literal modulus defect is nonzero everywhere for each noncanonical
positive coupling; the supplied density is smooth and strictly positive. -/
theorem nonlinearModulusDefect_ne_zero (p : MassiveParameters) {lam : ℝ} (hlam : 0 < lam)
    (hneq : lam ≠ p.hbar ^ 2 / 4) (x : Covector) :
    (((1 - 4 * lam / p.hbar ^ 2) *
      box (fun y => ‖ActionDensity.actionField p (density p lam) (fun _ => 0) y‖)
        Madelung.coordinateVector x /
      ‖ActionDensity.actionField p (density p lam) (fun _ => 0) x‖ : ℝ) : ℂ) *
      ActionDensity.actionField p (density p lam) (fun _ => 0) x ≠ 0 := by
  obtain ⟨hHJ, hcont⟩ := generalized_madelung p hlam x
  have hHJ' : minkowski
      (fun i => directionalDerivative (fun _ : Covector => (0 : ℝ))
        (Madelung.coordinateVector i) x)
      (fun i => directionalDerivative (fun _ : Covector => (0 : ℝ))
        (Madelung.coordinateVector i) x) - p.m ^ 2 * p.c ^ 2 =
      4 * lam * box (fun y => Real.sqrt (density p lam y)) Madelung.coordinateVector x /
        Real.sqrt (density p lam x) := by linarith
  have heq := kg_eq_nonlinearModulusDefect_density p lam
    (contDiff_density p lam 2).contDiffAt contDiffAt_const
    (density_pos p lam x) Madelung.coordinateVector hHJ' hcont
  rw [← heq]
  exact physical_kg_ne_zero p hlam hneq x

/-- Universal physical-clock linearization of all smooth positive stationary
fields selects exactly the canonical coupling. The converse uses the concrete
nonconstant exponential, rather than assuming every individual field detects λ. -/
theorem every_stationary_field_linear_iff_canonical (p : MassiveParameters)
    {lam : ℝ} (hlam : 0 < lam) :
    (∀ ρ S : Covector → ℝ, ContDiff ℝ ∞ ρ → ContDiff ℝ ∞ S →
      (∀ x, 0 < ρ x) →
      GeneralCouplingStationarity.RelativeStationaryOn p lam ρ S
        Madelung.coordinateVector Set.univ →
      ∀ x, box (ActionDensity.actionField p ρ S) Madelung.coordinateVector x +
        (((p.m ^ 2 * p.c ^ 2 / p.hbar ^ 2 : ℝ) : ℂ) *
          ActionDensity.actionField p ρ S x) = 0) ↔
      lam = p.hbar ^ 2 / 4 := by
  constructor
  · intro h
    have hk := h (density p lam) (fun _ => 0) (contDiff_density p lam ∞)
      contDiff_const (density_pos p lam) (relativeStationaryOn p hlam isOpen_univ) 0
    exact (physical_kg_iff_canonical p hlam 0).mp hk
  · intro h ρ S hρ hS hpos hstationary x
    rw [h] at hstationary
    exact (GeneralCouplingStationarity.relativeStationaryOn_canonical_iff_kleinGordon p
      isOpen_univ (fun _ _ => hρ.contDiffAt) (fun _ _ => hS.contDiffAt)
      (fun y _ => hpos y)).mp hstationary x (Set.mem_univ x)

end FoliationQM.GeneralCouplingExample
