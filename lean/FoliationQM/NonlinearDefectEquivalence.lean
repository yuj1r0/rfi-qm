module

public import FoliationQM.PolarRegularity

/-!
Source: v13 `eq:nonlinear_defect`.

The literal nonlinear modulus equation with the fixed physical phase S/hbar
is equivalent to the generalized Hamilton--Jacobi and actual continuity
equations for every real coupling. Positivity and local C² regularity justify
the modulus derivatives. No stationary-action or field-equation hypothesis
is needed for the equivalence itself.
-/
@[expose] public section

namespace FoliationQM.NonlinearDefectEquivalence

open scoped Topology
open PolarSecondDifferential

/-- The fixed-phase nonlinear defect encodes both generalized real jet
equations, including the reverse implication, for arbitrary real coupling. -/
theorem kgResidual_eq_nonlinearDefect_iff (p : MassiveParameters) (lam R S : ℝ)
    (dR dS : Covector) (boxR boxS : ℝ) (hR : 0 < R) :
    PolarSecondJet.kgResidual p R S dR dS boxR boxS =
        (((1 - 4 * lam / p.hbar ^ 2) * boxR / R : ℝ) : ℂ) *
          PolarSecondJet.wave p R S ↔
      minkowski dS dS - p.m ^ 2 * p.c ^ 2 = 4 * lam * boxR / R ∧
        PolarSecondJet.continuityResidual R dR dS boxS = 0 := by
  constructor
  · intro h
    rw [PolarSecondJet.kgResidual_decomposition p R S dR dS boxR boxS hR] at h
    have he : phase (S / p.hbar) ≠ 0 := Complex.exp_ne_zero _
    have h' :
        (((-R / p.hbar ^ 2 * PolarSecondJet.hjResidual p R dS boxR : ℝ) : ℂ) +
          Complex.I * ((PolarSecondJet.continuityResidual R dR dS boxS /
            (p.hbar * R) : ℝ) : ℂ)) =
        (((1 - 4 * lam / p.hbar ^ 2) * boxR / R : ℝ) : ℂ) * (R : ℂ) := by
      apply mul_left_cancel₀ he
      calc
        _ = _ := h
        _ = _ := by unfold PolarSecondJet.wave; ring
    have hr := congrArg Complex.re h'
    have hi := congrArg Complex.im h'
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero] at hr
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, zero_mul, mul_zero, one_mul, zero_add,
      add_zero] at hi
    have hR0 : R ≠ 0 := ne_of_gt hR
    have hh0 : p.hbar ≠ 0 := ne_of_gt p.hbar_pos
    refine ⟨?_, (div_eq_zero_iff.mp hi).resolve_right (mul_ne_zero hh0 hR0)⟩
    unfold PolarSecondJet.hjResidual at hr
    field_simp [hh0, hR0] at hr ⊢
    nlinarith
  · rintro ⟨hHJ, hcont⟩
    exact PolarSecondJet.kgResidual_eq_nonlinearDefect p lam R S dR dS boxR boxS
      hR hHJ hcont

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual amplitude-curvature equation is equivalent to generalized
Hamilton--Jacobi and actual current continuity on a positive phase chart. -/
theorem kg_eq_nonlinearDefect_iff (p : MassiveParameters) (lam : ℝ)
    {R S : E → ℝ} {x : E} (e : Fin 4 → E)
    (hR : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ R y)
    (hS : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ S y)
    (hR2 : ∀ μ, DifferentiableAt ℝ (directionalDerivative R (e μ)) x)
    (hS2 : ∀ μ, DifferentiableAt ℝ (directionalDerivative S (e μ)) x)
    (hpos : 0 < R x) :
    box (Madelung.actionField p R S) e x +
        (((p.m ^ 2 * p.c ^ 2 / p.hbar ^ 2 : ℝ) : ℂ) *
          Madelung.actionField p R S x) =
        (((1 - 4 * lam / p.hbar ^ 2) * box R e x / R x : ℝ) : ℂ) *
          Madelung.actionField p R S x ↔
      minkowski (fun μ => directionalDerivative S (e μ) x)
          (fun μ => directionalDerivative S (e μ) x) - p.m ^ 2 * p.c ^ 2 =
        4 * lam * box R e x / R x ∧ Madelung.currentDivergence R S e x = 0 := by
  rw [Madelung.kgResidual_actionField p e hR hS hR2 hS2,
    Madelung.currentDivergence_eq_continuityResidual e hR.self_of_nhds hS2]
  exact kgResidual_eq_nonlinearDefect_iff p lam (R x) (S x) _ _ _ _ hpos

/-- The literal modulus defect is equivalent to the two real equations;
positivity and continuity identify actual modulus and amplitude derivatives. -/
theorem kg_eq_nonlinearModulusDefect_iff (p : MassiveParameters) (lam : ℝ)
    {R S : E → ℝ} {x : E} (e : Fin 4 → E)
    (hR : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ R y)
    (hS : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ S y)
    (hR2 : ∀ μ, DifferentiableAt ℝ (directionalDerivative R (e μ)) x)
    (hS2 : ∀ μ, DifferentiableAt ℝ (directionalDerivative S (e μ)) x)
    (hpos : 0 < R x) :
    box (Madelung.actionField p R S) e x +
        (((p.m ^ 2 * p.c ^ 2 / p.hbar ^ 2 : ℝ) : ℂ) *
          Madelung.actionField p R S x) =
        (((1 - 4 * lam / p.hbar ^ 2) *
          box (fun y => ‖Madelung.actionField p R S y‖) e x /
            ‖Madelung.actionField p R S x‖ : ℝ) : ℂ) *
          Madelung.actionField p R S x ↔
      minkowski (fun μ => directionalDerivative S (e μ) x)
          (fun μ => directionalDerivative S (e μ) x) - p.m ^ 2 * p.c ^ 2 =
        4 * lam * box R e x / R x ∧ Madelung.currentDivergence R S e x = 0 := by
  rw [Madelung.box_norm_actionField p e hR.self_of_nhds.continuousAt hpos,
    Madelung.actionField_norm p R S x hpos.le]
  exact kg_eq_nonlinearDefect_iff p lam e hR hS hR2 hS2 hpos

/-- At positive locally C² density, the fixed-physical-phase nonlinear
modulus equation is exactly generalized Hamilton--Jacobi plus the actual
density-current continuity equation, for every real coupling. -/
theorem kg_eq_nonlinearModulusDefect_density_iff (p : MassiveParameters)
    (lam : ℝ) {ρ S : E → ℝ} {x : E} (hρ : ContDiffAt ℝ 2 ρ x)
    (hS : ContDiffAt ℝ 2 S x) (hpos : 0 < ρ x) (e : Fin 4 → E) :
    box (ActionDensity.actionField p ρ S) e x +
        (((p.m ^ 2 * p.c ^ 2 / p.hbar ^ 2 : ℝ) : ℂ) *
          ActionDensity.actionField p ρ S x) =
        (((1 - 4 * lam / p.hbar ^ 2) *
          box (fun y => ‖ActionDensity.actionField p ρ S y‖) e x /
            ‖ActionDensity.actionField p ρ S x‖ : ℝ) : ℂ) *
          ActionDensity.actionField p ρ S x ↔
      minkowski (fun μ => directionalDerivative S (e μ) x)
          (fun μ => directionalDerivative S (e μ) x) - p.m ^ 2 * p.c ^ 2 =
        4 * lam * box (fun z => Real.sqrt (ρ z)) e x / Real.sqrt (ρ x) ∧
      PolarRegularity.densityCurrentDivergence ρ S e x = 0 := by
  obtain ⟨hR, hS', hR2, hS2⟩ :=
    PolarRegularity.sqrt_density_second_order_hypotheses hρ hS hpos e
  have h := kg_eq_nonlinearModulusDefect_iff p lam e hR hS' hR2 hS2
    (Real.sqrt_pos.2 hpos)
  rw [PolarRegularity.currentDivergence_sqrt_density hρ.continuousAt hpos e] at h
  exact h

end FoliationQM.NonlinearDefectEquivalence
