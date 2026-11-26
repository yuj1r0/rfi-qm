module

public import FoliationQM.PolarSecondDifferential

/-!
Actual flat-space Klein--Gordon/Madelung identities for v13 `thm:kahler` and
`eq:nonlinear_defect`. The real phase is a local lift. The four constant
directions represent the (+---) contraction, with x⁰ = ct for coordinate
directions. Conservation here means vanishing divergence of R² ∂S; no
derivation by an action principle or integrated conservation law is claimed.
-/
@[expose] public section

namespace FoliationQM.Madelung

open scoped Topology
open PolarSecondDifferential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Physical wave field with the action phase S/hbar. -/
noncomputable def actionField (p : MassiveParameters) (R S : E → ℝ) : E → ℂ :=
  amplitudeField R (fun y => S y / p.hbar)

/-- Standard coordinate directions on spacetime with coordinates (ct,x,y,z). -/
def coordinateVector (μ : Fin 4) : Covector := Pi.single μ 1

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The physical field has the prescribed modulus at nonnegative amplitude. -/
theorem actionField_norm (p : MassiveParameters) (R S : E → ℝ) (x : E)
    (hR : 0 ≤ R x) : ‖actionField p R S x‖ = R x := by
  rw [actionField, amplitudeField, norm_mul, phase, Complex.norm_exp_ofReal_mul_I,
    mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR]

/-- Positive continuous amplitude equals the wave modulus on a neighborhood,
so their actual wave operators agree at the point. -/
theorem box_norm_actionField (p : MassiveParameters) {R S : E → ℝ} {x : E}
    (e : Fin 4 → E) (hR : ContinuousAt R x) (hpos : 0 < R x) :
    box (fun y => ‖actionField p R S y‖) e x = box R e x := by
  have heq : (fun y => ‖actionField p R S y‖) =ᶠ[𝓝 x] R := by
    filter_upwards [hR.eventually (Ioi_mem_nhds hpos)] with y hy
    exact actionField_norm p R S y hy.le
  have hfd := heq.fderiv (𝕜 := ℝ)
  have hsecond (v : E) :
      secondDirectionalDerivative (fun y => ‖actionField p R S y‖) v x =
        secondDirectionalDerivative R v x := by
    have hd : directionalDerivative (fun y => ‖actionField p R S y‖) v =ᶠ[𝓝 x]
        directionalDerivative R v := hfd.mono fun _ hy => congrArg (fun L => L v) hy
    exact congrArg (fun L => L v) (hd.fderiv_eq (𝕜 := ℝ))
  unfold box
  rw [hsecond, hsecond, hsecond, hsecond]

/-- Lowered components of the phase current, before the constant Noether factor. -/
noncomputable def phaseCurrent (R S : E → ℝ) (e : Fin 4 → E) (μ : Fin 4)
    (x : E) : ℝ :=
  R x ^ 2 * directionalDerivative S (e μ) x

/-- Actual divergence with the inverse Minkowski signs (+---). -/
noncomputable def currentDivergence (R S : E → ℝ) (e : Fin 4 → E) (x : E) : ℝ :=
  directionalDerivative (phaseCurrent R S e 0) (e 0) x -
    directionalDerivative (phaseCurrent R S e 1) (e 1) x -
    directionalDerivative (phaseCurrent R S e 2) (e 2) x -
    directionalDerivative (phaseCurrent R S e 3) (e 3) x

/-- Product rule for the derivative entering each current-divergence component. -/
theorem directionalDerivative_phaseCurrent {R S : E → ℝ} {x : E}
    (e : Fin 4 → E) (μ : Fin 4) (hR : DifferentiableAt ℝ R x)
    (hS2 : DifferentiableAt ℝ (directionalDerivative S (e μ)) x) :
    directionalDerivative (phaseCurrent R S e μ) (e μ) x =
      2 * R x * directionalDerivative R (e μ) x * directionalDerivative S (e μ) x +
        R x ^ 2 * secondDirectionalDerivative S (e μ) x := by
  have hd : HasFDerivAt (phaseCurrent R S e μ) _ x :=
    (hR.hasFDerivAt.pow 2).mul hS2.hasFDerivAt
  unfold directionalDerivative
  rw [hd.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, secondDirectionalDerivative,
    directionalDerivative]
  ring

/-- The expanded continuity residual is the actual divergence of R² ∂S. -/
theorem currentDivergence_eq_continuityResidual {R S : E → ℝ} {x : E}
    (e : Fin 4 → E) (hR : DifferentiableAt ℝ R x)
    (hS2 : ∀ μ, DifferentiableAt ℝ (directionalDerivative S (e μ)) x) :
    currentDivergence R S e x =
      PolarSecondJet.continuityResidual (R x)
        (fun μ => directionalDerivative R (e μ) x)
        (fun μ => directionalDerivative S (e μ) x) (box S e x) := by
  unfold currentDivergence
  rw [directionalDerivative_phaseCurrent e 0 hR (hS2 0),
    directionalDerivative_phaseCurrent e 1 hR (hS2 1),
    directionalDerivative_phaseCurrent e 2 hR (hS2 2),
    directionalDerivative_phaseCurrent e 3 hR (hS2 3)]
  simp only [PolarSecondJet.continuityResidual, minkowski, box]
  ring

/-- The KG operator formed from actual derivatives equals the concrete jet
residual. This identity requires regularity but assumes no field equation. -/
theorem kgResidual_actionField (p : MassiveParameters) {R S : E → ℝ} {x : E}
    (e : Fin 4 → E)
    (hR : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ R y)
    (hS : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ S y)
    (hR2 : ∀ μ, DifferentiableAt ℝ (directionalDerivative R (e μ)) x)
    (hS2 : ∀ μ, DifferentiableAt ℝ (directionalDerivative S (e μ)) x) :
    box (actionField p R S) e x +
        (((p.m ^ 2 * p.c ^ 2 / p.hbar ^ 2 : ℝ) : ℂ) * actionField p R S x) =
      PolarSecondJet.kgResidual p (R x) (S x)
        (fun μ => directionalDerivative R (e μ) x)
        (fun μ => directionalDerivative S (e μ) x) (box R e x) (box S e x) := by
  unfold actionField
  rw [box_actionField p e hR hS hR2 hS2]
  rfl

/-- On a positive-amplitude phase chart, the actual complex KG equation is
equivalent to the real Hamilton--Jacobi--Bohm equation and actual continuity
equation. All derivatives are those of the specified real source fields. -/
theorem kg_eq_zero_iff_madelung (p : MassiveParameters) {R S : E → ℝ} {x : E}
    (e : Fin 4 → E)
    (hR : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ R y)
    (hS : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ S y)
    (hR2 : ∀ μ, DifferentiableAt ℝ (directionalDerivative R (e μ)) x)
    (hS2 : ∀ μ, DifferentiableAt ℝ (directionalDerivative S (e μ)) x)
    (hpos : 0 < R x) :
    box (actionField p R S) e x +
        (((p.m ^ 2 * p.c ^ 2 / p.hbar ^ 2 : ℝ) : ℂ) * actionField p R S x) = 0 ↔
      minkowski (fun μ => directionalDerivative S (e μ) x)
          (fun μ => directionalDerivative S (e μ) x) =
        p.m ^ 2 * p.c ^ 2 + p.hbar ^ 2 * box R e x / R x ∧
      currentDivergence R S e x = 0 := by
  rw [kgResidual_actionField p e hR hS hR2 hS2,
    PolarSecondJet.kgResidual_eq_zero_iff p (R x) (S x) _ _ _ _ hpos,
    currentDivergence_eq_continuityResidual e hR.self_of_nhds hS2]
  simp only [PolarSecondJet.hjResidual, sub_sub, sub_eq_zero]

/-- Explicit spacetime-coordinate specialization of KG/Madelung equivalence. -/
theorem kg_eq_zero_iff_madelung_coordinates (p : MassiveParameters)
    {R S : Covector → ℝ} {x : Covector}
    (hR : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ R y)
    (hS : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ S y)
    (hR2 : ∀ μ, DifferentiableAt ℝ (directionalDerivative R (coordinateVector μ)) x)
    (hS2 : ∀ μ, DifferentiableAt ℝ (directionalDerivative S (coordinateVector μ)) x)
    (hpos : 0 < R x) :
    box (actionField p R S) coordinateVector x +
        (((p.m ^ 2 * p.c ^ 2 / p.hbar ^ 2 : ℝ) : ℂ) * actionField p R S x) = 0 ↔
      minkowski (fun μ => directionalDerivative S (coordinateVector μ) x)
          (fun μ => directionalDerivative S (coordinateVector μ) x) =
        p.m ^ 2 * p.c ^ 2 + p.hbar ^ 2 * box R coordinateVector x / R x ∧
      currentDivergence R S coordinateVector x = 0 :=
  kg_eq_zero_iff_madelung p coordinateVector hR hS hR2 hS2 hpos

/-- The actual nonlinear wave defect follows from the generalized real HJ
equation and actual vanishing current divergence. Stationary variation is
a separate statement from these supplied differential equations. -/
theorem kg_eq_nonlinearDefect (p : MassiveParameters) (lam : ℝ)
    {R S : E → ℝ} {x : E} (e : Fin 4 → E)
    (hR : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ R y)
    (hS : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ S y)
    (hR2 : ∀ μ, DifferentiableAt ℝ (directionalDerivative R (e μ)) x)
    (hS2 : ∀ μ, DifferentiableAt ℝ (directionalDerivative S (e μ)) x)
    (hpos : 0 < R x)
    (hHJ : minkowski (fun μ => directionalDerivative S (e μ) x)
        (fun μ => directionalDerivative S (e μ) x) - p.m ^ 2 * p.c ^ 2 =
      4 * lam * box R e x / R x)
    (hcont : currentDivergence R S e x = 0) :
    box (actionField p R S) e x +
        (((p.m ^ 2 * p.c ^ 2 / p.hbar ^ 2 : ℝ) : ℂ) * actionField p R S x) =
      (((1 - 4 * lam / p.hbar ^ 2) * box R e x / R x : ℝ) : ℂ) * actionField p R S x := by
  rw [kgResidual_actionField p e hR hS hR2 hS2]
  rw [currentDivergence_eq_continuityResidual e hR.self_of_nhds hS2] at hcont
  exact PolarSecondJet.kgResidual_eq_nonlinearDefect p lam (R x) (S x)
    (fun μ => directionalDerivative R (e μ) x)
    (fun μ => directionalDerivative S (e μ) x) (box R e x) (box S e x) hpos hHJ hcont

/-- The literal modulus form of the source nonlinear defect, conditional on
the explicit real generalized HJ and actual continuity equations. -/
theorem kg_eq_nonlinearModulusDefect (p : MassiveParameters) (lam : ℝ)
    {R S : E → ℝ} {x : E} (e : Fin 4 → E)
    (hR : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ R y)
    (hS : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ S y)
    (hR2 : ∀ μ, DifferentiableAt ℝ (directionalDerivative R (e μ)) x)
    (hS2 : ∀ μ, DifferentiableAt ℝ (directionalDerivative S (e μ)) x)
    (hpos : 0 < R x)
    (hHJ : minkowski (fun μ => directionalDerivative S (e μ) x)
        (fun μ => directionalDerivative S (e μ) x) - p.m ^ 2 * p.c ^ 2 =
      4 * lam * box R e x / R x)
    (hcont : currentDivergence R S e x = 0) :
    box (actionField p R S) e x +
        (((p.m ^ 2 * p.c ^ 2 / p.hbar ^ 2 : ℝ) : ℂ) * actionField p R S x) =
      (((1 - 4 * lam / p.hbar ^ 2) * box (fun y => ‖actionField p R S y‖) e x /
        ‖actionField p R S x‖ : ℝ) : ℂ) * actionField p R S x := by
  rw [box_norm_actionField p e hR.self_of_nhds.continuousAt hpos,
    actionField_norm p R S x hpos.le]
  exact kg_eq_nonlinearDefect p lam e hR hS hR2 hS2 hpos hHJ hcont

end FoliationQM.Madelung
