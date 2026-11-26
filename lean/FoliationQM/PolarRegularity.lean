module

public import FoliationQM.ActionDensity
public import FoliationQM.Madelung
public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
Sources: v13 `thm:kahler` and `eq:nonlinear_defect`.

Local C² density and phase fields suffice for the actual second-derivative
KG/Madelung identities. Positivity is required only at the point: continuity
provides the positive neighborhood needed for the square-root amplitude.
The real phase is supplied on the local chart. Integrated stationarity and
the construction of an inverse phase chart remain separate results.
-/
@[expose] public section

namespace FoliationQM.PolarRegularity

open scoped Topology
open PolarSecondDifferential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Local C² regularity supplies first differentiability on a neighborhood. -/
theorem eventually_differentiableAt_of_contDiffAt_two {f : E → F} {x : E}
    (hf : ContDiffAt ℝ 2 f x) :
    ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y := by
  filter_upwards [hf.eventually (by norm_num)] with y hy
  exact hy.differentiableAt (by norm_num)

/-- A fixed directional derivative of a locally C² field is differentiable. -/
theorem differentiableAt_directionalDerivative_of_contDiffAt_two
    {f : E → F} {x : E} (hf : ContDiffAt ℝ 2 f x) (v : E) :
    DifferentiableAt ℝ (directionalDerivative f v) x := by
  have hd : ContDiffAt ℝ 1 (fderiv ℝ f) x := hf.fderiv_right (by norm_num)
  exact (hd.clm_apply contDiffAt_const).differentiableAt_one

/-- Positive C² density gives every amplitude and phase regularity hypothesis
used by the actual KG/Madelung equivalence, for any four fixed directions. -/
theorem sqrt_density_second_order_hypotheses {ρ S : E → ℝ} {x : E}
    (hρ : ContDiffAt ℝ 2 ρ x) (hS : ContDiffAt ℝ 2 S x) (hpos : 0 < ρ x)
    (e : Fin 4 → E) :
    (∀ᶠ y in 𝓝 x, DifferentiableAt ℝ (fun z => Real.sqrt (ρ z)) y) ∧
    (∀ᶠ y in 𝓝 x, DifferentiableAt ℝ S y) ∧
    (∀ μ, DifferentiableAt ℝ
      (directionalDerivative (fun z => Real.sqrt (ρ z)) (e μ)) x) ∧
    (∀ μ, DifferentiableAt ℝ (directionalDerivative S (e μ)) x) := by
  have hR : ContDiffAt ℝ 2 (fun z => Real.sqrt (ρ z)) x := hρ.sqrt (ne_of_gt hpos)
  exact ⟨eventually_differentiableAt_of_contDiffAt_two hR,
    eventually_differentiableAt_of_contDiffAt_two hS,
    fun μ => differentiableAt_directionalDerivative_of_contDiffAt_two hR (e μ),
    fun μ => differentiableAt_directionalDerivative_of_contDiffAt_two hS (e μ)⟩

/-- The concrete positive-density polar field inherits the local C²
regularity of density and real action phase. -/
theorem contDiffAt_actionField (p : MassiveParameters) {ρ S : E → ℝ} {x : E}
    (hρ : ContDiffAt ℝ 2 ρ x) (hS : ContDiffAt ℝ 2 S x) (hpos : 0 < ρ x) :
    ContDiffAt ℝ 2 (ActionDensity.actionField p ρ S) x := by
  have hR := Complex.ofRealCLM.contDiff.contDiffAt.comp x (hρ.sqrt (ne_of_gt hpos))
  have hSc := Complex.ofRealCLM.contDiff.contDiffAt.comp x (hS.div_const p.hbar)
  exact hR.mul ((hSc.mul (contDiffAt_const (c := Complex.I))).cexp)

/-- The source continuity current in the density and action-phase variables. -/
noncomputable def densityCurrent (ρ S : E → ℝ) (e : Fin 4 → E) (μ : Fin 4)
    (x : E) : ℝ := ρ x * directionalDerivative S (e μ) x

/-- Actual divergence of the density current, with the (+---) metric signs. -/
noncomputable def densityCurrentDivergence (ρ S : E → ℝ) (e : Fin 4 → E)
    (x : E) : ℝ :=
  directionalDerivative (densityCurrent ρ S e 0) (e 0) x -
    directionalDerivative (densityCurrent ρ S e 1) (e 1) x -
    directionalDerivative (densityCurrent ρ S e 2) (e 2) x -
    directionalDerivative (densityCurrent ρ S e 3) (e 3) x

/-- Positive continuous density identifies the amplitude-current divergence
with the literal density-current divergence. No field equation is assumed. -/
theorem currentDivergence_sqrt_density {ρ S : E → ℝ} {x : E}
    (hρ : ContinuousAt ρ x) (hpos : 0 < ρ x) (e : Fin 4 → E) :
    Madelung.currentDivergence (fun z => Real.sqrt (ρ z)) S e x =
      densityCurrentDivergence ρ S e x := by
  have heq (μ : Fin 4) :
      Madelung.phaseCurrent (fun z => Real.sqrt (ρ z)) S e μ =ᶠ[𝓝 x]
        densityCurrent ρ S e μ := by
    filter_upwards [hρ.eventually (Ioi_mem_nhds hpos)] with y hy
    simp only [Madelung.phaseCurrent, densityCurrent, Real.sq_sqrt hy.le]
  have hd (μ : Fin 4) :
      directionalDerivative
          (Madelung.phaseCurrent (fun z => Real.sqrt (ρ z)) S e μ) (e μ) x =
        directionalDerivative (densityCurrent ρ S e μ) (e μ) x :=
    congrArg (fun L => L (e μ)) ((heq μ).fderiv_eq (𝕜 := ℝ))
  unfold Madelung.currentDivergence densityCurrentDivergence
  rw [hd 0, hd 1, hd 2, hd 3]

/-- The positive-density C² local KG equation is equivalent to the real
Hamilton--Jacobi--Bohm equation and the actual density-current continuity
equation. This removes the separate derivative-regularity hypotheses. -/
theorem kg_eq_zero_iff_madelung_density (p : MassiveParameters)
    {ρ S : E → ℝ} {x : E} (hρ : ContDiffAt ℝ 2 ρ x)
    (hS : ContDiffAt ℝ 2 S x) (hpos : 0 < ρ x) (e : Fin 4 → E) :
    box (ActionDensity.actionField p ρ S) e x +
        (((p.m ^ 2 * p.c ^ 2 / p.hbar ^ 2 : ℝ) : ℂ) *
          ActionDensity.actionField p ρ S x) = 0 ↔
      minkowski (fun μ => directionalDerivative S (e μ) x)
          (fun μ => directionalDerivative S (e μ) x) =
        p.m ^ 2 * p.c ^ 2 +
          p.hbar ^ 2 * box (fun z => Real.sqrt (ρ z)) e x / Real.sqrt (ρ x) ∧
      densityCurrentDivergence ρ S e x = 0 := by
  obtain ⟨hR, hS', hR2, hS2⟩ := sqrt_density_second_order_hypotheses hρ hS hpos e
  have h := Madelung.kg_eq_zero_iff_madelung p e hR hS' hR2 hS2 (Real.sqrt_pos.2 hpos)
  rw [currentDivergence_sqrt_density hρ.continuousAt hpos e] at h
  exact h

/-- Coordinate form for spacetime (ct,x,y,z), requiring C² regularity and
positive density only locally at the evaluation point. -/
theorem kg_eq_zero_iff_madelung_density_coordinates (p : MassiveParameters)
    {ρ S : Covector → ℝ} {x : Covector} (hρ : ContDiffAt ℝ 2 ρ x)
    (hS : ContDiffAt ℝ 2 S x) (hpos : 0 < ρ x) :
    box (ActionDensity.actionField p ρ S) Madelung.coordinateVector x +
        (((p.m ^ 2 * p.c ^ 2 / p.hbar ^ 2 : ℝ) : ℂ) *
          ActionDensity.actionField p ρ S x) = 0 ↔
      minkowski (fun μ => directionalDerivative S (Madelung.coordinateVector μ) x)
          (fun μ => directionalDerivative S (Madelung.coordinateVector μ) x) =
        p.m ^ 2 * p.c ^ 2 + p.hbar ^ 2 *
          box (fun z => Real.sqrt (ρ z)) Madelung.coordinateVector x / Real.sqrt (ρ x) ∧
      densityCurrentDivergence ρ S Madelung.coordinateVector x = 0 :=
  kg_eq_zero_iff_madelung_density p hρ hS hpos Madelung.coordinateVector

/-- The literal modulus defect for the density polar field under local C²
regularity, positive density, and the supplied generalized real equations.
The real equations are hypotheses; they are not derived by stationarity here. -/
theorem kg_eq_nonlinearModulusDefect_density (p : MassiveParameters) (lam : ℝ)
    {ρ S : E → ℝ} {x : E} (hρ : ContDiffAt ℝ 2 ρ x)
    (hS : ContDiffAt ℝ 2 S x) (hpos : 0 < ρ x) (e : Fin 4 → E)
    (hHJ : minkowski (fun μ => directionalDerivative S (e μ) x)
        (fun μ => directionalDerivative S (e μ) x) - p.m ^ 2 * p.c ^ 2 =
      4 * lam * box (fun z => Real.sqrt (ρ z)) e x / Real.sqrt (ρ x))
    (hcont : densityCurrentDivergence ρ S e x = 0) :
    box (ActionDensity.actionField p ρ S) e x +
        (((p.m ^ 2 * p.c ^ 2 / p.hbar ^ 2 : ℝ) : ℂ) *
          ActionDensity.actionField p ρ S x) =
      (((1 - 4 * lam / p.hbar ^ 2) *
        box (fun y => ‖ActionDensity.actionField p ρ S y‖) e x /
          ‖ActionDensity.actionField p ρ S x‖ : ℝ) : ℂ) *
        ActionDensity.actionField p ρ S x := by
  obtain ⟨hR, hS', hR2, hS2⟩ := sqrt_density_second_order_hypotheses hρ hS hpos e
  have hcont' : Madelung.currentDivergence (fun z => Real.sqrt (ρ z)) S e x = 0 := by
    rw [currentDivergence_sqrt_density hρ.continuousAt hpos e]
    exact hcont
  exact Madelung.kg_eq_nonlinearModulusDefect p lam e hR hS' hR2 hS2
    (Real.sqrt_pos.2 hpos) hHJ hcont'

end FoliationQM.PolarRegularity
