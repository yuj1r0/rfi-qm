module

public import FoliationQM.CurvedPolarKinetic
public import FoliationQM.CurvedKineticCovariance
public import FoliationQM.CurvedFluxRegularity
public import FoliationQM.PolarLocalInverse

/-!
# The polar and complex curved-spacetime actions

Theorem 9.2 combines the inverse-metric contraction of the actual field
derivatives with the scalar-curvature term from symmetric ordering. On a
positive density chart the two scalar densities agree pointwise, including
all off-diagonal metric entries. Multiplication by the coordinate volume
factor gives equal finite actions on the chart.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator Topology
namespace FoliationQM.CurvedPolarAction

open MeasureTheory LorentzMatrixGroup RNCVolumeDensity CurvedGradientCovariance
open RNCCoordinateCurvature ActionDensity

/-- The signed mass coefficient of the curved Klein–Gordon action. -/
def massTerm (p : MassiveParameters) (g : Covector → Mat4) (x : Covector) : ℝ :=
  p.m ^ 2 * p.c ^ 2 - p.hbar ^ 2 / 6 * scalar g x

/-- The real quadratic Klein–Gordon action density of the complex scalar. -/
def kgDensity (p : MassiveParameters) (g : Covector → Mat4) (ψ : Covector → ℂ) : Covector → ℝ :=
  CurvedKineticCovariance.actionDensity g (massTerm p g) p.hbar ψ

/-- The v13 density, real-action phase, logarithmic Fisher and curvature density in arbitrary coordinates. -/
def hydroDensity (p : MassiveParameters) (g : Covector → Mat4) (ρ S : Covector → ℝ) (x : Covector) : ℝ :=
  ρ x * (pairing g S S x - p.m ^ 2 * p.c ^ 2 +
    p.hbar ^ 2 / 4 * pairing g (Real.log ∘ ρ) (Real.log ∘ ρ) x +
    p.hbar ^ 2 / 6 * scalar g x)

/-- The Klein–Gordon action over the supplied coordinate region. -/
def kgAction (p : MassiveParameters) (g : Covector → Mat4) (ψ : Covector → ℂ) (U : Set Covector) : ℝ :=
  ∫ x in U, volumeFactor (g x) * kgDensity p g ψ x

/-- The curved phase-density action over the same coordinate region. -/
def hydroAction (p : MassiveParameters) (g : Covector → Mat4) (ρ S : Covector → ℝ) (U : Set Covector) : ℝ :=
  ∫ x in U, volumeFactor (g x) * hydroDensity p g ρ S x

/-- The curvature-adjusted mass coefficient is continuous for a locally C² metric of negative determinant. -/
theorem massTerm_continuousAt (p : MassiveParameters) {g : Covector → Mat4} {x : Covector}
    (hg : ContDiffAt ℝ 2 g x) (hd : (g x).det < 0) : ContinuousAt (massTerm p g) x :=
  continuousAt_const.sub (continuousAt_const.mul (CurvedFluxRegularity.scalar_continuousAt hg hd))

/-- Substitution of the actual polar field turns the curved Klein–Gordon density into the full phase-density expression. -/
theorem density_eq (p : MassiveParameters) (g : Covector → Mat4) {ρ S : Covector → ℝ} {x : Covector}
    (hρ : DifferentiableAt ℝ ρ x) (hS : DifferentiableAt ℝ S x) (hp : 0 < ρ x) :
    kgDensity p g (actionField p ρ S) x = hydroDensity p g ρ S x := by
  have hBorn : Complex.normSq (actionField p ρ S x) = ρ x := polarField_normSq ρ _ x hp.le
  rw [kgDensity, CurvedKineticCovariance.actionDensity, CurvedPolarKinetic.polar_kinetic_re p g hρ hS hp, hBorn]
  unfold massTerm hydroDensity
  ring

/-- Agreement of complex field germs preserves the full action density including its derivatives. -/
theorem kgDensity_congr (p : MassiveParameters) (g : Covector → Mat4) {ψ χ : Covector → ℂ} {x : Covector}
    (he : ψ =ᶠ[𝓝 x] χ) : kgDensity p g ψ x = kgDensity p g χ x := by
  simp only [kgDensity, CurvedKineticCovariance.actionDensity, CurvedFluxGreen.kinetic, he.fderiv_eq (𝕜 := ℝ),
    he.self_of_nhds]

/-- On a measurable positive chart, either volume-weighted polar integrand is integrable exactly when the other is. -/
theorem integrable_iff (p : MassiveParameters) (g : Covector → Mat4) {ρ S : Covector → ℝ}
    {U : Set Covector} (hU : MeasurableSet U) (hρ : ∀ x ∈ U, DifferentiableAt ℝ ρ x)
    (hS : ∀ x ∈ U, DifferentiableAt ℝ S x) (hp : ∀ x ∈ U, 0 < ρ x) :
    IntegrableOn (fun x => volumeFactor (g x) * kgDensity p g (actionField p ρ S) x) U ↔
    IntegrableOn (fun x => volumeFactor (g x) * hydroDensity p g ρ S x) U := by
  exact integrable_congr <| (ae_restrict_mem hU).mono fun x hx =>
    congrArg (volumeFactor (g x) * ·) (density_eq p g (hρ x hx) (hS x hx) (hp x hx))

/-- The actual volume integrals of the two action densities agree on a measurable positive chart. -/
theorem action_eq (p : MassiveParameters) (g : Covector → Mat4) {ρ S : Covector → ℝ}
    {U : Set Covector} (hU : MeasurableSet U) (hρ : ∀ x ∈ U, DifferentiableAt ℝ ρ x)
    (hS : ∀ x ∈ U, DifferentiableAt ℝ S x) (hp : ∀ x ∈ U, 0 < ρ x) :
    kgAction p g (actionField p ρ S) U = hydroAction p g ρ S U := by
  exact setIntegral_congr_fun hU fun x hx =>
    congrArg (volumeFactor (g x) * ·) (density_eq p g (hρ x hx) (hS x hx) (hp x hx))

/-- Around a nonzero C¹ wave the density and a real phase can be reconstructed so that the two curved actions agree on every measurable subregion. -/
theorem local_inverse_action (p : MassiveParameters) (g : Covector → Mat4) {ψ : Covector → ℂ}
    {U : Set Covector} (hU : IsOpen U) (hψ : ContDiffOn ℝ 1 ψ U)
    {x : Covector} (hx : x ∈ U) (hn : ψ x ≠ 0) :
    ∃ V : Set Covector, ∃ S : Covector → ℝ, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ContDiffOn ℝ 1 S V ∧ ∀ W : Set Covector, MeasurableSet W → W ⊆ V →
        kgAction p g ψ W = hydroAction p g (fun z => Complex.normSq (ψ z)) S W := by
  obtain ⟨V, hv, hxv, hsub, hρ, hS, he⟩ := PolarLocalInverse.exists_local_polar_reconstruction p hU hψ hx hn
  refine ⟨V, _, hv, hxv, hsub, hS, fun W hW hw => setIntegral_congr_fun hW fun z hz => ?_⟩
  have hV := hv.mem_nhds (hw hz)
  have heq := Filter.eventually_of_mem hV (fun y hy => (he y hy).2)
  exact congrArg (volumeFactor (g z) * ·) <| (kgDensity_congr p g heq).symm.trans <|
    density_eq p g ((hρ _ (hw hz)).contDiffAt hV).differentiableAt_one
      ((hS _ (hw hz)).contDiffAt hV).differentiableAt_one (he z (hw hz)).1

end FoliationQM.CurvedPolarAction
