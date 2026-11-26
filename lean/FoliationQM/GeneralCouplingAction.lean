module

public import FoliationQM.RelativePolarStationaryAction

/-!
# Actual real action for an arbitrary positive Fisher coupling

Sources: v13 `eq:general_lambda_action` and `eq:nonlinear_defect`.
The density below is the literal source expression with a free coefficient λ.
Its relative action integrates the pointwise density change. A positive λ
permits an auxiliary parameter record with ℏ = 2√λ, used only to transport
proved real-action identities. This auxiliary record does not identify the
source's fixed physical phase S / p.hbar with S / (2√λ).
-/
@[expose] public section

namespace FoliationQM.GeneralCouplingAction

open MeasureTheory ActionDensity ActionVariation PolarTestVariations FlatIntegrationByParts
open scoped Topology ContDiff ComplexConjugate

/-- Auxiliary parameters for the real-action proof: mass and light speed
are unchanged, while the square of the auxiliary ℏ is 4λ. -/
noncomputable def effectiveParameters (p : MassiveParameters) (lam : ℝ) (hlam : 0 < lam) :
    MassiveParameters where
  c := p.c
  m := p.m
  hbar := 2 * Real.sqrt lam
  c_pos := p.c_pos
  m_pos := p.m_pos
  hbar_pos := mul_pos (by norm_num) (Real.sqrt_pos.2 hlam)

/-- The auxiliary parameter has the prescribed square. -/
theorem effectiveParameters_hbar_sq (p : MassiveParameters) {lam : ℝ} (hlam : 0 < lam) :
    (effectiveParameters p lam hlam).hbar ^ 2 = 4 * lam := by
  change (2 * Real.sqrt lam) ^ 2 = 4 * lam
  nlinarith [Real.sq_sqrt hlam.le]

/-- The canonical Fisher coefficient of the auxiliary record is exactly λ. -/
theorem effectiveParameters_fisher (p : MassiveParameters) {lam : ℝ} (hlam : 0 < lam) :
    (effectiveParameters p lam hlam).hbar ^ 2 / 4 = lam := by
  rw [effectiveParameters_hbar_sq p hlam]
  ring

/-- At the physical canonical coefficient the auxiliary parameters are the
original parameters, including their positive ℏ. -/
theorem effectiveParameters_canonical (p : MassiveParameters) :
    effectiveParameters p (p.hbar ^ 2 / 4)
      (div_pos (sq_pos_of_pos p.hbar_pos) (by norm_num)) = p := by
  have hs : 2 * Real.sqrt (p.hbar ^ 2 / 4) = p.hbar := by
    have hsqr := Real.sq_sqrt (show 0 ≤ p.hbar ^ 2 / 4 by positivity)
    have hnonneg := Real.sqrt_nonneg (p.hbar ^ 2 / 4)
    nlinarith [p.hbar_pos]
  cases p
  simp only [effectiveParameters, MassiveParameters.mk.injEq]
  exact ⟨True.intro, True.intro, hs⟩

/-- The actual source density at general coupling, using real Fréchet
derivatives of S and log ρ and the explicit Minkowski contraction. -/
noncomputable def hydroIntegrand (p : MassiveParameters) (lam : ℝ)
    (ρ S : Covector → ℝ) (e : Fin 4 → Covector) (x : Covector) : ℝ :=
  ρ x * (minkowski (fun i => fderiv ℝ S x (e i)) (fun i => fderiv ℝ S x (e i)) -
    p.m ^ 2 * p.c ^ 2 + lam *
      minkowski (fun i => fderiv ℝ (fun y => Real.log (ρ y)) x (e i))
        (fun i => fderiv ℝ (fun y => Real.log (ρ y)) x (e i)))

/-- The ordinary restricted source action, whose finiteness is a separate
integrability condition whenever this integral is used variationally. -/
noncomputable def hydroActionOn (p : MassiveParameters) (lam : ℝ)
    (ρ S : Covector → ℝ) (e : Fin 4 → Covector) (U : Set Covector) : ℝ :=
  ∫ x in U, hydroIntegrand p lam ρ S e x

/-- Pointwise change of the actual general-coupling density, background first. -/
noncomputable def relativeHydroDensity (p : MassiveParameters) (lam : ℝ)
    (ρ S ρ' S' : Covector → ℝ) (e : Fin 4 → Covector) (x : Covector) : ℝ :=
  hydroIntegrand p lam ρ' S' e x - hydroIntegrand p lam ρ S e x

/-- The relative action integrates the density change itself, without
subtracting potentially nonintegrable whole actions. -/
noncomputable def relativeHydroAction (p : MassiveParameters) (lam : ℝ)
    (ρ S ρ' S' : Covector → ℝ) (e : Fin 4 → Covector) (U : Set Covector) : ℝ :=
  ∫ x in U, relativeHydroDensity p lam ρ S ρ' S' e x

/-- The literal λ density is exactly the canonical real density for the
auxiliary record. This algebraic identity needs no differentiability premise. -/
theorem hydroIntegrand_eq_effective (p : MassiveParameters) {lam : ℝ} (hlam : 0 < lam)
    (ρ S : Covector → ℝ) (e : Fin 4 → Covector) (x : Covector) :
    hydroIntegrand p lam ρ S e x =
      PolarChartAction.hydroIntegrand (effectiveParameters p lam hlam) ρ S e x := by
  simp only [hydroIntegrand, PolarChartAction.hydroIntegrand, hydroDensity,
    effectiveParameters_fisher p hlam]
  rfl

/-- The literal ordinary actions have the same auxiliary-parameter identity. -/
theorem hydroActionOn_eq_effective (p : MassiveParameters) {lam : ℝ} (hlam : 0 < lam)
    (ρ S : Covector → ℝ) (e : Fin 4 → Covector) (U : Set Covector) :
    hydroActionOn p lam ρ S e U =
      OpenPolarStationaryAction.hydroActionOn (effectiveParameters p lam hlam) ρ S e U := by
  simp only [hydroActionOn, OpenPolarStationaryAction.hydroActionOn,
    hydroIntegrand_eq_effective p hlam]

/-- Pointwise relative density is preserved by the auxiliary-parameter proof. -/
theorem relativeHydroDensity_eq_effective (p : MassiveParameters) {lam : ℝ} (hlam : 0 < lam)
    (ρ S ρ' S' : Covector → ℝ) (e : Fin 4 → Covector) (x : Covector) :
    relativeHydroDensity p lam ρ S ρ' S' e x =
      RelativePolarStationaryAction.relativeHydroDensity
        (effectiveParameters p lam hlam) ρ S ρ' S' e x := by
  simp only [relativeHydroDensity, RelativePolarStationaryAction.relativeHydroDensity,
    hydroIntegrand_eq_effective p hlam]

/-- Equality of the actual relative integral is independent of any finiteness
assumption on the background or perturbed whole densities. -/
theorem relativeHydroAction_eq_effective (p : MassiveParameters) {lam : ℝ} (hlam : 0 < lam)
    (ρ S ρ' S' : Covector → ℝ) (e : Fin 4 → Covector) (U : Set Covector) :
    relativeHydroAction p lam ρ S ρ' S' e U =
      RelativePolarStationaryAction.relativeHydroAction
        (effectiveParameters p lam hlam) ρ S ρ' S' e U := by
  simp only [relativeHydroAction, RelativePolarStationaryAction.relativeHydroAction,
    relativeHydroDensity_eq_effective p hlam]

/-- With genuinely integrable whole densities, relative action agrees with
their ordinary action difference for every real coupling. -/
theorem relativeHydroAction_eq_sub (p : MassiveParameters) (lam : ℝ)
    (ρ S ρ' S' : Covector → ℝ) (e : Fin 4 → Covector) (U : Set Covector)
    (hbase : IntegrableOn (hydroIntegrand p lam ρ S e) U)
    (hnew : IntegrableOn (hydroIntegrand p lam ρ' S' e) U) :
    relativeHydroAction p lam ρ S ρ' S' e U =
      hydroActionOn p lam ρ' S' e U - hydroActionOn p lam ρ S e U :=
  integral_sub hnew hbase

/-- At λ = ℏ²/4 the literal density is the existing physical canonical one. -/
theorem hydroIntegrand_canonical (p : MassiveParameters)
    (ρ S : Covector → ℝ) (e : Fin 4 → Covector) (x : Covector) :
    hydroIntegrand p (p.hbar ^ 2 / 4) ρ S e x = PolarChartAction.hydroIntegrand p ρ S e x := rfl

/-- At λ = ℏ²/4 the actual relative action is the established physical action. -/
theorem relativeHydroAction_canonical (p : MassiveParameters)
    (ρ S ρ' S' : Covector → ℝ) (e : Fin 4 → Covector) (U : Set Covector) :
    relativeHydroAction p (p.hbar ^ 2 / 4) ρ S ρ' S' e U =
      RelativePolarStationaryAction.relativeHydroAction p ρ S ρ' S' e U := rfl

/-- The density change under independent smooth compact interior real tests
is genuinely integrable near zero, even with infinite background action. -/
theorem eventually_integrableOn_relativeHydroDensity_affine (p : MassiveParameters)
    {lam : ℝ} (hlam : 0 < lam) {ρ S a b : Covector → ℝ} {U : Set Covector} (hU : IsOpen U)
    (hρ : ∀ x ∈ U, ContDiffAt ℝ ∞ ρ x) (hS : ∀ x ∈ U, ContDiffAt ℝ ∞ S x)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hpos : ∀ x ∈ U, 0 < ρ x)
    (hca : HasCompactSupport a) (hcb : HasCompactSupport b)
    (hsa : tsupport a ⊆ U) (hsb : tsupport b ⊆ U) (e : Fin 4 → Covector) :
    ∀ᶠ t in 𝓝 (0 : ℝ), IntegrableOn
      (relativeHydroDensity p lam ρ S (fun x => ρ x + t * a x) (fun x => S x + t * b x) e) U := by
  simp only [funext (relativeHydroDensity_eq_effective p hlam ρ S _ _ e)]
  exact RelativePolarStationaryAction.eventually_integrableOn_relativeHydroDensity_affine
    (effectiveParameters p lam hlam) hU hρ hS ha hb hpos hca hcb hsa hsb e

/-- Actual first variation of the literal source action, transported through
the auxiliary real-action identity. The phase in this intermediate pairing
is the auxiliary phase; fixed-physical-clock conclusions are separate. -/
theorem hasDerivAt_relativeHydroAction_affine (p : MassiveParameters)
    {lam : ℝ} (hlam : 0 < lam) {ρ S a b : Covector → ℝ} {U : Set Covector} (hU : IsOpen U)
    (hρ : ∀ x ∈ U, ContDiffAt ℝ ∞ ρ x) (hS : ∀ x ∈ U, ContDiffAt ℝ ∞ S x)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hpos : ∀ x ∈ U, 0 < ρ x)
    (hca : HasCompactSupport a) (hcb : HasCompactSupport b)
    (hsa : tsupport a ⊆ U) (hsb : tsupport b ⊆ U) (e : Fin 4 → Covector) :
    HasDerivAt (fun t : ℝ => relativeHydroAction p lam ρ S
      (fun x => ρ x + t * a x) (fun x => S x + t * b x) e U)
      (-2 * ∫ x in U, (conj (testTangent (effectiveParameters p lam hlam) ρ S a b x) *
        kgOperator (effectiveParameters p lam hlam)
          (actionField (effectiveParameters p lam hlam) ρ S) e x).re) 0 := by
  simp only [relativeHydroAction_eq_effective p hlam]
  exact RelativePolarStationaryAction.hasDerivAt_relativeHydroAction_affine
    (effectiveParameters p lam hlam) hU hρ hS ha hb hpos hca hcb hsa hsb e

end FoliationQM.GeneralCouplingAction
