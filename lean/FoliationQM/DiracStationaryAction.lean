module
public import FoliationQM.DiracOnShellDensity
public import FoliationQM.DiracFundamentalLemma
public import FoliationQM.DiracActionIntegrationByParts

/-!
# Stationarity of the flat spinor action and the Dirac equation

For v13 `thm:dirac_lift`, stationarity tests actual derivatives of integrals
over an open subset of flat spacetime. The compact interior fundamental
lemma detects all components of the Dirac residual. A nonzero speed
coefficient is needed to recover it from the action. The affine criterion
applies already to locally C¹ backgrounds.
-/

@[expose] public section
noncomputable section
open scoped Topology ContDiff
namespace FoliationQM.DiracStationaryAction
open MeasureTheory DiracMatrices DiracEquation DiracActionSupport DiracResidualField
open DiracAffineFieldVariation (affine)
open DiracInteriorVariation DiracCurveJetCalculus DiracRelativeAction

variable (hbar c m : ℝ)

/-- Every smooth compact interior affine test gives zero first derivative of the relative action. -/
def AffineStationary (U : Set Covector) (ψ : Covector → Spinor) : Prop :=
  ∀ η : Covector → Spinor, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ U →
    HasDerivAt (fun t => relativeAction hbar c m ψ (affine ψ η t) U) 0 0

/-- Every admissible smooth interior variation gives zero first derivative of the relative action. -/
def RelativeStationary (U : Set Covector) (ψ : Covector → Spinor) : Prop :=
  ∀ V : Variation U ψ,
    HasDerivAt (fun t => relativeAction hbar c m ψ (slice V.family t) U) 0 0

/-- Ordinary-action stationarity on finite-action backgrounds. -/
def AbsoluteStationary (U : Set Covector) (ψ : Covector → Spinor) : Prop :=
  ∀ V : Variation U ψ, HasDerivAt (fun t => action hbar c m (slice V.family t) U) 0 0

variable {U : Set Covector} {ψ : Covector → Spinor}

/-- On a locally C¹ background, testing affine compact variations is equivalent to the
pointwise equation on the whole open domain. -/
theorem affine_iff (hU : IsOpen U) (hψ : ∀ x ∈ U, ContDiffAt ℝ 1 ψ x) (hc : c ≠ 0) :
    AffineStationary hbar c m U ψ ↔ ∀ x ∈ U, diracField hbar m c ψ x = 0 := by
  have hR : ContinuousOn (diracField hbar m c ψ) U :=
    fun x hx => (continuousAt_diracField hbar m c (hψ x hx)).continuousWithinAt
  rw [← DiracFundamentalLemma.vanishing_pairings_iff hU hR]
  constructor
  · intro h η hη hcompact hs
    have hd := DiracActionIntegrationByParts.hasDerivAt_relative_affine hbar c m
      hU hψ (hη.of_le (by simp)) hcompact hs
    have he := hd.unique (h η hη hcompact hs)
    exact (mul_eq_zero.mp he).resolve_left (mul_ne_zero (by norm_num) hc)
  · intro h η hη hcompact hs
    have hd := DiracActionIntegrationByParts.hasDerivAt_relative_affine hbar c m
      hU hψ (hη.of_le (by simp)) hcompact hs
    have hz : ∫ x in U, tested hbar m c ψ η x = 0 := h η hη hcompact hs
    simpa only [hz, mul_zero] using hd

/-- Every compact test is realized as an admissible smooth field family. -/
theorem affine_of_relative (hψ : ∀ x ∈ U, ContDiffAt ℝ ∞ ψ x)
    (h : RelativeStationary hbar c m U ψ) : AffineStationary hbar c m U ψ := by
  intro η hη hc hs
  exact h (affineVariation η hψ hη hc hs)

/-- The equation implies vanishing first variation along every admissible family. -/
theorem relative_of_equation (hU : IsOpen U) (he : ∀ x ∈ U, diracField hbar m c ψ x = 0) :
    RelativeStationary hbar c m U ψ := by
  intro V
  have hz : (∫ x in U, tested hbar m c ψ (velocity V.family 0) x) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    rw [tested, he x hx]
    change DiracResidualPairing.pairCLM _ (0 : Spinor) = 0
    exact map_zero _
  simpa only [hz, mul_zero] using DiracActionIntegrationByParts.hasDerivAt_relative hbar c m V hU

/-- Smooth compact-family stationarity is equivalent to the actual flat Dirac equation. -/
theorem relative_iff (hU : IsOpen U) (hψ : ∀ x ∈ U, ContDiffAt ℝ ∞ ψ x) (hc : c ≠ 0) :
    RelativeStationary hbar c m U ψ ↔ ∀ x ∈ U, diracField hbar m c ψ x = 0 :=
  ⟨fun h => (affine_iff hbar c m hU (fun x hx => (hψ x hx).of_le (by simp)) hc).mp
    (affine_of_relative hbar c m hψ h), relative_of_equation hbar c m hU⟩

/-- In the manuscript's normalization the statement is the equation on the actual coordinate derivatives. -/
theorem relative_iff_dirac (hU : IsOpen U) (hψ : ∀ x ∈ U, ContDiffAt ℝ ∞ ψ x) (hc : c ≠ 0) :
    RelativeStationary hbar c m U ψ ↔ ∀ x ∈ U,
      jetEquation hbar m c (ψ x) (fun μ => fderiv ℝ ψ x (DiracFieldDensity.coordinateDirections μ)) := by
  rw [relative_iff hbar c m hU hψ hc]
  simp_rw [diracField_eq_zero_iff]

/-- With an integrable background, the ordinary and relative actions have the same stationary fields. -/
theorem absolute_iff_relative (hU : IsOpen U) (hbase : IntegrableOn (dens hbar c m ψ) U) :
    AbsoluteStationary hbar c m U ψ ↔ RelativeStationary hbar c m U ψ := by
  constructor <;> intro h V
  · have hzero := (DiracActionIntegrationByParts.hasDerivAt_action hbar c m V hU hbase).unique (h V)
    simpa only [hzero] using DiracActionIntegrationByParts.hasDerivAt_relative hbar c m V hU
  · have hzero := (DiracActionIntegrationByParts.hasDerivAt_relative hbar c m V hU).unique (h V)
    simpa only [hzero] using DiracActionIntegrationByParts.hasDerivAt_action hbar c m V hU hbase

/-- Ordinary finite-action stationarity gives the pointwise Dirac equation and conversely. -/
theorem absolute_iff (hU : IsOpen U) (hψ : ∀ x ∈ U, ContDiffAt ℝ ∞ ψ x) (hc : c ≠ 0)
    (hbase : IntegrableOn (dens hbar c m ψ) U) :
    AbsoluteStationary hbar c m U ψ ↔ ∀ x ∈ U, diracField hbar m c ψ x = 0 :=
  (absolute_iff_relative hbar c m hU hbase).trans (relative_iff hbar c m hU hψ hc)

/-- Every Dirac solution has finite ordinary action and is stationary along admissible variations. -/
theorem absolute_of_equation (hU : IsOpen U) (he : ∀ x ∈ U, diracField hbar m c ψ x = 0) :
    AbsoluteStationary hbar c m U ψ :=
  (absolute_iff_relative hbar c m hU
    (DiracOnShellDensity.integrableOn_dens hbar c m hU.measurableSet he)).mpr
      (relative_of_equation hbar c m hU he)

/-- Finiteness and stationarity together characterize solutions without a separate
integrability hypothesis on the background. -/
theorem finite_stationary_iff (hU : IsOpen U) (hψ : ∀ x ∈ U, ContDiffAt ℝ ∞ ψ x) (hc : c ≠ 0) :
    (IntegrableOn (dens hbar c m ψ) U ∧ AbsoluteStationary hbar c m U ψ) ↔
      ∀ x ∈ U, diracField hbar m c ψ x = 0 := by
  constructor
  · rintro ⟨hfin, hstat⟩
    exact (absolute_iff hbar c m hU hψ hc hfin).mp hstat
  · intro he
    exact ⟨DiracOnShellDensity.integrableOn_dens hbar c m hU.measurableSet he,
      absolute_of_equation hbar c m hU he⟩

end FoliationQM.DiracStationaryAction
