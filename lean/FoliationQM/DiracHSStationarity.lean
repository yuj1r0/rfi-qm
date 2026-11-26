module
public import FoliationQM.DiracHSVariation

/-!
# Stationarity of the regular Hestenes–Takabayasi action

For v13 `thm:dirac_lift` and `eq:dirac_polar_lagrangian_main`, stationarity
is tested on actual families in the Clifford quotient manifold. On a smooth
regular flat domain it is equivalent to the Dirac equation. For the ordinary
action the finite stationary predicate includes integrability of its density.
-/

@[expose] public section
noncomputable section
open scoped Topology ContDiff Manifold
namespace FoliationQM.DiracHSStationarity
open MeasureTheory DiracMatrices DiracPolarCoordinates DiracPolarVariation
open DiracPolarVariationTransport DiracHSVariation DiracEquation

variable (hbar c m : ℝ)

/-- Every admissible quotient variation has zero relative polar-action derivative at zero. -/
def RelativeStationary (U : Set Covector) (q : Covector → Q) : Prop :=
  ∀ P : PolarVariation U q, HasDerivAt (fun t => DiracHSAction.relativeAction hbar c m q (slice P t) U) 0 0

/-- Vanishing of the ordinary polar-action derivative for every admissible quotient family. -/
def AbsoluteStationary (U : Set Covector) (q : Covector → Q) : Prop :=
  ∀ P : PolarVariation U q, HasDerivAt (fun t => DiracHSAction.action hbar c m (slice P t) U) 0 0

/-- Finiteness and ordinary stationarity for the polar action. -/
def FiniteStationary (U : Set Covector) (q : Covector → Q) : Prop :=
  IntegrableOn (DiracHSDensity.density hbar c m q) U ∧ AbsoluteStationary hbar c m U q

variable {U : Set Covector} {q : Covector → Q} {ψ : Covector → Spinor}
variable (hU : IsOpen U) (h : Represents U q ψ)
include hU h

/-- Polar and spinor relative stationarity are equivalent through their actual compact families. -/
theorem relative_iff_spinor :
    RelativeStationary hbar c m U q ↔ DiracStationaryAction.RelativeStationary hbar c m U ψ := by
  constructor
  · intro hs V
    exact (hs (DiracPolarTestRealization.lift hU h V)).congr_of_eventuallyEq
      (relative_lift hbar c m hU h V).symm
  · intro hs P
    exact (hs (toSpinor hU h P).toVariation).congr_of_eventuallyEq (relative_toSpinor hbar c m hU h P)

/-- Ordinary polar and spinor action derivatives test the same stationarity condition. -/
theorem absolute_iff_spinor :
    AbsoluteStationary hbar c m U q ↔ DiracStationaryAction.AbsoluteStationary hbar c m U ψ := by
  constructor
  · intro hs V
    exact (hs (DiracPolarTestRealization.lift hU h V)).congr_of_eventuallyEq
      (action_lift hbar c m hU h V).symm
  · intro hs P
    exact (hs (toSpinor hU h P).toVariation).congr_of_eventuallyEq (action_toSpinor hbar c m hU h P)

/-- For a locally smooth represented spinor, the relative polar action is stationary
exactly when the actual four-coordinate Dirac equation holds on U. -/
theorem relative_iff_dirac (hψ : ∀ x ∈ U, ContDiffAt ℝ ∞ ψ x) (hc : c ≠ 0) :
    RelativeStationary hbar c m U q ↔ ∀ x ∈ U, diracField hbar m c ψ x = 0 :=
  (relative_iff_spinor hbar c m hU h).trans (DiracStationaryAction.relative_iff hbar c m hU hψ hc)

/-- A Dirac solution gives finite polar action and ordinary stationarity with arbitrary real parameters. -/
theorem finite_of_equation (hψ : ∀ x ∈ U, ContDiffAt ℝ 1 ψ x)
    (he : ∀ x ∈ U, diracField hbar m c ψ x = 0) : FiniteStationary hbar c m U q :=
  ⟨(DiracHSAction.integrable_iff hbar c m hU h hψ).mpr (DiracOnShellDensity.integrableOn_dens hbar c m hU.measurableSet he),
    (absolute_iff_spinor hbar c m hU h).mpr (DiracStationaryAction.absolute_of_equation hbar c m hU he)⟩

/-- On ordinary finite-action fields, polar stationarity is equivalent to the pointwise Dirac equation. -/
theorem finite_iff_dirac (hψ : ∀ x ∈ U, ContDiffAt ℝ ∞ ψ x) (hc : c ≠ 0) :
    FiniteStationary hbar c m U q ↔ ∀ x ∈ U, diracField hbar m c ψ x = 0 := by
  have hc1 : ∀ x ∈ U, ContDiffAt ℝ 1 ψ x := fun x hx => (hψ x hx).of_le (by simp)
  constructor
  · rintro ⟨hb, hs⟩
    exact (DiracStationaryAction.finite_stationary_iff hbar c m hU hψ hc).mp
      ⟨(DiracHSAction.integrable_iff hbar c m hU h hc1).mp hb, (absolute_iff_spinor hbar c m hU h).mp hs⟩
  · exact finite_of_equation hbar c m hU h hc1

/-- The ordinary polar action has value zero on a represented Dirac solution. -/
theorem action_eq_zero_of_equation (hψ : ∀ x ∈ U, ContDiffAt ℝ 1 ψ x)
    (he : ∀ x ∈ U, diracField hbar m c ψ x = 0) : DiracHSAction.action hbar c m q U = 0 :=
  (DiracHSAction.action_eq hbar c m hU h hψ).trans (DiracOnShellDensity.action_eq_zero hbar c m he)

omit h in
/-- Intrinsic quotient-field statement, requiring only smoothness of the given quotient field on U. -/
theorem quotient_iff_dirac (hq : ∀ x ∈ U, ContMDiffAt 𝓘(ℝ,Covector) model ∞ q x) (hc : c ≠ 0) :
    (RelativeStationary hbar c m U q ↔ ∀ x ∈ U, diracField hbar m c (fun y => decode (q y)) x = 0) ∧
    (FiniteStationary hbar c m U q ↔ ∀ x ∈ U, diracField hbar m c (fun y => decode (q y)) x = 0) := by
  have hr : Represents U q (fun y => decode (q y)) := fun _ _ => rfl
  have hd := fun x hx => contDiffAt_decode (hq x hx)
  exact ⟨relative_iff_dirac hbar c m hU hr hd hc, finite_iff_dirac hbar c m hU hr hd hc⟩

omit h in
/-- Starting from a spinor regular only on U, its encoded polar action is stationary
exactly when the Dirac equation holds for its true first derivatives there. -/
theorem encoded_iff_jetEquation (hr : ∀ x ∈ U, SpinorRegularity.Regular (ψ x))
    (hψ : ∀ x ∈ U, ContDiffAt ℝ ∞ ψ x) (hc : c ≠ 0) :
    RelativeStationary hbar c m U (fun y => encode (ψ y)) ↔ ∀ x ∈ U,
      jetEquation hbar m c (ψ x) (fun μ => fderiv ℝ ψ x (DiracFieldDensity.coordinateDirections μ)) := by
  rw [relative_iff_dirac hbar c m hU (encode_represents hr) hψ hc]
  simp_rw [diracField_eq_zero_iff]

end FoliationQM.DiracHSStationarity
