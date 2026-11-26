module

public import FoliationQM.CoordinateAxisZeroExtension
public import FoliationQM.WeightedPolarEnergyL2

/-!
# A weak extension constructed from positive polar energy

Source: v13 `thm:wallstrom` Part (c), and the field/derivative L²
prerequisites of `eq:weak_pde_cutoff_bound`, component kinds C and D.
The supplied unit-circle phase and finite positive auxiliary-metric energy
give the actual zero extension and its coordinate L² derivatives on a compact
region. Every smooth compact test supported there satisfies the ambient weak
directional identity. No global real phase, Hilbert Sobolev membership or
general nodal geometry is assumed or asserted.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.CoordinateAxisPolarExtension

open MeasureTheory Set LorentzMatrixGroup RNCCoordinateConnection
open AuxiliaryMetricEnergy CirclePolarEnergy CoordinateAxisZeroExtension
open scoped ContDiff Topology Matrix.Norms.Operator

/-- Finite positive polar energy off the coordinate axis constructs an actual L² zero extension with L² coordinate derivatives and the ambient weak identity for every supported compact test and direction. -/
theorem polar_weak_extension {K : Set Covector} {H : Covector → Mat4}
    (hK : IsCompact K) (hH : ContinuousOn H K)
    (hpos : ∀ x ∈ K, (H x).PosDef)
    {R : Covector → ℝ} {q : Covector → ℂ}
    {dR α : Covector → Covector →L[ℝ] ℝ} {omega : ℝ}
    (hR : ∀ x ∈ K \ {y : Covector | y 2 = 0 ∧ y 3 = 0},
      HasFDerivAt R (dR x) x)
    (hq : ∀ x ∈ K \ {y : Covector | y 2 = 0 ∧ y 3 = 0},
      HasFDerivAt q ((α x).smulRight (-Complex.I * (omega : ℂ) * q x)) x)
    (hunit : ∀ x ∈ K \ {y : Covector | y 2 = 0 ∧ y 3 = 0}, ‖q x‖ = 1)
    (he : Integrable (fun x => (R x) ^ 2 +
      realEnergy (H x) (fun i => dR x (axis i)) +
      omega ^ 2 * (R x) ^ 2 * realEnergy (H x) (fun i => α x (axis i)))
      ((volume.restrict (K \ {y : Covector | y 2 = 0 ∧ y 3 = 0})).withDensity
        (fun x => ENNReal.ofReal (density (H x))))) :
    MemLp (zeroExtension (field R q)) 2 (volume.restrict K) ∧
    (∀ i : Fin 4, MemLp
      (fun x => fderiv ℝ (zeroExtension (field R q)) x (axis i)) 2
      (volume.restrict K)) ∧
    ∀ {φ : Covector → ℂ}, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ K → ∀ v : Covector,
      Integrable (fun x => star (fderiv ℝ φ x v) * zeroExtension (field R q) x)
        volume ∧
      Integrable (fun x => star (φ x) *
        fderiv ℝ (zeroExtension (field R q)) x v) volume ∧
      (∫ x, star (fderiv ℝ φ x v) * zeroExtension (field R q) x) =
        -(∫ x, star (φ x) * fderiv ℝ (zeroExtension (field R q)) x v) := by
  have hN : IsClosed {y : Covector | y 2 = 0 ∧ y 3 = 0} :=
    (isClosed_eq (continuous_apply 2) continuous_const).inter
      (isClosed_eq (continuous_apply 3) continuous_const)
  obtain ⟨hψ, hD⟩ := WeightedPolarEnergyL2.polar_memLp hK
    (hK.measurableSet.diff hN.measurableSet) sdiff_subset hH hpos hR hq hunit he
  obtain ⟨hu, hDu⟩ := memLp_data hψ hD
  refine ⟨hu, hDu, ?_⟩
  intro φ hφ hc hs v
  exact weak_identity hφ hc hs hψ hD
    (fun x hx => (hasFDerivAt_field (hR x hx) (hq x hx)).differentiableAt) v

end FoliationQM.CoordinateAxisPolarExtension
