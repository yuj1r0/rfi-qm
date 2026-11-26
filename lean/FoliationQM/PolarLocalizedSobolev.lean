module

public import FoliationQM.LocalizedCoordinateSobolev
public import FoliationQM.CoordinateAxisPolarExtension

/-!
# Localized Sobolev regularity from positive polar energy

Source: v13 `thm:wallstrom` Part (c), component kinds C and D.
Actual positive polar energy supplies the constructed zero extension's local
L² data and compact-test weak derivatives. Smooth compact localizations,
transported to the genuine Euclidean product space, therefore belong to the
pinned Fourier-Bessel H¹ space. Energy on every compact subset gives this
conclusion for every localizer supported in the region. No distributional
derivative equality or Sobolev membership is assumed. General nodal geometry,
intrinsic chart independence, weak-PDE composition and Cauchy conclusions
remain separate.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.CoordinateAxisPolarExtension

open MeasureTheory Set LorentzMatrixGroup RNCCoordinateConnection
open AuxiliaryMetricEnergy CirclePolarEnergy CoordinateAxisZeroExtension
open ProductTubeCoordinates TemperedDistribution
open scoped ContDiff Topology SchwartzMap Matrix.Norms.Operator

local notation "Space" => WithLp 2 (ℂ × ℂ)

/-- Finite positive polar energy gives genuine H¹ membership of every smooth compact localization of the constructed zero extension, transported by the actual Hilbert coordinate equivalence. -/
theorem polar_localized_memSobolev {K : Set Covector} {H : Covector → Mat4}
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
        (fun x => ENNReal.ofReal (density (H x)))))
    {η : Covector → ℂ} (hη : ContDiff ℝ ∞ η)
    (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ K) :
    ∃ hf : MemLp (fun y : Space => η (coordinates.symm y) *
        zeroExtension (field R q) (coordinates.symm y)) 2 volume,
      MemSobolev 1 2 (hf.toLp _ : 𝓢'(Space, ℂ)) := by
  obtain ⟨hu, hDu, hweak⟩ := polar_weak_extension hK hH hpos hR hq hunit he
  exact LocalizedCoordinateSobolev.localized_memSobolev
    hK.measurableSet hu hDu hweak hη hcη hsη

/-- Positive polar energy on every compact subset gives actual H¹ for every supported smooth compact localization of the same zero extension, without openness or an assumed weak derivative identity. -/
theorem polar_localizations_memSobolev {U : Set Covector} {H : Covector → Mat4}
    (hH : ContinuousOn H U) (hpos : ∀ x ∈ U, (H x).PosDef)
    {R : Covector → ℝ} {q : Covector → ℂ}
    {dR α : Covector → Covector →L[ℝ] ℝ} {omega : ℝ}
    (hR : ∀ x ∈ U \ {y : Covector | y 2 = 0 ∧ y 3 = 0},
      HasFDerivAt R (dR x) x)
    (hq : ∀ x ∈ U \ {y : Covector | y 2 = 0 ∧ y 3 = 0},
      HasFDerivAt q ((α x).smulRight (-Complex.I * (omega : ℂ) * q x)) x)
    (hunit : ∀ x ∈ U \ {y : Covector | y 2 = 0 ∧ y 3 = 0}, ‖q x‖ = 1)
    (he : ∀ K : Set Covector, IsCompact K → K ⊆ U →
      Integrable (fun x => (R x) ^ 2 +
        realEnergy (H x) (fun i => dR x (axis i)) +
        omega ^ 2 * (R x) ^ 2 * realEnergy (H x) (fun i => α x (axis i)))
        ((volume.restrict (K \ {y : Covector | y 2 = 0 ∧ y 3 = 0})).withDensity
          (fun x => ENNReal.ofReal (density (H x))))) :
    ∀ {η : Covector → ℂ}, ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ U →
      ∃ hf : MemLp (fun y : Space => η (coordinates.symm y) *
          zeroExtension (field R q) (coordinates.symm y)) 2 volume,
        MemSobolev 1 2 (hf.toLp _ : 𝓢'(Space, ℂ)) := by
  intro η hη hcη hsη
  have hK : IsCompact (tsupport η) := hcη.isCompact
  exact polar_localized_memSobolev hK (hH.mono hsη)
    (fun x hx => hpos x (hsη hx))
    (fun x hx => hR x ⟨hsη hx.1, hx.2⟩)
    (fun x hx => hq x ⟨hsη hx.1, hx.2⟩)
    (fun x hx => hunit x ⟨hsη hx.1, hx.2⟩)
    (he (tsupport η) hK hsη) hη hcη subset_rfl

end FoliationQM.CoordinateAxisPolarExtension
