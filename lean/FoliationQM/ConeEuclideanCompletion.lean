module

public import FoliationQM.ConeEuclideanRigidity
public import FoliationQM.ConeTangentialDistance
public import FoliationQM.ConeTangentialUpper
public import FoliationQM.PowerConeCompletion
public import FoliationQM.GeneralCouplingExample

/-!
# Unrestricted Euclidean isometric completion iff canonical coupling

Sources: v13 `lem:uniqueness` and `eq:unique_params`. The completed space is
the genuine completion of the actual intrinsic source metric. The Euclidean
isometry is arbitrary: no power formula, chosen angular coordinate, or
tip-image condition is required. Local bounds from actual C1 paths force
the scale left by the independent rotation/radial rigidity theorem to be one.
The canonical isometry supplies the converse. This is a global metric
completion theorem; arbitrary local smooth-atlas extensions are a separate
notion and are not built into the statement.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.ConeEuclideanCompletion

open ConeCompletion ConeRadial
open scoped ContDiff

variable (hbar coupling : ℝ) [Fact (0 < hbar)] [Fact (0 < coupling)]

/-- The genuine local tangential metric rules out every nonunit constant
scaling of physical chord distance, in both directions. -/
theorem scale_eq_one_of_dist_eq (a : ℝ) (ha : 0 < a)
    (hdist : ∀ p q : ConeManifold.Point hbar coupling,
      dist p q = a * dist p.value q.value) : a = 1 :=
  le_antisymm (ConeTangentialUpper.scale_le_one_of_dist_eq hbar coupling a ha hdist)
    (ConeTangentialDistance.one_le_scale_of_dist_eq hbar coupling a ha hdist)

/-- Any Euclidean isometric equivalence of the genuine completed cone forces
canonical coupling, without any prescribed coordinate or image of the tip. -/
theorem coupling_eq_canonical_of_isometry (E : Completed hbar coupling ≃ᵢ ℂ) :
    coupling = hbar ^ 2 / 4 := by
  apply (radialScale_eq_one_iff hbar coupling Fact.out).mp
  apply scale_eq_one_of_dist_eq hbar coupling (radialScale hbar coupling)
    (radialScale_pos hbar coupling Fact.out Fact.out)
  intro p q
  have h := ConeEuclideanRigidity.dist_eq_scaled_chord_of_isometry hbar coupling E
    (p : Completed hbar coupling) (q : Completed hbar coupling)
  simpa only [UniformSpace.Completion.dist_eq, coordinate_coe] using h

/-- The actual intrinsic cone completion is Euclidean isometrically exactly
at canonical coupling. This quantifies over all isometric equivalences. -/
theorem nonempty_isometry_iff :
    Nonempty (Completed hbar coupling ≃ᵢ ℂ) ↔ coupling = hbar ^ 2 / 4 := by
  constructor
  · rintro ⟨E⟩
    exact coupling_eq_canonical_of_isometry hbar coupling E
  · intro hc
    exact ⟨PowerConeCompletion.canonicalCompletionIsometry hbar coupling hc⟩

/-- Every noncanonical positive coupling excludes all Euclidean isometric
equivalences of the completed cone, not only the stipulated power family. -/
theorem no_isometry_of_noncanonical (hc : coupling ≠ hbar ^ 2 / 4) :
    ¬Nonempty (Completed hbar coupling ≃ᵢ ℂ) :=
  fun h => hc ((nonempty_isometry_iff hbar coupling).mp h)

/-- The source cone-angle criterion is equivalent to actual unrestricted
Euclidean isometric completion; no circumference-invariance premise is used. -/
theorem nonempty_isometry_iff_coneAngle :
    Nonempty (Completed hbar coupling ≃ᵢ ℂ) ↔
      MasterMetricAndCone.coneAngle hbar coupling = 2 * Real.pi :=
  (nonempty_isometry_iff hbar coupling).trans
    (MasterMetricAndCone.coneAngle_eq_two_pi_iff hbar coupling Fact.out Fact.out).symm

/-- Unrestricted Euclidean completion and the canonical Born exponent give
exactly the existing actual completed-isometry witness in the source power family. -/
theorem power_completion_iff_unrestricted_and_exponent (α : ℝ) :
    (∃ E : Completed hbar coupling ≃ᵢ ℂ,
      E (tip hbar coupling) = 0 ∧
      ∀ p : ConeManifold.Point hbar coupling,
        E (p : Completed hbar coupling) = PowerConeCompletion.powerCoordinate hbar coupling α p) ↔
      Nonempty (Completed hbar coupling ≃ᵢ ℂ) ∧ α = 1 / 2 := by
  rw [PowerConeCompletion.exists_power_isometric_completion_iff, nonempty_isometry_iff]
  exact and_comm

/-- The global metric-completion selection and universal physical-clock
linearization of smooth positive stationary fields are the same criterion.
The stationary equations and the noncanonical witness were independently proved. -/
theorem completion_iff_universal_linearization (p : MassiveParameters) [Fact (0 < p.hbar)] :
    Nonempty (Completed p.hbar coupling ≃ᵢ ℂ) ↔
      (∀ ρ S : Covector → ℝ, ContDiff ℝ ∞ ρ → ContDiff ℝ ∞ S →
        (∀ x, 0 < ρ x) →
        GeneralCouplingStationarity.RelativeStationaryOn p coupling ρ S
          Madelung.coordinateVector Set.univ →
        ∀ x, PolarSecondDifferential.box (ActionDensity.actionField p ρ S)
          Madelung.coordinateVector x +
          (((p.m ^ 2 * p.c ^ 2 / p.hbar ^ 2 : ℝ) : ℂ) *
            ActionDensity.actionField p ρ S x) = 0) :=
  (nonempty_isometry_iff p.hbar coupling).trans
    (GeneralCouplingExample.every_stationary_field_linear_iff_canonical p
      (lam := coupling) Fact.out).symm

end FoliationQM.ConeEuclideanCompletion
