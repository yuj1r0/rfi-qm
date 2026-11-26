module

public import FoliationQM.CurvedCoordinateDynamics
public import FoliationQM.CurvedAuxiliaryNorm
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Regularity of the actual force and full spacetime gradient

The true covariant acceleration is continuous for C² metric and C¹ velocity
data. Coordinate-time conversion preserves continuity on its nonzero
temporal domain. The auxiliary gradient uses every component of the actual
Fréchet differential. For a fixed continuous nonsingular background on a
compact region, continuity also produces a positive uniform bound on the
same inverse-metric raising operator used in the force estimates.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedForceRegularity

open LorentzMatrixGroup RNCCoordinateConnection CurvedGradientCovariance CurvedConnectionComponents
  CurvedCovariantDerivative CurvedCoordinateDynamics CurvedAuxiliaryNorm ContinuousLinearMap
open scoped Topology Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false

variable {g : Covector → Mat4} {U : Covector → Covector} {q : Covector → ℝ} {x : Covector}

/-- The genuine covariant acceleration is continuous for a C² nonsingular metric and a C¹ vector field. -/
theorem continuousAt_acceleration (hg : ContDiffAt ℝ 2 g x) (hu : IsUnit (g x).det)
    (hU : ContDiffAt ℝ 1 U x) : ContinuousAt (acceleration g U) x := by
  have hD := (hU.continuousAt_fderiv (by decide)).clm_apply hU.continuousAt
  have hΓ := (((contDiffAt_connectionBilin hg
    ((g x).isUnit_iff_isUnit_det.mpr hu)).continuousAt.clm_apply hU.continuousAt).clm_apply
      hU.continuousAt)
  exact hD.add hΓ

/-- The coordinate force formed from the actual covariant acceleration is continuous wherever the temporal velocity component is nonzero. -/
theorem continuousAt_coordinateForce (c : ℝ) (hg : ContDiffAt ℝ 2 g x)
    (hu : IsUnit (g x).det) (hU : ContDiffAt ℝ 1 U x) (h0 : U x 0 ≠ 0) :
    ContinuousAt (coordinateForce c g U) x := by
  have ha := continuousAt_acceleration hg hu hU
  have ht : ContinuousAt (fun y => U y 0) x :=
    (proj 0 : Covector →L[ℝ] ℝ).continuous.continuousAt.comp hU.continuousAt
  have hat : ContinuousAt (fun y => acceleration g U y 0) x :=
    (proj 0 : Covector →L[ℝ] ℝ).continuous.continuousAt.comp ha
  change ContinuousAt (fun y => (c ^ 2 / (U y 0) ^ 2) •
    (acceleration g U y - (acceleration g U y 0 / U y 0) • U y)) x
  exact (continuousAt_const.div (ht.pow 2) (pow_ne_zero 2 h0)).smul
    (ha.sub ((hat.div ht h0).smul hU.continuousAt))

/-- All four components of the actual spacetime differential vary continuously for a C¹ scalar field. -/
theorem continuousAt_components (hq : ContDiffAt ℝ 1 q x) :
    ContinuousAt (CurvedGradientCovariance.components q) x := by
  apply continuousAt_pi.mpr
  intro i
  exact (apply ℝ ℝ (axis i)).continuous.continuousAt.comp
    (hq.continuousAt_fderiv (by decide))

/-- The full actual spacetime differential is continuous as a vector in the fixed Euclidean auxiliary covector space. -/
theorem continuousAt_auxGradient (hq : ContDiffAt ℝ 1 q x) :
    ContinuousAt (fun y => (WithLp.toLp 2 (CurvedGradientCovariance.components q y) :
      EuclideanSpace ℝ (Fin 4))) x :=
  (PiLp.continuous_toLp 2 (fun _ : Fin 4 => ℝ)).continuousAt.comp (continuousAt_components hq)

/-- The Euclidean norm of the full actual spacetime differential is continuous for a C¹ scalar field. -/
theorem continuousAt_gradientNorm (hq : ContDiffAt ℝ 1 q x) :
    ContinuousAt (fun y => norm2 (CurvedGradientCovariance.components q y)) x :=
  (continuousAt_auxGradient hq).norm

/-- A continuous nonsingular metric gives a continuous actual inverse-metric raising operator. -/
theorem continuousAt_inverse_raise (hg : ContinuousAt g x) (hu : IsUnit (g x).det) :
    ContinuousAt (fun y => raiseMap ((g y)⁻¹)) x := by
  have hi := (LorentzCayleySmooth.contDiffAt_inverse 0
    ((g x).isUnit_iff_isUnit_det.mpr hu)).continuousAt.comp hg
  exact matrixRaiseMap.continuous.continuousAt.comp hi

/-- Continuity and pointwise nonsingularity of the metric on a region make the actual inverse-raising operator continuous on that region. -/
theorem continuousOn_inverse_raise {K : Set Covector} (hg : ContinuousOn g K)
    (hu : ∀ x ∈ K, IsUnit (g x).det) :
    ContinuousOn (fun y => raiseMap ((g y)⁻¹)) K := by
  intro x hx
  have hi := (LorentzCayleySmooth.contDiffAt_inverse 0
    ((g x).isUnit_iff_isUnit_det.mpr (hu x hx))).continuousAt.comp_continuousWithinAt (hg x hx)
  exact matrixRaiseMap.continuous.continuousAt.comp_continuousWithinAt hi

/-- A fixed continuous nonsingular metric on a compact region has a positive uniform bound on its actual inverse-raising operator norm. -/
theorem exists_inverse_raise_bound {K : Set Covector} (hK : IsCompact K)
    (hg : ContinuousOn g K) (hu : ∀ x ∈ K, IsUnit (g x).det) :
    ∃ Bg : ℝ, 0 < Bg ∧ ∀ x ∈ K, ‖raiseMap ((g x)⁻¹)‖ ≤ Bg := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (continuousOn_inverse_raise hg hu)
  refine ⟨max B 0 + 1, by positivity, ?_⟩
  intro x hx
  have hb := hB x hx
  have hm := le_max_left B 0
  linarith

end FoliationQM.CurvedForceRegularity
