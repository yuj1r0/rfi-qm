module

public import FoliationQM.CanonicalCompletion
public import FoliationQM.PuncturedPlaneDetour

/-!
# Intrinsic curve distance and the canonical source metric

Sources: v13 `lem:uniqueness`, `eq:unique_params`, and
`eq:master_local_metric`, canonical branch. The distance is an infimum of
integrals of the actual derivative speeds of nonvanishing `C¹` curves with
specified endpoints in the global complex coordinate. Arbitrarily short
polynomial detours prove that this intrinsic distance equals the previously
constructed metric. Thus its genuine completion is the completion of this
concrete curve-length metric as well.

On a real phase chart, the actual speed and its length integral agree with
the canonical source tensor `dρ²/(4ρ) + ρ dΦ²`. Local `C¹` regularity is
required at every point of the closed parameter interval, and positivity is
required only on that interval. No noncanonical cone completion or general
manifold theorem is asserted.
-/
@[expose] public section

noncomputable section

namespace FoliationQM.CanonicalConeGeometry

open CanonicalPolarMetric PolarDifferential PuncturedPlaneDetour
open Set MeasureTheory
open scoped ENNReal

/-- Intrinsic distance integrates actual speeds of all nonvanishing `C¹`
curves between the two physical-circle points in their global coordinate. -/
def intrinsicEDist (p q : Point) : ℝ≥0∞ :=
  PuncturedPlaneDetour.intrinsicEDist (toComplex p) (toComplex q)

/-- The infimum of actual curve lengths equals the canonical metric. -/
theorem intrinsicEDist_eq_edist (p q : Point) : intrinsicEDist p q = edist p q := by
  rw [intrinsicEDist,
    PuncturedPlaneDetour.intrinsicEDist_eq_edist (toComplex_ne_zero p) (toComplex_ne_zero q)]
  exact isometry_toComplex.edist_eq p q

/-- The actual curve-length infimum is finite for every pair of points. -/
theorem intrinsicEDist_ne_top (p q : Point) : intrinsicEDist p q ≠ ⊤ := by
  rw [intrinsicEDist_eq_edist]
  exact edist_ne_top p q

/-- The real intrinsic distance comes from the proved finite curve infimum. -/
def intrinsicDist (p q : Point) : ℝ := (intrinsicEDist p q).toReal

/-- The finite intrinsic curve distance equals the actual canonical distance. -/
theorem intrinsicDist_eq_dist (p q : Point) : intrinsicDist p q = dist p q := by
  rw [intrinsicDist, intrinsicEDist_eq_edist, edist_dist, ENNReal.toReal_ofReal dist_nonneg]

/-- The dense embedding into the genuine canonical completion preserves
the concrete intrinsic curve-length distance. -/
theorem completion_dist_eq_intrinsicDist (p q : Point) :
    dist (p : CanonicalCompletion.Completed) (q : CanonicalCompletion.Completed) =
      intrinsicDist p q := by
  rw [UniformSpace.Completion.dist_eq, intrinsicDist_eq_dist]

/-- The speed obtained from the canonical source metric tensor. -/
def sourceSpeed (ρ Φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.sqrt ((deriv ρ t) ^ 2 / (4 * ρ t) + ρ t * (deriv Φ t) ^ 2)

/-- The norm of the actual derivative equals the source metric speed on
every differentiable positive-density real phase chart. -/
theorem norm_deriv_polarField {ρ Φ : ℝ → ℝ} {t : ℝ}
    (hρ : DifferentiableAt ℝ ρ t) (hΦ : DifferentiableAt ℝ Φ t) (hpos : 0 < ρ t) :
    ‖deriv (polarField ρ Φ) t‖ = sourceSpeed ρ Φ t := by
  have hsq := fderiv_polarField_norm_sq hρ hΦ hpos (1 : ℝ)
  simp only [fderiv_apply_one_eq_deriv] at hsq
  rw [sourceSpeed, ← hsq]
  exact (Real.sqrt_sq (norm_nonneg _)).symm

/-- Local `C¹` density and phase on the closed interval, with positive
density there, make the actual source metric speed genuinely integrable. -/
theorem integrableOn_sourceSpeed {ρ Φ : ℝ → ℝ}
    (hρ : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 1 ρ t)
    (hΦ : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 1 Φ t)
    (hpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < ρ t) :
    IntegrableOn (sourceSpeed ρ Φ) (Icc 0 1) := by
  have hcρ : ContinuousOn ρ (Icc 0 1) :=
    fun t ht => (hρ t ht).continuousAt.continuousWithinAt
  have hcdρ : ContinuousOn (deriv ρ) (Icc 0 1) :=
    fun t ht => ((hρ t ht).derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  have hcdΦ : ContinuousOn (deriv Φ) (Icc 0 1) :=
    fun t ht => ((hΦ t ht).derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  have hc : ContinuousOn (sourceSpeed ρ Φ) (Icc 0 1) :=
    (((hcdρ.pow 2).div (continuousOn_const.mul hcρ)
      (fun t ht => mul_ne_zero (by norm_num) (ne_of_gt (hpos t ht)))).add
      (hcρ.mul (hcdΦ.pow 2))).sqrt
  exact hc.integrableOn_Icc

/-- The actual extended length of the polar curve is exactly the integral
of the canonical source metric speed, with no finiteness premise. -/
theorem curveELength_polarField {ρ Φ : ℝ → ℝ}
    (hρ : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ ρ t)
    (hΦ : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ Φ t)
    (hpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < ρ t) :
    curveELength (polarField ρ Φ) =
      ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal (sourceSpeed ρ Φ t) := by
  apply setLIntegral_congr_fun measurableSet_Icc
  intro t ht
  dsimp only
  rw [← ofReal_norm, norm_deriv_polarField (hρ t ht) (hΦ t ht) (hpos t ht)]

/-- Under local `C¹` hypotheses the extended curve length is the ordinary
real integral of the source speed, whose integrability is proved above. -/
theorem curveELength_polarField_eq_integral {ρ Φ : ℝ → ℝ}
    (hρ : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 1 ρ t)
    (hΦ : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 1 Φ t)
    (hpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < ρ t) :
    curveELength (polarField ρ Φ) =
      ENNReal.ofReal (∫ t in Icc (0 : ℝ) 1, sourceSpeed ρ Φ t) := by
  rw [curveELength_polarField
    (fun t ht => (hρ t ht).differentiableAt (by norm_num))
    (fun t ht => (hΦ t ht).differentiableAt (by norm_num)) hpos]
  exact (ofReal_integral_eq_lintegral_ofReal (integrableOn_sourceSpeed hρ hΦ hpos)
    (Filter.Eventually.of_forall fun t => Real.sqrt_nonneg _)).symm

/-- Every local `C¹` positive-density real phase curve is admissible for the
actual intrinsic-distance infimum, with precisely its polar endpoints. -/
theorem admissible_polarField {ρ Φ : ℝ → ℝ}
    (hρ : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 1 ρ t)
    (hΦ : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 1 Φ t)
    (hpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < ρ t) :
    Admissible
      (toComplex (ofLift (ρ 0) (Φ 0) (hpos 0 ⟨le_rfl, zero_le_one⟩)))
      (toComplex (ofLift (ρ 1) (Φ 1) (hpos 1 ⟨zero_le_one, le_rfl⟩)))
      (polarField ρ Φ) := by
  refine ⟨?_, rfl, rfl, ?_⟩
  · intro t ht
    have hR := Complex.ofRealCLM.contDiff.contDiffAt.comp t
      ((hρ t ht).sqrt (ne_of_gt (hpos t ht)))
    have hΦc := Complex.ofRealCLM.contDiff.contDiffAt.comp t (hΦ t ht)
    exact (hR.mul ((hΦc.mul (contDiffAt_const (c := Complex.I))).cexp)).contDiffWithinAt
  · intro t ht
    exact toComplex_ne_zero (ofLift (ρ t) (Φ t) (hpos t ht))

end FoliationQM.CanonicalConeGeometry
