module

public import FoliationQM.CurvedEuclideanTrajectories
public import FoliationQM.PhaseTrajectoryEstimate

/-!
# Quantitative Euclidean bounds for actual KG coordinate trajectories

The actual first-order normalized KG path supplies both Euclidean phase
equations. Metric and KG regularity derive the needed along-curve
integrability. A supplied classical reference curve and an explicit common
no-exit phase region retain the source hypotheses. The final specialization
constructs the force envelope from the actual full defect-gradient supremum;
neither an acceleration equation nor that force bound is assumed.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedPhaseTrajectoryBound

open LorentzMatrixGroup CurvedCoordinateVelocity CurvedCoordinateDynamics
  CurvedCoordinateTrajectories CurvedNormalizedQuantumForce CurvedPolarKG
  CurvedQuantumForceBound CurvedQuantumForceCriterion CurvedDefectSupremum
  CurvedEuclideanTrajectories WeightedPhaseError MeasureTheory Set
open scoped Topology Matrix.Norms.Operator

variable (p : MassiveParameters) {g : Covector → Mat4} {R S : Covector → ℝ}
  {γ : ℝ → Covector} {Y W : ℝ → EuclideanSpace ℝ (Fin 3)} {T Lx Lv : ℝ}
  {Ω : ℝ → Set (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))}

variable (hT : 0 < T) (hLx : 0 ≤ Lx) (hLv : 0 ≤ Lv)
  (hγ : ContinuousOn γ (Icc 0 T))
  (hY : ContinuousOn Y (Icc 0 T)) (hW : ContinuousOn W (Icc 0 T))
  (hreg : ∀ s ∈ Icc 0 T, RegularPolarAt p g R S (γ s))
  (hq : ∀ s ∈ Icc 0 T, 0 < 1 + defect p g R (γ s))
  (h0 : ∀ s ∈ Icc 0 T, normalizedVelocity p g R S (γ s) 0 ≠ 0)
  (hODE : ∀ s ∈ Ioo 0 T,
    HasDerivAt γ (coordinateVelocity p.c (normalizedVelocity p g R S) (γ s)) s)
  (htime : ∀ s ∈ Icc 0 T, γ s 0 = p.c * s)
  (hmetricY : ∀ s ∈ Icc 0 T,
    ContDiffAt ℝ 2 g (coordinatePoint p.c s (WithLp.ofLp (Y s))))
  (hunitY : ∀ s ∈ Icc 0 T, IsUnit (g (coordinatePoint p.c s (WithLp.ofLp (Y s)))).det)
  (hYODE : ∀ s ∈ Ioo 0 T, HasDerivAt Y (W s) s)
  (hWODE : ∀ s ∈ Ioo 0 T, HasDerivAt W (geodesic p.c g s (Y s) (W s)) s)
  (hXm : ∀ s ∈ Icc 0 T, (position γ s, velocity p g R S γ s) ∈ Ω s)
  (hYm : ∀ s ∈ Icc 0 T, (Y s, W s) ∈ Ω s)
  (hG : ∀ s ∈ Icc 0 T, ∀ z ∈ Ω s, ∀ w ∈ Ω s,
    ‖geodesic p.c g s z.1 z.2 - geodesic p.c g s w.1 w.2‖ ≤
      Lx * ‖z.1 - w.1‖ + Lv * ‖z.2 - w.2‖)

include hT hLx hLv hγ hY hW hreg hq h0 hODE htime hmetricY hunitY
  hYODE hWODE hXm hYm hG

/-- An actual first-order KG coordinate path satisfies the exact source weighted phase bound under a common no-exit region and an almost-everywhere bound on its actual spatial force. -/
theorem phase_error_bound {A : ℝ → ℝ}
    (hf : ∀ᵐ s ∂volume.restrict (Icc 0 T),
      spatialForceNorm p g R S s (spatialPart (γ s)) ≤ A s)
    (hA : IntervalIntegrable A volume 0 T) (hAn : ∀ s ∈ Icc 0 T, 0 ≤ A s) :
    ∀ t ∈ Icc 0 T,
      ‖position γ t - Y t‖ + T * ‖velocity p g R S γ t - W t‖ ≤
        Real.exp (rate T Lx Lv * T) *
          (‖position γ 0 - Y 0‖ + T * ‖velocity p g R S γ 0 - W 0‖ +
            T * ∫ s in 0..T, A s) := by
  have hXc := continuousOn_position hγ
  have hVc := continuousOn_velocity hγ hreg hq h0
  have hfc := continuousOn_force hγ hreg hq h0
  have hGX : ContinuousOn (fun s => geodesic p.c g s (position γ s)
      (velocity p g R S γ s)) (Icc 0 T) := by
    apply continuousOn_geodesic p.c g hXc hVc
    · intro s hs
      change ContDiffAt ℝ 2 g (coordinatePoint p.c s (spatialPart (γ s)))
      rw [← reconstruct_position p.c s (γ s) (htime s hs)]
      exact (hreg s hs).metric_C2
    · intro s hs
      change IsUnit (g (coordinatePoint p.c s (spatialPart (γ s)))).det
      rw [← reconstruct_position p.c s (γ s) (htime s hs)]
      exact isUnit_iff_ne_zero.mpr (hreg s hs).det_neg.ne
  have hGY := continuousOn_geodesic p.c g hY hW hmetricY hunitY
  have hforce : ∀ᵐ s ∂volume.restrict (Icc 0 T), ‖force p g R S γ s‖ ≤ A s := by
    filter_upwards [hf, ae_restrict_mem measurableSet_Icc] with s hs hmem
    rw [force_norm p g R S (htime s hmem)]
    exact hs
  exact PhaseTrajectoryEstimate.phase_error_bound_of_continuous hT hLx hLv
    hXc hY hVc hW
    (fun s hs => hasDerivAt_position p g R S (hODE s hs)) hYODE
    (fun s hs => hasDerivAt_velocity (hreg s (Ioo_subset_Icc_self hs))
      (hq s (Ioo_subset_Icc_self hs)) (h0 s (Ioo_subset_Icc_self hs))
      (hODE s hs) (htime s (Ioo_subset_Icc_self hs))) hWODE
    hGX hGY hfc
    (PhaseTrajectoryEstimate.endpoint_bound_of_no_exit hXm hYm hG) hforce hA hAn

/-- The actual Euclidean position stays within the same exact integrated-force bound as the weighted phase error. -/
theorem position_error_bound {A : ℝ → ℝ}
    (hf : ∀ᵐ s ∂volume.restrict (Icc 0 T),
      spatialForceNorm p g R S s (spatialPart (γ s)) ≤ A s)
    (hA : IntervalIntegrable A volume 0 T) (hAn : ∀ s ∈ Icc 0 T, 0 ≤ A s) :
    ∀ t ∈ Icc 0 T, ‖position γ t - Y t‖ ≤
      Real.exp (rate T Lx Lv * T) *
        (‖position γ 0 - Y 0‖ + T * ‖velocity p g R S γ 0 - W 0‖ +
          T * ∫ s in 0..T, A s) := by
  intro t ht
  have H := phase_error_bound p hT hLx hLv hγ hY hW hreg hq h0 hODE htime
    hmetricY hunitY hYODE hWODE hXm hYm hG hf hA hAn t ht
  have hv := mul_nonneg hT.le (norm_nonneg (velocity p g R S γ t - W t))
  linarith

/-- The computed full defect-gradient supremum supplies the actual force envelope and hence the position estimate, without assuming a force bound or a second-order KG trajectory equation. -/
theorem position_error_bound_of_gradientSup
    (K : ℝ → Set (Fin 3 → ℝ))
    (hregTube : RegularOnTube p g R S T K)
    (hDbnd : DifferentialBoundedOnTube p g R T K)
    (hspatial : ∀ s ∈ Icc 0 T, spatialPart (γ s) ∈ K s)
    {umin δ Bv Bg : ℝ} (hmin : 0 < umin) (hδ : 0 < δ)
    (hBv : 0 ≤ Bv) (hBg : 0 ≤ Bg)
    (hu : ∀ s ∈ Icc 0 T, umin ≤ |normalizedVelocity p g R S (γ s) 0|)
    (hδq : ∀ s ∈ Icc 0 T, δ ≤ 1 + defect p g R (γ s))
    (hratio : ∀ s ∈ Icc 0 T, ∀ j : Fin 3,
      |normalizedVelocity p g R S (γ s) j.succ / normalizedVelocity p g R S (γ s) 0| ≤ Bv)
    (hraise : ∀ s ∈ Icc 0 T, ‖CurvedAuxiliaryNorm.raiseMap ((g (γ s))⁻¹)‖ ≤ Bg)
    (hBInt : IntervalIntegrable (gradientSup p g R S T K hregTube hDbnd) volume 0 T) :
    ∀ t ∈ Icc 0 T, ‖position γ t - Y t‖ ≤
      Real.exp (rate T Lx Lv * T) *
        (‖position γ 0 - Y 0‖ + T * ‖velocity p g R S γ 0 - W 0‖ +
          T * ((sourceCoefficient p.c umin δ Bv Bg * p.c ^ 2) *
            ∫ s in 0..T, gradientSup p g R S T K hregTube hDbnd s)) := by
  let C := sourceCoefficient p.c umin δ Bv Bg * p.c ^ 2
  let B := gradientSup p g R S T K hregTube hDbnd
  have hC : 0 ≤ C := mul_nonneg (sourceCoefficient_pos hmin hδ hBv hBg).le (sq_nonneg p.c)
  have hforce : ∀ᵐ s ∂volume.restrict (Icc 0 T),
      spatialForceNorm p g R S s (spatialPart (γ s)) ≤ C * B s := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    have he : coordinatePoint p.c s (spatialPart (γ s)) = γ s :=
      (reconstruct_position p.c s (γ s) (htime s hs)).symm
    exact point_force_le p g R S T K hregTube hDbnd hs (hspatial s hs)
      hmin hδ hBv hBg (by simpa only [he] using hu s hs)
      (by simpa only [he] using hδq s hs)
      (by simpa only [he] using hratio s hs)
      (by simpa only [he] using hraise s hs)
  have H := position_error_bound p hT hLx hLv hγ hY hW hreg hq h0 hODE htime
    hmetricY hunitY hYODE hWODE hXm hYm hG hforce (hBInt.const_mul C)
    (fun s _ => mul_nonneg hC (gradientSup_nonneg hregTube hDbnd s))
  simpa only [intervalIntegral.integral_const_mul] using H

end FoliationQM.CurvedPhaseTrajectoryBound
