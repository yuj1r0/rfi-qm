module

public import FoliationQM.CurvedEuclideanTrajectories
public import FoliationQM.ProbabilityTrajectoryEstimate

/-!
# Probability comparison for actual polar KG trajectories

Physical curve data contain the first-order coordinate KG equation and
regularity, rather than an assumed acceleration or error estimate. These
data construct the actual controlled Euclidean phase curves. One common
full-measure set of starting labels supplies their all-time comparison.
Explicit spatial-flow measurability and genuine initial integrability then
give finite moments for the actual pushforward probability measure.
Identification with conserved slice-current flux remains a separate task.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedProbabilityTrajectoryEstimate

open LorentzMatrixGroup CurvedCoordinateVelocity CurvedCoordinateDynamics
  CurvedCoordinateTrajectories CurvedNormalizedQuantumForce CurvedPolarKG
  CurvedQuantumForceBound CurvedQuantumForceCriterion CurvedEuclideanTrajectories
  ProbabilityTrajectoryEstimate WeightedPhaseError MeasureTheory Set Filter
open scoped Topology Matrix.Norms.Operator

/-- Actual first-order regular polar KG data for a supplied finite-time curve in an explicit common no-exit phase region. -/
structure PolarCurveOn (p : MassiveParameters) (g : Covector → Mat4)
    (R S : Covector → ℝ) (T : ℝ)
    (Ω : ℝ → Set (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)))
    (γ : ℝ → Covector) : Prop where
  /-- The supplied full coordinate path is continuous up to both endpoints. -/
  curve_continuous : ContinuousOn γ (Icc 0 T)
  /-- The actual metric, amplitude and phase satisfy the regular local KG assumptions along the closed path. -/
  regular : ∀ s ∈ Icc 0 T, RegularPolarAt p g R S (γ s)
  /-- The actual mass-defect normalization is positive along the path. -/
  normalization_pos : ∀ s ∈ Icc 0 T, 0 < 1 + defect p g R (γ s)
  /-- The temporal component of the actual normalized velocity is nonzero. -/
  time_nonzero : ∀ s ∈ Icc 0 T, normalizedVelocity p g R S (γ s) 0 ≠ 0
  /-- The actual first-order coordinate-time equation holds at interior times. -/
  coordinate_derivative : ∀ s ∈ Ioo 0 T,
    HasDerivAt γ (coordinateVelocity p.c (normalizedVelocity p g R S) (γ s)) s
  /-- The full path uses the prescribed coordinate time x⁰=ct. -/
  coordinate_time : ∀ s ∈ Icc 0 T, γ s 0 = p.c * s
  /-- The actual Euclidean position and velocity remain in the common phase region. -/
  no_exit : ∀ s ∈ Icc 0 T, (position γ s, velocity p g R S γ s) ∈ Ω s

variable {p : MassiveParameters} {g : Covector → Mat4} {R S : Covector → ℝ}
  {T : ℝ} {Ω : ℝ → Set (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))}
  {γ : ℝ → Covector} {A : ℝ → ℝ}

/-- Actual first-order polar KG data construct both controlled phase equations and their continuity; only the source's bound on the actual force is supplied. -/
theorem controlledCurve_of_polar (h : PolarCurveOn p g R S T Ω γ)
    (hf : ∀ᵐ s ∂volume.restrict (Icc 0 T),
      spatialForceNorm p g R S s (spatialPart (γ s)) ≤ A s) :
    ControlledCurve (geodesic p.c g) A Ω T (position γ) (velocity p g R S γ)
      (force p g R S γ) := by
  have hX := continuousOn_position h.curve_continuous
  have hV := continuousOn_velocity h.curve_continuous h.regular h.normalization_pos h.time_nonzero
  refine {
    position_continuous := hX
    velocity_continuous := hV
    position_derivative := fun s hs => hasDerivAt_position p g R S (h.coordinate_derivative s hs)
    velocity_derivative := fun s hs => hasDerivAt_velocity (h.regular s (Ioo_subset_Icc_self hs))
      (h.normalization_pos s (Ioo_subset_Icc_self hs)) (h.time_nonzero s (Ioo_subset_Icc_self hs))
      (h.coordinate_derivative s hs) (h.coordinate_time s (Ioo_subset_Icc_self hs))
    field_continuous := ?_
    force_continuous := continuousOn_force h.curve_continuous h.regular h.normalization_pos h.time_nonzero
    no_exit := h.no_exit
    force_bound := ?_ }
  · apply continuousOn_geodesic p.c g hX hV
    · intro s hs
      change ContDiffAt ℝ 2 g (coordinatePoint p.c s (spatialPart (γ s)))
      rw [← reconstruct_position p.c s (γ s) (h.coordinate_time s hs)]
      exact (h.regular s hs).metric_C2
    · intro s hs
      change IsUnit (g (coordinatePoint p.c s (spatialPart (γ s)))).det
      rw [← reconstruct_position p.c s (γ s) (h.coordinate_time s hs)]
      exact isUnit_iff_ne_zero.mpr (h.regular s hs).det_neg.ne
  · filter_upwards [hf, ae_restrict_mem measurableSet_Icc] with s hs hmem
    rw [force_norm p g R S (h.coordinate_time s hmem)]
    exact hs

/-- Actual reference geodesic equations and metric regularity construct the reference phase curve, deriving its field continuity instead of assuming it. -/
theorem referenceCurve_of_metric (c : ℝ) (g : Covector → Mat4)
    {Y W : ℝ → EuclideanSpace ℝ (Fin 3)}
    (hY : ContinuousOn Y (Icc 0 T)) (hW : ContinuousOn W (Icc 0 T))
    (hg : ∀ s ∈ Icc 0 T, ContDiffAt ℝ 2 g (coordinatePoint c s (WithLp.ofLp (Y s))))
    (hu : ∀ s ∈ Icc 0 T, IsUnit (g (coordinatePoint c s (WithLp.ofLp (Y s)))).det)
    (hYODE : ∀ s ∈ Ioo 0 T, HasDerivAt Y (W s) s)
    (hWODE : ∀ s ∈ Ioo 0 T, HasDerivAt W (geodesic c g s (Y s) (W s)) s)
    (hno : ∀ s ∈ Icc 0 T, (Y s, W s) ∈ Ω s) :
    ReferenceCurve (geodesic c g) Ω T Y W where
  position_continuous := hY
  velocity_continuous := hW
  position_derivative := hYODE
  velocity_derivative := hWODE
  field_continuous := continuousOn_geodesic c g hY hW hg hu
  no_exit := hno

section Labels

variable {Label : Type*} [MeasurableSpace Label]
  {Γ : ℝ → Label → Covector} {Y W : ℝ → EuclideanSpace ℝ (Fin 3)}
  {Lx Lv : ℝ}

/-- One common full-measure set of actual polar KG curves gives the weighted Euclidean phase estimate simultaneously at every time; no uncountable intersection of timewise full-measure sets is used. -/
theorem ae_phase_error_bound_of_polar (μ : Measure Label)
    (hT : 0 < T) (hLx : 0 ≤ Lx) (hLv : 0 ≤ Lv)
    (hRef : ReferenceCurve (geodesic p.c g) Ω T Y W)
    (hG : ∀ s ∈ Icc 0 T, ∀ z ∈ Ω s, ∀ w ∈ Ω s,
      ‖geodesic p.c g s z.1 z.2 - geodesic p.c g s w.1 w.2‖ ≤
        Lx * ‖z.1 - w.1‖ + Lv * ‖z.2 - w.2‖)
    (hA : IntervalIntegrable A volume 0 T) (hAn : ∀ s ∈ Icc 0 T, 0 ≤ A s)
    (hCurves : ∀ᵐ a ∂μ, PolarCurveOn p g R S T Ω (fun s => Γ s a) ∧
      ∀ᵐ s ∂volume.restrict (Icc 0 T),
        spatialForceNorm p g R S s (spatialPart (Γ s a)) ≤ A s) :
    ∀ᵐ a ∂μ, ∀ t ∈ Icc 0 T,
      ‖position (fun s => Γ s a) t - Y t‖ +
        T * ‖velocity p g R S (fun s => Γ s a) t - W t‖ ≤
      Real.exp (rate T Lx Lv * T) *
        (‖position (fun s => Γ s a) 0 - Y 0‖ +
          T * ‖velocity p g R S (fun s => Γ s a) 0 - W 0‖ +
          T * ∫ s in 0..T, A s) := by
  exact ProbabilityTrajectoryEstimate.ae_phase_error_bound μ hT hLx hLv hRef hG hA hAn
    (hCurves.mono fun _ h => controlledCurve_of_polar h.1 h.2)

/-- Genuine measurable spatial pushforwards of actual polar KG trajectories have finite first moments and satisfy the exact averaged bound, derived from initial integrability and one common full-measure set of analytic curve hypotheses. -/
theorem mapped_position_moment_bound_of_polar (μ : Measure Label) [IsProbabilityMeasure μ]
    (hT : 0 < T) (hLx : 0 ≤ Lx) (hLv : 0 ≤ Lv)
    (hRef : ReferenceCurve (geodesic p.c g) Ω T Y W)
    (hG : ∀ s ∈ Icc 0 T, ∀ z ∈ Ω s, ∀ w ∈ Ω s,
      ‖geodesic p.c g s z.1 z.2 - geodesic p.c g s w.1 w.2‖ ≤
        Lx * ‖z.1 - w.1‖ + Lv * ‖z.2 - w.2‖)
    (hA : IntervalIntegrable A volume 0 T) (hAn : ∀ s ∈ Icc 0 T, 0 ≤ A s)
    (hCurves : ∀ᵐ a ∂μ, PolarCurveOn p g R S T Ω (fun s => Γ s a) ∧
      ∀ᵐ s ∂volume.restrict (Icc 0 T),
        spatialForceNorm p g R S s (spatialPart (Γ s a)) ≤ A s)
    (hX : ∀ t ∈ Icc 0 T, AEMeasurable (fun a => position (fun s => Γ s a) t) μ)
    (ha : Integrable (fun a => ‖position (fun s => Γ s a) 0 - Y 0‖) μ)
    (hb : Integrable (fun a => ‖velocity p g R S (fun s => Γ s a) 0 - W 0‖) μ) :
    ∀ t ∈ Icc 0 T,
      Integrable (fun x : EuclideanSpace ℝ (Fin 3) => ‖x‖)
        (μ.map (fun a => position (fun s => Γ s a) t)) ∧
      Integrable (fun x => ‖x - Y t‖) (μ.map (fun a => position (fun s => Γ s a) t)) ∧
      (∫ x, ‖x - Y t‖ ∂μ.map (fun a => position (fun s => Γ s a) t)) ≤
        Real.exp (rate T Lx Lv * T) *
          ((∫ a, ‖position (fun s => Γ s a) 0 - Y 0‖ ∂μ) +
            T * (∫ a, ‖velocity p g R S (fun s => Γ s a) 0 - W 0‖ ∂μ) +
            T * ∫ s in 0..T, A s) := by
  have hcontrolled := hCurves.mono fun _ h => controlledCurve_of_polar h.1 h.2
  intro t ht
  have hm := ProbabilityTrajectoryEstimate.mapped_position_moment_bound μ
    hT hLx hLv hRef hG hA hAn hcontrolled hX ha hb t ht
  exact ⟨ProbabilityTransportMoment.norm_integrable_of_error hm.1, hm⟩

end Labels
end FoliationQM.CurvedProbabilityTrajectoryEstimate
