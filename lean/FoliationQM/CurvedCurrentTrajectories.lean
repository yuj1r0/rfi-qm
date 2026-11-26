module

public import FoliationQM.CurvedCurrentTransport
public import FoliationQM.CurvedProbabilityTrajectoryEstimate

/-!
# Actual current-flow trajectories

The supplied spatial flow determines the full coordinate-time path. Its
first-order equation and initial values follow from the primitive flow data.
One common full-measure set of labels supplies the actual polar curves and
force controls used by the probability comparison theorem.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedCurrentTrajectories

open LorentzMatrixGroup CurvedCoordinateCurrent CurvedCoordinateVelocity
  CurvedCoordinateDynamics CurvedCoordinateTrajectories CurvedNormalizedQuantumForce
  CurvedEuclideanTrajectories CurvedCurrentTransport CurvedProbabilityTrajectoryEstimate
  CurvedQuantumForceCriterion MeasureTheory Set Filter
open scoped Topology Matrix.Norms.Operator

/-- The actual full coordinate-time trajectory of a carried starting label. -/
def trajectory (p : MassiveParameters) (Phi : ℝ × (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (a : Fin 3 → ℝ) (t : ℝ) : Covector := eventMap p.c (t, Phi (t, a))

variable {p : MassiveParameters} {g : Covector → Mat4} {R S : Covector → ℝ}
  {Phi : ℝ × (Fin 3 → ℝ) → (Fin 3 → ℝ)} {T t : ℝ} {A : Set (Fin 3 → ℝ)}
  {a : Fin 3 → ℝ}
  {Ω : ℝ → Set (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))}

/-- The actual path has the prescribed time coordinate. -/
theorem trajectory_time : trajectory p Phi a t 0 = p.c * t := rfl

/-- Spatial projection recovers the supplied flow exactly. -/
theorem trajectory_spatial : spatialPart (trajectory p Phi a t) = Phi (t, a) := rfl

/-- The actual Euclidean position is the Euclidean realization of the spatial flow. -/
theorem position_eq : position (trajectory p Phi a) t = WithLp.toLp 2 (Phi (t, a)) := rfl

/-- The actual Euclidean velocity is the normalized coordinate velocity along the flow. -/
theorem velocity_eq : velocity p g R S (trajectory p Phi a) t =
    WithLp.toLp 2 (spatialVelocity p g R S (t, Phi (t, a))) := rfl

/-- Joint regularity of the actual flow gives continuity of the full path at both endpoints. -/
theorem continuousOn_trajectory (h : FlowData p g R S Phi T A) (ha : a ∈ A) :
    ContinuousOn (trajectory p Phi a) (Icc 0 T) := by
  intro t ht
  have hp : ContinuousAt (fun s : ℝ => (s, a)) t :=
    continuousAt_id.prodMk continuousAt_const
  have hPhi : ContinuousAt (fun s => Phi (s, a)) t :=
    (h.flow_C2 a ha t ht).continuousAt.comp (f := fun s : ℝ => (s, a)) hp
  exact ((eventMap p.c).continuous.continuousAt.comp
    (continuousAt_id.prodMk hPhi)).continuousWithinAt

/-- The primitive spatial ODE and derived positive time component reconstruct the actual full coordinate ODE. -/
theorem hasDerivAt_trajectory (h : FlowData p g R S Phi T A) (ha : a ∈ A)
    (ht : t ∈ Ioo 0 T) :
    HasDerivAt (trajectory p Phi a)
      (coordinateVelocity p.c (normalizedVelocity p g R S) (trajectory p Phi a t)) t := by
  have hd := (eventMap p.c).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (h.time_ode a ha t ht).self_of_nhds)
  have hv : eventMap p.c (1, spatialVelocity p g R S (t, Phi (t, a))) =
      coordinateVelocity p.c (normalizedVelocity p g R S) (trajectory p Phi a t) := by
    unfold trajectory
    rw [reconstruct_velocity p.c (normalizedVelocity p g R S) _
      (h.time_pos ha (Ioo_subset_Icc_self ht)).ne']
    change eventMap p.c (1, spatialVelocity p g R S (t, Phi (t, a))) =
      spacetimeVelocity p.c (spatialVelocity p g R S (t, Phi (t, a)))
    rw [eventMap_apply]
    simp only [coordinatePoint, spacetimeVelocity, mul_one]
  rw [hv] at hd
  exact hd

/-- The actual initial identity germ fixes the initial Euclidean position. -/
theorem initial_position_eq (h : FlowData p g R S Phi T A) (ha : a ∈ A) :
    position (trajectory p Phi a) 0 = WithLp.toLp 2 a := by
  rw [position_eq, h.initial_eq ha]

/-- The actual initial identity germ evaluates the initial velocity at the starting label. -/
theorem initial_velocity_eq (h : FlowData p g R S Phi T A) (ha : a ∈ A) :
    velocity p g R S (trajectory p Phi a) 0 =
      WithLp.toLp 2 (spatialVelocity p g R S (0, a)) := by
  rw [velocity_eq, h.initial_eq ha]

/-- Primitive physical flow data construct the actual polar curve; only its true common-region containment is supplied. -/
theorem polarCurveOn (h : FlowData p g R S Phi T A) (ha : a ∈ A)
    (hno : ∀ s ∈ Icc 0 T,
      (WithLp.toLp 2 (Phi (s, a)),
        WithLp.toLp 2 (spatialVelocity p g R S (s, Phi (s, a)))) ∈ Ω s) :
    PolarCurveOn p g R S T Ω (trajectory p Phi a) where
  curve_continuous := continuousOn_trajectory h ha
  regular := h.regular a ha
  normalization_pos := h.normalization_pos a ha
  time_nonzero := fun _ hs => (h.time_pos ha hs).ne'
  coordinate_derivative := fun _ hs => hasDerivAt_trajectory h ha hs
  coordinate_time := fun _ _ => trajectory_time
  no_exit := by simpa only [position_eq, velocity_eq] using hno

/-- One actual current-almost-everywhere label event identifies the initial position function. -/
theorem ae_initial_position_eq (h : FlowData p g R S Phi T A) :
    (fun a => position (trajectory p Phi a) 0) =ᵐ[normalizedInitial p g R S A]
      (fun a => WithLp.toLp 2 a) :=
  h.ae_mem_domain.mono fun _ ha => initial_position_eq h ha

/-- One actual current-almost-everywhere label event identifies the initial velocity function. -/
theorem ae_initial_velocity_eq (h : FlowData p g R S Phi T A) :
    (fun a => velocity p g R S (trajectory p Phi a) 0) =ᵐ[normalizedInitial p g R S A]
      (fun a => WithLp.toLp 2 (spatialVelocity p g R S (0, a))) :=
  h.ae_mem_domain.mono fun _ ha => initial_velocity_eq h ha

/-- One common label event with whole-interval containment gives actual polar curves almost everywhere. -/
theorem ae_polar_curves (h : FlowData p g R S Phi T A)
    (hNo : ∀ᵐ a ∂normalizedInitial p g R S A, ∀ s ∈ Icc 0 T,
      (WithLp.toLp 2 (Phi (s, a)),
        WithLp.toLp 2 (spatialVelocity p g R S (s, Phi (s, a)))) ∈ Ω s) :
    ∀ᵐ a ∂normalizedInitial p g R S A, PolarCurveOn p g R S T Ω (trajectory p Phi a) := by
  filter_upwards [h.ae_mem_domain, hNo] with a ha hno
  exact polarCurveOn h ha hno

/-- A single common label event supplies both actual polar curves and their actual almost-everywhere time-force bound. -/
theorem ae_polar_curves_and_force (h : FlowData p g R S Phi T A) {B : ℝ → ℝ}
    (hControls : ∀ᵐ a ∂normalizedInitial p g R S A,
      (∀ s ∈ Icc 0 T,
        (WithLp.toLp 2 (Phi (s, a)),
          WithLp.toLp 2 (spatialVelocity p g R S (s, Phi (s, a)))) ∈ Ω s) ∧
      (∀ᵐ s ∂volume.restrict (Icc 0 T),
        spatialForceNorm p g R S s (Phi (s, a)) ≤ B s)) :
    ∀ᵐ a ∂normalizedInitial p g R S A,
      PolarCurveOn p g R S T Ω (trajectory p Phi a) ∧
      (∀ᵐ s ∂volume.restrict (Icc 0 T),
        spatialForceNorm p g R S s (spatialPart (trajectory p Phi a s)) ≤ B s) := by
  filter_upwards [h.ae_mem_domain, hControls] with a ha hc
  exact ⟨polarCurveOn h ha hc.1, by simpa only [trajectory_spatial] using hc.2⟩

end FoliationQM.CurvedCurrentTrajectories
