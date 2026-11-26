module

public import FoliationQM.MappedTubeSupport
public import FoliationQM.CurvedCurrentTrajectories

/-!
# Pointwise containment of the actual current in a compact worldtube

One common initial-current almost-everywhere label event supplies genuine
pointwise initial bounds and label-dependent integrable actual force bounds.
The proved physical trajectory estimate derives the all-time position bound.
Actual current transport then gives zero outside mass and support containment
in a compact coordinate-time tube. No first-moment bound replaces these inputs.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedCurrentTubeSupport

open LorentzMatrixGroup CurvedCoordinateCurrent CurvedCoordinateDynamics
  CurvedCoordinateTrajectories CurvedEuclideanTrajectories CurvedQuantumForceCriterion
  CurvedCurrentTransport CurvedCurrentTrajectories CurvedProbabilityTrajectoryEstimate
  ProbabilityTrajectoryEstimate WeightedPhaseError MeasureTheory Set Filter Metric
open scoped ENNReal Topology Matrix.Norms.Operator

variable {p : MassiveParameters} {g : Covector → Mat4} {R S : Covector → ℝ}
  {Phi : ℝ × (Fin 3 → ℝ) → (Fin 3 → ℝ)} {T Lx Lv : ℝ} {A : Set (Fin 3 → ℝ)}
  {Ω : ℝ → Set (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))}
  {Y W : ℝ → EuclideanSpace ℝ (Fin 3)} {F : (Fin 3 → ℝ) → ℝ → ℝ}
  {rx rv rJ : ℝ}

/-- One common label event of actual initial errors, whole-time containment and genuinely integrated physical forcing. -/
def PointwiseControl (h : FiniteFlowData p g R S Phi T A)
    (Ω : ℝ → Set (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)))
    (F : (Fin 3 → ℝ) → ℝ → ℝ) (Y0 W0 : EuclideanSpace ℝ (Fin 3))
    (rx rv rJ : ℝ) : Prop :=
  ∀ᵐ a ∂(initialProbability h : Measure (Fin 3 → ℝ)),
    (∀ s ∈ Icc 0 T,
      (WithLp.toLp 2 (Phi (s, a)),
        WithLp.toLp 2 (spatialVelocity p g R S (s, Phi (s, a)))) ∈ Ω s) ∧
    ‖WithLp.toLp 2 a - Y0‖ ≤ rx ∧
    ‖WithLp.toLp 2 (spatialVelocity p g R S (0, a)) - W0‖ ≤ rv ∧
    IntervalIntegrable (F a) volume 0 T ∧
    (∀ s ∈ Icc 0 T, 0 ≤ F a s) ∧
    (∀ᵐ s ∂volume.restrict (Icc 0 T), spatialForceNorm p g R S s (Phi (s, a)) ≤ F a s) ∧
    (∫ s in 0..T, F a s) ≤ rJ

/-- The actual physical curve estimate derives a single all-time almost-everywhere position radius from pointwise initial and integrated-force bounds. -/
theorem ae_position_bound (h : FiniteFlowData p g R S Phi T A)
    (hT : 0 < T) (hLx : 0 ≤ Lx) (hLv : 0 ≤ Lv)
    (hRef : ReferenceCurve (geodesic p.c g) Ω T Y W)
    (hG : ∀ s ∈ Icc 0 T, ∀ z ∈ Ω s, ∀ w ∈ Ω s,
      ‖geodesic p.c g s z.1 z.2 - geodesic p.c g s w.1 w.2‖ ≤
        Lx * ‖z.1 - w.1‖ + Lv * ‖z.2 - w.2‖)
    (hControl : PointwiseControl h Ω F (Y 0) (W 0) rx rv rJ) :
    ∀ᵐ a ∂(initialProbability h : Measure (Fin 3 → ℝ)), ∀ t ∈ Icc 0 T,
      dist (WithLp.toLp 2 (Phi (t, a))) (Y t) ≤
        Real.exp (rate T Lx Lv * T) * (rx + T * rv + T * rJ) := by
  filter_upwards [h.toFlowData.ae_mem_domain, hControl] with a ha hlabel
  rcases hlabel with ⟨hno, hx, hv, hFI, hFn, hFb, hJ⟩
  have hc := controlledCurve_of_polar (A := F a) (polarCurveOn h.toFlowData ha hno)
    (by simpa only [trajectory_spatial] using hFb)
  have hb := hc.position_error_bound hRef hT hLx hLv hG hFI hFn
  have hm : ‖WithLp.toLp 2 a - Y 0‖ +
      T * ‖WithLp.toLp 2 (spatialVelocity p g R S (0, a)) - W 0‖ +
      T * (∫ s in 0..T, F a s) ≤ rx + T * rv + T * rJ :=
    add_le_add (add_le_add hx (mul_le_mul_of_nonneg_left hv hT.le))
      (mul_le_mul_of_nonneg_left hJ hT.le)
  intro t ht
  have hb' := hb t ht
  rw [initial_position_eq h.toFlowData ha, initial_velocity_eq h.toFlowData ha,
    position_eq] at hb'
  rw [dist_eq_norm]
  exact hb'.trans (mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le)

/-- Actual current transport converts the derived pointwise radius into zero outside mass, true support inclusion and compact support on every slice. -/
theorem support_zero_mass_compact (h : FiniteFlowData p g R S Phi T A)
    (hT : 0 < T) (hLx : 0 ≤ Lx) (hLv : 0 ≤ Lv)
    (hRef : ReferenceCurve (geodesic p.c g) Ω T Y W)
    (hG : ∀ s ∈ Icc 0 T, ∀ z ∈ Ω s, ∀ w ∈ Ω s,
      ‖geodesic p.c g s z.1 z.2 - geodesic p.c g s w.1 w.2‖ ≤
        Lx * ‖z.1 - w.1‖ + Lv * ‖z.2 - w.2‖)
    (hControl : PointwiseControl h Ω F (Y 0) (W 0) rx rv rJ) :
    ∀ t ∈ Icc 0 T,
      (currentProbability h t : Measure (EuclideanSpace ℝ (Fin 3))).support ⊆
        Metric.closedBall (Y t) (Real.exp (rate T Lx Lv * T) * (rx + T * rv + T * rJ)) ∧
      (currentProbability h t : Measure (EuclideanSpace ℝ (Fin 3)))
        (Metric.closedBall (Y t) (Real.exp (rate T Lx Lv * T) * (rx + T * rv + T * rJ)))ᶜ = 0 ∧
      IsCompact (currentProbability h t : Measure (EuclideanSpace ℝ (Fin 3))).support := by
  have hb := ae_position_bound h hT hLx hLv hRef hG hControl
  intro t ht
  have hbT := hb.mono fun _ ha => ha t ht
  have hX := h.toFlowData.aemeasurable_position ht
  have hmap : (initialProbability h : Measure (Fin 3 → ℝ)).map
      (fun a => WithLp.toLp 2 (Phi (t, a))) =
      (currentProbability h t : Measure (EuclideanSpace ℝ (Fin 3))) :=
    (h.toFlowData.euclidean_current_pushforward ht).trans (currentProbability_eq_density h ht).symm
  rw [← hmap]
  exact ⟨MappedTubeSupport.support_map_subset_closedBall hX hbT,
    MappedTubeSupport.map_compl_closedBall_eq_zero hX hbT,
    MappedTubeSupport.isCompact_support_map hX hbT⟩

/-- The actual current-support graph lies in a genuinely compact coordinate-time tube; no graph-closure assertion is needed. -/
theorem compact_worldtube_containment (h : FiniteFlowData p g R S Phi T A)
    (hT : 0 < T) (hLx : 0 ≤ Lx) (hLv : 0 ≤ Lv)
    (hRef : ReferenceCurve (geodesic p.c g) Ω T Y W)
    (hG : ∀ s ∈ Icc 0 T, ∀ z ∈ Ω s, ∀ w ∈ Ω s,
      ‖geodesic p.c g s z.1 z.2 - geodesic p.c g s w.1 w.2‖ ≤
        Lx * ‖z.1 - w.1‖ + Lv * ‖z.2 - w.2‖)
    (hControl : PointwiseControl h Ω F (Y 0) (W 0) rx rv rJ) :
    let radius := Real.exp (rate T Lx Lv * T) * (rx + T * rv + T * rJ)
    IsCompact {tx : ℝ × EuclideanSpace ℝ (Fin 3) |
      tx.1 ∈ Icc 0 T ∧ dist tx.2 (Y tx.1) ≤ radius} ∧
    {tx : ℝ × EuclideanSpace ℝ (Fin 3) | tx.1 ∈ Icc 0 T ∧
      tx.2 ∈ (currentProbability h tx.1 : Measure (EuclideanSpace ℝ (Fin 3))).support} ⊆
    {tx | tx.1 ∈ Icc 0 T ∧ dist tx.2 (Y tx.1) ≤ radius} := by
  refine ⟨MappedTubeSupport.isCompact_worldtube hRef.position_continuous _, ?_⟩
  intro tx htx
  exact ⟨htx.1, (support_zero_mass_compact h hT hLx hLv hRef hG hControl tx.1 htx.1).1 htx.2⟩

/-- Actual pointwise bounds proportional to the width yield literal compact worldtube containment with the exact fixed coefficient. -/
theorem width_tube_containment (h : FiniteFlowData p g R S Phi T A)
    (hT : 0 < T) (hLx : 0 ≤ Lx) (hLv : 0 ≤ Lv)
    (hRef : ReferenceCurve (geodesic p.c g) Ω T Y W)
    (hG : ∀ s ∈ Icc 0 T, ∀ z ∈ Ω s, ∀ w ∈ Ω s,
      ‖geodesic p.c g s z.1 z.2 - geodesic p.c g s w.1 w.2‖ ≤
        Lx * ‖z.1 - w.1‖ + Lv * ‖z.2 - w.2‖)
    {Cx Cv CJ width : ℝ}
    (hControl : PointwiseControl h Ω F (Y 0) (W 0) (Cx * width) (Cv * width) (CJ * width)) :
    let radius := (Real.exp (rate T Lx Lv * T) * (Cx + T * Cv + T * CJ)) * width
    IsCompact {tx : ℝ × EuclideanSpace ℝ (Fin 3) |
      tx.1 ∈ Icc 0 T ∧ dist tx.2 (Y tx.1) ≤ radius} ∧
    {tx : ℝ × EuclideanSpace ℝ (Fin 3) | tx.1 ∈ Icc 0 T ∧
      tx.2 ∈ (currentProbability h tx.1 : Measure (EuclideanSpace ℝ (Fin 3))).support} ⊆
    {tx | tx.1 ∈ Icc 0 T ∧ dist tx.2 (Y tx.1) ≤ radius} := by
  have heq : Real.exp (rate T Lx Lv * T) *
      (Cx * width + T * (Cv * width) + T * (CJ * width)) =
      (Real.exp (rate T Lx Lv * T) * (Cx + T * Cv + T * CJ)) * width := by ring
  simpa only [heq] using compact_worldtube_containment h hT hLx hLv hRef hG hControl

end FoliationQM.CurvedCurrentTubeSupport
