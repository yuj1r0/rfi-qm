module

public import FoliationQM.CurvedCurrentTrajectories
public import FoliationQM.CurvedWassersteinTrajectoryEstimate

/-!
# Concentration of the actual normalized geometric current

Primitive physical flow and finite initial flux data determine the probability
measures. Genuine initial moments and one common full-measure label event give
finite transport costs, their exact time supremum bound, and explicit-filter
concentration. The conserved current law is supplied by its proved construction.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedCurrentConcentration

open LorentzMatrixGroup CurvedCoordinateCurrent CurvedCoordinateDynamics
  CurvedCoordinateTrajectories CurvedEuclideanTrajectories CurvedQuantumForceCriterion
  CurvedCurrentTransport CurvedCurrentTrajectories CurvedProbabilityTrajectoryEstimate
  ProbabilityTrajectoryEstimate WeightedPhaseError WassersteinCoupling
  UniformTransportConcentration MeasureTheory Set Filter
open scoped ENNReal Topology Matrix.Norms.Operator

variable {p : MassiveParameters} {g : Covector → Mat4} {R S : Covector → ℝ}
  {Phi : ℝ × (Fin 3 → ℝ) → (Fin 3 → ℝ)} {T Lx Lv : ℝ} {A : Set (Fin 3 → ℝ)}
  {Ω : ℝ → Set (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))}
  {Y W : ℝ → EuclideanSpace ℝ (Fin 3)} {F : ℝ → ℝ}

/-- Actual initial-current moments and a common label event of physical controls. -/
structure SourceControl (h : FiniteFlowData p g R S Phi T A)
    (Ω : ℝ → Set (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)))
    (F : ℝ → ℝ) (Y0 W0 : EuclideanSpace ℝ (Fin 3)) : Prop where
  force_integrable : IntervalIntegrable F volume 0 T
  force_nonneg : ∀ s ∈ Icc 0 T, 0 ≤ F s
  label_controls : ∀ᵐ a ∂(initialProbability h : Measure (Fin 3 → ℝ)),
    (∀ s ∈ Icc 0 T,
      (WithLp.toLp 2 (Phi (s, a)),
        WithLp.toLp 2 (spatialVelocity p g R S (s, Phi (s, a)))) ∈ Ω s) ∧
    (∀ᵐ s ∂volume.restrict (Icc 0 T), spatialForceNorm p g R S s (Phi (s, a)) ≤ F s)
  position_integrable : Integrable (fun a => ‖WithLp.toLp 2 a - Y0‖)
    (initialProbability h : Measure (Fin 3 → ℝ))
  velocity_integrable : Integrable
    (fun a => ‖WithLp.toLp 2 (spatialVelocity p g R S (0, a)) - W0‖)
    (initialProbability h : Measure (Fin 3 → ℝ))

/-- Controls on the entire carried domain imply the primary common almost-everywhere controls. -/
theorem sourceControl_of_domain_controls (h : FiniteFlowData p g R S Phi T A)
    {Y0 W0 : EuclideanSpace ℝ (Fin 3)}
    (hF : IntervalIntegrable F volume 0 T) (hFn : ∀ s ∈ Icc 0 T, 0 ≤ F s)
    (hLabels : ∀ a ∈ A,
      (∀ s ∈ Icc 0 T,
        (WithLp.toLp 2 (Phi (s, a)),
          WithLp.toLp 2 (spatialVelocity p g R S (s, Phi (s, a)))) ∈ Ω s) ∧
      (∀ᵐ s ∂volume.restrict (Icc 0 T), spatialForceNorm p g R S s (Phi (s, a)) ≤ F s))
    (hdx : Integrable (fun a => ‖WithLp.toLp 2 a - Y0‖)
      (initialProbability h : Measure (Fin 3 → ℝ)))
    (hdb : Integrable (fun a => ‖WithLp.toLp 2 (spatialVelocity p g R S (0, a)) - W0‖)
      (initialProbability h : Measure (Fin 3 → ℝ))) : SourceControl h Ω F Y0 W0 :=
  ⟨hF, hFn, h.toFlowData.ae_mem_domain.mono fun a ha => hLabels a ha, hdx, hdb⟩

/-- Actual initial current moments and physical trajectories give finite transport cost for the literal geometric current density. -/
theorem finite_cost_and_bound (h : FiniteFlowData p g R S Phi T A)
    (hT : 0 < T) (hLx : 0 ≤ Lx) (hLv : 0 ≤ Lv)
    (hRef : ReferenceCurve (geodesic p.c g) Ω T Y W)
    (hG : ∀ s ∈ Icc 0 T, ∀ z ∈ Ω s, ∀ w ∈ Ω s,
      ‖geodesic p.c g s z.1 z.2 - geodesic p.c g s w.1 w.2‖ ≤
        Lx * ‖z.1 - w.1‖ + Lv * ‖z.2 - w.2‖)
    (hControl : SourceControl h Ω F (Y 0) (W 0)) :
    ∀ t ∈ Icc 0 T,
      eW1 (euclideanCurrent p g R S Phi A t) (Measure.dirac (Y t)) ≠ ∞ ∧
      (eW1 (euclideanCurrent p g R S Phi A t) (Measure.dirac (Y t))).toReal ≤
        Real.exp (rate T Lx Lv * T) *
          ((∫ a, ‖WithLp.toLp 2 a - Y 0‖ ∂(initialProbability h : Measure (Fin 3 → ℝ))) +
            T * (∫ a, ‖WithLp.toLp 2 (spatialVelocity p g R S (0, a)) - W 0‖
              ∂(initialProbability h : Measure (Fin 3 → ℝ))) + T * ∫ s in 0..T, F s) := by
  have hpae : (fun a => ‖position (trajectory p Phi a) 0 - Y 0‖)
      =ᵐ[(initialProbability h : Measure (Fin 3 → ℝ))] (fun a => ‖WithLp.toLp 2 a - Y 0‖) :=
    (ae_initial_position_eq h.toFlowData).fun_comp (fun x => ‖x - Y 0‖)
  have hvae : (fun a => ‖velocity p g R S (trajectory p Phi a) 0 - W 0‖)
      =ᵐ[(initialProbability h : Measure (Fin 3 → ℝ))]
      (fun a => ‖WithLp.toLp 2 (spatialVelocity p g R S (0, a)) - W 0‖) :=
    (ae_initial_velocity_eq h.toFlowData).fun_comp (fun x => ‖x - W 0‖)
  have hc := ae_polar_curves_and_force h.toFlowData hControl.label_controls
  have hX : ∀ t ∈ Icc 0 T, AEMeasurable (fun a => position (trajectory p Phi a) t)
      (initialProbability h : Measure (Fin 3 → ℝ)) :=
    fun _ ht => h.toFlowData.aemeasurable_position ht
  have hb := CurvedWassersteinTrajectoryEstimate.finite_cost_and_bound
    (Γ := fun s a => trajectory p Phi a s)
    (initialProbability h : Measure (Fin 3 → ℝ)) hT hLx hLv hRef hG
    hControl.force_integrable hControl.force_nonneg hc hX
    (hControl.position_integrable.congr hpae.symm)
    (hControl.velocity_integrable.congr hvae.symm)
  intro t ht
  have hm : (initialProbability h : Measure (Fin 3 → ℝ)).map
      (fun a => position (trajectory p Phi a) t) = euclideanCurrent p g R S Phi A t :=
    h.toFlowData.euclidean_current_pushforward ht
  simpa only [hm, integral_congr_ae hpae, integral_congr_ae hvae] using hb t ht

/-- The exact source coefficient is positive and bounds the actual time supremum of finite current transport costs. -/
theorem sup_bound (h : FiniteFlowData p g R S Phi T A)
    (hT : 0 < T) (hLx : 0 ≤ Lx) (hLv : 0 ≤ Lv)
    (hRef : ReferenceCurve (geodesic p.c g) Ω T Y W)
    (hG : ∀ s ∈ Icc 0 T, ∀ z ∈ Ω s, ∀ w ∈ Ω s,
      ‖geodesic p.c g s z.1 z.2 - geodesic p.c g s w.1 w.2‖ ≤
        Lx * ‖z.1 - w.1‖ + Lv * ‖z.2 - w.2‖)
    (hControl : SourceControl h Ω F (Y 0) (W 0)) :
    0 < Real.exp (rate T Lx Lv * T) ∧
    (∀ t ∈ Icc 0 T, eW1 (euclideanCurrent p g R S Phi A t) (Measure.dirac (Y t)) ≠ ∞) ∧
    0 ≤ timeSup (fun t =>
      (eW1 (euclideanCurrent p g R S Phi A t) (Measure.dirac (Y t))).toReal) T ∧
    timeSup (fun t =>
      (eW1 (euclideanCurrent p g R S Phi A t) (Measure.dirac (Y t))).toReal) T ≤
      Real.exp (rate T Lx Lv * T) *
        ((∫ a, ‖WithLp.toLp 2 a - Y 0‖ ∂(initialProbability h : Measure (Fin 3 → ℝ))) +
          T * (∫ a, ‖WithLp.toLp 2 (spatialVelocity p g R S (0, a)) - W 0‖
            ∂(initialProbability h : Measure (Fin 3 → ℝ))) + T * ∫ s in 0..T, F s) :=
  ⟨source_constant_pos T Lx Lv, finite_cost_sup_bound hT.le
    (finite_cost_and_bound h hT hLx hLv hRef hG hControl)⟩

/-- Actual preservation of the full carrying image identifies the current probability with the literal fixed-slice Euclidean density. -/
theorem currentProbability_eq_fixed_density (h : FiniteFlowData p g R S Phi T A)
    {t : ℝ} (ht : t ∈ Icc 0 T) (himage : (fun a => Phi (t, a)) '' A = A) :
    (currentProbability h t : Measure (EuclideanSpace ℝ (Fin 3))) =
      (initialMass p g R S A)⁻¹ •
        ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (WithLp.toLp 2 '' A)).withDensity
          (fun y => ENNReal.ofReal (density p g R S (t, WithLp.ofLp y))) := by
  rw [currentProbability_eq_density h ht, euclideanCurrent, himage]

/-- Forward preservation and an actual region-preserving right inverse derive the full fixed-slice current identity. -/
theorem currentProbability_eq_fixed_density_of_inverse_preservation
    (h : FiniteFlowData p g R S Phi T A) {t : ℝ} (ht : t ∈ Icc 0 T)
    {psi : (Fin 3 → ℝ) → (Fin 3 → ℝ)}
    (hforward : MapsTo (fun a => Phi (t, a)) A A) (hback : MapsTo psi A A)
    (hright : ∀ y ∈ A, Phi (t, psi y) = y) :
    (currentProbability h t : Measure (EuclideanSpace ℝ (Fin 3))) =
      (initialMass p g R S A)⁻¹ •
        ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (WithLp.toLp 2 '' A)).withDensity
          (fun y => ENNReal.ofReal (density p g R S (t, WithLp.ofLp y))) :=
  currentProbability_eq_fixed_density h ht
    (WeightedJacobianPushforward.image_eq_of_forward_inverse_preservation hforward hback hright)

section Family

variable {ι : Type*}

/-- The actual current probability family has eventually finite costs converging uniformly in time, with its genuine supremum tending to zero. -/
theorem family_concentration_of_eventually
    (P : ι → MassiveParameters) (g : Covector → Mat4)
    (amp phase : ι → Covector → ℝ)
    (Phi : ι → ℝ × (Fin 3 → ℝ) → (Fin 3 → ℝ)) (domains : ι → Set (Fin 3 → ℝ))
    (H : ∀ i, FiniteFlowData (P i) g (amp i) (phase i) (Phi i) T (domains i)) (l : Filter ι)
    {c : ℝ} (hc : ∀ i, (P i).c = c) {F : ι → ℝ → ℝ}
    (hT : 0 < T) (hLx : 0 ≤ Lx) (hLv : 0 ≤ Lv)
    (hRef : ReferenceCurve (geodesic c g) Ω T Y W)
    (hG : ∀ s ∈ Icc 0 T, ∀ z ∈ Ω s, ∀ w ∈ Ω s,
      ‖geodesic c g s z.1 z.2 - geodesic c g s w.1 w.2‖ ≤
        Lx * ‖z.1 - w.1‖ + Lv * ‖z.2 - w.2‖)
    (hGood : ∀ᶠ i in l, SourceControl (H i) Ω (F i) (Y 0) (W 0))
    (hdx : Tendsto (fun i => ∫ a, ‖WithLp.toLp 2 a - Y 0‖
      ∂(initialProbability (H i) : Measure (Fin 3 → ℝ))) l (𝓝 0))
    (hdb : Tendsto (fun i => ∫ a,
      ‖WithLp.toLp 2 (spatialVelocity (P i) g (amp i) (phase i) (0, a)) - W 0‖
      ∂(initialProbability (H i) : Measure (Fin 3 → ℝ))) l (𝓝 0))
    (hJ : Tendsto (fun i => ∫ s in 0..T, F i s) l (𝓝 0)) :
    let ν := fun i t => (currentProbability (H i) t : Measure (EuclideanSpace ℝ (Fin 3)))
    (∀ᶠ i in l, ∀ t ∈ Icc 0 T, eW1 (ν i t) (Measure.dirac (Y t)) ≠ ∞) ∧
      TendstoUniformlyOn (fun i t => (eW1 (ν i t) (Measure.dirac (Y t))).toReal)
        (fun _ => 0) l (Icc 0 T) ∧
      Tendsto (fun i => timeSup (fun t => (eW1 (ν i t) (Measure.dirac (Y t))).toReal) T)
        l (𝓝 0) := by
  dsimp only
  apply uniform_concentration_of_bound l hT.le ?_
    (source_majorant_tendsto l T Lx Lv hdx hdb hJ)
  filter_upwards [hGood] with i hi t ht
  rw [currentProbability_eq_density (H i) ht]
  exact finite_cost_and_bound (H i) hT hLx hLv
    (by simpa only [hc i] using hRef) (by simpa only [hc i] using hG) hi t ht

end Family
end FoliationQM.CurvedCurrentConcentration
