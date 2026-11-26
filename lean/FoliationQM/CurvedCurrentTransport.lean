module

public import FoliationQM.CurvedFlowDensityConservation
public import FoliationQM.GeometricCurrentFlux
public import FoliationQM.WeightedJacobianPushforward
public import FoliationQM.WeightedProbabilityTransport
public import FoliationQM.EuclideanDensityTransport
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Actual geometric current transport on a supplied smooth flow

The flow data contain genuine differential, inverse, initial and geometric
conditions. Current conservation and measure transport are derived from
those data. The transported slice is the actual image of the initial label
domain. Future coorientation makes the real density strictly positive.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedCurrentTransport

open LorentzMatrixGroup CurvedCoordinateCurrent CurvedQuantumForceBound
  CurvedPolarKG CurvedNormalizedQuantumForce GeometricLorentzFrame
  SpatialFlowDifferential SpatialFlowJacobian Set Filter MeasureTheory
  WeightedJacobianPushforward
open scoped Topology BigOperators Matrix.Norms.Operator ENNReal
set_option backward.isDefEq.respectTransparency false

/-- Actual future frame data at a coordinate point, with the genuine spacelike spatial Gram. -/
def FutureSliceAt (p : MassiveParameters) (g : Covector → Mat4) (R S : Covector → ℝ)
    (q : ℝ × (Fin 3 → ℝ)) : Prop :=
  ∃ orientation : Orientation ℝ Covector (Fin 4), ∃ future : Set Covector,
    ∃ e : Frame (g (eventMap p.c q)).toBilin' orientation future,
      0 < (e.basis 0) 0 ∧
      (SpacelikeSliceGeometry.spatialGram (g (eventMap p.c q))).PosDef ∧
      normalizedVelocity p g R S (eventMap p.c q) ∈ future

/-- Primitive actual smooth-flow and geometric data on a measurable carrying label domain. -/
structure FlowData (p : MassiveParameters) (g : Covector → Mat4) (R S : Covector → ℝ)
    (Phi : ℝ × (Fin 3 → ℝ) → (Fin 3 → ℝ)) (T : ℝ) (A : Set (Fin 3 → ℝ)) : Prop where
  time_nonneg : 0 ≤ T
  domain_measurable : MeasurableSet A
  flow_C2 : ∀ a ∈ A, ∀ t ∈ Icc 0 T, ContDiffAt ℝ 2 Phi (t, a)
  regular : ∀ a ∈ A, ∀ t ∈ Icc 0 T,
    RegularPolarAt p g R S (eventMap p.c (t, Phi (t, a)))
  normalization_pos : ∀ a ∈ A, ∀ t ∈ Icc 0 T,
    0 < 1 + defect p g R (eventMap p.c (t, Phi (t, a)))
  future_slice : ∀ a ∈ A, ∀ t ∈ Icc 0 T, FutureSliceAt p g R S (t, Phi (t, a))
  time_ode : ∀ a ∈ A, ∀ t ∈ Ioo 0 T, ∀ᶠ z in 𝓝 a,
    HasDerivAt (fun s => Phi (s, z)) (spatialVelocity p g R S (t, Phi (t, z))) t
  local_left_inverse : ∀ a ∈ A, ∀ t ∈ Icc 0 T,
    ∃ ψ : (Fin 3 → ℝ) → (Fin 3 → ℝ), DifferentiableAt ℝ ψ (Phi (t, a)) ∧
      (fun z => ψ (Phi (t, z))) =ᶠ[𝓝 a] id
  initial_germ : ∀ a ∈ A, (fun z => Phi (0, z)) =ᶠ[𝓝 a] id
  slice_injective : ∀ t ∈ Icc 0 T, InjOn (fun a => Phi (t, a)) A

variable {p : MassiveParameters} {g : Covector → Mat4} {R S : Covector → ℝ}
  {Phi : ℝ × (Fin 3 → ℝ) → (Fin 3 → ℝ)} {T t : ℝ} {A : Set (Fin 3 → ℝ)}
  {a : Fin 3 → ℝ} {q : ℝ × (Fin 3 → ℝ)}

/-- The selected actual future frame gives positive normalized coordinate time. -/
theorem FutureSliceAt.time_pos (hf : FutureSliceAt p g R S q)
    (hreg : RegularPolarAt p g R S (eventMap p.c q)) :
    0 < normalizedVelocity p g R S (eventMap p.c q) 0 := by
  obtain ⟨orientation, future, e, htime, hsp, hU⟩ := hf
  exact GeometricCurrentFlux.time_pos_of_mem_future e htime hreg.det_neg hsp hU

/-- Future geometry and actual polar regularity give positive real current density. -/
theorem FutureSliceAt.density_pos (hf : FutureSliceAt p g R S q)
    (hreg : RegularPolarAt p g R S (eventMap p.c q))
    (hq : 0 < 1 + defect p g R (eventMap p.c q)) : 0 < density p g R S q := by
  obtain ⟨orientation, future, e, htime, hsp, hU⟩ := hf
  exact GeometricCurrentFlux.physical_density_pos_of_normalized q e htime
    hreg.det_neg hsp hreg.amplitude_pos hq hU

/-- The real density is literally the actual unit-normal flux times induced Gram volume. -/
theorem FutureSliceAt.geometric_density_eq (hf : FutureSliceAt p g R S q)
    (hreg : RegularPolarAt p g R S (eventMap p.c q)) :
    let x := eventMap p.c q
    ((SpacelikeSliceGeometry.normalCovector (g x) ⬝ᵥ
      GeometricCurrentFlux.physicalCurrent p g R S x) / p.c) *
      SpacelikeSliceGeometry.sliceVolumeFactor (g x) = density p g R S q := by
  obtain ⟨orientation, future, e, htime, hsp, hU⟩ := hf
  exact GeometricCurrentFlux.physical_flux_density_eq p g R S q hreg.det_neg hsp

/-- The genuine initial identity germ identifies each carried initial position. -/
theorem FlowData.initial_eq (h : FlowData p g R S Phi T A) (ha : a ∈ A) :
    Phi (0, a) = a := (h.initial_germ a ha).self_of_nhds

/-- The actual normalized temporal velocity is positive throughout the closed carrying tube. -/
theorem FlowData.time_pos (h : FlowData p g R S Phi T A) (ha : a ∈ A) (ht : t ∈ Icc 0 T) :
    0 < normalizedVelocity p g R S (eventMap p.c (t, Phi (t, a))) 0 :=
  (h.future_slice a ha t ht).time_pos (h.regular a ha t ht)

/-- The literal real density is positive on every transported carrying slice. -/
theorem FlowData.density_pos (h : FlowData p g R S Phi T A) (ha : a ∈ A) (ht : t ∈ Icc 0 T) :
    0 < density p g R S (t, Phi (t, a)) :=
  (h.future_slice a ha t ht).density_pos (h.regular a ha t ht) (h.normalization_pos a ha t ht)

/-- Initial current positivity is derived at the actual label, using the true initial identity. -/
theorem FlowData.initial_density_pos (h : FlowData p g R S Phi T A) (ha : a ∈ A) :
    0 < density p g R S (0, a) := by
  simpa only [h.initial_eq ha] using h.density_pos ha ⟨le_rfl, h.time_nonneg⟩

/-- Joint flow regularity supplies the actual spatial slice derivative. -/
theorem FlowData.hasFDerivAt_slice (h : FlowData p g R S Phi T A)
    (ha : a ∈ A) (ht : t ∈ Icc 0 T) :
    HasFDerivAt (fun z => Phi (t, z)) (spatialDifferential Phi (t, a)) a :=
  hasFDerivAt_spatial_slice ((h.flow_C2 a ha t ht).differentiableAt (by decide))

/-- The actual slice flow is continuous on the carrying domain. -/
theorem FlowData.continuousOn_slice (h : FlowData p g R S Phi T A) (ht : t ∈ Icc 0 T) :
    ContinuousOn (fun a => Phi (t, a)) A :=
  fun _ ha => (h.hasFDerivAt_slice ha ht).continuousAt.continuousWithinAt

/-- The actual physical density-Jacobian law follows from the primitive supplied-flow data. -/
theorem FlowData.density_jacobian_law (h : FlowData p g R S Phi T A)
    (ha : a ∈ A) (ht : t ∈ Icc 0 T) :
    density p g R S (t, Phi (t, a)) * |spatialJacobianDet Phi (t, a)| =
      density p g R S (0, a) :=
  CurvedFlowDensityConservation.density_mul_abs_det_eq_initial h.time_nonneg
    (h.flow_C2 a ha) (h.regular a ha) (h.normalization_pos a ha)
    (fun _ hs => (h.time_pos ha hs).ne') (h.time_ode a ha) (h.local_left_inverse a ha)
    (h.initial_germ a ha) t ht

/-- Initial polar regularity supplies genuine regional continuity of the real initial density. -/
theorem FlowData.continuousOn_initial_density (h : FlowData p g R S Phi T A) :
    ContinuousOn (fun a => density p g R S (0, a)) A := by
  intro a ha
  have hr := h.regular a ha 0 ⟨le_rfl, h.time_nonneg⟩
  rw [h.initial_eq ha] at hr
  have hd := (contDiffAt_density hr).differentiableAt_one.hasFDerivAt.comp a
    (hasFDerivAt_prodMk_right 0 a)
  exact hd.continuousAt.continuousWithinAt

/-- Polar regularity at every actual image point gives regional target-density continuity. -/
theorem FlowData.continuousOn_image_density (h : FlowData p g R S Phi T A)
    (ht : t ∈ Icc 0 T) :
    ContinuousOn (fun y => density p g R S (t, y)) ((fun a => Phi (t, a)) '' A) := by
  rintro y ⟨a, ha, rfl⟩
  have hd := (contDiffAt_density (h.regular a ha t ht)).differentiableAt_one.hasFDerivAt.comp
    (Phi (t, a)) (hasFDerivAt_prodMk_right t (Phi (t, a)))
  exact hd.continuousAt.continuousWithinAt

/-- The actual current measure on a coordinate slice uses its literal real geometric density. -/
def sliceMeasure (p : MassiveParameters) (g : Covector → Mat4) (R S : Covector → ℝ)
    (A : Set (Fin 3 → ℝ)) (t : ℝ) : Measure (Fin 3 → ℝ) :=
  weightedDensity volume A (fun a => density p g R S (t, a))

/-- The common normalizing constant is the actual initial extended current mass. -/
def initialMass (p : MassiveParameters) (g : Covector → Mat4) (R S : Covector → ℝ)
    (A : Set (Fin 3 → ℝ)) : ℝ≥0∞ := sliceMeasure p g R S A 0 univ

/-- The initial current measure is scaled by its own actual initial mass. -/
def normalizedInitial (p : MassiveParameters) (g : Covector → Mat4) (R S : Covector → ℝ)
    (A : Set (Fin 3 → ℝ)) : Measure (Fin 3 → ℝ) :=
  (initialMass p g R S A)⁻¹ • sliceMeasure p g R S A 0

/-- The transported current uses its actual image domain and the same initial mass. -/
def normalizedCurrent (p : MassiveParameters) (g : Covector → Mat4) (R S : Covector → ℝ)
    (Phi : ℝ × (Fin 3 → ℝ) → (Fin 3 → ℝ)) (A : Set (Fin 3 → ℝ))
    (t : ℝ) : Measure (Fin 3 → ℝ) :=
  (initialMass p g R S A)⁻¹ • sliceMeasure p g R S ((fun a => Phi (t, a)) '' A) t

/-- The actual Euclidean current density uses canonical Euclidean volume and the conserved initial mass. -/
def euclideanCurrent (p : MassiveParameters) (g : Covector → Mat4) (R S : Covector → ℝ)
    (Phi : ℝ × (Fin 3 → ℝ) → (Fin 3 → ℝ)) (A : Set (Fin 3 → ℝ))
    (t : ℝ) : Measure (EuclideanSpace ℝ (Fin 3)) :=
  (initialMass p g R S A)⁻¹ •
    ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
      (WithLp.toLp 2 '' ((fun a => Phi (t, a)) '' A))).withDensity
      (fun y => ENNReal.ofReal (density p g R S (t, WithLp.ofLp y)))

/-- The actual slice derivative is a genuine within-domain derivative witness for change of variables. -/
theorem FlowData.hasFDerivWithinAt_slice (h : FlowData p g R S Phi T A)
    (ha : a ∈ A) (ht : t ∈ Icc 0 T) :
    HasFDerivWithinAt (fun z => Phi (t, z))
      (fderiv ℝ (fun z => Phi (t, z)) a) A a :=
  (h.hasFDerivAt_slice ha ht).differentiableAt.hasFDerivAt.hasFDerivWithinAt

/-- The actual injective differentiable slice has a measurable image domain. -/
theorem FlowData.image_measurable (h : FlowData p g R S Phi T A) (ht : t ∈ Icc 0 T) :
    MeasurableSet ((fun a => Phi (t, a)) '' A) :=
  measurable_image_of_fderivWithin h.domain_measurable
    (fun _ ha => h.hasFDerivWithinAt_slice ha ht) (h.slice_injective t ht)

/-- The proved physical law supplies the actual derivative-determinant identity almost everywhere on labels. -/
theorem FlowData.density_jacobian_ae (h : FlowData p g R S Phi T A) (ht : t ∈ Icc 0 T) :
    ∀ᵐ a ∂(volume : Measure (Fin 3 → ℝ)).restrict A,
      density p g R S (0, a) =
        |(fderiv ℝ (fun z => Phi (t, z)) a).det| * density p g R S (t, Phi (t, a)) := by
  filter_upwards [ae_restrict_mem h.domain_measurable] with a ha
  have hl := h.density_jacobian_law ha ht
  rw [spatialJacobianDet_eq_linearMap_det
    ((h.flow_C2 a ha t ht).differentiableAt (by decide))] at hl
  simpa only [mul_comm] using hl.symm

/-- The actual flow map is measurable for the genuine initial current measure. -/
theorem FlowData.aemeasurable_slice (h : FlowData p g R S Phi T A) (ht : t ∈ Icc 0 T) :
    AEMeasurable (fun a => Phi (t, a)) (sliceMeasure p g R S A 0) :=
  aemeasurable_weighted_map volume h.domain_measurable
    (fun _ ha => h.hasFDerivWithinAt_slice ha ht) (fun a => density p g R S (0, a))

/-- Genuine Jacobian change of variables derives transport of the literal physical current measure. -/
theorem FlowData.current_pushforward (h : FlowData p g R S Phi T A) (ht : t ∈ Icc 0 T) :
    (sliceMeasure p g R S A 0).map (fun a => Phi (t, a)) =
      sliceMeasure p g R S ((fun a => Phi (t, a)) '' A) t :=
  map_weightedDensity_of_density_jacobian volume h.domain_measurable
    (fun _ ha => h.hasFDerivWithinAt_slice ha ht) (h.slice_injective t ht)
    (h.continuousOn_initial_density.aemeasurable h.domain_measurable)
    ((h.continuousOn_image_density ht).aemeasurable (h.image_measurable ht))
    (h.density_jacobian_ae ht)

/-- Genuine real initial integrability propagates, with equality of the actual real current fluxes. -/
theorem FlowData.integrable_current_and_flux_eq (h : FlowData p g R S Phi T A)
    (hi : IntegrableOn (fun a => density p g R S (0, a)) A volume) (ht : t ∈ Icc 0 T) :
    IntegrableOn (fun y => density p g R S (t, y)) ((fun a => Phi (t, a)) '' A) volume ∧
      (∫ y in (fun a => Phi (t, a)) '' A, density p g R S (t, y)) =
        ∫ a in A, density p g R S (0, a) :=
  integrableOn_image_and_integral_eq_initial volume h.domain_measurable
    (fun _ ha => h.hasFDerivWithinAt_slice ha ht) (h.slice_injective t ht)
    hi (h.density_jacobian_ae ht)

/-- The actual source-current normalization preserves the genuine flow measurability certificate. -/
theorem FlowData.aemeasurable_normalized_slice (h : FlowData p g R S Phi T A)
    (ht : t ∈ Icc 0 T) :
    AEMeasurable (fun a => Phi (t, a)) (normalizedInitial p g R S A) :=
  WeightedProbabilityTransport.aemeasurable_normalized (h.aemeasurable_slice ht)

/-- The same actual initial mass gives the normalized physical current pushforward law. -/
theorem FlowData.normalized_current_pushforward (h : FlowData p g R S Phi T A)
    (ht : t ∈ Icc 0 T) :
    (normalizedInitial p g R S A).map (fun a => Phi (t, a)) =
      normalizedCurrent p g R S Phi A t :=
  WeightedProbabilityTransport.normalized_map (h.aemeasurable_slice ht) (h.current_pushforward ht)

/-- Exact volume preservation identifies the normalized coordinate current with its actual Euclidean density. -/
theorem normalizedCurrent_map_toLp (p : MassiveParameters) (g : Covector → Mat4)
    (R S : Covector → ℝ) (Phi : ℝ × (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (A : Set (Fin 3 → ℝ)) (t : ℝ) :
    (normalizedCurrent p g R S Phi A t).map (WithLp.toLp 2) =
      euclideanCurrent p g R S Phi A t :=
  EuclideanDensityTransport.map_normalized_coordinate_density_toLp
    (initialMass p g R S A) ((fun a => Phi (t, a)) '' A) (fun y => density p g R S (t, y))

/-- The actual Euclidean spatial flow is measurable under the normalized initial physical current. -/
theorem FlowData.aemeasurable_position (h : FlowData p g R S Phi T A) (ht : t ∈ Icc 0 T) :
    AEMeasurable (fun a => WithLp.toLp 2 (Phi (t, a))) (normalizedInitial p g R S A) :=
  EuclideanDensityTransport.aemeasurable_toLp_after_flow (h.aemeasurable_normalized_slice ht)

/-- The actual normalized Euclidean density is the genuine spatial pushforward of the initial current. -/
theorem FlowData.euclidean_current_pushforward (h : FlowData p g R S Phi T A)
    (ht : t ∈ Icc 0 T) :
    (normalizedInitial p g R S A).map (fun a => WithLp.toLp 2 (Phi (t, a))) =
      euclideanCurrent p g R S Phi A t := by
  rw [EuclideanDensityTransport.map_toLp_after_pushforward
    (h.aemeasurable_normalized_slice ht) (h.normalized_current_pushforward ht),
    normalizedCurrent_map_toLp]

/-- The actual normalized initial current is carried by the label domain on one common almost-everywhere event. -/
theorem FlowData.ae_mem_domain (h : FlowData p g R S Phi T A) :
    ∀ᵐ a ∂normalizedInitial p g R S A, a ∈ A := by
  apply Measure.ae_smul_measure
  exact (withDensity_absolutelyContinuous (volume.restrict A)
    (fun a => ENNReal.ofReal (density p g R S (0, a)))).ae_le
    (ae_restrict_mem h.domain_measurable)

/-- Primitive physical flow data with genuine finite positive initial real flux. -/
structure FiniteFlowData (p : MassiveParameters) (g : Covector → Mat4) (R S : Covector → ℝ)
    (Phi : ℝ × (Fin 3 → ℝ) → (Fin 3 → ℝ)) (T : ℝ) (A : Set (Fin 3 → ℝ))
    : Prop extends FlowData p g R S Phi T A where
  initial_integrable : IntegrableOn (fun a => density p g R S (0, a)) A volume
  initial_flux_pos : 0 < ∫ a in A, density p g R S (0, a)

/-- Actual future geometry supplies real initial nonnegativity before extended-mass interpretation. -/
theorem FlowData.initial_nonneg_ae (h : FlowData p g R S Phi T A) :
    ∀ᵐ a ∂(volume : Measure (Fin 3 → ℝ)).restrict A, 0 ≤ density p g R S (0, a) := by
  filter_upwards [ae_restrict_mem h.domain_measurable] with a ha
  exact (h.initial_density_pos ha).le

/-- Genuine initial integrability identifies the true extended mass with the finite real flux integral. -/
theorem FiniteFlowData.initialMass_eq (h : FiniteFlowData p g R S Phi T A) :
    initialMass p g R S A = ENNReal.ofReal (∫ a in A, density p g R S (0, a)) :=
  WeightedProbabilityTransport.withDensity_mass_eq_ofReal_integral (volume.restrict A)
    h.initial_integrable h.toFlowData.initial_nonneg_ae

/-- Genuine positive finite initial mass follows from actual real integrability and future density positivity. -/
theorem FiniteFlowData.initialMass_pos_finite (h : FiniteFlowData p g R S Phi T A) :
    0 < initialMass p g R S A ∧ initialMass p g R S A < ∞ :=
  WeightedProbabilityTransport.withDensity_finite_positive_mass (volume.restrict A)
    h.initial_integrable h.toFlowData.initial_nonneg_ae h.initial_flux_pos

/-- The actual finite positive initial current normalizes to a genuine probability measure. -/
theorem FiniteFlowData.initial_probability (h : FiniteFlowData p g R S Phi T A) :
    IsProbabilityMeasure (normalizedInitial p g R S A) :=
  WeightedProbabilityTransport.normalized_probability
    h.initialMass_pos_finite.1 h.initialMass_pos_finite.2

/-- The same conserved initial mass normalizes each actual transported current to probability. -/
theorem FiniteFlowData.current_probability (h : FiniteFlowData p g R S Phi T A)
    (ht : t ∈ Icc 0 T) : IsProbabilityMeasure (normalizedCurrent p g R S Phi A t) :=
  WeightedProbabilityTransport.normalized_target_probability (h.toFlowData.aemeasurable_slice ht)
    (h.toFlowData.current_pushforward ht) h.initialMass_pos_finite.1 h.initialMass_pos_finite.2

/-- The exact Euclidean current density is a genuine probability at every claimed time. -/
theorem FiniteFlowData.euclidean_current_probability (h : FiniteFlowData p g R S Phi T A)
    (ht : t ∈ Icc 0 T) : IsProbabilityMeasure (euclideanCurrent p g R S Phi A t) := by
  let := h.current_probability ht
  rw [← normalizedCurrent_map_toLp p g R S Phi A t]
  infer_instance

/-- The bundled initial probability contains the actual normalized geometric current measure. -/
def initialProbability (h : FiniteFlowData p g R S Phi T A) : ProbabilityMeasure (Fin 3 → ℝ) :=
  ⟨normalizedInitial p g R S A, h.initial_probability⟩

/-- The actual Euclidean current probability is explicitly extended by a fixed point mass outside the certified interval. -/
def currentProbability (h : FiniteFlowData p g R S Phi T A) (t : ℝ) :
    ProbabilityMeasure (EuclideanSpace ℝ (Fin 3)) :=
  if ht : t ∈ Icc 0 T then
    ⟨euclideanCurrent p g R S Phi A t, h.euclidean_current_probability ht⟩
  else (Measure.dirac (0 : EuclideanSpace ℝ (Fin 3))).toProbabilityMeasure

/-- On the claimed interval the probability realization is exactly the literal Euclidean current density. -/
theorem currentProbability_eq_density (h : FiniteFlowData p g R S Phi T A) (ht : t ∈ Icc 0 T) :
    (currentProbability h t : Measure (EuclideanSpace ℝ (Fin 3))) =
      euclideanCurrent p g R S Phi A t := by
  simp only [currentProbability, dite_eq_left ht, ProbabilityMeasure.coe_mk]

/-- On the certified interval the current probability equals the genuine measurable spatial pushforward. -/
theorem currentProbability_eq_map (h : FiniteFlowData p g R S Phi T A) (ht : t ∈ Icc 0 T) :
    currentProbability h t = (initialProbability h).map (fun a => WithLp.toLp 2 (Phi (t, a))) := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [currentProbability_eq_density h ht]
  exact (h.toFlowData.euclidean_current_pushforward ht).symm

/-- An actual image identity gives the full fixed-domain normalized current law. -/
theorem FlowData.normalized_current_pushforward_fixed (h : FlowData p g R S Phi T A)
    (ht : t ∈ Icc 0 T) (himage : (fun a => Phi (t, a)) '' A = A) :
    (normalizedInitial p g R S A).map (fun a => Phi (t, a)) =
      (initialMass p g R S A)⁻¹ • sliceMeasure p g R S A t := by
  simpa only [normalizedCurrent, himage] using h.normalized_current_pushforward ht

/-- Actual forward preservation and a region-preserving right inverse give full fixed-slice physical transport. -/
theorem FlowData.normalized_current_pushforward_of_inverse_preservation
    (h : FlowData p g R S Phi T A) (ht : t ∈ Icc 0 T) {psi : (Fin 3 → ℝ) → (Fin 3 → ℝ)}
    (hforward : MapsTo (fun a => Phi (t, a)) A A) (hback : MapsTo psi A A)
    (hright : ∀ y ∈ A, Phi (t, psi y) = y) :
    (normalizedInitial p g R S A).map (fun a => Phi (t, a)) =
      (initialMass p g R S A)⁻¹ • sliceMeasure p g R S A t :=
  h.normalized_current_pushforward_fixed ht
    (image_eq_of_forward_inverse_preservation hforward hback hright)

end FoliationQM.CurvedCurrentTransport
