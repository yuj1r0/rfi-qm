module

public import FoliationQM.PolarDifferential
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Topology.MetricSpace.Isometry

/-!
# The canonical metric on positive density and the physical phase circle

Source: v13 `lem:uniqueness`, canonical existence direction. A point has an
actual circle-valued phase and strictly positive density. The fresh structure
carries the metric induced by its injective complex polar map, so there is no
competing product metric instance. Its distances are Euclidean chord distances;
no unproved equality with a separately defined intrinsic path metric is used.
The derivative of every real phase lift recovers the source metric tensor.
-/

@[expose] public section

namespace FoliationQM.CanonicalPolarMetric

/-- A positive density and one physical circle-valued phase. -/
structure Point where
  density : ℝ
  density_pos : 0 < density
  phase : Circle

/-- The canonical global polar coordinate map. -/
noncomputable def toComplex (p : Point) : ℂ :=
  (Real.sqrt p.density : ℂ) * (p.phase : ℂ)

/-- The polar radius is the square root of the positive density. -/
theorem norm_toComplex (p : Point) : ‖toComplex p‖ = Real.sqrt p.density := by
  simp [toComplex, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]

/-- Squared modulus recovers density exactly. -/
theorem normSq_toComplex (p : Point) : Complex.normSq (toComplex p) = p.density := by
  rw [Complex.normSq_eq_norm_sq, norm_toComplex, Real.sq_sqrt p.density_pos.le]

/-- A positive-density polar point never maps to the origin. -/
theorem toComplex_ne_zero (p : Point) : toComplex p ≠ 0 := by
  intro h
  have hn := norm_toComplex p
  rw [h, norm_zero] at hn
  exact (Real.sqrt_pos.mpr p.density_pos).ne' hn.symm

/-- The physical-circle polar map is globally injective. -/
theorem toComplex_injective : Function.Injective toComplex := by
  intro p q h
  have hρ : p.density = q.density := by
    simpa only [normSq_toComplex] using congrArg Complex.normSq h
  have hphase : p.phase = q.phase := by
    apply Circle.coe_injective
    apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr p.density_pos)))
    simpa only [toComplex, hρ] using h
  cases p
  cases q
  cases hρ
  cases hphase
  rfl

/-- The genuine metric induced by the injective Euclidean polar map. -/
noncomputable instance instMetricSpace : MetricSpace Point :=
  MetricSpace.induced toComplex toComplex_injective inferInstance

/-- The global polar map preserves the actual induced metric. -/
theorem isometry_toComplex : Isometry toComplex :=
  MetricSpace.isometry_induced toComplex toComplex_injective

/-- Distances are precisely the complex Euclidean chord distances. -/
theorem dist_eq (p q : Point) : dist p q = ‖toComplex p - toComplex q‖ := by
  rw [← isometry_toComplex.dist_eq p q, dist_eq_norm]

/-- The induced distance vanishes exactly when density and circle phase agree. -/
theorem dist_eq_zero_iff (p q : Point) :
    dist p q = 0 ↔ p.density = q.density ∧ p.phase = q.phase := by
  rw [dist_eq_zero]
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨hρ, hphase⟩
    cases p
    cases q
    cases hρ
    cases hphase
    rfl

/-- Explicit inverse coordinates at a nonzero complex point. -/
noncomputable def fromComplex (z : ℂ) (hz : z ≠ 0) : Point where
  density := Complex.normSq z
  density_pos := Complex.normSq_pos.mpr hz
  phase := ⟨z / (‖z‖ : ℂ), by
    apply mem_sphere_zero_iff_norm.mpr
    simp [Complex.norm_real, norm_ne_zero_iff.mpr hz]⟩

/-- The explicit inverse has the expected density coordinate. -/
theorem fromComplex_density (z : ℂ) (hz : z ≠ 0) :
    (fromComplex z hz).density = Complex.normSq z := rfl

/-- The explicit inverse normalizes the complex point to its unit phase. -/
theorem fromComplex_phase (z : ℂ) (hz : z ≠ 0) :
    ((fromComplex z hz).phase : ℂ) = z / (‖z‖ : ℂ) := rfl

/-- Reconstructing from the explicit inverse returns the complex point. -/
theorem toComplex_fromComplex (z : ℂ) (hz : z ≠ 0) :
    toComplex (fromComplex z hz) = z := by
  change (Real.sqrt (Complex.normSq z) : ℂ) * (z / (‖z‖ : ℂ)) = z
  rw [← Complex.norm_def]
  exact mul_div_cancel₀ z (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz))

/-- The explicit inverse recovers both original polar coordinates. -/
theorem fromComplex_toComplex (p : Point) :
    fromComplex (toComplex p) (toComplex_ne_zero p) = p := by
  apply toComplex_injective
  exact toComplex_fromComplex _ _

/-- The range is exactly the punctured complex plane. -/
theorem range_toComplex : Set.range toComplex = {z : ℂ | z ≠ 0} := by
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    exact toComplex_ne_zero p
  · intro hz
    exact ⟨fromComplex z hz, toComplex_fromComplex z hz⟩

/-- The canonical positive-density image is dense in the full complex plane. -/
theorem denseRange_toComplex : DenseRange toComplex := by
  rw [DenseRange, range_toComplex]
  exact dense_compl_singleton (0 : ℂ)

/-- The global polar map is continuous for the actual metric. -/
theorem continuous_toComplex : Continuous toComplex := isometry_toComplex.continuous

/-- The density coordinate is continuous for the induced metric. -/
theorem continuous_density : Continuous Point.density := by
  have h : Continuous (fun p : Point => ‖toComplex p‖ ^ 2) :=
    continuous_toComplex.norm.pow 2
  simpa only [← Complex.normSq_eq_norm_sq, normSq_toComplex] using h

/-- The circle coordinate is recovered continuously by normalization. -/
theorem continuous_phase : Continuous Point.phase := by
  have h : Continuous (fun p : Point => toComplex p / (‖toComplex p‖ : ℂ)) :=
    continuous_toComplex.div
      (Complex.continuous_ofReal.comp continuous_toComplex.norm)
      (fun p => Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (toComplex_ne_zero p)))
  apply continuous_induced_rng.mpr
  convert h using 1
  funext p
  exact (congrArg (fun q : Point => (q.phase : ℂ)) (fromComplex_toComplex p)).symm

/-- The underlying parameters with their ordinary product topology. -/
abbrev Coordinates := {ρ : ℝ // 0 < ρ} × Circle

/-- Ordinary positive-density and circle coordinates determine a metric point. -/
def ofCoordinates (q : Coordinates) : Point := ⟨q.1, q.1.property, q.2⟩

/-- The induced metric topology agrees with the ordinary polar parameter topology. -/
theorem continuous_ofCoordinates : Continuous ofCoordinates := by
  apply isometry_toComplex.isEmbedding.continuous_iff.mpr
  change Continuous (fun q : Coordinates =>
    (Real.sqrt (q.1 : ℝ) : ℂ) * (q.2 : ℂ))
  exact (Complex.continuous_ofReal.comp
    (Real.continuous_sqrt.comp (continuous_subtype_val.comp continuous_fst))).mul
    (continuous_subtype_val.comp continuous_snd)

/-- The polar parameters and induced metric space are genuinely homeomorphic. -/
noncomputable def coordinatesHomeomorph : Coordinates ≃ₜ Point where
  toFun := ofCoordinates
  invFun := fun p => (⟨p.density, p.density_pos⟩, p.phase)
  left_inv := by intro q; cases q; rfl
  right_inv := by intro p; cases p; rfl
  continuous_toFun := continuous_ofCoordinates
  continuous_invFun := (continuous_density.subtype_mk _).prodMk continuous_phase

/-- The homeomorphism to polar metric points uses the supplied coordinates. -/
theorem coordinatesHomeomorph_apply (q : Coordinates) :
    coordinatesHomeomorph q = ofCoordinates q := rfl

/-- A real phase lift gives an actual point of the physical circle metric. -/
noncomputable def ofLift (ρ θ : ℝ) (hρ : 0 < ρ) : Point :=
  ⟨ρ, hρ, Circle.exp θ⟩

/-- The complex chart of a real lift is the source's canonical polar field. -/
theorem toComplex_ofLift (ρ θ : ℝ) (hρ : 0 < ρ) :
    toComplex (ofLift ρ θ hρ) =
      (Real.sqrt ρ : ℂ) * FoliationQM.phase θ := rfl

/-- A fixed circle ray has its ordinary radial Euclidean distance. -/
theorem dist_same_phase (p q : Point) (hphase : p.phase = q.phase) :
    dist p q = |Real.sqrt p.density - Real.sqrt q.density| := by
  rw [dist_eq]
  simp only [toComplex, hphase, ← sub_mul, norm_mul, Circle.norm_coe, mul_one,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Euclidean target differential of any real lift gives exactly the
canonical positive-density metric tensor. -/
theorem lift_metric_tensor {ρ θ : E → ℝ} {x : E}
    (hρ : DifferentiableAt ℝ ρ x) (hθ : DifferentiableAt ℝ θ x)
    (hpos : 0 < ρ x) (v : E) :
    ‖fderiv ℝ (PolarDifferential.polarField ρ θ) x v‖ ^ 2 =
      (fderiv ℝ ρ x v) ^ 2 / (4 * ρ x) + ρ x * (fderiv ℝ θ x v) ^ 2 :=
  PolarDifferential.fderiv_polarField_norm_sq hρ hθ hpos v

end FoliationQM.CanonicalPolarMetric
