module

public import FoliationQM.ConeIntrinsicMetric
public import FoliationQM.EquivalentMetricCompletion
public import FoliationQM.CanonicalCompletion

/-!
# Genuine metric completion of the positive-coupling cone

Sources: v13 `lem:uniqueness` and `eq:cone_angle`, general positive-coupling
completion topology. The completed space is the actual uniform completion of
the intrinsic cone metric. The proved upper and lower distance bounds supply
its uniform equivalence to the canonical completion; only then is the latter's
complex coordinate used to identify its topology and unique added point.

For every positive coupling the completion has precisely one tip, and density
tends to zero exactly when a family converges to it. The resulting complex
coordinate is a homeomorphism. No Euclidean isometry or smooth noncanonical
tip is asserted.
-/
@[expose] public section

noncomputable section

namespace FoliationQM.ConeCompletion

open UniformSpace Filter Topology
open ConeIntrinsicMetric
open scoped NNReal

variable (hbar coupling : ℝ) [Fact (0 < hbar)] [Fact (0 < coupling)]

/-- The actual uniform completion of the genuine intrinsic cone metric. -/
abbrev Completed := Completion (ConeManifold.Point hbar coupling)

/-- The metric comparison induces a uniform equivalence of actual completions. -/
def canonicalCompletionEquiv : Completed hbar coupling ≃ᵤ CanonicalCompletion.Completed :=
  EquivalentMetricCompletion.completionEquiv (canonicalEquiv hbar coupling)
    (lipschitz_canonicalEquiv hbar coupling) (antilipschitz_canonicalEquiv hbar coupling)

/-- The genuine positive-coupling completion is homeomorphic to the complex
plane; this is a topological identification, not an isometry assertion. -/
def complexHomeomorph : Completed hbar coupling ≃ₜ ℂ :=
  (canonicalCompletionEquiv hbar coupling).toHomeomorph.trans
    CanonicalCompletion.complexEquiv.toHomeomorph

/-- The physical complex coordinate extended to the intrinsic completion. -/
def coordinate : Completed hbar coupling → ℂ := complexHomeomorph hbar coupling

/-- The completed comparison agrees with the original polar bijection. -/
theorem canonicalCompletionEquiv_coe (p : ConeManifold.Point hbar coupling) :
    canonicalCompletionEquiv hbar coupling (p : Completed hbar coupling) =
      (canonicalEquiv hbar coupling p : CanonicalCompletion.Completed) :=
  EquivalentMetricCompletion.completionEquiv_coe (canonicalEquiv hbar coupling)
    (lipschitz_canonicalEquiv hbar coupling) (antilipschitz_canonicalEquiv hbar coupling) p

/-- The completed coordinate preserves every original physical complex value. -/
theorem coordinate_coe (p : ConeManifold.Point hbar coupling) :
    coordinate hbar coupling (p : Completed hbar coupling) = p.value := by
  change CanonicalCompletion.coordinate
    (canonicalCompletionEquiv hbar coupling (p : Completed hbar coupling)) = p.value
  rw [canonicalCompletionEquiv_coe, CanonicalCompletion.coordinate_coe,
    canonicalEquiv_toComplex]

/-- The completed physical coordinate retains the reciprocal lower-factor
Lipschitz bound proved for the original intrinsic metric. -/
theorem coordinate_lipschitz :
    LipschitzWith (⟨ConeSpeed.lowerFactor hbar coupling,
      (ConeSpeed.lowerFactor_pos hbar coupling Fact.out Fact.out).le⟩ : ℝ≥0)⁻¹
      (coordinate hbar coupling) := by
  have h := CanonicalCompletion.complexEquiv.isometry.lipschitzWith.comp
    (EquivalentMetricCompletion.completionEquiv_lipschitz (canonicalEquiv hbar coupling)
      (lipschitz_canonicalEquiv hbar coupling) (antilipschitz_canonicalEquiv hbar coupling))
  simpa only [one_mul] using! h

/-- The inverse bound also survives completion, so the physical complex
coordinate is quantitatively bi-Lipschitz at every completed point. -/
theorem coordinate_antilipschitz :
    AntilipschitzWith (⟨ConeSpeed.upperFactor hbar coupling,
      (ConeSpeed.upperFactor_pos hbar coupling).le⟩ : ℝ≥0)
      (coordinate hbar coupling) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  have h := (EquivalentMetricCompletion.completionEquiv_antilipschitz
    (canonicalEquiv hbar coupling) (lipschitz_canonicalEquiv hbar coupling)
    (antilipschitz_canonicalEquiv hbar coupling)).le_mul_dist x y
  rw [← CanonicalCompletion.complexEquiv.dist_eq] at h
  simpa only using! h

/-- The tip is obtained by transporting the canonical completion's added point. -/
def tip : Completed hbar coupling :=
  (canonicalCompletionEquiv hbar coupling).symm CanonicalCompletion.tip

/-- The completed comparison carries the cone tip to the canonical tip. -/
theorem canonicalCompletionEquiv_tip :
    canonicalCompletionEquiv hbar coupling (tip hbar coupling) = CanonicalCompletion.tip :=
  (canonicalCompletionEquiv hbar coupling).apply_symm_apply _

/-- The completed physical complex coordinate vanishes at the tip. -/
theorem coordinate_tip : coordinate hbar coupling (tip hbar coupling) = 0 := by
  change CanonicalCompletion.coordinate
    (canonicalCompletionEquiv hbar coupling (tip hbar coupling)) = 0
  rw [canonicalCompletionEquiv_tip, CanonicalCompletion.coordinate_tip]

/-- Distance from any completed point to the tip is bounded below by the
positive lower speed factor times its physical amplitude. -/
theorem dist_tip_lower_bound (x : Completed hbar coupling) :
    ConeSpeed.lowerFactor hbar coupling * ‖coordinate hbar coupling x‖ ≤
      dist x (tip hbar coupling) := by
  have h := (coordinate_lipschitz hbar coupling).dist_le_mul x (tip hbar coupling)
  change dist (coordinate hbar coupling x) (coordinate hbar coupling (tip hbar coupling)) ≤
    (ConeSpeed.lowerFactor hbar coupling)⁻¹ * dist x (tip hbar coupling) at h
  simp only [coordinate_tip, dist_zero_right] at h
  exact (le_inv_mul_iff₀ (ConeSpeed.lowerFactor_pos hbar coupling Fact.out Fact.out)).mp h

/-- Distance from any completed point to the tip is bounded above by the
finite upper speed factor times its physical amplitude. -/
theorem dist_tip_upper_bound (x : Completed hbar coupling) :
    dist x (tip hbar coupling) ≤
      ConeSpeed.upperFactor hbar coupling * ‖coordinate hbar coupling x‖ := by
  have h := (coordinate_antilipschitz hbar coupling).le_mul_dist x (tip hbar coupling)
  change dist x (tip hbar coupling) ≤ ConeSpeed.upperFactor hbar coupling *
    dist (coordinate hbar coupling x) (coordinate hbar coupling (tip hbar coupling)) at h
  simpa only [coordinate_tip, dist_zero_right] using h

/-- Zero physical complex coordinate characterizes exactly the cone tip. -/
theorem coordinate_eq_zero_iff (x : Completed hbar coupling) :
    coordinate hbar coupling x = 0 ↔ x = tip hbar coupling := by
  change CanonicalCompletion.coordinate (canonicalCompletionEquiv hbar coupling x) = 0 ↔
    x = (canonicalCompletionEquiv hbar coupling).symm CanonicalCompletion.tip
  rw [CanonicalCompletion.coordinate_eq_zero_iff]
  exact (canonicalCompletionEquiv hbar coupling).toEquiv.eq_symm_apply.symm

/-- The genuine intrinsic completion adds exactly one point. -/
theorem compl_range_coe :
    (Set.range (fun p : ConeManifold.Point hbar coupling => (p : Completed hbar coupling)))ᶜ =
      {tip hbar coupling} :=
  EquivalentMetricCompletion.compl_range_coe_eq_singleton (canonicalEquiv hbar coupling)
    (lipschitz_canonicalEquiv hbar coupling) (antilipschitz_canonicalEquiv hbar coupling)
    CanonicalCompletion.tip CanonicalCompletion.compl_range_coe

/-- Every point away from the tip belongs to the original punctured cone. -/
theorem mem_range_coe_iff (x : Completed hbar coupling) :
    x ∈ Set.range (fun p : ConeManifold.Point hbar coupling => (p : Completed hbar coupling)) ↔
      x ≠ tip hbar coupling := by
  have hx := Set.ext_iff.mp (compl_range_coe hbar coupling) x
  change (¬x ∈ Set.range (fun p : ConeManifold.Point hbar coupling =>
    (p : Completed hbar coupling))) ↔ x = tip hbar coupling at hx
  simpa only [not_not] using (not_congr hx)

/-- The physical Born density extends continuously through the completed tip. -/
def density (x : Completed hbar coupling) : ℝ :=
  CanonicalCompletion.density (canonicalCompletionEquiv hbar coupling x)

/-- The extended density is squared modulus of the preserved physical coordinate. -/
theorem density_eq_norm_sq (x : Completed hbar coupling) :
    density hbar coupling x = ‖coordinate hbar coupling x‖ ^ 2 := rfl

/-- Original points retain precisely their physical squared-modulus density. -/
theorem density_coe (p : ConeManifold.Point hbar coupling) :
    density hbar coupling (p : Completed hbar coupling) = Complex.normSq p.value := by
  rw [density_eq_norm_sq, coordinate_coe, Complex.normSq_eq_norm_sq]

/-- The extended physical density is continuous on the genuine cone completion. -/
theorem continuous_density : Continuous (density hbar coupling) :=
  CanonicalCompletion.continuous_density.comp (canonicalCompletionEquiv hbar coupling).continuous

/-- The completed physical density is everywhere nonnegative. -/
theorem density_nonneg (x : Completed hbar coupling) : 0 ≤ density hbar coupling x :=
  CanonicalCompletion.density_nonneg _

/-- Vanishing density characterizes the unique added cone point. -/
theorem density_eq_zero_iff (x : Completed hbar coupling) :
    density hbar coupling x = 0 ↔ x = tip hbar coupling := by
  rw [density_eq_norm_sq, sq_eq_zero_iff, norm_eq_zero, coordinate_eq_zero_iff]

/-- For arbitrary families, approach to the completed tip is exactly
vanishing density; no hypothesis on winding or phase convergence is required. -/
theorem tendsto_tip_iff_density {ι : Type*} {l : Filter ι}
    {f : ι → Completed hbar coupling} :
    Tendsto f l (𝓝 (tip hbar coupling)) ↔
      Tendsto (fun i => density hbar coupling (f i)) l (𝓝 0) := by
  rw [(canonicalCompletionEquiv hbar coupling).toHomeomorph.isEmbedding.tendsto_nhds_iff]
  change Tendsto (fun i => canonicalCompletionEquiv hbar coupling (f i)) l
    (𝓝 (canonicalCompletionEquiv hbar coupling (tip hbar coupling))) ↔ _
  rw [canonicalCompletionEquiv_tip]
  exact CanonicalCompletion.tendsto_tip_iff_density

/-- Original cone points converge to the unique completed tip exactly when
their physical squared-modulus densities tend to zero. -/
theorem tendsto_coe_tip_iff_density {ι : Type*} {l : Filter ι}
    {f : ι → ConeManifold.Point hbar coupling} :
    Tendsto (fun i => (f i : Completed hbar coupling)) l (𝓝 (tip hbar coupling)) ↔
      Tendsto (fun i => Complex.normSq (f i).value) l (𝓝 0) := by
  simpa only [density_coe] using
    (tendsto_tip_iff_density hbar coupling
      (f := fun i => (f i : Completed hbar coupling)) (l := l))

end FoliationQM.ConeCompletion
