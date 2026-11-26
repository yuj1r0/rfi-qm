module

public import FoliationQM.ConeManifold
public import FoliationQM.CanonicalPolarMetric
public import Mathlib.Topology.MetricSpace.Completion

/-!
# The genuine intrinsic metric for every positive cone coupling

Sources: v13 `lem:uniqueness`, `eq:unique_params`.
The distance is the finite infimum of the actual source lengths of C1 paths.
Uniform speed comparisons prove quantitative bounds, separation, and the
compatibility of this metric with the original punctured-plane topology.
The physical coordinate bijection to the canonical polar space is bi-Lipschitz;
it is not asserted to be an isometry at noncanonical coupling.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.ConeIntrinsicMetric

open Set Topology ConeManifold
open scoped ENNReal NNReal Manifold

/-- Every actual cone path has length at least the uniform lower factor times
its Euclidean endpoint distance. Taking the genuine path infimum retains this bound. -/
theorem intrinsicEDist_lower_bound (hbar coupling : ℝ) (hh : 0 < hbar)
    (hc : 0 < coupling) (p q : Point hbar coupling) :
    ENNReal.ofReal (ConeSpeed.lowerFactor hbar coupling) * edist p.value q.value ≤
      intrinsicEDist hbar coupling p q := by
  apply le_of_forall_gt
  intro r hr
  obtain ⟨γ, hzero, hone, hsmooth, hlen⟩ :=
    Manifold.exists_lt_of_riemannianEDist_lt hr
  have ha : PuncturedPlaneDetour.Admissible p.value q.value (fun t => (γ t).value) :=
    ⟨contDiffOn_value_curve hsmooth, congrArg Point.value hzero,
      congrArg Point.value hone, fun t _ => (γ t).value_ne_zero⟩
  have hlo := ConeSpeed.curveELength_lower_bound hbar coupling hh hc (fun t => (γ t).value)
  have hlength : ConeSpeed.curveELength hbar coupling (fun t => (γ t).value) =
      Manifold.pathELength 𝓘(ℝ, ℂ) γ 0 1 :=
    (pathELength_eq_integral γ 0 1).symm
  exact ((mul_le_mul' (le_refl _) (PuncturedPlaneDetour.edist_le_curveELength ha)).trans
    (hlo.trans_eq hlength)).trans_lt hlen

/-- Euclidean detours and the upper speed bound give a global finite upper
bound on the actual cone path infimum. -/
theorem intrinsicEDist_upper_bound (hbar coupling : ℝ) (p q : Point hbar coupling) :
    intrinsicEDist hbar coupling p q ≤
      ENNReal.ofReal (ConeSpeed.upperFactor hbar coupling) * edist p.value q.value := by
  rw [← PuncturedPlaneDetour.intrinsicEDist_eq_edist p.value_ne_zero q.value_ne_zero,
    PuncturedPlaneDetour.intrinsicEDist]
  have hn : ENNReal.ofReal (ConeSpeed.upperFactor hbar coupling) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (ConeSpeed.upperFactor_pos hbar coupling)
  simp_rw [ENNReal.mul_iInf_of_ne hn ENNReal.ofReal_ne_top]
  apply le_iInf
  intro γ
  apply le_iInf
  intro hγ
  exact (ConeManifold.intrinsicEDist_le_curveELength p q hγ).trans
    (ConeSpeed.curveELength_upper_bound hbar coupling γ)

/-- All pairs have finite actual intrinsic distance. -/
theorem intrinsicEDist_ne_top (hbar coupling : ℝ) (p q : Point hbar coupling) :
    intrinsicEDist hbar coupling p q ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (edist_ne_top _ _))
    (intrinsicEDist_upper_bound hbar coupling p q)

/-- The real distance is obtained from the proved finite path infimum. -/
def intrinsicDist (hbar coupling : ℝ) (p q : Point hbar coupling) : ℝ :=
  (intrinsicEDist hbar coupling p q).toReal

/-- The real intrinsic distance has the same positive lower comparison. -/
theorem intrinsicDist_lower_bound (hbar coupling : ℝ) (hh : 0 < hbar)
    (hc : 0 < coupling) (p q : Point hbar coupling) :
    ConeSpeed.lowerFactor hbar coupling * dist p.value q.value ≤ intrinsicDist hbar coupling p q := by
  have h := ENNReal.toReal_mono (intrinsicEDist_ne_top hbar coupling p q)
    (intrinsicEDist_lower_bound hbar coupling hh hc p q)
  simpa only [intrinsicDist, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (ConeSpeed.lowerFactor_pos hbar coupling hh hc).le,
    edist_dist, ENNReal.toReal_ofReal dist_nonneg] using h

/-- The real intrinsic distance has the finite upper comparison. -/
theorem intrinsicDist_upper_bound (hbar coupling : ℝ) (p q : Point hbar coupling) :
    intrinsicDist hbar coupling p q ≤ ConeSpeed.upperFactor hbar coupling * dist p.value q.value := by
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (edist_ne_top _ _))
    (intrinsicEDist_upper_bound hbar coupling p q)
  simpa only [intrinsicDist, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (ConeSpeed.upperFactor_pos hbar coupling).le,
    edist_dist, ENNReal.toReal_ofReal dist_nonneg] using h

/-- Self-distance of the actual real path infimum is zero. -/
theorem intrinsicDist_self (hbar coupling : ℝ) (p : Point hbar coupling) :
    intrinsicDist hbar coupling p p = 0 := by
  simp only [intrinsicDist, intrinsicEDist_self, ENNReal.toReal_zero]

/-- Symmetry descends from reversal of actual paths. -/
theorem intrinsicDist_comm (hbar coupling : ℝ) (p q : Point hbar coupling) :
    intrinsicDist hbar coupling p q = intrinsicDist hbar coupling q p := by
  rw [intrinsicDist, intrinsicDist, intrinsicEDist_comm]

/-- The triangle inequality descends from actual path reparameterization and gluing. -/
theorem intrinsicDist_triangle (hbar coupling : ℝ) (p q r : Point hbar coupling) :
    intrinsicDist hbar coupling p r ≤ intrinsicDist hbar coupling p q +
      intrinsicDist hbar coupling q r := by
  rw [intrinsicDist, intrinsicDist, intrinsicDist, ← ENNReal.toReal_add
    (intrinsicEDist_ne_top hbar coupling p q) (intrinsicEDist_ne_top hbar coupling q r)]
  exact ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨intrinsicEDist_ne_top hbar coupling p q,
      intrinsicEDist_ne_top hbar coupling q r⟩) (intrinsicEDist_triangle p q r)

/-- The positive lower bound proves that distinct physical points have positive distance. -/
theorem eq_of_intrinsicDist_eq_zero (hbar coupling : ℝ) (hh : 0 < hbar)
    (hc : 0 < coupling) (p q : Point hbar coupling) (h : intrinsicDist hbar coupling p q = 0) :
    p = q := by
  apply value_injective
  apply eq_of_dist_eq_zero
  have hlo := intrinsicDist_lower_bound hbar coupling hh hc p q
  rw [h] at hlo
  exact le_antisymm (nonpos_of_mul_nonpos_right hlo (ConeSpeed.lowerFactor_pos hbar coupling hh hc))
    dist_nonneg

private theorem open_iff_comparable {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
    (f : X → Y) (hf : IsEmbedding f) (d : X → X → ℝ)
    {c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hlo : ∀ x y, c * dist (f x) (f y) ≤ d x y)
    (hhi : ∀ x y, d x y ≤ C * dist (f x) (f y)) (s : Set X) :
    IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ∀ y, d x y < ε → y ∈ s := by
  let : MetricSpace X := (MetricSpace.induced f hf.injective inferInstance).replaceTopology
    hf.isInducing.eq_induced
  have hd (x y : X) : dist x y = dist (f x) (f y) := rfl
  constructor
  · intro hs x hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hs x hx
    refine ⟨c * ε, mul_pos hc hε, ?_⟩
    intro y hy
    apply hball
    rw [Metric.mem_ball, hd, dist_comm]
    exact (mul_lt_mul_iff_right₀ hc).mp ((hlo x y).trans_lt hy)
  · intro hs
    apply Metric.isOpen_iff.mpr
    intro x hx
    obtain ⟨ε, hε, he⟩ := hs x hx
    refine ⟨ε / C, div_pos hε hC, ?_⟩
    intro y hy
    apply he y
    have hxy : dist (f x) (f y) < ε / C := by
      simpa only [Metric.mem_ball, hd, dist_comm] using hy
    apply (hhi x y).trans_lt
    simpa only [mul_comm] using (lt_div_iff₀ hC).mp hxy

/-- The path metric has exactly the previously constructed manifold topology. -/
theorem isOpen_iff_intrinsicDist (hbar coupling : ℝ) (hh : 0 < hbar)
    (hc : 0 < coupling) (s : Set (Point hbar coupling)) :
    IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ∀ y, intrinsicDist hbar coupling x y < ε → y ∈ s :=
  open_iff_comparable Point.value isEmbedding_value (intrinsicDist hbar coupling)
    (ConeSpeed.lowerFactor_pos hbar coupling hh hc) (ConeSpeed.upperFactor_pos hbar coupling)
    (intrinsicDist_lower_bound hbar coupling hh hc) (intrinsicDist_upper_bound hbar coupling) s

variable (hbar coupling : ℝ) [Fact (0 < hbar)] [Fact (0 < coupling)]

/-- The actual finite intrinsic metric, with its topology definitionally equal
to the ordinary punctured-plane manifold topology. -/
instance instMetricSpace : MetricSpace (Point hbar coupling) :=
  MetricSpace.ofDistTopology (intrinsicDist hbar coupling)
    (intrinsicDist_self hbar coupling) (intrinsicDist_comm hbar coupling)
    (intrinsicDist_triangle hbar coupling)
    (isOpen_iff_intrinsicDist hbar coupling Fact.out Fact.out)
    (eq_of_intrinsicDist_eq_zero hbar coupling Fact.out Fact.out)

/-- The registered metric distance is the actual curve-length infimum. -/
theorem dist_eq_intrinsicDist (p q : Point hbar coupling) :
    dist p q = intrinsicDist hbar coupling p q := rfl

/-- The registered extended distance is exactly Mathlib's source-speed path infimum. -/
theorem edist_eq_intrinsicEDist (p q : Point hbar coupling) :
    edist p q = intrinsicEDist hbar coupling p q := by
  rw [edist_dist, dist_eq_intrinsicDist, intrinsicDist,
    ENNReal.ofReal_toReal (intrinsicEDist_ne_top hbar coupling p q)]

/-- The physical coordinate bijection keeps density and phase fixed. -/
def canonicalEquiv : Point hbar coupling ≃ CanonicalPolarMetric.Point where
  toFun p := CanonicalPolarMetric.fromComplex p.value p.value_ne_zero
  invFun p := ⟨CanonicalPolarMetric.toComplex p, CanonicalPolarMetric.toComplex_ne_zero p⟩
  left_inv _ := value_injective (CanonicalPolarMetric.toComplex_fromComplex _ _)
  right_inv p := CanonicalPolarMetric.fromComplex_toComplex p

omit [Fact (0 < hbar)] [Fact (0 < coupling)] in
/-- The bijection preserves the actual physical complex coordinate. -/
theorem canonicalEquiv_toComplex (p : Point hbar coupling) :
    CanonicalPolarMetric.toComplex (canonicalEquiv hbar coupling p) = p.value :=
  CanonicalPolarMetric.toComplex_fromComplex p.value p.value_ne_zero

omit [Fact (0 < hbar)] [Fact (0 < coupling)] in
/-- Euclidean distance of the canonical images is the coordinate chord distance. -/
theorem canonicalEquiv_dist (p q : Point hbar coupling) :
    dist (canonicalEquiv hbar coupling p) (canonicalEquiv hbar coupling q) =
      dist p.value q.value := by
  rw [← CanonicalPolarMetric.isometry_toComplex.dist_eq,
    canonicalEquiv_toComplex, canonicalEquiv_toComplex]

/-- The physical coordinate bijection has the proved reciprocal lower-factor Lipschitz bound. -/
theorem lipschitz_canonicalEquiv :
    LipschitzWith (⟨ConeSpeed.lowerFactor hbar coupling,
      (ConeSpeed.lowerFactor_pos hbar coupling Fact.out Fact.out).le⟩ : ℝ≥0)⁻¹
      (canonicalEquiv hbar coupling) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  change dist (canonicalEquiv hbar coupling p) (canonicalEquiv hbar coupling q) ≤
    (ConeSpeed.lowerFactor hbar coupling)⁻¹ * intrinsicDist hbar coupling p q
  rw [canonicalEquiv_dist]
  have hlo := intrinsicDist_lower_bound hbar coupling Fact.out Fact.out p q
  have hp := ConeSpeed.lowerFactor_pos hbar coupling Fact.out Fact.out
  exact (le_inv_mul_iff₀ hp).mpr hlo

/-- The same bijection has the proved upper-factor inverse Lipschitz bound. -/
theorem antilipschitz_canonicalEquiv :
    AntilipschitzWith (⟨ConeSpeed.upperFactor hbar coupling,
      (ConeSpeed.upperFactor_pos hbar coupling).le⟩ : ℝ≥0)
      (canonicalEquiv hbar coupling) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro p q
  rw [canonicalEquiv_dist, dist_eq_intrinsicDist]
  exact intrinsicDist_upper_bound hbar coupling p q

omit [Fact (0 < coupling)] in
/-- At canonical coupling both quantitative speed factors are exactly one. -/
theorem canonical_factors (hc : coupling = hbar ^ 2 / 4) :
    ConeSpeed.lowerFactor hbar coupling = 1 ∧ ConeSpeed.upperFactor hbar coupling = 1 := by
  have hh : hbar ≠ 0 := ne_of_gt (show 0 < hbar from Fact.out)
  have hr : ConeSpeed.radialFactorSq hbar coupling = 1 := by
    rw [hc, ConeSpeed.radialFactorSq]
    field_simp
  simp [ConeSpeed.lowerFactor, ConeSpeed.upperFactor, hr]

/-- The general path metric specializes to the exact Euclidean chord distance
at canonical coupling, consistently with the earlier canonical construction. -/
theorem dist_canonical (hc : coupling = hbar ^ 2 / 4) (p q : Point hbar coupling) :
    dist p q = dist p.value q.value := by
  obtain ⟨hl, hu⟩ := canonical_factors hbar coupling hc
  have hlo := intrinsicDist_lower_bound hbar coupling Fact.out Fact.out p q
  have hhi := intrinsicDist_upper_bound hbar coupling p q
  rw [hl, one_mul] at hlo
  rw [hu, one_mul] at hhi
  exact le_antisymm hhi hlo

/-- The actual general intrinsic metric and previously verified canonical metric
are isometric at the canonical coupling. -/
theorem isometry_canonicalEquiv (hc : coupling = hbar ^ 2 / 4) :
    Isometry (canonicalEquiv hbar coupling) := by
  apply Isometry.of_dist_eq
  intro p q
  rw [canonicalEquiv_dist, dist_canonical hbar coupling hc]

end FoliationQM.ConeIntrinsicMetric
