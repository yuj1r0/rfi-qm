module

public import FoliationQM.ConeSpeed
public import Mathlib.Geometry.Manifold.Riemannian.PathELength
public import Mathlib.Geometry.Manifold.ContMDiff.Basic

/-!
# The punctured cone chart and its genuine intrinsic extended distance

Source: v13 `lem:uniqueness`, general positive-coupling metric construction.
The punctured complex coordinate carries its ordinary topology and a single
global manifold chart. Tangent lengths come from the actual source tensor.
The intrinsic distance is Mathlib's infimum over actual `C¹` manifold paths;
its triangle inequality is proved by reparameterization and gluing, not assumed.
Metric separation, finiteness and completion are separate consequences of the
uniform speed bounds.
-/

@[expose] public section

noncomputable section

namespace FoliationQM.ConeManifold

open Set MeasureTheory Topology
open scoped Manifold ContDiff ENNReal

/-- A nonzero physical complex coordinate, with parameters tagging its metric. -/
structure Point (hbar coupling : ℝ) where
  value : ℂ
  value_ne_zero : value ≠ 0

variable {hbar coupling : ℝ}

/-- The punctured coordinate type is nonempty. -/
instance : Nonempty (Point hbar coupling) := ⟨⟨1, one_ne_zero⟩⟩

/-- Before constructing any distance, the topology is the ordinary punctured
complex-plane topology. -/
instance : TopologicalSpace (Point hbar coupling) :=
  TopologicalSpace.induced Point.value inferInstance

/-- The physical coordinate distinguishes all points. -/
theorem value_injective : Function.Injective (Point.value (hbar := hbar) (coupling := coupling)) := by
  intro p q h
  cases p
  cases q
  cases h
  rfl

/-- The physical coordinate is a topological embedding by construction. -/
theorem isEmbedding_value : IsEmbedding (Point.value (hbar := hbar) (coupling := coupling)) :=
  ⟨⟨rfl⟩, value_injective⟩

/-- The global chart image is exactly the punctured complex plane. -/
theorem range_value : Set.range (Point.value (hbar := hbar) (coupling := coupling)) =
    {z : ℂ | z ≠ 0} := by
  ext z
  exact ⟨fun ⟨p, hp⟩ => hp ▸ p.value_ne_zero, fun hz => ⟨⟨z, hz⟩, rfl⟩⟩

/-- The coordinate is an open embedding, hence a legitimate global chart. -/
theorem isOpenEmbedding_value : IsOpenEmbedding
    (Point.value (hbar := hbar) (coupling := coupling)) := by
  refine ⟨isEmbedding_value, ?_⟩
  rw [range_value]
  exact isOpen_ne

/-- The single coordinate gives the punctured plane its ordinary manifold atlas. -/
instance : ChartedSpace ℂ (Point hbar coupling) :=
  isOpenEmbedding_value.singletonChartedSpace

/-- Every chosen chart is the same physical complex coordinate. -/
theorem chartAt_value (p q : Point hbar coupling) : chartAt ℂ p q = q.value := rfl

/-- The atlas is smooth to every order. -/
instance (n : ℕ∞ω) : IsManifold 𝓘(ℝ, ℂ) n (Point hbar coupling) :=
  isOpenEmbedding_value.isManifold_singleton

/-- The global physical coordinate is smooth. -/
theorem contMDiff_value (n : ℕ∞ω) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n
      (Point.value (hbar := hbar) (coupling := coupling)) :=
  contMDiff_isOpenEmbedding isOpenEmbedding_value

/-- Tangents in the single global chart are real-linear complex vectors. -/
def tangentCoordinate (p : Point hbar coupling) : TangentSpace 𝓘(ℝ, ℂ) p ≃L[ℝ] ℂ :=
  tangentSpaceCastModel 𝓘(ℝ, ℂ) p

/-- Tangent extended norms are the square roots of the actual source tensor. -/
instance (p : Point hbar coupling) : ENorm (TangentSpace 𝓘(ℝ, ℂ) p) :=
  ⟨fun v => ENNReal.ofReal (ConeSpeed.speed hbar coupling p.value (tangentCoordinate p v))⟩

/-- Source tangent lengths scale by the absolute value of a real scalar. -/
instance (p : Point hbar coupling) : ENormSMulClass ℝ (TangentSpace 𝓘(ℝ, ℂ) p) where
  enorm_smul a v := by
    change ENNReal.ofReal (ConeSpeed.speed hbar coupling p.value
      (tangentCoordinate p (a • v))) = ‖a‖ₑ *
        ENNReal.ofReal (ConeSpeed.speed hbar coupling p.value (tangentCoordinate p v))
    rw [map_smul, ConeSpeed.speed_smul, ENNReal.ofReal_mul (abs_nonneg a),
      Real.enorm_eq_ofReal_abs]

/-- The genuine manifold path infimum using the source tangent lengths. -/
def intrinsicEDist (hbar coupling : ℝ) (p q : Point hbar coupling) : ℝ≥0∞ :=
  Manifold.riemannianEDist 𝓘(ℝ, ℂ) p q

/-- Constant paths give zero self-distance. -/
theorem intrinsicEDist_self (p : Point hbar coupling) : intrinsicEDist hbar coupling p p = 0 :=
  Manifold.riemannianEDist_self

/-- Reversing actual paths gives symmetry of the path infimum. -/
theorem intrinsicEDist_comm (p q : Point hbar coupling) :
    intrinsicEDist hbar coupling p q = intrinsicEDist hbar coupling q p :=
  Manifold.riemannianEDist_comm

/-- Reparameterizing and gluing actual `C¹` paths proves the triangle inequality. -/
theorem intrinsicEDist_triangle (p q r : Point hbar coupling) :
    intrinsicEDist hbar coupling p r ≤
      intrinsicEDist hbar coupling p q + intrinsicEDist hbar coupling q r :=
  Manifold.riemannianEDist_triangle

/-- The manifold derivative of an actual curve is its ordinary coordinate
derivative, represented in the single global chart. -/
theorem tangentCoordinate_mfderiv_curve (γ : ℝ → Point hbar coupling) (t : ℝ) :
    tangentCoordinate (γ t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ t 1) =
      deriv (fun u => (γ u).value) t := by
  have hw : writtenInExtChartAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) t γ = fun u => (γ u).value := by
    ext u
    simp [writtenInExtChartAt, extChartAt]
  have hd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ t ↔
      DifferentiableAt ℝ (fun u => (γ u).value) t := by
    rw [mdifferentiableAt_iff, hw]
    rw [modelWithCornersSelf_coe, Set.range_id, ext_chart_model_space_apply,
      differentiableWithinAt_univ]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨isEmbedding_value.isInducing.continuousAt_iff.mpr h.continuousAt, h⟩
  rw [mfderiv, hd]
  split_ifs with h
  · rw [hw, modelWithCornersSelf_coe, Set.range_id, ext_chart_model_space_apply,
      fderivWithin_univ]
    change (fderiv ℝ (fun u => (γ u).value) t) (1 : ℝ) = _
    rw [fderiv_apply_one_eq_deriv]
  · simp [tangentCoordinate, deriv_zero_of_not_differentiableAt h]

/-- The actual manifold path length is exactly the integral of the source
speed of its ordinary complex-coordinate derivative. -/
theorem pathELength_eq_integral (γ : ℝ → Point hbar coupling) (a b : ℝ) :
    Manifold.pathELength 𝓘(ℝ, ℂ) γ a b =
      ∫⁻ t in Icc a b, ENNReal.ofReal
        (ConeSpeed.speed hbar coupling (γ t).value (deriv (fun u => (γ u).value) t)) := by
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  apply lintegral_congr
  intro t
  change ENNReal.ofReal (ConeSpeed.speed hbar coupling (γ t).value
    (tangentCoordinate (γ t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ t 1))) = _
  rw [tangentCoordinate_mfderiv_curve]

/-- A manifold `C¹` curve has an ordinary `C¹` complex coordinate on the
same parameter set. -/
theorem contDiffOn_value_curve {γ : ℝ → Point hbar coupling} {s : Set ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 γ s) :
    ContDiffOn ℝ 1 (fun t => (γ t).value) s := by
  exact contMDiffOn_iff_contDiffOn.mp ((contMDiff_value 1).comp_contMDiffOn hγ)

/-- Ordinary `C¹` regularity of the complex coordinate also suffices for
manifold `C¹` regularity on the same parameter set. -/
theorem contMDiffOn_curve_of_contDiffOn_value {γ : ℝ → Point hbar coupling} {s : Set ℝ}
    (hγ : ContDiffOn ℝ 1 (fun t => (γ t).value) s) :
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 γ s := by
  intro t ht
  rw [contMDiffWithinAt_iff]
  constructor
  · exact isEmbedding_value.isInducing.continuousWithinAt_iff.mpr
      ((hγ t ht).continuousWithinAt)
  · simpa [extChartAt, Function.comp_def] using hγ t ht

/-- The source intrinsic distance is bounded by the actual weighted length
of every `C¹` complex curve that avoids zero on the parameter interval. -/
theorem intrinsicEDist_le_curveELength (p q : Point hbar coupling) {γ : ℝ → ℂ}
    (hγ : PuncturedPlaneDetour.Admissible p.value q.value γ) :
    intrinsicEDist hbar coupling p q ≤ ConeSpeed.curveELength hbar coupling γ := by
  let η : ℝ → Point hbar coupling := fun t =>
    ⟨γ (projIcc 0 1 zero_le_one t),
      hγ.2.2.2 _ (projIcc 0 1 zero_le_one t).property⟩
  have hval : EqOn (fun t => (η t).value) γ (Icc 0 1) := by
    intro t ht
    simp [η, projIcc_of_mem, ht]
  have hη : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 η (Icc 0 1) :=
    contMDiffOn_curve_of_contDiffOn_value (hγ.1.congr hval)
  have h0 : η 0 = p := by
    apply value_injective
    exact (hval ⟨le_rfl, zero_le_one⟩).trans hγ.2.1
  have h1 : η 1 = q := by
    apply value_injective
    exact (hval ⟨zero_le_one, le_rfl⟩).trans hγ.2.2.1
  have hle := Manifold.riemannianEDist_le_pathELength hη h0 h1 zero_le_one
  apply hle.trans_eq
  rw [pathELength_eq_integral, ConeSpeed.curveELength]
  simp only [← restrict_Ioo_eq_restrict_Icc]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have he : (fun u => (η u).value) =ᶠ[𝓝 t] γ := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
    exact hval ⟨hu.1.le, hu.2.le⟩
  dsimp only
  have htEq : (η t).value = γ t := hval ⟨ht.1.le, ht.2.le⟩
  rw [htEq, he.deriv_eq]

end FoliationQM.ConeManifold
