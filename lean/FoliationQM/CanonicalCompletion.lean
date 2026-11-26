module

public import FoliationQM.CanonicalPolarMetric
public import Mathlib.Topology.MetricSpace.Completion

/-!
# Completion of the canonical physical-circle metric

Sources: v13 `lem:uniqueness` and `eq:unique_params`, canonical branch.
The starting space consists of positive densities and physical circle phases,
with the actual metric constructed in `CanonicalPolarMetric`. Its uniform
completion is constructed by Mathlib before it is identified isometrically
with the complex plane. Exactly one point is added, at zero amplitude.

The distance completed here is the explicit Euclidean pullback metric. These
theorems do not identify it with the intrinsic length distance of a source
Riemannian tensor or construct a smooth structure on a noncanonical cone.
-/
@[expose] public section

noncomputable section

namespace FoliationQM.CanonicalCompletion

open CanonicalPolarMetric UniformSpace
open Filter Topology

/-- The genuine uniform completion of the canonical physical-circle metric. -/
abbrev Completed := Completion Point

/-- The complex polar coordinate extends by uniform continuity to the actual
completion of the original metric space. -/
def coordinate : Completed → ℂ := Completion.extension toComplex

/-- The completed coordinate agrees with the original polar coordinate. -/
theorem coordinate_coe (p : Point) : coordinate (p : Completed) = toComplex p :=
  Completion.extension_coe isometry_toComplex.uniformContinuous p

/-- Extension to the completion preserves every distance. -/
theorem isometry_coordinate : Isometry coordinate :=
  isometry_toComplex.completion_extension

/-- The completed coordinate covers the entire complex plane: the complete
isometric image is closed and contains the dense original image. -/
theorem coordinate_surjective : Function.Surjective coordinate := by
  have hs : Set.range toComplex ⊆ Set.range coordinate := by
    rintro z ⟨p, rfl⟩
    exact ⟨(p : Completed), coordinate_coe p⟩
  have hd : Dense (Set.range coordinate) := denseRange_toComplex.mono hs
  have hc : IsClosed (Set.range coordinate) :=
    isometry_coordinate.isClosedEmbedding.isClosed_range
  exact Set.range_eq_univ.mp (hc.closure_eq.symm.trans hd.closure_eq)

/-- The actual completion is isometrically equivalent to the Euclidean
complex plane, rather than being defined to be that plane. -/
def complexEquiv : Completed ≃ᵢ ℂ :=
  { Equiv.ofBijective coordinate
      ⟨isometry_coordinate.injective, coordinate_surjective⟩ with
    isometry_toFun := isometry_coordinate }

/-- The isometric equivalence still uses the original polar coordinate on
each positive-density physical-circle point. -/
theorem complexEquiv_coe (p : Point) : complexEquiv (p : Completed) = toComplex p :=
  coordinate_coe p

/-- The completed coordinate is the unique uniformly continuous extension
of the original physical-circle polar coordinate. -/
theorem coordinate_unique {f : Completed → ℂ} (hf : UniformContinuous f)
    (h : ∀ p : Point, f (p : Completed) = toComplex p) : f = coordinate := by
  exact (Completion.extension_unique isometry_toComplex.uniformContinuous hf
    (fun p => (h p).symm)).symm

/-- The added zero-amplitude point is obtained using the proved equivalence. -/
def tip : Completed := complexEquiv.symm 0

/-- The completion tip has zero complex coordinate. -/
theorem coordinate_tip : coordinate tip = 0 :=
  complexEquiv.apply_symm_apply 0

/-- Zero complex coordinate characterizes exactly the completion tip. -/
theorem coordinate_eq_zero_iff (x : Completed) : coordinate x = 0 ↔ x = tip := by
  rw [← coordinate_tip]
  exact isometry_coordinate.injective.eq_iff

/-- No original positive-density point is the added completion tip. -/
theorem coe_ne_tip (p : Point) : (p : Completed) ≠ tip := by
  intro h
  have hz := congrArg coordinate h
  rw [coordinate_coe, coordinate_tip] at hz
  exact toComplex_ne_zero p hz

/-- Every completion point outside the tip is an original positive-density
physical-circle point, so no further points are introduced. -/
theorem mem_range_coe_iff (x : Completed) :
    x ∈ Set.range (fun p : Point => (p : Completed)) ↔ x ≠ tip := by
  constructor
  · rintro ⟨p, rfl⟩
    exact coe_ne_tip p
  · intro hx
    have hz : coordinate x ≠ 0 := fun h => hx ((coordinate_eq_zero_iff x).1 h)
    refine ⟨fromComplex (coordinate x) hz, ?_⟩
    apply isometry_coordinate.injective
    rw [coordinate_coe, toComplex_fromComplex]

/-- The entire missing set in the original completion embedding is the
singleton consisting of the zero-amplitude tip. -/
theorem compl_range_coe :
    (Set.range (fun p : Point => (p : Completed)))ᶜ = {tip} := by
  ext x
  change ¬x ∈ Set.range (fun p : Point => (p : Completed)) ↔ x = tip
  rw [mem_range_coe_iff]
  exact not_not

/-- Distance to the added tip is exactly the Euclidean amplitude. -/
theorem dist_tip (x : Completed) : dist x tip = ‖coordinate x‖ := by
  rw [← isometry_coordinate.dist_eq, coordinate_tip, dist_zero_right]

/-- On original points, distance to the added tip is the positive square
root of the physical density. -/
theorem dist_coe_tip (p : Point) : dist (p : Completed) tip = Real.sqrt p.density := by
  rw [dist_tip, coordinate_coe, norm_toComplex]

/-- The physical density extends to the completion as squared amplitude. -/
def density (x : Completed) : ℝ := ‖coordinate x‖ ^ 2

/-- The extended density equals the original physical density on the entire
positive-density physical-circle space. -/
theorem density_coe (p : Point) : density (p : Completed) = p.density := by
  rw [density, coordinate_coe, norm_toComplex]
  exact Real.sq_sqrt p.density_pos.le

/-- The extended physical density is continuous, including at the tip. -/
theorem continuous_density : Continuous density :=
  isometry_coordinate.continuous.norm.pow 2

/-- The extended density is everywhere nonnegative. -/
theorem density_nonneg (x : Completed) : 0 ≤ density x := sq_nonneg _

/-- The extended density vanishes exactly at the unique added point. -/
theorem density_eq_zero_iff (x : Completed) : density x = 0 ↔ x = tip := by
  rw [density, sq_eq_zero_iff, norm_eq_zero, coordinate_eq_zero_iff]

/-- The density on the completed space is exactly squared distance from its
unique zero-amplitude tip. -/
theorem density_eq_dist_sq (x : Completed) : density x = dist x tip ^ 2 := by
  rw [dist_tip]
  rfl

/-- Convergence to the completion tip is equivalent to vanishing density,
with no restriction on the phase behavior. -/
theorem tendsto_tip_iff_density {ι : Type*} {l : Filter ι} {f : ι → Completed} :
    Tendsto f l (𝓝 tip) ↔ Tendsto (fun i => density (f i)) l (𝓝 0) := by
  constructor
  · intro h
    simpa [Function.comp_def, density, coordinate_tip] using
      continuous_density.continuousAt.tendsto.comp h
  · intro h
    rw [tendsto_iff_dist_tendsto_zero]
    have hs := Real.continuous_sqrt.continuousAt.tendsto.comp h
    simpa [Function.comp_def, density, Real.sqrt_sq_eq_abs, dist_tip] using hs

/-- A family of original physical-circle points converges to the added tip
exactly when its original positive densities tend to zero. -/
theorem tendsto_coe_tip_iff_density {ι : Type*} {l : Filter ι} {f : ι → Point} :
    Tendsto (fun i => (f i : Completed)) l (𝓝 tip) ↔
      Tendsto (fun i => (f i).density) l (𝓝 0) := by
  simpa only [density_coe] using
    (tendsto_tip_iff_density (f := fun i => (f i : Completed)) (l := l))

end FoliationQM.CanonicalCompletion
