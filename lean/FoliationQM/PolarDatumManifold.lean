module
public import FoliationQM.PolarScalarManifolds
public import FoliationQM.SpecialLinearManifold
public import FoliationQM.PolarDatumSmooth
public import FoliationQM.PolarSignCovering
public import FoliationQM.RegularSpinorManifold
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# The intrinsic eight-dimensional polar datum manifold

Sources: the concrete polar data of v13 `prop:takabayasi` and
`eq:takabayasi_polar`. The actual nonzero complex amplitude and actual
determinant-one matrix coordinates identify the existing datum topology
with the product of their natural subtype topologies. The intrinsic
open-amplitude atlas and the intrinsic rational matrix atlas then supply
an explicit pulled-back product atlas on the same datum space. Its
transitions are exactly product chart transitions, its real model has
dimension eight, and its coordinate homeomorphism is a genuine bundled
diffeomorphism. Hausdorffness uses the existing datum instance and second
countability follows from the actual coordinate homeomorphism.

For arbitrary charted source manifolds, smoothness into the datum
manifold is equivalent to smoothness of the actual complex amplitude and
ambient matrix coordinates, including arbitrary within-set domains.
On normed sources this recovers the independently defined earlier
coordinate regularity predicate. Actual scalar multiplication followed
by the real-linear inverse spinor encoding proves smoothness of the
genuine regular-spinor realization. The actual simultaneous sign
operation is a bundled smooth involution.

This construction uses only the independently specified intrinsic
amplitude and matrix manifolds. It does not obtain the datum atlas from
the spinor realization, choose a global representative of a sign class,
or identify the concrete matrix model with an abstract Spin group.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Operator Manifold
open Function Set Topology
namespace FoliationQM.PolarDatumManifold
open DiracMatrices SpinorMatrix PolarSignQuotient PolarAmplitudeTopology SourcePolarDatum

/-- The intrinsic real normed datum model is the complex amplitude model times the three-complex-coordinate matrix model. -/
abbrev Model := ℂ × SpecialLinearCharts.Model

/-- The chart codomain is Mathlib's tagged product of the intrinsic amplitude and matrix chart spaces. -/
abbrev ChartModel := ModelProd ℂ SpecialLinearCharts.Model

/-- The actual model with corners is the product of the intrinsic nonzero-amplitude and determinant-one matrix models. -/
abbrev model : ModelWithCorners ℝ Model ChartModel :=
  (𝓘(ℝ, ℂ)).prod 𝓘(ℝ, SpecialLinearCharts.Model)

/-- Actual datum coordinates pair its nonzero complex amplitude with its determinant-one matrix, retaining both constraints. -/
def coordinates (d : Datum) : NonzeroComplex × SpecialLinearMatrix :=
  (⟨d.t, d.t_ne_zero⟩, ⟨d.A, d.det_eq_one⟩)

/-- The actual inverse coordinate map assembles a datum from a nonzero complex amplitude and a determinant-one matrix. -/
def ofCoordinates (p : NonzeroComplex × SpecialLinearMatrix) : Datum :=
  ⟨p.1.val, p.2.val, p.1.property, p.2.property⟩

/-- Assembling the actual coordinates of a datum recovers that original datum. -/
theorem ofCoordinates_coordinates (d : Datum) : ofCoordinates (coordinates d) = d := rfl

/-- Extracting the coordinates of an assembled datum recovers both original subtype coordinates. -/
theorem coordinates_ofCoordinates (p : NonzeroComplex × SpecialLinearMatrix) :
    coordinates (ofCoordinates p) = p := rfl

/-- The existing natural datum topology is homeomorphic to the intrinsic amplitude and determinant-one matrix product through its actual coordinates. -/
def coordinateHomeomorph : Datum ≃ₜ NonzeroComplex × SpecialLinearMatrix where
  toFun := coordinates
  invFun := ofCoordinates
  left_inv := ofCoordinates_coordinates
  right_inv := coordinates_ofCoordinates
  continuous_toFun := (PolarDatumTopology.continuous_t.subtype_mk _).prodMk
    (PolarDatumTopology.continuous_A.subtype_mk _)
  continuous_invFun := PolarDatumTopology.continuous_iff.mpr
    ⟨continuous_subtype_val.comp continuous_fst, continuous_subtype_val.comp continuous_snd⟩

/-- The natural datum topology is second countable by its actual coordinate homeomorphism to the product of two matrix and scalar subspaces. -/
instance instSecondCountableTopologyDatum : SecondCountableTopology Datum :=
  coordinateHomeomorph.secondCountableTopology

/-- The existing datum topology carries the explicit pullback of the independently constructed intrinsic amplitude and matrix product atlas. -/
instance instChartedSpaceDatum : ChartedSpace ChartModel Datum where
  atlas := {e | ∃ e' ∈ atlas ChartModel (NonzeroComplex × SpecialLinearMatrix),
    e = coordinateHomeomorph.transOpenPartialHomeomorph e'}
  chartAt d := coordinateHomeomorph.transOpenPartialHomeomorph
    (chartAt ChartModel (coordinateHomeomorph d))
  mem_chart_source d := mem_chart_source ChartModel (coordinateHomeomorph d)
  chart_mem_atlas d := ⟨_, chart_mem_atlas ChartModel (coordinateHomeomorph d), rfl⟩

/-- The preferred datum chart is exactly the preferred intrinsic product chart precomposed with the actual coordinate homeomorphism. -/
theorem chartAt_eq (d : Datum) :
    chartAt ChartModel d = coordinateHomeomorph.transOpenPartialHomeomorph
      (chartAt ChartModel (coordinateHomeomorph d)) := rfl

/-- Every actual datum atlas transition is exactly an intrinsic product chart transition, giving a real manifold to every order. -/
instance instIsManifoldDatum (n : WithTop ℕ∞) : IsManifold model n Datum where
  compatible := by
    rintro e e' ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    rw [Homeomorph.transOpenPartialHomeomorph_symm_trans]
    exact (contDiffGroupoid n model).compatible ha hb

/-- The actual coordinate map from the intrinsic datum manifold to the intrinsic product manifold is smooth to every order. -/
theorem contMDiff_coordinates (n : WithTop ℕ∞) :
    ContMDiff model model n coordinates := by
  change ContMDiff model model n coordinateHomeomorph
  intro d
  have hh := (contMDiff_id (I := model) (n := n) :
    ContMDiff model model n (fun p : NonzeroComplex × SpecialLinearMatrix => p))
      (coordinateHomeomorph d)
  rw [contMDiffAt_iff] at hh ⊢
  refine ⟨coordinateHomeomorph.continuous.continuousAt, ?_⟩
  convert hh.2 using 1
  all_goals simp [chartAt_eq, Function.comp_def]
  all_goals rfl

/-- The actual inverse coordinate map from the intrinsic product manifold to the datum manifold is smooth to every order. -/
theorem contMDiff_ofCoordinates (n : WithTop ℕ∞) :
    ContMDiff model model n ofCoordinates := by
  change ContMDiff model model n coordinateHomeomorph.symm
  intro p
  have hh := (contMDiff_id (I := model) (n := n) :
    ContMDiff model model n (fun p : NonzeroComplex × SpecialLinearMatrix => p)) p
  rw [contMDiffAt_iff] at hh ⊢
  refine ⟨coordinateHomeomorph.symm.continuous.continuousAt, ?_⟩
  convert hh.2 using 1
  all_goals simp [chartAt_eq, Function.comp_def]
  all_goals rfl

/-- The actual coordinate homeomorphism is a genuine bundled diffeomorphism for the explicitly constructed intrinsic datum and product atlases. -/
def coordinateDiffeomorph (n : WithTop ℕ∞) :
    Diffeomorph model model Datum (NonzeroComplex × SpecialLinearMatrix) n where
  toEquiv := coordinateHomeomorph.toEquiv
  contMDiff_toFun := contMDiff_coordinates n
  contMDiff_invFun := contMDiff_ofCoordinates n

/-- The coordinate diffeomorphism evaluates to the actual nonzero-amplitude and determinant-one matrix pair. -/
theorem coordinateDiffeomorph_apply (n : WithTop ℕ∞) (d : Datum) :
    coordinateDiffeomorph n d = coordinates d := rfl

/-- The inverse coordinate diffeomorphism evaluates to the actual datum assembled from the two intrinsic factor values. -/
theorem coordinateDiffeomorph_symm_apply (n : WithTop ℕ∞)
    (p : NonzeroComplex × SpecialLinearMatrix) :
    (coordinateDiffeomorph n).symm p = ofCoordinates p := rfl

/-- The bundled coordinate diffeomorphism retains exactly the natural coordinate homeomorphism as its underlying topological map. -/
theorem coordinateDiffeomorph_toHomeomorph (n : WithTop ℕ∞) :
    (coordinateDiffeomorph n).toHomeomorph = coordinateHomeomorph := rfl

/-- The intrinsic amplitude and matrix product model has real dimension eight. -/
theorem model_finrank : Module.finrank ℝ Model = 8 := by
  simp [Model, SpecialLinearCharts.Model, Module.finrank_prod, Module.finrank_pi_fintype,
    Complex.finrank_real_complex]

section GeneralSource
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  {n : WithTop ℕ∞} {f : M → Datum} {s : Set M} {x : M}

/-- For any charted source and any subset, intrinsic datum smoothness is equivalent to manifold smoothness of its actual amplitude and ambient matrix values. -/
theorem contMDiffWithinAt_iff_coordinates :
    ContMDiffWithinAt I model n f s x ↔
      ContMDiffWithinAt I 𝓘(ℝ, ℂ) n (fun y => (f y).t) s x ∧
      ContMDiffWithinAt I 𝓘(ℝ, Mat2) n (fun y => (f y).A) s x := by
  constructor
  · intro hf
    have hp := (coordinateDiffeomorph n).contMDiffAt.comp_contMDiffWithinAt x hf
    exact ⟨PolarScalarManifolds.contMDiffWithinAt_amplitude_iff.mp hp.fst,
      SpecialLinearManifold.contMDiffWithinAt_iff_value.mp hp.snd⟩
  · rintro ⟨ht, hA⟩
    have ht' : ContMDiffWithinAt I 𝓘(ℝ, ℂ) n
        (fun y => (coordinates (f y)).1) s x :=
      PolarScalarManifolds.contMDiffWithinAt_amplitude_iff.mpr ht
    have hA' : ContMDiffWithinAt I 𝓘(ℝ, SpecialLinearCharts.Model) n
        (fun y => (coordinates (f y)).2) s x :=
      SpecialLinearManifold.contMDiffWithinAt_iff_value.mpr hA
    exact (coordinateDiffeomorph n).symm.contMDiffAt.comp_contMDiffWithinAt x
      (ht'.prodMk hA')

/-- For any charted source, intrinsic datum smoothness at a point is equivalent to manifold smoothness of its actual amplitude and ambient matrix values. -/
theorem contMDiffAt_iff_coordinates :
    ContMDiffAt I model n f x ↔
      ContMDiffAt I 𝓘(ℝ, ℂ) n (fun y => (f y).t) x ∧
      ContMDiffAt I 𝓘(ℝ, Mat2) n (fun y => (f y).A) x :=
  contMDiffWithinAt_iff_coordinates

/-- For any charted source, intrinsic datum smoothness on any subset is equivalent to smoothness of both actual coordinate maps on that subset. -/
theorem contMDiffOn_iff_coordinates :
    ContMDiffOn I model n f s ↔
      ContMDiffOn I 𝓘(ℝ, ℂ) n (fun y => (f y).t) s ∧
      ContMDiffOn I 𝓘(ℝ, Mat2) n (fun y => (f y).A) s := by
  constructor
  · intro h
    exact ⟨fun y hy => (contMDiffWithinAt_iff_coordinates.mp (h y hy)).1,
      fun y hy => (contMDiffWithinAt_iff_coordinates.mp (h y hy)).2⟩
  · rintro ⟨ht, hA⟩ y hy
    exact contMDiffWithinAt_iff_coordinates.mpr ⟨ht y hy, hA y hy⟩

/-- For any charted source, global intrinsic datum smoothness is equivalent to global smoothness of both actual coordinate maps. -/
theorem contMDiff_iff_coordinates :
    ContMDiff I model n f ↔
      ContMDiff I 𝓘(ℝ, ℂ) n (fun y => (f y).t) ∧
      ContMDiff I 𝓘(ℝ, Mat2) n (fun y => (f y).A) := by
  constructor
  · intro h
    exact ⟨fun y => (contMDiffAt_iff_coordinates.mp (h y)).1,
      fun y => (contMDiffAt_iff_coordinates.mp (h y)).2⟩
  · rintro ⟨ht, hA⟩ y
    exact contMDiffAt_iff_coordinates.mpr ⟨ht y, hA y⟩

end GeneralSource

section NormedSource
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {n : WithTop ℕ∞} {f : E → Datum} {s : Set E} {x : E}

/-- On a real normed source, intrinsic datum smoothness within any set is equivalent to actual real Frechet smoothness of both coordinates. -/
theorem contMDiffWithinAt_iff_contDiffWithinAt_coordinates :
    ContMDiffWithinAt 𝓘(ℝ, E) model n f s x ↔
      ContDiffWithinAt ℝ n (fun y => (f y).t) s x ∧
      ContDiffWithinAt ℝ n (fun y => (f y).A) s x := by
  rw [contMDiffWithinAt_iff_coordinates]
  exact and_congr _root_.contMDiffWithinAt_iff_contDiffWithinAt
    _root_.contMDiffWithinAt_iff_contDiffWithinAt

/-- On a real normed source, intrinsic datum smoothness at a point is exactly the independently defined earlier amplitude and matrix regularity predicate. -/
theorem contMDiffAt_iff_coordinateContDiffAt :
    ContMDiffAt 𝓘(ℝ, E) model n f x ↔ PolarDatumSmooth.CoordinateContDiffAt n f x := by
  rw [contMDiffAt_iff_coordinates]
  exact and_congr _root_.contMDiffAt_iff_contDiffAt _root_.contMDiffAt_iff_contDiffAt

/-- On a real normed source, intrinsic datum smoothness on any set is equivalent to actual real Frechet smoothness of its amplitude and matrix coordinates. -/
theorem contMDiffOn_iff_contDiffOn_coordinates :
    ContMDiffOn 𝓘(ℝ, E) model n f s ↔
      ContDiffOn ℝ n (fun y => (f y).t) s ∧
      ContDiffOn ℝ n (fun y => (f y).A) s := by
  rw [contMDiffOn_iff_coordinates]
  exact and_congr _root_.contMDiffOn_iff_contDiffOn _root_.contMDiffOn_iff_contDiffOn

/-- On a real normed source, global intrinsic datum smoothness is equivalent to actual real Frechet smoothness of both coordinate maps. -/
theorem contMDiff_iff_contDiff_coordinates :
    ContMDiff 𝓘(ℝ, E) model n f ↔
      ContDiff ℝ n (fun y => (f y).t) ∧ ContDiff ℝ n (fun y => (f y).A) := by
  rw [contMDiff_iff_coordinates]
  exact and_congr _root_.contMDiff_iff_contDiff _root_.contMDiff_iff_contDiff

end NormedSource

/-- The actual complex amplitude coordinate is smooth on the intrinsic datum manifold. -/
theorem contMDiff_t (n : WithTop ℕ∞) : ContMDiff model 𝓘(ℝ, ℂ) n Datum.t :=
  (contMDiff_iff_coordinates.mp (contMDiff_id (I := model) (n := n))).1

/-- The actual ambient two-by-two matrix coordinate is smooth on the intrinsic datum manifold. -/
theorem contMDiff_A (n : WithTop ℕ∞) : ContMDiff model 𝓘(ℝ, Mat2) n Datum.A :=
  (contMDiff_iff_coordinates.mp (contMDiff_id (I := model) (n := n))).2

/-- The genuine ambient spinor realization is smooth by actual amplitude-matrix multiplication and the real-linear inverse spinor encoding. -/
theorem contMDiff_realize_value (n : WithTop ℕ∞) :
    ContMDiff model 𝓘(ℝ, Spinor) n (fun d : Datum => (realize d).val) := by
  have hp : ContDiff ℝ n (fun p : ℂ × Mat2 => ofMatrix (p.1 • p.2)) :=
    (SpinorMatrixSmooth.contDiff_ofMatrix n).comp (contDiff_fst.smul contDiff_snd)
  exact hp.contMDiff.comp ((contMDiff_t n).prodMk_space (contMDiff_A n))

/-- The actual realization into the regular-spinor manifold is smooth for the independently constructed intrinsic datum atlas. -/
theorem contMDiff_realize (n : WithTop ℕ∞) :
    ContMDiff model 𝓘(ℝ, Spinor) n (realize : Datum → RegularSpinor) :=
  (contMDiff_realize_value n).of_comp_isOpenEmbedding RegularSpinorManifold.isOpenEmbedding_value

/-- The actual simultaneous sign operation is smooth because it negates both actual smooth coordinate maps. -/
theorem contMDiff_negDatum (n : WithTop ℕ∞) : ContMDiff model model n negDatum := by
  apply contMDiff_iff_coordinates.mpr
  constructor
  · have hn : ContDiff ℝ n (fun z : ℂ => -z) := contDiff_id.neg
    exact hn.contMDiff.comp (contMDiff_t n)
  · have hn : ContDiff ℝ n (fun A : Mat2 => -A) := contDiff_id.neg
    exact hn.contMDiff.comp (contMDiff_A n)

/-- The actual simultaneous sign involution is a bundled diffeomorphism of the intrinsic datum manifold. -/
def negDiffeomorph (n : WithTop ℕ∞) : Diffeomorph model model Datum Datum n where
  toEquiv := PolarDatumTopology.negHomeomorph.toEquiv
  contMDiff_toFun := contMDiff_negDatum n
  contMDiff_invFun := contMDiff_negDatum n

/-- The bundled sign diffeomorphism retains exactly the existing actual sign homeomorphism as its underlying topological map. -/
theorem negDiffeomorph_toHomeomorph (n : WithTop ℕ∞) :
    (negDiffeomorph n).toHomeomorph = PolarDatumTopology.negHomeomorph := rfl

end FoliationQM.PolarDatumManifold
