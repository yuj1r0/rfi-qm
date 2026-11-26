module
public import FoliationQM.MetricLorentzTetradCover
public import FoliationQM.GeometricLorentzFrameBundle
public import FoliationQM.LorentzFrameExtension

/-!
# Boundary extension in the actual metric-derived Lorentz frame bundle

For the geometric frame component of v13 `prop:takabayasi`, independent
metric, orientation, and future geometry determine the actual tetrad atlas.
A continuous parameterized square contained in one of its chart domains
admits a frame filling of the prescribed boundary exactly when its Lorentz
loop coefficient vanishes. The map takes values in the original geometric
frame total space. The parameterization need not be injective, so this is
a field over the parameterized square rather than a section of its image.
-/

@[expose] public section
noncomputable section
open Bundle
open scoped Topology Manifold
namespace FoliationQM.MetricFrameExtension
open LorentzMatrixGroup MetricLorentzTetradCover GeometricLorentzFrameBundle
open CliffordSpinLoopMonodromy

variable {E H B F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace B] [ChartedSpace H B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {V : B → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  {n : WithTop ℕ∞} [ContMDiffVectorBundle n F V I]
  (D : SmoothLorentzMetricGeometry.Data (F := F) I V n)

/-- A frame field over the square with all four specified boundary values,
in the original metric-derived geometric frame total space. -/
abbrev Filling (i : B) (σ : C(unitInterval × unitInterval, B))
    (γ : Path (1 : ProperFutureLorentz) 1) :=
  FrameSquareExtension.Filling (principalAtlas (tetradData D)) i σ γ

/-- Each value is an actual geometric frame over the specified base point of the parameterized square. -/
theorem map_proj (i : B) (σ : C(unitInterval × unitInterval, B))
    (γ : Path (1 : ProperFutureLorentz) 1) (S : Filling D i σ γ)
    (z : unitInterval × unitInterval) : (S.map z).proj = σ z := S.proj_map z

/-- Every one of the four original vector-bundle points in a filling varies continuously. -/
theorem continuous_vector (i : B) (σ : C(unitInterval × unitInterval, B))
    (γ : Path (1 : ProperFutureLorentz) 1) (S : Filling D i σ γ) (a : Fin 4) :
    Continuous (fun z =>
      (⟨(S.map z).proj, (S.map z).snd.basis a⟩ : TotalSpace F V)) :=
  (GeometricLorentzFrameBundle.continuous_vector (tetradData D) a).comp S.map.continuous

/-- On a whole square contained in one computed metric-tetrad chart, actual frame filling
is exactly the nullhomotopy of its coordinate boundary loop. -/
theorem nonempty_iff_homotopic (i : B) (σ : C(unitInterval × unitInterval, B))
    (γ : Path (1 : ProperFutureLorentz) 1)
    (hσ : ∀ z, σ z ∈ SmoothLorentzMetricGeometry.domain D i) :
    Nonempty (Filling D i σ γ) ↔ γ.Homotopic (Path.refl 1) :=
  FrameSquareExtension.nonempty_iff (principalAtlas (tetradData D)) i σ γ hσ

/-- A metric-frame filling exists exactly when the actual Clifford lift of the boundary closes. -/
theorem nonempty_iff_lift_closes (i : B) (σ : C(unitInterval × unitInterval, B))
    (γ : Path (1 : ProperFutureLorentz) 1)
    (hσ : ∀ z, σ z ∈ SmoothLorentzMetricGeometry.domain D i) :
    Nonempty (Filling D i σ γ) ↔ liftLoop γ 1 = 1 :=
  LorentzFrameExtension.nonempty_iff_lift_closes (principalAtlas (tetradData D)) i σ γ hσ

/-- The actual metric-frame boundary extension criterion is the zero normalized mod-two loop coefficient. -/
theorem nonempty_iff_coefficient_zero (i : B) (σ : C(unitInterval × unitInterval, B))
    (γ : Path (1 : ProperFutureLorentz) 1)
    (hσ : ∀ z, σ z ∈ SmoothLorentzMetricGeometry.domain D i) :
    Nonempty (Filling D i σ γ) ↔ LorentzFrameExtension.coefficient γ = 0 :=
  LorentzFrameExtension.nonempty_iff_coefficient_zero (principalAtlas (tetradData D)) i σ γ hσ

/-- The genuine nontrivial Lorentz generator cannot bound such a metric-frame filling. -/
theorem generator_no_filling (i : B) (σ : C(unitInterval × unitInterval, B))
    (hσ : ∀ z, σ z ∈ SmoothLorentzMetricGeometry.domain D i) :
    ¬ Nonempty (Filling D i σ generatorLoop) :=
  LorentzFrameExtension.generator_no_filling (principalAtlas (tetradData D)) i σ hσ

/-- The constant boundary has an actual metric-frame filling over the full contained square. -/
theorem refl_filling (i : B) (σ : C(unitInterval × unitInterval, B))
    (hσ : ∀ z, σ z ∈ SmoothLorentzMetricGeometry.domain D i) :
    Nonempty (Filling D i σ (Path.refl 1)) :=
  LorentzFrameExtension.refl_filling (principalAtlas (tetradData D)) i σ hσ

end FoliationQM.MetricFrameExtension
