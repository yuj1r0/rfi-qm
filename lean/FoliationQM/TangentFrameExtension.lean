module
public import FoliationQM.MetricFrameExtension
public import FoliationQM.TangentLorentzTetradCover

/-!
# Boundary extension for actual tangent Lorentz frames

For the tangent-frame component of v13 `prop:takabayasi`, a C^(n+1)
base supplies the original C^n tangent vector bundle. Its independently
specified metric geometry constructs the tetrad atlas used here.
The filling is a continuous actual tangent-frame field over a parameterized
square, whose entire image lies in one computed tetrad chart. No injectivity
of that parameterization, smoothness of the filling, or independent tangent
bundle regularity is assumed.
-/

@[expose] public section
noncomputable section
open Bundle
open scoped Topology Manifold
namespace FoliationQM.TangentFrameExtension
open LorentzMatrixGroup CliffordSpinLoopMonodromy

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace M] [ChartedSpace H M]
  (n : WithTop ℕ∞) [IsManifold I (n + 1) M]
  (D : TangentLorentzTetradCover.Data (M := M) I n)

/-- A filling in the actual tangent-frame total space after deriving the C^n
tangent bundle from the stated C^(n+1) base. -/
abbrev Filling (i : M) (σ : C(unitInterval × unitInterval, M))
    (γ : Path (1 : ProperFutureLorentz) 1) :=
  letI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  letI : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  MetricFrameExtension.Filling D i σ γ

/-- The domain is the computed metric-compatible chart of the original tangent bundle. -/
abbrev domain (i : M) : TopologicalSpace.Opens M :=
  letI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  letI : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  SmoothLorentzMetricGeometry.domain D i

/-- The actual tangent-frame value projects to the original base point of the parameterized square. -/
theorem map_proj (i : M) (σ : C(unitInterval × unitInterval, M))
    (γ : Path (1 : ProperFutureLorentz) 1) (S : Filling I n D i σ γ)
    (z : unitInterval × unitInterval) :
    letI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    letI : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
      TangentBundle.contMDiffVectorBundle
    (S.map z).proj = σ z := by
  let : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  let : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  exact MetricFrameExtension.map_proj D i σ γ S z

/-- All four actual tangent vectors vary continuously in Mathlib's original tangent-bundle topology. -/
theorem continuous_vector (i : M) (σ : C(unitInterval × unitInterval, M))
    (γ : Path (1 : ProperFutureLorentz) 1) (S : Filling I n D i σ γ) (a : Fin 4) :
    letI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    letI : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
      TangentBundle.contMDiffVectorBundle
    Continuous (fun z =>
      (⟨(S.map z).proj, (S.map z).snd.basis a⟩ : TangentBundle I M)) := by
  let : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  let : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  exact MetricFrameExtension.continuous_vector D i σ γ S a

/-- For a whole square contained in a computed tangent tetrad chart, filling is exactly boundary nullhomotopy. -/
theorem nonempty_iff_homotopic (i : M) (σ : C(unitInterval × unitInterval, M))
    (γ : Path (1 : ProperFutureLorentz) 1) (hσ : ∀ z, σ z ∈ domain I n D i) :
    Nonempty (Filling I n D i σ γ) ↔ γ.Homotopic (Path.refl 1) := by
  let : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  let : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  exact MetricFrameExtension.nonempty_iff_homotopic D i σ γ hσ

/-- The actual tangent-frame filling exists precisely when the genuine lifted Lorentz boundary closes. -/
theorem nonempty_iff_lift_closes (i : M) (σ : C(unitInterval × unitInterval, M))
    (γ : Path (1 : ProperFutureLorentz) 1) (hσ : ∀ z, σ z ∈ domain I n D i) :
    Nonempty (Filling I n D i σ γ) ↔ liftLoop γ 1 = 1 := by
  let : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  let : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  exact MetricFrameExtension.nonempty_iff_lift_closes D i σ γ hσ

/-- Tangent-frame boundary filling is detected by zero mod-two loop coefficient at the derived regularity. -/
theorem nonempty_iff_coefficient_zero (i : M) (σ : C(unitInterval × unitInterval, M))
    (γ : Path (1 : ProperFutureLorentz) 1) (hσ : ∀ z, σ z ∈ domain I n D i) :
    Nonempty (Filling I n D i σ γ) ↔ LorentzFrameExtension.coefficient γ = 0 := by
  let : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  let : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  exact MetricFrameExtension.nonempty_iff_coefficient_zero D i σ γ hσ

/-- The actual nontrivial Lorentz loop obstructs a tangent-frame filling even over a contained square. -/
theorem generator_no_filling (i : M) (σ : C(unitInterval × unitInterval, M))
    (hσ : ∀ z, σ z ∈ domain I n D i) :
    ¬ Nonempty (Filling I n D i σ generatorLoop) := by
  let : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  let : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  exact MetricFrameExtension.generator_no_filling D i σ hσ

/-- The constant boundary admits a continuous field of actual tangent Lorentz frames over the square. -/
theorem refl_filling (i : M) (σ : C(unitInterval × unitInterval, M))
    (hσ : ∀ z, σ z ∈ domain I n D i) :
    Nonempty (Filling I n D i σ (Path.refl 1)) := by
  let : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  let : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  exact MetricFrameExtension.refl_filling D i σ hσ

end FoliationQM.TangentFrameExtension
