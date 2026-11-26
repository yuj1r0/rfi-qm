module
public import FoliationQM.SourceQuotientManifold
public import FoliationQM.SmoothTrivialBundle
public import Mathlib.Topology.FiberBundle.Constructions
public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Smooth polar sections of the fixed trivial bundles

Source: the fixed-representation section statement in v13 `prop:takabayasi`.
The fibers are the independently constructed literal source quotient and
regular four-spinors. Their actual natural fiber diffeomorphism induces
an actual base-preserving diffeomorphism between `Bundle.Trivial` total
spaces over any supplied real charted base. On a smooth base, these
explicit product-pullback total-space atlases are smooth manifolds.

Smooth sections are the dependent sections whose actual total-space
graphs are smooth, using `SmoothTrivialBundle.SmoothSection`. The exact
fiber realization gives a bijection of these sections, with its genuine
inverse and graph compatibility. The pointwise formula agrees with the
source polar spinor expression. This is a fixed trivial-bundle result;
it does not construct a nontrivial spin bundle or choose global
individual density/real-angle/matrix representatives.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator Manifold
open Function Set Topology
namespace FoliationQM.PolarBundleSections
open DiracMatrices PolarSignQuotient SourcePolarQuotient SourcePolarDatum

/-- The actual total space of the fixed trivial bundle with literal source-quotient fiber. -/
abbrev SourceTotal (B : Type*) :=
  Bundle.TotalSpace SourceQuotient (Bundle.Trivial B SourceQuotient)
/-- The actual total space of the fixed trivial bundle with regular-spinor fiber. -/
abbrev SpinorTotal (B : Type*) :=
  Bundle.TotalSpace RegularSpinor (Bundle.Trivial B RegularSpinor)

/-- Actual fiberwise polar realization in the fixed trivial bundle, preserving the base point. -/
def totalRealize (B : Type*) (p : SourceTotal B) : SpinorTotal B :=
  ⟨p.proj, regularHomeomorph p.snd⟩

/-- Actual fiberwise inverse reconstruction in the fixed trivial bundle, with quotient-valued output. -/
def totalReconstruct (B : Type*) (p : SpinorTotal B) : SourceTotal B :=
  ⟨p.proj, regularHomeomorph.symm p.snd⟩

/-- Total-space realization applies the established natural quotient realization in the fiber. -/
theorem totalRealize_mk (B : Type*) (b : B) (q : SourceQuotient) :
    totalRealize B ⟨b, q⟩ = ⟨b, regularHomeomorph q⟩ := rfl

/-- Actual total-space realization preserves the bundle projection. -/
theorem totalRealize_proj (B : Type*) (p : SourceTotal B) :
    (totalRealize B p).proj = p.proj := rfl

/-- The realized fiber is exactly the actual natural source-quotient realization. -/
theorem totalRealize_snd (B : Type*) (p : SourceTotal B) :
    (totalRealize B p).snd = regularHomeomorph p.snd := rfl

/-- Actual quotient reconstruction preserves the bundle projection. -/
theorem totalReconstruct_proj (B : Type*) (p : SpinorTotal B) :
    (totalReconstruct B p).proj = p.proj := rfl

/-- Actual total-space reconstruction is a left inverse of actual realization. -/
theorem totalReconstruct_realize (B : Type*) (p : SourceTotal B) :
    totalReconstruct B (totalRealize B p) = p := by
  cases p
  simp [totalReconstruct, totalRealize]

/-- Actual total-space realization is a left inverse of actual reconstruction. -/
theorem totalRealize_reconstruct (B : Type*) (p : SpinorTotal B) :
    totalRealize B (totalReconstruct B p) = p := by
  cases p
  simp [totalReconstruct, totalRealize]

/-- On literal positive-density, real-angle and determinant-one matrix data, total-space realization is exactly the source polar spinor formula (`prop:takabayasi`). -/
theorem totalRealize_mk_real (B : Type*) (b : B)
    (rho : PolarAmplitudeTopology.PositiveDensity) (beta : ℝ) (A : SpecialLinearMatrix) :
    (totalRealize B ⟨b, Quotient.mk SourcePolarQuotient.signSetoid
      (rho, (beta : ChiralAngleCircle.Angle), A)⟩).snd.val =
      PolarSpinorBilinears.polarSpinor rho beta (SpecialLinearSpin.spin A) :=
  SourceQuotientManifold.value_mk_real rho beta A

section SmoothBase
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (B : Type*) [TopologicalSpace B] [ChartedSpace H B]

attribute [local instance] SmoothTrivialBundle.totalChartedSpace

variable (n : WithTop ℕ∞)

/-- A supplied smooth real base gives the actual source-quotient trivial-bundle total space its explicit smooth product-pullback atlas. -/
theorem isManifold_sourceTotal [IsManifold I n B] :
    IsManifold (I.prod 𝓘(ℝ, Spinor)) n (SourceTotal B) :=
  SmoothTrivialBundle.isManifold_total I 𝓘(ℝ, Spinor) B SourceQuotient n

/-- A supplied smooth real base gives the actual regular-spinor trivial-bundle total space its explicit smooth product-pullback atlas. -/
theorem isManifold_spinorTotal [IsManifold I n B] :
    IsManifold (I.prod 𝓘(ℝ, Spinor)) n (SpinorTotal B) :=
  SmoothTrivialBundle.isManifold_total I 𝓘(ℝ, Spinor) B RegularSpinor n

/-- The genuine base-preserving diffeomorphism of the actual fixed trivial-bundle total spaces. -/
def totalRealization :
    Diffeomorph (I.prod 𝓘(ℝ, Spinor)) (I.prod 𝓘(ℝ, Spinor))
      (SourceTotal B) (SpinorTotal B) n :=
  SmoothTrivialBundle.totalMapDiffeomorph I B (SourceQuotientManifold.regularDiffeomorph n)

/-- The total-space diffeomorphism is the previously defined actual polar realization. -/
theorem totalRealization_apply (p : SourceTotal B) :
    totalRealization I B n p = totalRealize B p := rfl

/-- The inverse total-space diffeomorphism is the previously defined actual quotient reconstruction. -/
theorem totalRealization_symm_apply (p : SpinorTotal B) :
    (totalRealization I B n).symm p = totalReconstruct B p := rfl

/-- The genuine total-space diffeomorphism preserves the actual bundle projection. -/
theorem totalRealization_proj (p : SourceTotal B) :
    (totalRealization I B n p).proj = p.proj := rfl

/-- Actual fixed-bundle polar realization is smooth to every supplied order. -/
theorem contMDiff_totalRealize :
    ContMDiff (I.prod 𝓘(ℝ, Spinor)) (I.prod 𝓘(ℝ, Spinor)) n (totalRealize B) :=
  (totalRealization I B n).contMDiff

/-- Actual fixed-bundle quotient reconstruction is smooth to every supplied order. -/
theorem contMDiff_totalReconstruct :
    ContMDiff (I.prod 𝓘(ℝ, Spinor)) (I.prod 𝓘(ℝ, Spinor)) n (totalReconstruct B) :=
  (totalRealization I B n).symm.contMDiff

/-- Dependent sections of the actual source-quotient trivial bundle whose actual total-space graphs are smooth. -/
abbrev SourceSection := SmoothTrivialBundle.SmoothSection I 𝓘(ℝ, Spinor) B SourceQuotient n
/-- Dependent sections of the actual regular-spinor trivial bundle whose actual total-space graphs are smooth. -/
abbrev SpinorSection := SmoothTrivialBundle.SmoothSection I 𝓘(ℝ, Spinor) B RegularSpinor n

/-- The actual polar fiber diffeomorphism gives an exact equivalence of smooth dependent sections of the fixed trivial bundles (`prop:takabayasi`). -/
def sectionEquiv : SourceSection I B n ≃ SpinorSection I B n :=
  SmoothTrivialBundle.sectionCongr I B (SourceQuotientManifold.regularDiffeomorph n)

/-- The smooth-section equivalence realizes the source quotient pointwise. -/
theorem sectionEquiv_apply (s : SourceSection I B n) (b : B) :
    (sectionEquiv I B n s).val b = regularHomeomorph (s.val b) := rfl

/-- The inverse smooth-section equivalence reconstructs the actual source quotient pointwise. -/
theorem sectionEquiv_symm_apply (s : SpinorSection I B n) (b : B) :
    ((sectionEquiv I B n).symm s).val b = regularHomeomorph.symm (s.val b) := rfl

/-- Taking a section graph commutes pointwise with actual total-space realization. -/
theorem sectionEquiv_graph (s : SourceSection I B n) (b : B) :
    totalRealize B ⟨b, s.val b⟩ = ⟨b, (sectionEquiv I B n s).val b⟩ := rfl

/-- Actual total-space realization maps the entire graph function to the graph of the corresponding smooth spinor section. -/
theorem sectionEquiv_graph_commutes (s : SourceSection I B n) :
    totalRealize B ∘ (fun b => (⟨b, s.val b⟩ : SourceTotal B)) =
      (fun b => (⟨b, (sectionEquiv I B n s).val b⟩ : SpinorTotal B)) := rfl

/-- Every smooth regular-spinor section has a unique smooth quotient-valued source section in the fixed trivial bundle; no global individual representative is selected. -/
theorem existsUnique_sourceSection (s : SpinorSection I B n) :
    ∃! t : SourceSection I B n, ∀ b, regularHomeomorph (t.val b) = s.val b := by
  refine ⟨(sectionEquiv I B n).symm s, ?_, ?_⟩
  · intro b
    rw [sectionEquiv_symm_apply, Homeomorph.apply_symm_apply]
  · intro t ht
    apply Subtype.ext
    funext b
    apply regularHomeomorph.injective
    rw [ht b, sectionEquiv_symm_apply, Homeomorph.apply_symm_apply]

end SmoothBase

end FoliationQM.PolarBundleSections
