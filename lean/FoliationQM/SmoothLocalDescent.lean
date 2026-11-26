module
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
import all Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# Smoothness detected by actual local diffeomorphisms

Source: the density-separated quotient compatibility in v13 `prop:takabayasi`.
These geometric helpers derive smoothness downstairs from smoothness upstairs
using actual local inverses. Surjectivity is required for the global criterion.
The product construction retains the supplied factor atlases and maps.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold
open Function Set Filter Topology
namespace FoliationQM.SmoothLocalDescent

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {H K L : Type*} [TopologicalSpace H] [TopologicalSpace K] [TopologicalSpace L]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
  {P : ModelWithCorners ℝ G L}
  {M N X : Type*} [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace X]
  [ChartedSpace H M] [ChartedSpace K N] [ChartedSpace L X]
  {n : WithTop ℕ∞}

/-- Smoothness at the image of a local diffeomorphism is exactly smoothness of the actual composite at its chosen preimage. -/
theorem contMDiffAt_comp_iff {f : M → N} {g : N → X} {x : M}
    (hf : IsLocalDiffeomorphAt I J n f x) :
    ContMDiffAt I P n (g ∘ f) x ↔ ContMDiffAt J P n g (f x) := by
  constructor
  · intro h
    have hcomp := h.comp_of_eq (hf.contMDiffAt_localInverse)
      (hf.localInverse_left_inv hf.localInverse_mem_target)
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [hf.localInverse_eventuallyEq_right] with y hy
    exact congrArg g hy.symm
  · intro h
    exact h.comp x hf.contMDiffAt

/-- A surjective local diffeomorphism detects global smoothness without adding any smoothness premise for the descended map. -/
theorem contMDiff_comp_iff {f : M → N} {g : N → X}
    (hf : IsLocalDiffeomorph I J n f) (hs : Surjective f) :
    ContMDiff I P n (g ∘ f) ↔ ContMDiff J P n g := by
  constructor
  · intro h y
    obtain ⟨x, rfl⟩ := hs y
    exact (contMDiffAt_comp_iff (hf x)).mp (h x)
  · intro h
    exact h.comp hf.contMDiff

/-- The identity on a supplied first factor times an actual local diffeomorphism is a local diffeomorphism for the ordinary product atlases. -/
theorem isLocalDiffeomorph_id_prodMap {f : M → N}
    (hf : IsLocalDiffeomorph I J n f) :
    IsLocalDiffeomorph (P.prod I) (P.prod J) n (Prod.map (id : X → X) f) := by
  rintro ⟨a, x⟩
  have h := hf x
  unfold IsLocalDiffeomorphAt at h
  obtain ⟨e, hx, he⟩ := h
  let p : PartialDiffeomorph (P.prod I) (P.prod J) (X × M) (X × N) n := {
    toPartialEquiv := (OpenPartialHomeomorph.refl X).toPartialEquiv.prod e.toPartialEquiv
    open_source := isOpen_univ.prod e.open_source
    open_target := isOpen_univ.prod e.open_target
    contMDiffOn_toFun := contMDiff_id.contMDiffOn.prodMap e.contMDiffOn_toFun
    contMDiffOn_invFun := contMDiff_id.contMDiffOn.prodMap e.contMDiffOn_invFun }
  refine ⟨p, ⟨mem_univ a, hx⟩, ?_⟩
  intro y hy
  exact Prod.ext rfl (he hy.2)

end FoliationQM.SmoothLocalDescent
