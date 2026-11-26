module
public import FoliationQM.SignedMetricProjection
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-!
# Smooth signed normalization and residuals in an actual vector bundle

Source scope: the metric-tetrad component of v13 `prop:takabayasi`.
The metric and vector inputs are genuine dependent sections in the original
bundle and iterated Hom-bundle atlases. Pairing, the positive signed-square
normalization factor, normalization, and the explicit metric residual inherit
their stated regularity from these actual graph hypotheses.

Every assertion is local, including versions within arbitrary sets. Only the
actual signed square at the specified point must be positive for square-root
normalization. No symmetry, sign-square law, orthogonality, frame, or additional
base-manifold regularity is assumed. The original topology and charts are
unchanged, and no smoothness is claimed at a zero normalization denominator.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Bundle Set
open scoped Manifold Bundle
namespace FoliationQM.SmoothSignedMetricProjection

variable {E H B F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace B] [ChartedSpace H B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {n : WithTop ℕ∞} {g : ∀ x : B, V x →L[ℝ] V x →L[ℝ] ℝ}
  {u v : ∀ x : B, V x} {s : Set B} {x : B}

/-- Evaluating the actual bilinear metric on two actual section graphs is smooth within the specified set, using the genuine iterated Hom-bundle evaluation. -/
theorem contMDiffWithinAt_pairing
    (hg : ContMDiffWithinAt I (I.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun y => (⟨y, g y⟩ : TotalSpace (F →L[ℝ] F →L[ℝ] ℝ)
        (fun y : B => V y →L[ℝ] V y →L[ℝ] ℝ))) s x)
    (hu : ContMDiffWithinAt I (I.prod 𝓘(ℝ, F)) n
      (fun y => (⟨y, u y⟩ : TotalSpace F V)) s x)
    (hv : ContMDiffWithinAt I (I.prod 𝓘(ℝ, F)) n
      (fun y => (⟨y, v y⟩ : TotalSpace F V)) s x) :
    ContMDiffWithinAt I 𝓘(ℝ, ℝ) n (fun y => g y (u y) (v y)) s x := by
  have hp : ContMDiffWithinAt I (I.prod 𝓘(ℝ, ℝ)) n
      (fun y => (⟨y, g y (u y) (v y)⟩ : TotalSpace ℝ (Bundle.Trivial B ℝ))) s x :=
    hg.clm_bundle_apply₂ hu hv
  simpa using (Bundle.contMDiffWithinAt_totalSpace.mp hp).2

/-- Pairing actual smooth metric and vector-section graphs yields an ordinary smooth scalar at the specified point. -/
theorem contMDiffAt_pairing
    (hg : ContMDiffAt I (I.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun y => (⟨y, g y⟩ : TotalSpace (F →L[ℝ] F →L[ℝ] ℝ)
        (fun y : B => V y →L[ℝ] V y →L[ℝ] ℝ))) x)
    (hu : ContMDiffAt I (I.prod 𝓘(ℝ, F)) n
      (fun y => (⟨y, u y⟩ : TotalSpace F V)) x)
    (hv : ContMDiffAt I (I.prod 𝓘(ℝ, F)) n
      (fun y => (⟨y, v y⟩ : TotalSpace F V)) x) :
    ContMDiffAt I 𝓘(ℝ, ℝ) n (fun y => g y (u y) (v y)) x :=
  contMDiffWithinAt_pairing hg hu hv

/-- The computed positive signed normalization factor is smooth within an arbitrary set when the actual signed metric square at the point is strictly positive. -/
theorem contMDiffWithinAt_scale (ε : ℝ)
    (hg : ContMDiffWithinAt I (I.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun y => (⟨y, g y⟩ : TotalSpace (F →L[ℝ] F →L[ℝ] ℝ)
        (fun y : B => V y →L[ℝ] V y →L[ℝ] ℝ))) s x)
    (hu : ContMDiffWithinAt I (I.prod 𝓘(ℝ, F)) n
      (fun y => (⟨y, u y⟩ : TotalSpace F V)) s x)
    (hpos : 0 < ε * g x (u x) (u x)) :
    ContMDiffWithinAt I 𝓘(ℝ, ℝ) n
      (fun y => SignedMetricProjection.scale (g y).toLinearMap₁₂ ε (u y)) s x := by
  have hp : ContMDiffWithinAt I 𝓘(ℝ, ℝ) n (fun y => ε * g y (u y) (u y)) s x :=
    (show ContDiff ℝ n (fun t : ℝ => ε * t) by fun_prop).comp_contMDiffWithinAt
      (contMDiffWithinAt_pairing hg hu hu)
  have hf : ContDiffAt ℝ n (fun t : ℝ => (Real.sqrt t)⁻¹) (ε * g x (u x) (u x)) :=
    (Real.contDiffAt_sqrt hpos.ne').inv (ne_of_gt (Real.sqrt_pos.mpr hpos))
  simpa only [SignedMetricProjection.scale, Function.comp_def,
    ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply] using hf.comp_contMDiffWithinAt (f := fun y : B => ε * g y (u y) (u y)) (x := x) hp

/-- The actual signed normalization factor is smooth at a point of its genuine positive signed-square domain. -/
theorem contMDiffAt_scale (ε : ℝ)
    (hg : ContMDiffAt I (I.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun y => (⟨y, g y⟩ : TotalSpace (F →L[ℝ] F →L[ℝ] ℝ)
        (fun y : B => V y →L[ℝ] V y →L[ℝ] ℝ))) x)
    (hu : ContMDiffAt I (I.prod 𝓘(ℝ, F)) n
      (fun y => (⟨y, u y⟩ : TotalSpace F V)) x)
    (hpos : 0 < ε * g x (u x) (u x)) :
    ContMDiffAt I 𝓘(ℝ, ℝ) n
      (fun y => SignedMetricProjection.scale (g y).toLinearMap₁₂ ε (u y)) x :=
  contMDiffWithinAt_scale ε hg hu hpos

/-- The actual normalized dependent vector-section graph is smooth within the specified set on its genuine positive signed-square domain. -/
theorem contMDiffWithinAt_normalize (ε : ℝ)
    (hg : ContMDiffWithinAt I (I.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun y => (⟨y, g y⟩ : TotalSpace (F →L[ℝ] F →L[ℝ] ℝ)
        (fun y : B => V y →L[ℝ] V y →L[ℝ] ℝ))) s x)
    (hu : ContMDiffWithinAt I (I.prod 𝓘(ℝ, F)) n
      (fun y => (⟨y, u y⟩ : TotalSpace F V)) s x)
    (hpos : 0 < ε * g x (u x) (u x)) :
    ContMDiffWithinAt I (I.prod 𝓘(ℝ, F)) n
      (fun y => (⟨y, SignedMetricProjection.normalize (g y).toLinearMap₁₂ ε (u y)⟩ :
        TotalSpace F V)) s x :=
  (contMDiffWithinAt_scale ε hg hu hpos).smul_section hu

/-- The actual signed normalization is a smooth section graph at every point with positive signed metric square, without a symmetry or sign-square-law premise. -/
theorem contMDiffAt_normalize (ε : ℝ)
    (hg : ContMDiffAt I (I.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun y => (⟨y, g y⟩ : TotalSpace (F →L[ℝ] F →L[ℝ] ℝ)
        (fun y : B => V y →L[ℝ] V y →L[ℝ] ℝ))) x)
    (hu : ContMDiffAt I (I.prod 𝓘(ℝ, F)) n
      (fun y => (⟨y, u y⟩ : TotalSpace F V)) x)
    (hpos : 0 < ε * g x (u x) (u x)) :
    ContMDiffAt I (I.prod 𝓘(ℝ, F)) n
      (fun y => (⟨y, SignedMetricProjection.normalize (g y).toLinearMap₁₂ ε (u y)⟩ :
        TotalSpace F V)) x :=
  contMDiffWithinAt_normalize ε hg hu hpos

/-- The explicit signed metric residual is a smooth actual dependent section graph within an arbitrary set; no normalization, unit-square, or orthogonality premise is needed. -/
theorem contMDiffWithinAt_residual (ε : ℝ)
    (hg : ContMDiffWithinAt I (I.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun y => (⟨y, g y⟩ : TotalSpace (F →L[ℝ] F →L[ℝ] ℝ)
        (fun y : B => V y →L[ℝ] V y →L[ℝ] ℝ))) s x)
    (hu : ContMDiffWithinAt I (I.prod 𝓘(ℝ, F)) n
      (fun y => (⟨y, u y⟩ : TotalSpace F V)) s x)
    (hv : ContMDiffWithinAt I (I.prod 𝓘(ℝ, F)) n
      (fun y => (⟨y, v y⟩ : TotalSpace F V)) s x) :
    ContMDiffWithinAt I (I.prod 𝓘(ℝ, F)) n
      (fun y => (⟨y, SignedMetricProjection.residual (g y).toLinearMap₁₂ ε (u y) (v y)⟩ :
        TotalSpace F V)) s x := by
  have hp : ContMDiffWithinAt I 𝓘(ℝ, ℝ) n (fun y => ε * g y (u y) (v y)) s x :=
    (show ContDiff ℝ n (fun t : ℝ => ε * t) by fun_prop).comp_contMDiffWithinAt
      (contMDiffWithinAt_pairing hg hu hv)
  simpa only [SignedMetricProjection.residual_apply, Pi.sub_apply, Pi.smul_apply',
    ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply] using hv.sub_section (hp.smul_section hu)

/-- The actual residual of smooth metric and vector-section graphs is smooth at the specified point, without any unproved projection-domain premise. -/
theorem contMDiffAt_residual (ε : ℝ)
    (hg : ContMDiffAt I (I.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun y => (⟨y, g y⟩ : TotalSpace (F →L[ℝ] F →L[ℝ] ℝ)
        (fun y : B => V y →L[ℝ] V y →L[ℝ] ℝ))) x)
    (hu : ContMDiffAt I (I.prod 𝓘(ℝ, F)) n
      (fun y => (⟨y, u y⟩ : TotalSpace F V)) x)
    (hv : ContMDiffAt I (I.prod 𝓘(ℝ, F)) n
      (fun y => (⟨y, v y⟩ : TotalSpace F V)) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, F)) n
      (fun y => (⟨y, SignedMetricProjection.residual (g y).toLinearMap₁₂ ε (u y) (v y)⟩ :
        TotalSpace F V)) x :=
  contMDiffWithinAt_residual ε hg hu hv

end FoliationQM.SmoothSignedMetricProjection
