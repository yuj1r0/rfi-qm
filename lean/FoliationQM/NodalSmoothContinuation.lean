module

public import FoliationQM.EmbeddedNodalWeakKG
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Smooth continuation across a null nodal set

Source: v13 `thm:wallstrom` Part(c), the conclusion "`ψ` coincides with the
unique global smooth solution having nodal set `𝒩`", component kind D. The
manuscript obtains a smooth solution almost everywhere equal to the weak
extension from the cited finite-energy Cauchy uniqueness theorem. This module
proves what follows from that identification. Let `𝒩` be a closed set of zero
volume, `ψ` a field continuous off `𝒩`, and `u` a continuous field almost
everywhere equal to `ψ` on an open set `U`. Then `u` equals `ψ` at every point
of `U` off `𝒩`, such a `u` is unique on `U`, and its squared modulus is any
continuous extension of `|ψ|²`, so its zero set is exactly `𝒩` when that
extension vanishes exactly on `𝒩`. If `u` is twice continuously differentiable
and `ψ` solves the curvature-coupled Klein–Gordon equation off `𝒩`, then `u`
solves it on all of `U`.

The existence of such a `u` is the content of the cited Cauchy theorem and is
a hypothesis here; it is not proved.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.NodalSmoothContinuation

open Filter MeasureTheory Set Manifold LorentzMatrixGroup RNCVolumeDensity
open CurvedKGTestResidual CurvedWaveDivergence RNCCoordinateConnection RealLorentzFrame
open scoped ContDiff Topology Manifold Matrix.Norms.Operator

variable {N U : Set Covector} {ψ u : Covector → ℂ}

/-- A continuous field almost everywhere equal to a field continuous off a
closed set agrees with it at every point off that set. -/
theorem eqOn_off (hU : IsOpen U) (hN : IsClosed N) (hψ : ContinuousOn ψ (U \ N))
    (hu : ContinuousOn u U) (hae : u =ᵐ[volume.restrict U] ψ) : EqOn u ψ (U \ N) :=
  Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset sdiff_subset hae)
    (hU.sdiff hN) (hu.mono sdiff_subset) hψ

/-- The continuous representative on an open set is unique. -/
theorem eqOn_of_ae_eq {v : Covector → ℂ} (hU : IsOpen U) (hu : ContinuousOn u U)
    (hv : ContinuousOn v U) (hue : u =ᵐ[volume.restrict U] ψ)
    (hve : v =ᵐ[volume.restrict U] ψ) : EqOn u v U :=
  Measure.eqOn_open_of_ae_eq (hue.trans hve.symm) hU hu hv

/-- The complement of a set of zero volume is dense in every open set. -/
theorem subset_closure_off (hU : IsOpen U) (hnull : volume N = 0) : U ⊆ closure (U \ N) := by
  have hd : Dense {x : Covector | x ∉ N} :=
    Measure.dense_of_ae (measure_eq_zero_iff_ae_notMem.mp hnull)
  exact hd.open_subset_closure_inter hU

/-- The squared modulus of the continuous representative is any continuous
extension of the squared modulus off the null set. -/
theorem norm_sq_eq {ρ : Covector → ℝ} (hU : IsOpen U) (hnull : volume N = 0)
    (hu : ContinuousOn u U) (huψ : EqOn u ψ (U \ N)) (hρ : ContinuousOn ρ U)
    (hρψ : ∀ x ∈ U \ N, ρ x = ‖ψ x‖ ^ 2) : ∀ x ∈ U, ‖u x‖ ^ 2 = ρ x := by
  have h : EqOn (fun x => ‖u x‖ ^ 2) ρ (U \ N) := fun x hx => by
    change ‖u x‖ ^ 2 = ρ x
    rw [huψ hx, hρψ x hx]
  exact h.of_subset_closure (hu.norm.pow 2) hρ sdiff_subset (subset_closure_off hU hnull)

/-- If the continuous extension of the density vanishes exactly on the null
set, the zero set of the continuous representative is exactly that set. -/
theorem eq_zero_iff {ρ : Covector → ℝ} (hU : IsOpen U) (hnull : volume N = 0)
    (hu : ContinuousOn u U) (huψ : EqOn u ψ (U \ N)) (hρ : ContinuousOn ρ U)
    (hρψ : ∀ x ∈ U \ N, ρ x = ‖ψ x‖ ^ 2) (hzero : ∀ x ∈ U, ρ x = 0 ↔ x ∈ N) :
    ∀ x ∈ U, u x = 0 ↔ x ∈ N := by
  intro x hx
  rw [← hzero x hx, ← norm_sq_eq hU hnull hu huψ hρ hρψ x hx]
  simp

variable (p : MassiveParameters) {g : Covector → Mat4}

/-- The Klein–Gordon operator depends only on the germ of the field. -/
theorem kgOperator_congr {x : Covector} (h : u =ᶠ[𝓝 x] ψ) :
    kgOperator p g u x = kgOperator p g ψ x := by
  have hflux (i : Fin 4) : (fun y => flux g u y i) =ᶠ[𝓝 x] fun y => flux g ψ y i := by
    filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
    simp only [flux, hy]
  have hd (i : Fin 4) :
      fderiv ℝ (fun y => flux g u y i) x = fderiv ℝ (fun y => flux g ψ y i) x :=
    (hflux i).fderiv_eq
  simp only [kgOperator, wave, hd, h.eq_of_nhds]

/-- A twice continuously differentiable field solving the equation off a set
of zero volume solves it everywhere on the open set. -/
theorem kgOperator_eq_zero (hU : IsOpen U) (hnull : volume N = 0)
    (hg : ∀ x ∈ U, ContDiffAt ℝ 2 g x) (hd : ∀ x ∈ U, (g x).det < 0)
    (hu : ∀ x ∈ U, ContDiffAt ℝ 2 u x) (hKG : ∀ x ∈ U \ N, kgOperator p g u x = 0) :
    ∀ x ∈ U, kgOperator p g u x = 0 := by
  have hcont : ContinuousOn (residual p g u) U := fun x hx =>
    (residual_continuousAt p (hg x hx) (hd x hx) (hu x hx)).continuousWithinAt
  have h0 : EqOn (residual p g u) (fun _ => 0) (U \ N) := fun x hx =>
    (residual_zero_iff p g u x).2 (hKG x hx)
  have h := h0.of_subset_closure hcont continuousOn_const sdiff_subset
    (subset_closure_off hU hnull)
  exact fun x hx => (residual_zero_iff p g u x).1 (h hx)

/-- Smooth continuation across a closed null nodal set: a twice continuously
differentiable field almost everywhere equal to a solution off the set agrees
with it off the set and solves the equation on the whole open set. -/
theorem continuation (hU : IsOpen U) (hN : IsClosed N) (hnull : volume N = 0)
    (hg : ∀ x ∈ U, ContDiffAt ℝ 2 g x) (hd : ∀ x ∈ U, (g x).det < 0)
    (hψ : ∀ x ∈ U \ N, ContDiffAt ℝ 2 ψ x) (hKG : ∀ x ∈ U \ N, kgOperator p g ψ x = 0)
    (hu : ∀ x ∈ U, ContDiffAt ℝ 2 u x) (hae : u =ᵐ[volume.restrict U] ψ) :
    EqOn u ψ (U \ N) ∧ ∀ x ∈ U, kgOperator p g u x = 0 := by
  have hcu : ContinuousOn u U := fun x hx => (hu x hx).continuousAt.continuousWithinAt
  have hcψ : ContinuousOn ψ (U \ N) := fun x hx => (hψ x hx).continuousAt.continuousWithinAt
  have heq := eqOn_off hU hN hcψ hcu hae
  refine ⟨heq, kgOperator_eq_zero p hU hnull hg hd hu fun x hx => ?_⟩
  rw [kgOperator_congr p (heq.eventuallyEq_of_mem ((hU.sdiff hN).mem_nhds hx))]
  exact hKG x hx

variable {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S]

/-- Smooth continuation across a closed embedded nodal surface, with exact
identification of the nodal set of the continued field. -/
theorem embedded_continuation {f : S → Covector}
    (hf : IsSmoothEmbedding 𝓘(ℝ, ℂ) 𝓘(ℝ, Covector) ∞ f) (hN : IsClosed (range f))
    (hU : IsOpen U) (hg : ∀ x ∈ U, ContDiffAt ℝ 2 g x) (hd : ∀ x ∈ U, (g x).det < 0)
    (hψ : ∀ x ∈ U \ range f, ContDiffAt ℝ 2 ψ x)
    (hKG : ∀ x ∈ U \ range f, kgOperator p g ψ x = 0)
    (hu : ∀ x ∈ U, ContDiffAt ℝ 2 u x) (hae : u =ᵐ[volume.restrict U] ψ)
    {ρ : Covector → ℝ} (hρ : ContinuousOn ρ U) (hρψ : ∀ x ∈ U \ range f, ρ x = ‖ψ x‖ ^ 2)
    (hzero : ∀ x ∈ U, ρ x = 0 ↔ x ∈ range f) :
    EqOn u ψ (U \ range f) ∧ (∀ x ∈ U, kgOperator p g u x = 0) ∧
    (∀ x ∈ U, ‖u x‖ ^ 2 = ρ x) ∧ ∀ x ∈ U, u x = 0 ↔ x ∈ range f := by
  have hnull := EmbeddedNodalNullity.volume_range_eq_zero hf
  have hcu : ContinuousOn u U := fun x hx => (hu x hx).continuousAt.continuousWithinAt
  obtain ⟨heq, hop⟩ := continuation p hU hN hnull hg hd hψ hKG hu hae
  exact ⟨heq, hop, norm_sq_eq hU hnull hcu heq hρ hρψ,
    eq_zero_iff hU hnull hcu heq hρ hρψ hzero⟩

end FoliationQM.NodalSmoothContinuation
