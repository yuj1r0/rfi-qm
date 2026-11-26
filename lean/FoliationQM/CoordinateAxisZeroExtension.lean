module

public import FoliationQM.CoordinateOffAxisWeakDerivative
public import FoliationQM.RNCCoordinateConnection
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.LinearAlgebra.Pi

/-!
# Zero extension across the flat coordinate axis

Source: v13 `thm:wallstrom` Part (c), component kinds C and D.
The literal coordinate axis is closed and null. Setting the field to zero
there preserves its off-axis germ and transfers genuine local L² data for
the field and its actual coordinate derivatives. Finite linear reconstruction
then supplies every directional L² bound needed for the ambient weak identity.
Almost-everywhere uniqueness here is uniqueness of an extension agreeing off
the null axis; standard Hilbert H¹, general nodal charts and Cauchy uniqueness
remain separate.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.CoordinateAxisZeroExtension

open Filter MeasureTheory Set RNCCoordinateConnection
open scoped ContDiff Topology

/-- The actual field, set to zero on the literal codimension-two coordinate axis. -/
def zeroExtension (ψ : Covector → ℂ) : Covector → ℂ :=
  {x : Covector | ¬ (x 2 = 0 ∧ x 3 = 0)}.indicator ψ

private theorem axis_closed : IsClosed {x : Covector | x 2 = 0 ∧ x 3 = 0} := by
  exact (isClosed_eq (continuous_apply (2 : Fin 4)) continuous_const).inter
    (isClosed_eq (continuous_apply (3 : Fin 4)) continuous_const)

private theorem off_axis_ae : ∀ᵐ x : Covector ∂volume, ¬ (x 2 = 0 ∧ x 3 = 0) :=
  measure_eq_zero_iff_ae_notMem.mp SmoothCoordinateTubeCutoff.axis_null

/-- Zero extension preserves every off-axis germ and the ambient a.e. class; every other extension agreeing off the axis is a.e. equal to it. -/
theorem off_axis_data (ψ : Covector → ℂ) :
    (∀ x : Covector, ¬ (x 2 = 0 ∧ x 3 = 0) →
      zeroExtension ψ =ᶠ[𝓝 x] ψ) ∧
    zeroExtension ψ =ᵐ[volume] ψ ∧
    ∀ χ : Covector → ℂ,
      (∀ x : Covector, ¬ (x 2 = 0 ∧ x 3 = 0) → χ x = ψ x) →
      χ =ᵐ[volume] zeroExtension ψ := by
  have hg : ∀ x : Covector, ¬ (x 2 = 0 ∧ x 3 = 0) →
      zeroExtension ψ =ᶠ[𝓝 x] ψ := by
    intro x hx
    filter_upwards [axis_closed.isOpen_compl.mem_nhds hx] with y hy
    exact indicator_of_mem hy ψ
  have ha : zeroExtension ψ =ᵐ[volume] ψ := by
    filter_upwards [off_axis_ae] with x hx
    exact (hg x hx).eq_of_nhds
  refine ⟨hg, ha, ?_⟩
  intro χ hχ
  filter_upwards [off_axis_ae, ha] with x hx he
  exact (hχ x hx).trans he.symm

/-- Field and actual coordinate-derivative L² data off the null axis transfer to the zero extension on any set, without a measurable-set or differentiability premise. -/
theorem memLp_data {K : Set Covector} {ψ : Covector → ℂ}
    (hψ : MemLp ψ 2 (volume.restrict (K \ {x : Covector | x 2 = 0 ∧ x 3 = 0})))
    (hD : ∀ i : Fin 4, MemLp (fun x => fderiv ℝ ψ x (axis i)) 2
      (volume.restrict (K \ {x : Covector | x 2 = 0 ∧ x 3 = 0}))) :
    MemLp (zeroExtension ψ) 2 (volume.restrict K) ∧ ∀ i : Fin 4,
      MemLp (fun x => fderiv ℝ (zeroExtension ψ) x (axis i)) 2
        (volume.restrict K) := by
  have hμ : volume.restrict (K \ {x : Covector | x 2 = 0 ∧ x 3 = 0}) =
      volume.restrict K := by
    apply Measure.restrict_congr_set
    filter_upwards [off_axis_ae] with x hx
    simp only [Set.mem_sdiff, mem_ofPred_eq, hx, not_false_eq_true, and_true]
  rw [hμ] at hψ hD
  have H := off_axis_data ψ
  refine ⟨MemLp.ae_eq (ae_restrict_of_ae H.2.1.symm) hψ, ?_⟩
  intro i
  apply MemLp.ae_eq (hf_Lp := hD i)
  filter_upwards [ae_restrict_of_ae off_axis_ae] with x hx
  exact (congrArg (fun L : Covector →L[ℝ] ℂ => L (axis i)) (H.1 x hx).fderiv_eq).symm

private theorem memLp_directional {K : Set Covector} {ψ : Covector → ℂ}
    (hD : ∀ i : Fin 4, MemLp (fun x => fderiv ℝ ψ x (axis i)) 2 (volume.restrict K))
    (v : Covector) :
    MemLp (fun x => fderiv ℝ ψ x v) 2 (volume.restrict K) := by
  have hb (i : Fin 4) : (fun j : Fin 4 => if i = j then (1 : ℝ) else 0) = axis i := by
    funext j
    simp [axis, Pi.single_apply, eq_comm]
  have he (x : Covector) : fderiv ℝ ψ x v =
      ∑ i : Fin 4, v i • fderiv ℝ ψ x (axis i) := by
    simpa only [hb, ContinuousLinearMap.coe_coe] using
      LinearMap.pi_apply_eq_sum_univ (fderiv ℝ ψ x).toLinearMap v
  simp_rw [he]
  exact memLp_finsetSum Finset.univ (fun i _ => (hD i).const_smul (v i))

/-- Actual off-axis differentiability and coordinate L² data yield genuinely integrable ambient pairings and the weak directional derivative identity for the constructed zero extension. -/
theorem weak_identity {K : Set Covector} {φ ψ : Covector → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ K)
    (hψ : MemLp ψ 2 (volume.restrict (K \ {x : Covector | x 2 = 0 ∧ x 3 = 0})))
    (hD : ∀ i : Fin 4, MemLp (fun x => fderiv ℝ ψ x (axis i)) 2
      (volume.restrict (K \ {x : Covector | x 2 = 0 ∧ x 3 = 0})))
    (hdiff : ∀ x ∈ K \ {y : Covector | y 2 = 0 ∧ y 3 = 0}, DifferentiableAt ℝ ψ x)
    (v : Covector) :
    Integrable (fun x => star (fderiv ℝ φ x v) * zeroExtension ψ x) volume ∧
    Integrable (fun x => star (φ x) * fderiv ℝ (zeroExtension ψ) x v) volume ∧
    (∫ x, star (fderiv ℝ φ x v) * zeroExtension ψ x) =
      -(∫ x, star (φ x) * fderiv ℝ (zeroExtension ψ) x v) := by
  obtain ⟨hL, hDL⟩ := memLp_data hψ hD
  apply CoordinateOffAxisWeakDerivative.weak_directional_identity hφ hc hs hL
    (fun x hx => (hdiff x hx).congr_of_eventuallyEq ((off_axis_data ψ).1 x hx.2)) v
  exact memLp_directional hDL v

end FoliationQM.CoordinateAxisZeroExtension
