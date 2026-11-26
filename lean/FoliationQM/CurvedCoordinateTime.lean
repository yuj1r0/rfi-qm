module

public import FoliationQM.LorentzMatrixGroup
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Actual local coordinate-time reparameterization

A C¹ proper-parameter curve with a positive time component has an actual
local inverse for its coordinate-time function. Differentiating that
inverse gives the coordinate-time trajectory equation on a neighborhood,
not just its formal coefficient at one point. No global flow is assumed.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedCoordinateTime

open Filter LorentzMatrixGroup
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Coordinate time for a spacetime curve whose zeroth coordinate is `ct`. -/
def coordinateTime (c : ℝ) (γ : ℝ → Covector) (τ : ℝ) : ℝ := γ τ 0 / c

variable {γ : ℝ → Covector} {U : Covector → Covector} {τ₀ : ℝ}

/-- The actual coordinate-time derivative is the zeroth component of the curve derivative divided by `c`. -/
theorem hasDerivAt_coordinateTime (c : ℝ) {v : Covector} (hγ : HasDerivAt γ v τ₀) :
    HasDerivAt (coordinateTime c γ) (v 0 / c) τ₀ :=
  (hasDerivAt_pi.mp hγ 0).div_const c

/-- Taking the time coordinate and dividing by a constant preserves local continuous differentiability. -/
theorem contDiffAt_coordinateTime (c : ℝ) {n : WithTop ℕ∞} (hγ : ContDiffAt ℝ n γ τ₀) :
    ContDiffAt ℝ n (coordinateTime c γ) τ₀ := by
  let P : Covector →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  exact (P.contDiff.contDiffAt.comp τ₀ hγ).div_const c

/-- A positive-time C¹ trajectory admits a genuine local coordinate-time inverse and the reparameterized trajectory equation on a neighborhood. -/
theorem exists_local_reparametrization {c : ℝ} (hc : 0 < c) (hγ : ContDiffAt ℝ 1 γ τ₀)
    (hODE : ∀ᶠ τ in 𝓝 τ₀, HasDerivAt γ (U (γ τ)) τ) (hU0 : 0 < U (γ τ₀) 0) :
    ∃ κ : ℝ → ℝ,
      κ (coordinateTime c γ τ₀) = τ₀ ∧
      (∀ᶠ τ in 𝓝 τ₀, κ (coordinateTime c γ τ) = τ) ∧
      (∀ᶠ t in 𝓝 (coordinateTime c γ τ₀), coordinateTime c γ (κ t) = t) ∧
      HasDerivAt κ (c / U (γ τ₀) 0) (coordinateTime c γ τ₀) ∧
      HasDerivAt (γ ∘ κ) ((c / U (γ τ₀) 0) • U (γ τ₀)) (coordinateTime c γ τ₀) ∧
      (∀ᶠ t in 𝓝 (coordinateTime c γ τ₀),
        HasDerivAt (γ ∘ κ) ((c / U (γ (κ t)) 0) • U (γ (κ t))) t) ∧
      (∀ᶠ t in 𝓝 (coordinateTime c γ τ₀), γ (κ t) 0 = c * t) := by
  let f := coordinateTime c γ
  have hf : ContDiffAt ℝ 1 f τ₀ := contDiffAt_coordinateTime c hγ
  have hd : HasDerivAt f (U (γ τ₀) 0 / c) τ₀ := hasDerivAt_coordinateTime c hODE.self_of_nhds
  have hpos : 0 < U (γ τ₀) 0 / c := div_pos hU0 hc
  have hstrict := hf.hasStrictDerivAt' hd (by decide)
  let e : OpenPartialHomeomorph ℝ ℝ :=
    (hstrict.hasStrictFDerivAt_equiv hpos.ne').toOpenPartialHomeomorph f
  have he_fun : (e : ℝ → ℝ) = f :=
    (hstrict.hasStrictFDerivAt_equiv hpos.ne').toOpenPartialHomeomorph_coe
  have hsource : τ₀ ∈ e.source :=
    (hstrict.hasStrictFDerivAt_equiv hpos.ne').mem_toOpenPartialHomeomorph_source
  have htarget : f τ₀ ∈ e.target := e.map_source hsource
  have hvalue : e.symm (f τ₀) = τ₀ := e.left_inv hsource
  have hleft : ∀ᶠ τ in 𝓝 τ₀, e.symm (f τ) = τ := e.eventually_left_inverse hsource
  have hright : ∀ᶠ t in 𝓝 (f τ₀), f (e.symm t) = t := e.eventually_right_inverse htarget
  have hdi : HasDerivAt e.symm (c / U (γ τ₀) 0) (f τ₀) := by
    have hh : HasDerivAt e (U (γ τ₀) 0 / c) (e.symm (f τ₀)) := by
      simpa only [he_fun, hvalue] using hd
    simpa only [inv_div] using e.hasDerivAt_symm htarget hpos.ne' hh
  have hreparam : HasDerivAt (γ ∘ e.symm) ((c / U (γ τ₀) 0) • U (γ τ₀)) (f τ₀) := by
    have hh : HasDerivAt γ (U (γ τ₀)) (e.symm (f τ₀)) := by
      rw [hvalue]
      exact hODE.self_of_nhds
    exact hh.scomp (f τ₀) hdi
  have hcd : ContinuousAt (deriv f) τ₀ :=
    (hf.fderiv_right (m := 0) (by decide)).continuousAt.clm_apply continuousAt_const
  have hslope : ∀ᶠ τ in 𝓝 τ₀, 0 < deriv f τ :=
    hcd.eventually (Ioi_mem_nhds (by rw [hd.deriv]; exact hpos))
  have htend : Tendsto e.symm (𝓝 (f τ₀)) (𝓝 τ₀) := e.tendsto_symm hsource
  have hnear : ∀ᶠ t in 𝓝 (f τ₀),
      HasDerivAt (γ ∘ e.symm) ((c / U (γ (e.symm t)) 0) • U (γ (e.symm t))) t := by
    filter_upwards [e.open_target.mem_nhds htarget, htend.eventually hODE,
      htend.eventually hslope] with t ht hγt hpt
    have hdt : HasDerivAt f (U (γ (e.symm t)) 0 / c) (e.symm t) :=
      hasDerivAt_coordinateTime c hγt
    have hn : U (γ (e.symm t)) 0 / c ≠ 0 := by
      rw [← hdt.deriv]
      exact hpt.ne'
    have hit : HasDerivAt e.symm (c / U (γ (e.symm t)) 0) t := by
      simpa only [inv_div] using e.hasDerivAt_symm ht hn hdt
    exact hγt.scomp t hit
  refine ⟨e.symm, hvalue, hleft, hright, hdi, hreparam, hnear, ?_⟩
  filter_upwards [hright] with t ht
  have he : γ (e.symm t) 0 / c = t := ht
  exact (div_eq_iff hc.ne').mp he |>.trans (mul_comm t c)

end FoliationQM.CurvedCoordinateTime
