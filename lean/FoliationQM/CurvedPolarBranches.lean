module

public import FoliationQM.CurvedPolarAction
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Overlap of local action phases in the curved polar action

Every nonzero complex field value in a smooth patch has the anchored
logarithmic coordinates of the scalar wave. On an overlap, positivity fixes
the density, and continuity fixes a single integer phase shift on a
neighborhood of each point. Thus the curved action-gradient contraction
agrees for the two real lifts in any coordinate metric.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedPolarBranches

open ActionDensity PolarDifferential PolarLocalInverse Filter Set
open scoped Topology Matrix.Norms.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A nonzero field value admits a local positive squared-modulus density and a real
action of the original regularity, with exact reconstruction on the full open patch. -/
theorem exists_polar_branch (p : MassiveParameters) {n : WithTop ℕ∞} {ψ : E → ℂ} {U : Set E} {x : E}
    (hU : IsOpen U) (hψ : ContDiffOn ℝ n ψ U) (hx : x ∈ U) (hn : ψ x ≠ 0) :
    ∃ (V : Set E) (S : E → ℝ), IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ContDiffOn ℝ n (fun y => ‖ψ y‖ ^ 2) V ∧ ContDiffOn ℝ n S V ∧
      ∀ y ∈ V, 0 < ‖ψ y‖ ^ 2 ∧ actionField p (fun z => ‖ψ z‖ ^ 2) S y = ψ y := by
  obtain ⟨V, ho, hxV, hVU, hd, hS, he⟩ := exists_local_polar_reconstruction p hU hψ hx hn
  refine ⟨V, fun z => localAction p (ψ x) (ψ z), ho, hxV, hVU, ?_, hS, ?_⟩
  · simpa only [Complex.sq_norm] using hd
  · simpa only [Complex.sq_norm] using he

/-- When continuous angular lifts have the same phase germ, one integer turn
relates their values throughout a neighborhood of the chosen point. -/
theorem angle_overlap {X : Type*} [TopologicalSpace X] {S T : X → ℝ} {x : X} (hS : ContinuousAt S x) (hT : ContinuousAt T x)
    (he : (fun y => phase (S y)) =ᶠ[𝓝 x] fun y => phase (T y)) :
    ∃ n : ℤ, ∀ᶠ y in 𝓝 x, S y - T y = (n : ℝ) * (2 * Real.pi) := by
  let d := fun y => S y - T y
  have hOne : ∀ᶠ y in 𝓝 x, Circle.exp (d y) = 1 := by
    filter_upwards [he] with y hy
    have hc : Circle.exp (S y) = Circle.exp (T y) := Subtype.ext hy
    simp only [d, Circle.exp_sub, hc, div_self']
  obtain ⟨n, hn⟩ := Circle.exp_eq_one.mp hOne.self_of_nhds
  have hp := Real.pi_pos
  have hmem : d x ∈ Ioo (d x - Real.pi / 2) (d x + Real.pi / 2) := ⟨by linarith, by linarith⟩
  have hd : ContinuousAt d x := hS.sub hT
  have hinj := Circle.exp_injOn_Icc (a := d x - Real.pi / 2) (b := d x + Real.pi / 2) (by linarith)
  refine ⟨n, ?_⟩
  filter_upwards [hOne, hd.eventually_mem (isOpen_Ioo.mem_nhds hmem)] with y hy hym
  exact (hinj (Ioo_subset_Icc_self hym) (Ioo_subset_Icc_self hmem) (hy.trans hOne.self_of_nhds.symm)).trans hn

/-- Two positive-density representations of the same field germ have identical densities
and real actions differing by one locally constant integer multiple of 2πℏ. -/
theorem overlap {X : Type*} [TopologicalSpace X] (p : MassiveParameters) {ρ σ S T : X → ℝ} {x : X}
    (hρ : ∀ᶠ y in 𝓝 x, 0 < ρ y) (hσ : ∀ᶠ y in 𝓝 x, 0 < σ y)
    (hS : ContinuousAt S x) (hT : ContinuousAt T x)
    (he : actionField p ρ S =ᶠ[𝓝 x] actionField p σ T) :
    ρ =ᶠ[𝓝 x] σ ∧ ∃ n : ℤ, S =ᶠ[𝓝 x] fun y => T y + (n : ℝ) * (2 * Real.pi * p.hbar) := by
  have hD : ρ =ᶠ[𝓝 x] σ := by
    filter_upwards [hρ, hσ, he] with y hyρ hyσ hy
    exact (polarField_normSq ρ _ y hyρ.le).symm.trans
      ((congrArg Complex.normSq hy).trans (polarField_normSq σ _ y hyσ.le))
  have ha : (fun y => phase (S y / p.hbar)) =ᶠ[𝓝 x] fun y => phase (T y / p.hbar) := by
    filter_upwards [hD, hρ, he] with y hyD hyρ hy
    change (Real.sqrt (ρ y) : ℂ) * phase (S y / p.hbar) =
      (Real.sqrt (σ y) : ℂ) * phase (T y / p.hbar) at hy
    rw [← hyD] at hy
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hyρ).ne') hy
  obtain ⟨n, hn⟩ := angle_overlap (hS.div_const p.hbar) (hT.div_const p.hbar) ha
  refine ⟨hD, n, ?_⟩
  filter_upwards [hn] with y hy
  field_simp [p.hbar_pos.ne'] at hy
  linarith

/-- Both the density and action Fréchet differentials are independent of the
positive polar representative of the same complex wave germ. -/
theorem overlap_differentials (p : MassiveParameters) {ρ σ S T : E → ℝ} {x : E}
    (hρ : ∀ᶠ y in 𝓝 x, 0 < ρ y) (hσ : ∀ᶠ y in 𝓝 x, 0 < σ y)
    (hS : ContinuousAt S x) (hT : ContinuousAt T x)
    (he : actionField p ρ S =ᶠ[𝓝 x] actionField p σ T) :
    fderiv ℝ ρ x = fderiv ℝ σ x ∧ fderiv ℝ S x = fderiv ℝ T x := by
  obtain ⟨hd, n, hs⟩ := overlap p hρ hσ hS hT he
  exact ⟨hd.fderiv_eq, hs.fderiv_eq.trans (fderiv_add_const _)⟩

/-- The inverse-metric action-gradient norm in the curved polar action agrees on phase overlaps. -/
theorem pairing_independent (p : MassiveParameters) (g : Covector → LorentzMatrixGroup.Mat4)
    {ρ σ S T : Covector → ℝ} {x : Covector} (hρ : ∀ᶠ y in 𝓝 x, 0 < ρ y)
    (hσ : ∀ᶠ y in 𝓝 x, 0 < σ y) (hS : ContinuousAt S x) (hT : ContinuousAt T x)
    (he : actionField p ρ S =ᶠ[𝓝 x] actionField p σ T) :
    CurvedGradientCovariance.pairing g S S x = CurvedGradientCovariance.pairing g T T x := by
  have hd := (overlap_differentials p hρ hσ hS hT he).2
  have hc : CurvedGradientCovariance.components S x = CurvedGradientCovariance.components T x :=
    funext fun i => congrArg (fun L : Covector →L[ℝ] ℝ => L (RNCCoordinateConnection.axis i)) hd
  simp only [CurvedGradientCovariance.pairing, hc]

/-- The complete hydrodynamic action density is independent of the positive polar
representation, including its Fisher and scalar-curvature terms. -/
theorem hydroDensity_independent (p : MassiveParameters) (g : Covector → LorentzMatrixGroup.Mat4)
    {ρ σ S T : Covector → ℝ} {x : Covector} (hρ : ∀ᶠ y in 𝓝 x, 0 < ρ y)
    (hσ : ∀ᶠ y in 𝓝 x, 0 < σ y) (hS : ContinuousAt S x) (hT : ContinuousAt T x)
    (he : actionField p ρ S =ᶠ[𝓝 x] actionField p σ T) :
    CurvedPolarAction.hydroDensity p g ρ S x = CurvedPolarAction.hydroDensity p g σ T x := by
  have hd := (overlap p hρ hσ hS hT he).1
  have hlog : (fun y => Real.log (ρ y)) =ᶠ[𝓝 x] (fun y => Real.log (σ y)) :=
    hd.mono fun _ hy => congrArg Real.log hy
  have hc : CurvedGradientCovariance.components (Real.log ∘ ρ) x =
      CurvedGradientCovariance.components (Real.log ∘ σ) x :=
    funext fun i => congrArg (fun L : Covector →L[ℝ] ℝ => L (RNCCoordinateConnection.axis i)) hlog.fderiv_eq
  rw [CurvedPolarAction.hydroDensity, CurvedPolarAction.hydroDensity, hd.self_of_nhds,
    pairing_independent p g hρ hσ hS hT he]
  simp only [CurvedGradientCovariance.pairing, hc]

/-- Integrating the hydrodynamic density on an open overlap gives the same action
for either continuous real phase lift and its positive density. -/
theorem hydroAction_independent (p : MassiveParameters) (g : Covector → LorentzMatrixGroup.Mat4)
    {U : Set Covector} (hU : IsOpen U) {ρ σ S T : Covector → ℝ}
    (hρ : ∀ y ∈ U, 0 < ρ y) (hσ : ∀ y ∈ U, 0 < σ y)
    (hS : ContinuousOn S U) (hT : ContinuousOn T U)
    (he : EqOn (actionField p ρ S) (actionField p σ T) U) :
    CurvedPolarAction.hydroAction p g ρ S U = CurvedPolarAction.hydroAction p g σ T U := by
  apply MeasureTheory.setIntegral_congr_fun hU.measurableSet
  intro x hx
  have hm := hU.mem_nhds hx
  exact congrArg (RNCVolumeDensity.volumeFactor (g x) * ·) <| hydroDensity_independent p g
    (Filter.mem_of_superset hm hρ) (Filter.mem_of_superset hm hσ)
    ((hS x hx).continuousAt hm) ((hT x hx).continuousAt hm) (Filter.mem_of_superset hm he)

end FoliationQM.CurvedPolarBranches
