module

public import FoliationQM.TwoParticleMarginals
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Parameter derivatives of spatial fiber integrals

In v13 `eq:marginal_continuity` the retained time and position may be taken
together as a single parameter. The scalar field may be the Born density or
one component of the retained current. A local bound on the actual Fréchet
partial, integrable in the remote spatial variable, justifies differentiation
of each of these integrals.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.MarginalParameterIntegral

open LorentzCoordinates MeasureTheory Filter
open scoped Topology

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The scalar marginal on the remote spatial slice, with parameter `p` held fixed. -/
def marginal (q : P → Spatial → ℝ) (p : P) : ℝ := ∫ y, q p y

/-- The derivative in the retained parameter at a fixed remote coordinate. -/
def «partial» (q : P → Spatial → ℝ) (p : P) (y : Spatial) : P →L[ℝ] ℝ :=
  fderiv ℝ (fun r => q r y) p

/-- A common neighborhood in the parameter on which an integrable spatial
envelope bounds the norm of the partial derivative almost everywhere. -/
def DominatedAt (q : P → Spatial → ℝ) (p : P) : Prop :=
  ∃ s ∈ 𝓝 p, ∃ B : Spatial → ℝ, Integrable B ∧ ∀ᵐ y, ∀ r ∈ s, ‖«partial» q r y‖ ≤ B y

/-- Local conditions at a retained parameter for differentiating a spatial
integral. The exceptional remote set may be discarded before testing all
parameters in the neighborhood. -/
structure RegularAt (q : P → Spatial → ℝ) (p : P) : Prop where
  fiber : Integrable (q p)
  measurable : ∀ᶠ r in 𝓝 p, AEStronglyMeasurable (q r) volume
  partial_measurable : AEStronglyMeasurable («partial» q p) volume
  differentiable : ∃ s ∈ 𝓝 p, ∀ᵐ y, ∀ r ∈ s, DifferentiableAt ℝ (fun z => q z y) r
  dominated : DominatedAt q p

variable {q : P → Spatial → ℝ} {p : P}

/-- The partial of a jointly differentiable field is its full derivative along `(v,0)`. -/
theorem partial_eq_comp (hq : Differentiable ℝ (Function.uncurry q)) (p : P) (y : Spatial) :
    «partial» q p y = (fderiv ℝ (Function.uncurry q) (p,y)).comp
      (ContinuousLinearMap.inl ℝ P Spatial) := by
  change fderiv ℝ (Function.uncurry q ∘ fun r => (r,y)) p = _
  exact (HasFDerivAt.comp (g := Function.uncurry q) (f := fun r => (r,y)) p
    (hq (p,y)).hasFDerivAt (hasFDerivAt_prodMk_left p y)).fderiv

/-- Joint C¹ regularity gives continuity of the operator-valued parameter partial. -/
theorem continuous_partial (hq : ContDiff ℝ 1 (Function.uncurry q)) :
    Continuous (fun z : P × Spatial => «partial» q z.1 z.2) := by
  simp_rw [partial_eq_comp (hq.differentiable (by decide))]
  exact (hq.continuous_fderiv (by decide)).clm_comp continuous_const

/-- A jointly C¹ field with an integrable selected fiber and a local derivative
envelope satisfies the parameter regularity assumptions. -/
theorem RegularAt.of_contDiff (hq : ContDiff ℝ 1 (Function.uncurry q)) (hi : Integrable (q p))
    (hd : DominatedAt q p) : RegularAt q p where
  fiber := hi
  measurable := Eventually.of_forall fun r =>
    (hq.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  partial_measurable :=
    ((continuous_partial hq).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  differentiable := ⟨Set.univ, univ_mem, Eventually.of_forall fun y r _ =>
    (hq.comp (contDiff_prodMk_left y)).differentiable (by decide) r⟩
  dominated := hd

/-- The operator-valued partial derivative is Bochner integrable on the remote slice. -/
theorem integrable_partial (h : RegularAt q p) : Integrable («partial» q p) := by
  obtain ⟨s, hs, B, hi, hB⟩ := h.dominated
  exact hi.mono' h.partial_measurable (hB.mono fun _ hy => hy p (mem_of_mem_nhds hs))

/-- The actual parameter derivative is integrable in every fixed direction. -/
theorem integrable_partial_apply (h : RegularAt q p) (v : P) :
    Integrable (fun y => «partial» q p y v) :=
  (ContinuousLinearMap.apply ℝ ℝ v).integrable_comp (integrable_partial h)

/-- The spatial integral has Fréchet derivative the integral of its parameter partial. -/
theorem marginal_hasFDerivAt (h : RegularAt q p) :
    HasFDerivAt (marginal q) (∫ y, «partial» q p y) p := by
  obtain ⟨s, hs, B, hi, hB⟩ := h.dominated
  obtain ⟨d, hd, hdiff⟩ := h.differentiable
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (F := q) (inter_mem hs hd) h.measurable
    h.fiber h.partial_measurable (hB.mono fun _ hy r hr => hy r hr.1) hi
    (hdiff.mono fun _ hy r hr => (hy r hr.2).hasFDerivAt)

/-- Evaluation in a retained direction commutes with differentiation and remote integration. -/
theorem marginal_fderiv_apply (h : RegularAt q p) (v : P) :
    fderiv ℝ (marginal q) p v = ∫ y, «partial» q p y v := by
  rw [(marginal_hasFDerivAt h).fderiv, ContinuousLinearMap.integral_apply (integrable_partial h)]

/-- For jointly C¹ fields with finite fibers, a local envelope at every parameter
also gives continuity of the integrated derivative and C¹ regularity of the marginal. -/
theorem contDiff_marginal (hq : ContDiff ℝ 1 (Function.uncurry q)) (hi : ∀ p, Integrable (q p))
    (hd : ∀ p, DominatedAt q p) : ContDiff ℝ 1 (marginal q) := by
  apply contDiff_one_iff_hasFDerivAt.mpr
  refine ⟨fun p => ∫ y, «partial» q p y, continuous_iff_continuousAt.mpr ?_,
    fun p => marginal_hasFDerivAt (.of_contDiff hq (hi p) (hd p))⟩
  intro p
  obtain ⟨s, hs, B, hB, hbound⟩ := hd p
  exact continuousAt_of_dominated (Eventually.of_forall fun r =>
    (RegularAt.of_contDiff hq (hi r) (hd r)).partial_measurable)
    (Filter.mem_of_superset hs fun r hr => hbound.mono fun _ hy => hy r hr) hB
    (Eventually.of_forall fun y =>
      ((continuous_partial hq).comp (continuous_id.prodMk continuous_const)).continuousAt)

end FoliationQM.MarginalParameterIntegral
