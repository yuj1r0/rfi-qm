module

public import FoliationQM.TidalFieldEquation
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# The tidal variation along the modulus curve

Source: v13 `thm:tidal_dispersion` (Conjecture 9.7) and `eq:tidal_KG_eq`, the
variation `δ|ψ| = (ψ/2|ψ|) δψ* + c.c.` of `eq:tidal_lagrangian_thm`, component
kinds B and C. For a twice continuously differentiable field `ψ` that does not
vanish on a set `U`, and a continuously differentiable complex variation `η`
with compact support in `U`, the relative tidal functional of the modulus
`|ψ + t η|` is differentiable in `t` at `t = 0`, with derivative
`-2 Re ∫ η̄ (ψ/|ψ|) ∂_j(T^{ji} ∂_i |ψ|)`.

The functional is differentiated along the curve `|ψ + t η|` itself. The
coordinate gradient of the modulus along the curve is `|u| Re(u⁻¹ v)` with
`u = ψ + t η` and `v = ∂ψ + t ∂η`; its parameter derivative at `t = 0` is the
gradient of the amplitude direction `Re(ψ̄ η)/|ψ|`, and the interchange of the
parameter derivative with the integral is by dominated convergence on the
compact support of `η`. The external velocity is held fixed. Nothing here
supports the physical ansatz of the conjecture or extends through zeros of
the field.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.TidalModulusVariation

open MeasureTheory Set Matrix LorentzMatrixGroup RNCCoordinateConnection RealLorentzFrame
open TidalAmplitudeVariation TidalCoefficient TidalFieldEquation NodalPolarConverse
open scoped Topology ComplexConjugate

/-- The derivative `|u| Re(u⁻¹ v)` of the modulus at a value `u` whose
derivative is `v`. -/
def modulusSlope (u v : ℂ) : ℝ := ‖u‖ * (u⁻¹ * v).re

/-- The derivative of `modulusSlope u v` when `u` has derivative `w` and `v`
has derivative `b`. -/
def modulusSlopeDeriv (u v w b : ℂ) : ℝ :=
  ‖u‖ * (u⁻¹ * w).re * (u⁻¹ * v).re + ‖u‖ * (u⁻¹ * b - u⁻¹ ^ 2 * w * v).re

/-- The derivative of the modulus slope is symmetric in the two first-order
directions. -/
theorem modulusSlopeDeriv_comm (u v w b : ℂ) :
    modulusSlopeDeriv u v w b = modulusSlopeDeriv u w v b := by
  simp only [modulusSlopeDeriv]
  rw [show u⁻¹ ^ 2 * w * v = u⁻¹ ^ 2 * v * w by ring]
  ring

/-- The amplitude direction `Re(ψ̄ η)/|ψ|` is the modulus slope of the value
`ψ` in the direction `η`. -/
theorem amplitudeDirection_eq (ψ η : Covector → ℂ) (x : Covector) :
    amplitudeDirection ψ η x = modulusSlope (ψ x) (η x) := by
  simp only [amplitudeDirection, modulusSlope]
  by_cases hz : ψ x = 0
  · simp [hz]
  have hn : ‖ψ x‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq,
    show conj (ψ x) * (((‖ψ x‖ ^ 2)⁻¹ : ℝ) : ℂ) * η x =
      (((‖ψ x‖ ^ 2)⁻¹ : ℝ) : ℂ) * (conj (ψ x) * η x) by ring, Complex.re_ofReal_mul]
  field_simp

section Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {u v : E → ℂ}
  {Du Dv : E →L[ℝ] ℂ} {x : E}

/-- The chain rule for the modulus slope of two differentiable complex
functions, at a point where the first does not vanish. -/
theorem hasFDerivAt_modulusSlope (hu : HasFDerivAt u Du x) (hv : HasFDerivAt v Dv x)
    (hne : u x ≠ 0) :
    ∃ L : E →L[ℝ] ℝ, HasFDerivAt (fun y => modulusSlope (u y) (v y)) L x ∧
      ∀ e, L e = modulusSlopeDeriv (u x) (v x) (Du e) (Dv e) := by
  have hamp := hasFDerivAt_amplitude hu hne
  have hinv : HasFDerivAt (fun y => (u y)⁻¹)
      ((-ContinuousLinearMap.mulLeftRight ℝ ℂ (u x)⁻¹ (u x)⁻¹).comp Du) x :=
    (hasFDerivAt_inv' (𝕜 := ℝ) hne).comp x hu
  have hre := Complex.reCLM.hasFDerivAt.comp x (hinv.mul hv)
  refine ⟨_, hamp.mul hre, fun e => ?_⟩
  simp only [modulusSlopeDeriv, amplitude, _root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, amplitudeDeriv_apply, Complex.reCLM_apply,
    _root_.neg_apply, ContinuousLinearMap.mulLeftRight_apply, smul_eq_mul]
  rw [show (u x)⁻¹ * Dv e + v x * -((u x)⁻¹ * Du e * (u x)⁻¹) =
    (u x)⁻¹ * Dv e - (u x)⁻¹ ^ 2 * Du e * v x by ring]
  ring

end Calculus

/-- Along the line `z + s w`, `a + s b` the modulus slope has the parameter
derivative `modulusSlopeDeriv`. -/
theorem hasDerivAt_modulusSlope_line {z w a b : ℂ} {t : ℝ} (h : z + (t : ℂ) * w ≠ 0) :
    HasDerivAt (fun s : ℝ => modulusSlope (z + (s : ℂ) * w) (a + (s : ℂ) * b))
      (modulusSlopeDeriv (z + (t : ℂ) * w) (a + (t : ℂ) * b) w b) t := by
  have hu : HasDerivAt (fun s : ℝ => z + (s : ℂ) * w) w t :=
    (((hasDerivAt_id' t).ofReal_comp.mul_const w).const_add z).congr_deriv (by simp)
  have hv : HasDerivAt (fun s : ℝ => a + (s : ℂ) * b) b t :=
    (((hasDerivAt_id' t).ofReal_comp.mul_const b).const_add a).congr_deriv (by simp)
  obtain ⟨L, hL, hval⟩ := hasFDerivAt_modulusSlope hu.hasFDerivAt hv.hasFDerivAt h
  refine hL.hasDerivAt.congr_deriv ?_
  rw [hval]
  simp

section Continuity

variable {X : Type*} [TopologicalSpace X] {s : Set X} {u v w b : X → ℂ}

/-- The modulus slope of continuous data is continuous where the value does
not vanish. -/
theorem continuousOn_modulusSlope (hu : ContinuousOn u s) (hv : ContinuousOn v s)
    (hne : ∀ x ∈ s, u x ≠ 0) : ContinuousOn (fun x => modulusSlope (u x) (v x)) s :=
  hu.norm.mul (Complex.continuous_re.comp_continuousOn ((hu.inv₀ hne).mul hv))

/-- The derivative of the modulus slope is continuous in continuous data
where the value does not vanish. -/
theorem continuousOn_modulusSlopeDeriv (hu : ContinuousOn u s) (hv : ContinuousOn v s)
    (hw : ContinuousOn w s) (hb : ContinuousOn b s) (hne : ∀ x ∈ s, u x ≠ 0) :
    ContinuousOn (fun x => modulusSlopeDeriv (u x) (v x) (w x) (b x)) s :=
  ((hu.norm.mul (Complex.continuous_re.comp_continuousOn ((hu.inv₀ hne).mul hw))).mul
    (Complex.continuous_re.comp_continuousOn ((hu.inv₀ hne).mul hv))).add
    (hu.norm.mul (Complex.continuous_re.comp_continuousOn
      (((hu.inv₀ hne).mul hb).sub ((((hu.inv₀ hne).pow 2).mul hw).mul hv))))

end Continuity

/-- The bilinear form `g_i M^{ij} h_j`. -/
def form (M : Mat4) (g h : Fin 4 → ℝ) : ℝ := g ⬝ᵥ (M *ᵥ h)

/-- The form of a symmetric matrix is symmetric. -/
theorem form_symm {M : Mat4} (hM : M.IsSymm) (g h : Fin 4 → ℝ) : form M g h = form M h g := by
  simp only [form]
  rw [dotProduct_mulVec, ← mulVec_transpose, hM.eq, dotProduct_comm]

/-- The product rule for the quadratic form along a differentiable curve of
vectors. -/
theorem hasDerivAt_form {M : Mat4} {g : ℝ → Fin 4 → ℝ} {g' : Fin 4 → ℝ} {t : ℝ}
    (hg : ∀ i, HasDerivAt (fun s => g s i) (g' i) t) :
    HasDerivAt (fun s => form M (g s) (g s)) (form M g' (g t) + form M (g t) g') t := by
  have h : HasDerivAt (fun s => ∑ i, g s i * ∑ j, M i j * g s j)
      (∑ i, (g' i * ∑ j, M i j * g t j + g t i * ∑ j, M i j * g' j)) t :=
    HasDerivAt.fun_sum fun i _ => (hg i).mul
      (HasDerivAt.fun_sum fun j _ => (hg j).const_mul (M i j))
  simpa only [form, dotProduct, mulVec, Finset.sum_add_distrib] using h

/-- The form of continuous data is continuous. -/
theorem continuousOn_form {X : Type*} [TopologicalSpace X] {s : Set X} {M : X → Mat4}
    {g h : X → Fin 4 → ℝ} (hM : ∀ i j, ContinuousOn (fun x => M x i j) s)
    (hg : ∀ i, ContinuousOn (fun x => g x i) s) (hh : ∀ i, ContinuousOn (fun x => h x i) s) :
    ContinuousOn (fun x => form (M x) (g x) (h x)) s := by
  simp only [form, dotProduct, mulVec]
  exact continuousOn_finsetSum _ fun i _ => (hg i).mul
    (continuousOn_finsetSum _ fun j _ => (hM i j).mul (hh j))

variable {T : Covector → Mat4} {ψ η : Covector → ℂ} {U : Set Covector}

/-- The coordinate gradient of the modulus along the curve `ψ + t η`. -/
theorem grad_modulus {x : Covector} (hψ : DifferentiableAt ℝ ψ x) (hη : DifferentiableAt ℝ η x)
    (t : ℝ) (hne : ψ x + (t : ℂ) * η x ≠ 0) (i : Fin 4) :
    grad (fun y => ‖ψ y + (t : ℂ) * η y‖) x i =
      modulusSlope (ψ x + (t : ℂ) * η x)
        (fderiv ℝ ψ x (axis i) + (t : ℂ) * fderiv ℝ η x (axis i)) := by
  have h := hasFDerivAt_amplitude (ψ := fun y => ψ y + (t : ℂ) * η y)
    (hψ.hasFDerivAt.add (hη.hasFDerivAt.const_mul (t : ℂ))) hne
  have h' : fderiv ℝ (fun y => ‖ψ y + (t : ℂ) * η y‖) x =
      amplitudeDeriv (ψ x + (t : ℂ) * η x) (fderiv ℝ ψ x + (t : ℂ) • fderiv ℝ η x) := h.fderiv
  simp only [grad, h', amplitudeDeriv_apply, modulusSlope, _root_.add_apply, _root_.smul_apply,
    smul_eq_mul]

/-- The coordinate gradient of the amplitude direction `Re(ψ̄ η)/|ψ|`. -/
theorem grad_amplitudeDirection {x : Covector} (hψ : DifferentiableAt ℝ ψ x)
    (hη : DifferentiableAt ℝ η x) (hne : ψ x ≠ 0) (i : Fin 4) :
    grad (amplitudeDirection ψ η) x i =
      modulusSlopeDeriv (ψ x) (η x) (fderiv ℝ ψ x (axis i)) (fderiv ℝ η x (axis i)) := by
  obtain ⟨L, hL, hval⟩ := hasFDerivAt_modulusSlope hψ.hasFDerivAt hη.hasFDerivAt hne
  have hfun : amplitudeDirection ψ η = fun y => modulusSlope (ψ y) (η y) :=
    funext (amplitudeDirection_eq ψ η)
  change fderiv ℝ (amplitudeDirection ψ η) x (axis i) = _
  rw [hfun, hL.fderiv, hval]

private theorem amplitudeDirection_data (hψ : ∀ x ∈ U, ContDiffAt ℝ 2 ψ x)
    (hne : ∀ x ∈ U, ψ x ≠ 0) (hη : ContDiff ℝ 1 η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ U) :
    ContDiff ℝ 1 (amplitudeDirection ψ η) ∧ HasCompactSupport (amplitudeDirection ψ η) ∧
      tsupport (amplitudeDirection ψ η) ⊆ tsupport η := by
  have hsupp : Function.support (amplitudeDirection ψ η) ⊆ Function.support η := by
    intro x hx hηx
    exact hx (by simp [amplitudeDirection, hηx])
  refine ⟨contDiff_iff_contDiffAt.2 fun x => ?_, hc.mono hsupp, closure_mono hsupp⟩
  by_cases hx : x ∈ tsupport η
  · have hψ1 : ContDiffAt ℝ 1 ψ x := (hψ x (hs hx)).of_le (by norm_num)
    have hnum : ContDiffAt ℝ 1 (fun y => (conj (ψ y) * η y).re) x :=
      Complex.reCLM.contDiff.contDiffAt.comp x
        ((Complex.conjCLE.contDiff.contDiffAt.comp x hψ1).mul hη.contDiffAt)
    exact hnum.div (hψ1.norm ℝ (hne x (hs hx))) (norm_ne_zero_iff.mpr (hne x (hs hx)))
  · have hz : amplitudeDirection ψ η =ᶠ[𝓝 x] fun _ => 0 :=
      (notMem_tsupport_iff_eventuallyEq.mp hx).mono fun y hy => by
        simp [amplitudeDirection, hy]
    exact contDiffAt_const.congr_of_eventuallyEq hz

/-- The first variation of the tidal functional along the modulus curve
`|ψ + t η|` of a compactly supported complex variation is
`-2 Re ∫ η̄ (ψ/|ψ|) ∂_j(T^{ji} ∂_i |ψ|)`. -/
theorem first_variation_modulus (hsym : ∀ x ∈ U, (T x).IsSymm)
    (hT : ∀ i j, ∀ x ∈ U, ContDiffAt ℝ 1 (fun y => T y i j) x)
    (hψ : ∀ x ∈ U, ContDiffAt ℝ 2 ψ x) (hne : ∀ x ∈ U, ψ x ≠ 0)
    (hη : ContDiff ℝ 1 η) (hc : HasCompactSupport η) (hs : tsupport η ⊆ U) :
    HasDerivAt (fun t : ℝ => ∫ x,
        (tidalDensity T (fun y => ‖ψ y + (t : ℂ) * η y‖) x -
          tidalDensity T (fun y => ‖ψ y‖) x))
      (-2 * ∫ x, (conj (η x) * (ψ x / (‖ψ x‖ : ℂ) *
        (tidalDivergence T (fun y => ‖ψ y‖) x : ℂ))).re) 0 := by
  classical
  set K : Set Covector := tsupport η with hKdef
  have hK : IsCompact K := hc
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hψd : ∀ x ∈ K, DifferentiableAt ℝ ψ x := fun x hx =>
    (hψ x (hs hx)).differentiableAt (by norm_num)
  have hηd : ∀ x, DifferentiableAt ℝ η x := fun x => hη.differentiable one_ne_zero x
  have hψK : ContinuousOn ψ K := fun x hx => (hψ x (hs hx)).continuousAt.continuousWithinAt
  obtain ⟨m, hm, hmK⟩ := hK.exists_forall_le' (f := fun x => ‖ψ x‖) hψK.norm (a := 0)
    (fun x hx => norm_pos_iff.mpr (hne x (hs hx)))
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hη.continuous
  have hC1 : 0 < |C| + 1 := by positivity
  set δ : ℝ := m / (2 * (|C| + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  have hne' : ∀ t : ℝ, |t| ≤ δ → ∀ x ∈ K, ψ x + (t : ℂ) * η x ≠ 0 := by
    intro t ht x hx h0
    have h1 : ‖ψ x‖ = ‖(t : ℂ) * η x‖ := by
      rw [eq_neg_of_add_eq_zero_left h0, norm_neg]
    have h2 : ‖(t : ℂ) * η x‖ ≤ δ * (|C| + 1) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul ht ((hC x).trans ((le_abs_self C).trans (by linarith)))
        (norm_nonneg _) hδ.le
    have h3 : δ * (|C| + 1) = m / 2 := by
      rw [hδdef]
      field_simp
    have h4 := hmK x hx
    linarith
  let dψ : Fin 4 → Covector → ℂ := fun i x => fderiv ℝ ψ x (axis i)
  let dη : Fin 4 → Covector → ℂ := fun i x => fderiv ℝ η x (axis i)
  let G : ℝ → Covector → Fin 4 → ℝ := fun t x i =>
    modulusSlope (ψ x + (t : ℂ) * η x) (dψ i x + (t : ℂ) * dη i x)
  let G' : ℝ → Covector → Fin 4 → ℝ := fun t x i =>
    modulusSlopeDeriv (ψ x + (t : ℂ) * η x) (dψ i x + (t : ℂ) * dη i x) (η x) (dη i x)
  let S : Set (ℝ × Covector) := Metric.closedBall 0 δ ×ˢ K
  have hS : IsCompact S := (isCompact_closedBall 0 δ).prod hK
  have hmemS : ∀ t : ℝ, |t| ≤ δ → ∀ x ∈ K, (t, x) ∈ S := fun t ht x hx =>
    ⟨mem_closedBall_zero_iff.mpr ((Real.norm_eq_abs t).le.trans ht), hx⟩
  have hcast : Continuous fun p : ℝ × Covector => (p.1 : ℂ) :=
    Complex.continuous_ofReal.comp continuous_fst
  have hu : ContinuousOn (fun p : ℝ × Covector => ψ p.2 + (p.1 : ℂ) * η p.2) S :=
    (hψK.comp continuousOn_snd fun p hp => hp.2).add
      (hcast.mul (hη.continuous.comp continuous_snd)).continuousOn
  have hdψK (i : Fin 4) : ContinuousOn (dψ i) K := fun x hx =>
    ((((hψ x (hs hx)).fderiv_right (m := 1) (by norm_num)).continuousAt).clm_apply
      continuousAt_const).continuousWithinAt
  have hdη (i : Fin 4) : Continuous (dη i) :=
    (hη.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hv (i : Fin 4) :
      ContinuousOn (fun p : ℝ × Covector => dψ i p.2 + (p.1 : ℂ) * dη i p.2) S :=
    ((hdψK i).comp continuousOn_snd fun p hp => hp.2).add
      (hcast.mul ((hdη i).comp continuous_snd)).continuousOn
  have hw : ContinuousOn (fun p : ℝ × Covector => η p.2) S :=
    (hη.continuous.comp continuous_snd).continuousOn
  have hb (i : Fin 4) : ContinuousOn (fun p : ℝ × Covector => dη i p.2) S :=
    ((hdη i).comp continuous_snd).continuousOn
  have huS : ∀ p ∈ S, ψ p.2 + (p.1 : ℂ) * η p.2 ≠ 0 := fun p hp =>
    hne' p.1 ((Real.norm_eq_abs p.1).ge.trans (mem_closedBall_zero_iff.mp hp.1)) p.2 hp.2
  have hGS (i : Fin 4) : ContinuousOn (fun p : ℝ × Covector => G p.1 p.2 i) S :=
    continuousOn_modulusSlope hu (hv i) huS
  have hG'S (i : Fin 4) : ContinuousOn (fun p : ℝ × Covector => G' p.1 p.2 i) S :=
    continuousOn_modulusSlopeDeriv hu (hv i) hw (hb i) huS
  have hTU (i j : Fin 4) : ContinuousOn (fun y => T y i j) U := fun x hx =>
    (hT i j x hx).continuousAt.continuousWithinAt
  have hTS (i j : Fin 4) : ContinuousOn (fun p : ℝ × Covector => T p.2 i j) S :=
    (hTU i j).comp continuousOn_snd fun p hp => hs hp.2
  let Γ : ℝ × Covector → ℝ := fun p => form (T p.2) (G p.1 p.2) (G p.1 p.2)
  let Φ : ℝ × Covector → ℝ := fun p =>
    form (T p.2) (G' p.1 p.2) (G p.1 p.2) + form (T p.2) (G p.1 p.2) (G' p.1 p.2)
  have hΓ : ContinuousOn Γ S := continuousOn_form hTS hGS hGS
  have hΦ : ContinuousOn Φ S :=
    (continuousOn_form hTS hG'S hGS).add (continuousOn_form hTS hGS hG'S)
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hΦ
  let F : ℝ → Covector → ℝ := fun t x =>
    tidalDensity T (fun y => ‖ψ y + (t : ℂ) * η y‖) x - tidalDensity T (fun y => ‖ψ y‖) x
  let F' : ℝ → Covector → ℝ := fun t => K.indicator fun x => Φ (t, x)
  have hFout : ∀ t x, x ∉ K → F t x = 0 := by
    intro t x hx
    have hz : η =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
    have he : (fun y => ‖ψ y + (t : ℂ) * η y‖) =ᶠ[𝓝 x] fun y => ‖ψ y‖ :=
      hz.mono fun y hy => by simp [hy]
    have hg : grad (fun y => ‖ψ y + (t : ℂ) * η y‖) x = grad (fun y => ‖ψ y‖) x := by
      funext i
      change fderiv ℝ (fun y => ‖ψ y + (t : ℂ) * η y‖) x (axis i) =
        fderiv ℝ (fun y => ‖ψ y‖) x (axis i)
      rw [he.fderiv_eq]
    simp only [F, tidalDensity, hg, sub_self]
  have hG0 : ∀ x ∈ K, grad (fun y => ‖ψ y‖) x = G 0 x := by
    intro x hx
    funext i
    have h := grad_modulus (hψd x hx) (hηd x) 0 (by simpa using hne x (hs hx)) i
    simpa [G, dψ, dη] using h
  have hFin : ∀ t : ℝ, |t| ≤ δ → ∀ x ∈ K, F t x = Γ (t, x) - Γ (0, x) := by
    intro t ht x hx
    have h1 : grad (fun y => ‖ψ y + (t : ℂ) * η y‖) x = G t x :=
      funext fun i => grad_modulus (hψd x hx) (hηd x) t (hne' t ht x hx) i
    simp only [F, Γ, tidalDensity, form, h1, hG0 x hx]
  have habs : ∀ t ∈ Metric.ball (0 : ℝ) δ, |t| ≤ δ := fun t ht =>
    (Real.norm_eq_abs t).ge.trans (mem_ball_zero_iff.mp ht).le
  have hdiff : ∀ x, ∀ t ∈ Metric.ball (0 : ℝ) δ, HasDerivAt (fun s => F s x) (F' t x) t := by
    intro x t ht
    by_cases hx : x ∈ K
    · have hGd (i : Fin 4) : HasDerivAt (fun s : ℝ => G s x i) (G' t x i) t :=
        hasDerivAt_modulusSlope_line (hne' t (habs t ht) x hx)
      have h := (hasDerivAt_form (M := T x) (g := fun s => G s x) (g' := G' t x) hGd).sub_const
        (Γ (0, x))
      have hev : (fun s => F s x) =ᶠ[𝓝 t]
          fun s => form (T x) (G s x) (G s x) - Γ (0, x) := by
        filter_upwards [Metric.isOpen_ball.mem_nhds ht] with s hs'
        exact hFin s (habs s hs') x hx
      have hF' : F' t x = form (T x) (G' t x) (G t x) + form (T x) (G t x) (G' t x) := by
        simp only [F', indicator_of_mem hx, Φ]
      rw [hF']
      exact h.congr_of_eventuallyEq hev
    · have hF' : F' t x = 0 := by simp only [F', indicator_of_notMem hx]
      rw [hF', show (fun s => F s x) = fun _ => 0 from funext fun s => hFout s x hx]
      exact hasDerivAt_const t 0
  have hbound : ∀ x, ∀ t ∈ Metric.ball (0 : ℝ) δ, ‖F' t x‖ ≤ K.indicator (fun _ => B) x := by
    intro x t ht
    by_cases hx : x ∈ K
    · simp only [F', indicator_of_mem hx]
      exact hB (t, x) (hmemS t (habs t ht) x hx)
    · simp [F', indicator_of_notMem hx]
  have hslice : ∀ t : ℝ, |t| ≤ δ → ∀ {f : ℝ × Covector → ℝ}, ContinuousOn f S →
      AEStronglyMeasurable (K.indicator fun x => f (t, x)) volume := by
    intro t ht f hf
    have hcont : ContinuousOn (fun x => f (t, x)) K :=
      hf.comp (continuous_const.prodMk continuous_id).continuousOn fun x hx => hmemS t ht x hx
    exact (aestronglyMeasurable_indicator_iff hKm).mpr (hcont.aestronglyMeasurable hKm)
  have hFmeas : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (F t) volume := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with t ht
    have hEq : F t = K.indicator fun x => (fun p : ℝ × Covector => Γ p - Γ (0, p.2)) (t, x) := by
      funext x
      by_cases hx : x ∈ K
      · rw [indicator_of_mem hx]
        exact hFin t (habs t ht) x hx
      · rw [indicator_of_notMem hx]
        exact hFout t x hx
    rw [hEq]
    exact hslice t (habs t ht) (hΓ.sub (hΓ.comp
      (continuous_const.prodMk continuous_snd).continuousOn
      fun p hp => hmemS 0 (by simpa using hδ.le) p.2 hp.2))
  have hF0 : Integrable (F 0) volume := by
    have h0 : F 0 = fun _ => 0 := by
      funext x
      simp [F]
    rw [h0]
    exact integrable_zero _ _ _
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := F) (F' := F')
    (x₀ := (0 : ℝ)) (bound := K.indicator fun _ => B)
    (Metric.ball_mem_nhds (0 : ℝ) hδ) hFmeas hF0 (hslice 0 (by simpa using hδ.le) hΦ)
    (Filter.Eventually.of_forall hbound)
    ((integrableOn_const hK.measure_lt_top.ne).integrable_indicator hKm)
    (Filter.Eventually.of_forall hdiff)
  obtain ⟨hda, hca, hts⟩ := amplitudeDirection_data hψ hne hη hc hs
  have hval : ∀ x, F' 0 x = tidalCross T (fun y => ‖ψ y‖) (amplitudeDirection ψ η) x := by
    intro x
    by_cases hx : x ∈ K
    · have hga : grad (amplitudeDirection ψ η) x = G' 0 x := by
        funext i
        rw [grad_amplitudeDirection (hψd x hx) (hηd x) (hne x (hs hx)) i, modulusSlopeDeriv_comm]
        simp [G', dψ, dη]
      have hF' : F' 0 x = form (T x) (G' 0 x) (G 0 x) + form (T x) (G 0 x) (G' 0 x) := by
        simp only [F', indicator_of_mem hx, Φ]
      have hcross : tidalCross T (fun y => ‖ψ y‖) (amplitudeDirection ψ η) x =
          2 * ((T x *ᵥ G 0 x) ⬝ᵥ G' 0 x) := by
        simp only [tidalCross, tidalFlux, hG0 x hx, hga]
      have e1 := form_symm (hsym x (hs hx)) (G 0 x) (G' 0 x)
      have e2 : form (T x) (G' 0 x) (G 0 x) = (T x *ᵥ G 0 x) ⬝ᵥ G' 0 x := dotProduct_comm _ _
      rw [hF', hcross, e1, e2]
      ring
    · have he : amplitudeDirection ψ η =ᶠ[𝓝 x] 0 :=
        notMem_tsupport_iff_eventuallyEq.mp fun h => hx (hts h)
      have hgrad : grad (amplitudeDirection ψ η) x = 0 := by
        funext i
        simp [grad, he.fderiv_eq]
      have hF' : F' 0 x = 0 := by simp only [F', indicator_of_notMem hx]
      rw [hF']
      simp [tidalCross, hgrad]
  have hint : (∫ x, F' 0 x) =
      ∫ x, tidalCross T (fun y => ‖ψ y‖) (amplitudeDirection ψ η) x :=
    integral_congr_ae (Filter.Eventually.of_forall hval)
  have hR : ∀ x ∈ U, ContDiffAt ℝ 2 (fun y => ‖ψ y‖) x := fun x hx =>
    (hψ x hx).norm ℝ (hne x hx)
  have hfun : (fun x => amplitudeDirection ψ η x * tidalDivergence T (fun y => ‖ψ y‖) x) =
      fun x => (conj (η x) * (ψ x / (‖ψ x‖ : ℂ) *
        (tidalDivergence T (fun y => ‖ψ y‖) x : ℂ))).re :=
    funext fun x => amplitudeDirection_mul ψ η x _
  have h := key.2
  rw [hint, integral_cross_eq hT hR hda hca (hts.trans hs), hfun] at h
  exact h

end FoliationQM.TidalModulusVariation
