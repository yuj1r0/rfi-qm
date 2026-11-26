module

public import FoliationQM.TwoBodyDifferentialHamiltonian
public import FoliationQM.SchwartzFiberDerivative
public import FoliationQM.RemoteFluxDivergence

/-!
# Cancellation of the remote differential Hamiltonian

The integral over the second particle's Cartesian slice removes its real
multiplication potential pointwise and its Laplacian by Schwartz integration
by parts along each spatial axis. The same differential operator commutes
with the retained derivative of a Schwartz-valued family.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.TwoBodyRemoteHamiltonian

open MeasureTheory LorentzCoordinates ObserverGaussianFisher SchwartzFiberDerivative
open TwoBodyHamiltonianRealization
open scoped BigOperators Topology

private def line (i : Fin 3) : Fiber →L[ℝ] Fiber := LineDeriv.lineDerivOpCLM ℝ Fiber (axes i)
private def lapCLM : Fiber →L[ℝ] Fiber := ∑ i, (line i).comp (line i)

private theorem lap_apply (u : Fiber) (y : Spatial) : lap u y = lapCLM u y := by
  simp only [lap, lapCLM, sum_apply]
  rfl

private def pair : ℂ →L[ℝ] ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.mul ℝ ℂ).comp Complex.conjCLE.toContinuousLinearMap

private theorem pair_int (u v : Fiber) : Integrable (fun y => star (u y) * v y) :=
  ScalarFiberPairing.integrable_pair (u.memLp 2 volume) (v.memLp 2 volume)

private theorem by_parts (u v : Fiber) (i : Fin 3) :
    (∫ y, star (u y) * line i v y) = -(∫ y, star (line i u y) * v y) :=
  SchwartzMap.integral_bilinear_lineDerivOp_right_eq_neg_left u v pair (axes i)

/-- The full Cartesian Laplacian is symmetric under the actual remote integral. -/
theorem lap_green (u v : Fiber) :
    (∫ y, star (lap u y) * v y) = ∫ y, star (u y) * lap v y := by
  have hl (u : Fiber) (y : Spatial) : lap u y = ∑ i, line i (line i u) y := rfl
  simp only [hl, star_sum, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => pair_int (line i (line i u)) v),
    integral_finsetSum _ (fun i _ => pair_int u (line i (line i v)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [by_parts u (line i v) i, by_parts (line i u) v i, neg_neg]

private theorem bracket (h m : ℝ) (V : Spatial → ℝ) (u v : Fiber) (y : Spatial) :
    star (one h m V u y) * v y - star (u y) * one h m V v y =
      -((h^2 / (2*m) : ℝ) : ℂ) * (star (lap u y)*v y - star (u y)*lap v y) := by
  simp only [one, star_add, star_mul, star_neg, Complex.star_def, Complex.conj_ofReal]
  ring

/-- The difference of the two Hamiltonian pairings is integrable even without
any boundedness or integrability condition on the common real potential. -/
theorem integrable_commutator (h m : ℝ) (V : Spatial → ℝ) (u v : Fiber) :
    Integrable (fun y => star (one h m V u y) * v y - star (u y) * one h m V v y) := by
  simp_rw [bracket, lap_apply]
  exact ((pair_int (lapCLM u) v).sub (pair_int u (lapCLM v))).const_mul _

/-- The second particle's literal Schrödinger Hamiltonian contributes zero
to the integrated commutator of any two remote Schwartz fibers. -/
theorem integral_commutator_zero (h m : ℝ) (V : Spatial → ℝ) (u v : Fiber) :
    (∫ y, star (one h m V u y) * v y - star (u y) * one h m V v y) = 0 := by
  simp_rw [bracket]
  have h₁ : Integrable (fun y => star (lap u y)*v y) := by
    simp_rw [lap_apply]; exact pair_int (lapCLM u) v
  have h₂ : Integrable (fun y => star (u y)*lap v y) := by
    simp_rw [lap_apply]; exact pair_int u (lapCLM v)
  rw [integral_const_mul, integral_sub h₁ h₂, lap_green, sub_self, mul_zero]

/-- A retained derivative passes through the differential Hamiltonian acting
on the remote variable, including its arbitrary real multiplication potential. -/
theorem retained_fderiv_one {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (h m : ℝ) (V : Spatial → ℝ) (S : X → Fiber) {x : X} (hS : DifferentiableAt ℝ S x)
    (v : X) (y : Spatial) :
    fderiv ℝ (fun z => one h m V (S z) y) x v = one h m V (fderiv ℝ S x v) y := by
  let ev := (BoundedContinuousFunction.evalCLM ℝ y).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℝ Spatial ℂ)
  have hL := hasFDerivAt_image (ev.comp lapCLM) hS.hasFDerivAt
  have hE := hasFDerivAt_image ev hS.hasFDerivAt
  have hd := (hL.const_mul (-((h^2/(2*m):ℝ):ℂ))).add (hE.const_mul (V y : ℂ))
  simp_rw [one, lap_apply]
  exact congrArg (fun A : X →L[ℝ] ℂ => A v) hd.fderiv

/-- The scalar overlap integral for the two remote fibers. -/
def overlap (u v : Fiber) : ℂ := ∫ y, star (u y) * v y

private theorem hilbert_overlap (u v : Fiber) :
    inner ℂ (u.toLp 2 volume) (v.toLp 2 volume) = overlap u v :=
  ScalarFiberPairing.inner_toLp (u.memLp 2 volume) (v.memLp 2 volume)

private theorem time_toLp {U : ℝ → Fiber} {u : Fiber} {t : ℝ} (hU : HasDerivAt U u t) :
    HasDerivAt (fun s => (U s).toLp 2 volume) (u.toLp 2 volume) t := by
  have he := (hasFDerivAt_image (SchwartzMap.toLpCLM ℝ ℂ 2 volume) hU.hasFDerivAt).hasDerivAt
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    one_smul, SchwartzMap.toLpCLM_apply] using he

/-- Differentiation of the scalar overlap along two strongly differentiable
Schwartz paths includes the two independently differentiated fibers. -/
theorem overlap_derivative {U W : ℝ → Fiber} {u w : Fiber} {t : ℝ}
    (hU : HasDerivAt U u t) (hW : HasDerivAt W w t) :
    HasDerivAt (fun s => overlap (U s) (W s)) (overlap (U t) w + overlap u (W t)) t := by
  have hd := (time_toLp hU).inner ℂ (time_toLp hW)
  simpa only [hilbert_overlap] using hd

/-- The complex velocity generated by the remote differential Hamiltonian. -/
def velocity (h m : ℝ) (V : Spatial → ℝ) (u : Fiber) (y : Spatial) : ℂ :=
  (-Complex.I / (h : ℂ)) * one h m V u y

private theorem skew (h : ℝ) : star (-Complex.I / (h : ℂ)) = -(-Complex.I / (h : ℂ)) := by
  simp [neg_div]

/-- The literal remote Schrödinger velocities make cancelling contributions to
the physical overlap derivative. The other two velocity components remain. -/
theorem overlap_cancellation (h m : ℝ) (V : Spatial → ℝ) {U W : ℝ → Fiber}
    {u w : Fiber} {t : ℝ} (hU : HasDerivAt U u t) (hW : HasDerivAt W w t) (a b : Fiber)
    (hu : ∀ y, u y = a y + velocity h m V (U t) y)
    (hw : ∀ y, w y = b y + velocity h m V (W t) y) :
    HasDerivAt (fun s => overlap (U s) (W s)) (overlap (U t) b + overlap a (W t)) t := by
  apply (overlap_derivative hU hW).congr_deriv
  let q := -Complex.I / (h : ℂ)
  have he (y : Spatial) : star (U t y) * w y + star (u y) * W t y =
      (star (U t y) * b y + star (a y) * W t y) +
        (-q) * (star (one h m V (U t) y) * W t y - star (U t y) * one h m V (W t) y) := by
    rw [hu, hw]
    simp only [velocity, star_add, star_mul, skew, q]
    ring
  unfold overlap
  rw [← integral_add (pair_int (U t) w) (pair_int u (W t))]
  simp_rw [he]
  have hab : Integrable (fun y => star (U t y) * b y + star (a y)* W t y) :=
    (pair_int (U t) b).add (pair_int a (W t))
  rw [integral_add hab ((integrable_commutator h m V (U t) (W t)).const_mul (-q)),
    integral_const_mul, integral_commutator_zero, mul_zero, add_zero,
    integral_add (pair_int (U t) b) (pair_int a (W t))]

/-- The scalar Born mass integrated over the remote particle. -/
def density (u : Fiber) : ℝ := ∫ y, ‖u y‖^2

/-- The integrated density derivative has only the retained velocity on its right side. -/
theorem density_cancellation (h m : ℝ) (V : Spatial → ℝ) {U : ℝ → Fiber} {u : Fiber} {t : ℝ}
    (hU : HasDerivAt U u t) (a : Fiber) (hu : ∀ y, u y = a y + velocity h m V (U t) y) :
    HasDerivAt (fun s => density (U s)) (2 * (overlap (U t) a).re) t := by
  have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (overlap_cancellation h m V hU hU a a hu hu)
  have hn (f : Fiber) : (overlap f f).re = density f := by
    rw [← hilbert_overlap]
    exact (norm_sq_eq_re_inner (𝕜 := ℂ) (f.toLp 2 volume)).symm.trans
      (ScalarFiberPairing.norm_sq_toLp (f.memLp 2 volume))
  have hc : (overlap a (U t)).re = (overlap (U t) a).re := by
    rw [← hilbert_overlap, ← hilbert_overlap]
    simpa only [Complex.conj_re] using
      congrArg Complex.re (inner_conj_symm (𝕜 := ℂ) ((U t).toLp 2 volume) (a.toLp 2 volume))
  simpa only [Function.comp_def, Complex.reCLM_apply, hn, Complex.add_re, hc, two_mul] using hd

/-- When the second path is the actual retained derivative, the physical
marginal current has no contribution from the remote Hamiltonian. -/
theorem current_cancellation (h m₁ m₂ : ℝ) (V : Spatial → ℝ) (S : ℝ → Spatial → Fiber)
    {t : ℝ} (x d : Spatial) (hS : ∀ s, DifferentiableAt ℝ (S s) x) {u w : Fiber}
    (hU : HasDerivAt (fun s => S s x) u t)
    (hW : HasDerivAt (fun s => fderiv ℝ (S s) x d) w t) (a b : Fiber)
    (hu : ∀ y, u y = a y + velocity h m₂ V (S t x) y)
    (hw : ∀ y, w y = b y + velocity h m₂ V (fderiv ℝ (S t) x d) y) :
    HasDerivAt (fun s => (h/m₁) * ∫ y,
      (star (S s x y) * fderiv ℝ (fun z => S s z y) x d).im)
      ((h/m₁) * (overlap (S t x) b + overlap a (fderiv ℝ (S t) x d)).im) t := by
  have hd := (Complex.imCLM.hasFDerivAt.comp_hasDerivAt t
    (overlap_cancellation h m₂ V hU hW a b hu hw)).const_mul (h/m₁)
  have he (s : ℝ) : (overlap (S s x) (fderiv ℝ (S s) x d)).im =
      ∫ y, (star (S s x y) * fderiv ℝ (fun z => S s z y) x d).im := by
    simp only [overlap, fderiv_eval (S s) (hS s)]
    exact (integral_im (pair_int _ _)).symm
  simpa only [Function.comp_def, Complex.imCLM_apply, he] using hd

private theorem eval_time {U : ℝ → Fiber} {u : Fiber} {t : ℝ}
    (hU : HasDerivAt U u t) (y : Spatial) : HasDerivAt (fun s => U s y) (u y) t := by
  let T := (BoundedContinuousFunction.evalCLM ℝ y).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℝ Spatial ℂ)
  have he := (hasFDerivAt_image T hU.hasFDerivAt).hasDerivAt
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    one_smul] using! he

private theorem mixed (F : ℝ × Spatial → ℂ) (hf : ContDiff ℝ 2 F) (t : ℝ) (x d : Spatial) :
    deriv (fun s => fderiv ℝ (fun z => F (s,z)) x d) t =
      fderiv ℝ (fun z => deriv (fun s => F (s,z)) t) x d := by
  have hF := hf.differentiable (by norm_num)
  have ht (z : Spatial) : deriv (fun s => F (s,z)) t = fderiv ℝ F (t,z) (1,0) := by
    have H := ((hF (t,z)).hasFDerivAt.comp t (hasFDerivAt_prodMk_left (𝕜 := ℝ) t z)).hasDerivAt
    exact H.deriv
  have hx (s : ℝ) : fderiv ℝ (fun z => F (s,z)) x d = fderiv ℝ F (s,x) (0,d) :=
    congrArg (fun D : Spatial →L[ℝ] ℂ => D d)
      ((hF (s,x)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right s x)).fderiv
  let p := (t,x)
  have hD : DifferentiableAt ℝ (fderiv ℝ F) p :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) p
  have ha (v : ℝ × Spatial) : HasFDerivAt (fun q => fderiv ℝ F q v)
      ((ContinuousLinearMap.apply ℝ ℂ v).comp (fderiv ℝ (fderiv ℝ F) p)) p :=
    (ContinuousLinearMap.apply ℝ ℂ v).hasFDerivAt.comp p hD.hasFDerivAt
  simp_rw [ht, hx]
  change deriv ((fun q => fderiv ℝ F q (0,d)) ∘ fun s => (s,x)) t =
    fderiv ℝ ((fun q => fderiv ℝ F q (1,0)) ∘ fun z => (t,z)) x d
  rw [((ha (0,d)).comp t (hasFDerivAt_prodMk_left t x)).hasDerivAt.deriv,
    ((ha (1,0)).comp x (hasFDerivAt_prodMk_right t x)).fderiv]
  exact hf.contDiffAt.isSymmSndFDerivAt (by norm_num) (1,0) (0,d)

/-- One local scalar evolution equation implies both cancellations. Strong
time differentiability of the fiber and its retained derivative permits passage
to the remote integral. Ordinary scalar C² regularity identifies the two
mixed derivatives, so the differentiated Schrödinger equation follows from
the original equation on a retained neighborhood. -/
theorem observable_derivatives_of_local_equation (h m₁ m₂ : ℝ) (V : Spatial → ℝ)
    (S : ℝ → Spatial → Fiber) (t : ℝ) (x d : Spatial) (T A : Spatial → Fiber)
    (hS : ∀ s, DifferentiableAt ℝ (S s) x)
    (hreg : ∀ y, ContDiff ℝ 2 (fun p : ℝ × Spatial => S p.1 p.2 y))
    (hT : ∀ᶠ z in 𝓝 x, HasDerivAt (fun s => S s z) (T z) t)
    {w : Fiber} (hW : HasDerivAt (fun s => fderiv ℝ (S s) x d) w t)
    (hA : DifferentiableAt ℝ A x)
    (heq : ∀ᶠ z in 𝓝 x, ∀ y, T z y = A z y + velocity h m₂ V (S t z) y) :
    HasDerivAt (fun s => density (S s x)) (2 * (overlap (S t x) (A x)).re) t ∧
      HasDerivAt (fun s => (h/m₁) * ∫ y,
        (star (S s x y) * fderiv ℝ (fun z => S s z y) x d).im)
        ((h/m₁) * (overlap (S t x) (fderiv ℝ A x d) +
          overlap (A x) (fderiv ℝ (S t) x d)).im) t := by
  refine ⟨density_cancellation h m₂ V hT.self_of_nhds (A x) heq.self_of_nhds, ?_⟩
  apply current_cancellation h m₁ m₂ V S x d hS hT.self_of_nhds hW
    (A x) (fderiv ℝ A x d) heq.self_of_nhds
  intro y
  have h₁ : (fun s => fderiv ℝ (fun z => S s z y) x d) =
      (fun s => (fderiv ℝ (S s) x d) y) := funext fun s => fderiv_eval (S s) (hS s) y d
  have h₂ : (fun z => deriv (fun s => S s z y) t) =ᶠ[𝓝 x]
      (fun z => A z y + velocity h m₂ V (S t z) y) := by
    filter_upwards [hT, heq] with z hz he
    exact ((eval_time hz y).deriv).trans (he y)
  let ev := (BoundedContinuousFunction.evalCLM ℝ y).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℝ Spatial ℂ)
  let q := -Complex.I / (h : ℂ)
  have hbase : HasFDerivAt (fun z => A z y) (ev.comp (fderiv ℝ A x)) x :=
    hasFDerivAt_image ev hA.hasFDerivAt
  have hlap := hasFDerivAt_image (ev.comp lapCLM) (hS t).hasFDerivAt
  have hpot := hasFDerivAt_image ev (hS t).hasFDerivAt
  have hH := (hlap.const_mul (-((h^2/(2*m₂):ℝ):ℂ))).add (hpot.const_mul (V y : ℂ))
  have hH' : DifferentiableAt ℝ (fun z => one h m₂ V (S t z) y) x := by
    simp_rw [one, lap_apply]
    exact hH.differentiableAt
  calc
    _ = deriv (fun s => (fderiv ℝ (S s) x d) y) t := (eval_time hW y).deriv.symm
    _ = deriv (fun s => fderiv ℝ (fun z => S s z y) x d) t := by rw [h₁]
    _ = fderiv ℝ (fun z => deriv (fun s => S s z y) t) x d :=
      mixed (fun p => S p.1 p.2 y) (hreg y) t x d
    _ = _ := by
      rw [h₂.fderiv_eq]
      change fderiv ℝ (fun z => A z y + q * one h m₂ V (S t z) y) x d =
        (fderiv ℝ A x d) y + q * one h m₂ V (fderiv ℝ (S t) x d) y
      rw [(hbase.fun_add (hH'.hasFDerivAt.const_mul q)).fderiv]
      exact congrArg (((fderiv ℝ A x d) y) + q * ·) (retained_fderiv_one h m₂ V (S t) (hS t) d y)

/-- The retained differential velocity, formed by differentiating the
Schwartz-valued wave in the first particle's three Cartesian directions. -/
def retainedVelocity (h m : ℝ) (V : Spatial → ℝ) (S : Spatial → Fiber) (x : Spatial) : Fiber :=
  (-Complex.I / (h : ℂ)) •
    (-((h^2/(2*m):ℝ):ℂ) • (∑ i, fderiv ℝ (fun z => fderiv ℝ S z (axes i)) x (axes i)) +
      (V x : ℂ) • S x)

/-- Evaluating the retained Schwartz velocity gives the literal one-body
scalar Schrödinger differential expression at each remote position. -/
theorem retainedVelocity_apply (h m : ℝ) (V : Spatial → ℝ) (S : Spatial → Fiber)
    (hS : Differentiable ℝ S) (hD : ∀ i, Differentiable ℝ (fun z => fderiv ℝ S z (axes i)))
    (x y : Spatial) :
    retainedVelocity h m V S x y = (-Complex.I / (h : ℂ)) * one h m V (fun z => S z y) x := by
  have hs (i : Fin 3) (z : Spatial) :
      fderiv ℝ (fun w => S w y) z (axes i) = (fderiv ℝ S z (axes i)) y :=
    fderiv_eval S (hS z) y (axes i)
  simp only [retainedVelocity, one, lap, hs, fun i => fderiv_eval _ (hD i x) y (axes i),
    smul_apply, add_apply, sum_apply, smul_eq_mul]

/-- For the two-particle Schrödinger equation with local potentials, both
observable derivatives contain just the explicit retained Hamiltonian and its
retained derivative. All Schwartz differentiability hypotheses concern the
wave or that explicit retained velocity. The sole evolution hypothesis is the
original undifferentiated joint equation near the retained position. -/
theorem observable_derivatives_of_joint (h m₁ m₂ : ℝ) (hh : h ≠ 0) (V₁ V₂ : Spatial → ℝ)
    (S : ℝ → Spatial → Fiber) (t : ℝ) (x d : Spatial) (T : Spatial → Fiber)
    (hS : ∀ s, DifferentiableAt ℝ (S s) x)
    (hS₁ : Differentiable ℝ (S t))
    (hS₂ : ∀ i, Differentiable ℝ (fun z => fderiv ℝ (S t) z (axes i)))
    (hreg : ∀ y, ContDiff ℝ 2 (fun p : ℝ × Spatial => S p.1 p.2 y))
    (hT : ∀ᶠ z in 𝓝 x, HasDerivAt (fun s => S s z) (T z) t)
    {w : Fiber} (hW : HasDerivAt (fun s => fderiv ℝ (S s) x d) w t)
    (hA : DifferentiableAt ℝ (retainedVelocity h m₁ V₁ (S t)) x)
    (hpde : ∀ᶠ z in 𝓝 x, ∀ y, Complex.I * (h : ℂ) * deriv (fun s => S s z y) t =
      joint h m₁ m₂ V₁ V₂ (fun p => S t p.1 p.2) (z,y)) :
    HasDerivAt (fun s => density (S s x))
      (2 * (overlap (S t x) (retainedVelocity h m₁ V₁ (S t) x)).re) t ∧
    HasDerivAt (fun s => (h/m₁) * ∫ y, (star (S s x y) * fderiv ℝ (fun z => S s z y) x d).im)
      ((h/m₁) * (overlap (S t x) (fderiv ℝ (retainedVelocity h m₁ V₁ (S t)) x d) +
        overlap (retainedVelocity h m₁ V₁ (S t) x) (fderiv ℝ (S t) x d)).im) t := by
  apply observable_derivatives_of_local_equation h m₁ m₂ V₂ S t x d T _ hS hreg hT hW hA
  filter_upwards [hpde, hT] with z hz ht
  intro y
  have split : joint h m₁ m₂ V₁ V₂ (fun p => S t p.1 p.2) (z,y) =
      one h m₁ V₁ (fun r => S t r y) z + one h m₂ V₂ (S t z) y := by
    simp only [joint, one, Complex.ofReal_add]
    ring
  have he := hz y
  rw [(eval_time ht y).deriv, split] at he
  rw [retainedVelocity_apply h m₁ V₁ (S t) hS₁ hS₂]
  unfold velocity
  rw [← mul_add, ← he]
  have hn : (h : ℂ) ≠ 0 := by exact_mod_cast hh
  field_simp
  simp [Complex.I_sq]

end FoliationQM.TwoBodyRemoteHamiltonian
