module

public import FoliationQM.LiouvilleDifferential
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Actual Hamilton–Jacobi section pullback and the proper-time clock

Source: v13 `thm:contact_period` part (i), especially the Hamilton–Jacobi
pullback following the restricted Reeb calculation. Momentum is defined from
the actual Frechet derivative of a scalar phase, and its section is actually
differentiated under local C2 hypotheses. The pulled-back Liouville form is
proved equal to the actual exterior derivative of the scalar zero-form.

The exactness result holds for any sufficiently smooth phase. Membership in
the future mass shell is a separate consequence of the eikonal and time-
orientation conditions. With momentum equal to mass times the lowered proper
velocity, the exact phase clock agrees with the normalized Minkowski proper-
time form. No periodic clock postulate or non-squeezing result is assumed here.
-/

@[expose] public section

noncomputable section
namespace FoliationQM.HamiltonJacobiPullback
open ContactReeb
open scoped BigOperators

/-- A scalar phase regarded as an actual alternating zero-form. -/
def scalarForm (S : Covector → ℝ) (x : Covector) : Covector [⋀^Fin 0]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.constOfIsEmpty ℝ Covector (Fin 0) (S x)
/-- The genuine exterior derivative of the scalar phase zero-form. -/
def phaseDifferential (S : Covector → ℝ) (x : Covector) : Covector [⋀^Fin 1]→L[ℝ] ℝ :=
  extDeriv (scalarForm S) x

/-- The actual phase differential evaluates as the Frechet derivative of the phase. -/
theorem phaseDifferential_apply (S : Covector → ℝ) (x : Covector) (v : Fin 1 → Covector) :
    phaseDifferential S x v = fderiv ℝ S x (v 0) := by
  change extDeriv (fun x => ContinuousAlternatingMap.constOfIsEmpty ℝ Covector (Fin 0) (S x)) x v = _
  rw [extDeriv_constOfIsEmpty]
  rfl

/-- Local C2 regularity of the scalar phase gives C2 regularity of its zero-form. -/
theorem contDiffAt_scalarForm {S : Covector → ℝ} {x : Covector} (hS : ContDiffAt ℝ 2 S x) :
    ContDiffAt ℝ 2 (scalarForm S) x := by
  exact (ContinuousAlternatingMap.constOfIsEmptyLIE ℝ Covector ℝ (Fin 0)).contDiff.contDiffAt.comp x hS

/-- The actual phase differential is closed by the exterior-derivative square-zero theorem. -/
theorem extDeriv_phaseDifferential_zero {S : Covector → ℝ} {x : Covector}
    (hS : ContDiffAt ℝ 2 S x) : extDeriv (phaseDifferential S) x = 0 :=
  extDeriv_extDeriv_apply (contDiffAt_scalarForm hS) (by simp)

/-- Lower momentum components obtained from the actual phase derivative with the source minus sign. -/
def momentum (S : Covector → ℝ) (x : Covector) : Covector :=
  fun i => -(fderiv ℝ S x) (Pi.single i 1)
/-- The Hamilton–Jacobi graph in flat cotangent space, using the actual phase derivative. -/
def sectionMap (S : Covector → ℝ) (x : Covector) : Ambient := (x, momentum S x)

/-- Projection of the Hamilton–Jacobi section to spacetime is the identity. -/
theorem sectionMap_fst (S : Covector → ℝ) (x : Covector) : (sectionMap S x).1 = x := rfl

/-- The Hamilton–Jacobi section is injective because its base projection is the identity. -/
theorem sectionMap_injective (S : Covector → ℝ) : Function.Injective (sectionMap S) := by
  intro x y h
  exact congrArg Prod.fst h

/-- The basis expansion of the actual phase derivative identifies its negative with the momentum pairing. -/
theorem momentum_pairing (S : Covector → ℝ) (x v : Covector) :
    pairing (momentum S x) v = -(fderiv ℝ S x v) := by
  have hv : ∑ i : Fin 4, v i • Pi.single i (1 : ℝ) = v := by
    ext j
    simp [Pi.single_apply]
  conv_rhs => rw [← hv]
  simp [pairing, momentum, mul_comm, Finset.sum_neg_distrib]

/-- A locally C2 phase has a differentiable momentum field. -/
theorem differentiableAt_momentum {S : Covector → ℝ} {x : Covector}
    (hS : ContDiffAt ℝ 2 S x) : DifferentiableAt ℝ (momentum S) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ S) x :=
    (hS.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  apply differentiableAt_pi.mpr
  intro i
  exact (hd.clm_apply (differentiableAt_const (Pi.single i 1))).neg

/-- A smooth phase has a smooth momentum field. -/
theorem contDiffAt_momentum {S : Covector → ℝ} {x : Covector}
    (hS : ContDiffAt ℝ (⊤ : ℕ∞) S x) :
    ContDiffAt ℝ (⊤ : ℕ∞) (momentum S) x := by
  have hd := hS.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  apply contDiffAt_pi.mpr
  intro i
  exact (hd.clm_apply contDiffAt_const).neg

/-- The actual Hamilton–Jacobi section is smooth wherever the phase is smooth. -/
theorem contDiffAt_sectionMap {S : Covector → ℝ} {x : Covector}
    (hS : ContDiffAt ℝ (⊤ : ℕ∞) S x) :
    ContDiffAt ℝ (⊤ : ℕ∞) (sectionMap S) x :=
  contDiffAt_id.prodMk (contDiffAt_momentum hS)

/-- The actual section derivative has identity base component and the actual momentum derivative. -/
theorem hasFDerivAt_sectionMap {S : Covector → ℝ} {x : Covector}
    (hS : ContDiffAt ℝ 2 S x) :
    HasFDerivAt (sectionMap S)
      ((ContinuousLinearMap.id ℝ Covector).prod (fderiv ℝ (momentum S) x)) x :=
  (hasFDerivAt_id x).prodMk (differentiableAt_momentum hS).hasFDerivAt

/-- Identify the actual Frechet derivative of the Hamilton–Jacobi section. -/
theorem fderiv_sectionMap {S : Covector → ℝ} {x : Covector}
    (hS : ContDiffAt ℝ 2 S x) :
    fderiv ℝ (sectionMap S) x =
      (ContinuousLinearMap.id ℝ Covector).prod (fderiv ℝ (momentum S) x) :=
  (hasFDerivAt_sectionMap hS).fderiv

/-- The actual Liouville form pulled back by the actual derivative of the phase section. -/
def pullback (S : Covector → ℝ) (x : Covector) : Covector [⋀^Fin 1]→L[ℝ] ℝ :=
  (LiouvilleDifferential.liouville (sectionMap S x)).compContinuousLinearMap
    (fderiv ℝ (sectionMap S) x)

/-- The genuine Liouville pullback along the phase section is exactly the actual differential dS. -/
theorem pullback_eq_phaseDifferential {S : Covector → ℝ} {x : Covector}
    (hS : ContDiffAt ℝ 2 S x) : pullback S x = phaseDifferential S x := by
  ext v
  change LiouvilleDifferential.liouville (sectionMap S x)
    (fun i => fderiv ℝ (sectionMap S) x (v i)) = _
  rw [LiouvilleDifferential.liouville_apply, phaseDifferential_apply, fderiv_sectionMap hS]
  change -(pairing (momentum S x) (v 0)) = _
  rw [momentum_pairing, neg_neg]

/-- Each actual momentum derivative component is the corresponding negative phase Hessian component. -/
theorem fderiv_momentum_apply {S : Covector → ℝ} {x : Covector}
    (hS : ContDiffAt ℝ 2 S x) (v : Covector) (i : Fin 4) :
    fderiv ℝ (momentum S) x v i =
      -(fderiv ℝ (fderiv ℝ S) x v (Pi.single i 1)) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ S) x :=
    (hS.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hi := (hd.hasFDerivAt.clm_apply (hasFDerivAt_const (Pi.single i 1) x)).neg
  have hp := (differentiableAt_momentum hS).hasFDerivAt
  have hpi := (ContinuousLinearMap.proj i : Covector →L[ℝ] ℝ).hasFDerivAt.comp x hp
  have heq := hi.unique hpi
  have hv := congrArg (fun f : Covector →L[ℝ] ℝ => f v) heq
  simpa using hv.symm

/-- The actual section derivative consists of the input vector and the negative phase Hessian components. -/
theorem fderiv_sectionMap_apply {S : Covector → ℝ} {x : Covector}
    (hS : ContDiffAt ℝ 2 S x) (v : Covector) :
    fderiv ℝ (sectionMap S) x v =
      (v, fun i => -(fderiv ℝ (fderiv ℝ S) x v (Pi.single i 1))) := by
  rw [fderiv_sectionMap hS]
  apply Prod.ext
  · rfl
  · funext i
    exact fderiv_momentum_apply hS v i

/-- On an open domain, a C2 phase gives equality of the actual Liouville pullback and dS everywhere. -/
theorem pullback_eq_phaseDifferential_on {S : Covector → ℝ} {U : Set Covector}
    (hU : IsOpen U) (hS : ContDiffOn ℝ 2 S U) : Set.EqOn (pullback S) (phaseDifferential S) U := by
  intro x hx
  exact pullback_eq_phaseDifferential (hS.contDiffAt (hU.mem_nhds hx))

/-- The actual Hamilton–Jacobi pullback is closed under local C2 phase regularity. -/
theorem extDeriv_pullback_zero {S : Covector → ℝ} {x : Covector}
    (hS : ContDiffAt ℝ 2 S x) : extDeriv (pullback S) x = 0 := by
  have heq : pullback S =ᶠ[nhds x] phaseDifferential S :=
    (hS.eventually (by norm_num)).mono (fun _ h => pullback_eq_phaseDifferential h)
  rw [heq.extDeriv_eq]
  exact extDeriv_phaseDifferential_zero hS

/-- The phase-clock one-form is minus the actual phase differential divided by mass times c squared. -/
def clockForm (S : Covector → ℝ) (m c : ℝ) (x : Covector) : Covector [⋀^Fin 1]→L[ℝ] ℝ :=
  (-(m*c^2)⁻¹) • phaseDifferential S x

/-- Evaluate the clock one-form as the scaled actual scalar derivative. -/
theorem clockForm_apply (S : Covector → ℝ) (m c : ℝ) (x : Covector) (v : Fin 1 → Covector) :
    clockForm S m c x v = -(fderiv ℝ S x (v 0))/(m*c^2) := by
  simp [clockForm, phaseDifferential_apply, div_eq_mul_inv]
  ring

/-- The source clock form is minus the actual Liouville section pullback divided by mass times c squared. -/
theorem clockForm_eq_scaled_pullback {S : Covector → ℝ} {x : Covector}
    (hS : ContDiffAt ℝ 2 S x) (m c : ℝ) :
    clockForm S m c x = (-(m*c^2)⁻¹) • pullback S x := by
  rw [pullback_eq_phaseDifferential hS]
  rfl

/-- The phase clock is the genuine exterior derivative of the scalar clock phase −S/(mc²). -/
theorem clockForm_exact (S : Covector → ℝ) (m c : ℝ) (x : Covector) :
    clockForm S m c x = extDeriv (scalarForm (fun y => -(S y)/(m*c^2))) x := by
  have heq : scalarForm (fun y => -(S y)/(m*c^2)) = (-(m*c^2)⁻¹) • scalarForm S := by
    funext y
    ext v
    simp [scalarForm, div_eq_mul_inv]
    ring
  rw [heq, extDeriv_smul]
  rfl

/-- The actual phase graph lies in the future mass shell when its momentum satisfies the eikonal and future conditions. -/
theorem sectionMap_onShell {S : Covector → ℝ} {m c : ℝ} {x : Covector}
    (heikonal : minkowski (momentum S x) (momentum S x) = m^2*c^2)
    (hfuture : 0 < momentum S x 0) : OnShell m c (sectionMap S x).2 :=
  ⟨heikonal,hfuture⟩

/-- The physical proper-time one-form obtained by lowering a raised velocity using Minkowski signature and dividing by c squared. -/
def properTimeForm (c : ℝ) (u : Covector) : Covector [⋀^Fin 1]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.ofSubsingleton ℝ Covector ℝ (0 : Fin 1)
    ((c^2)⁻¹ • ∑ i : Fin 4, sharp u i • ContinuousLinearMap.proj i)

/-- The physical proper-time form evaluates to the Minkowski velocity pairing divided by c squared. -/
theorem properTimeForm_apply (c : ℝ) (u : Covector) (v : Fin 1 → Covector) :
    properTimeForm c u v = minkowski u (v 0) / c^2 := by
  change ((c^2)⁻¹ • ∑ i : Fin 4, sharp u i • ContinuousLinearMap.proj i) (v 0) = _
  simp only [smul_apply, sum_apply, smul_eq_mul,
    ContinuousLinearMap.proj_apply]
  rw [← pairing, pairing_sharp_left]
  ring

/-- When actual phase momentum is mass times lowered proper velocity, the phase clock equals the proper-time form. -/
theorem clockForm_eq_properTimeForm {S : Covector → ℝ} {m c : ℝ} {x u : Covector}
    (hm : 0 < m) (hSu : momentum S x = m • sharp u) :
    clockForm S m c x = properTimeForm c u := by
  ext v
  rw [clockForm_apply, properTimeForm_apply]
  have hp := momentum_pairing S x (v 0)
  rw [hSu, pairing_smul_left, pairing_sharp_left] at hp
  rw [← hp]
  field_simp

/-- A normalized future velocity related to the actual phase momentum puts the phase section on the future shell. -/
theorem sectionMap_onShell_of_velocity {S : Covector → ℝ} {m c : ℝ} {x u : Covector}
    (hm : 0 < m) (hSu : momentum S x = m • sharp u)
    (hu : minkowski u u = c^2) (hfuture : 0 < u 0) :
    OnShell m c (sectionMap S x).2 := by
  apply sectionMap_onShell
  · rw [hSu]
    calc
      minkowski (m • sharp u) (m • sharp u) = m^2 * minkowski u u := by
        simp [minkowski, sharp]
        ring
      _ = m^2*c^2 := by rw [hu]
  · rw [hSu]
    simpa [sharp] using mul_pos hm hfuture

/-- The physical proper-time form evaluates to one on a normalized future-speed velocity. -/
theorem properTimeForm_velocity {c : ℝ} {u : Covector} (hc : 0 < c)
    (hu : minkowski u u = c^2) : properTimeForm c u (fun _ => u) = 1 := by
  rw [properTimeForm_apply, hu]
  exact div_self (pow_ne_zero _ hc.ne')

/-- The source Hamilton–Jacobi section simultaneously satisfies the future-shell, exact-pullback, and physical-clock identities. -/
theorem hamiltonJacobi_clock_bridge {S : Covector → ℝ} {m c : ℝ} {x u : Covector}
    (hS : ContDiffAt ℝ 2 S x) (hm : 0 < m)
    (hSu : momentum S x = m • sharp u)
    (hu : minkowski u u = c^2) (hfuture : 0 < u 0) :
    OnShell m c (sectionMap S x).2 ∧
      pullback S x = phaseDifferential S x ∧
      clockForm S m c x = properTimeForm c u :=
  ⟨sectionMap_onShell_of_velocity hm hSu hu hfuture,
    pullback_eq_phaseDifferential hS, clockForm_eq_properTimeForm hm hSu⟩

/-- The continuous linear derivative of an affine constant-momentum phase. -/
def affineDerivative (p : Covector) : Covector →L[ℝ] ℝ :=
  ∑ i : Fin 4, (-p i) • ContinuousLinearMap.proj i

/-- An affine scalar phase with prescribed constant lower momentum. -/
def affinePhase (p : Covector) (k : ℝ) (x : Covector) : ℝ := k + affineDerivative p x

/-- The affine example has the source action form k minus the momentum-position pairing. -/
theorem affinePhase_eq (p : Covector) (k : ℝ) (x : Covector) :
    affinePhase p k x = k - pairing p x := by
  simp [affinePhase, affineDerivative, pairing, sub_eq_add_neg]

/-- The affine constant-momentum phase is smooth. -/
theorem contDiff_affinePhase (p : Covector) (k : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (affinePhase p k) :=
  contDiff_const.add (affineDerivative p).contDiff

/-- The affine phase has its displayed actual Frechet derivative. -/
theorem hasFDerivAt_affinePhase (p : Covector) (k : ℝ) (x : Covector) :
    HasFDerivAt (affinePhase p k) (affineDerivative p) x :=
  (affineDerivative p).hasFDerivAt.const_add k

/-- Differentiating the affine example recovers exactly its prescribed momentum. -/
theorem momentum_affinePhase (p : Covector) (k : ℝ) (x : Covector) :
    momentum (affinePhase p k) x = p := by
  ext i
  rw [momentum, (hasFDerivAt_affinePhase p k x).fderiv]
  simp [affineDerivative, Pi.single_apply]

/-- Every future-shell constant momentum gives an actual affine Hamilton–Jacobi section of that shell. -/
theorem affine_section_onShell {p : Covector} {m c : ℝ} (hp : OnShell m c p)
    (k : ℝ) (x : Covector) : OnShell m c (sectionMap (affinePhase p k) x).2 := by
  change OnShell m c (momentum (affinePhase p k) x)
  rwa [momentum_affinePhase]

/-- Positive mass and speed provide a concrete nonvacuous affine rest-momentum shell section. -/
theorem rest_affine_section_onShell {m c : ℝ} (hm : 0 < m) (hc : 0 < c)
    (k : ℝ) (x : Covector) :
    OnShell m c (sectionMap (affinePhase ![m*c,0,0,0] k) x).2 := by
  apply affine_section_onShell
  constructor
  · simp [minkowski]
    ring
  · exact mul_pos hm hc

end FoliationQM.HamiltonJacobiPullback
