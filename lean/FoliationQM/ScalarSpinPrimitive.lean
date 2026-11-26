module
public import FoliationQM.ScalarSpinDefect
public import FoliationQM.SpecialLinearCurvature
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare

/-!
# Phase primitives of the physical spin connection

For the irrotational condition in v13 `thm:dirac_lift`, the spin-axis form
of a C² determinant-one matrix field has a phase potential on a convex open
domain precisely when its actual scalar curvature vanishes there. On any
open domain with this property, every point has a ball carrying a potential.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator Topology
namespace FoliationQM.ScalarSpinPrimitive
open Set Filter DiracFieldDensity SpinorMatrix SpecialLinearConnection LorentzConnectionCurvature

variable (p : MassiveParameters) {A : Covector → Mat2} {U : Set Covector} {x : Covector}

/-- The continuous linear spin-axis one-form at a point of the original matrix field. -/
def oneForm (A : Covector → Mat2) (x : Covector) : Covector →L[ℝ] ℝ :=
  ({ toFun := spinConnection p.hbar (bodyOmega A) x
     map_add' := by
       intro v w
       simp [spinConnection, bodyOmega_add, mul_add]
     map_smul' := by
       intro r v
       simp [spinConnection, bodyOmega_smul, smul_eq_mul]
       ring } : Covector →ₗ[ℝ] ℝ).toContinuousLinearMap

/-- The packaged one-form evaluates to the physical scalar connection in every direction. -/
theorem oneForm_apply (A : Covector → Mat2) (x v : Covector) :
    oneForm p A x v = spinConnection p.hbar (bodyOmega A) x v := rfl

private theorem coordinate_expansion (A : Covector → Mat2) (x : Covector) :
    oneForm p A x = ∑ μ, (oneForm p A x (coordinateDirections μ)) •
      (ContinuousLinearMap.proj μ : Covector →L[ℝ] ℝ) := by
  ext v
  calc
    oneForm p A x v = ∑ μ, v μ • (oneForm p A x (coordinateDirections μ)) := by
      conv_lhs => rw [pi_eq_sum_univ' v]
      rw [map_sum]
      simp [coordinateDirections]
    _ = _ := by simp [Fin.sum_univ_four, mul_comm, smul_eq_mul]

/-- The physical one-form loses one derivative from the C² rotor and is C¹ at a determinant-one point. -/
theorem contDiffAt_oneForm (hA : ContDiffAt ℝ 2 A x) (hd : (A x).det = 1) :
    ContDiffAt ℝ 1 (oneForm p A) x := by
  have hu : IsUnit (A x) := (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [hd]; exact isUnit_one)
  have hinv : ContDiffAt ℝ 1 (fun M : Mat2 => M⁻¹) (A x) := by
    rcases hu with ⟨u, hu⟩
    rw [← hu]
    simpa only [Matrix.nonsing_inv_eq_ringInverse] using (contDiffAt_ringInverse (n := 1) ℝ u)
  have hbody (v : Covector) : ContDiffAt ℝ 1 (fun y => bodyOmega A y v) x := by
    apply SpecialLinearLieAlgebra.omegaCLM.contDiff.contDiffAt.comp x
    exact (hinv.comp x (hA.of_le (by norm_num))).mul
      ((hA.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const)
  have h (μ : Fin 4) : ContDiffAt ℝ 1 (fun y => oneForm p A y (coordinateDirections μ)) x :=
    contDiffAt_const.mul (contDiffAt_pi.mp (contDiffAt_pi.mp (hbody _) 1) 2)
  have he : oneForm p A = fun y => ∑ μ, (oneForm p A y (coordinateDirections μ)) •
      (ContinuousLinearMap.proj μ : Covector →L[ℝ] ℝ) := funext (coordinate_expansion p A)
  rw [he]
  exact ContDiffAt.sum (fun μ _ => (h μ).smul contDiffAt_const)

/-- C² matrix regularity and determinant one at the point make the actual form differentiable. -/
theorem differentiableAt_oneForm (hA : ContDiffAt ℝ 2 A x) (hd : (A x).det = 1) :
    DifferentiableAt ℝ (oneForm p A) x := (contDiffAt_oneForm p hA hd).differentiableAt_one

/-- The signed scalar curvature contraction of the body Maurer–Cartan coefficients. -/
def curvature (A : Covector → Mat2) (x v w : Covector) : ℝ :=
  ∑ k, RealLorentzFrame.sign k *
    (bodyOmega A x v 1 k * bodyOmega A x w k 2 - bodyOmega A x w 1 k * bodyOmega A x v k 2)

/-- Irrotationality means vanishing of the physical curvature contraction throughout the domain. -/
def FlatOn (A : Covector → Mat2) (U : Set Covector) : Prop :=
  ∀ x ∈ U, ∀ v w, curvature A x v w = 0

/-- The antisymmetric Fréchet derivative of the actual one-form is its half-ℏ curvature. -/
theorem alternatingDerivative_eq (hA : ContDiffAt ℝ 2 A x) (hd : ∀ᶠ y in 𝓝 x, (A y).det = 1)
    (v w : Covector) :
    fderiv ℝ (oneForm p A) x v w - fderiv ℝ (oneForm p A) x w v = p.hbar / 2 * curvature A x v w := by
  have he (u a : Covector) :
      fderiv ℝ (fun y => spinConnection p.hbar (bodyOmega A) y u) x a = fderiv ℝ (oneForm p A) x a u := by
    have h := ((differentiableAt_oneForm p hA hd.self_of_nhds).hasFDerivAt.clm_apply (hasFDerivAt_const u x))
    change fderiv ℝ (fun y => oneForm p A y u) x a = _
    rw [h.fderiv]
    simp
  simpa only [he, curvature] using SpecialLinearCurvature.spinConnection_curvature hA hd p.hbar v w

/-- Comparing the primitive's differential with the physical form identifies all four scalar phase components. -/
theorem connection_eq_gradient {S : Covector → ℝ} (hs : HasFDerivAt S (oneForm p A x) x) :
    ScalarSpinDefect.connection p A x = ScalarSpinDefect.gradient S x := by
  funext μ
  change spinConnection p.hbar (bodyOmega A) x (coordinateDirections μ) = fderiv ℝ S x (coordinateDirections μ)
  rw [hs.fderiv]
  rfl

/-- A flat C² determinant-one field on a convex open region has a single real potential for its spin one-form there. -/
theorem exists_primitive (hU : IsOpen U) (hconv : Convex ℝ U)
    (hA : ∀ y ∈ U, ContDiffAt ℝ 2 A y) (hd : ∀ y ∈ U, (A y).det = 1) (hf : FlatOn A U) :
    ∃ S : Covector → ℝ, ∀ y ∈ U, HasFDerivAt S (oneForm p A y) y := by
  apply hconv.exists_forall_hasFDerivAt_of_fderiv_symmetric hU
  · exact fun y hy => (differentiableAt_oneForm p (hA y hy) (hd y hy)).differentiableWithinAt
  · intro y hy v w
    have he := alternatingDerivative_eq p (hA y hy) (Filter.mem_of_superset (hU.mem_nhds hy) hd) v w
    simpa [hf y hy v w, sub_eq_zero] using he

/-- A potential with the true spin one-form as derivative is C² throughout the given open domain. -/
theorem contDiffAt_primitive (hU : IsOpen U) (hA : ContDiffAt ℝ 2 A x) (hd : (A x).det = 1)
    {S : Covector → ℝ} (hs : ∀ y ∈ U, HasFDerivAt S (oneForm p A y) y) (hx : x ∈ U) :
    ContDiffAt ℝ 2 S x := by
  apply (contDiffAt_succ_iff_hasFDerivAt (n := 1)).mpr
  exact ⟨oneForm p A, ⟨U, hU.mem_nhds hx, hs⟩, contDiffAt_oneForm p hA hd⟩

/-- Any true primitive of the spin connection forces its scalar curvature to vanish on an open region. -/
theorem flatOn_of_primitive (hU : IsOpen U) (hA : ∀ y ∈ U, ContDiffAt ℝ 2 A y)
    (hd : ∀ y ∈ U, (A y).det = 1) {S : Covector → ℝ}
    (hs : ∀ y ∈ U, HasFDerivAt S (oneForm p A y) y) : FlatOn A U := by
  intro y hy v w
  have hh := second_derivative_symmetric_of_eventually_of_real
    (Filter.mem_of_superset (hU.mem_nhds hy) hs)
    (differentiableAt_oneForm p (hA y hy) (hd y hy)).hasFDerivAt v w
  have he := alternatingDerivative_eq p (hA y hy) (Filter.mem_of_superset (hU.mem_nhds hy) hd) v w
  rw [hh, sub_self, eq_comm, mul_eq_zero] at he
  exact he.resolve_left (div_ne_zero p.hbar_pos.ne' (by norm_num))

/-- On arbitrary open regions flatness gives a genuine potential on a ball around each point. -/
theorem exists_primitive_ball (hU : IsOpen U) (hA : ∀ y ∈ U, ContDiffAt ℝ 2 A y)
    (hd : ∀ y ∈ U, (A y).det = 1) (hf : FlatOn A U) (hx : x ∈ U) :
    ∃ r > 0, Metric.ball x r ⊆ U ∧ ∃ S : Covector → ℝ,
      ∀ y ∈ Metric.ball x r, HasFDerivAt S (oneForm p A y) y := by
  obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.mp hU x hx
  exact ⟨r, hr, hb, exists_primitive p Metric.isOpen_ball (convex_ball x r)
    (fun y hy => hA y (hb hy)) (fun y hy => hd y (hb hy)) (fun y hy => hf y (hb hy))⟩

end FoliationQM.ScalarSpinPrimitive
