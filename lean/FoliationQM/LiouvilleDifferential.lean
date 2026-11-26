module

public import FoliationQM.ContactReeb
public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Tactic.NormNum

/-!
# The actual Liouville exterior differential and restricted Reeb equations

Source: v13 `thm:contact_period`, the Liouville form and restricted Reeb
calculation in its first part. The field is a genuine continuous alternating
one-form. Actual Frechet differentiation and Mathlib's actual exterior
derivative yield the canonical two-form. The final theorems combine this
analytic calculation with the proved linearized-shell Reeb characterization.
The shell chart, seven-form contact volume, and global contact manifold
interpretation are separate constructions; no ambient vanishing of the
Reeb contraction is claimed.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.LiouvilleDifferential
open ContactReeb
open scoped BigOperators

/-- The actual continuous linear coordinate differential dx^i on flat cotangent space. -/
def positionCoordinate (i : Fin 4) : Ambient →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ Covector Covector)
/-- The actual continuous linear coordinate differential dp_i on flat cotangent space. -/
def momentumCoordinate (i : Fin 4) : Ambient →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ Covector Covector)
/-- The position coordinate differential bundled as a genuine continuous alternating one-form. -/
def coordinateForm (i : Fin 4) : Ambient [⋀^Fin 1]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.ofSubsingleton ℝ Ambient ℝ (0 : Fin 1) (positionCoordinate i)
/-- The Liouville one-form field with the source sign, minus lower momentum paired with position. -/
def liouville (z : Ambient) : Ambient [⋀^Fin 1]→L[ℝ] ℝ :=
  ∑ i : Fin 4, (-z.2 i) • coordinateForm i

/-- The position differential evaluates the corresponding position component. -/
theorem positionCoordinate_apply (i : Fin 4) (z : Ambient) : positionCoordinate i z = z.1 i := rfl
/-- The momentum differential evaluates the corresponding momentum component. -/
theorem momentumCoordinate_apply (i : Fin 4) (z : Ambient) : momentumCoordinate i z = z.2 i := rfl
/-- The bundled one-form evaluates the actual position coordinate. -/
theorem coordinateForm_apply (i : Fin 4) (v : Fin 1 → Ambient) : coordinateForm i v = (v 0).1 i := rfl

/-- The actual bundled Liouville form agrees with the source coordinate contraction. -/
theorem liouville_apply (z : Ambient) (v : Fin 1 → Ambient) : liouville z v = alpha z (v 0) := by
  simp [liouville, ContinuousAlternatingMap.sum_apply, coordinateForm_apply,
    alpha, pairing, Finset.sum_neg_distrib, neg_mul]

/-- The dependence of the Liouville form on the phase-space point is an actual continuous linear map. -/
def liouvilleLinear : Ambient →L[ℝ] (Ambient [⋀^Fin 1]→L[ℝ] ℝ) :=
  ∑ i : Fin 4, (momentumCoordinate i).smulRight (-coordinateForm i)

/-- The bundled continuous linear dependence equals the defined Liouville field. -/
theorem liouvilleLinear_apply (z : Ambient) : liouvilleLinear z = liouville z := by
  simp only [liouvilleLinear, sum_apply,
    ContinuousLinearMap.smulRight_apply, momentumCoordinate_apply, liouville]
  apply Finset.sum_congr rfl
  intro i _
  exact (smul_neg (z.2 i) (coordinateForm i)).trans (neg_smul (z.2 i) (coordinateForm i)).symm

/-- The Liouville field has its actual continuous linear derivative at every point. -/
theorem hasFDerivAt_liouville (z : Ambient) :
    HasFDerivAt liouville liouvilleLinear z := by
  have he : liouville = liouvilleLinear := funext fun y => (liouvilleLinear_apply y).symm
  rw [he]
  exact liouvilleLinear.hasFDerivAt

/-- The actual Frechet derivative of the Liouville one-form field is its linear coefficient map. -/
theorem fderiv_liouville (z : Ambient) : fderiv ℝ liouville z = liouvilleLinear :=
  (hasFDerivAt_liouville z).fderiv

/-- The actual Liouville differential-form field is smooth on flat cotangent space. -/
theorem contDiff_liouville : ContDiff ℝ (⊤ : ℕ∞) liouville := by
  unfold liouville
  apply ContDiff.sum
  intro i _
  exact ((momentumCoordinate i).contDiff.neg).smul contDiff_const

/-- The genuine continuous linear derivative of Liouville evaluation on a fixed vector. -/
def evaluationDerivative (v : Ambient) : Ambient →L[ℝ] ℝ :=
  ∑ i : Fin 4, (-v.1 i) • momentumCoordinate i

/-- Fixed-vector derivative evaluation retains the negative lower-momentum pairing. -/
theorem evaluationDerivative_apply (v z : Ambient) :
    evaluationDerivative v z = alpha z v := by
  simp [evaluationDerivative, momentumCoordinate_apply, alpha, pairing,
    mul_comm, neg_mul, Finset.sum_neg_distrib]

/-- Evaluation on a fixed one-vector has the proved actual Frechet derivative. -/
theorem hasFDerivAt_liouville_eval (z : Ambient) (v : Fin 1 → Ambient) :
    HasFDerivAt (fun y => liouville y v) (evaluationDerivative (v 0)) z := by
  have he : (fun y => liouville y v) = evaluationDerivative (v 0) := by
    funext y
    rw [liouville_apply, evaluationDerivative_apply]
  rw [he]
  exact (evaluationDerivative (v 0)).hasFDerivAt

/-- The actual derivative of a fixed evaluation is the explicit coordinate derivative. -/
theorem fderiv_liouville_eval (z : Ambient) (v : Fin 1 → Ambient) :
    fderiv ℝ (fun y => liouville y v) z = evaluationDerivative (v 0) :=
  (hasFDerivAt_liouville_eval z v).fderiv

/-- The genuine Mathlib exterior derivative of the Liouville field equals dx^mu wedge dp_mu on every pair. -/
theorem extDeriv_liouville_apply (z : Ambient) (v : Fin 2 → Ambient) :
    extDeriv liouville z v = canonicalTwo (v 0) (v 1) := by
  rw [extDeriv_apply (contDiff_liouville.differentiable (by norm_num) z)]
  simp only [fderiv_liouville_eval, evaluationDerivative_apply]
  simp [Fin.removeNth, alpha, canonicalTwo, pairing, Fin.sum_univ_succ]; ring

/-- The canonical two-form as the actual exterior derivative of Liouville at the origin. -/
def canonicalForm : Ambient [⋀^Fin 2]→L[ℝ] ℝ := extDeriv liouville 0

/-- The actual canonical alternating two-form has the standard coordinate evaluation. -/
theorem canonicalForm_apply (v : Fin 2 → Ambient) :
    canonicalForm v = canonicalTwo (v 0) (v 1) :=
  extDeriv_liouville_apply 0 v

/-- The actual exterior derivative is the same canonical two-form at every phase-space point. -/
theorem extDeriv_liouville (z : Ambient) : extDeriv liouville z = canonicalForm := by
  ext v
  rw [extDeriv_liouville_apply, canonicalForm_apply]

/-- The canonical two-form is nonzero, as witnessed by one conjugate coordinate pair. -/
theorem canonicalForm_ne_zero : canonicalForm ≠ 0 := by
  intro h
  have hval := congrArg (fun T : Ambient [⋀^Fin 2]→L[ℝ] ℝ =>
    T ![(Pi.single 0 1, 0), (0, Pi.single 0 1)]) h
  norm_num [canonicalForm_apply, canonicalTwo, pairing, Fin.sum_univ_succ, Pi.single_apply] at hval

/-- The actual ambient exterior derivative of Liouville is nonzero everywhere. -/
theorem extDeriv_liouville_ne_zero (z : Ambient) : extDeriv liouville z ≠ 0 := by
  rw [extDeriv_liouville]
  exact canonicalForm_ne_zero

/-- The actual exterior derivative is a smooth constant two-form field. -/
theorem contDiff_extDeriv_liouville : ContDiff ℝ (⊤ : ℕ∞) (extDeriv liouville) := by
  have he : extDeriv liouville = fun _ => canonicalForm := funext extDeriv_liouville
  rw [he]
  exact contDiff_const

/-- The actual second exterior derivative of the smooth Liouville field vanishes. -/
theorem second_extDeriv_liouville : extDeriv (extDeriv liouville) = 0 := by
  exact extDeriv_extDeriv contDiff_liouville (by simp)

/-- The actual Liouville form normalizes the proposed Reeb direction to one
on the massive positive-energy shell. -/
theorem liouville_reeb_eq_one {m c : ℝ} (hm : 0 < m) (hc : 0 < c)
    {z : Ambient} (hs : OnShell m c z.2) :
    liouville z (fun _ => reeb m c z.2) = 1 := by
  rw [liouville_apply]
  exact alpha_reeb_eq_one hm hc hs

/-- The actual exterior differential annihilates the Reeb direction only
after restricting the other argument to the linearized mass shell. -/
theorem extDeriv_liouville_reeb_tangent (z : Ambient) (m c : ℝ) (v : Ambient)
    (hv : Tangent z.2 v) :
    extDeriv liouville z ![reeb m c z.2, v] = 0 := by
  rw [extDeriv_liouville_apply]
  exact canonicalTwo_reeb_tangent m c z.2 v hv

/-- The actual Liouville one-form and its actual exterior derivative
characterize the unique source Reeb vector on the constrained massive shell. -/
theorem actual_reeb_characterization {m c : ℝ} (hm : 0 < m) (hc : 0 < c)
    {z w : Ambient} (hs : OnShell m c z.2) :
    (liouville z (fun _ => w) = 1 ∧
      ∀ v : Ambient, Tangent z.2 v → extDeriv liouville z ![w, v] = 0) ↔
        w = reeb m c z.2 := by
  simp only [liouville_apply, extDeriv_liouville_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  exact reeb_characterization hm hc hs

end FoliationQM.LiouvilleDifferential
