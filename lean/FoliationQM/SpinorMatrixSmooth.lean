module
public import FoliationQM.SpecialLinearSpin
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.InnerProductSpace.Calculus
/-!
# Actual smoothness of the concrete spinor matrix model

Sources: the regular polar reconstruction in v13 `prop:takabayasi`,
`eq:takabayasi_polar`, and the actual scalar-pseudoscalar density in
`eq:scalar_pseudoscalar_bilinears`. The real-linear coordinate equivalence
and its inverse are smooth. The actual two-by-two determinant is a
polynomial in continuous real-linear coordinate evaluations. Its norm is
the already proved invariant density, so the density is smooth on the
strict regular domain, where this determinant does not vanish.

The explicit four-by-four representative of a two-by-two matrix is also
proved real-linear and packaged as a continuous-linear map, making its
smoothness available without a determinant-one premise. All matrix
calculus uses the existing operator norm. No smooth real phase on the
entire regular domain or abstract spin-group classification is asserted.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
namespace FoliationQM.SpinorMatrixSmooth
open DiracMatrices SpinorMatrix SpinorRegularity SpecialLinearSpin

/-- The actual real-linear spinor-to-matrix encoding is smooth to every order. -/
theorem contDiff_toMatrix (n : WithTop ℕ∞) : ContDiff ℝ n toMatrix :=
  continuousLinearEquiv.contDiff

/-- The actual inverse matrix-to-spinor coordinates are smooth to every order. -/
theorem contDiff_ofMatrix (n : WithTop ℕ∞) : ContDiff ℝ n ofMatrix :=
  continuousLinearEquiv.symm.contDiff

private def entryCLM (i j : Fin 2) : Mat2 →L[ℝ] ℂ :=
  ({ toFun := fun M => M i j
     map_add' := by intros; rfl
     map_smul' := by intros; rfl } : Mat2 →ₗ[ℝ] ℂ).toContinuousLinearMap

private theorem contDiff_entry (n : WithTop ℕ∞) (i j : Fin 2) :
    ContDiff ℝ n (fun M : Mat2 => M i j) := (entryCLM i j).contDiff

/-- The actual complex two-by-two determinant is real-smooth to every order as its explicit coordinate polynomial. -/
theorem contDiff_det (n : WithTop ℕ∞) : ContDiff ℝ n (Matrix.det : Mat2 → ℂ) := by
  have h := ((contDiff_entry n 0 0).mul (contDiff_entry n 1 1)).sub
    ((contDiff_entry n 0 1).mul (contDiff_entry n 1 0))
  convert! h using 1
  ext M
  exact Matrix.det_fin_two M

/-- The actual determinant of the encoded spinor is real-smooth to every order on the entire spinor space. -/
theorem contDiff_spinorDet (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun psi : Spinor => Matrix.det (toMatrix psi)) :=
  (contDiff_det n).comp (contDiff_toMatrix n)

/-- At every strictly regular spinor, the actual invariant density is smooth because its determinant is nonzero. -/
theorem contDiffAt_invariantDensity (n : WithTop ℕ∞) {psi : Spinor} (hpsi : Regular psi) :
    ContDiffAt ℝ n invariantDensity psi := by
  have h := (contDiff_spinorDet n).contDiffAt.norm ℝ
    ((det_ne_zero_iff_regular psi).mpr hpsi)
  simpa only [norm_det_toMatrix] using h

/-- The actual scalar-pseudoscalar invariant density is smooth on the source strict regular domain. -/
theorem contDiffOn_invariantDensity (n : WithTop ℕ∞) :
    ContDiffOn ℝ n invariantDensity {psi | Regular psi} :=
  fun _ hpsi => (contDiffAt_invariantDensity n hpsi).contDiffWithinAt

/-- The explicit four-by-four spin representative preserves addition of actual two-by-two matrices. -/
theorem spin_add (A B : Mat2) : spin (A+B) = spin A + spin B := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spin, weylDual] <;> ring

/-- The explicit spin representative preserves real scalar multiplication, with its complex conjugations retained. -/
theorem spin_real_smul (r : ℝ) (A : Mat2) : spin (r • A) = r • spin A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spin, weylDual] <;> ring

/-- The actual explicit spin representative as a real continuous-linear map between matrix spaces. -/
def spinCLM : Mat2 →L[ℝ] Mat :=
  ({ toFun := spin
     map_add' := spin_add
     map_smul' := spin_real_smul } : Mat2 →ₗ[ℝ] Mat).toContinuousLinearMap

/-- The continuous-linear representative evaluates to the actual four-by-four spin matrix. -/
theorem spinCLM_apply (A : Mat2) : spinCLM A = spin A := rfl

/-- The actual explicit spin representative is real-smooth to every order on all two-by-two matrix inputs. -/
theorem contDiff_spin (n : WithTop ℕ∞) : ContDiff ℝ n spin := spinCLM.contDiff

end FoliationQM.SpinorMatrixSmooth
