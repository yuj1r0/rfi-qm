module
public import FoliationQM.SpinLorentzOrientation
public import FoliationQM.SpinLorentzCentralizer
/-!
# The exact two-sign kernel of the actual physical Lorentz action

Source scope: the concrete spin-frame sign ambiguity in v13 `prop:takabayasi`
and `eq:tetrad_rotor_map`. Identity physical action first implies an actual
unitary representative by evaluating the proved Pauli sandwich on the time
basis vector. Cancelling this genuine inverse gives commutation with all
Pauli vector matrices. The independently checked finite centralizer and the
actual determinant-one constraint then force precisely the two sign matrices.

The central negative identity is an explicit, nontrivial special linear group
element. Kernel and fiber statements concern the existing homomorphism into
the independently defined proper future Lorentz group and the actual physical
matrices. No target is defined by its represented image. Surjectivity, quotient
covering structure, and identification with an abstract Clifford spin group
are not asserted here.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator Matrix
namespace FoliationQM.SpinLorentzKernel
open SpinorMatrix SourcePolarDatum SpecialLinearGroupManifold
open SpinLorentzAction SpinLorentzOrientation LorentzMatrixGroup

/-- The nontrivial central sign representative is the actual negative identity matrix. -/
def negativeOne : SpecialLinearMatrix :=
  ⟨-(1 : Mat2), by norm_num [Matrix.det_fin_two]⟩

/-- The central sign element has exactly the negative identity as its matrix. -/
@[simp]
theorem negativeOne_val : negativeOne.val = -(1 : Mat2) := rfl

/-- The two central sign representatives are genuinely distinct. -/
theorem negativeOne_ne_one : negativeOne ≠ 1 := by
  intro h
  have he := congrArg (fun A : SpecialLinearMatrix => A.val 0 0) h
  norm_num [negativeOne] at he

/-- Multiplication by the central sign representative negates the actual matrix. -/
@[simp]
theorem negativeOne_mul_val (A : SpecialLinearMatrix) :
    (negativeOne * A).val = -A.val := by simp

/-- The actual sign representative is central in the special linear group. -/
theorem negativeOne_central (A : SpecialLinearMatrix) :
    negativeOne * A = A * negativeOne := by
  apply Subtype.ext
  simp

/-- The nontrivial central sign representative squares to the identity. -/
@[simp]
theorem negativeOne_sq : negativeOne * negativeOne = 1 := by
  apply Subtype.ext
  simp

/-- Equality of actual proper-future images is exactly equality of their physical matrices. -/
theorem properFutureHom_eq_iff_matrix (A B : SpecialLinearMatrix) :
    properFutureHom A = properFutureHom B ↔ lorentzMatrix A.val = lorentzMatrix B.val := by
  constructor
  · intro h
    exact congrArg (fun L : ProperFutureLorentz => matrix L.val) h
  · intro h
    apply Subtype.ext
    apply matrix_injective
    exact h

/-- The nontrivial sign representative maps to the actual Lorentz identity. -/
@[simp]
theorem properFutureHom_negativeOne : properFutureHom negativeOne = 1 := by
  rw [← properFutureHom.map_one, properFutureHom_eq_iff_matrix]
  exact lorentzMatrix_neg 1

open SpinLorentzPauli SpinLorentzCentralizer

/-- A trivial actual physical action forces the representative to be unitary, by testing the genuine Pauli sandwich on the time basis vector. -/
theorem kernel_unitary (A : Mat2) (hA : A.det = 1) (hker : lorentzMatrix A = 1) :
    A * A.conjTranspose = 1 := by
  have h := pauli_sandwich A hA (Pi.single 0 1)
  simpa only [hker, Matrix.one_mulVec, pauli_zero_basis, mul_one] using h

/-- A trivial actual physical action forces commutation with every actual Pauli vector matrix, using the derived conjugate-transpose inverse. -/
theorem kernel_commute_pauli (A : Mat2) (hA : A.det = 1)
    (hker : lorentzMatrix A = 1) (v : FoliationQM.Covector) : Commute A (pauli v) := by
  have h0 : A.conjTranspose * A = 1 := mul_eq_one_comm.mp (kernel_unitary A hA hker)
  have hX := pauli_sandwich A hA v
  rw [hker, Matrix.one_mulVec] at hX
  change A * pauli v = pauli v * A
  have h := congrArg (fun M : Mat2 => M * A) hX
  simpa only [mul_assoc, h0, mul_one] using h

/-- The actual physical Lorentz matrix is the identity exactly for the two scalar sign matrices; the converse and necessity use genuine matrix equations. -/
theorem matrix_kernel_iff (A : Mat2) (hA : A.det = 1) :
    lorentzMatrix A = 1 ↔ A = 1 ∨ A = -(1 : Mat2) := by
  constructor
  · intro hker
    exact eq_one_or_neg_one_of_commute_pauli A
      (kernel_commute_pauli A hA hker (Pi.single 3 1))
      (kernel_commute_pauli A hA hker (Pi.single 1 1)) hA
  · rintro (rfl | rfl)
    · exact lorentzMatrix_one
    · rw [lorentzMatrix_neg, lorentzMatrix_one]

/-- The genuine homomorphism into the independent proper future Lorentz group has exactly identity and negative identity in its kernel. -/
theorem properFutureHom_eq_one_iff (A : SpecialLinearMatrix) :
    properFutureHom A = 1 ↔ A = 1 ∨ A = negativeOne := by
  have hm : properFutureHom A = 1 ↔ lorentzMatrix A.val = 1 := by
    simpa only [map_one, coe_one, lorentzMatrix_one] using properFutureHom_eq_iff_matrix A 1
  rw [hm, matrix_kernel_iff A.val A.property]
  constructor
  · rintro (h | h)
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- Two actual special linear representatives induce the same proper future Lorentz transformation exactly when they differ by the single central sign. -/
theorem properFutureHom_eq_iff (A B : SpecialLinearMatrix) :
    properFutureHom A = properFutureHom B ↔ A = B ∨ A = negativeOne * B := by
  constructor
  · intro h
    have he : properFutureHom (A * B⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
    rcases (properFutureHom_eq_one_iff (A * B⁻¹)).mp he with he | he
    · left
      have hh := congrArg (fun C : SpecialLinearMatrix => C * B) he
      simpa only [mul_assoc, inv_mul_cancel, mul_one, one_mul] using hh
    · right
      have hh := congrArg (fun C : SpecialLinearMatrix => C * B) he
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh
  · rintro (rfl | rfl)
    · rfl
    · simp

/-- The complete physical-matrix fiber criterion is literal equality or matrix negation for determinant-one inputs. -/
theorem lorentzMatrix_eq_iff (A B : Mat2) (hA : A.det = 1) (hB : B.det = 1) :
    lorentzMatrix A = lorentzMatrix B ↔ A = B ∨ A = -B := by
  rw [← properFutureHom_eq_iff_matrix ⟨A, hA⟩ ⟨B, hB⟩, properFutureHom_eq_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl (congrArg Subtype.val h)
    · right
      simpa only [negativeOne_mul_val] using congrArg Subtype.val h
  · rintro (h | h)
    · exact Or.inl (Subtype.ext h)
    · right
      apply Subtype.ext
      simpa only [negativeOne_mul_val] using h

end FoliationQM.SpinLorentzKernel
