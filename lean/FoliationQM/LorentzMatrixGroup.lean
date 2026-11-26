module
public import FoliationQM.SpecialLinearFrameLaws
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Group.Subgroup

/-!
# Independent Lorentz matrix groups in the source signature

Source: the Lorentz-frame claim of v13 `prop:takabayasi`. The target is
specified independently of the concrete two-by-two spin representation:
real invertible four-by-four matrices preserving the explicit (+---)
metric. The proper future subgroup additionally preserves determinant one
and the actual future timelike cone. No matrix-image characterization,
spin covering, or existence of a spin lift is assumed in these definitions.

All groups retain the natural matrix-unit and subgroup topologies. The
metric-signed transpose inverse and both metric identities are proved
from the independent metric equation, not from a supplied frame expansion.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
namespace FoliationQM.LorentzMatrixGroup
open DiracMatrices RealLorentzFrame Matrix

/-- The ambient real matrix space for the independent four-dimensional Lorentz target. -/
abbrev Mat4 := Matrix (Fin 4) (Fin 4) ℝ

/-- The source Minkowski metric in its fixed (+---) ordered coordinate basis. -/
def eta : Mat4 := Matrix.diagonal sign

/-- The fixed metric matrix is symmetric. -/
theorem eta_transpose : eta.transpose = eta := Matrix.diagonal_transpose _

/-- Raising and lowering twice is the identity in the source signature. -/
theorem eta_sq : eta * eta = 1 := by
  rw [eta, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst j
    simp [sign_sq]
  · simp [h]

/-- The determinant of the fixed Minkowski metric is minus one. -/
theorem eta_det : eta.det = -1 := by
  norm_num [eta, Matrix.det_diagonal, Fin.prod_univ_succ, sign]

/-- Independent metric preservation forces the signed transpose to be a left inverse. -/
theorem signedTranspose_mul_of_metric (M : Mat4) (hM : M.transpose * eta * M = eta) :
    (eta * M.transpose * eta) * M = 1 := by
  calc
    _ = eta * (M.transpose * eta * M) := by noncomm_ring
    _ = eta * eta := by rw [hM]
    _ = 1 := eta_sq

/-- The independent Lorentz metric equation implies actual matrix invertibility. -/
theorem isUnit_of_metric (M : Mat4) (hM : M.transpose * eta * M = eta) : IsUnit M := by
  have hl := signedTranspose_mul_of_metric M hM
  exact ⟨⟨M, eta * M.transpose * eta, mul_eq_one_comm.mp hl, hl⟩, rfl⟩

/-- The actual matrix inverse of an independently specified Lorentz matrix is its metric-signed transpose. -/
theorem inverse_formula_of_metric (M : Mat4) (hM : M.transpose * eta * M = eta) :
    M⁻¹ = eta * M.transpose * eta :=
  Matrix.inv_eq_left_inv (signedTranspose_mul_of_metric M hM)

/-- Independent column metric preservation also gives the row metric identity. -/
theorem metric_rows_of_metric (M : Mat4) (hM : M.transpose * eta * M = eta) :
    M * eta * M.transpose = eta := by
  have hr := mul_eq_one_comm.mp (signedTranspose_mul_of_metric M hM)
  have he := congrArg (fun X : Mat4 => X * eta) hr
  simpa only [Matrix.mul_assoc, eta_sq, Matrix.mul_one, Matrix.one_mul] using he

/-- Every independently metric-preserving real matrix has determinant square one. -/
theorem det_sq_of_metric (M : Mat4) (hM : M.transpose * eta * M = eta) : M.det ^ 2 = 1 := by
  have hd := congrArg Matrix.det hM
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, eta_det] at hd
  nlinarith

/-- The explicitly defined Minkowski form is the ordinary coordinate dot product with the fixed metric acting on the second vector. -/
theorem minkowski_eq_dot_eta (v w : Covector) : minkowski v w = dotProduct v (eta *ᵥ w) := by
  simp [minkowski, eta, dotProduct, Matrix.mulVec, Fin.sum_univ_succ, sign]
  ring

/-- The independent matrix metric equation preserves the actual Minkowski bilinear form on all vector pairs. -/
theorem minkowski_mulVec_of_metric (M : Mat4) (hM : M.transpose * eta * M = eta)
    (v w : Covector) : minkowski (M *ᵥ v) (M *ᵥ w) = minkowski v w := by
  rw [minkowski_eq_dot_eta, minkowski_eq_dot_eta]
  calc
    _ = dotProduct v (M.transpose *ᵥ (eta *ᵥ (M *ᵥ w))) := by
      rw [Matrix.dotProduct_transpose_mulVec]
      exact dotProduct_comm _ _
    _ = dotProduct v (eta *ᵥ w) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM]

/-- The full Lorentz group is the independently defined metric-preserving subgroup of real matrix units. -/
def lorentzGroup : Subgroup Mat4ˣ where
  carrier := {u | (u.val).transpose * eta * u.val = eta}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change (a.val * b.val).transpose * eta * (a.val * b.val) = eta
    rw [Matrix.transpose_mul]
    calc
      _ = b.val.transpose * (a.val.transpose * eta * a.val) * b.val := by noncomm_ring
      _ = eta := by rw [ha, hb]
  inv_mem' := by
    intro a ha
    change (a⁻¹).val.transpose * eta * (a⁻¹).val = eta
    have hl : (a⁻¹).val.transpose * a.val.transpose = 1 := by
      rw [← Matrix.transpose_mul]
      simp
    calc
      _ = (a⁻¹).val.transpose * (a.val.transpose * eta * a.val) * (a⁻¹).val := by rw [ha]
      _ = ((a⁻¹).val.transpose * a.val.transpose) * eta * (a.val * (a⁻¹).val) := by noncomm_ring
      _ = eta := by rw [hl]; simp

/-- The full Lorentz group with its inherited matrix-unit group operations and topology. -/
abbrev Lorentz := lorentzGroup

/-- The actual real matrix underlying a Lorentz group element. -/
def matrix (L : Lorentz) : Mat4 := L.val.val

/-- The identity Lorentz element has the actual identity matrix. -/
theorem matrix_one : matrix 1 = 1 := rfl

/-- Lorentz group multiplication is the actual ordered real matrix product. -/
theorem matrix_mul (L K : Lorentz) : matrix (L * K) = matrix L * matrix K := rfl

/-- Every independently defined Lorentz element satisfies the exact source metric equation. -/
theorem metric (L : Lorentz) : (matrix L).transpose * eta * matrix L = eta := L.property

/-- The actual underlying matrix uniquely determines a Lorentz element. -/
theorem matrix_injective : Function.Injective matrix := by
  intro L K h
  apply Subtype.ext
  exact Units.ext h

/-- The group inverse has exactly the actual nonsingular matrix inverse. -/
theorem matrix_inv (L : Lorentz) : matrix L⁻¹ = (matrix L)⁻¹ := by
  have hl : matrix L⁻¹ * matrix L = 1 := by rw [← matrix_mul]; simp [matrix_one]
  exact (Matrix.inv_eq_left_inv hl).symm

/-- The underlying-matrix map is continuous for the natural subgroup and matrix-unit topologies. -/
theorem continuous_matrix : Continuous matrix :=
  Units.continuous_val.comp continuous_subtype_val

/-- The future timelike cone is defined by the actual source time coordinate and strictly positive Minkowski square. -/
def futureCone (v : Covector) : Prop := 0 < v 0 ∧ 0 < minkowski v v

/-- A real matrix preserves the actual future timelike cone in both directions of its action. -/
def preservesFutureCone (M : Mat4) : Prop :=
  ∀ v : Covector, futureCone (M *ᵥ v) ↔ futureCone v

/-- The actual identity matrix preserves the future timelike cone. -/
theorem preservesFutureCone_one : preservesFutureCone (1 : Mat4) := by
  intro v
  simp

/-- Actual cone preservation is closed under the ordered matrix product. -/
theorem preservesFutureCone_mul {M N : Mat4} (hM : preservesFutureCone M)
    (hN : preservesFutureCone N) : preservesFutureCone (M * N) := by
  intro v
  rw [← Matrix.mulVec_mulVec]
  exact (hM (N *ᵥ v)).trans (hN v)

/-- Cone preservation of an invertible matrix gives cone preservation of its actual inverse unit. -/
theorem preservesFutureCone_inv (u : Mat4ˣ) (hu : preservesFutureCone u.val) :
    preservesFutureCone (u⁻¹).val := by
  intro v
  have h := hu ((u⁻¹).val *ᵥ v)
  simpa only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] using h.symm

/-- The independent proper future Lorentz subgroup combines determinant one with actual future-timelike-cone preservation. -/
def properFutureGroup : Subgroup Lorentz where
  carrier := {L | (matrix L).det = 1 ∧ preservesFutureCone (matrix L)}
  one_mem' := by simpa [matrix_one] using And.intro (Matrix.det_one (n := Fin 4) (R := ℝ)) preservesFutureCone_one
  mul_mem' := by
    intro L K hL hK
    change (matrix (L * K)).det = 1 ∧ preservesFutureCone (matrix (L * K))
    rw [matrix_mul]
    exact ⟨by rw [Matrix.det_mul, hL.1, hK.1, one_mul], preservesFutureCone_mul hL.2 hK.2⟩
  inv_mem' := by
    intro L hL
    constructor
    · rw [matrix_inv, Matrix.det_nonsing_inv, hL.1]
      simp
    · exact preservesFutureCone_inv L.val hL.2

/-- The proper future Lorentz group is a subgroup specified independently of any spin representation. -/
abbrev ProperFutureLorentz := properFutureGroup

end FoliationQM.LorentzMatrixGroup
