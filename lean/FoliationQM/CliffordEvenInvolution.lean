module
public import FoliationQM.CliffordEvenPauli

/-!
# Even Clifford conjugation, Pauli adjugation, and exact normalization

Source scope: the genuine Clifford realization underlying v13
`prop:takabayasi` and `eq:tetrad_rotor_map`. The actual Clifford conjugation
restricts to the even Minkowski algebra as a real linear involution that
reverses multiplication. The universal even Pauli map sends it to the
actual two-by-two adjugate, as proved by even Clifford induction.

The independently proved faithful Pauli equivalence then identifies each
left or right strict Clifford normalization with complex determinant one.
The universal Dirac representation is faithful on the even algebra and
takes this involution to the genuine Dirac adjoint there. These statements
are restricted to even elements; they do not identify odd Clifford
conjugation with the Dirac adjoint. The generated-vector condition of
Mathlib's spin group and its converse identification remain separate.
-/

@[expose] public section

noncomputable section
namespace FoliationQM.CliffordEvenInvolution
open CliffordMinkowski SpinorMatrix SpinLorentzPauli CliffordEvenPauli
open CliffordAlgebra

/-- The actual even subalgebra of the real Minkowski Clifford algebra. -/
abbrev Even := CliffordAlgebra.even quadratic

/-- The restriction of the genuine Clifford conjugation to its even subalgebra. -/
def evenStar (x : Even) : Even :=
  ⟨star (x : CliffordMinkowski.Algebra), by
    change star (x : CliffordMinkowski.Algebra) ∈ evenOdd quadratic 0
    simpa only [CliffordAlgebra.star_def, reverse_mem_evenOdd_iff,
      involute_mem_evenOdd_iff] using
      (show (x : CliffordMinkowski.Algebra) ∈ evenOdd quadratic 0 from x.property)⟩

/-- The restricted involution is exactly the ambient Clifford star. -/
theorem evenStar_coe (x : Even) :
    (evenStar x : CliffordMinkowski.Algebra) = star (x : CliffordMinkowski.Algebra) := rfl

/-- Actual even Clifford conjugation preserves addition. -/
theorem evenStar_add (x y : Even) : evenStar (x+y) = evenStar x + evenStar y := by
  apply Subtype.ext
  exact star_add _ _

/-- Actual even Clifford conjugation reverses the order of multiplication. -/
theorem evenStar_mul (x y : Even) : evenStar (x*y) = evenStar y * evenStar x := by
  apply Subtype.ext
  exact star_mul _ _

/-- Clifford conjugation is linear over the real scalar field. -/
theorem evenStar_smul (r : ℝ) (x : Even) : evenStar (r • x) = r • evenStar x := by
  apply Subtype.ext
  exact CliffordAlgebra.star_smul _ _

/-- Applying the genuine even Clifford conjugation twice returns the original element. -/
theorem evenStar_involutive : Function.Involutive evenStar := by
  intro x
  apply Subtype.ext
  exact star_star _

/-- The actual even Clifford involution bundled as a real linear equivalence. -/
def evenStarLinearEquiv : Even ≃ₗ[ℝ] Even where
  toFun := evenStar
  invFun := evenStar
  left_inv := evenStar_involutive
  right_inv := evenStar_involutive
  map_add' := evenStar_add
  map_smul' := evenStar_smul

/-- Actual Clifford conjugation fixes real scalar elements. -/
theorem evenStar_algebraMap (r : ℝ) :
    evenStar (algebraMap ℝ Even r) = algebraMap ℝ Even r := by
  apply Subtype.ext
  exact CliffordAlgebra.star_algebraMap _

/-- The genuine Clifford conjugate of an even vector pair is the reversed pair. -/
theorem evenStar_pair (v w : Vector) :
    evenStar ((CliffordAlgebra.even.ι quadratic).bilin v w) =
      (CliffordAlgebra.even.ι quadratic).bilin w v := by
  apply Subtype.ext
  change star (CliffordAlgebra.ι quadratic v * CliffordAlgebra.ι quadratic w) =
    CliffordAlgebra.ι quadratic w * CliffordAlgebra.ι quadratic v
  simp only [star_mul, star_ι, neg_mul_neg]

private theorem adjugate_add (A B : Mat2) :
    (A+B).adjugate = A.adjugate + B.adjugate := by
  simp only [Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [add_comm]

private theorem adjugate_algebraMap (r : ℝ) :
    (algebraMap ℝ Mat2 r).adjugate = algebraMap ℝ Mat2 r := by
  simp only [Algebra.algebraMap_eq_smul_one, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem adjugate_involutive (A : Mat2) : A.adjugate.adjugate = A := by
  simpa using Matrix.adjugate_adjugate' A

/-- The actual even Pauli map takes Clifford conjugation to two-by-two matrix adjugation. -/
theorem evenPauli_evenStar (x : Even) : evenPauli (evenStar x) = (evenPauli x).adjugate := by
  obtain ⟨x,hx⟩ := x
  induction x, hx using CliffordAlgebra.even_induction quadratic with
  | algebraMap r =>
    change evenPauli (evenStar (algebraMap ℝ Even r)) = (evenPauli (algebraMap ℝ Even r)).adjugate
    rw [evenStar_algebraMap, evenPauli.commutes, adjugate_algebraMap]
  | add x y hx hy ihx ihy =>
    change evenPauli (evenStar (⟨x,hx⟩ + ⟨y,hy⟩)) = (evenPauli (⟨x,hx⟩ + ⟨y,hy⟩)).adjugate
    rw [evenStar_add, map_add, map_add, adjugate_add, ihx, ihy]
  | ι_mul_ι_mul v w x hx ih =>
    change evenPauli (evenStar ((CliffordAlgebra.even.ι quadratic).bilin v w * ⟨x,hx⟩)) =
      (evenPauli ((CliffordAlgebra.even.ι quadratic).bilin v w * ⟨x,hx⟩)).adjugate
    rw [evenStar_mul, map_mul, map_mul, Matrix.adjugate_mul_distrib, ih,
      evenStar_pair, evenPauli_pair, evenPauli_pair, Matrix.adjugate_mul_distrib, adjugate_involutive]

/-- The universal Clifford representation agrees on every actual even element with its Pauli-Weyl spin matrix. -/
theorem dirac_even (x : Even) :
    dirac (x : CliffordMinkowski.Algebra) = SpecialLinearSpin.spin (evenPauli x) := by
  obtain ⟨x,hx⟩ := x
  induction x, hx using CliffordAlgebra.even_induction quadratic with
  | algebraMap r =>
    change dirac (algebraMap ℝ CliffordMinkowski.Algebra r) =
      SpecialLinearSpin.spin (evenPauli (algebraMap ℝ Even r))
    rw [dirac.commutes, evenPauli.commutes, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, SpinorMatrixSmooth.spin_real_smul,
      SpecialLinearSpin.spin_one]
  | add x y hx hy ihx ihy =>
    change dirac (x+y) = SpecialLinearSpin.spin (evenPauli (⟨x,hx⟩ + ⟨y,hy⟩))
    rw [map_add, map_add, SpinorMatrixSmooth.spin_add, ihx, ihy]
  | ι_mul_ι_mul v w x hx ih =>
    change dirac (CliffordAlgebra.ι quadratic v * CliffordAlgebra.ι quadratic w * x) =
      SpecialLinearSpin.spin (evenPauli ((CliffordAlgebra.even.ι quadratic).bilin v w * ⟨x,hx⟩))
    rw [map_mul dirac, map_mul evenPauli, dirac_pair, evenPauli_pair, ih]
    exact (SpecialLinearSpin.spin_mul _ _).symm

/-- The universal Dirac representation is faithful on the genuine even Minkowski Clifford algebra. -/
theorem dirac_even_injective :
    Function.Injective (fun x : Even => dirac (x : CliffordMinkowski.Algebra)) := by
  intro x y h
  apply evenPauli_injective
  apply SpecialLinearSpin.spin_injective
  simpa only [dirac_even] using h

/-- On actual even elements, Clifford conjugation is represented by the genuine Dirac adjoint. -/
theorem dirac_evenStar (x : Even) :
    dirac (star (x : CliffordMinkowski.Algebra)) =
      DiracAdjoint.diracAdjoint (dirac (x : CliffordMinkowski.Algebra)) := by
  change dirac (evenStar x : CliffordMinkowski.Algebra) =
    DiracAdjoint.diracAdjoint (dirac (x : CliffordMinkowski.Algebra))
  rw [dirac_even, dirac_even, evenPauli_evenStar,
    SpecialLinearSpin.spin_diracAdjoint]

/-- The represented left Clifford norm is the actual matrix determinant times the identity. -/
theorem evenPauli_star_norm (x : Even) :
    evenPauli (evenStar x * x) = (evenPauli x).det • (1 : Mat2) := by
  rw [map_mul, evenPauli_evenStar, Matrix.adjugate_mul]

/-- The represented right Clifford norm is the same actual determinant times the identity. -/
theorem evenPauli_norm_star (x : Even) :
    evenPauli (x * evenStar x) = (evenPauli x).det • (1 : Mat2) := by
  rw [map_mul, evenPauli_evenStar, Matrix.mul_adjugate]

/-- The genuine left Clifford normalization equals one exactly when its faithful Pauli image has determinant one. -/
theorem star_norm_one_iff_det_one (x : Even) :
    star (x : CliffordMinkowski.Algebra) * (x : CliffordMinkowski.Algebra) = 1 ↔
      (evenPauli x).det = 1 := by
  constructor
  · intro h
    have hE : evenStar x * x = 1 := Subtype.ext h
    have hM := evenPauli_star_norm x
    rw [hE, map_one] at hM
    have h00 := congrArg (fun A : Mat2 => A 0 0) hM
    simpa using h00.symm
  · intro h
    have hE : evenStar x * x = 1 := by
      apply evenPauli_injective
      rw [evenPauli_star_norm, h, one_smul, map_one]
    exact congrArg Subtype.val hE

/-- The genuine right Clifford normalization equals one exactly when its faithful Pauli image has determinant one. -/
theorem norm_star_one_iff_det_one (x : Even) :
    (x : CliffordMinkowski.Algebra) * star (x : CliffordMinkowski.Algebra) = 1 ↔
      (evenPauli x).det = 1 := by
  constructor
  · intro h
    have hE : x * evenStar x = 1 := Subtype.ext h
    have hM := evenPauli_norm_star x
    rw [hE, map_one] at hM
    have h00 := congrArg (fun A : Mat2 => A 0 0) hM
    simpa using h00.symm
  · intro h
    have hE : x * evenStar x = 1 := by
      apply evenPauli_injective
      rw [evenPauli_norm_star, h, one_smul, map_one]
    exact congrArg Subtype.val hE

end FoliationQM.CliffordEvenInvolution
