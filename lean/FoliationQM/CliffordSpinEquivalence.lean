module
public import FoliationQM.CliffordSpinSurjective

/-!
# The actual Minkowski Clifford spin group and SL(2,C)

Source scope: the abstract Clifford-spin identification underlying v13
`prop:takabayasi` and `eq:tetrad_rotor_map`. The existing Mathlib spin
subgroup, including its generated-vector membership condition, is
identified with the actual determinant-one complex matrices by the
proved injective and surjective Pauli homomorphism.

The inverse has exactly the previously constructed even-algebra inverse
as its ambient value. Consequently, strict Clifford normalization on an
actual even element suffices for genuine spin-group membership; this
converse is derived from the explicit generated-element surjectivity
proof and faithful even representation. No topology or global choice of
a representative of the Lorentz double cover is asserted here.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CliffordSpinEquivalence
open CliffordMinkowski CliffordEvenPauli CliffordEvenInvolution CliffordSpinMap
open SourcePolarDatum SpinorMatrix

/-- The genuine Minkowski Clifford spin group is isomorphic to the actual determinant-one complex two-by-two matrix group. -/
def spinEquiv : Spin ≃* SpecialLinearMatrix :=
  MulEquiv.ofBijective CliffordSpinMap.toMatrix ⟨toMatrix_injective, CliffordSpinSurjective.toMatrix_surjective⟩

/-- The group equivalence retains the actual Pauli homomorphism on Clifford spin elements. -/
theorem spinEquiv_apply (s : Spin) : spinEquiv s = toMatrix s := rfl

/-- The inverse group equivalence has precisely the inverse even-Pauli element as its actual even value. -/
theorem spinEquiv_symm_toEven (A : SpecialLinearMatrix) :
    toEven (spinEquiv.symm A) = evenPauliEquiv.symm A.val := by
  apply evenPauliEquiv.injective
  rw [evenPauliEquiv.apply_symm_apply, evenPauliEquiv_apply]
  change (toMatrix (spinEquiv.symm A)).val = A.val
  exact congrArg Subtype.val (spinEquiv.apply_symm_apply A)

/-- The inverse group equivalence retains the same literal ambient Clifford element as the even-algebra inverse. -/
theorem spinEquiv_symm_coe (A : SpecialLinearMatrix) :
    (spinEquiv.symm A : CliffordMinkowski.Algebra) =
      (evenPauliEquiv.symm A.val : CliffordMinkowski.Algebra) :=
  congrArg (fun x : CliffordAlgebra.even quadratic => x.val) (spinEquiv_symm_toEven A)

/-- An actual even Clifford element belongs to the generated spin group exactly when its faithful Pauli matrix has determinant one. -/
theorem mem_spinGroup_iff_det_one (x : CliffordAlgebra.even quadratic) :
    (x : CliffordMinkowski.Algebra) ∈ spinGroup quadratic ↔
      (evenPauli x).det = 1 := by
  constructor
  · intro hx
    exact (star_norm_one_iff_det_one x).mp
      (pinGroup.star_mul_self_of_mem (spinGroup.mem_pin hx))
  · intro hx
    obtain ⟨s, hs⟩ := CliffordSpinSurjective.toMatrix_surjective ⟨evenPauli x,hx⟩
    have he : toEven s = x := by
      apply evenPauli_injective
      exact congrArg Subtype.val hs
    have hc := congrArg (fun x : CliffordAlgebra.even quadratic => x.val) he
    change (s : CliffordMinkowski.Algebra) = (x : CliffordMinkowski.Algebra) at hc
    rw [← hc]
    exact s.property

/-- Strict left Clifford normalization characterizes actual spin membership on the even algebra. -/
theorem mem_spinGroup_iff_star_norm_one (x : CliffordAlgebra.even quadratic) :
    (x : CliffordMinkowski.Algebra) ∈ spinGroup quadratic ↔
      star (x : CliffordMinkowski.Algebra) * (x : CliffordMinkowski.Algebra) = 1 := by
  rw [mem_spinGroup_iff_det_one, star_norm_one_iff_det_one]

/-- Strict right Clifford normalization characterizes actual spin membership on the even algebra. -/
theorem mem_spinGroup_iff_norm_star_one (x : CliffordAlgebra.even quadratic) :
    (x : CliffordMinkowski.Algebra) ∈ spinGroup quadratic ↔
      (x : CliffordMinkowski.Algebra) * star (x : CliffordMinkowski.Algebra) = 1 := by
  rw [mem_spinGroup_iff_det_one, norm_star_one_iff_det_one]

/-- Genuine spin membership on the even algebra is equivalent to both actual Clifford-star normalization identities. -/
theorem mem_spinGroup_iff_unitary (x : CliffordAlgebra.even quadratic) :
    (x : CliffordMinkowski.Algebra) ∈ spinGroup quadratic ↔
      (x : CliffordMinkowski.Algebra) ∈ unitary CliffordMinkowski.Algebra := by
  rw [Unitary.mem_iff, mem_spinGroup_iff_det_one,
    star_norm_one_iff_det_one, norm_star_one_iff_det_one, and_self]

/-- In the actual Minkowski Clifford algebra, evenness and strict Clifford unitarity recover the full generated spin-group condition. -/
theorem mem_spinGroup_iff_even_and_unitary (x : CliffordMinkowski.Algebra) :
    x ∈ spinGroup quadratic ↔
      x ∈ CliffordAlgebra.even quadratic ∧ x ∈ unitary CliffordMinkowski.Algebra := by
  constructor
  · intro hx
    exact ⟨hx.2,hx.1.2⟩
  · rintro ⟨he,hu⟩
    exact (mem_spinGroup_iff_unitary ⟨x,he⟩).mpr hu

/-- The actual Dirac representative of the inverse spin-group equivalence is exactly the established concrete spin matrix. -/
theorem dirac_spinEquiv_symm (A : SpecialLinearMatrix) :
    dirac (spinEquiv.symm A : CliffordMinkowski.Algebra) = SpecialLinearSpin.spin A.val := by
  rw [dirac_eq_spin]
  exact congrArg (fun B : SpecialLinearMatrix => SpecialLinearSpin.spin B.val)
    (spinEquiv.apply_symm_apply A)

/-- The actual central negative element is the normalized square of a spatial Clifford vector. -/
def negativeOne : Spin :=
  CliffordSpinGenerators.pair quadratic (basisVector 1) (basisVector 1) (by
    norm_num [quadratic_basisVector, RealLorentzFrame.sign])

/-- The spatial-pair spin element has exactly the ambient Clifford value minus one. -/
theorem negativeOne_coe : (negativeOne : CliffordMinkowski.Algebra) = -1 := by
  rw [negativeOne, CliffordSpinGenerators.pair_coe, CliffordAlgebra.ι_sq_scalar,
    quadratic_basisVector]
  norm_num [RealLorentzFrame.sign]

/-- The actual negative spin element is distinct from the identity. -/
theorem negativeOne_ne_one : negativeOne ≠ 1 := by
  intro h
  have hc := congrArg (fun s : Spin => (s : CliffordMinkowski.Algebra)) h
  rw [negativeOne_coe] at hc
  change -(1 : CliffordMinkowski.Algebra) = 1 at hc
  have hm := congrArg dirac hc
  have h00 := congrArg (fun A : DiracMatrices.Mat => A 0 0) hm
  norm_num at h00

/-- The group equivalence sends the genuine negative Clifford element to minus the matrix identity. -/
theorem spinEquiv_negativeOne : (spinEquiv negativeOne).val = -(1 : Mat2) := by
  change evenPauli (toEven negativeOne) = -(1 : Mat2)
  have he : toEven negativeOne = -(1 : CliffordAlgebra.even quadratic) :=
    Subtype.ext negativeOne_coe
  rw [he, map_neg, map_one]

end FoliationQM.CliffordSpinEquivalence
