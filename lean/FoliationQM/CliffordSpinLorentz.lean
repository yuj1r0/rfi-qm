module
public import FoliationQM.CliffordSpinEquivalence
public import FoliationQM.SpinLorentzSurjective

/-!
# The literal Clifford Spin action on the proper future Lorentz group

Source scope: the abstract spin-frame identification in v13
`prop:takabayasi` and `eq:tetrad_rotor_map`. The source retains Mathlib's
actual generated, even, strictly normalized Minkowski spin group. Its
faithful Pauli homomorphism is composed with the established physical
homomorphism into the independently defined proper future Lorentz group.
The resulting map is onto and has precisely the two actual Clifford signs
as its kernel and fibers.

The vector-action theorem concerns literal Clifford multiplication.
Generated Spin membership first proves that conjugation preserves the
embedded vector range. Applying the universal Dirac representation and
the actual physical lower-gamma formulas then identifies that vector by
vector-level injectivity. Faithfulness on the full Clifford algebra is
not assumed. These are algebraic action and image statements; topology,
covering structure and any universal-cover assertion remain separate.
-/

@[expose] public section

noncomputable section
open scoped Matrix
namespace FoliationQM.CliffordSpinLorentz
open CliffordMinkowski CliffordSpinMap CliffordSpinEquivalence
open SourcePolarDatum SpinorMatrix SpecialLinearSpin LorentzMatrixGroup

/-- The actual Clifford Spin homomorphism into the independently defined proper future Lorentz group. -/
def lorentzHom : Spin →* ProperFutureLorentz :=
  SpinLorentzOrientation.properFutureHom.comp CliffordSpinMap.toMatrix

/-- The Lorentz map is exactly the established physical homomorphism of the actual Pauli representative. -/
theorem lorentzHom_apply (s : Spin) :
    lorentzHom s = SpinLorentzOrientation.properFutureHom (CliffordSpinMap.toMatrix s) := rfl

/-- The actual Lorentz matrix is the physical matrix of the faithful Spin representative. -/
theorem lorentzHom_matrix (s : Spin) :
    matrix (lorentzHom s).val =
      SpinLorentzAction.lorentzMatrix (CliffordSpinMap.toMatrix s).val :=
  SpinLorentzOrientation.properFutureHom_matrix _

/-- The actual Lorentz vector action is ordinary matrix multiplication by that physical matrix. -/
theorem lorentzHom_action (s : Spin) (v : Vector) :
    SpinLorentzSurjective.action (lorentzHom s) v =
      SpinLorentzAction.lorentzMatrix (CliffordSpinMap.toMatrix s).val *ᵥ v := by
  rw [SpinLorentzSurjective.action, lorentzHom_matrix]

/-- Every independently specified proper future Lorentz element has an actual abstract Clifford Spin lift. -/
theorem lorentzHom_surjective : Function.Surjective lorentzHom :=
  SpinLorentzSurjective.properFutureHom_surjective.comp
    CliffordSpinSurjective.toMatrix_surjective

/-- The actual Clifford negative element maps to the established negative identity matrix. -/
theorem toMatrix_negativeOne :
    CliffordSpinMap.toMatrix CliffordSpinEquivalence.negativeOne =
      SpinLorentzKernel.negativeOne := by
  apply Subtype.ext
  exact CliffordSpinEquivalence.spinEquiv_negativeOne

/-- The kernel consists exactly of the identity and the genuine central negative Clifford element. -/
theorem lorentzHom_eq_one_iff (s : Spin) :
    lorentzHom s = 1 ↔ s = 1 ∨ s = CliffordSpinEquivalence.negativeOne := by
  rw [lorentzHom_apply, SpinLorentzKernel.properFutureHom_eq_one_iff,
    ← toMatrix_negativeOne, ← CliffordSpinMap.toMatrix.map_one]
  exact or_congr CliffordSpinMap.toMatrix_injective.eq_iff
    CliffordSpinMap.toMatrix_injective.eq_iff

/-- Two actual Clifford Spin elements give the same Lorentz transformation exactly when they differ by the central sign. -/
theorem lorentzHom_eq_iff (s t : Spin) :
    lorentzHom s = lorentzHom t ↔
      s = t ∨ s = CliffordSpinEquivalence.negativeOne * t := by
  rw [lorentzHom_apply, lorentzHom_apply, SpinLorentzKernel.properFutureHom_eq_iff,
    ← toMatrix_negativeOne, ← map_mul]
  exact or_congr CliffordSpinMap.toMatrix_injective.eq_iff
    CliffordSpinMap.toMatrix_injective.eq_iff

/-- The universal Dirac representation sends the actual Spin inverse to the genuine matrix inverse. -/
theorem dirac_spin_inv (s : Spin) :
    dirac (s⁻¹).val = (spin (CliffordSpinMap.toMatrix s).val)⁻¹ := by
  change dirac (star s.val) = _
  rw [dirac_spin_star, dirac_eq_spin]
  exact (spin_inverse _ (CliffordSpinMap.toMatrix s).property).symm

/-- Conjugation of every lower-gamma vector expansion is exactly the physical Lorentz matrix action. -/
theorem conjugate_lowerGamma (A : Mat2) (hA : A.det = 1) (v : Vector) :
    spin A * lowerGamma v * (spin A)⁻¹ =
      lowerGamma (SpinLorentzAction.lorentzMatrix A *ᵥ v) := by
  simp only [lowerGamma, Finset.mul_sum, Finset.sum_mul, mul_smul_comm,
    smul_mul_assoc, SpinLorentzAction.physical_frame_expansion A hA,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro mu _
  simp only [Matrix.mulVec, dotProduct, Complex.ofReal_sum, Complex.ofReal_mul,
    Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro a _
  rw [mul_comm]

/-- Actual Clifford conjugation of every embedded vector is exactly the independently defined Lorentz vector action. -/
theorem conjugation_ι (s : Spin) (v : Vector) :
    s.val * CliffordAlgebra.ι quadratic v * (s⁻¹).val =
      CliffordAlgebra.ι quadratic (SpinLorentzSurjective.action (lorentzHom s) v) := by
  have hr := spinGroup.conjAct_smul_ι_mem_range_ι
    (x := spinGroup.toUnits s) s.property v
  obtain ⟨w,hw⟩ := hr
  have hw' : CliffordAlgebra.ι quadratic w =
      s.val * CliffordAlgebra.ι quadratic v * (s⁻¹).val := by
    rw [ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct] at hw
    change CliffordAlgebra.ι quadratic w =
      s.val * CliffordAlgebra.ι quadratic v * (s⁻¹).val at hw
    exact hw
  have hm := congrArg dirac hw'
  rw [dirac_ι, map_mul, map_mul, dirac_ι, dirac_eq_spin, dirac_spin_inv,
    conjugate_lowerGamma _ (CliffordSpinMap.toMatrix s).property] at hm
  have he : w = SpinLorentzSurjective.action (lorentzHom s) v := by
    apply lowerGamma_injective
    simpa only [lorentzHom_action] using hm
  rw [← hw', he]

end FoliationQM.CliffordSpinLorentz
