module
public import FoliationQM.CliffordEvenInvolution
public import FoliationQM.CliffordSpinGenerators
public import FoliationQM.SpecialLinearGroupManifold

/-!
# The actual Clifford Spin homomorphism to determinant-one matrices

Source scope: the abstract Clifford identification underlying v13
`prop:takabayasi` and `eq:tetrad_rotor_map`. The source is Mathlib's
literal spinGroup of the real (+---) quadratic form, retaining its
generated-vector, evenness and strict normalization conditions. The
faithful even Pauli representation gives an injective homomorphism to
the existing determinant-one matrix group. Determinant one follows from
actual Clifford normalization; it is not an extra hypothesis.

Surjectivity and its required generated-vector construction are separate.
The universal Dirac representation agrees exactly with the established
concrete spin matrices on every actual abstract Spin element.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CliffordSpinMap
open CliffordMinkowski CliffordEvenPauli CliffordEvenInvolution
open SourcePolarDatum SpinorMatrix SpinLorentzPauli

/-- The literal Mathlib spin group of the actual real Minkowski quadratic form. -/
abbrev Spin := spinGroup quadratic

/-- The natural multiplicative inclusion of actual Spin elements into the genuine even algebra. -/
def toEven : Spin →* CliffordAlgebra.even quadratic where
  toFun s := ⟨s.val, spinGroup.mem_even s.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The even-algebra inclusion retains the underlying abstract Clifford element exactly. -/
theorem toEven_coe (s : Spin) : (toEven s : CliffordMinkowski.Algebra) = s.val := rfl

/-- Every actual abstract Spin element has determinant-one Pauli image, by its strict Clifford normalization. -/
theorem determinant_one (s : Spin) : (evenPauli (toEven s)).det = 1 :=
  (star_norm_one_iff_det_one (toEven s)).mp
    (pinGroup.star_mul_self_of_mem (spinGroup.mem_pin s.property))

/-- The actual faithful Clifford-Spin representation as a homomorphism into the existing determinant-one matrices. -/
def toMatrix : Spin →* SpecialLinearMatrix where
  toFun s := ⟨evenPauli (toEven s), determinant_one s⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' s t := by apply Subtype.ext; simp

/-- The determinant-one homomorphism retains exactly the actual even Pauli matrix. -/
theorem toMatrix_coe (s : Spin) : (toMatrix s).val = evenPauli (toEven s) := rfl

/-- The abstract Spin-to-matrix homomorphism is injective by proved faithfulness of the genuine even representation. -/
theorem toMatrix_injective : Function.Injective toMatrix := by
  intro s t h
  have he : toEven s = toEven t := evenPauli_injective (congrArg Subtype.val h)
  apply Subtype.ext
  exact congrArg (fun x : CliffordAlgebra.even quadratic => x.val) he

/-- The even image of an actual normalized vector pair is its literal even Clifford product. -/
theorem toEven_pair (v w : Vector) (h : quadratic v * quadratic w = 1) :
    toEven (CliffordSpinGenerators.pair quadratic v w h) =
      (CliffordAlgebra.even.ι quadratic).bilin v w := rfl

/-- The actual Spin homomorphism sends a normalized vector pair to its physical Pauli-adjugate matrix product. -/
theorem toMatrix_pair (v w : Vector) (h : quadratic v * quadratic w = 1) :
    (toMatrix (CliffordSpinGenerators.pair quadratic v w h)).val =
      pauli v * (pauli w).adjugate := by
  rw [toMatrix_coe, toEven_pair, evenPauli_pair]

/-- The universal abstract Clifford representation of every Spin element is exactly its previously constructed concrete Dirac spin matrix. -/
theorem dirac_eq_spin (s : Spin) :
    dirac s.val = SpecialLinearSpin.spin (toMatrix s).val :=
  dirac_even (toEven s)

/-- The universal Dirac representation is faithful on the literal abstract Spin group. -/
theorem dirac_spin_injective : Function.Injective (fun s : Spin => dirac s.val) := by
  intro s t h
  apply toMatrix_injective
  apply Subtype.ext
  apply SpecialLinearSpin.spin_injective
  simpa only [dirac_eq_spin] using h

/-- Clifford star on actual Spin elements is represented by the genuine Dirac adjoint. -/
theorem dirac_spin_star (s : Spin) :
    dirac (star s.val) = DiracAdjoint.diracAdjoint (dirac s.val) :=
  dirac_evenStar (toEven s)

end FoliationQM.CliffordSpinMap
