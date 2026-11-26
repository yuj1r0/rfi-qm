module
public import FoliationQM.LorentzPathSpinEquivalence
public import FoliationQM.SpinSignLocalCoefficients

/-!
# Intrinsic binary coefficients for Lorentz path classes

For the geometric characteristic-class comparison supporting v13
`prop:takabayasi`, the coefficient value is defined intrinsically:
zero for the identity path class, one for every other kernel class.
The actual Spin comparison proves that the intrinsic kernel has two
elements and that this literal value is additive. The resulting
character retains that original definition; it is not defined by a
physical sign-map composite. A genuine nontrivial Lorentz loop supplies
an explicit nonzero normalization example.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LorentzPathCoefficient
open BasedPathGroup LorentzMatrixGroup LorentzPathSpinEquivalence

/-- The literal kernel of the intrinsic Lorentz path-class endpoint homomorphism. -/
abbrev Kernel := (projection (G := ProperFutureLorentz)).ker

/-- The intrinsic binary value tests only equality of the path class with the unit. -/
def value (z : Kernel) : ZMod 2 := by
  classical
  exact if z = 1 then 0 else 1

/-- The intrinsic value is zero precisely for the identity path class. -/
theorem value_zero_iff (z : Kernel) : value z = 0 ↔ z = 1 := by
  classical
  by_cases hz : z = 1 <;> simp [value, hz]

/-- The intrinsic value is one precisely for a nonidentity kernel path class. -/
theorem value_one_iff (z : Kernel) : value z = 1 ↔ z ≠ 1 := by
  classical
  by_cases hz : z = 1 <;> simp [value, hz]

/-- The identity has intrinsic coefficient zero directly by its definition. -/
theorem value_one : value (1 : Kernel) = 0 := (value_zero_iff 1).mpr rfl

/-- The independently constructed intrinsic endpoint kernel has exactly two elements,
as proved by the actual commuting Spin equivalence. -/
theorem kernel_card : Nat.card Kernel = 2 :=
  (Nat.card_congr kernelEquiv.toEquiv).trans CliffordSpinSignKernel.kernel_card

/-- The intrinsically defined zero-or-one value agrees with the physical sign
encoding only after applying the proved actual kernel equivalence. -/
theorem value_eq_encode (z : Kernel) :
    value z = SpinSignLocalCoefficients.encode (kernelEquiv z) := by
  rcases CliffordSpinSignKernel.eq_one_or_generator (kernelEquiv z) with hz | hz
  · have h : z = 1 := kernelEquiv.injective (hz.trans kernelEquiv.map_one.symm)
    rw [h, value_one, map_one, SpinSignLocalCoefficients.encode_one]
  · have h : z ≠ 1 := by
      intro he
      rw [he, map_one] at hz
      exact CliffordSpinSignKernel.generator_ne_one hz.symm
    rw [(value_one_iff z).mpr h, hz, SpinSignLocalCoefficients.encode_generator]

/-- Multiplication of intrinsic kernel classes adds their literal binary values,
using the proved comparison rather than assuming a coefficient group law. -/
theorem value_mul (z w : Kernel) : value (z * w) = value z + value w := by
  rw [value_eq_encode, map_mul, SpinSignLocalCoefficients.encode_mul,
    ← value_eq_encode, ← value_eq_encode]

/-- The canonical intrinsic kernel character has literal zero-or-one value;
its group laws are theorems about the independently constructed path classes. -/
def character : Kernel →* Multiplicative (ZMod 2) where
  toFun z := Multiplicative.ofAdd (value z)
  map_one' := by rw [value_one]; rfl
  map_mul' z w := by rw [value_mul, ofAdd_add]

/-- Evaluation of the canonical character retains its intrinsic definition exactly. -/
theorem character_apply (z : Kernel) : character z = Multiplicative.ofAdd (value z) := rfl

/-- The canonical intrinsic character and the physical normalized kernel map agree
under the actual comparison, as a proved equality rather than a definition. -/
theorem character_eq_kernel (z : Kernel) :
    character z = CliffordSpinSignKernel.kernelEquivZModTwo (kernelEquiv z) := by
  rw [character_apply, value_eq_encode]
  rfl

/-- The canonical intrinsic character distinguishes every intrinsic endpoint-kernel class. -/
theorem character_injective : Function.Injective character := by
  intro z w h
  apply kernelEquiv.injective
  apply CliffordSpinSignKernel.kernelEquivZModTwo.injective
  rw [← character_eq_kernel, ← character_eq_kernel]
  exact h

/-- Both binary values are attained by the independently defined intrinsic character. -/
theorem character_surjective : Function.Surjective character := by
  intro a
  obtain ⟨z, hz⟩ := (kernelEquiv.trans CliffordSpinSignKernel.kernelEquivZModTwo).surjective a
  exact ⟨z, (character_eq_kernel z).trans hz⟩

/-- The actual non-null Lorentz generator defines a specific intrinsic kernel class. -/
def generator : Kernel :=
  ⟨pathClass CliffordSpinLoopMonodromy.generatorLoop,
    projection_pathClass CliffordSpinLoopMonodromy.generatorLoop⟩

/-- The intrinsic generator is nontrivial by actual endpoint-relative Lorentz homotopy. -/
theorem generator_ne_one : generator ≠ 1 := by
  intro h
  have hc : classOf (fromPath CliffordSpinLoopMonodromy.generatorLoop) = 1 :=
    congrArg Subtype.val h
  exact CliffordSpinLoopMonodromy.generatorLoop_not_nullhomotopic
    ((classOf_eq_one_iff _).mp hc)

/-- The actual nontrivial Lorentz loop receives the intrinsic residue one. -/
theorem value_generator : value generator = 1 := (value_one_iff generator).mpr generator_ne_one

/-- The canonical character is concretely nonzero on the genuine Lorentz generator. -/
theorem character_generator : character generator = Multiplicative.ofAdd (1 : ZMod 2) := by
  rw [character_apply, value_generator]

/-- Actual path lifting sends the displayed intrinsic generator to the genuine negative Clifford unit. -/
theorem kernelEquiv_generator : kernelEquiv generator = CliffordSpinSignKernel.generator := by
  apply Subtype.ext
  rw [kernelEquiv_val]
  change LorentzPathEndpoint.toSpin (classOf (fromPath CliffordSpinLoopMonodromy.generatorLoop)) =
    CliffordSpinEquivalence.negativeOne
  rw [LorentzPathEndpoint.toSpin_classOf, LorentzPathEndpoint.endpoint_fromPath]
  change CliffordSpinLoopMonodromy.liftLoop CliffordSpinLoopMonodromy.generatorLoop 1 = _
  rw [CliffordSpinLoopMonodromy.liftLoop_generatorLoop]
  exact CliffordSpinLoopMonodromy.signPath.target

end FoliationQM.LorentzPathCoefficient
