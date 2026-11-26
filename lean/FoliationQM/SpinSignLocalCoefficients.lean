module
public import FoliationQM.SpinSignHTwo
public import FoliationQM.CliffordSpinLorentzFields

/-!
# Locally constant mod-two coefficients and the physical Clifford signs

For the Spin-frame component of v13 `prop:takabayasi`, the established
cyclic identification sends the negative Clifford sign to one in
ZMod 2. Smooth physical sign coefficients on their actual domain
are exactly locally constant mod-two coefficients there.
-/

@[expose] public section
noncomputable section
open scoped Manifold
namespace FoliationQM.SpinSignLocalCoefficients
open CliffordSpinSignKernel CliffordSpinMap CliffordSpinLorentz CliffordSpinLorentzSmooth

/-- Encode the genuine Clifford kernel as additive mod-two coefficients. -/
def encode (s : Kernel) : ZMod 2 := Multiplicative.toAdd (kernelEquivZModTwo s)

/-- Decode a mod-two coefficient as an element of the actual physical kernel. -/
def decode (a : ZMod 2) : Kernel := kernelEquivZModTwo.symm (Multiplicative.ofAdd a)

/-- Encoding a decoded coefficient recovers that same coefficient. -/
theorem encode_decode (a : ZMod 2) : encode (decode a) = a :=
  congrArg Multiplicative.toAdd (kernelEquivZModTwo.apply_symm_apply _)

/-- Decoding an encoded physical sign recovers that same sign. -/
theorem decode_encode (s : Kernel) : decode (encode s) = s :=
  kernelEquivZModTwo.symm_apply_apply _

/-- The Clifford identity corresponds to zero. -/
theorem encode_one : encode 1 = 0 := congrArg Multiplicative.toAdd kernelEquivZModTwo_one

/-- The negative Clifford generator corresponds to the nonzero mod-two coefficient. -/
theorem encode_generator : encode generator = 1 :=
  congrArg Multiplicative.toAdd kernelEquivZModTwo_generator

/-- Multiplication of physical signs becomes addition of their coefficients. -/
theorem encode_mul (a b : Kernel) : encode (a * b) = encode a + encode b :=
  congrArg Multiplicative.toAdd (kernelEquivZModTwo.map_mul a b)

/-- Inversion of physical signs becomes additive negation. -/
theorem encode_inv (a : Kernel) : encode a⁻¹ = -encode a :=
  congrArg Multiplicative.toAdd (kernelEquivZModTwo.map_inv a)

/-- The zero mod-two coefficient decodes as the Clifford identity. -/
theorem decode_zero : decode 0 = 1 := kernelEquivZModTwo.symm.map_one

/-- Addition of coefficients becomes multiplication of their physical signs. -/
theorem decode_add (a b : ZMod 2) : decode (a + b) = decode a * decode b :=
  kernelEquivZModTwo.symm.map_mul _ _

/-- Additive negation decodes as inversion. -/
theorem decode_neg (a : ZMod 2) : decode (-a) = (decode a)⁻¹ :=
  kernelEquivZModTwo.symm.map_inv _

/-- Equality of additive coefficients detects equality of the actual signs. -/
theorem encode_injective : Function.Injective encode := by
  intro a b h
  exact (decode_encode a).symm.trans ((congrArg decode h).trans (decode_encode b))

variable {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace B] [ChartedSpace H B] {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞}

/-- Smooth physical signs become locally constant mod-two coefficients on the actual subset. -/
theorem locallyConstant_encode {U : Set B} {f : B → Kernel}
    (hf : ContMDiffOn I spinModel n (fun x => (f x).val) U) :
    IsLocallyConstant (fun x : U => encode (f x)) :=
  ((IsLocallyConstant.iff_continuous _).mpr
    (hf.continuousOn.domRestrict.subtype_mk _)).comp encode

/-- Locally constant coefficients decode to smooth physical signs at any order
because their continuous Spin field has constant Lorentz projection. -/
theorem contMDiffOn_decode {U : Set B} {f : B → ZMod 2}
    (hf : IsLocallyConstant (fun x : U => f x)) :
    ContMDiffOn I spinModel n (fun x => (decode (f x)).val) U := by
  have hc : ContinuousOn (fun x => (decode (f x)).val) U :=
    continuousOn_iff_continuous_domRestrict.mpr ((hf.comp (fun a => (decode a).val)).continuous)
  apply (CliffordSpinLorentzFields.contMDiffOn_iff_projection hc).mpr
  have he : (fun x => lorentzHom ((decode (f x)).val)) = fun _ => 1 :=
    funext (fun x => (decode (f x)).property)
  change ContMDiffOn I lorentzModel n (fun x => lorentzHom ((decode (f x)).val)) U
  rw [he]
  exact contMDiffOn_const

end FoliationQM.SpinSignLocalCoefficients
