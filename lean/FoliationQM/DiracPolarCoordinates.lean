module
public import FoliationQM.CliffordSpinPolarReconstruction

/-!
# Polar coordinates for local variations of a strictly regular Dirac field

For v13 `thm:dirac_lift` and `prop:takabayasi`, use the actual Clifford
polar quotient diffeomorphism. Its realization always has positive scalar-
pseudoscalar invariant. On this open set its inverse is smooth at the
same order as the spinor field. A fixed fallback outside the open set
allows ambient field expressions to be written as total functions.
-/

@[expose] public section
noncomputable section
open scoped Manifold Topology ContDiff Matrix.Norms.Operator
namespace FoliationQM.DiracPolarCoordinates
open DiracMatrices SpinorRegularity PolarSignQuotient
open CliffordSpinPolarReconstruction (regularDiffeomorph regularDiffeomorph_toHomeomorph)

/-- The full quotient of the genuine density, four-pi angle and Clifford Spin source data. -/
abbrev Q := CliffordSpinPolarQuotient.SourceQuotient

/-- The previously constructed manifold model for this actual polar quotient. -/
abbrev model := CliffordSpinPolarReconstruction.model

/-- Realize a quotient class through the smooth polar diffeomorphism and include it in the spinor space. -/
def decode (q : Q) : Spinor := (regularDiffeomorph ∞ q).val

/-- Regard a regular spinor as a point of the strict open subtype, with a fixed value outside the subtype. -/
def regularize (z : Spinor) : RegularSpinor := by
  classical
  exact if h : Regular z then ⟨z, h⟩ else Classical.choice inferInstance

/-- Encode the ambient spinor using the inverse diffeomorphism on the strict regular domain. -/
def encode (z : Spinor) : Q := (regularDiffeomorph ∞).symm (regularize z)

/-- Regularization returns the original spinor wherever the invariant density is positive. -/
theorem regularize_of_regular {z : Spinor} (hz : Regular z) : regularize z = ⟨z, hz⟩ := by
  classical
  simp [regularize, hz]

/-- Every realized polar field satisfies the strict invariant-density condition. -/
theorem regular_decode (q : Q) : Regular (decode q) := (regularDiffeomorph ∞ q).property

/-- Decoding after encoding reproduces every spinor on the strict open set. -/
theorem decode_encode {z : Spinor} (hz : Regular z) : decode (encode z) = z := by
  simp only [decode, encode, (regularDiffeomorph ∞).apply_symm_apply, regularize_of_regular hz]

/-- Encoding after decoding recovers the original quotient class. -/
theorem encode_decode (q : Q) : encode (decode q) = q := by
  rw [encode, regularize_of_regular (regular_decode q)]
  exact (regularDiffeomorph ∞).symm_apply_apply q

/-- Realization of a source representative agrees with its actual Clifford formula. -/
theorem decode_mk (d : CliffordSpinPolarDatum.SourceDatum) :
    decode (Quotient.mk CliffordSpinPolarQuotient.sourceSetoid d) =
      (CliffordSpinPolarRealization.realizeSource d).val :=
  congrArg Subtype.val (CliffordSpinPolarReconstruction.regularDiffeomorph_mk ∞ d)

/-- The ambient realization is injective on the quotient itself. -/
theorem decode_injective : Function.Injective decode := Function.LeftInverse.injective encode_decode

/-- The range in ambient spinor space is exactly the strict invariant-density domain. -/
theorem range_decode : Set.range decode = {z : Spinor | Regular z} := by
  ext z
  exact ⟨fun ⟨q, e⟩ => e ▸ regular_decode q, fun hz => ⟨encode z, decode_encode hz⟩⟩

/-- The ambient realization uses the same quotient map at every differentiability order. -/
theorem decode_eq (n : WithTop ℕ∞) (q : Q) : decode q = (regularDiffeomorph n q).val := by
  change ((regularDiffeomorph ∞).toHomeomorph q).val = ((regularDiffeomorph n).toHomeomorph q).val
  rw [regularDiffeomorph_toHomeomorph, regularDiffeomorph_toHomeomorph]

/-- The inverse also has the same underlying map at every differentiability order. -/
theorem encode_eq (n : WithTop ℕ∞) (z : Spinor) : encode z = (regularDiffeomorph n).symm (regularize z) := by
  change (regularDiffeomorph ∞).toHomeomorph.symm (regularize z) =
    (regularDiffeomorph n).toHomeomorph.symm (regularize z)
  rw [regularDiffeomorph_toHomeomorph, regularDiffeomorph_toHomeomorph]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : WithTop ℕ∞} {x : E}

/-- Composing a locally smooth quotient field with realization is smooth in the ambient spinor calculus. -/
theorem contDiffAt_decode {f : E → Q} (hf : ContMDiffAt 𝓘(ℝ,E) model n f x) :
    ContDiffAt ℝ n (fun y => decode (f y)) x := by
  have h := (regularDiffeomorph n).contMDiff.contMDiffAt.comp x hf
  simp_rw [decode_eq n]
  exact RegularSpinorManifold.contMDiffAt_iff_value.mp h

/-- Strict regularity holds on a neighborhood of any regular value of a continuous field. -/
theorem eventually_regular {X : Type*} [TopologicalSpace X] {f : X → Spinor} {x₀ : X}
    (hf : ContinuousAt f x₀) (hr : Regular (f x₀)) : ∀ᶠ y in 𝓝 x₀, Regular (f y) :=
  hf (LocalPolarFields.regularDomain_isOpen.mem_nhds hr)

/-- A field smooth at a strictly regular point gives a locally smooth quotient field there. -/
theorem contMDiffAt_encode {f : E → Spinor} (hf : ContDiffAt ℝ n f x) (hr : Regular (f x)) :
    ContMDiffAt 𝓘(ℝ,E) model n (fun y => encode (f y)) x := by
  have he : (fun y => (regularize (f y)).val) =ᶠ[𝓝 x] f := by
    filter_upwards [eventually_regular hf.continuousAt hr] with y hy
    exact congrArg Subtype.val (regularize_of_regular hy)
  have hsub : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,Spinor) n (fun y => regularize (f y)) x :=
    RegularSpinorManifold.contMDiffAt_iff_value.mpr (hf.congr_of_eventuallyEq he)
  simp_rw [encode_eq n]
  exact (regularDiffeomorph n).symm.contMDiff.contMDiffAt.comp x hsub

end FoliationQM.DiracPolarCoordinates
