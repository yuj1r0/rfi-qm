module
public import FoliationQM.ModTwoRestriction
public import FoliationQM.SpinSignLocalCoefficients

/-!
# Comparing physical signs with independently defined mod-two cohomology

For the Spin-frame component of v13 `prop:takabayasi`, encoding the
actual Clifford kernel gives an additive equivalence between the
original degree-two obstruction group and locally constant mod-two
cohomology on the same cover. The map respects the actual pair
coboundaries and all open refinements.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.SpinModTwoComparison
open SpinSignCohomology SpinSignLocalCoefficients CliffordSpinCoverRefinement

variable {E H B ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace B] [ChartedSpace H B] {I : ModelWithCorners ℝ E H}
  {U : ι → TopologicalSpace.Opens B} {n : WithTop ℕ∞}

/-- Encode a smooth Clifford pair coefficient as an independent locally constant coefficient. -/
def toOne (a : OneCochain I U n) : ModTwoCohomology.OneCochain U where
  value i j x := encode (a.value i j x)
  local_value i j := locallyConstant_encode (a.smooth_value i j)
  identity i x hi := by rw [a.identity i x hi, encode_one]

/-- Decode an independent pair coefficient as a smooth coefficient in the physical kernel. -/
def fromOne (a : ModTwoCohomology.OneCochain U) : OneCochain I U n where
  value i j x := decode (a.value i j x)
  smooth_value i j := contMDiffOn_decode (a.local_value i j)
  identity i x hi := by rw [a.identity i x hi, decode_zero]

/-- Encode a physical triple cocycle into the independently defined additive cocycle group. -/
def toTwo (z : TwoCocycle I U n) : ModTwoCohomology.TwoCocycle U where
  value i j k x := encode (z.value i j k x)
  local_value i j k := locallyConstant_encode (z.smooth_value i j k)
  self_left i k x hi hk := by rw [z.self_left i k x hi hk, encode_one]
  self_right i k x hi hk := by rw [z.self_right i k x hi hk, encode_one]
  quadruple i j k l x hi hj hk hl := by
    simpa only [encode_mul] using congrArg encode (z.quadruple i j k l x hi hj hk hl)

/-- Decode an independent mod-two cocycle as a normalized smooth Clifford sign cocycle. -/
def fromTwo (z : ModTwoCohomology.TwoCocycle U) : TwoCocycle I U n where
  value i j k x := decode (z.value i j k x)
  smooth_value i j k := contMDiffOn_decode (z.local_value i j k)
  self_left i k x hi hk := by rw [z.self_left i k x hi hk, decode_zero]
  self_right i k x hi hk := by rw [z.self_right i k x hi hk, decode_zero]
  quadruple i j k l x hi hj hk hl := by
    simpa only [decode_add] using congrArg decode (z.quadruple i j k l x hi hj hk hl)

/-- Every total coefficient is retained by the physical encoding followed by decoding. -/
theorem fromTwo_toTwo (z : TwoCocycle I U n) : fromTwo (toTwo z) = z :=
  SpinSignHTwo.cocycle_ext (fun _ _ _ _ => decode_encode _)

/-- Every total mod-two coefficient is retained by decoding followed by encoding. -/
theorem toTwo_fromTwo (z : ModTwoCohomology.TwoCocycle U) : toTwo (fromTwo (I := I) (n := n) z) = z :=
  ModTwoCohomology.cocycle_ext (fun _ _ _ _ => encode_decode _)

/-- The original multiplicative pair coboundary encodes as the independent additive one. -/
theorem encode_boundary (a : OneCochain I U n) (i j k : ι) (x : B) :
    encode (boundary a i j k x) = ModTwoCohomology.boundary (toOne a) i j k x := by
  simp only [boundary, ModTwoCohomology.boundary, toOne, encode_mul, encode_inv, sub_eq_add_neg]

/-- Decoding an independent pair coboundary gives precisely the original sign coboundary. -/
theorem decode_boundary (a : ModTwoCohomology.OneCochain U) (i j k : ι) (x : B) :
    decode (ModTwoCohomology.boundary a i j k x) = boundary (fromOne (I := I) (n := n) a) i j k x := by
  simp only [boundary, ModTwoCohomology.boundary, fromOne, sub_eq_add_neg, decode_add, decode_neg]

/-- Encoding identifies exactly the two original relations by pair coboundaries on true triples. -/
theorem toTwo_related_iff (z w : TwoCocycle I U n) :
    ModTwoCohomology.Related (toTwo z) (toTwo w) ↔ Related z w := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨fromOne a, fun i j k x hi hj hk => ?_⟩
    have h := congrArg decode (ha i j k x hi hj hk)
    simpa only [toTwo, decode_add, decode_boundary (I := I) (n := n), decode_encode] using h
  · rintro ⟨a, ha⟩
    refine ⟨toOne a, fun i j k x hi hj hk => ?_⟩
    have h := congrArg encode (ha i j k x hi hj hk)
    simpa only [toTwo, encode_mul, encode_boundary] using h

/-- Decoding also preserves and reflects the independent relation. -/
theorem fromTwo_related_iff (z w : ModTwoCohomology.TwoCocycle U) :
    Related (fromTwo (I := I) (n := n) z) (fromTwo w) ↔ ModTwoCohomology.Related z w := by
  rw [← toTwo_related_iff, toTwo_fromTwo, toTwo_fromTwo]

/-- Pointwise multiplication of physical cocycles is encoded as additive cocycle addition. -/
theorem toTwo_mul (z w : TwoCocycle I U n) : toTwo (z * w) = toTwo z + toTwo w :=
  ModTwoCohomology.cocycle_ext (fun _ _ _ _ => encode_mul _ _)

/-- The additive form of the physical sign group is equivalent to the independently
defined locally constant mod-two cohomology group. -/
def classEquiv (I : ModelWithCorners ℝ E H) (U : ι → TopologicalSpace.Opens B)
    (n : WithTop ℕ∞) : Additive (ObstructionClass I U n) ≃+ ModTwoCohomology.H2 U where
  toFun c := Quotient.map toTwo (fun z w h => (toTwo_related_iff z w).mpr h) c.toMul
  invFun c := Additive.ofMul (Quotient.map (fromTwo (I := I) (n := n))
    (fun z w h => (fromTwo_related_iff z w).mpr h) c)
  left_inv c := by
    refine Quotient.inductionOn c ?_
    intro z
    change Additive.ofMul (classOf (fromTwo (toTwo z))) = Additive.ofMul (classOf z)
    rw [fromTwo_toTwo]
  right_inv c := by
    refine Quotient.inductionOn c ?_
    intro z
    change ModTwoCohomology.classOf (toTwo (fromTwo (I := I) (n := n) z)) = ModTwoCohomology.classOf z
    rw [toTwo_fromTwo]
  map_add' c d := by
    refine Quotient.inductionOn₂ c d ?_
    intro z w
    change ModTwoCohomology.classOf (toTwo (z * w)) = ModTwoCohomology.classOf (toTwo z + toTwo w)
    rw [toTwo_mul]

/-- On representatives the comparison applies the actual sign-to-mod-two encoding to each coefficient. -/
theorem classEquiv_classOf (z : TwoCocycle I U n) :
    classEquiv I U n (Additive.ofMul (classOf z)) = ModTwoCohomology.classOf (toTwo z) := rfl

/-- The coefficient comparison commutes with all open refinements, including independent index universes. -/
theorem classEquiv_restrict (R : Refinement U κ) (c : ObstructionClass I U n) :
    classEquiv I R.domain n (Additive.ofMul (SpinSignHTwo.restrictHom R c)) =
      ModTwoRestriction.restrictHom R (classEquiv I U n (Additive.ofMul c)) := by
  refine Quotient.inductionOn c ?_
  intro z
  rfl

end FoliationQM.SpinModTwoComparison
