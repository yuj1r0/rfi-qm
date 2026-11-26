module
public import FoliationQM.SpinSignHOne
public import FoliationQM.ModTwoPullback

/-!
# Smooth pullback of degree-one Clifford signs

For the Spin-frame component of v13 `prop:takabayasi`, composing a smooth
sign coefficient with a smooth base map preserves its regularity on the
preimage of its chart overlap. The chart signs witnessing a coboundary
pull back by the same formula, giving a homomorphism on first cohomology.
-/

@[expose] public section
noncomputable section
open scoped Manifold
namespace FoliationQM.SpinHOnePullback
open SpinSignCohomology SpinSignOneCocycle SpinSignHOne ModTwoPullback

variable {B X Y ι EX EB EY HX HB HY : Type*}
  [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  [NormedAddCommGroup EY] [NormedSpace ℝ EY] [TopologicalSpace HY]
  [TopologicalSpace X] [ChartedSpace HX X] [TopologicalSpace B] [ChartedSpace HB B]
  [TopologicalSpace Y] [ChartedSpace HY Y]
  {IX : ModelWithCorners ℝ EX HX} {IB : ModelWithCorners ℝ EB HB} {IY : ModelWithCorners ℝ EY HY}
  {n : WithTop ℕ∞} {U : ι → TopologicalSpace.Opens B}
  (f : C(X, B)) (hf : ContMDiff IX IB n f)

/-- Pull back a chart sign by evaluating it at the image under the base map. -/
def zero (a : ZeroCochain IB U n) : ZeroCochain IX (domain f U) n where
  value i x := a.value i (f x)
  smooth_value i := (a.smooth_value i).comp hf.contMDiffOn (fun _ hx => hx)

/-- The pulled chart sign is the original sign at the image point. -/
theorem zero_value (a : ZeroCochain IB U n) (i : ι) (x : X) :
    (zero f hf a).value i x = a.value i (f x) := rfl

/-- Pull back a normalized pair cochain on the actual preimage intersections. -/
def one (b : OneCochain IB U n) : OneCochain IX (domain f U) n where
  value i j x := b.value i j (f x)
  smooth_value i j := (b.smooth_value i j).comp hf.contMDiffOn (fun _ hx => hx)
  identity i x hx := b.identity i (f x) hx

/-- The normalized pair coefficient is evaluated at the original image point. -/
theorem one_value (b : OneCochain IB U n) (i j : ι) (x : X) :
    (one f hf b).value i j x = b.value i j (f x) := rfl

/-- The degree-one composition law pulls back on all genuine triple intersections. -/
def cocycle (z : Cocycle IB U n) : Cocycle IX (domain f U) n :=
  ⟨one f hf z.val, fun i j k x hi hj hk => z.property i j k (f x) hi hj hk⟩

/-- The pulled cocycle retains the literal physical sign at the image point. -/
theorem cocycle_value (z : Cocycle IB U n) (i j : ι) (x : X) :
    (cocycle f hf z).val.value i j x = z.val.value i j (f x) := rfl

/-- The coboundary of pulled chart signs equals the pullback of their original coboundary. -/
theorem cocycle_coboundary (a : ZeroCochain IB U n) :
    cocycle f hf (coboundary a) = coboundary (zero f hf a) := rfl

/-- Pullback carries agreement on the actual original overlaps to agreement on preimage overlaps. -/
theorem overlap {z w : Cocycle IB U n} (h : OverlapEq z w) :
    OverlapEq (cocycle f hf z) (cocycle f hf w) :=
  fun i j x hi hj => h i j (f x) hi hj

/-- A smooth chartwise gauge relating two representatives pulls back to a gauge of their pullbacks. -/
theorem gaugeRelated {z w : Cocycle IB U n} (h : GaugeRelated z w) :
    GaugeRelated (cocycle f hf z) (cocycle f hf w) := by
  obtain ⟨a, ha⟩ := h
  exact ⟨zero f hf a, fun i j x hi hj => ha i j (f x) hi hj⟩

/-- Pullback preserves the neutral sign cocycle on the whole base. -/
theorem cocycle_one : cocycle f hf (1 : Cocycle IB U n) = 1 := rfl

/-- Pullback preserves pointwise multiplication of the sign cocycles. -/
theorem cocycle_mul (z w : Cocycle IB U n) :
    cocycle f hf (z * w) = cocycle f hf z * cocycle f hf w := rfl

/-- Pullback preserves inversion of the physical sign cocycles. -/
theorem cocycle_inv (z : Cocycle IB U n) :
    cocycle f hf z⁻¹ = (cocycle f hf z)⁻¹ := rfl

/-- A smooth base map induces a group homomorphism on fixed-cover sign cohomology. -/
def hom (U : ι → TopologicalSpace.Opens B) : H1 IB U n →* H1 IX (domain f U) n where
  toFun c := Con.liftOn c (fun z => classOf (cocycle f hf z))
    (fun _ _ h => (SpinSignHOne.classOf_eq_iff _ _).mpr (gaugeRelated f hf h))
  map_one' := rfl
  map_mul' c d := by
    obtain ⟨z, rfl⟩ := classOf_surjective c
    obtain ⟨w, rfl⟩ := classOf_surjective d
    rfl

/-- A represented class pulls back to the class of its actual coefficient pullback. -/
theorem hom_classOf (z : Cocycle IB U n) :
    hom f hf U (classOf z) = classOf (cocycle f hf z) := rfl

/-- Pullback along the identity fixes every fixed-cover first cohomology class. -/
theorem hom_id (U : ι → TopologicalSpace.Opens B) (c : H1 IB U n) :
    hom (.id B) (contMDiff_id (I := IB)) U c = c := by
  obtain ⟨z, rfl⟩ := classOf_surjective c
  rfl

/-- Successive smooth pullbacks agree with pullback along the composite base map. -/
theorem hom_comp (f : C(X, B)) (g : C(Y, X)) (hf : ContMDiff IX IB n f)
    (hg : ContMDiff IY IX n g) (U : ι → TopologicalSpace.Opens B)
    (c : H1 IB U n) :
    hom g hg (domain f U) (hom f hf U c) = hom (f.comp g) (hf.comp hg) U c := by
  obtain ⟨z, rfl⟩ := classOf_surjective c
  rfl

end FoliationQM.SpinHOnePullback
