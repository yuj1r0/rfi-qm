module
public import FoliationQM.SpinLorentzKernel
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Topology.Algebra.Group.Quotient

/-!
# The actual two-sign kernel and its natural group quotient

Source scope: the represented Lorentz-frame sign ambiguity in v13
`prop:takabayasi` and `eq:tetrad_rotor_map`. The kernel is the actual
kernel of the homomorphism into the independently defined proper future
Lorentz group. Its proved classification identifies it with the two
central scalar signs, and a Boolean equivalence records its exact size.

The actual group quotient carries its canonical quotient topology, with
an open continuous projection and injective continuous descended map.
Represented fibers have exactly two points. The range equivalence below
is explicitly to the image subgroup: full-target surjectivity and a
covering of the full Lorentz group require separate proofs. No abstract
Clifford-spin or universal-cover identification is asserted here.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
open Topology
namespace FoliationQM.SpinLorentzSignQuotient
open SourcePolarDatum LorentzMatrixGroup SpinLorentzOrientation SpinLorentzKernel
open scoped Manifold

/-- The existing genuine Lie group structure gives the natural matrix subtype a topological group structure. -/
instance instTopologicalSpecialLinearMatrix : IsTopologicalGroup SpecialLinearMatrix :=
  topologicalGroup_of_lieGroup 𝓘(ℝ, SpecialLinearCharts.Model) 1

/-- The actual kernel of the physical homomorphism, proved to consist of exactly the two central signs. -/
abbrev SignKernel := properFutureHom.ker

/-- The natural group quotient by the actual sign kernel of the physical homomorphism. -/
abbrev SignQuotient := SpecialLinearMatrix ⧸ SignKernel

/-- The canonical quotient projection from the actual determinant-one matrix group. -/
def projection : SpecialLinearMatrix →* SignQuotient := QuotientGroup.mk' SignKernel

/-- Every quotient class has an actual determinant-one matrix representative. -/
theorem projection_surjective : Function.Surjective projection := QuotientGroup.mk_surjective

/-- The projection is continuous for the inherited source and actual quotient topologies. -/
theorem continuous_projection : Continuous projection := QuotientGroup.continuous_mk

/-- The sign quotient projection is an open map in the natural topological group structure. -/
theorem isOpenMap_projection : IsOpenMap projection := QuotientGroup.isOpenMap_coe

/-- The source projection has exactly the canonical quotient topology. -/
theorem isQuotientMap_projection : IsQuotientMap projection := QuotientGroup.isQuotientMap_mk _

/-- The physical Lorentz homomorphism descends to the actual group quotient. -/
def quotientHom : SignQuotient →* ProperFutureLorentz := QuotientGroup.kerLift properFutureHom

/-- Evaluating the descended map on a representative gives its original physical Lorentz image. -/
theorem quotientHom_projection (A : SpecialLinearMatrix) :
    quotientHom (projection A) = properFutureHom A := rfl

/-- Factoring by the exact kernel makes the descended physical map injective. -/
theorem quotientHom_injective : Function.Injective quotientHom :=
  QuotientGroup.kerLift_injective properFutureHom

/-- The descended physical homomorphism is continuous in the actual quotient topology. -/
theorem continuous_quotientHom : Continuous quotientHom := by
  apply isQuotientMap_projection.continuous_iff.mpr
  exact continuous_properFutureHom

/-- Equality of source quotient classes is exactly equality of their physical Lorentz images. -/
theorem projection_eq_iff (A B : SpecialLinearMatrix) :
    projection A = projection B ↔ properFutureHom A = properFutureHom B := by
  constructor
  · exact congrArg quotientHom
  · intro h
    exact quotientHom_injective h

/-- The descended map has exactly the original physical image, without an assumption that this is the entire Lorentz target. -/
theorem quotientHom_range : Set.range quotientHom = Set.range properFutureHom := by
  ext L
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨A, rfl⟩ := projection_surjective q
    exact ⟨A, rfl⟩
  · rintro ⟨A, rfl⟩
    exact ⟨projection A, rfl⟩

/-- A Lorentz element has a quotient representative exactly when it has an actual matrix lift. -/
theorem exists_quotient_preimage_iff (L : ProperFutureLorentz) :
    (∃ q, quotientHom q = L) ↔ ∃ A, properFutureHom A = L := by
  change L ∈ Set.range quotientHom ↔ L ∈ Set.range properFutureHom
  rw [quotientHom_range]

/-- The kernel is closed because the actual physical map is continuous into a Hausdorff group. -/
theorem isClosed_signKernel : IsClosed (SignKernel : Set SpecialLinearMatrix) :=
  isClosed_eq continuous_properFutureHom continuous_const

/-- The quotient retains Hausdorff separation for its independently specified quotient topology. -/
instance instT2SignQuotient : T2Space SignQuotient := by
  let : IsClosed (SignKernel : Set SpecialLinearMatrix) := isClosed_signKernel
  infer_instance

/-- The sign quotient remains path connected as a continuous image of the genuine source matrix group. -/
instance instPathConnectedSignQuotient : PathConnectedSpace SignQuotient :=
  projection_surjective.pathConnectedSpace continuous_projection

/-- The first isomorphism theorem identifies the sign quotient with the actual image subgroup; this statement alone does not identify the image with the full target. -/
def quotientRangeEquiv : SignQuotient ≃* properFutureHom.range :=
  QuotientGroup.quotientKerEquivRange properFutureHom

/-- The image-subgroup equivalence retains the original physical image on source representatives. -/
theorem quotientRangeEquiv_projection (A : SpecialLinearMatrix) :
    (quotientRangeEquiv (projection A)).val = properFutureHom A := rfl


/-- Membership in the actual kernel is exactly the two central signs. -/
theorem mem_signKernel_iff (A : SpecialLinearMatrix) :
    A ∈ SignKernel ↔ A = 1 ∨ A = negativeOne := properFutureHom_eq_one_iff A

/-- The two Boolean choices give the identity and actual negative-identity kernel elements. -/
def kernelFromBool : Bool → SignKernel
  | false => ⟨1, properFutureHom.map_one⟩
  | true => ⟨negativeOne, properFutureHom_negativeOne⟩

/-- The two sign choices give distinct actual kernel elements. -/
theorem kernelFromBool_injective : Function.Injective kernelFromBool := by
  intro b c h
  cases b <;> cases c
  · rfl
  · exact False.elim (negativeOne_ne_one (congrArg Subtype.val h).symm)
  · exact False.elim (negativeOne_ne_one (congrArg Subtype.val h))
  · rfl

/-- Every kernel element is one of the two explicitly represented signs. -/
theorem kernelFromBool_surjective : Function.Surjective kernelFromBool := by
  intro A
  rcases (mem_signKernel_iff A.val).mp A.property with h | h
  · exact ⟨false, Subtype.ext h.symm⟩
  · exact ⟨true, Subtype.ext h.symm⟩

/-- The actual physical kernel is explicitly equivalent to two Boolean sign choices. -/
def boolKernelEquiv : Bool ≃ SignKernel :=
  Equiv.ofBijective kernelFromBool ⟨kernelFromBool_injective, kernelFromBool_surjective⟩

/-- The actual physical kernel has the finite type structure of its two explicit signs. -/
instance instFintypeSignKernel : Fintype SignKernel := Fintype.ofEquiv Bool boolKernelEquiv

/-- There are exactly two elements in the actual homomorphism kernel. -/
theorem card_signKernel : Fintype.card SignKernel = 2 := by
  simpa using Fintype.card_congr boolKernelEquiv.symm

/-- The cardinality of the actual kernel is exactly two, independently of a chosen finite enumeration. -/
theorem natCard_signKernel : Nat.card SignKernel = 2 := by
  rw [Nat.card_eq_fintype_card, card_signKernel]

/-- The finite kernel has the discrete topology inherited from the genuine matrix source. -/
instance instDiscreteSignKernel : DiscreteTopology SignKernel := inferInstance

/-- Equality in the actual group quotient is exactly equality up to the single central sign. -/
theorem projection_eq_iff_sign (A B : SpecialLinearMatrix) :
    projection A = projection B ↔ A = B ∨ A = negativeOne * B := by
  rw [projection_eq_iff, properFutureHom_eq_iff]

/-- The quotient identifies the two actual opposite matrix representatives. -/
theorem projection_negativeOne_mul (A : SpecialLinearMatrix) :
    projection (negativeOne * A) = projection A :=
  (projection_eq_iff_sign _ _).mpr (Or.inr rfl)

/-- The two representatives of any represented Lorentz fiber are distinct. -/
theorem negativeOne_mul_ne (A : SpecialLinearMatrix) : negativeOne * A ≠ A := by
  intro h
  apply negativeOne_ne_one
  exact mul_right_cancel (show negativeOne * A = 1 * A by simpa using h)

/-- An actual fiber over the image of a given source representative. -/
abbrev RepresentedFiber (A : SpecialLinearMatrix) :=
  {B : SpecialLinearMatrix // properFutureHom B = properFutureHom A}

/-- Multiplying a represented fiber by the inverse of its anchor identifies it with the actual kernel. -/
def fiberKernelEquiv (A : SpecialLinearMatrix) : RepresentedFiber A ≃ SignKernel where
  toFun B := ⟨B.val * A⁻¹, by
    change properFutureHom (B.val * A⁻¹) = 1
    rw [map_mul, map_inv, B.property, mul_inv_cancel]⟩
  invFun k := ⟨k.val * A, by
    rw [map_mul, (show properFutureHom k.val = 1 from k.property), one_mul]⟩
  left_inv B := Subtype.ext (by simp [mul_assoc])
  right_inv k := Subtype.ext (by simp [mul_assoc])

/-- Every represented actual Lorentz fiber contains exactly two source matrices. -/
theorem natCard_representedFiber (A : SpecialLinearMatrix) : Nat.card (RepresentedFiber A) = 2 := by
  rw [Nat.card_congr (fiberKernelEquiv A), natCard_signKernel]

end FoliationQM.SpinLorentzSignQuotient
