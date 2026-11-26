module
public import FoliationQM.CliffordSpinSignKernel
public import FoliationQM.CliffordSpinUniversalCover
public import FoliationQM.CliffordSpinPathLifting
public import Mathlib.Algebra.Group.Equiv.Opposite

/-!
# The actual proper future Lorentz fundamental group

Source scope: the explicit assertion pi_1(SO^+(1,3)) = Z_2 in v13
Section 7, supporting `prop:takabayasi` and `eq:tetrad_rotor_map`.
The base is the independently defined proper future Lorentz group in
its original matrix topology. The total space is the genuine Minkowski
Clifford Spin group, whose simple connectivity has already been proved.
The original physical covering is a quotient covering by its exact
actual sign kernel. Its fundamental-group equivalence is normalized by
sending the genuine negative Clifford unit to the additive residue one.

The initial equivalence correctly takes values in the opposite kernel
group, respecting the library's path composition convention. Only the
proved commutative two-element target removes that opposite. Actual
lifted endpoints determine the displayed class, and the result is
independent of which actual Spin lift anchors a given Lorentz fiber.
No different topology, abstract replacement cover, or assumed Lorentz
fundamental-group classification is used. No SO(3) classification is
claimed by this module.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function
open scoped Topology
namespace FoliationQM.LorentzFundamentalGroup
open CliffordSpinMap CliffordSpinLorentz CliffordSpinCovering LorentzMatrixGroup
open CliffordSpinSignKernel CliffordSpinPathLifting

/-- The original physical Clifford Spin covering is a quotient covering for the literal action of its actual discrete sign kernel. -/
theorem lorentzHom_isQuotientCoveringMap : IsQuotientCoveringMap lorentzHom Kernel :=
  (lorentzHom_isCoveringMap.isQuotientMap lorentzHom_surjective).isQuotientCoveringMap_of_isDiscrete_ker_monoidHom
      (SetLike.isDiscrete_iff_discreteTopology.mpr (inferInstance : DiscreteTopology Kernel))

/-- The fundamental group at an arbitrary actual Lorentz point is multiplicatively equivalent to the opposite genuine sign kernel, through a specified actual Spin anchor. -/
def kernelFundamentalGroupEquiv (L : ProperFutureLorentz) (s : Fiber L) :
    FundamentalGroup ProperFutureLorentz L ≃* Kernelᵐᵒᵖ :=
  lorentzHom_isQuotientCoveringMap.fundamentalGroupEquiv s

/-- The opposite-kernel class acts on the actual initial Spin value to give exactly the transported endpoint. -/
theorem kernelFundamentalGroupEquiv_endpoint (L : ProperFutureLorentz) (s : Fiber L)
    (γ : FundamentalGroup ProperFutureLorentz L) :
    (MulOpposite.unop (kernelFundamentalGroupEquiv L s γ)).val * s.val =
      (transport γ.asHom s).val :=
  lorentzHom_isQuotientCoveringMap.unop_fundamentalGroupToMulOpposite_smul

/-- The opposite-kernel fundamental-group identification is independent of the actual anchor in a fixed Lorentz fiber because the proved sign kernel is commutative. -/
theorem kernelFundamentalGroupEquiv_anchor_independent (L : ProperFutureLorentz)
    (s t : Fiber L) : kernelFundamentalGroupEquiv L s = kernelFundamentalGroupEquiv L t :=
  lorentzHom_isQuotientCoveringMap.fundamentalGroupEquiv_eq s t

/-- The opposite actual sign kernel is identified with the multiplicative form of the additive two-element residue group, retaining the genuine negative-unit generator normalization. -/
def kernelOppositeEquiv : Kernelᵐᵒᵖ ≃* Multiplicative (ZMod 2) :=
  (MulEquiv.op kernelEquivZModTwo).trans MulOpposite.opMulEquiv.symm

/-- Removing the opposite uses exactly the previously proved kernel-to-residue equivalence on the actual underlying kernel element. -/
theorem kernelOppositeEquiv_apply (k : Kernelᵐᵒᵖ) :
    kernelOppositeEquiv k = kernelEquivZModTwo k.unop := rfl

/-- The actual Lorentz fundamental group at an arbitrary basepoint is the two-element residue group, with a specified actual Spin anchor. -/
def basedFundamentalGroupEquiv (L : ProperFutureLorentz) (s : Fiber L) :
    FundamentalGroup ProperFutureLorentz L ≃* Multiplicative (ZMod 2) :=
  (kernelFundamentalGroupEquiv L s).trans kernelOppositeEquiv

/-- The normalized Lorentz class is the exact residue of the underlying genuine kernel element obtained by monodromy. -/
theorem basedFundamentalGroupEquiv_apply (L : ProperFutureLorentz) (s : Fiber L)
    (γ : FundamentalGroup ProperFutureLorentz L) :
    basedFundamentalGroupEquiv L s γ =
      kernelEquivZModTwo (kernelFundamentalGroupEquiv L s γ).unop := rfl

/-- The normalized class determines the literal sign multiplying the initial actual Spin anchor to the transported endpoint. -/
theorem basedFundamentalGroupEquiv_endpoint (L : ProperFutureLorentz) (s : Fiber L)
    (γ : FundamentalGroup ProperFutureLorentz L) :
    (kernelEquivZModTwo.symm (basedFundamentalGroupEquiv L s γ)).val * s.val =
      (transport γ.asHom s).val := by
  rw [basedFundamentalGroupEquiv_apply, MulEquiv.symm_apply_apply]
  exact kernelFundamentalGroupEquiv_endpoint L s γ

/-- The generator-normalized Lorentz fundamental-group equivalence is independent of the individual Spin anchor within the fiber. -/
theorem basedFundamentalGroupEquiv_anchor_independent (L : ProperFutureLorentz)
    (s t : Fiber L) : basedFundamentalGroupEquiv L s = basedFundamentalGroupEquiv L t := by
  unfold basedFundamentalGroupEquiv
  rw [kernelFundamentalGroupEquiv_anchor_independent L s t]

/-- At every actual Lorentz basepoint the fundamental group has exactly two elements. -/
theorem fundamentalGroup_card (L : ProperFutureLorentz) :
    Nat.card (FundamentalGroup ProperFutureLorentz L) = 2 := by
  obtain ⟨s, hs⟩ := lorentzHom_surjective L
  rw [Nat.card_congr ((basedFundamentalGroupEquiv L ⟨s, hs⟩).toEquiv.trans
    Multiplicative.toAdd), Nat.card_eq_fintype_card, ZMod.card]

/-- The identity-based fundamental group of the independently defined proper future Lorentz group is exactly the multiplicative form of additive ZMod 2. -/
def fundamentalGroupEquiv :
    FundamentalGroup ProperFutureLorentz 1 ≃* Multiplicative (ZMod 2) :=
  basedFundamentalGroupEquiv 1 ⟨1, map_one lorentzHom⟩

/-- At the identity anchor the actual transported Spin endpoint is precisely the genuine kernel element represented by the normalized Lorentz fundamental-group class. -/
theorem fundamentalGroupEquiv_endpoint (γ : FundamentalGroup ProperFutureLorentz 1) :
    (kernelEquivZModTwo.symm (fundamentalGroupEquiv γ)).val =
      (transport γ.asHom ⟨1, map_one lorentzHom⟩).val := by
  simpa only [fundamentalGroupEquiv, mul_one] using
    basedFundamentalGroupEquiv_endpoint 1 ⟨1, map_one lorentzHom⟩ γ

/-- A normalized identity-based Lorentz class is trivial exactly when its actual lifted endpoint is the genuine Clifford unit. -/
theorem fundamentalGroupEquiv_eq_one_iff (γ : FundamentalGroup ProperFutureLorentz 1) :
    fundamentalGroupEquiv γ = 1 ↔ (transport γ.asHom ⟨1, map_one lorentzHom⟩).val = 1 := by
  rw [← fundamentalGroupEquiv_endpoint]
  constructor
  · intro h
    rw [h, map_one]
    rfl
  · intro h
    have hk : kernelEquivZModTwo.symm (fundamentalGroupEquiv γ) = 1 := Subtype.ext h
    have he := congrArg kernelEquivZModTwo hk
    simpa only [MulEquiv.apply_symm_apply, map_one] using he

/-- The fundamental-group equivalence sends a displayed lifted loop with actual endpoint k to the residue assigned to that genuine kernel element. -/
theorem fundamentalGroupEquiv_eq_kernel_iff (γ : FundamentalGroup ProperFutureLorentz 1)
    (k : Kernel) : fundamentalGroupEquiv γ = kernelEquivZModTwo k ↔
      (transport γ.asHom ⟨1, map_one lorentzHom⟩).val = k.val := by
  rw [← fundamentalGroupEquiv_endpoint]
  constructor
  · intro h
    rw [h, MulEquiv.symm_apply_apply]
  · intro h
    have hk : kernelEquivZModTwo.symm (fundamentalGroupEquiv γ) = k := Subtype.ext h
    exact (kernelEquivZModTwo.apply_symm_apply (fundamentalGroupEquiv γ)).symm.trans
      (congrArg kernelEquivZModTwo hk)

end FoliationQM.LorentzFundamentalGroup
