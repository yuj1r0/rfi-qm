module
public import FoliationQM.LorentzFundamentalGroup
public import FoliationQM.LorentzLocalPaths
public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# The identity Lorentz gauge cannot be contracted on the whole group

For the frame-bundle component of v13 `prop:takabayasi`, local paths to
group elements cannot be chosen jointly over the whole Lorentz group.
Its verified fundamental group has two elements. Contracting an invertible
global coordinate change would contract the identity and force that
fundamental group to have only one element.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LorentzIdentityHomotopyObstruction
open LorentzMatrixGroup TopologicalSpace

/-- The original Lorentz group has a countable topology basis inherited from
matrix units, embedded by their forward and inverse matrices. -/
instance instSecondCountable : SecondCountableTopology ProperFutureLorentz := by
  let : SecondCountableTopology Mat4 := by
    change SecondCountableTopology (Fin 4 → Fin 4 → ℝ)
    infer_instance
  let : SecondCountableTopology Mat4ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph : Mat4 ≃ₜ Mat4ᵐᵒᵖ).symm.isEmbedding.secondCountableTopology
  let : SecondCountableTopology Mat4ˣ :=
    (Units.isEmbedding_embedProduct (M := Mat4)).secondCountableTopology
  let : SecondCountableTopology Lorentz := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  exact Topology.IsEmbedding.subtypeVal.secondCountableTopology

/-- Simple connectivity would force the identity-based fundamental group to have
one element, contradicting its verified cardinal two. -/
theorem not_simplyConnected : ¬ SimplyConnectedSpace ProperFutureLorentz := by
  intro h
  let := h
  have hc := Nat.card_unique (α := FundamentalGroup ProperFutureLorentz 1)
  rw [LorentzFundamentalGroup.fundamentalGroup_card] at hc
  exact (by decide : (2 : ℕ) ≠ 1) hc

/-- The identity transition on the whole Lorentz base is not nullhomotopic. -/
theorem id_not_nullhomotopic : ¬ (ContinuousMap.id ProperFutureLorentz).Nullhomotopic := by
  intro h
  let : ContractibleSpace ProperFutureLorentz := (contractible_iff_id_nullhomotopic _).2 h
  exact not_simplyConnected inferInstance

/-- No homeomorphic reparametrization of this whole overlap gives a
nullhomotopic transition. This also applies to group inversion. -/
theorem homeomorph_not_nullhomotopic (e : ProperFutureLorentz ≃ₜ ProperFutureLorentz) :
    ¬ (e : C(ProperFutureLorentz, ProperFutureLorentz)).Nullhomotopic := by
  intro h
  apply id_not_nullhomotopic
  have he : (e : C(ProperFutureLorentz, ProperFutureLorentz)).comp
      (e.symm : C(ProperFutureLorentz, ProperFutureLorentz)) = .id _ :=
    ContinuousMap.ext (fun x => e.apply_symm_apply x)
  rw [← he]
  exact h.comp_left _

/-- A joint family of paths from a fixed element to the prescribed
homeomorphic transition would give the forbidden homotopy. -/
theorem no_joint_family (g : ProperFutureLorentz) (e : ProperFutureLorentz ≃ₜ ProperFutureLorentz) :
    ¬ ∃ h : C(unitInterval × ProperFutureLorentz, ProperFutureLorentz),
      (∀ x, h (0, x) = g) ∧ ∀ x, h (1, x) = e x := by
  rintro ⟨h, h₀, h₁⟩
  let H : (ContinuousMap.const ProperFutureLorentz g).Homotopy
      (e : C(ProperFutureLorentz, ProperFutureLorentz)) :=
    { toContinuousMap := h, map_zero_left := h₀, map_one_left := h₁ }
  exact homeomorph_not_nullhomotopic e ⟨g, ⟨H.symm⟩⟩

end FoliationQM.LorentzIdentityHomotopyObstruction
