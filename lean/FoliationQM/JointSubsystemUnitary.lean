module

public import FoliationQM.JointRemoteUnitary

/-!
# Two local unitary operators on the full spatial product

Coordinate exchange gives the retained-particle action from the remote
one. The two actions commute on product waves. Density of their linear
span extends commutation and uniqueness to all joint L² states.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.JointSubsystemUnitary

open MeasureTheory JointL2Sections JointL2Product JointRemoteUnitary LorentzCoordinates

/-- Pull back a six-dimensional wave along the exchange of its two spatial coordinates. -/
def swapMap : Joint →ₗᵢ[ℂ] Joint :=
  Lp.compMeasurePreservingₗᵢ ℂ Prod.swap Measure.measurePreserving_swap

/-- Coordinate exchange of the quotient wave uses the swapped representative almost everywhere. -/
theorem coe_swap (ψ : Joint) : (swapMap ψ : Spatial × Spatial → ℂ) =ᵐ[volume] ψ ∘ Prod.swap :=
  Lp.coeFn_compMeasurePreserving ψ Measure.measurePreserving_swap

/-- Exchanging both coordinates twice returns the original L² wave. -/
theorem swap_twice (ψ : Joint) : swapMap (swapMap ψ) = ψ := by
  apply Lp.ext
  exact (coe_swap (swapMap ψ)).trans
    (Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp (coe_swap ψ))

/-- Exchange as an isometric equivalence of the joint Hilbert space. -/
def exchange : Joint ≃ₗᵢ[ℂ] Joint :=
  LinearIsometryEquiv.ofSurjective swapMap fun ψ => ⟨swapMap ψ, swap_twice ψ⟩

/-- A product wave exchanges its two actual factors. -/
theorem exchange_product (u v : Remote) : exchange (product u v) = product v u := by
  apply Lp.ext
  filter_upwards [coe_swap (product u v),
    Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp (coe_product u v),
    coe_product v u] with z hx hy hz
  exact hx.trans (hy.trans ((mul_comm _ _).trans hz.symm))

/-- A retained subsystem unitary on the joint space acts through exchange and remote evolution. -/
def retained (U : Remote ≃ₗᵢ[ℂ] Remote) : Joint ≃ₗᵢ[ℂ] Joint :=
  (exchange.trans (remote U)).trans exchange

/-- On a product state the retained action transforms exactly the first factor. -/
theorem retained_product (U : Remote ≃ₗᵢ[ℂ] Remote) (u v : Remote) :
    retained U (product u v) = product (U u) v := by
  change exchange (remote U (exchange (product u v))) = _
  rw [exchange_product, remote_product, exchange_product]

/-- The two lifted subsystem operations commute on every joint L² wave. -/
theorem commute (U V : Remote ≃ₗᵢ[ℂ] Remote) (ψ : Joint) :
    retained U (remote V ψ) = remote V (retained U ψ) := by
  let A := (retained U).toContinuousLinearEquiv.toContinuousLinearMap
  let B := (remote V).toContinuousLinearEquiv.toContinuousLinearMap
  have h : A.comp B = B.comp A := JointL2Equivalence.ext_on_products fun u v => by
    change retained U (remote V (product u v)) = remote V (retained U (product u v))
    rw [remote_product, retained_product, retained_product, remote_product]
  exact DFunLike.congr_fun h ψ

/-- The tensor product of supplied subsystem unitaries on the physical six-dimensional space. -/
def factor (U V : Remote ≃ₗᵢ[ℂ] Remote) : Joint ≃ₗᵢ[ℂ] Joint :=
  (retained U).trans (remote V)

/-- The constructed joint operation has the defining action of the tensor product on pure tensors. -/
theorem factor_product (U V : Remote ≃ₗᵢ[ℂ] Remote) (u v : Remote) :
    factor U V (product u v) = product (U u) (V v) := by
  change remote V (retained U (product u v)) = _
  rw [retained_product, remote_product]

/-- The action on product waves uniquely specifies the bounded joint operator, including
its action on entangled waves. -/
theorem unique_factor (U V : Remote ≃ₗᵢ[ℂ] Remote) (A : Joint →L[ℂ] Joint)
    (h : ∀ u v, A (product u v) = product (U u) (V v)) :
    A = (factor U V).toContinuousLinearEquiv.toContinuousLinearMap :=
  JointL2Equivalence.ext_on_products fun u v => (h u v).trans (factor_product U V u v).symm

end FoliationQM.JointSubsystemUnitary
