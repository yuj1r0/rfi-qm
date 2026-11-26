module

public import FoliationQM.JointL2Equivalence

/-!
# The action of a remote unitary on joint spatial waves

Conjugating pointwise action on the iterated Hilbert space by the spatial
`L²` equivalence constructs a unitary on the full joint wave space. Its
action on almost every retained fiber characterizes it and gives the
usual tensor-factor action on product states.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.JointRemoteUnitary

open MeasureTheory LorentzCoordinates JointL2Sections JointL2Curry

/-- Apply a remote unitary pointwise as a bounded operator on the iterated space. -/
def pointwise (U : Remote ≃ₗᵢ[ℂ] Remote) : Outer →L[ℂ] Outer :=
  U.toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 volume

/-- The pointwise operator acts on the chosen representative almost everywhere. -/
theorem coe_pointwise (U : Remote ≃ₗᵢ[ℂ] Remote) (F : Outer) :
    (pointwise U F : Spatial → Remote) =ᵐ[volume] fun x => U (F x) :=
  U.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLpL F

/-- The inverse remote operator undoes pointwise action on every iterated wave. -/
theorem pointwise_inverse (U : Remote ≃ₗᵢ[ℂ] Remote) (F : Outer) :
    pointwise U.symm (pointwise U F) = F := by
  apply Lp.ext
  filter_upwards [coe_pointwise U.symm (pointwise U F), coe_pointwise U F] with x h₁ h₂
  exact h₁.trans ((congrArg U.symm h₂).trans (U.symm_apply_apply _))

/-- The pointwise action of a remote unitary is unitary on the iterated space. -/
def outer (U : Remote ≃ₗᵢ[ℂ] Remote) : Outer ≃ₗᵢ[ℂ] Outer where
  toLinearMap := (pointwise U).toLinearMap
  invFun := pointwise U.symm
  left_inv := pointwise_inverse U
  right_inv := pointwise_inverse U.symm
  norm_map' F := by
    change ‖pointwise U F‖ = ‖F‖
    have hsq : ‖pointwise U F‖ ^ 2 = ‖F‖ ^ 2 := by
      rw [norm_sq_integral (pointwise U F), norm_sq_integral F]
      apply integral_congr_ae
      filter_upwards [coe_pointwise U F] with x hx
      simp [hx]
    simpa only [sq_eq_sq_iff_abs_eq_abs, abs_norm] using hsq

/-- Any remote Hilbert-space unitary acts on the full joint spatial wave space. -/
def remote (U : Remote ≃ₗᵢ[ℂ] Remote) : Joint ≃ₗᵢ[ℂ] Joint :=
  (JointL2Equivalence.equiv.trans (outer U)).trans JointL2Equivalence.equiv.symm

/-- In the curried representation the remote action applies the given unitary
to almost every retained fiber. -/
theorem curry_remote (U : Remote ≃ₗᵢ[ℂ] Remote) (ψ : Joint) :
    (curry (remote U ψ) : Spatial → Remote) =ᵐ[volume] fun x => U (curry ψ x) := by
  change (JointL2Equivalence.equiv (JointL2Equivalence.equiv.symm
    (outer U (curry ψ))) : Spatial → Remote) =ᵐ[volume] _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact coe_pointwise U (curry ψ)

/-- The canonical sections of the original and transformed joint scalar waves
satisfy the same remote action law at almost every retained position. -/
theorem sections_remote (U : Remote ≃ₗᵢ[ℂ] Remote) (ψ : Joint) :
    sections (remote U ψ) =ᵐ[volume] fun x => U (sections ψ x) :=
  (coe_curry _).symm.trans <| (curry_remote U ψ).trans ((coe_curry ψ).fun_comp U)

/-- The fiberwise action specifies a unique joint wave up to equality in joint `L²`. -/
theorem eq_remote_iff_sections (U : Remote ≃ₗᵢ[ℂ] Remote) (ψ φ : Joint) :
    φ = remote U ψ ↔ sections φ =ᵐ[volume] fun x => U (sections ψ x) := by
  constructor
  · rintro rfl
    exact sections_remote U ψ
  · intro h
    apply curry.injective
    exact Lp.ext <| (coe_curry φ).trans <| h.trans <|
      (sections_remote U ψ).symm.trans (coe_curry _).symm

/-- The joint-space remote action of the identity is the identity. -/
theorem remote_refl : remote (LinearIsometryEquiv.refl ℂ Remote) =
    LinearIsometryEquiv.refl ℂ Joint := by
  ext1 ψ
  apply curry.injective
  apply Lp.ext
  exact curry_remote _ ψ

/-- Sequential remote unitary operations compose in their given order. -/
theorem remote_trans (U V : Remote ≃ₗᵢ[ℂ] Remote) :
    remote (U.trans V) = (remote U).trans (remote V) := by
  ext1 ψ
  apply curry.injective
  apply Lp.ext
  exact (curry_remote (U.trans V) ψ).trans <|
    ((curry_remote V (remote U ψ)).trans ((curry_remote U ψ).fun_comp V)).symm

/-- Applying the inverse on the remote Hilbert space inverts the joint unitary. -/
theorem remote_symm (U : Remote ≃ₗᵢ[ℂ] Remote) : remote U.symm = (remote U).symm := by
  ext1 ψ
  apply (remote U).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  apply curry.injective
  apply Lp.ext
  filter_upwards [curry_remote U (remote U.symm ψ), curry_remote U.symm ψ] with x h₁ h₂
  exact h₁.trans ((congrArg U h₂).trans (U.apply_symm_apply _))

/-- A product wave retains its first factor and acquires the transformed remote factor. -/
theorem remote_product (U : Remote ≃ₗᵢ[ℂ] Remote) (u v : Remote) :
    remote U (JointL2Product.product u v) = JointL2Product.product u (U v) := by
  apply curry.injective
  apply Lp.ext
  filter_upwards [curry_remote U (JointL2Product.product u v), JointL2Product.curry_product u v,
    JointL2Product.curry_product u (U v)] with x h₁ h₂ h₃
  exact h₁.trans ((congrArg U h₂).trans ((U.map_smul (u x) v).trans h₃.symm))

/-- The tensor-factor rule on products uniquely determines the bounded joint operator. -/
theorem unique_on_products (U : Remote ≃ₗᵢ[ℂ] Remote) (A : Joint →L[ℂ] Joint)
    (hA : ∀ u v, A (JointL2Product.product u v) = JointL2Product.product u (U v)) :
    A = (remote U).toContinuousLinearEquiv.toContinuousLinearMap :=
  JointL2Equivalence.ext_on_products fun u v => (hA u v).trans (remote_product U u v).symm

end FoliationQM.JointRemoteUnitary
