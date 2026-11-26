module

public import FoliationQM.JointL2Curry
public import FoliationQM.ScalarFiberPairing

/-!
# Product waves in the joint scalar L² space

In the tensor-propagator argument of v13 `thm:entanglement_nosignaling`,
a decomposable tensor represents the scalar wave u(x)v(y). Square
integrability, the product norm, and the factorization of overlaps all use
the concrete joint spatial volume. Currying gives the remote fiber u(x) • v.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.JointL2Product

open MeasureTheory LorentzCoordinates JointL2Sections JointL2Curry

/-- The scalar product of two square-integrable one-particle waves is square
integrable on the product of the spatial slices. -/
theorem product_memLp (u v : Remote) :
    MemLp (fun z : Spatial × Spatial => u z.1 * v z.2) 2 volume := by
  change MemLp _ 2 (volume.prod volume)
  have hm : AEStronglyMeasurable (fun z : Spatial × Spatial => u z.1 * v z.2) (volume.prod volume) :=
    (Lp.aestronglyMeasurable u).comp_fst.mul (Lp.aestronglyMeasurable v).comp_snd
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  simpa only [Pi.mul_apply, norm_mul, mul_pow] using
    (Lp.memLp u).norm.integrable_sq.mul_prod (Lp.memLp v).norm.integrable_sq

/-- The joint scalar L² class of a product wave. -/
def product (u v : Remote) : Joint := (product_memLp u v).toLp _

/-- The joint representative is the scalar product of the two representatives almost everywhere. -/
theorem coe_product (u v : Remote) :
    (product u v : Spatial × Spatial → ℂ) =ᵐ[volume] fun z => u z.1 * v z.2 :=
  (product_memLp u v).coeFn_toLp

/-- The remote L² class at almost every retained point is the second factor
multiplied by the scalar value of the first. -/
theorem curry_product (u v : Remote) :
    (curry (product u v) : Spatial → Remote) =ᵐ[volume] fun x => u x • v := by
  filter_upwards [curry_toLp (product_memLp u v)] with x hx
  apply Lp.ext
  exact hx.trans (Lp.coeFn_smul (u x) v).symm

/-- The complex overlap of two product states factors into the two subsystem overlaps. -/
theorem inner_product (u v a b : Remote) :
    inner ℂ (product u v) (product a b) = inner ℂ u a * inner ℂ v b := by
  rw [product, product, ScalarFiberPairing.inner_toLp]
  calc
    _ = ∫ z : Spatial × Spatial, inner ℂ (u z.1) (a z.1) * inner ℂ (v z.2) (b z.2)
          ∂volume.prod volume := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro z
      change star (u z.1 * v z.2) * (a z.1 * b z.2) =
        (a z.1 * star (u z.1)) * (b z.2 * star (v z.2))
      rw [star_mul]
      ring
    _ = _ := by
      rw [L2.inner_def u a, L2.inner_def v b]
      exact integral_prod_mul (fun x => inner ℂ (u x) (a x)) (fun y => inner ℂ (v y) (b y))

/-- The joint norm of a product state is the product of the one-particle L² norms. -/
theorem norm_product (u v : Remote) : ‖product u v‖ = ‖u‖ * ‖v‖ := by
  have h := inner_product u v u v
  simp only [inner_self_eq_norm_sq_to_K] at h
  have he : ‖product u v‖ ^ 2 = (‖u‖ * ‖v‖) ^ 2 := by
    rw [mul_pow]
    exact_mod_cast h
  simpa [sq_eq_sq_iff_abs_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg u) (norm_nonneg v))] using he

private def outerProduct : Remote →L[ℂ] Remote →L[ℂ] Outer :=
  ((ContinuousLinearMap.lsmul ℂ ℂ (E := Remote)).flip.compLpL₂ 2 volume).flip

private theorem curry_product_eq (u v : Remote) : curry (product u v) = outerProduct u v := by
  apply Lp.ext
  have he : (outerProduct u v : Spatial → Remote) =ᵐ[volume] fun x => u x • v :=
    ((ContinuousLinearMap.lsmul ℂ ℂ (E := Remote)).flip v).coeFn_compLp u
  exact (curry_product u v).trans he.symm

/-- Forming a product wave is a bounded complex bilinear map into the joint scalar space. -/
def productL : Remote →L[ℂ] Remote →L[ℂ] Joint :=
  (LinearMap.mk₂ ℂ product
    (fun u a v => curry.injective (by simp only [map_add, curry_product_eq, add_apply]))
    (fun c u v => curry.injective (by simp only [map_smul, curry_product_eq, smul_apply]))
    (fun u v b => curry.injective (by simp only [map_add, curry_product_eq]))
    (fun c u v => curry.injective (by simp only [map_smul, curry_product_eq]))).mkContinuous₂ 1
      (fun u v => by simp only [LinearMap.mk₂_apply, norm_product, one_mul, le_refl])

/-- Evaluating the bounded bilinear map returns the concrete product wave. -/
theorem productL_apply (u v : Remote) : productL u v = product u v := rfl

end FoliationQM.JointL2Product
