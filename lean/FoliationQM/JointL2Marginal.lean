module

public import FoliationQM.JointL2Curry
public import FoliationQM.ScalarFiberPairing

/-!
# Marginal Born density and flux pairings for joint wave representatives

A scalar wave and a candidate directional derivative in product L² have
integrable mixed current. Fubini identifies the spatial marginal of this
pairing with the inner product of their remote fibers almost everywhere.
The fiber norm of the wave gives the Born marginal with the same total mass.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.JointL2Marginal

open MeasureTheory LorentzCoordinates JointL2Sections
open scoped ComplexConjugate

/-- The first marginal of the Born density is integrable and has the total squared wave norm. -/
theorem marginal_mass {ψ : Spatial × Spatial → ℂ} (hψ : MemLp ψ 2 volume) :
    Integrable (fun x => ∫ y, ‖ψ (x,y)‖ ^ 2) ∧
      (∫ x, ∫ y, ‖ψ (x,y)‖ ^ 2) = ‖hψ.toLp ψ‖ ^ 2 := by
  have hi := ScalarFiberPairing.integrable_born hψ
  exact ⟨hi.integral_prod_left, (integral_prod _ hi).symm.trans (ScalarFiberPairing.norm_sq_toLp hψ).symm⟩

/-- The actual fiber inner product is the scalar marginal overlap integral
for arbitrary representatives of the two global L² classes. -/
theorem marginal_pair_ae {ψ φ : Spatial × Spatial → ℂ} (hψ : MemLp ψ 2 volume)
    (hφ : MemLp φ 2 volume) :
    ∀ᵐ x : Spatial, inner ℂ (JointL2Curry.curry (hψ.toLp ψ) x)
      (JointL2Curry.curry (hφ.toLp φ) x) = ∫ y, star (ψ (x,y)) * φ (x,y) := by
  filter_upwards [JointL2Curry.curry_toLp hψ, JointL2Curry.curry_toLp hφ] with x hx hy
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hx,hy] with y h₁ h₂
  rw [RCLike.inner_apply', h₁, h₂]
  rfl

/-- The diagonal of the curried kernel agrees almost everywhere with the
spatial integral of the Born density of the supplied representative. -/
theorem marginal_density_ae {ψ : Spatial × Spatial → ℂ} (hψ : MemLp ψ 2 volume) :
    ∀ᵐ x : Spatial, ‖JointL2Curry.curry (hψ.toLp ψ) x‖ ^ 2 = ∫ y, ‖ψ (x,y)‖ ^ 2 := by
  filter_upwards [JointL2Curry.curry_toLp hψ] with x hx
  let v : Remote := JointL2Curry.curry (hψ.toLp ψ) x
  have he := JointL2Curry.norm_sq_integral v
  exact he.trans (integral_congr_ae (hx.mono fun _ hy => congrArg (fun c : ℂ => ‖c‖ ^ 2) hy))

/-- Two joint square-integrable profiles give an integrable scalar marginal
current. A joint spatial derivative can be used as the second profile. -/
theorem current_integrable (hbar m : ℝ) {ψ φ : Spatial × Spatial → ℂ}
    (hψ : MemLp ψ 2 volume) (hφ : MemLp φ 2 volume) :
    Integrable (fun x => (hbar / m) * ∫ y, (star (ψ (x,y)) * φ (x,y)).im) := by
  have h := ScalarFiberPairing.integrable_pair hψ hφ
  exact h.im.integral_prod_left.const_mul _

end FoliationQM.JointL2Marginal
