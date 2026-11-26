module

public import FoliationQM.TwoBodyMadelung

/-!
# Local differential Hamiltonians on the two-particle configuration space

Each one-body Hamiltonian acts on its own spatial coordinate at a fixed
physical time. The Laplacians here are computed by twice differentiating
complex waves with respect to their real spatial arguments.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.TwoBodyHamiltonianRealization

open LorentzCoordinates ObserverGaussianFisher TwoBodyCoordinates TwoBodyActionDensity
open scoped BigOperators

/-- The spatial Laplacian of a complex wave in physical Cartesian directions. -/
def lap (f : Spatial → ℂ) (x : Spatial) : ℂ :=
  ∑ i, fderiv ℝ (fun z => fderiv ℝ f z (axes i)) x (axes i)

/-- The one-particle differential Hamiltonian at a fixed time. -/
def one (h m : ℝ) (V : Spatial → ℝ) (f : Spatial → ℂ) (x : Spatial) : ℂ :=
  -((h^2/(2*m) : ℝ) : ℂ) * lap f x + (V x : ℂ) * f x

/-- The joint differential Hamiltonian with local potentials for both particles. -/
def joint (h m₁ m₂ : ℝ) (V₁ V₂ : Spatial → ℝ) (f : Spatial × Spatial → ℂ)
    (p : Spatial × Spatial) : ℂ :=
  -((h^2/(2*m₁) : ℝ) : ℂ) * lap (fun x => f (x,p.2)) p.1 -
    ((h^2/(2*m₂) : ℝ) : ℂ) * lap (fun y => f (p.1,y)) p.2 +
    ((V₁ p.1 + V₂ p.2 : ℝ) : ℂ) * f p

/-- Constant complex multiples factor out of the spatial Laplacian. -/
theorem lap_const_mul {f : Spatial → ℂ} (hf : ContDiff ℝ 2 f) (c : ℂ) (x : Spatial) :
    lap (fun z => c*f z) x = c*lap f x := by
  have hd := hf.differentiable (by decide)
  simp only [lap, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hi : DifferentiableAt ℝ (fun z => fderiv ℝ f z (axes i)) x :=
    PolarRegularity.differentiableAt_directionalDerivative_of_contDiffAt_two hf.contDiffAt (axes i)
  simp only [fun z => fderiv_const_mul (hd z) c, smul_apply, smul_eq_mul,
    fderiv_const_mul hi]

/-- Applying the literal joint Hamiltonian to a separated wave gives the sum
of the two one-particle actions with their respective masses and potentials. -/
theorem joint_product (h m₁ m₂ : ℝ) (V₁ V₂ : Spatial → ℝ) {f g : Spatial → ℂ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (p : Spatial × Spatial) :
    joint h m₁ m₂ V₁ V₂ (fun z => f z.1 * g z.2) p =
      one h m₁ V₁ f p.1 * g p.2 + f p.1 * one h m₂ V₂ g p.2 := by
  have hl : lap (fun x => f x * g p.2) p.1 = g p.2 * lap f p.1 := by
    simpa only [mul_comm (f _) (g p.2)] using lap_const_mul hf (g p.2) p.1
  simp only [joint, one, hl, lap_const_mul hg, Complex.ofReal_add]
  ring

/-- The printed spacetime equation is exactly evolution by this spatial
Hamiltonian on the physical time slice. -/
theorem equation_iff_slice (h m₁ m₂ : ℝ) (V₁ V₂ : Base → ℝ) {ψ : Point → ℂ}
    {t : ℝ} {x y : Spatial} (hψ : ContDiffAt ℝ 2 ψ ((t,x),y)) :
    TwoBodyMadelung.Equation h m₁ m₂ (localPotential V₁ V₂) ψ ((t,x),y) ↔
      Complex.I * (h : ℂ) * deriv (fun s => ψ ((s,x),y)) t =
      joint h m₁ m₂ (fun z => V₁ (t,z)) (fun z => V₂ (t,z))
        (fun z => ψ ((t,z.1),z.2)) (x,y) := by
  rw [(hasDerivAt_time (hψ.differentiableAt (by decide))).deriv]
  simp only [TwoBodyMadelung.Equation, joint, lap, localPotential, lap₁, lap₂,
    left_second hψ, right_second hψ]

end FoliationQM.TwoBodyHamiltonianRealization
