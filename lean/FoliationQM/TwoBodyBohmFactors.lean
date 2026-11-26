module

public import FoliationQM.ObserverGaussianFisher
public import FoliationQM.PolarRegularity

/-!
# Product amplitudes in the two-particle Bohm potential

At fixed physical time, the Cartesian Laplacians in v13 `eq:Q12_bohm`
act separately on the two spatial positions. For a marginal amplitude
`A(x)` times a conditional amplitude `B(x,y)`, the first Laplacian produces
the printed conditional curvature and mixed logarithmic-gradient terms.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.TwoBodyBohmFactors

open LorentzCoordinates ObserverGaussianFisher
open scoped Topology BigOperators

/-- A single Cartesian spatial derivative, evaluated at its physical position. -/
def d (i : Fin 3) (f : Spatial → ℝ) (x : Spatial) : ℝ := fderiv ℝ f x (axes i)

/-- The sum of the three genuine Cartesian second partials on the physical spatial slice. -/
def lap (f : Spatial → ℝ) (x : Spatial) : ℝ := ∑ i, d i (d i f) x

/-- A one-particle Bohm potential in the amplitude coordinate. -/
def one (h m : ℝ) (a : Spatial → ℝ) (x : Spatial) : ℝ :=
  -(h ^ 2 / (2 * m)) * (lap a x / a x)

/-- The fixed-time configuration-space Bohm potential with separate particle masses. -/
def configQ (h m₁ m₂ : ℝ) (R : Spatial × Spatial → ℝ) (x y : Spatial) : ℝ :=
  one h m₁ (fun u => R (u,y)) x + one h m₂ (fun v => R (x,v)) y

/-- The extra curvature and mixed gradient terms from the first-particle
dependence of a conditional remote amplitude. -/
def cross (h m : ℝ) (A : Spatial → ℝ) (B : Spatial × Spatial → ℝ) (x y : Spatial) : ℝ :=
  -(h ^ 2 / (2 * m)) * (lap (fun u => B (u,y)) x / B (x,y) +
    2 * ∑ i, (d i A x / A x) * (d i (fun u => B (u,y)) x / B (x,y)))

private theorem d_mul (i : Fin 3) {f g : Spatial → ℝ} {x : Spatial}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    d i (fun z => f z * g z) x = d i f x * g x + f x * d i g x := by
  simp only [d, fderiv_fun_mul hf hg, add_apply, smul_apply, smul_eq_mul]
  ring

private theorem dd_mul (i : Fin 3) {f g : Spatial → ℝ} {x : Spatial}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    d i (d i (fun z => f z * g z)) x =
      d i (d i f) x * g x + f x * d i (d i g) x + 2 * (d i f x * d i g x) := by
  have he : d i (fun z => f z * g z) =ᶠ[𝓝 x] fun z => d i f z * g z + f z * d i g z := by
    filter_upwards [PolarRegularity.eventually_differentiableAt_of_contDiffAt_two hf,
      PolarRegularity.eventually_differentiableAt_of_contDiffAt_two hg] with z hzf hzg
    exact d_mul i hzf hzg
  have hf₁ := hf.differentiableAt (by norm_num)
  have hg₁ := hg.differentiableAt (by norm_num)
  have df : DifferentiableAt ℝ (d i f) x :=
    PolarRegularity.differentiableAt_directionalDerivative_of_contDiffAt_two hf (axes i)
  have dg : DifferentiableAt ℝ (d i g) x :=
    PolarRegularity.differentiableAt_directionalDerivative_of_contDiffAt_two hg (axes i)
  change fderiv ℝ (d i (fun z => f z * g z)) x (axes i) = _
  rw [he.fderiv_eq, fderiv_fun_add (df.fun_mul hg₁) (hf₁.fun_mul dg), add_apply]
  change d i (fun z => d i f z * g z) x + d i (fun z => f z * d i g z) x = _
  rw [d_mul i df hg₁, d_mul i hf₁ dg]
  ring

/-- The product rule for the genuine three-dimensional Laplacian at a C² point. -/
theorem lap_mul {f g : Spatial → ℝ} {x : Spatial} (hf : ContDiffAt ℝ 2 f x)
    (hg : ContDiffAt ℝ 2 g x) : lap (fun z => f z * g z) x =
      lap f x * g x + f x * lap g x + 2 * ∑ i, d i f x * d i g x := by
  simp only [lap, fun i => dd_mul i hf hg, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]

private theorem d_const_mul (c : ℝ) (f : Spatial → ℝ) (i : Fin 3) (x : Spatial) :
    d i (fun z => c * f z) x = c * d i f x := by
  change (fderiv ℝ (c • f) x) (axes i) = _
  rw [fderiv_const_smul_field]
  rfl

/-- A constant spatial amplitude factor scales the Laplacian by the same constant. -/
theorem lap_const_mul (c : ℝ) (f : Spatial → ℝ) (x : Spatial) :
    lap (fun z => c * f z) x = c * lap f x := by
  simp only [lap, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [show d i (fun z => c * f z) = fun z => c * d i f z from funext (d_const_mul c f i)]
  exact d_const_mul c (d i f) i x

private theorem one_const_mul (h m c : ℝ) (f : Spatial → ℝ) (x : Spatial) (hc : c ≠ 0) :
    one h m (fun z => c * f z) x = one h m f x := by
  simp only [one, lap_const_mul, mul_div_mul_left _ _ hc]

/-- The Bohm potential of a marginal times a conditional amplitude has the two
single-coordinate contributions and the exact cross term displayed in v13. -/
theorem conditional_product (h m₁ m₂ : ℝ) (A : Spatial → ℝ) (B : Spatial × Spatial → ℝ)
    (x y : Spatial) (hA : ContDiffAt ℝ 2 A x)
    (hB : ContDiffAt ℝ 2 (fun u => B (u,y)) x) (ha : A x ≠ 0) (hb : B (x,y) ≠ 0) :
    configQ h m₁ m₂ (fun z => A z.1 * B z) x y =
      one h m₁ A x + one h m₂ (fun v => B (x,v)) y + cross h m₁ A B x y := by
  let b := fun u => B (u,y)
  have hs : (∑ i, (d i A x / A x) * (d i b x / b x)) =
      (∑ i, d i A x * d i b x) / (A x * b x) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => div_mul_div_comm _ _ _ _
  change one h m₁ (fun u => A u * b u) x + one h m₂ (fun v => A x * B (x,v)) y = _
  rw [one_const_mul h m₂ (A x) _ y ha]
  suffices he : one h m₁ (fun u => A u * b u) x = one h m₁ A x + cross h m₁ A B x y by
    rw [he]
    ring
  change -(h^2 / (2*m₁)) * (lap (fun u => A u * b u) x / (A x * b x)) =
    -(h^2 / (2*m₁)) * (lap A x / A x) +
      -(h^2 / (2*m₁)) * (lap b x / b x + 2 * ∑ i, (d i A x/A x) * (d i b x/b x))
  rw [lap_mul hA hB, hs]
  generalize -(h^2 / (2*m₁)) = k
  have hb' : b x ≠ 0 := hb
  field_simp [ha, hb']
  ring

/-- A remote-only conditional amplitude has zero correction from the first spatial sector. -/
theorem cross_separable (h m : ℝ) (A B : Spatial → ℝ) (x y : Spatial) :
    cross h m A (fun z => B z.2) x y = 0 := by
  have hc (i : Fin 3) (c : ℝ) : d i (fun _ => c) = fun _ => 0 := by
    funext z
    simp [d]
  simp [cross, lap, hc]

/-- At nonzero factors the joint potential for a separable amplitude is the
sum of the two one-particle Bohm potentials. -/
theorem separable (h m₁ m₂ : ℝ) (A B : Spatial → ℝ) (x y : Spatial)
    (ha : A x ≠ 0) (hb : B y ≠ 0) :
    configQ h m₁ m₂ (fun z => A z.1 * B z.2) x y = one h m₁ A x + one h m₂ B y := by
  change one h m₁ (fun u => A u * B y) x + one h m₂ (fun v => A x * B v) y = _
  simp_rw [mul_comm (A _) (B y)]
  rw [one_const_mul h m₁ (B y) A x hb, one_const_mul h m₂ (A x) B y ha]

end FoliationQM.TwoBodyBohmFactors
