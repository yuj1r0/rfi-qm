module

public import FoliationQM.LorentzCoordinates
public import FoliationQM.FisherNormalization
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Spatial marginals and normalized two-particle conditional densities

V13 lines 1186–1196 in the source file define the first marginal by
integration over the second spatial coordinate at a fixed time. The
conditional integrates to one on each integrable positive-mass fiber.
Fubini gives both marginals their joint total mass, and supplies
fiber integrability almost everywhere for a jointly integrable density.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.TwoParticleMarginals

open LorentzCoordinates MeasureTheory

/-- Marginal density of the first particle on its full spatial slice. -/
def left (f : Spatial × Spatial → ℝ) (x : Spatial) : ℝ := ∫ y, f (x,y)

/-- Marginal density of the second particle on its full spatial slice. -/
def right (f : Spatial × Spatial → ℝ) (y : Spatial) : ℝ := ∫ x, f (x,y)

/-- Conditional density of the second spatial coordinate given the first. -/
def conditional (f : Spatial × Spatial → ℝ) (x y : Spatial) : ℝ := f (x,y) / left f x

/-- Exchange the two particle labels in the joint density. -/
def swap (f : Spatial × Spatial → ℝ) (z : Spatial × Spatial) : ℝ := f z.swap

/-- Applying the label exchange twice returns the joint density. -/
theorem swap_swap (f : Spatial × Spatial → ℝ) : swap (swap f) = f := rfl

/-- The left marginal of the exchanged density is the original right marginal. -/
theorem left_swap (f : Spatial × Spatial → ℝ) : left (swap f) = right f := rfl

/-- The right marginal of the exchanged density is the original left marginal. -/
theorem right_swap (f : Spatial × Spatial → ℝ) : right (swap f) = left f := rfl

/-- Swapping labels normalizes the first coordinate by the original right marginal. -/
theorem conditional_swap (f : Spatial × Spatial → ℝ) (x y : Spatial) :
    conditional (swap f) y x = f (x,y) / right f y := rfl

/-- Label exchange preserves the joint spatial mass. -/
theorem integral_swap (f : Spatial × Spatial → ℝ) : (∫ z, swap f z) = ∫ z, f z :=
  integral_prod_swap f

/-- Joint integrability yields integrability of both marginal functions. -/
theorem integrable_marginals (f : Spatial × Spatial → ℝ) (hf : Integrable f) :
    Integrable (left f) ∧ Integrable (right f) := ⟨hf.integral_prod_left, hf.integral_prod_right⟩

/-- The first marginal has the same total mass as the joint density. -/
theorem integral_left (f : Spatial × Spatial → ℝ) (hf : Integrable f) :
    (∫ x, left f x) = ∫ z, f z := (integral_prod f hf).symm

/-- The second marginal also has total mass equal to that of the joint density. -/
theorem integral_right (f : Spatial × Spatial → ℝ) (hf : Integrable f) :
    (∫ y, right f y) = ∫ z, f z := (integral_prod_symm f hf).symm

private theorem integral_pos_of_pos (d : Spatial → ℝ) (hi : Integrable d) (hp : ∀ y, 0 < d y) :
    0 < ∫ y, d y := by
  apply (integral_pos_iff_support_of_nonneg (fun y => (hp y).le) hi).2
  have hs : Function.support d = Set.univ := by ext y; simp [(hp y).ne']
  rw [hs]
  exact Measure.measure_univ_pos.mpr (NeZero.ne volume)

/-- An integrable strictly positive fiber has a positive first marginal at that point. -/
theorem left_pos (f : Spatial × Spatial → ℝ) (x : Spatial)
    (hi : Integrable (fun y => f (x,y))) (hp : ∀ y, 0 < f (x,y)) : 0 < left f x :=
  integral_pos_of_pos _ hi hp

/-- An integrable strictly positive fiber in the first coordinate gives a positive right marginal. -/
theorem right_pos (f : Spatial × Spatial → ℝ) (y : Spatial)
    (hi : Integrable (fun x => f (x,y))) (hp : ∀ x, 0 < f (x,y)) : 0 < right f y :=
  integral_pos_of_pos _ hi hp

/-- The conditional fiber remains integrable after division by its marginal. -/
theorem integrable_conditional (f : Spatial × Spatial → ℝ) (x : Spatial)
    (hi : Integrable (fun y => f (x,y))) : Integrable (conditional f x) := hi.div_const _

/-- At each integrable fiber of positive mass, the conditional is an actual unit-mass density. -/
theorem integral_conditional (f : Spatial × Spatial → ℝ) (x : Spatial)
    (hi : Integrable (fun y => f (x,y))) (hm : 0 < left f x) : (∫ y, conditional f x y) = 1 :=
  FisherNormalization.integral_normalizedDensity hi hm rfl

/-- The joint density is the marginal times the conditional at each point above positive mass. -/
theorem factorization (f : Spatial × Spatial → ℝ) (x y : Spatial) (hm : 0 < left f x) :
    f (x,y) = left f x * conditional f x y := by
  unfold conditional
  field_simp [hm.ne']

/-- Joint integrability and strict positivity yield normalized conditionals almost everywhere.
The distinguished first coordinate need not have been assigned an individual integrability proof. -/
theorem ae_conditional_normalized (f : Spatial × Spatial → ℝ) (hf : Integrable f)
    (hp : ∀ x y, 0 < f (x,y)) :
    ∀ᵐ x, 0 < left f x ∧ Integrable (conditional f x) ∧ (∫ y, conditional f x y) = 1 := by
  filter_upwards [hf.prod_right_ae] with x hx
  have hm := left_pos f x hx (hp x)
  exact ⟨hm, integrable_conditional f x hx, integral_conditional f x hx hm⟩

end FoliationQM.TwoParticleMarginals
