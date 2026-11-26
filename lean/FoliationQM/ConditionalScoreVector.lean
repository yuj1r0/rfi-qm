module

public import FoliationQM.ConditionalScoreCentering
public import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Vector form of the conditional-score identity

The three coordinate components below implement the spatial gradient
in v13 Eq. `eq:score_zero`. The vector Bochner integrals are integrable
at every first-particle coordinate, and their components are the
derivatives of the conditional normalization in those directions.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.ConditionalScoreVector

open MeasureTheory LorentzCoordinates TwoParticleMarginals MarginalDifferentiation ConditionalScoreCentering

variable {f : Spatial × Spatial → ℝ}

/-- Coordinate gradient in the conditioning particle's spatial coordinates. -/
def gradient (p : Spatial → ℝ) (x : Spatial) : Spatial :=
  fun i => fderiv ℝ p x (Pi.single i 1)

/-- Vector form of the source identity, including integrability and actual
differentiation of the normalized conditional integral. -/
theorem mean_score (H : Regular f) (x : Spatial) :
    let q := conditional f
    let s := fun y => q x y • gradient (fun u => Real.log (q u y)) x
    let d := fun y => gradient (fun u => q u y) x
    Integrable s ∧ Integrable d ∧
      (∫ y, s y) = ∫ y, d y ∧
      (∫ y, d y) = gradient (fun u => ∫ y, q u y) x ∧
      gradient (fun u => ∫ y, q u y) x = 0 := by
  let s := fun y => conditional f x y • gradient (fun u => Real.log (conditional f u y)) x
  let d := fun y => gradient (fun u => conditional f u y) x
  have hs (i : Fin 3) : Integrable (fun y => s y i) := integrable_conditional_score H x (Pi.single i 1)
  have hd (i : Fin 3) : Integrable (fun y => d y i) := integrable_condD H x (Pi.single i 1)
  have hs0 : (∫ y, s y) = 0 := by
    ext i
    exact (eval_integral hs i).trans (integral_conditional_score H x (Pi.single i 1))
  have hd0 : (∫ y, d y) = 0 := by
    ext i
    exact (eval_integral hd i).trans (integral_condD H x (Pi.single i 1))
  have hmass : (fun u => ∫ y, conditional f u y) = fun _ => 1 := by
    funext u
    exact integral_conditional f u (H.left_fiber u) (left_pos f u (H.left_fiber u) (fun y => H.pos (u,y)))
  have hz : gradient (fun u => ∫ y, conditional f u y) x = 0 := by
    rw [hmass]
    funext i
    simp [gradient]
  exact ⟨Integrable.of_eval hs, Integrable.of_eval hd, hs0.trans hd0.symm, hd0.trans hz.symm, hz⟩

/-- Against the joint weight the centered conditional score has zero
fiber integral even after multiplication by a first-particle observable.
This is the vanishing mixed term in the Fisher decomposition. -/
theorem centered_observable (H : Regular f) (a : Spatial → ℝ) (x v : Spatial) :
    Integrable (fun y => f (x,y) * a x * condScore f x y v) ∧
      (∫ y, f (x,y) * a x * condScore f x y v) = 0 := by
  have hpos := left_pos f x (H.left_fiber x) (fun y => H.pos (x,y))
  have he : (fun y => f (x,y) * a x * condScore f x y v) =
      fun y => (left f x * a x) * (conditional f x y * condScore f x y v) := by
    funext y
    calc
      _ = (left f x * conditional f x y) * a x * condScore f x y v :=
        congrArg (fun t => t * a x * condScore f x y v) (factorization f x y hpos)
      _ = _ := by ring
  rw [he, integral_const_mul, integral_conditional_score H, mul_zero]
  exact ⟨(integrable_conditional_score H x v).const_mul _, rfl⟩

end FoliationQM.ConditionalScoreVector
