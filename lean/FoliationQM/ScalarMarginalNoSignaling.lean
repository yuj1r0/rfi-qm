module

public import FoliationQM.JointMarginalHistory
public import FoliationQM.DecoupledPropagator
public import FoliationQM.SchwartzFiberDerivative

/-!
# Equality of the scalar marginal integrals at every retained position

For two choices of the remote propagator, differentiable Schwartz-valued
representatives identify the Hilbert observables with the physical scalar
integrals. The two waves can have different wave functions at each time.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.ScalarMarginalNoSignaling

open MeasureTheory LorentzCoordinates JointL2Sections JointSubsystemUnitary
open JointRemoteUnitary JointMarginalHistory SchwartzFiberDerivative HilbertFiberObservables

/-- The joint scalar wave obtained by evaluating each retained-position Schwartz fiber. -/
def field (S : Spatial → Fiber) (z : Spatial × Spatial) : ℂ := S z.1 z.2

/-- For differentiable Schwartz fibers, a joint L² class determines the stated
continuous fiber representative at every retained position. -/
theorem represents {S : Spatial → Fiber} (hs : Differentiable ℝ S)
    (hi : MemLp (field S) 2 volume) :
    Represents (hi.toLp (field S)) (hilbertWave S) := by
  constructor
  · exact continuous_iff_continuousAt.mpr fun x => (hasFDerivAt_hilbertWave S (hs x)).continuousAt
  · filter_upwards [JointL2Curry.curry_toLp hi] with x hx
    exact Lp.ext (((S x).coeFn_toLp 2 volume).trans hx.symm)

/-- Comparing two remote choices gives pointwise equality of the scalar Born
and directional current integrals at every regular retained position. -/
theorem scalar_integrals (U V W : Remote ≃ₗᵢ[ℂ] Remote) (ψ : Joint)
    (S T : Spatial → Fiber) (hs : Differentiable ℝ S) (ht : Differentiable ℝ T)
    (hi : MemLp (field S) 2 volume) (hj : MemLp (field T) 2 volume)
    (hS : hi.toLp (field S) = factor U V ψ) (hT : hj.toLp (field T) = factor U W ψ)
    (hbar m : ℝ) (x v : Spatial) :
    (∫ y, ‖S x y‖^2) = (∫ y, ‖T x y‖^2) ∧
      (hbar / m) * (∫ y, (star (S x y) * fderiv ℝ (fun z => S z y) x v).im) =
      (hbar / m) * (∫ y, (star (T x y) * fderiv ℝ (fun z => T z y) x v).im) := by
  have rs := represents hs hi
  have rt := represents ht hj
  rw [hS] at rs
  rw [hT] at rt
  let R := V.symm.trans W
  have hr : remote R (factor U V ψ) = factor U W ψ := by
    change remote (V.symm.trans W) (remote V (retained U ψ)) = remote W (retained U ψ)
    rw [remote_trans, remote_symm]
    simp
  have hf : hilbertWave T = fun z => R (hilbertWave S z) := by
    apply Measure.eq_of_ae_eq (μ := volume) _ rt.continuous (R.continuous.comp rs.continuous)
    have h := curry_remote R (factor U V ψ)
    rw [hr] at h
    exact (rt.coe_eq.trans h).trans (rs.coe_eq.symm.fun_comp R)
  constructor
  · rw [← ScalarFiberPairing.norm_sq_toLp ((S x).memLp 2 volume),
      ← ScalarFiberPairing.norm_sq_toLp ((T x).memLp 2 volume)]
    change ‖hilbertWave S x‖^2 = ‖hilbertWave T x‖^2
    rw [hf, R.norm_map]
  · rw [← current_eq_integral hbar m S (hs x), ← current_eq_integral hbar m T (ht x), hf]
    exact (current_isometry R.toLinearIsometry hbar m (hilbertWave S)
      (hasFDerivAt_hilbertWave S (hs x)).differentiableAt v).symm

/-- At each time the true scalar marginal integrals agree for two different
remote Hamiltonians whose joint evolutions satisfy the decoupled strong
equations on dense domains and have the same retained propagator. -/
theorem generated_histories {hbar s : ℝ}
    {A B C : ℝ → Remote →ₗ.[ℂ] Remote} {H K : ℝ → Joint →ₗ.[ℂ] Joint}
    {U V W : ℝ → Remote ≃ₗᵢ[ℂ] Remote} {P Q : ℝ → Joint ≃ₗᵢ[ℂ] Joint}
    (hP : DecoupledPropagator.EvolutionOn hbar s Set.univ A B H U V P)
    (hQ : DecoupledPropagator.EvolutionOn hbar s Set.univ A C K U W Q)
    (ψ : Joint) (S T : ℝ → Spatial → Fiber)
    (hs : ∀ t, Differentiable ℝ (S t)) (ht : ∀ t, Differentiable ℝ (T t))
    (hi : ∀ t, MemLp (field (S t)) 2 volume) (hj : ∀ t, MemLp (field (T t)) 2 volume)
    (hS : ∀ t, (hi t).toLp (field (S t)) = P t ψ)
    (hT : ∀ t, (hj t).toLp (field (T t)) = Q t ψ)
    (m : ℝ) (x v : Spatial) :
    (fun t => (∫ y, ‖S t x y‖^2, (hbar/m) * ∫ y, (star (S t x y) *
      fderiv ℝ (fun z => S t z y) x v).im)) =
    (fun t => (∫ y, ‖T t x y‖^2, (hbar/m) * ∫ y, (star (T t x y) *
      fderiv ℝ (fun z => T t z y) x v).im)) := by
  funext t
  have hp := hS t
  have hq := hT t
  rw [DecoupledPropagator.factorization hP t] at hp
  rw [DecoupledPropagator.factorization hQ t] at hq
  obtain ⟨hρ, hj'⟩ := scalar_integrals (U t) (V t) (W t) ψ (S t) (T t) (hs t) (ht t)
    (hi t) (hj t) hp hq hbar m x v
  exact Prod.ext hρ hj'

end FoliationQM.ScalarMarginalNoSignaling
