module

public import FoliationQM.LatticePolarTrajectoryError
public import FoliationQM.LatticeUnitaryTrajectory

/-!
# Rectangular wave error for a family of regulator widths

The distance is computed on the raw complex wave and the exact Neumann
trajectory with its own initial data. Positive mesh spacing converts the
Euclidean site norm to the solver's rectangular norm. Uniform separation
from nodes and a bounded radial stencil yield an error quadratic in the
regulator on a fixed grid and fixed time interval.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LatticeRectangularTrajectoryError

open LatticeUnitaryPropagator LatticeUnitaryTrajectory LatticeRegularizedFlow
open LatticePolarTrajectoryError LatticeResidualHilbertNorm LatticeComplexEnergy LatticeLagHamiltonian
open Asymptotics Filter Set

/-- Distance between two raw site profiles in the rectangular sampling measure. -/
def rectangularDistance {n : ℕ} (h : ℝ) (z w : Fin n → ℂ) : ℝ :=
  Real.sqrt (h * ∑ i, Complex.normSq (z i - w i))

/-- The rectangular distance is √h times the Euclidean distance of the same profiles. -/
theorem distance_eq {n : ℕ} {h : ℝ} (hh : 0 ≤ h) (z w : Fin n → ℂ) :
    rectangularDistance h z w = Real.sqrt h * ‖WithLp.toLp 2 z - WithLp.toLp 2 w‖ := by
  rw [rectangularDistance, Real.sqrt_mul hh, EuclideanSpace.norm_eq]
  simp only [Complex.normSq_eq_norm_sq]
  rfl

/-- Raw rectangular wave error relative to the unitary solution from the same initial profile. -/
def waveError {n : ℕ} (p : MassiveParameters) (h : ℝ) (V : Fin n → ℝ)
    (γ : ℝ → State n) (a b : ℝ) : ℝ :=
  rectangularDistance h (wave (γ b).1 (lagPhase p (γ b).2))
    (trajectory p h V (wave (γ a).1 (lagPhase p (γ a).2)) (b-a))

/-- A fixed finite time interval with amplitude floor δ and radial-stencil
norm bound M gives an explicit weighted trajectory error. -/
theorem waveError_le {n : ℕ} (p : MassiveParameters) {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε)
    (V : Fin n → ℝ) (γ : ℝ → State n) {a b δ M : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (hγ : ∀ t ∈ Icc a b, HasDerivAt γ (field p h ε V (γ t)) t)
    (hr : ∀ t ∈ Icc a b, ∀ i, δ ≤ |(γ t).1 i|)
    (hM : ∀ t ∈ Icc a b, radialNorm (γ t).1 (lagPhase p (γ t).2) ≤ M) :
    waveError p h V γ a b ≤ Real.sqrt h * (b-a) * (p.ellC*p.c/(2*h^2)) * M / δ^2 * ε^2 := by
  rw [waveError, distance_eq hh.le]
  have he := LatticePolarTrajectoryError.away_bound p h ε V γ hab hε hδ hγ hr hM
  calc
    _ ≤ Real.sqrt h * ((b-a) * (p.ellC*p.c/(2*h^2)) * (ε^2/δ^2) * M) :=
      mul_le_mul_of_nonneg_left he (Real.sqrt_nonneg _)
    _ = _ := by ring

/-- On a fixed grid, a family of genuine regularized solutions with a uniform
amplitude floor and stencil bound has rectangular wave error O(ε²). Each
reference evolution starts at the corresponding member's own initial wave. -/
theorem family_error {n : ℕ} {ι : Type*} (l : Filter ι) (p : MassiveParameters)
    {h : ℝ} (hh : 0 < h) (V : Fin n → ℝ) (ε : ι → ℝ) (γ : ι → ℝ → State n)
    {a b δ M : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (hf : ∀ᶠ k in l, 0 < ε k ∧
      (∀ t ∈ Icc a b, HasDerivAt (γ k) (field p h (ε k) V (γ k t)) t) ∧
      (∀ t ∈ Icc a b, ∀ i, δ ≤ |(γ k t).1 i|) ∧
      (∀ t ∈ Icc a b, radialNorm (γ k t).1 (lagPhase p (γ k t).2) ≤ M)) :
    (fun k => waveError p h V (γ k) a b) =O[l] (fun k => (ε k)^2) := by
  apply IsBigO.of_bound (Real.sqrt h * (b-a) * (p.ellC*p.c/(2*h^2)) * M / δ^2)
  filter_upwards [hf] with k hk
  have hn : 0 ≤ waveError p h V (γ k) a b := Real.sqrt_nonneg _
  simpa only [Real.norm_of_nonneg hn, Real.norm_of_nonneg (sq_nonneg _)] using
    waveError_le p hh hk.1 V (γ k) hab hδ hk.2.1 hk.2.2.1 hk.2.2.2

end FoliationQM.LatticeRectangularTrajectoryError
