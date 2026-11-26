module

public import FoliationQM.LatticeDuhamel
public import FoliationQM.LatticeResidualHilbertNorm
public import FoliationQM.LatticeSchrodingerReconstruction

/-!
# Comparison of the regularized polar wave and exact Neumann evolution

Along an actual solution of the regularized amplitude and lag equations, the
reconstructed Hilbert-space wave solves the inhomogeneous Schrödinger equation.
The forcing is continuous through nodes for each positive regulator width.
Integrating its norm bounds the error from exact propagation of the same
initial wave. On a fixed grid and an interval separated from nodes, an upper
bound on the radial stencil gives an explicit error quadratic in the width.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LatticePolarTrajectoryError

open LatticeRegularizedFlow LatticeLagHamiltonian LatticeComplexEnergy LatticeUnitaryPropagator
open LatticeNeumannMatrix LatticeSchrodingerResidual LatticeSchrodingerReconstruction
open LatticeResidualHilbertNorm LatticeClockRegularization LatticePolarStencil
open Set MeasureTheory WithLp

/-- Signed reconstruction of the lag state as a complex Euclidean site vector. -/
def hilbertWave {n : ℕ} (p : MassiveParameters) (x : State n) : Space n :=
  toLp 2 (wave x.1 (lagPhase p x.2))

private theorem generator_sites {n : ℕ} (p : MassiveParameters) (h : ℝ) (V : Fin n → ℝ)
    (z : Fin n → ℂ) : toLp 2 (schrodinger p h V z) = generator p h V (toLp 2 z) := by
  apply ofLp_injective
  funext i
  change -Complex.I * LatticeNeumannHamiltonian.frequency p h V z i =
    -Complex.I * ofLp (ham p h V (toLp 2 z)) i
  rw [ham, Matrix.ofLp_toEuclideanCLM, ofLp_toLp, frequencyMatrix_mulVec]

/-- The actual signed wave has generator velocity plus the explicitly computed
forcing at every site, also when some amplitudes vanish. -/
theorem hilbert_wave_derivative {n : ℕ} (p : MassiveParameters) (h ε : ℝ) (V : Fin n → ℝ)
    (γ : ℝ → State n) (t : ℝ) (hε : 0 < ε) (hγ : HasDerivAt γ (field p h ε V (γ t)) t) :
    HasDerivAt (fun s => hilbertWave p (γ s))
      (generator p h V (hilbertWave p (γ t)) +
        residualState p h ε (γ t).1 (lagPhase p (γ t).2)) t := by
  let lift := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℂ)).symm
  have hd := lift.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
    (wave_path_with_residual p h ε V γ t (fun _ => Or.inr hε.ne') hγ)
  apply hd.congr_deriv
  change toLp 2 (_ + _) = _
  rw [toLp_add, generator_sites]
  rfl

/-- The Hilbert forcing varies continuously with the joint polar state for
a positive regulator, including on its nodal set. -/
theorem residual_continuous {n : ℕ} (p : MassiveParameters) (h ε : ℝ) (hε : 0 < ε) :
    Continuous (fun x : State n => residualState p h ε x.1 (lagPhase p x.2)) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin n => ℂ)).comp
  apply continuous_pi
  intro i
  unfold LatticeSchrodingerResidual.residual lagPhase phase defectFraction radial
  have hden (x : State n) : (x.1 i)^2 + ε^2 ≠ 0 :=
    (denominator_pos ε (x.1 i) (Or.inr hε.ne')).ne'
  fun_prop (disch := assumption)

/-- Variation of constants for the actual regularized trajectory starting at a.
The interval integral transports each explicitly reconstructed residual to b. -/
theorem variation_of_constants {n : ℕ} (p : MassiveParameters) (h ε : ℝ) (V : Fin n → ℝ)
    (γ : ℝ → State n) {a b : ℝ} (hab : a ≤ b) (hε : 0 < ε)
    (hγ : ∀ t ∈ Icc a b, HasDerivAt γ (field p h ε V (γ t)) t) :
    hilbertWave p (γ b) - propagator p h V (b-a) (hilbertWave p (γ a)) =
      ∫ t in a..b, propagator p h V (b-t)
        (residualState p h ε (γ t).1 (lagPhase p (γ t).2)) := by
  have hd t ht := hilbert_wave_derivative p h ε V γ t hε (hγ t ht)
  apply LatticeDuhamel.duhamel p h V _ _ hab
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => hd t (Ioo_subset_Icc_self ht))
  exact (residual_continuous p h ε hε).comp_continuousOn
    (fun t ht => (hγ t ht).continuousAt.continuousWithinAt)

/-- From identical initial data, exact unitary propagation differs from the
regularized polar wave by at most the integral of the forcing norm. -/
theorem integral_bound {n : ℕ} (p : MassiveParameters) (h ε : ℝ) (V : Fin n → ℝ)
    (γ : ℝ → State n) {a b : ℝ} (hab : a ≤ b) (hε : 0 < ε)
    (hγ : ∀ t ∈ Icc a b, HasDerivAt γ (field p h ε V (γ t)) t) :
    ‖hilbertWave p (γ b) - propagator p h V (b-a) (hilbertWave p (γ a))‖ ≤
      ∫ t in a..b, ‖residualState p h ε (γ t).1 (lagPhase p (γ t).2)‖ := by
  have hd t ht := hilbert_wave_derivative p h ε V γ t hε (hγ t ht)
  apply LatticeDuhamel.integral_bound p h V _ _ _ hab
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => hd t (Ioo_subset_Icc_self ht)) (fun _ _ => le_rfl)
  exact ((residual_continuous p h ε hε).comp_continuousOn
    (fun t ht => (hγ t ht).continuousAt.continuousWithinAt)).norm.intervalIntegrable_of_Icc hab

/-- An amplitude floor δ and radial stencil norm bound M on the time interval
yield a trajectory error proportional to its length and to ε²/δ². -/
theorem away_bound {n : ℕ} (p : MassiveParameters) (h ε : ℝ) (V : Fin n → ℝ)
    (γ : ℝ → State n) {a b δ M : ℝ} (hab : a ≤ b) (hε : 0 < ε) (hδ : 0 < δ)
    (hγ : ∀ t ∈ Icc a b, HasDerivAt γ (field p h ε V (γ t)) t)
    (haway : ∀ t ∈ Icc a b, ∀ i, δ ≤ |(γ t).1 i|)
    (hM : ∀ t ∈ Icc a b, radialNorm (γ t).1 (lagPhase p (γ t).2) ≤ M) :
    ‖hilbertWave p (γ b) - propagator p h V (b-a) (hilbertWave p (γ a))‖ ≤
      (b-a) * (p.ellC*p.c/(2*h^2)) * (ε^2/δ^2) * M := by
  have hd t ht := hilbert_wave_derivative p h ε V γ t hε (hγ t ht)
  let C := (p.ellC*p.c/(2*h^2)) * (ε^2/δ^2) * M
  have hn (t : ℝ) (ht : t ∈ Ioo a b) :
      ‖residualState p h ε (γ t).1 (lagPhase p (γ t).2)‖ ≤ C := by
    have ht' := Ioo_subset_Icc_self ht
    apply (norm_residualState_le p h ε δ _ _ hδ (haway t ht')).trans
    exact mul_le_mul_of_nonneg_left (hM t ht') (by positivity [ClockScales.ellC_pos p, p.c_pos])
  have hb := LatticeDuhamel.uniform_bound p h V _ _ C hab
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => hd t (Ioo_subset_Icc_self ht)) hn
  convert hb using 1
  unfold C
  ring

end FoliationQM.LatticePolarTrajectoryError
