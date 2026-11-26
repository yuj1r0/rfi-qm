module

public import FoliationQM.GaussianPositiveFrequencyPacket
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Noncompact initial support of the actual Gaussian packet

Source: v13 rem:wkb_rates_tails, Gaussian clause. Kind C.
The previously constructed positive-frequency Klein–Gordon packet has the
strictly positive Gaussian as its actual initial spatial value. These results
concern that initial wave support. Current positivity, transported probability
densities and uniform dynamical controls retain their separate hypotheses.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.GaussianPacketSupport
open LorentzCoordinates OsmoticSliceFields GaussianPositiveFrequencyPacket

/-- The actual positive-frequency packet is nonzero everywhere on its initial slice. -/
theorem initial_ne_zero (μ : ℝ) {σ : ℝ} (hσ : 0 < σ) (y : Spatial) :
    packet μ σ (slicePoint 0 y) ≠ 0 := by
  rw [initial_value μ hσ y]
  exact Complex.ofReal_ne_zero.mpr (GaussianCauchySlice.amplitude_pos σ y).ne'

/-- The actual initial wave has full spatial function support. -/
theorem initial_support_eq_univ (μ : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    Function.support (fun y : Spatial => packet μ σ (slicePoint 0 y)) = Set.univ :=
  Function.support_eq_univ (initial_ne_zero μ hσ)

/-- Its closed spatial support is also the entire space. -/
theorem initial_tsupport_eq_univ (μ : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    tsupport (fun y : Spatial => packet μ σ (slicePoint 0 y)) = Set.univ := by
  rw [tsupport, initial_support_eq_univ μ hσ, closure_univ]

/-- The actual initial Gaussian wave cannot have compact spatial support. -/
theorem initial_not_hasCompactSupport (μ : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    ¬ HasCompactSupport (fun y : Spatial => packet μ σ (slicePoint 0 y)) := by
  rw [HasCompactSupport, initial_tsupport_eq_univ μ hσ]
  exact noncompact_univ Spatial

end FoliationQM.GaussianPacketSupport
