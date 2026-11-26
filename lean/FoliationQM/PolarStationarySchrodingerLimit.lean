module

public import FoliationQM.RelativeStationarySchrodingerLimit
public import FoliationQM.RelativePolarStationaryAction
public import FoliationQM.RestActionPhase

/-!
# The nonrelativistic limit of actual relative polar stationarity

Source: v13 `cor:schrodinger`, component kinds C and D. Supplied real density
and action fields remain smooth; the density stays positive on each original open region.
The actual physical polar envelopes converge locally in L¹. Genuine polar
stationarity gives scalar stationarity, then the weak and classical limits.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.PolarStationarySchrodingerLimit

open Filter Set LorentzCoordinates PolarSecondDifferential
open ActionDensity LaboratoryCoordinates LaboratoryKG RestEnvelopeKG
open RelativePolarStationaryAction RelativeStationaryAction
open Madelung (coordinateVector)
open scoped Topology ContDiff

variable {P : ℕ → MassiveParameters} {ρ S : ℕ → Covector → ℝ}
  {U : Set Covector} {V : ℕ → Set Covector} {u : Covector → ℂ}

/-- Actual relative polar stationarity and local L¹ convergence of the literal physical polar envelopes give the weak Schrödinger equation on the mapped open region. -/
theorem weak_of_relative_polar (p : MassiveParameters) (hU : IsOpen U)
    (hV : ∀ n, IsOpen (V n))
    (hm : ∀ n, (P n).m = p.m) (hh : ∀ n, (P n).hbar = p.hbar)
    (hc : Tendsto (fun n => (P n).c) atTop atTop)
    (hmap : ∀ n, MapsTo (toNormal (P n).c) U (V n))
    (hρ : ∀ n, ∀ y ∈ V n, ContDiffAt ℝ ∞ (ρ n) y)
    (hS : ∀ n, ∀ y ∈ V n, ContDiffAt ℝ ∞ (S n) y)
    (hpos : ∀ n, ∀ y ∈ V n, 0 < ρ n y)
    (hstat : ∀ n, RelativePolarStationaryOn (P n) (ρ n) (S n) coordinateVector (V n))
    (hfield : ScalarLocalTesting.LocalL1 U
      (fun n => actionField (P n) (pullback (P n).c (ρ n))
        (fun x => pullback (P n).c (S n) x + (P n).m * (P n).c ^ 2 * x 0)) u) :
    WeakSchrodingerEquation.WeakEquation p u (fun _ => 0) U := by
  have hψ : ∀ n, ∀ y ∈ V n, ContDiffAt ℝ 2 (actionField (P n) (ρ n) (S n)) y :=
    fun n y hy => (OpenPolarVariations.contDiffAt_actionField (P n)
      (hρ n y hy) (hS n y hy) (hpos n y hy)).of_le (by simp)
  have hscalar : ∀ n, RelativeStationaryOn (P n)
      (actionField (P n) (ρ n) (S n)) coordinateVector (V n) :=
    fun n => (relativePolarStationaryOn_iff_relativeStationaryOn (P n) (hV n)
      (hρ n) (hS n) (hpos n) coordinateVector).mp (hstat n)
  have hf : ScalarLocalTesting.LocalL1 U
      (fun n => envelope (P n) (actionField (P n) (ρ n) (S n))) u := by
    simpa only [RestActionPhase.envelope_actionField] using hfield
  exact RelativeStationarySchrodingerLimit.weak_of_relative_stationary
    p hU hV hm hh hc hmap hψ hscalar hf

/-- When the same local L¹ limit is C², actual supplied relative polar stationarity yields the literal physical Schrödinger equation without temporal or jet-control assumptions. -/
theorem classical_of_relative_polar (p : MassiveParameters) (hU : IsOpen U)
    (hV : ∀ n, IsOpen (V n))
    (hm : ∀ n, (P n).m = p.m) (hh : ∀ n, (P n).hbar = p.hbar)
    (hc : Tendsto (fun n => (P n).c) atTop atTop)
    (hmap : ∀ n, MapsTo (toNormal (P n).c) U (V n))
    (hρ : ∀ n, ∀ y ∈ V n, ContDiffAt ℝ ∞ (ρ n) y)
    (hS : ∀ n, ∀ y ∈ V n, ContDiffAt ℝ ∞ (S n) y)
    (hpos : ∀ n, ∀ y ∈ V n, 0 < ρ n y)
    (hstat : ∀ n, RelativePolarStationaryOn (P n) (ρ n) (S n) coordinateVector (V n))
    (hfield : ScalarLocalTesting.LocalL1 U
      (fun n => actionField (P n) (pullback (P n).c (ρ n))
        (fun x => pullback (P n).c (S n) x + (P n).m * (P n).c ^ 2 * x 0)) u)
    (hu : ∀ x ∈ U, ContDiffAt ℝ 2 u x) :
    ∀ x ∈ U, Complex.I * (p.hbar : ℂ) * directionalDerivative u (coordinateVector 0) x =
      -(((p.hbar ^ 2 / (2 * p.m) : ℝ) : ℂ) * spatialLaplacian u x) := by
  have hψ : ∀ n, ∀ y ∈ V n, ContDiffAt ℝ 2 (actionField (P n) (ρ n) (S n)) y :=
    fun n y hy => (OpenPolarVariations.contDiffAt_actionField (P n)
      (hρ n y hy) (hS n y hy) (hpos n y hy)).of_le (by simp)
  have hscalar : ∀ n, RelativeStationaryOn (P n)
      (actionField (P n) (ρ n) (S n)) coordinateVector (V n) :=
    fun n => (relativePolarStationaryOn_iff_relativeStationaryOn (P n) (hV n)
      (hρ n) (hS n) (hpos n) coordinateVector).mp (hstat n)
  have hf : ScalarLocalTesting.LocalL1 U
      (fun n => envelope (P n) (actionField (P n) (ρ n) (S n))) u := by
    simpa only [RestActionPhase.envelope_actionField] using hfield
  exact RelativeStationarySchrodingerLimit.classical_of_relative_stationary
    p hU hV hm hh hc hmap hψ hscalar hf hu

end FoliationQM.PolarStationarySchrodingerLimit
