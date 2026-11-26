module

public import FoliationQM.RelativeStationaryAction
public import FoliationQM.KleinGordonWeakLimit

/-!
# Schrödinger limits from actual relative stationary action

Source: v13 `cor:schrodinger`, component kinds C and D. Relative stationarity
on each original normal-coordinate region supplies the KG equation. The actual
physical coordinate maps land in those regions, and local L¹ convergence of
the same rest envelopes gives a weak limit. C² regularity of that limit gives
the classical equation; no finite background action or temporal bound is used.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.RelativeStationarySchrodingerLimit

open Filter Set ScalarLocalTesting PolarSecondDifferential
open LaboratoryCoordinates LaboratoryKG RestEnvelopeKG WeakSchrodingerEquation
open RelativeStationaryAction
open Madelung (coordinateVector)
open scoped Topology ContDiff

variable {P : ℕ → MassiveParameters} {ψ : ℕ → Covector → ℂ}
variable {u : Covector → ℂ} {U : Set Covector} {V : ℕ → Set Covector}

/-- Actual relative stationarity and local L¹ convergence of the same physical rest envelopes give the weak Schrödinger equation on the physical region. -/
theorem weak_of_relative_stationary (p : MassiveParameters) (hU : IsOpen U)
    (hV : ∀ n, IsOpen (V n))
    (hm : ∀ n, (P n).m = p.m) (hh : ∀ n, (P n).hbar = p.hbar)
    (hc : Tendsto (fun n => (P n).c) atTop atTop)
    (hmap : ∀ n, MapsTo (toNormal (P n).c) U (V n))
    (hψ : ∀ n, ∀ y ∈ V n, ContDiffAt ℝ 2 (ψ n) y)
    (hstat : ∀ n, RelativeStationaryOn (P n) (ψ n) coordinateVector (V n))
    (hfield : LocalL1 U (fun n => envelope (P n) (ψ n)) u) :
    WeakEquation p u (fun _ => 0) U := by
  apply KleinGordonWeakLimit.source_weak_limit_of_KG p hU hm hh hc
    (fun n x hx => hψ n _ (hmap n hx)) _ hfield
  intro n x hx
  exact (relativeStationaryOn_iff_kgOperator (P n) (hV n) coordinateVector
    (hψ n)).1 (hstat n) _ (hmap n hx)

/-- A C² local L¹ limit of actual relatively stationary original fields satisfies the literal physical Schrödinger PDE on the mapped physical region. -/
theorem classical_of_relative_stationary (p : MassiveParameters) (hU : IsOpen U)
    (hV : ∀ n, IsOpen (V n))
    (hm : ∀ n, (P n).m = p.m) (hh : ∀ n, (P n).hbar = p.hbar)
    (hc : Tendsto (fun n => (P n).c) atTop atTop)
    (hmap : ∀ n, MapsTo (toNormal (P n).c) U (V n))
    (hψ : ∀ n, ∀ y ∈ V n, ContDiffAt ℝ 2 (ψ n) y)
    (hstat : ∀ n, RelativeStationaryOn (P n) (ψ n) coordinateVector (V n))
    (hfield : LocalL1 U (fun n => envelope (P n) (ψ n)) u)
    (hu : ∀ x ∈ U, ContDiffAt ℝ 2 u x) :
    ∀ x ∈ U,
      Complex.I * (p.hbar : ℂ) * directionalDerivative u (coordinateVector 0) x =
        -(((p.hbar ^ 2 / (2 * p.m) : ℝ) : ℂ) * spatialLaplacian u x) := by
  have h := classical_of_weak p hU hu continuousOn_const
    (weak_of_relative_stationary p hU hV hm hh hc hmap hψ hstat hfield)
  intro x hx
  have he : schrodingerResidual p u x = 0 := by
    simpa only [mul_zero, add_zero] using h x hx
  exact eq_neg_of_add_eq_zero_left he

end FoliationQM.RelativeStationarySchrodingerLimit
