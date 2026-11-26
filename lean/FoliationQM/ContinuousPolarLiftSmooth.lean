module
public import FoliationQM.PolarSignCovering
public import FoliationQM.PolarDatumSmooth
public import FoliationQM.SpecialLinearFrameSmooth
/-!
# Continuous polar lifts inherit actual coordinate regularity

Source bridge for v13 `prop:takabayasi`. Local injectivity of the actual
proved polar covering makes continuous lifts that agree at a point and
realize the same nearby field agree on a neighborhood. Thus their local
sign choice cannot vary arbitrarily near that point.

An anchored coordinate-smooth lift was constructed independently from
the actual determinant branches. Comparing any continuous datum lift
with it proves that the lift inherits precisely the regularity of its
actual realized spinor. Pointwise, global and open-domain criteria retain
the continuity premise explicitly. The genuine spin representation and
real frame consequently inherit that same regularity. No abstract
quotient-manifold structure or global section is supplied by these results.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
open Topology Filter Set
namespace FoliationQM.ContinuousPolarLiftSmooth
open PolarSignQuotient PolarDatumTopology PolarSignCovering
variable {X : Type*} [TopologicalSpace X]
/-- Continuous datum lifts with the same value and the same nearby realization agree on a neighborhood by actual local injectivity. -/
theorem eventually_eq_of_realize {f g : X → Datum} {x : X}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) (h₀ : f x=g x)
    (he : (fun y => realize (f y)) =ᶠ[𝓝 x] (fun y => realize (g y))) :
    f =ᶠ[𝓝 x] g := by
  obtain ⟨U,hU,hx,hinj⟩ := realize_isLocalHomeomorph.isLocallyInjective (f x)
  have hfy := hf.tendsto.eventually (hU.mem_nhds hx)
  have hgx : g x ∈ U := h₀ ▸ hx
  have hgy := hg.tendsto.eventually (hU.mem_nhds hgx)
  filter_upwards [hfy,hgy,he] with y hy hz heq
  exact hinj hy hz heq

/-- Continuous lifts of the same nearby realized field differ by one fixed sign on a neighborhood of the specified point. -/
theorem eventually_eq_or_neg_of_realize {f g : X → Datum} {x : X}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x)
    (he : (fun y => realize (f y)) =ᶠ[𝓝 x] (fun y => realize (g y))) :
    f =ᶠ[𝓝 x] g ∨ f =ᶠ[𝓝 x] (fun y => negDatum (g y)) := by
  rcases (realize_eq_iff_related _ _).mp he.self_of_nhds with h|h
  · exact Or.inl (eventually_eq_of_realize hf hg h he)
  · apply Or.inr
    apply eventually_eq_of_realize hf (continuous_negDatum.continuousAt.comp hg) h
    filter_upwards [he] with y hy
    exact hy.trans ((realize_eq_iff_related _ _).mpr (Or.inr rfl)).symm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
open PolarDatumSmooth

/-- Any continuous actual datum lift inherits coordinate regularity of the same order from its actual realized spinor field. -/
theorem coordinateContDiffAt_of_continuousAt (n : WithTop ℕ∞) {d : E → Datum} {x : E}
    (hd : ContinuousAt d x)
    (hreal : ContDiffAt ℝ n (fun y => (realize (d y)).val) x) :
    CoordinateContDiffAt n d x := by
  obtain ⟨g,hg,hgx,hgReal⟩ := exists_coordinateContDiffAt_lift_through n
    (fun y => realize (d y)) hreal (d x) rfl
  have he : d =ᶠ[𝓝 x] g := eventually_eq_of_realize hd
    (continuousAt_of_coordinateContDiffAt hg) hgx.symm
      (Filter.Eventually.of_forall (fun y => (hgReal y).symm))
  constructor
  · exact hg.1.congr_of_eventuallyEq (he.mono fun _ h => congrArg Datum.t h)
  · exact hg.2.congr_of_eventuallyEq (he.mono fun _ h => congrArg Datum.A h)

/-- Actual datum coordinate regularity is equivalent to natural continuity plus regularity of the actual realized spinor at the point. -/
theorem coordinateContDiffAt_iff (n : WithTop ℕ∞) (d : E → Datum) (x : E) :
    CoordinateContDiffAt n d x ↔ ContinuousAt d x ∧
      ContDiffAt ℝ n (fun y => (realize (d y)).val) x := by
  constructor
  · intro h
    exact ⟨continuousAt_of_coordinateContDiffAt h,contDiffAt_realize h⟩
  · rintro ⟨hd,hreal⟩
    exact coordinateContDiffAt_of_continuousAt n hd hreal

/-- Everywhere local coordinate regularity is equivalent to global natural continuity and global regularity of the actual spinor realization. -/
theorem coordinateContDiffAt_everywhere_iff (n : WithTop ℕ∞) (d : E → Datum) :
    (∀ x, CoordinateContDiffAt n d x) ↔ Continuous d ∧
      ContDiff ℝ n (fun y => (realize (d y)).val) := by
  simp only [coordinateContDiffAt_iff,forall_and,continuous_iff_continuousAt,
    contDiff_iff_contDiffAt]

/-- On an open domain, local coordinate regularity is equivalent to continuity and actual realized-field regularity restricted to that domain. -/
theorem coordinateContDiffAt_on_open_iff (n : WithTop ℕ∞) (d : E → Datum)
    {U : Set E} (hU : IsOpen U) :
    (∀ x ∈ U, CoordinateContDiffAt n d x) ↔ ContinuousOn d U ∧
      ContDiffOn ℝ n (fun y => (realize (d y)).val) U := by
  constructor
  · intro h
    exact ⟨fun x hx => (continuousAt_of_coordinateContDiffAt (h x hx)).continuousWithinAt,
      fun x hx => (contDiffAt_realize (h x hx)).contDiffWithinAt⟩
  · rintro ⟨hd,hr⟩ x hx
    exact coordinateContDiffAt_of_continuousAt n (hd.continuousAt (hU.mem_nhds hx))
      (hr.contDiffAt (hU.mem_nhds hx))

/-- The actual four-by-four spin representative of any continuous polar lift inherits the realized field regularity at the point. -/
theorem contDiffAt_spin_of_continuous_lift (n : WithTop ℕ∞) {d : E → Datum} {x : E}
    (hd : ContinuousAt d x)
    (hreal : ContDiffAt ℝ n (fun y => (realize (d y)).val) x) :
    ContDiffAt ℝ n (fun y => SpecialLinearSpin.spin (d y).A) x :=
  (SpinorMatrixSmooth.contDiff_spin n).contDiffAt.comp x
    (coordinateContDiffAt_of_continuousAt n hd hreal).2

/-- The actual real Lorentz-frame matrix of any continuous polar lift inherits the realized field regularity at the point. -/
theorem contDiffAt_frame_of_continuous_lift (n : WithTop ℕ∞) {d : E → Datum} {x : E}
    (hd : ContinuousAt d x)
    (hreal : ContDiffAt ℝ n (fun y => (realize (d y)).val) x) :
    ContDiffAt ℝ n (fun y => SpecialLinearFrame.frame (d y).A) x :=
  (SpecialLinearFrameSmooth.contDiff_frame n).contDiffAt.comp x
    (coordinateContDiffAt_of_continuousAt n hd hreal).2
end FoliationQM.ContinuousPolarLiftSmooth
