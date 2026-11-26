module
public import FoliationQM.TwistedScalarStationarity
public import FoliationQM.DiracRegularVariations
public import FoliationQM.RelativeStationaryAction

/-!
# Restricting variations to regular chiral scalar spinors

For v13 `thm:dirac_lift`, on the strict regular chart the scalar field is
nonzero on the integration domain. Compactness of the change carrier
gives one parameter neighborhood on which each spinor variation remains
strictly regular. This preserves the complete action germ.
-/

@[expose] public section
noncomputable section
open scoped Topology ContDiff
namespace FoliationQM.TwistedRegularStationarity
open DiracMatrices SpinorRegularity TwistedScalarCurve TwistedScalarStationarity TwistedScalarAction
open TwistedScalarVariation TwistedScalarField

variable {U : Set Covector} {z : Covector → ℂ}

/-- Put an arbitrary scalar family on the rest-spinor line, retaining its full joint domain and carrier. -/
def restVariation (V : Variation U z) :
    DiracInteriorVariation.Variation U (ScalarRestKinetic.lift z) where
  family y := ScalarRestKinetic.embed (V.family y)
  params := V.params
  params_open := V.params_open
  zero_mem := V.zero_mem
  carrier := V.carrier
  compact := V.compact
  interior := V.interior
  initial x := congrArg ScalarRestKinetic.embed (V.initial x)
  smooth t ht x hx := (V.smooth t ht x hx).smul_const restSpinor
  fixed t ht x hx := congrArg ScalarRestKinetic.embed (V.fixed t ht x hx)

/-- Every scalar family of a nonvanishing background has a restriction with identical actual
field and carrier, strictly regular for the given physical chiral twist everywhere on U. -/
theorem exists_regular_restriction (β : Covector → ℝ) (V : Variation U z) (hU : IsOpen U)
    (hn : ∀ x ∈ U, z x ≠ 0) :
    ∃ W : Variation U z, W.family = V.family ∧ W.carrier = V.carrier ∧ W.params ⊆ V.params ∧
      ∀ t ∈ W.params, ∀ x ∈ U, Regular (field β (SmoothActionDensity.slice W.family t) x) := by
  have hr : ∀ x ∈ U, Regular (ScalarRestKinetic.lift z x) :=
    fun x hx => (ScalarRestKinetic.regular_embed_iff _).mpr (hn x hx)
  obtain ⟨T, ho, h0, hs, hT⟩ := DiracRegularVariations.exists_regular_params (restVariation V) hU hr
  let W : Variation U z :=
    { V with
      params := T
      params_open := ho
      zero_mem := h0
      smooth := fun t ht => V.smooth t (hs ht)
      fixed := fun t ht => V.fixed t (hs ht) }
  refine ⟨W, rfl, rfl, hs, fun t ht x hx => ?_⟩
  exact (regular_field_iff _ _ _).mpr ((ScalarRestKinetic.regular_embed_iff _).mp (hT t ht x hx))

/-- Zero relative derivative only along families remaining inside the physical regular locus. -/
def RegularStationary (p : MassiveParameters) (β : Covector → ℝ) (z : Covector → ℂ) (U : Set Covector) : Prop :=
  ∀ V : Variation U z, (∀ t ∈ V.params, ∀ x ∈ U, Regular (field β (SmoothActionDensity.slice V.family t) x)) →
    HasDerivAt (fun t => relativeAction p β z (SmoothActionDensity.slice V.family t) U) 0 0

/-- At a regular background, restricting to regular curves detects exactly ordinary compact-family stationarity. -/
theorem regular_iff (p : MassiveParameters) (β : Covector → ℝ) (hU : IsOpen U) (hn : ∀ x ∈ U, z x ≠ 0) :
    RegularStationary p β z U ↔ StationaryOn p β z U := by
  constructor
  · intro h V
    obtain ⟨W, hf, _, _, hr⟩ := exists_regular_restriction β V hU hn
    simpa only [hf] using h W hr
  · exact fun h V _ => h V

/-- Regular variations of a smooth nonvanishing scalar field at fixed chiral angle yield the same wave equation. -/
theorem regular_iff_force (p : MassiveParameters) {β : Covector → ℝ} (hU : IsOpen U)
    (hb : ∀ x ∈ U, ContDiffAt ℝ 1 β x) (hz : ∀ x ∈ U, ContDiffAt ℝ ∞ z x) (hn : ∀ x ∈ U, z x ≠ 0) :
    RegularStationary p β z U ↔ ∀ x ∈ U, force p β z x = 0 :=
  (regular_iff p β hU hn).trans (stationary_iff_force p hU hb hz)

/-- Constant chiral angles give exactly relative Klein–Gordon stationarity of the scalar field. -/
theorem constant_angle_iff (p : MassiveParameters) (b : ℝ) (hU : IsOpen U)
    (hz : ∀ x ∈ U, ContDiffAt ℝ ∞ z x) :
    StationaryOn p (fun _ => b) z U ↔
      RelativeStationaryAction.RelativeStationaryOn p z DiracFieldDensity.coordinateDirections U := by
  rw [stationary_iff_force p hU (fun _ _ => contDiffAt_const) hz,
    RelativeStationaryAction.relativeStationaryOn_iff_kgOperator p hU _ (fun x hx => (hz x hx).of_le (by simp))]
  simp_rw [force, TwistedScalarDensity.potential_const, Complex.ofReal_zero, zero_mul, add_zero]

end FoliationQM.TwistedRegularStationarity
