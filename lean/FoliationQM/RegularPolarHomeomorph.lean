module
public import FoliationQM.PolarLocalSections
/-!
# The natural polar sign quotient is homeomorphic to regular spinors

Sources: v13 `prop:takabayasi` and `eq:takabayasi_polar`.
The datum topology is induced by its independent actual amplitude/matrix
coordinates, and its sign quotient uses the standard quotient topology.
Continuous actual realization descends to that quotient. Its explicitly
constructed inverse is continuous because the two open determinant
branches provide genuine local continuous datum sections. Both algebraic
round trips were already proved from the independent exact sign fibers.
This establishes a homeomorphism, not a topology transported from the
regular-spinor target. A globally continuous choice of one representative,
a global real angle and abstract Spin/bundle classification are not asserted.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
open Topology
namespace FoliationQM.RegularPolarHomeomorph
open PolarSignQuotient PolarDatumTopology PolarLocalSections

/-- The actual regular-spinor realization is continuous on the natural polar sign quotient. -/
theorem continuous_toRegular : Continuous toRegular :=
  continuous_realize.quotient_lift (fun d e h => (realize_eq_iff_related d e).mpr h)

/-- The explicit quotient inverse is globally continuous by the two actual local continuous datum sections. -/
theorem continuous_ofRegular : Continuous ofRegular := by
  apply continuous_iff_continuousAt.mpr
  intro q
  obtain ⟨s, hs, hreal⟩ := exists_continuous_local_section q
  have he : ofRegular = fun y => Quotient.mk signSetoid (s y) := by
    funext y
    apply toRegular_bijective.injective
    rw [toRegular_ofRegular, toRegular_mk, hreal]
  rw [he]
  exact quotient_mk_continuous.continuousAt.comp hs

/-- The natural simultaneous-sign quotient is homeomorphic to the whole strict regular-spinor subtype. -/
def regularHomeomorph : PolarQuotient ≃ₜ RegularSpinor where
  toEquiv := regularEquiv
  continuous_toFun := continuous_toRegular
  continuous_invFun := continuous_ofRegular

/-- The actual homeomorphism evaluates to the existing spinor realization on every sign class. -/
theorem regularHomeomorph_apply (q : PolarQuotient) : regularHomeomorph q = toRegular q := rfl

/-- The inverse homeomorphism is the class of the explicitly reconstructed polar datum. -/
theorem regularHomeomorph_symm_apply (q : RegularSpinor) : regularHomeomorph.symm q = ofRegular q := rfl

/-- Actual datum realization is open as the open sign projection followed by the proved homeomorphism. -/
theorem realize_isOpenMap : IsOpenMap realize :=
  regularHomeomorph.isOpenMap.comp quotient_mk_isOpenMap

/-- Actual datum realization is a genuine quotient map for the existing natural topologies. -/
theorem realize_isQuotientMap : IsQuotientMap realize :=
  regularHomeomorph.isQuotientMap.comp isQuotientMap_quotient_mk'

variable {X : Type*} [TopologicalSpace X]
/-- Continuity of a quotient-valued map is exactly continuity of its actual regular-spinor realization. -/
theorem continuous_toRegular_comp_iff (f : X → PolarQuotient) :
    Continuous (fun x => toRegular (f x)) ↔ Continuous f := by
  constructor
  · intro h
    have hh := continuous_ofRegular.comp h
    simpa only [Function.comp_def, ofRegular_toRegular] using hh
  · intro h
    exact continuous_toRegular.comp h

/-- Continuity of a regular-spinor map is exactly continuity of its actual reconstructed sign class. -/
theorem continuous_ofRegular_comp_iff (f : X → RegularSpinor) :
    Continuous (fun x => ofRegular (f x)) ↔ Continuous f := by
  constructor
  · intro h
    have hh := continuous_toRegular.comp h
    simpa only [Function.comp_def, toRegular_ofRegular] using hh
  · intro h
    exact continuous_ofRegular.comp h

end FoliationQM.RegularPolarHomeomorph
