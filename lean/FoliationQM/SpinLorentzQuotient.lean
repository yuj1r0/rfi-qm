module
public import FoliationQM.SpinLorentzSurjective
public import FoliationQM.SpinLorentzCovering
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
/-!
# The natural sign quotient as the full proper future Lorentz topological group

Source scope: the concrete two-sign Lorentz-frame identification in v13
`prop:takabayasi` and `eq:tetrad_rotor_map`. The source is the existing
special linear group quotient by the actual kernel, already proved to be
exactly the two central signs. The target is the independently defined
proper future Lorentz subgroup with its existing natural topology.

The canonical quotient-kernel multiplicative equivalence uses the proved
full-target surjectivity. The descended map is open because its composite
with the continuous surjective quotient projection is the actual open
physical homomorphism. Thus the equivalence and its inverse are continuous
without transporting or replacing either topology. A bundled continuous
multiplicative equivalence and exact representative formulas record the
identification. The inverse chooses a sign class, not a continuous individual
matrix representative. No abstract Clifford spin-group or universal-cover
identification is asserted here.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
namespace FoliationQM.SpinLorentzQuotient
open SourcePolarDatum LorentzMatrixGroup SpinLorentzOrientation SpinLorentzSignQuotient
open SpinLorentzSurjective

/-- The descended map reaches the full independently defined proper future Lorentz group. -/
theorem quotientHom_surjective : Function.Surjective quotientHom := by
  intro L
  obtain ⟨A, hA⟩ := properFutureHom_surjective L
  exact ⟨projection A, hA⟩

/-- The actual sign quotient is multiplicatively equivalent to the full independent proper future Lorentz group. -/
def quotientMulEquiv : SignQuotient ≃* ProperFutureLorentz :=
  QuotientGroup.quotientKerEquivOfSurjective properFutureHom properFutureHom_surjective

/-- The multiplicative equivalence retains precisely the pre-existing descended homomorphism. -/
theorem quotientMulEquiv_apply (q : SignQuotient) : quotientMulEquiv q = quotientHom q := rfl

/-- On every actual special linear representative the equivalence is exactly its original physical Lorentz image. -/
theorem quotientMulEquiv_projection (A : SpecialLinearMatrix) :
    quotientMulEquiv (projection A) = properFutureHom A := rfl

/-- The inverse equivalence recovers the actual sign class of every special linear representative. -/
theorem quotientMulEquiv_symm_image (A : SpecialLinearMatrix) :
    quotientMulEquiv.symm (properFutureHom A) = projection A :=
  quotientMulEquiv.symm_apply_apply (projection A)

/-- The descended homomorphism is an actual open map: its composite with the continuous surjective quotient projection is the already proved open physical homomorphism. -/
theorem isOpenMap_quotientHom : IsOpenMap quotientHom := by
  apply IsOpenMap.of_comp continuous_projection projection_surjective
  exact SpinLorentzCovering.isOpenMap_properFutureHom

/-- The canonical multiplicative equivalence is a homeomorphism for the existing source quotient and independently specified Lorentz topologies. -/
def quotientHomeomorph : SignQuotient ≃ₜ ProperFutureLorentz :=
  quotientMulEquiv.toEquiv.toHomeomorphOfContinuousOpen
    continuous_quotientHom isOpenMap_quotientHom

/-- The homeomorphism is exactly the existing descended physical homomorphism at every quotient class. -/
theorem quotientHomeomorph_apply (q : SignQuotient) : quotientHomeomorph q = quotientHom q := rfl

/-- The actual homeomorphism sends each sign class to the original physical Lorentz image. -/
theorem quotientHomeomorph_projection (A : SpecialLinearMatrix) :
    quotientHomeomorph (projection A) = properFutureHom A := rfl

/-- Its inverse gives the sign class of any actual lift, independently of which of the two representatives is supplied. -/
theorem quotientHomeomorph_symm_image (A : SpecialLinearMatrix) :
    quotientHomeomorph.symm (properFutureHom A) = projection A :=
  quotientHomeomorph.symm_apply_apply (projection A)

/-- A class is the inverse image of a Lorentz element exactly when any displayed representative maps to that element; no individual representative is chosen continuously. -/
theorem quotientHomeomorph_symm_eq_projection_iff (L : ProperFutureLorentz)
    (A : SpecialLinearMatrix) :
    quotientHomeomorph.symm L = projection A ↔ L = properFutureHom A :=
  quotientHomeomorph.symm_apply_eq

/-- The same actual identification bundled as a two-sided continuous multiplicative equivalence. -/
def quotientMulHomeomorph : SignQuotient ≃ₜ* ProperFutureLorentz where
  toMulEquiv := quotientMulEquiv
  continuous_toFun := continuous_quotientHom
  continuous_invFun := quotientHomeomorph.continuous_symm

/-- Forgetting multiplication recovers the already constructed actual homeomorphism. -/
theorem quotientMulHomeomorph_toHomeomorph :
    quotientMulHomeomorph.toHomeomorph = quotientHomeomorph := rfl

/-- Forgetting continuity recovers the canonical quotient-kernel multiplicative equivalence. -/
theorem quotientMulHomeomorph_toMulEquiv :
    quotientMulHomeomorph.toMulEquiv = quotientMulEquiv := rfl

end FoliationQM.SpinLorentzQuotient
