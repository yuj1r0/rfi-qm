module
public import FoliationQM.SpecialLinearColumnCoordinates
public import FoliationQM.PuncturedSpaceSimplyConnected
public import Mathlib.Topology.Homotopy.Product
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Simple connectivity of the actual complex special linear group

Source scope: the simple-connectivity component of the Spin/Lorentz
identification in v13 `prop:takabayasi` and `eq:tetrad_rotor_map`.
The actual determinant-one matrix space retains its original topology.
Its independently proved first-column homeomorphism identifies it with
the product of the punctured two-complex-coordinate space and a complex
fiber coordinate. The punctured factor has real dimension four and is
simply connected by the proved finite-dimensional punctured-space
theorem. The complex factor is contractible. Products are handled by
the genuine product and projection operations on path homotopy classes.

No polar decomposition, unproved deformation retraction, assumed
simple connectivity, or change of topology is used. The physical
universal covering consequences are established in the dependent
Clifford Spin module.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.SpecialLinearSimplyConnected
open SpecialLinearColumnCoordinates SourcePolarDatum

/-- Products of simply connected spaces are simply connected, by the actual product and projection identities for path homotopy classes. -/
theorem simplyConnectedSpace_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [SimplyConnectedSpace X] [SimplyConnectedSpace Y] : SimplyConnectedSpace (X × Y) := by
  apply simply_connected_iff_paths_homotopic.mpr
  refine ⟨inferInstance, ?_⟩
  intro x y
  refine ⟨fun p q => ?_⟩
  calc
    p = Path.Homotopic.prod (Path.Homotopic.projLeft p) (Path.Homotopic.projRight p) :=
      (Path.Homotopic.prod_projLeft_projRight p).symm
    _ = Path.Homotopic.prod (Path.Homotopic.projLeft q) (Path.Homotopic.projRight q) := by
      congr 1 <;> exact Subsingleton.elim _ _
    _ = q := Path.Homotopic.prod_projLeft_projRight q

/-- The two actual complex first-column coordinates form a real vector space of dimension four. -/
theorem column_finrank : Module.finrank ℝ Column = 4 := by
  simp [Column, Module.finrank_pi_fintype, Complex.finrank_real_complex]

/-- The original nonzero-column subtype is simply connected by its proved real dimension bound. -/
instance instSimplyConnectedPuncturedColumn : SimplyConnectedSpace PuncturedColumn :=
  PuncturedSpaceSimplyConnected.simplyConnectedSpace Column (by rw [column_finrank]; norm_num)

/-- The actual column-coordinate product is simply connected, with a contractible complex fiber. -/
instance instSimplyConnectedCoordinates : SimplyConnectedSpace Coordinates :=
  simplyConnectedSpace_prod

/-- The genuine complex determinant-one matrix group is simply connected in its unchanged natural topology. -/
theorem simplyConnectedSpace_specialLinear : SimplyConnectedSpace SpecialLinearMatrix :=
  columnHomeomorph.toHomotopyEquiv.simplyConnectedSpace

/-- Typeclass form of the proved simple connectivity of the original determinant-one matrix group. -/
instance instSimplyConnectedSpecialLinearMatrix : SimplyConnectedSpace SpecialLinearMatrix :=
  simplyConnectedSpace_specialLinear

end FoliationQM.SpecialLinearSimplyConnected
