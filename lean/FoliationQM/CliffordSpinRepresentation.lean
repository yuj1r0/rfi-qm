module
public import FoliationQM.CliffordSpinManifold
public import FoliationQM.CliffordSpinLorentz
public import FoliationQM.SpinLorentzPolarCompatibility
public import FoliationQM.MatrixDifferential

/-!
# Smooth physical representations and actual Clifford coordinates

Source scope: the genuine Spin factor in v13 `prop:takabayasi`, the
representation in `eq:takabayasi_polar`, and `eq:tetrad_rotor_map`.
The existing universal Clifford representation, restricted to the literal
generated Spin group, is smooth for its compatible six-dimensional atlas.
An explicit real-linear recovery map, obtained by acting on the fixed
rest spinor, recovers its Pauli matrix. Thus smoothness of a field into
actual Spin is equivalent to smoothness of its actual Dirac matrix,
including arbitrary within-set domains.

The independently constructed sixteen Clifford basis coordinates give a
second equivalent regularity criterion. The coordinate maps are genuine
linear composites through the actual even algebra and universal Dirac
representation. No norm or new topology on the full Clifford algebra is
introduced. The actual physical Lorentz matrix entries are smooth as
well; a smooth atlas on the Lorentz target and differentiated equations
of motion are separate obligations.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Operator Manifold
namespace FoliationQM.CliffordSpinRepresentation
open CliffordMinkowski CliffordSpinMap CliffordSpinManifold
open DiracMatrices SpinorMatrix CliffordEvenDimension CliffordEvenPauli

/-- The actual universal Clifford Dirac representation restricted to the literal Spin group. -/
def representation (s : Spin) : Mat := dirac s.val

/-- Restricting the universal representation gives precisely the already verified physical spin matrix. -/
theorem representation_eq_spin (s : Spin) :
    representation s = SpecialLinearSpin.spin (CliffordSpinMap.toMatrix s).val :=
  CliffordSpinMap.dirac_eq_spin s

/-- The restricted actual Dirac representation is faithful. -/
theorem representation_injective : Function.Injective representation :=
  CliffordSpinMap.dirac_spin_injective

/-- Applying a matrix to the fixed rest spinor and encoding the result is a real continuous-linear recovery map. -/
def recoverMatrix : Mat →L[ℝ] Mat2 :=
  SpinorMatrix.continuousLinearEquiv.toContinuousLinearMap.comp
    (MatrixDifferential.mulVecCLM restSpinor)

/-- The actual recovery map sends every spin matrix back to its original two-by-two matrix, without a determinant hypothesis. -/
theorem recoverMatrix_spin (A : Mat2) :
    recoverMatrix (SpecialLinearSpin.spin A) = A :=
  SpecialLinearSpin.spin_rest_matrix A

/-- The real-linear recovery recovers exactly the actual Pauli value of every Clifford Spin element. -/
theorem recoverMatrix_representation (s : Spin) :
    recoverMatrix (representation s) = (CliffordSpinMap.toMatrix s).val := by
  rw [representation_eq_spin, recoverMatrix_spin]

/-- The literal Dirac representation is manifold-smooth to every order. -/
theorem contMDiff_representation (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℝ, Model) 𝓘(ℝ, Mat) n representation := by
  have h := (SpinorMatrixSmooth.contDiff_spin n).contMDiff.comp
    ((SpecialLinearManifold.contMDiff_value n).comp (contMDiff_toMatrix n))
  convert! h using 1
  exact funext representation_eq_spin

/-- The actual full Clifford basis coordinate space, independent of the Pauli representation. -/
abbrev Coordinates := Finset (Fin 4) → ℝ

/-- A genuine Spin element expressed in the independently constructed full Clifford basis. -/
def coordinates (s : Spin) : Coordinates := cliffordBasis.equivFun s.val

/-- The actual inverse even-Pauli map followed by full Clifford basis coordinates is real continuous-linear. -/
def matrixCoordinates : Mat2 →L[ℝ] Coordinates :=
  (cliffordBasis.equivFun.toLinearMap.comp
    ((CliffordAlgebra.even quadratic).val.toLinearMap.comp
      evenPauliEquiv.symm.toLinearMap)).toContinuousLinearMap

/-- Actual inverse even coordinates recover precisely the full Clifford coordinates of every Spin element. -/
theorem matrixCoordinates_toMatrix (s : Spin) :
    matrixCoordinates (CliffordSpinMap.toMatrix s).val = coordinates s := by
  change cliffordBasis.equivFun
    ((evenPauliEquiv.symm (evenPauliEquiv (CliffordSpinMap.toEven s))).val) = _
  rw [evenPauliEquiv.symm_apply_apply]
  rfl

/-- Evaluating the universal Dirac map after inverse full Clifford coordinates is a real continuous-linear matrix map. -/
def coordinateRepresentation : Coordinates →L[ℝ] Mat :=
  (dirac.toLinearMap.comp cliffordBasis.equivFun.symm.toLinearMap).toContinuousLinearMap

/-- Universal representation of the actual basis coordinates equals the literal Spin representation. -/
theorem coordinateRepresentation_coordinates (s : Spin) :
    coordinateRepresentation (coordinates s) = representation s := by
  change dirac (cliffordBasis.equivFun.symm (cliffordBasis.equivFun s.val)) = _
  rw [cliffordBasis.equivFun.symm_apply_apply]
  rfl

/-- The canonical full Clifford coordinates of the actual Spin inclusion are smooth to every order. -/
theorem contMDiff_coordinates (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℝ, Model) 𝓘(ℝ, Coordinates) n coordinates := by
  have h := matrixCoordinates.contMDiff.comp
    ((SpecialLinearManifold.contMDiff_value n).comp (contMDiff_toMatrix n))
  simpa only [Function.comp_def, matrixCoordinates_toMatrix] using h

section GeneralSource
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  {n : WithTop ℕ∞} {f : M → Spin} {s : Set M} {x : M}

/-- On any charted source and within any set, actual Spin smoothness is exactly smoothness of its literal universal Dirac matrix field. -/
theorem contMDiffWithinAt_iff_representation :
    ContMDiffWithinAt I 𝓘(ℝ, Model) n f s x ↔
      ContMDiffWithinAt I 𝓘(ℝ, Mat) n (fun y => representation (f y)) s x := by
  constructor
  · intro hf
    exact (contMDiff_representation n).contMDiffAt.comp_contMDiffWithinAt x hf
  · intro hf
    apply CliffordSpinManifold.contMDiffWithinAt_iff_matrix.mpr
    have h := recoverMatrix.contMDiff.contMDiffAt.comp_contMDiffWithinAt x hf
    simpa only [Function.comp_def, recoverMatrix_representation] using h

/-- Actual Spin smoothness at a point is exactly smoothness of the literal Dirac matrix there. -/
theorem contMDiffAt_iff_representation :
    ContMDiffAt I 𝓘(ℝ, Model) n f x ↔
      ContMDiffAt I 𝓘(ℝ, Mat) n (fun y => representation (f y)) x :=
  contMDiffWithinAt_iff_representation

/-- Actual Spin smoothness on an arbitrary set is exactly smoothness of the literal Dirac matrix field on that set. -/
theorem contMDiffOn_iff_representation :
    ContMDiffOn I 𝓘(ℝ, Model) n f s ↔
      ContMDiffOn I 𝓘(ℝ, Mat) n (fun y => representation (f y)) s := by
  constructor
  · intro h y hy
    exact contMDiffWithinAt_iff_representation.mp (h y hy)
  · intro h y hy
    exact contMDiffWithinAt_iff_representation.mpr (h y hy)

/-- Global actual Spin smoothness is exactly global smoothness of the literal universal Dirac matrix field. -/
theorem contMDiff_iff_representation :
    ContMDiff I 𝓘(ℝ, Model) n f ↔
      ContMDiff I 𝓘(ℝ, Mat) n (fun y => representation (f y)) := by
  constructor
  · intro h y
    exact contMDiffAt_iff_representation.mp (h y)
  · intro h y
    exact contMDiffAt_iff_representation.mpr (h y)

/-- On every charted source and within every set, actual Spin smoothness is equivalent to smoothness of its independently constructed full Clifford basis coordinates. -/
theorem contMDiffWithinAt_iff_coordinates :
    ContMDiffWithinAt I 𝓘(ℝ, Model) n f s x ↔
      ContMDiffWithinAt I 𝓘(ℝ, Coordinates) n (fun y => coordinates (f y)) s x := by
  constructor
  · intro hf
    exact (contMDiff_coordinates n).contMDiffAt.comp_contMDiffWithinAt x hf
  · intro hf
    apply contMDiffWithinAt_iff_representation.mpr
    have h := coordinateRepresentation.contMDiff.contMDiffAt.comp_contMDiffWithinAt x hf
    simpa only [Function.comp_def, coordinateRepresentation_coordinates] using h

/-- Smoothness into actual Spin at a point is exactly smoothness of the canonical Clifford basis coordinates. -/
theorem contMDiffAt_iff_coordinates :
    ContMDiffAt I 𝓘(ℝ, Model) n f x ↔
      ContMDiffAt I 𝓘(ℝ, Coordinates) n (fun y => coordinates (f y)) x :=
  contMDiffWithinAt_iff_coordinates

/-- Smoothness into actual Spin on an arbitrary set is exactly smoothness of its canonical Clifford basis coordinate field. -/
theorem contMDiffOn_iff_coordinates :
    ContMDiffOn I 𝓘(ℝ, Model) n f s ↔
      ContMDiffOn I 𝓘(ℝ, Coordinates) n (fun y => coordinates (f y)) s := by
  constructor
  · intro h y hy
    exact contMDiffWithinAt_iff_coordinates.mp (h y hy)
  · intro h y hy
    exact contMDiffWithinAt_iff_coordinates.mpr (h y hy)

/-- Global actual Spin smoothness is exactly smoothness of its canonical full Clifford basis coordinate field. -/
theorem contMDiff_iff_coordinates :
    ContMDiff I 𝓘(ℝ, Model) n f ↔
      ContMDiff I 𝓘(ℝ, Coordinates) n (fun y => coordinates (f y)) := by
  constructor
  · intro h y
    exact contMDiffAt_iff_coordinates.mp (h y)
  · intro h y
    exact contMDiffAt_iff_coordinates.mpr (h y)

end GeneralSource

/-- The actual proper future Lorentz matrix induced by a genuine Clifford Spin element is smooth in its ambient real matrix entries. -/
theorem contMDiff_lorentz_matrix (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℝ, Model) 𝓘(ℝ, LorentzMatrixGroup.Mat4) n
      (fun s : Spin => LorentzMatrixGroup.matrix (CliffordSpinLorentz.lorentzHom s).val) := by
  have h := (SpinLorentzPolarCompatibility.contDiff_lorentzMatrix n).contMDiff.comp
    ((SpecialLinearManifold.contMDiff_value n).comp (contMDiff_toMatrix n))
  simpa only [Function.comp_def, CliffordSpinLorentz.lorentzHom_matrix] using h

end FoliationQM.CliffordSpinRepresentation
