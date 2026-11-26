module
public import FoliationQM.SmoothLorentzTetrad
public import Mathlib.Geometry.Manifold.MFDeriv.Tangent

/-!
# Actual tangent coordinates and local tetrad matrices

A supplied four-element basis of the manifold model fixes real coordinate
labels. The coordinates below use Mathlib's actual tangent-bundle
trivializations. On a genuine chart source they are the derivative of the
extended base chart, and their inverse is the derivative of its inverse.
No topology or charted structure is replaced.

The finite-order graph criteria assume a C^(n+1) base manifold and derive the
C^n tangent vector bundle locally. The matrix identities concern actual
vectors in TangentSpace, including arbitrary supplied local tetrads; they do
not assert existence of a metric-orthonormal tetrad or a geometric Spin lift.
This is the tangent-coordinate component for `prop:takabayasi`; it supports
the downstream geometric bridge surrounding `thm:dirac_lift` without asserting
unconditional existence of geometric data.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Bundle Module Matrix
open scoped Manifold Bundle Topology Matrix.Norms.Elementwise
namespace FoliationQM.TangentTetradCoordinates

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  (b : Basis (Fin 4) ℝ E)

/-- Four real coordinates obtained from the existing tangent trivialization at the indicated base chart. -/
def coordinates (c x : M) (v : TangentSpace I x) : Fin 4 → ℝ :=
  b.equivFunL ((trivializationAt E (TangentSpace I) c) ⟨x, v⟩).2

/-- The inverse coordinate formula uses the existing fiberwise inverse tangent trivialization; claims of inversion are restricted to its true chart source. -/
def reconstruct (c x : M) (v : Fin 4 → ℝ) : TangentSpace I x :=
  (trivializationAt E (TangentSpace I) c).symmL ℝ x (b.equivFunL.symm v)

/-- On a true chart source the coordinate map is the corresponding continuous linear tangent trivialization followed by the fixed model-basis coordinates. -/
theorem coordinates_eq_linear (c : M) {x : M} (hx : x ∈ (chartAt H c).source)
    (v : TangentSpace I x) :
    coordinates I b c x v = b.equivFunL
      ((trivializationAt E (TangentSpace I) c).continuousLinearMapAt ℝ x v) := by
  rw [Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hx]
  rfl

/-- Actual tangent coordinates are the manifold derivative of the extended base chart, expressed in the fixed four-element model basis. -/
theorem coordinates_eq_mfderiv (c : M) {x : M} (hx : x ∈ (chartAt H c).source)
    (v : TangentSpace I x) :
    coordinates I b c x v = b.equivFunL (mfderiv I 𝓘(ℝ, E) (extChartAt I c) x v) := by
  rw [coordinates_eq_linear I b c hx, TangentBundle.continuousLinearMapAt_trivializationAt hx]
  rfl

/-- Reconstruction is the derivative within the model range of the actual inverse extended chart, applied to the vector specified by the model basis. -/
theorem reconstruct_eq_mfderivWithin (c : M) {x : M} (hx : x ∈ (chartAt H c).source)
    (v : Fin 4 → ℝ) :
    reconstruct I b c x v =
      mfderivWithin 𝓘(ℝ, E) I (extChartAt I c).symm (range I) (extChartAt I c x)
        (b.equivFunL.symm v) := by
  rw [reconstruct, TangentBundle.symmL_trivializationAt hx]
  rfl

/-- Reconstructing the coordinates recovers the actual tangent vector on the true base chart. -/
theorem reconstruct_coordinates (c : M) {x : M} (hx : x ∈ (chartAt H c).source)
    (v : TangentSpace I x) : reconstruct I b c x (coordinates I b c x v) = v := by
  rw [coordinates_eq_linear I b c hx, reconstruct, b.equivFunL.symm_apply_apply]
  exact Bundle.Trivialization.symmL_continuousLinearMapAt _ hx v

/-- Taking coordinates after reconstruction recovers all four prescribed real coordinates on the true base chart. -/
theorem coordinates_reconstruct (c : M) {x : M} (hx : x ∈ (chartAt H c).source)
    (v : Fin 4 → ℝ) : coordinates I b c x (reconstruct I b c x v) = v := by
  rw [coordinates_eq_linear I b c hx, reconstruct,
    Bundle.Trivialization.continuousLinearMapAt_symmL _ hx, b.equivFunL.apply_symm_apply]

/-- The actual tangent basis obtained from the chart's genuine linear trivialization and the supplied model basis. -/
def coordinateBasis (c : M) {x : M} (hx : x ∈ (chartAt H c).source) :
    Basis (Fin 4) ℝ (TangentSpace I x) :=
  (trivializationAt E (TangentSpace I) c).basisAt b hx

/-- The real coordinate function is exactly the representation in the induced actual tangent basis. -/
theorem coordinates_eq_repr (c : M) {x : M} (hx : x ∈ (chartAt H c).source)
    (v : TangentSpace I x) : coordinates I b c x v = (coordinateBasis I b c hx).repr v := by
  ext a
  simp [coordinates, coordinateBasis, Bundle.Trivialization.basisAt]

/-- An actual coordinate-basis vector is the inverse tangent trivialization of the corresponding model-basis vector on the true chart source. -/
theorem coordinateBasis_apply (c : M) {x : M} (hx : x ∈ (chartAt H c).source)
    (j : Fin 4) :
    coordinateBasis I b c hx j =
      (trivializationAt E (TangentSpace I) c).symmL ℝ x (b j) := by
  change (trivializationAt E (TangentSpace I) c).symm x (b j) = _
  exact (Bundle.Trivialization.symmL_apply _ hx (b j)).symm

/-- Entries of the genuine tangent-chart change matrix are the derivative of the target extended chart composed with the inverse-source derivative within the model range. -/
theorem coordinateBasis_change_entry (c d : M) {x : M}
    (hc : x ∈ (chartAt H c).source) (hd : x ∈ (chartAt H d).source) (a j : Fin 4) :
    (coordinateBasis I b d hd).toMatrix (coordinateBasis I b c hc) a j =
      b.equivFunL (mfderiv I 𝓘(ℝ, E) (extChartAt I d) x
        (mfderivWithin 𝓘(ℝ, E) I (extChartAt I c).symm (range I) (extChartAt I c x)
          (b j))) a := by
  rw [Basis.toMatrix_apply, ← coordinates_eq_repr I b d hd,
    coordinates_eq_mfderiv I b d hd, coordinateBasis_apply I b c hc,
    TangentBundle.symmL_trivializationAt hc]
  rfl

/-- The columns of this real matrix are coordinates of four actual tangent vectors, with no implicit identification of tangent fibers at different base points. -/
def tetradMatrix (c x : M) (X : Fin 4 → TangentSpace I x) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun a j => coordinates I b c x (X j) a

/-- A tetrad matrix is the basis-coordinate matrix of its actual tangent vectors on the chart source. -/
theorem tetradMatrix_eq_toMatrix (c : M) {x : M} (hx : x ∈ (chartAt H c).source)
    (X : Fin 4 → TangentSpace I x) :
    tetradMatrix I b c x X = (coordinateBasis I b c hx).toMatrix X := by
  ext a j
  exact congrFun (coordinates_eq_repr I b c hx (X j)) a

/-- A linear combination of actual tangent vectors has the coordinate column given by multiplication by the actual tetrad matrix. -/
theorem coordinates_sum (c : M) {x : M} (hx : x ∈ (chartAt H c).source)
    (X : Fin 4 → TangentSpace I x) (v : Fin 4 → ℝ) :
    coordinates I b c x (∑ j, v j • X j) = tetradMatrix I b c x X *ᵥ v := by
  ext a
  simp only [coordinates_eq_repr I b c hx, tetradMatrix_eq_toMatrix I b c hx,
    map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply,
    smul_eq_mul, Matrix.mulVec, dotProduct, Basis.toMatrix_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

/-- Reconstructing a matrix-produced coordinate column is the corresponding actual tangent-vector sum. -/
theorem reconstruct_mulVec (c : M) {x : M} (hx : x ∈ (chartAt H c).source)
    (X : Fin 4 → TangentSpace I x) (v : Fin 4 → ℝ) :
    reconstruct I b c x (tetradMatrix I b c x X *ᵥ v) = ∑ j, v j • X j := by
  rw [← coordinates_sum I b c hx, reconstruct_coordinates I b c hx]

/-- A genuine tangent basis gives an invertible tetrad coordinate matrix on every containing chart. -/
theorem isUnit_tetradMatrix (c : M) {x : M} (hx : x ∈ (chartAt H c).source)
    (X : Basis (Fin 4) ℝ (TangentSpace I x)) :
    IsUnit (tetradMatrix I b c x X) := by
  rw [tetradMatrix_eq_toMatrix I b c hx]
  let := (coordinateBasis I b c hx).invertibleToMatrix X
  exact isUnit_of_invertible _

/-- Actual change of tangent basis multiplies the coordinate matrices in the same order as basis expansion. -/
theorem tetradMatrix_mul_change (c : M) {x : M} (hx : x ∈ (chartAt H c).source)
    (X : Basis (Fin 4) ℝ (TangentSpace I x)) (Y : Fin 4 → TangentSpace I x) :
    tetradMatrix I b c x X * X.toMatrix Y = tetradMatrix I b c x Y := by
  simp only [tetradMatrix_eq_toMatrix I b c hx]
  exact Basis.toMatrix_mul_toMatrix _ _ _

/-- Coordinates of one actual tangent frame in two base charts differ by the genuine derivative-coordinate change matrix. -/
theorem tetradMatrix_change_chart (c d : M) {x : M}
    (hc : x ∈ (chartAt H c).source) (hd : x ∈ (chartAt H d).source)
    (X : Fin 4 → TangentSpace I x) :
    (coordinateBasis I b d hd).toMatrix (coordinateBasis I b c hc) *
      tetradMatrix I b c x X = tetradMatrix I b d x X := by
  simp only [tetradMatrix_eq_toMatrix I b c hc, tetradMatrix_eq_toMatrix I b d hd]
  exact Basis.toMatrix_mul_toMatrix _ _ _

omit [IsManifold I 1 M] in
/-- For a C^(n+1) base, an actual tangent-section graph is C^n within an arbitrary set exactly when its four genuine chart coordinates are; the tangent-bundle regularity is derived, not assumed. -/
theorem contMDiffWithinAt_graph_iff (n : WithTop ℕ∞) [IsManifold I (n + 1) M]
    (c : M) (X : ∀ x : M, TangentSpace I x) (s : Set M) {x : M}
    (hx : x ∈ (chartAt H c).source) :
    letI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    ContMDiffWithinAt I I.tangent n (fun y => (⟨y, X y⟩ : TangentBundle I M)) s x ↔
      ContMDiffWithinAt I 𝓘(ℝ, Fin 4 → ℝ) n (fun y => coordinates I b c y (X y)) s x := by
  let : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  let : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  rw [Bundle.Trivialization.contMDiffWithinAt_section (e := trivializationAt E (TangentSpace I) c) s hx]
  constructor
  · intro h
    exact b.equivFunL.contDiff.contMDiff.contMDiffAt.comp_contMDiffWithinAt x h
  · intro h
    have h' := b.equivFunL.symm.contDiff.contMDiff.contMDiffAt.comp_contMDiffWithinAt x h
    simpa only [coordinates, Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using h'

omit [IsManifold I 1 M] in
/-- The graph-coordinate criterion holds at an ordinary point with exactly one derivative of base regularity available for the tangent bundle. -/
theorem contMDiffAt_graph_iff (n : WithTop ℕ∞) [IsManifold I (n + 1) M]
    (c : M) (X : ∀ x : M, TangentSpace I x) {x : M}
    (hx : x ∈ (chartAt H c).source) :
    letI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    ContMDiffAt I I.tangent n (fun y => (⟨y, X y⟩ : TangentBundle I M)) x ↔
      ContMDiffAt I 𝓘(ℝ, Fin 4 → ℝ) n (fun y => coordinates I b c y (X y)) x :=
  contMDiffWithinAt_graph_iff I b n c X univ hx

omit [IsManifold I 1 M] in
/-- On any subset of one base chart, actual tangent-section graph regularity is equivalent to regularity of its four real chart coordinates, without an openness premise on that subset. -/
theorem contMDiffOn_graph_iff (n : WithTop ℕ∞) [IsManifold I (n + 1) M]
    (c : M) (X : ∀ x : M, TangentSpace I x) {s : Set M}
    (hs : s ⊆ (chartAt H c).source) :
    letI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    ContMDiffOn I I.tangent n (fun y => (⟨y, X y⟩ : TangentBundle I M)) s ↔
      ContMDiffOn I 𝓘(ℝ, Fin 4 → ℝ) n (fun y => coordinates I b c y (X y)) s := by
  let : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  exact forall₂_congr fun x hx => contMDiffWithinAt_graph_iff I b n c X s (hs hx)

omit [IsManifold I 1 M] in
/-- The four actual tangent-section graphs are C^n within a set exactly when their single real tetrad-coordinate matrix is C^n; the C^n tangent bundle is derived from the C^(n+1) base. -/
theorem contMDiffWithinAt_tetradMatrix_iff (n : WithTop ℕ∞) [IsManifold I (n + 1) M]
    (c : M) (X : Fin 4 → ∀ x : M, TangentSpace I x) (s : Set M) {x : M}
    (hx : x ∈ (chartAt H c).source) :
    letI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    ContMDiffWithinAt I 𝓘(ℝ, Matrix (Fin 4) (Fin 4) ℝ) n
        (fun y => tetradMatrix I b c y (fun j => X j y)) s x ↔
      ∀ j, ContMDiffWithinAt I I.tangent n
        (fun y => (⟨y, X j y⟩ : TangentBundle I M)) s x := by
  let : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  change ContMDiffWithinAt I 𝓘(ℝ, Fin 4 → Fin 4 → ℝ) n
      (fun y a j => coordinates I b c y (X j y) a) s x ↔ _
  simp only [contMDiffWithinAt_graph_iff I b n c _ s hx,
    contMDiffWithinAt_pi_module_iff]
  exact forall_comm

omit [IsManifold I 1 M] in
/-- On any subset of one base chart, the actual tetrad-coordinate matrix is C^n exactly when all four tangent-section graphs are C^n, without requiring the subset to be open. -/
theorem contMDiffOn_tetradMatrix_iff (n : WithTop ℕ∞) [IsManifold I (n + 1) M]
    (c : M) (X : Fin 4 → ∀ x : M, TangentSpace I x) {s : Set M}
    (hs : s ⊆ (chartAt H c).source) :
    letI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    ContMDiffOn I 𝓘(ℝ, Matrix (Fin 4) (Fin 4) ℝ) n
        (fun y => tetradMatrix I b c y (fun j => X j y)) s ↔
      ∀ j, ContMDiffOn I I.tangent n
        (fun y => (⟨y, X j y⟩ : TangentBundle I M)) s := by
  let : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  constructor
  · intro h j x hx
    exact (contMDiffWithinAt_tetradMatrix_iff I b n c X s (hs hx)).mp (h x hx) j
  · intro h x hx
    exact (contMDiffWithinAt_tetradMatrix_iff I b n c X s (hs hx)).mpr (fun j => h j x hx)

end FoliationQM.TangentTetradCoordinates
