module
public import FoliationQM.CliffordSpinTopology
public import FoliationQM.SpecialLinearGroupManifold
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# Smooth structure on the actual Minkowski Clifford Spin group

Source scope: the actual Clifford-spin factor underlying v13
`prop:takabayasi`, `eq:takabayasi_polar`, and `thm:dirac_lift`.
The literal Mathlib Spin group retains the canonical Clifford subtype
topology. Its proved Pauli homeomorphism pulls back the independently
constructed six-dimensional rational atlas on determinant-one matrices.
The resulting charts have exactly the existing matrix chart transitions.
The actual Spin-to-matrix map and its inverse are smooth, and literal
Clifford multiplication and inversion give a real Lie group to every
order. A smoothness criterion uses the actual ambient Pauli matrices.

This establishes a compatible smooth atlas on actual Spin. It does not
assert a universal covering, simple connectivity, an independently
constructed Lorentz target atlas, a spacetime spin structure, or a
variational derivation of the Dirac equation.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Operator Manifold
open Function Set Topology
namespace FoliationQM.CliffordSpinManifold
open CliffordSpinMap CliffordSpinEquivalence CliffordSpinTopology SourcePolarDatum SpinorMatrix

/-- The actual Spin atlas uses the existing three-complex-coordinate real model of the special linear group. -/
abbrev Model := SpecialLinearCharts.Model

/-- The actual Clifford Spin group is second countable in its existing canonical subtype topology. -/
instance instSecondCountableTopologySpin : SecondCountableTopology Spin :=
  spinHomeomorph.secondCountableTopology

/-- The canonical Spin topology carries the pullback of the independently constructed matrix rational atlas through the proved Pauli homeomorphism. -/
instance instChartedSpaceSpin : ChartedSpace Model Spin where
  atlas := {e | ∃ e' ∈ atlas Model SpecialLinearMatrix,
    e = spinHomeomorph.transOpenPartialHomeomorph e'}
  chartAt s := spinHomeomorph.transOpenPartialHomeomorph
    (chartAt Model (spinHomeomorph s))
  mem_chart_source s := mem_chart_source Model (spinHomeomorph s)
  chart_mem_atlas s := ⟨_, chart_mem_atlas Model (spinHomeomorph s), rfl⟩

/-- Every preferred Spin chart is exactly a preferred matrix chart composed with the actual Pauli map. -/
theorem chartAt_eq (s : Spin) :
    chartAt Model s = spinHomeomorph.transOpenPartialHomeomorph
      (chartAt Model (spinHomeomorph s)) := rfl

/-- The genuine Spin model has real dimension six. -/
theorem model_finrank : Module.finrank ℝ Model = 6 := by
  simp [Model, SpecialLinearCharts.Model, Module.finrank_pi_fintype,
    Complex.finrank_real_complex]

/-- Actual Spin chart transitions are exactly matrix chart transitions, proving a real manifold to every order. -/
instance instIsManifoldSpin (n : WithTop ℕ∞) : IsManifold 𝓘(ℝ, Model) n Spin where
  compatible := by
    rintro e e' ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    rw [Homeomorph.transOpenPartialHomeomorph_symm_trans]
    exact (contDiffGroupoid n 𝓘(ℝ, Model)).compatible ha hb

/-- The actual Pauli Spin homomorphism is smooth between the explicitly specified Spin and matrix atlases to every order. -/
theorem contMDiff_toMatrix (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℝ, Model) 𝓘(ℝ, Model) n CliffordSpinMap.toMatrix := by
  change ContMDiff 𝓘(ℝ, Model) 𝓘(ℝ, Model) n spinHomeomorph
  intro s
  have hh := (contMDiff_id (I := 𝓘(ℝ, Model)) (n := n) :
    ContMDiff 𝓘(ℝ, Model) 𝓘(ℝ, Model) n (fun A : SpecialLinearMatrix => A))
      (spinHomeomorph s)
  rw [contMDiffAt_iff] at hh ⊢
  refine ⟨spinHomeomorph.continuous.continuousAt, ?_⟩
  convert hh.2 using 1
  all_goals simp [chartAt_eq, Function.comp_def]

/-- The actual inverse Spin identification is smooth from the existing matrix manifold to the actual Clifford Spin manifold. -/
theorem contMDiff_spinEquiv_symm (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℝ, Model) 𝓘(ℝ, Model) n spinEquiv.symm := by
  change ContMDiff 𝓘(ℝ, Model) 𝓘(ℝ, Model) n spinHomeomorph.symm
  intro A
  have hh := (contMDiff_id (I := 𝓘(ℝ, Model)) (n := n) :
    ContMDiff 𝓘(ℝ, Model) 𝓘(ℝ, Model) n (fun B : SpecialLinearMatrix => B)) A
  rw [contMDiffAt_iff] at hh ⊢
  refine ⟨spinHomeomorph.symm.continuous.continuousAt, ?_⟩
  convert hh.2 using 1
  all_goals simp [chartAt_eq, Function.comp_def]

/-- The actual Clifford Spin identification is a genuine diffeomorphism for its compatible six-dimensional atlas and the independent rational matrix atlas. -/
def spinDiffeomorph (n : WithTop ℕ∞) :
    Diffeomorph 𝓘(ℝ, Model) 𝓘(ℝ, Model) Spin SpecialLinearMatrix n where
  toEquiv := spinHomeomorph.toEquiv
  contMDiff_toFun := contMDiff_toMatrix n
  contMDiff_invFun := contMDiff_spinEquiv_symm n

/-- The smooth identification evaluates to the actual Pauli homomorphism. -/
theorem spinDiffeomorph_apply (n : WithTop ℕ∞) (s : Spin) :
    spinDiffeomorph n s = CliffordSpinMap.toMatrix s := rfl

/-- The inverse smooth identification evaluates to the previously proved actual Clifford inverse. -/
theorem spinDiffeomorph_symm_apply (n : WithTop ℕ∞) (A : SpecialLinearMatrix) :
    (spinDiffeomorph n).symm A = spinEquiv.symm A := rfl

/-- The diffeomorphism retains exactly the homeomorphism for the independent canonical Clifford and matrix topologies. -/
theorem spinDiffeomorph_toHomeomorph (n : WithTop ℕ∞) :
    (spinDiffeomorph n).toHomeomorph = spinHomeomorph := rfl

section GeneralSource
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  {n : WithTop ℕ∞} {f : M → Spin} {s : Set M} {x : M}

/-- On every charted source and within every subset, actual Spin smoothness is equivalent to smoothness of its genuine ambient Pauli matrix values. -/
theorem contMDiffWithinAt_iff_matrix :
    ContMDiffWithinAt I 𝓘(ℝ, Model) n f s x ↔
      ContMDiffWithinAt I 𝓘(ℝ, Mat2) n
        (fun y => (CliffordSpinMap.toMatrix (f y)).val) s x := by
  constructor
  · intro hf
    exact SpecialLinearManifold.contMDiffWithinAt_iff_value.mp
      ((spinDiffeomorph n).contMDiffAt.comp_contMDiffWithinAt x hf)
  · intro hf
    have hm := SpecialLinearManifold.contMDiffWithinAt_iff_value.mpr hf
    convert (spinDiffeomorph n).symm.contMDiffAt.comp_contMDiffWithinAt x hm using 1
    funext y
    exact (spinEquiv.symm_apply_apply (f y)).symm

/-- Actual Spin smoothness at a point is equivalent to smoothness of its ambient Pauli matrix values. -/
theorem contMDiffAt_iff_matrix :
    ContMDiffAt I 𝓘(ℝ, Model) n f x ↔
      ContMDiffAt I 𝓘(ℝ, Mat2) n
        (fun y => (CliffordSpinMap.toMatrix (f y)).val) x :=
  contMDiffWithinAt_iff_matrix

/-- Actual Spin smoothness on an arbitrary set is equivalent to smoothness of the ambient Pauli matrix field there. -/
theorem contMDiffOn_iff_matrix :
    ContMDiffOn I 𝓘(ℝ, Model) n f s ↔
      ContMDiffOn I 𝓘(ℝ, Mat2) n
        (fun y => (CliffordSpinMap.toMatrix (f y)).val) s := by
  constructor
  · intro hf y hy
    exact contMDiffWithinAt_iff_matrix.mp (hf y hy)
  · intro hf y hy
    exact contMDiffWithinAt_iff_matrix.mpr (hf y hy)

/-- Global actual Spin smoothness is equivalent to smoothness of the genuine ambient Pauli matrix field. -/
theorem contMDiff_iff_matrix :
    ContMDiff I 𝓘(ℝ, Model) n f ↔
      ContMDiff I 𝓘(ℝ, Mat2) n
        (fun y => (CliffordSpinMap.toMatrix (f y)).val) := by
  constructor
  · intro hf y
    exact contMDiffAt_iff_matrix.mp (hf y)
  · intro hf y
    exact contMDiffAt_iff_matrix.mpr (hf y)

end GeneralSource

/-- Literal Clifford Spin multiplication is jointly smooth for the compatible atlas. -/
theorem contMDiff_mul (n : WithTop ℕ∞) :
    ContMDiff ((𝓘(ℝ, Model)).prod 𝓘(ℝ, Model)) 𝓘(ℝ, Model) n
      (fun p : Spin × Spin => p.1 * p.2) := by
  have hm := (spinDiffeomorph n).symm.contMDiff.comp
    ((SpecialLinearGroupManifold.contMDiff_mul n).comp
      (((contMDiff_toMatrix n).comp contMDiff_fst).prodMk
        ((contMDiff_toMatrix n).comp contMDiff_snd)))
  convert hm using 1
  funext p
  change p.1 * p.2 = spinEquiv.symm (spinEquiv p.1 * spinEquiv p.2)
  rw [← map_mul, spinEquiv.symm_apply_apply]

/-- Literal Clifford Spin inversion is smooth for the compatible atlas. -/
theorem contMDiff_inv (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℝ, Model) 𝓘(ℝ, Model) n (fun s : Spin => s⁻¹) := by
  have hi := (spinDiffeomorph n).symm.contMDiff.comp
    ((SpecialLinearGroupManifold.contMDiff_inv n).comp (contMDiff_toMatrix n))
  convert hi using 1
  funext s
  change s⁻¹ = spinEquiv.symm ((spinEquiv s)⁻¹)
  rw [← map_inv, spinEquiv.symm_apply_apply]

/-- The genuine Minkowski Clifford Spin group is a real Lie group to every differentiability order. -/
instance instLieGroupSpin (n : WithTop ℕ∞) : LieGroup 𝓘(ℝ, Model) n Spin where
  contMDiff_mul := contMDiff_mul n
  contMDiff_inv := contMDiff_inv n

end FoliationQM.CliffordSpinManifold
