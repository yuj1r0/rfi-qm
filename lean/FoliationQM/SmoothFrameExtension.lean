module
public import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame

/-!
# Smooth local extension of an independently specified fiber basis

Source scope: the geometric tetrad component of v13 `prop:takabayasi`.

An arbitrary basis in one actual vector-bundle fiber is transported through
an original compatible bundle trivialization to a fixed model-fiber basis.
The corresponding original local frame is smooth on the genuine open base
domain and returns precisely the prescribed basis at the anchor. Its graph
coordinates and pointwise basis are explicit; outside that domain the
section functions use the original local-frame zero extension.

No metric, orthogonality, orientation, or smooth frame extension is supplied
as an input. This is the local seed construction for subsequent metric
normalization and preserves the original vector-bundle topology and atlas.
-/

@[expose] public section
noncomputable section
open Bundle Set
open scoped Manifold Topology
namespace FoliationQM.SmoothFrameExtension

variable {E H B F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace B] [ChartedSpace H B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {ι : Type*}

/-- The actual open domain of the original bundle trivialization centered at the anchor. -/
def domain (x : B) : TopologicalSpace.Opens B :=
  ⟨(trivializationAt F V x).baseSet, (trivializationAt F V x).open_baseSet⟩

omit [NormedSpace ℝ F] [∀ x, Module ℝ (V x)] [VectorBundle ℝ F V]
  [∀ x, AddCommGroup (V x)] in
/-- The specified anchor belongs to its actual original trivialization domain. -/
theorem mem_domain (x : B) : x ∈ domain (F := F) (V := V) x :=
  mem_baseSet_trivializationAt F V x

/-- The prescribed actual fiber basis is transported to a fixed basis of the original model fiber. -/
def modelBasis (x : B) (b : Module.Basis ι ℝ (V x)) : Module.Basis ι ℝ F :=
  b.map ((trivializationAt F V x).linearEquivAt (R := ℝ) x (mem_domain (F := F) x))

/-- The actual seed sections are the original trivialization's local frame for the transported anchor basis. -/
def frame (x : B) (b : Module.Basis ι ℝ (V x)) : ι → (y : B) → V y :=
  (trivializationAt F V x).localFrame (modelBasis (F := F) x b)

/-- On the actual anchor chart, the extended sections are an explicit original-trivialization basis of each fiber. -/
def basisAt (x : B) (b : Module.Basis ι ℝ (V x))
    (y : B) (hy : y ∈ domain (F := F) (V := V) x) : Module.Basis ι ℝ (V y) :=
  (trivializationAt F V x).basisAt (modelBasis (F := F) x b) hy

/-- Each section agrees with the corresponding actual fiber basis vector on the true extension domain. -/
theorem frame_eq_basisAt (x : B) (b : Module.Basis ι ℝ (V x))
    (y : B) (hy : y ∈ domain (F := F) (V := V) x) (i : ι) :
    frame (F := F) x b i y = basisAt (F := F) x b y hy i :=
  (trivializationAt F V x).localFrame_apply_of_mem_baseSet (modelBasis (F := F) x b) hy

/-- Outside the original chart domain the total section function uses exactly the original local-frame zero value. -/
theorem frame_eq_zero_of_notMem (x : B) (b : Module.Basis ι ℝ (V x))
    (y : B) (hy : y ∉ domain (F := F) (V := V) x) (i : ι) : frame (F := F) x b i y = 0 :=
  (trivializationAt F V x).localFrame_apply_of_notMem (modelBasis (F := F) x b) hy

/-- The smooth seed section returns exactly the independently supplied fiber vector at its prescribed anchor. -/
theorem frame_at (x : B) (b : Module.Basis ι ℝ (V x)) (i : ι) : frame (F := F) x b i x = b i := by
  rw [frame_eq_basisAt (F := F) x b x (mem_domain (F := F) x)]
  exact ((trivializationAt F V x).linearEquivAt (R := ℝ) x (mem_domain (F := F) x)).symm_apply_apply (b i)

/-- The entire extended pointwise basis at the anchor is the originally supplied basis, without changing its order or vectors. -/
theorem basisAt_anchor (x : B) (b : Module.Basis ι ℝ (V x)) :
    basisAt (F := F) x b x (mem_domain (F := F) x) = b := by
  apply DFunLike.ext
  intro i
  exact (frame_eq_basisAt (F := F) x b x (mem_domain (F := F) x) i).symm.trans (frame_at (F := F) x b i)

/-- The graph of each actual extended vector has a constant model-fiber coordinate in the original anchor trivialization, on precisely its true domain. -/
theorem frame_coordinates (x : B) (b : Module.Basis ι ℝ (V x))
    (y : B) (hy : y ∈ domain (F := F) (V := V) x) (i : ι) :
    (trivializationAt F V x) (⟨y, frame (F := F) x b i y⟩ : TotalSpace F V) = (y, modelBasis (F := F) x b i) := by
  rw [frame_eq_basisAt (F := F) x b y hy]
  change (trivializationAt F V x)
    (⟨y, (trivializationAt F V x).symm y (modelBasis (F := F) x b i)⟩ : TotalSpace F V) = _
  exact (trivializationAt F V x).apply_mk_symm hy (modelBasis (F := F) x b i)

/-- The actual extended vectors are linearly independent on every fiber of the true original chart domain. -/
theorem linearIndependent_frame (x : B) (b : Module.Basis ι ℝ (V x))
    (y : B) (hy : y ∈ domain (F := F) (V := V) x) :
    LinearIndependent ℝ (fun i => frame (F := F) x b i y) := by
  simpa only [frame_eq_basisAt (F := F) x b y hy] using (basisAt (F := F) x b y hy).linearIndependent

/-- The actual extended vectors span every fiber over the true original chart domain. -/
theorem span_frame (x : B) (b : Module.Basis ι ℝ (V x))
    (y : B) (hy : y ∈ domain (F := F) (V := V) x) :
    Submodule.span ℝ (range (fun i => frame (F := F) x b i y)) = ⊤ := by
  simpa only [frame_eq_basisAt (F := F) x b y hy] using (basisAt (F := F) x b y hy).span_eq

variable {n : WithTop ℕ∞} [ContMDiffVectorBundle n F V I]

/-- The prescribed anchor basis extends to a genuine smooth local frame on its actual original trivialization domain. -/
theorem isLocalFrameOn_frame (x : B) (b : Module.Basis ι ℝ (V x)) :
    IsLocalFrameOn I F n (frame (F := F) x b) (domain (F := F) (V := V) x : Set B) :=
  (trivializationAt F V x).isLocalFrameOn_localFrame_baseSet I n (modelBasis (F := F) x b)

/-- Each actual extended section graph is smooth on the true anchor chart domain. -/
theorem contMDiffOn_frame (x : B) (b : Module.Basis ι ℝ (V x)) (i : ι) :
    ContMDiffOn I (I.prod 𝓘(ℝ, F)) n
      (fun y => (⟨y, frame (F := F) x b i y⟩ : TotalSpace F V)) (domain (F := F) (V := V) x : Set B) :=
  (isLocalFrameOn_frame (I := I) (n := n) x b).contMDiffOn i

/-- Every point of the original chart has an actual neighborhood on which each extended section graph is smooth. -/
theorem contMDiffAt_frame (x : B) (b : Module.Basis ι ℝ (V x))
    (y : B) (hy : y ∈ domain (F := F) (V := V) x) (i : ι) :
    ContMDiffAt I (I.prod 𝓘(ℝ, F)) n (fun z => (⟨z, frame (F := F) x b i z⟩ : TotalSpace F V)) y :=
  (contMDiffOn_frame (I := I) (n := n) x b i).contMDiffAt ((domain (F := F) x).isOpen.mem_nhds hy)

/-- Any independently specified actual fiber basis has a smooth local extension on an explicitly given original open chart, with the prescribed anchor values exact. -/
theorem exists_extension (x : B) (b : Module.Basis ι ℝ (V x)) :
    ∃ U : TopologicalSpace.Opens B, x ∈ U ∧
      ∃ s : ι → (y : B) → V y, IsLocalFrameOn I F n s (U : Set B) ∧ ∀ i, s i x = b i :=
  ⟨domain (F := F) x, mem_domain (F := F) x, frame (F := F) x b, isLocalFrameOn_frame (F := F) x b, frame_at (F := F) x b⟩

end FoliationQM.SmoothFrameExtension
