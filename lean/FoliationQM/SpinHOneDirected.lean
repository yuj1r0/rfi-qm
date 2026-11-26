module
public import FoliationQM.SpinHOneDescent
public import FoliationQM.SignCommonRefinement
public import Mathlib.Algebra.Colimit.DirectLimit

/-!
# A directed system of covers for smooth sign cohomology

For the global Spin-frame component of v13 `prop:takabayasi`, use open
neighborhoods indexed by their base points. Pointwise intersections give
common refinements. Every open cover, with indices in any universe,
admits such a refinement.
-/

@[expose] public section
noncomputable section
open Set
namespace FoliationQM.SpinHOneDirected
open CliffordSpinCoverRefinement SpinHOneRestriction SpinSignHOne

variable {B ι : Type*} [TopologicalSpace B]

/-- A family assigning an open neighborhood to each point of the base. -/
structure Cover (B : Type*) [TopologicalSpace B] where
  /-- The neighborhood indexed by a base point. -/
  domain : B → TopologicalSpace.Opens B
  /-- Each indexing point belongs to its assigned neighborhood. -/
  mem : ∀ x, x ∈ domain x

/-- The neighborhoods cover the base, including when the base is empty. -/
theorem Cover.covers (P : Cover B) (x : B) : ∃ i, x ∈ P.domain i := ⟨x, P.mem x⟩

instance : Nonempty (Cover B) := ⟨⟨fun _ => ⊤, fun _ => Set.mem_univ _⟩⟩

/-- Increasing in the order shrinks the neighborhood at each point. -/
instance : Preorder (Cover B) where
  le P Q := ∀ x, Q.domain x ≤ P.domain x
  le_refl _ _ := le_rfl
  le_trans _ _ _ h k x := (k x).trans (h x)

/-- Intersect the two assigned neighborhoods of every point. -/
def common (P Q : Cover B) : Cover B :=
  ⟨fun x => P.domain x ⊓ Q.domain x, fun x => ⟨P.mem x, Q.mem x⟩⟩

/-- The common neighborhoods refine the first family at the same points. -/
theorem le_common_left (P Q : Cover B) : P ≤ common P Q := fun _ => inf_le_left

/-- The common neighborhoods refine the second family at the same points. -/
theorem le_common_right (P Q : Cover B) : Q ≤ common P Q := fun _ => inf_le_right

instance : IsDirectedOrder (Cover B) where
  directed P Q := ⟨common P Q, le_common_left P Q, le_common_right P Q⟩

/-- Any assignment of containing original charts presents the neighborhoods as an open refinement. -/
def Cover.asRefinement (P : Cover B) {U : ι → TopologicalSpace.Opens B}
    (p : B → ι) (hp : ∀ x, P.domain x ≤ U (p x)) : Refinement U B where
  parent := p
  domain := P.domain
  covers := P.covers
  subset := hp

/-- Ordered neighborhoods form a refinement with the identity parent assignment. -/
def refine {P Q : Cover B} (h : P ≤ Q) : Refinement P.domain B :=
  Q.asRefinement id h

/-- Choose a containing chart for each point of an arbitrarily indexed open cover. -/
def anchor (U : ι → TopologicalSpace.Opens B) (hU : ∀ x : B, ∃ i, x ∈ U i) : Cover B :=
  ⟨(SignCommonRefinement.pointCover U hU).domain, SignCommonRefinement.pointCover_mem U hU⟩

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [ChartedSpace H B]

/-- The transition map from a coarser to a finer family is restriction of sign classes. -/
def transition (I : ModelWithCorners ℝ E H) (n : WithTop ℕ∞) (P Q : Cover B) (h : P ≤ Q) :
    H1 I P.domain n →* H1 I Q.domain n :=
  restrictHom (refine h)

variable {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞}

/-- Shrinking neighborhoods never identifies two distinct original sign classes. -/
theorem transition_injective {P Q : Cover B} (h : P ≤ Q) :
    Function.Injective (transition I n P Q h) :=
  SpinHOneDescent.restrictHom_injective (refine h)

instance : DirectedSystem (fun P : Cover B => H1 I P.domain n)
    (fun _ _ h => (transition I n _ _ h : _ → _)) where
  map_self P x := restrictHom_identity P.covers x
  map_map _ _ _ h k x := restrictHom_compose (refine h) (refine k) x

end FoliationQM.SpinHOneDirected
