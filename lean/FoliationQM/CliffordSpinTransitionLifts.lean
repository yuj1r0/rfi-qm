module
public import FoliationQM.CliffordSpinLorentzTransitions
public import FoliationQM.CliffordSpinSignKernel
public import FoliationQM.CentralTransitionDefect
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Actual pairwise Spin lifts and their central triple defect

Source scope: the local-to-global lifting content of v13 Section 7 and
`prop:takabayasi`. Independently supplied Lorentz transition data have
normalized pairwise genuine Clifford Spin lifts as separate inputs.
These inputs require only smoothness, projection on pair overlaps, and
identity on the diagonal. They do not require the Spin cocycle law or
reverse-pair compatibility.

On a genuine triple overlap the literal failure of the ordered Spin
composition law lies in the actual central two-sign kernel. Its ambient
Spin expression is smooth, and the kernel-valued function is locally
constant in the existing discrete kernel topology. Associativity and
proved centrality give the quadruple-overlap defect law. Adjacent
repeated indices normalize to one; arbitrary repeated indices are not
assumed to do so. Projected supplied Spin cocycles give honest examples
with zero defect on every triple overlap.

No arbitrary Lorentz cocycle lift, automatic removal of the defect,
cohomological characteristic-class identification, or spacetime Spin
structure is asserted by these conditional constructions.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Topology
open scoped Manifold
namespace FoliationQM.CliffordSpinTransitionLifts
open CliffordSpinMap CliffordSpinLorentz CliffordSpinSignKernel

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {B : Type*} [TopologicalSpace B] [ChartedSpace H B]
  {ι : Type*} {n : WithTop ℕ∞}

/-- The pairwise lift target retains the independently constructed actual Clifford Spin manifold model. -/
abbrev spinModel := CliffordSpinLorentzSmooth.spinModel

/-- Normalized smooth pairwise actual Spin lifts of independently specified Lorentz transitions, without any triple cocycle or reverse-pair compatibility premise. -/
structure PairLifts (D : CliffordSpinLorentzTransitions.Data I B ι n) where
  /-- The genuine Clifford Spin transition chosen for each ordered chart pair. -/
  transition : ι → ι → B → Spin
  /-- Smoothness is imposed precisely on the actual pair overlap. -/
  smooth_transition : ∀ i j, ContMDiffOn I spinModel n (transition i j)
    ((D.domain i : Set B) ∩ (D.domain j : Set B))
  /-- Every self-transition is the genuine Clifford unit on its chart. -/
  identity : ∀ i x, x ∈ D.domain i → transition i i x = 1
  /-- The physical projection agrees with the independent Lorentz transition exactly on its pair overlap. -/
  projection : ∀ i j x, x ∈ D.domain i → x ∈ D.domain j →
    lorentzHom (transition i j x) = D.transition i j x

variable {D : CliffordSpinLorentzTransitions.Data I B ι n}

/-- The actual open triple overlap, with the same supplied base topology and cover domains. -/
def tripleOverlap (D : CliffordSpinLorentzTransitions.Data I B ι n) (i j k : ι) :
    TopologicalSpace.Opens B := (D.domain i ⊓ D.domain j) ⊓ D.domain k

/-- The literal ordered triple defect of the actual pairwise Spin transitions; no off-overlap kernel assertion is made. -/
def defectValue (P : PairLifts D) (i j k : ι) (x : B) : Spin :=
  P.transition j k x * P.transition i j x * (P.transition i k x)⁻¹

/-- The literal triple defect projects to the Lorentz identity on exactly the actual triple overlap. -/
theorem defectValue_projects (P : PairLifts D) (i j k : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) (hk : x ∈ D.domain k) :
    lorentzHom (defectValue P i j k x) = 1 := by
  rw [defectValue, map_mul, map_mul, map_inv,
    P.projection j k x hj hk, P.projection i j x hi hj, P.projection i k x hi hk,
    D.comp i j k x hi hj hk, mul_inv_cancel]

/-- On a genuine triple overlap the actual defect is an element of the original physical Clifford sign kernel. -/
def defect (P : PairLifts D) (i j k : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) (hk : x ∈ D.domain k) : Kernel :=
  ⟨defectValue P i j k x, defectValue_projects P i j k x hi hj hk⟩

/-- The kernel-valued defect has precisely the displayed genuine Clifford multiplication and inverse formula. -/
theorem defect_val (P : PairLifts D) (i j k : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) (hk : x ∈ D.domain k) :
    (defect P i j k x hi hj hk).val =
      P.transition j k x * P.transition i j x * (P.transition i k x)⁻¹ := rfl

/-- On a true triple overlap the defect is exactly the identity or the genuine negative Clifford unit. -/
theorem defectValue_eq_one_or_negative (P : PairLifts D) (i j k : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) (hk : x ∈ D.domain k) :
    defectValue P i j k x = 1 ∨
      defectValue P i j k x = CliffordSpinEquivalence.negativeOne :=
  (lorentzHom_eq_one_iff _).mp (defectValue_projects P i j k x hi hj hk)

/-- A genuine triple-overlap defect commutes with every actual Clifford Spin element by the proved centrality of the physical sign kernel. -/
theorem defectValue_commute (P : PairLifts D) (i j k : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) (hk : x ∈ D.domain k) (s : Spin) :
    Commute (defectValue P i j k x) s :=
  kernel_mul_comm (defect P i j k x hi hj hk) s

/-- The ambient actual Spin defect is smooth on the precise triple overlap, by the smooth group operations and supplied pairwise regularity. -/
theorem contMDiffOn_defectValue (P : PairLifts D) (i j k : ι) :
    ContMDiffOn I spinModel n (defectValue P i j k) (tripleOverlap D i j k : Set B) := by
  have hjk : ContMDiffOn I spinModel n (P.transition j k)
      (tripleOverlap D i j k : Set B) :=
    (P.smooth_transition j k).mono (fun _ hx => ⟨hx.1.2, hx.2⟩)
  have hij : ContMDiffOn I spinModel n (P.transition i j)
      (tripleOverlap D i j k : Set B) :=
    (P.smooth_transition i j).mono (fun _ hx => hx.1)
  have hik : ContMDiffOn I spinModel n (P.transition i k)
      (tripleOverlap D i j k : Set B) :=
    (P.smooth_transition i k).mono (fun _ hx => ⟨hx.1.1, hx.2⟩)
  exact (CliffordSpinManifold.contMDiff_mul n).comp_contMDiffOn
    (((CliffordSpinManifold.contMDiff_mul n).comp_contMDiffOn (hjk.prodMk hij)).prodMk
      ((CliffordSpinManifold.contMDiff_inv n).comp_contMDiffOn hik))

/-- The actual kernel-valued defect on the original open triple-overlap subtype. -/
def kernelDefect (P : PairLifts D) (i j k : ι) : tripleOverlap D i j k → Kernel :=
  fun x => defect P i j k x.val x.property.1.1 x.property.1.2 x.property.2

/-- The kernel defect's actual Spin value agrees exactly with the literal ambient defect expression. -/
theorem kernelDefect_val (P : PairLifts D) (i j k : ι) (x : tripleOverlap D i j k) :
    (kernelDefect P i j k x).val = defectValue P i j k x.val := rfl

/-- The kernel-valued triple defect is continuous for the original subtype topology of the actual discrete sign kernel. -/
theorem continuous_kernelDefect (P : PairLifts D) (i j k : ι) :
    Continuous (kernelDefect P i j k) :=
  (contMDiffOn_defectValue P i j k).continuousOn.domRestrict.subtype_mk _

/-- The actual triple sign defect is locally constant on its genuine open overlap because the proved physical sign kernel is discrete. -/
theorem isLocallyConstant_kernelDefect (P : PairLifts D) (i j k : ι) :
    IsLocallyConstant (kernelDefect P i j k) :=
  (IsLocallyConstant.iff_continuous _).mpr (continuous_kernelDefect P i j k)

/-- The actual kernel defect is constant between any two points of a preconnected triple overlap. -/
theorem kernelDefect_eq_of_isPreconnected (P : PairLifts D) (i j k : ι)
    (hT : IsPreconnected (tripleOverlap D i j k : Set B))
    (x y : tripleOverlap D i j k) : kernelDefect P i j k x = kernelDefect P i j k y := by
  let _ : PreconnectedSpace (tripleOverlap D i j k) :=
    isPreconnected_iff_preconnectedSpace.mp hT
  exact (isLocallyConstant_kernelDefect P i j k).apply_eq_of_preconnectedSpace x y

/-- Every nonempty preconnected triple overlap carries one fixed actual kernel sign as its entire defect. -/
theorem exists_constant_kernelDefect (P : PairLifts D) (i j k : ι)
    (hT : IsPreconnected (tripleOverlap D i j k : Set B))
    (hne : (tripleOverlap D i j k : Set B).Nonempty) :
    ∃ z : Kernel, ∀ x : tripleOverlap D i j k, kernelDefect P i j k x = z := by
  obtain ⟨x, hx⟩ := hne
  exact ⟨kernelDefect P i j k ⟨x, hx⟩,
    fun y => kernelDefect_eq_of_isPreconnected P i j k hT y ⟨x, hx⟩⟩

/-- Vanishing of the literal defect is equivalent to the actual Spin composition equation, without assuming that equation as pair-lift input. -/
theorem defectValue_eq_one_iff (P : PairLifts D) (i j k : ι) (x : B) :
    defectValue P i j k x = 1 ↔
      P.transition j k x * P.transition i j x = P.transition i k x :=
  mul_inv_eq_one

/-- An adjacent repeated initial index has trivial actual defect by diagonal normalization on that chart. -/
theorem defectValue_self_left (P : PairLifts D) (i k : ι) (x : B)
    (hi : x ∈ D.domain i) : defectValue P i i k x = 1 := by
  simp only [defectValue, P.identity i x hi, mul_one, mul_inv_cancel]

/-- An adjacent repeated final index has trivial actual defect by diagonal normalization on that chart. -/
theorem defectValue_self_right (P : PairLifts D) (i k : ι) (x : B)
    (hk : x ∈ D.domain k) : defectValue P i k k x = 1 := by
  simp only [defectValue, P.identity k x hk, one_mul, mul_inv_cancel]

/-- The genuine central triple defects obey the ordered quadruple-overlap equation, derived from associativity and actual kernel centrality. -/
theorem defectValue_quadruple (P : PairLifts D) (i j k l : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) (hk : x ∈ D.domain k)
    (_hl : x ∈ D.domain l) :
    defectValue P j k l x * defectValue P i j l x =
      defectValue P i j k x * defectValue P i k l x :=
  CentralTransitionDefect.defect_quadruple (fun a b => P.transition a b x) i j k l
    (defectValue_commute P i j k x hi hj hk (P.transition k l x))

/-- Every supplied actual Spin cocycle gives normalized pair lifts of its literal projected independent Lorentz data. -/
def ofSpinData (S : CliffordSpinPolarCocycle.Data I B ι n) :
    PairLifts (CliffordSpinLorentzTransitions.ofSpinData S) where
  transition := S.transition
  smooth_transition := S.smooth_transition
  identity := S.identity
  projection _ _ _ _ _ := rfl

/-- Pair lifts constructed from supplied actual Spin cocycles retain the original genuine transition values. -/
theorem ofSpinData_transition (S : CliffordSpinPolarCocycle.Data I B ι n)
    (i j : ι) (x : B) : (ofSpinData S).transition i j x = S.transition i j x := rfl

/-- The triple defect of a supplied actual Spin cocycle vanishes on its genuine triple overlap by its independently supplied composition law. -/
theorem ofSpinData_defectValue (S : CliffordSpinPolarCocycle.Data I B ι n)
    (i j k : ι) (x : B) (hi : x ∈ S.domain i) (hj : x ∈ S.domain j)
    (hk : x ∈ S.domain k) : defectValue (ofSpinData S) i j k x = 1 :=
  (defectValue_eq_one_iff _ _ _ _ _).mpr (S.comp i j k x hi hj hk)

/-- The kernel-valued defect of every supplied actual Spin cocycle is precisely the identity kernel element. -/
theorem ofSpinData_defect (S : CliffordSpinPolarCocycle.Data I B ι n)
    (i j k : ι) (x : B) (hi : x ∈ S.domain i) (hj : x ∈ S.domain j)
    (hk : x ∈ S.domain k) : defect (ofSpinData S) i j k x hi hj hk = 1 :=
  Subtype.ext (ofSpinData_defectValue S i j k x hi hj hk)

/-- Every supplied open cover has literal identity pair lifts of its projected identity Lorentz data, requiring no simple-connectivity hypothesis on the base. -/
def identityPairLifts (U : ι → TopologicalSpace.Opens B) (hU : ∀ x : B, ∃ i, x ∈ U i) :
    PairLifts (CliffordSpinLorentzTransitions.ofSpinData
      (CliffordSpinPolarCocycle.identityData (I := I) (n := n) U hU)) :=
  ofSpinData (CliffordSpinPolarCocycle.identityData U hU)

/-- The explicit identity pair-lift example is the genuine Clifford unit everywhere, including off-overlap filler values. -/
theorem identityPairLifts_transition (U : ι → TopologicalSpace.Opens B)
    (hU : ∀ x : B, ∃ i, x ∈ U i) (i j : ι) (x : B) :
    (identityPairLifts (I := I) (n := n) U hU).transition i j x = 1 := rfl

end FoliationQM.CliffordSpinTransitionLifts
