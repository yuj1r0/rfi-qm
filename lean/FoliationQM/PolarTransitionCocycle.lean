module
public import FoliationQM.GaugePolarFields
public import Mathlib.Topology.FiberBundle.Basic

/-!
# Supplied smooth determinant-one transition cocycles

Source: the local quotient-bundle interpretation in v13 `prop:takabayasi`.
The input consists of an actual open cover and actual determinant-one matrix
transition functions, with regularity on overlaps and the usual independent
cocycle identities. A transition indexed i,j takes coordinates in chart i
to coordinates in chart j, so the order on triple overlaps is G_jk * G_ij.

The polar and spinor coordinate changes are the already proved actual matrix
actions. Their identities, overlap smoothness and equivariance are derived
from those inputs. A chosen cover index is used only to select local charts;
no continuity of this selection is asserted. These supplied transition data
do not identify an abstract spacetime Spin structure.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator Manifold
open Function Set Topology
namespace FoliationQM.PolarTransitionCocycle
open SourcePolarDatum PolarSignQuotient DiracMatrices

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (B : Type*) [TopologicalSpace B] [ChartedSpace H B]

/-- An independently supplied open cover and actual smooth matrix transitions, with chart i to chart j orientation and the ordinary group cocycle identities. -/
structure Data (ι : Type*) (n : WithTop ℕ∞) where
  /-- The actual open chart domains. -/
  domain : ι → TopologicalSpace.Opens B
  /-- Every base point belongs to a supplied chart domain. -/
  covers : ∀ x : B, ∃ i, x ∈ domain i
  /-- The actual determinant-one matrix carrying chart i coordinates to chart j coordinates. -/
  transition : ι → ι → B → SpecialLinearMatrix
  /-- Transition regularity is required on precisely the pairwise chart overlap. -/
  smooth_transition : ∀ i j, ContMDiffOn I 𝓘(ℝ, SpecialLinearCharts.Model) n
    (transition i j) ((domain i : Set B) ∩ (domain j : Set B))
  /-- The self-transition is the group identity on the actual chart domain. -/
  identity : ∀ i x, x ∈ domain i → transition i i x = 1
  /-- Actual group products obey the oriented cocycle identity on triple overlaps. -/
  comp : ∀ i j k x, x ∈ domain i → x ∈ domain j → x ∈ domain k →
    transition j k x * transition i j x = transition i k x

variable {I B} {ι : Type*} {n : WithTop ℕ∞} (D : Data I B ι n)

/-- Choose an index whose actual open domain contains the point, using only the supplied covering property. -/
def indexAt (x : B) : ι := Classical.choose (D.covers x)

/-- The selected index contains the actual point; no continuity of the index selection is needed. -/
theorem mem_domain_indexAt (x : B) : x ∈ D.domain (indexAt D x) :=
  Classical.choose_spec (D.covers x)

/-- On an overlap, the actual reverse transition is the group inverse of the forward transition. -/
theorem transition_reverse (i j : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) :
    D.transition j i x = (D.transition i j x)⁻¹ := by
  have h := D.comp i j i x hi hj hi
  rw [D.identity i x hi] at h
  calc
    D.transition j i x = D.transition j i x *
        (D.transition i j x * (D.transition i j x)⁻¹) := by rw [mul_inv_cancel, mul_one]
    _ = (D.transition j i x * D.transition i j x) * (D.transition i j x)⁻¹ :=
      (mul_assoc _ _ _).symm
    _ = (D.transition i j x)⁻¹ := by rw [h, one_mul]

/-- The actual polar coordinate change preserves density and left-multiplies the frame class by the supplied transition matrix. -/
def polarChange (i j : ι) (x : B) (p : DensityFrameManifold.Product) :
    DensityFrameManifold.Product := DensityFrameAction.productAction (D.transition i j x) p

/-- The actual spinor coordinate change is multiplication by the independently defined represented transition matrix. -/
def spinorChange (i j : ι) (x : B) (q : RegularSpinor) : RegularSpinor :=
  RegularSpinorAction.act (D.transition i j x) q

/-- The actual polar transition is the identity on its chart's domain. -/
theorem polarChange_self (i : ι) (x : B) (hx : x ∈ D.domain i)
    (p : DensityFrameManifold.Product) : polarChange D i i x p = p := by
  simp only [polarChange, D.identity i x hx, DensityFrameAction.productAction_one]

/-- The actual spinor transition is the identity on its chart's domain. -/
theorem spinorChange_self (i : ι) (x : B) (hx : x ∈ D.domain i)
    (q : RegularSpinor) : spinorChange D i i x q = q := by
  simp only [spinorChange, D.identity i x hx, RegularSpinorAction.act_one]

/-- Actual polar transitions compose in the supplied chart-change order on each triple overlap. -/
theorem polarChange_comp (i j k : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) (hk : x ∈ D.domain k)
    (p : DensityFrameManifold.Product) :
    polarChange D j k x (polarChange D i j x p) = polarChange D i k x p := by
  simp only [polarChange, ← DensityFrameAction.productAction_mul, D.comp i j k x hi hj hk]

/-- Actual represented-spinor transitions compose in the same supplied order on each triple overlap. -/
theorem spinorChange_comp (i j k : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) (hk : x ∈ D.domain k)
    (q : RegularSpinor) :
    spinorChange D j k x (spinorChange D i j x q) = spinorChange D i k x q := by
  simp only [spinorChange, ← RegularSpinorAction.act_mul, D.comp i j k x hi hj hk]

/-- Actual polar realization intertwines the supplied polar and represented-spinor coordinate changes at every point. -/
theorem change_equivariant (i j : ι) (x : B) (p : DensityFrameManifold.Product) :
    SourcePolarProductQuotient.productRegularHomeomorph (polarChange D i j x p) =
      spinorChange D i j x (SourcePolarProductQuotient.productRegularHomeomorph p) :=
  RegularSpinorAction.realization_equivariant (D.transition i j x) p

/-- The actual polar transition is smooth jointly in its base and fiber variables on the exact overlap domain. -/
theorem contMDiffOn_polarChange (i j : ι) :
    ContMDiffOn (I.prod DensityFrameManifold.model) DensityFrameManifold.model n
      (fun p : B × DensityFrameManifold.Product => polarChange D i j p.1 p.2)
      (((D.domain i : Set B) ∩ (D.domain j : Set B)) ×ˢ univ) := by
  have hg : ContMDiffOn (I.prod DensityFrameManifold.model) 𝓘(ℝ, SpecialLinearCharts.Model) n
      (fun p : B × DensityFrameManifold.Product => D.transition i j p.1)
      (((D.domain i : Set B) ∩ (D.domain j : Set B)) ×ˢ univ) :=
    (D.smooth_transition i j).comp contMDiff_fst.contMDiffOn (fun _ hx => hx.1)
  exact (DensityFrameAction.contMDiff_productAction n).comp_contMDiffOn
    (hg.prodMk contMDiff_snd.contMDiffOn)

/-- The actual spinor transition is smooth jointly in base and fiber variables on the exact overlap domain. -/
theorem contMDiffOn_spinorChange (i j : ι) :
    ContMDiffOn (I.prod 𝓘(ℝ, Spinor)) 𝓘(ℝ, Spinor) n
      (fun p : B × RegularSpinor => spinorChange D i j p.1 p.2)
      (((D.domain i : Set B) ∩ (D.domain j : Set B)) ×ˢ univ) := by
  have hg : ContMDiffOn (I.prod 𝓘(ℝ, Spinor)) 𝓘(ℝ, SpecialLinearCharts.Model) n
      (fun p : B × RegularSpinor => D.transition i j p.1)
      (((D.domain i : Set B) ∩ (D.domain j : Set B)) ×ˢ univ) :=
    (D.smooth_transition i j).comp contMDiff_fst.contMDiffOn (fun _ hx => hx.1)
  have h := (RegularSpinorAction.contMDiff_act n).comp_contMDiffOn
    (hg.prodMk contMDiff_snd.contMDiffOn)
  simpa only [Function.comp_def, spinorChange] using h

end FoliationQM.PolarTransitionCocycle
