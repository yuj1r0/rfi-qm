module
public import FoliationQM.PolarTransitionCocycle

/-!
# Actual changes of local frames for supplied polar transition cocycles

Source: the supplied-transition interpretation of v13 `prop:takabayasi`.
A frame change is an independently supplied determinant-one matrix function
for each actual chart, with smoothness required only on that chart's domain.
Its values outside the domain impose no extra regularity requirement.

The transformed transition is G'_ij = h_j G_ij h_i⁻¹ for the established
chart-i-to-chart-j convention. Genuine group identities and overlap
regularity give an actual new cocycle with the same open cover and exactly
the same selected index. Actual polar and represented-spinor actions
intertwine the transitions in both directions. Their local joint smoothness
is proved only on each chart times its fiber. Identity, inverse, and
successive frame changes obey actual equality of the constructed cocycles.
These are concrete changes of supplied bundle coordinates, with no claim of
covariance of a differentiated field equation or abstract Spin classification.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Operator Manifold
open Function Set Topology
namespace FoliationQM.CocycleGaugeTransform
open SourcePolarDatum PolarSignQuotient DiracMatrices PolarTransitionCocycle

variable {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace B] [ChartedSpace H B] {ι : Type*} {n : WithTop ℕ∞}
  (D : Data I B ι n)

/-- Independently supplied actual determinant-one matrix changes, smooth only on their respective actual chart domains. -/
structure FrameChange where
  /-- The actual determinant-one matrix change for each chart. -/
  value : ι → B → SpecialLinearMatrix
  /-- Smoothness is required on precisely the corresponding open chart domain. -/
  smooth_value : ∀ i, ContMDiffOn I 𝓘(ℝ, SpecialLinearCharts.Model) n
    (value i) (D.domain i)

variable (h : FrameChange D)

/-- The actual inverse matrix change is smooth on the same actual chart domain. -/
theorem contMDiffOn_value_inv (i : ι) :
    ContMDiffOn I 𝓘(ℝ, SpecialLinearCharts.Model) n
      (fun x => (h.value i x)⁻¹) (D.domain i) :=
  (SpecialLinearGroupManifold.contMDiff_inv n).comp_contMDiffOn (h.smooth_value i)

/-- Actual frame changes construct a genuine cocycle with transitions h_j G_ij h_i⁻¹ and the identical supplied cover. -/
def transformed : Data I B ι n where
  domain := D.domain
  covers := D.covers
  transition i j x := (h.value j x * D.transition i j x) * (h.value i x)⁻¹
  smooth_transition i j := by
    have hj := (h.smooth_value j).mono (show
      (D.domain i : Set B) ∩ D.domain j ⊆ D.domain j from inter_subset_right)
    have hi := (contMDiffOn_value_inv D h i).mono (show
      (D.domain i : Set B) ∩ D.domain j ⊆ D.domain i from inter_subset_left)
    exact (SpecialLinearGroupManifold.contMDiff_mul n).comp_contMDiffOn
      (((SpecialLinearGroupManifold.contMDiff_mul n).comp_contMDiffOn
        (hj.prodMk (D.smooth_transition i j))).prodMk hi)
  identity i x hx := by simp [D.identity i x hx]
  comp i j k x hi hj hk := by
    calc
      (h.value k x * D.transition j k x * (h.value j x)⁻¹) *
          (h.value j x * D.transition i j x * (h.value i x)⁻¹) =
        h.value k x * (D.transition j k x * D.transition i j x) * (h.value i x)⁻¹ := by
          simp [mul_assoc]
      _ = h.value k x * D.transition i k x * (h.value i x)⁻¹ := by
        rw [D.comp i j k x hi hj hk]

/-- The transformed cocycle retains exactly the original open chart domains. -/
theorem transformed_domain : (transformed D h).domain = D.domain := rfl

/-- The actual transformed transition has the precise chart-i-to-chart-j matrix order h_j G_ij h_i⁻¹. -/
theorem transformed_transition (i j : ι) (x : B) :
    (transformed D h).transition i j x =
      (h.value j x * D.transition i j x) * (h.value i x)⁻¹ := rfl

/-- The transformed cocycle retains the exact same selected covering index at every base point. -/
theorem indexAt_transformed (x : B) : indexAt (transformed D h) x = indexAt D x := rfl

/-- Actual polar action by a local frame change intertwines the original and transformed transitions at every base point. -/
theorem polar_intertwining (i j : ι) (x : B) (p : DensityFrameManifold.Product) :
    polarChange (transformed D h) i j x
      (DensityFrameAction.productAction (h.value i x) p) =
    DensityFrameAction.productAction (h.value j x) (polarChange D i j x p) := by
  change DensityFrameAction.productAction
    ((h.value j x * D.transition i j x) * (h.value i x)⁻¹)
    (DensityFrameAction.productAction (h.value i x) p) =
    DensityFrameAction.productAction (h.value j x)
      (DensityFrameAction.productAction (D.transition i j x) p)
  rw [← DensityFrameAction.productAction_mul, ← DensityFrameAction.productAction_mul]
  simp [mul_assoc]

/-- The actual represented-spinor action intertwines the original and transformed transitions in the same orientation. -/
theorem spinor_intertwining (i j : ι) (x : B) (q : RegularSpinor) :
    spinorChange (transformed D h) i j x
      (RegularSpinorAction.act (h.value i x) q) =
    RegularSpinorAction.act (h.value j x) (spinorChange D i j x q) := by
  change RegularSpinorAction.act
    ((h.value j x * D.transition i j x) * (h.value i x)⁻¹)
    (RegularSpinorAction.act (h.value i x) q) =
    RegularSpinorAction.act (h.value j x)
      (RegularSpinorAction.act (D.transition i j x) q)
  rw [← RegularSpinorAction.act_mul, ← RegularSpinorAction.act_mul]
  simp [mul_assoc]

/-- Actual inverse local frame changes intertwine transformed polar transitions back to the original ones. -/
theorem polar_intertwining_inv (i j : ι) (x : B) (p : DensityFrameManifold.Product) :
    polarChange D i j x
      (DensityFrameAction.productAction ((h.value i x)⁻¹) p) =
    DensityFrameAction.productAction ((h.value j x)⁻¹)
      (polarChange (transformed D h) i j x p) := by
  change DensityFrameAction.productAction (D.transition i j x)
    (DensityFrameAction.productAction ((h.value i x)⁻¹) p) =
    DensityFrameAction.productAction ((h.value j x)⁻¹)
      (DensityFrameAction.productAction
        ((h.value j x * D.transition i j x) * (h.value i x)⁻¹) p)
  rw [← DensityFrameAction.productAction_mul, ← DensityFrameAction.productAction_mul]
  simp [mul_assoc]

/-- Actual represented inverse frame changes intertwine transformed spinor transitions back to the original ones. -/
theorem spinor_intertwining_inv (i j : ι) (x : B) (q : RegularSpinor) :
    spinorChange D i j x
      (RegularSpinorAction.act ((h.value i x)⁻¹) q) =
    RegularSpinorAction.act ((h.value j x)⁻¹)
      (spinorChange (transformed D h) i j x q) := by
  change RegularSpinorAction.act (D.transition i j x)
    (RegularSpinorAction.act ((h.value i x)⁻¹) q) =
    RegularSpinorAction.act ((h.value j x)⁻¹)
      (RegularSpinorAction.act
        ((h.value j x * D.transition i j x) * (h.value i x)⁻¹) q)
  rw [← RegularSpinorAction.act_mul, ← RegularSpinorAction.act_mul]
  simp [mul_assoc]

/-- The actual local polar frame-change action is jointly smooth on its actual chart domain times the entire polar fiber. -/
theorem contMDiffOn_polarAction (i : ι) :
    ContMDiffOn (I.prod DensityFrameManifold.model) DensityFrameManifold.model n
      (fun p : B × DensityFrameManifold.Product =>
        DensityFrameAction.productAction (h.value i p.1) p.2)
      ((D.domain i : Set B) ×ˢ univ) := by
  have hg : ContMDiffOn (I.prod DensityFrameManifold.model) 𝓘(ℝ, SpecialLinearCharts.Model) n
      (fun p : B × DensityFrameManifold.Product => h.value i p.1)
      ((D.domain i : Set B) ×ˢ univ) := (h.smooth_value i).comp
    contMDiff_fst.contMDiffOn
    (show MapsTo Prod.fst ((D.domain i : Set B) ×ˢ univ) (D.domain i) from fun _ hx => hx.1)
  exact (DensityFrameAction.contMDiff_productAction n).comp_contMDiffOn
    (hg.prodMk contMDiff_snd.contMDiffOn)

/-- The actual inverse polar frame-change action is jointly smooth on the same chart domain times the polar fiber. -/
theorem contMDiffOn_polarAction_inv (i : ι) :
    ContMDiffOn (I.prod DensityFrameManifold.model) DensityFrameManifold.model n
      (fun p : B × DensityFrameManifold.Product =>
        DensityFrameAction.productAction ((h.value i p.1)⁻¹) p.2)
      ((D.domain i : Set B) ×ˢ univ) := by
  have hg : ContMDiffOn (I.prod DensityFrameManifold.model) 𝓘(ℝ, SpecialLinearCharts.Model) n
      (fun p : B × DensityFrameManifold.Product => (h.value i p.1)⁻¹)
      ((D.domain i : Set B) ×ˢ univ) := (contMDiffOn_value_inv D h i).comp
    contMDiff_fst.contMDiffOn
    (show MapsTo Prod.fst ((D.domain i : Set B) ×ˢ univ) (D.domain i) from fun _ hx => hx.1)
  exact (DensityFrameAction.contMDiff_productAction n).comp_contMDiffOn
    (hg.prodMk contMDiff_snd.contMDiffOn)

/-- The actual represented-spinor frame-change action is jointly smooth on its actual chart domain times the regular-spinor fiber. -/
theorem contMDiffOn_spinorAction (i : ι) :
    ContMDiffOn (I.prod 𝓘(ℝ, Spinor)) 𝓘(ℝ, Spinor) n
      (fun p : B × RegularSpinor => RegularSpinorAction.act (h.value i p.1) p.2)
      ((D.domain i : Set B) ×ˢ univ) := by
  have hg : ContMDiffOn (I.prod 𝓘(ℝ, Spinor)) 𝓘(ℝ, SpecialLinearCharts.Model) n
      (fun p : B × RegularSpinor => h.value i p.1)
      ((D.domain i : Set B) ×ˢ univ) := (h.smooth_value i).comp
    contMDiff_fst.contMDiffOn
    (show MapsTo Prod.fst ((D.domain i : Set B) ×ˢ univ) (D.domain i) from fun _ hx => hx.1)
  have hc := (RegularSpinorAction.contMDiff_act n).comp_contMDiffOn
    (hg.prodMk contMDiff_snd.contMDiffOn)
  simpa only [Function.comp_def] using hc

/-- The actual represented inverse action is jointly smooth on the same chart domain times the regular-spinor fiber. -/
theorem contMDiffOn_spinorAction_inv (i : ι) :
    ContMDiffOn (I.prod 𝓘(ℝ, Spinor)) 𝓘(ℝ, Spinor) n
      (fun p : B × RegularSpinor => RegularSpinorAction.act ((h.value i p.1)⁻¹) p.2)
      ((D.domain i : Set B) ×ˢ univ) := by
  have hg : ContMDiffOn (I.prod 𝓘(ℝ, Spinor)) 𝓘(ℝ, SpecialLinearCharts.Model) n
      (fun p : B × RegularSpinor => (h.value i p.1)⁻¹)
      ((D.domain i : Set B) ×ˢ univ) := (contMDiffOn_value_inv D h i).comp
    contMDiff_fst.contMDiffOn
    (show MapsTo Prod.fst ((D.domain i : Set B) ×ˢ univ) (D.domain i) from fun _ hx => hx.1)
  have hc := (RegularSpinorAction.contMDiff_act n).comp_contMDiffOn
    (hg.prodMk contMDiff_snd.contMDiffOn)
  simpa only [Function.comp_def] using hc

/-- The constant identity matrices define an actual local frame change on every supplied chart. -/
def identityChange : FrameChange D where
  value _ _ := 1
  smooth_value _ := contMDiffOn_const

/-- Actual inverse matrices define a local frame change for the transformed cocycle, on the unchanged chart domains. -/
def inverseChange : FrameChange (transformed D h) where
  value i x := (h.value i x)⁻¹
  smooth_value i := contMDiffOn_value_inv D h i

/-- Successive local frame changes compose by the actual ordered product k_i h_i, with smoothness only on the original chart domains. -/
def composeChange (k : FrameChange (transformed D h)) : FrameChange D where
  value i x := k.value i x * h.value i x
  smooth_value i := (SpecialLinearGroupManifold.contMDiff_mul n).comp_contMDiffOn
    ((k.smooth_value i).prodMk (h.smooth_value i))

private theorem data_ext {D₁ D₂ : Data I B ι n}
    (hd : D₁.domain = D₂.domain) (ht : D₁.transition = D₂.transition) : D₁ = D₂ := by
  cases D₁
  cases D₂
  cases hd
  cases ht
  rfl

/-- Changing all local frames by the identity leaves the actual supplied cocycle unchanged. -/
theorem transformed_identity : transformed D (identityChange D) = D := by
  apply data_ext (D₁ := transformed D (identityChange D)) (D₂ := D) rfl
  funext i j x
  change (1 * D.transition i j x) * 1⁻¹ = D.transition i j x
  simp

/-- Applying the actual inverse local frame change restores the original cocycle as an equality of the full supplied data. -/
theorem transformed_inverse : transformed (transformed D h) (inverseChange D h) = D := by
  apply data_ext (D₁ := transformed (transformed D h) (inverseChange D h)) (D₂ := D) rfl
  funext i j x
  change ((h.value j x)⁻¹ *
    ((h.value j x * D.transition i j x) * (h.value i x)⁻¹)) * ((h.value i x)⁻¹)⁻¹ =
      D.transition i j x
  simp [mul_assoc]

/-- Successive frame changes give exactly the cocycle constructed from their ordered composite, with no dependent recasting of the cover. -/
theorem transformed_compose (k : FrameChange (transformed D h)) :
    transformed (transformed D h) k = transformed D (composeChange D h k) := by
  apply data_ext (D₁ := transformed (transformed D h) k)
    (D₂ := transformed D (composeChange D h k)) rfl
  funext i j x
  change (k.value j x * ((h.value j x * D.transition i j x) * (h.value i x)⁻¹)) *
    (k.value i x)⁻¹ =
      ((k.value j x * h.value j x) * D.transition i j x) * (k.value i x * h.value i x)⁻¹
  simp [mul_assoc]

end FoliationQM.CocycleGaugeTransform
