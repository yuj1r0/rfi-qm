module
public import FoliationQM.CliffordSpinPolarAction
public import FoliationQM.PolarTransitionCocycle

/-!
# Independently supplied smooth Clifford Spin transition cocycles

Source scope: the supplied spin-frame cocycle interpretation of v13
`prop:takabayasi`. The data consist of an actual open cover and actual
generated Clifford Spin transitions, smooth precisely on pair overlaps,
with identity and correctly ordered composition on triple overlaps.
These are supplied Spin transitions; no existence of a lift of arbitrary
Lorentz transition functions or of a spacetime Spin structure is assumed
as a consequence.

The genuine smooth Spin group identification gives a full-data
bijection with the previously defined matrix cocycles on exactly the
same cover. The actual polar and spinor changes use separately proved
Clifford group actions; their overlap smoothness and equivariance are
derived. The represented change is literally the universal Clifford
Dirac map acting on the spinor. A genuine identity cocycle is supplied
for every given open cover, verifying that these premises are inhabited.
No field equation or integrated variational dynamics follows here.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Operator Manifold
open Function Set Topology
namespace FoliationQM.CliffordSpinPolarCocycle
open CliffordSpinMap CliffordSpinEquivalence CliffordSpinPolarReconstruction
open PolarSignQuotient DiracMatrices

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (B : Type*) [TopologicalSpace B] [ChartedSpace H B]

/-- Independently supplied open domains and genuine smooth Clifford Spin transitions, oriented from chart i to chart j. -/
structure Data (ι : Type*) (n : WithTop ℕ∞) where
  /-- The supplied actual open chart domains. -/
  domain : ι → TopologicalSpace.Opens B
  /-- The supplied domains cover the entire base. -/
  covers : ∀ x : B, ∃ i, x ∈ domain i
  /-- The actual Clifford Spin element taking chart i coordinates to chart j coordinates. -/
  transition : ι → ι → B → Spin
  /-- Smoothness is imposed only on the genuine pairwise overlap. -/
  smooth_transition : ∀ i j, ContMDiffOn I 𝓘(ℝ, CliffordSpinManifold.Model) n
    (transition i j) ((domain i : Set B) ∩ (domain j : Set B))
  /-- A self-transition equals the actual group identity on its chart. -/
  identity : ∀ i x, x ∈ domain i → transition i i x = 1
  /-- Triple-overlap composition has the actual chart i to j to k order. -/
  comp : ∀ i j k x, x ∈ domain i → x ∈ domain j → x ∈ domain k →
    transition j k x * transition i j x = transition i k x

variable {I B} {ι : Type*} {n : WithTop ℕ∞}

/-- Applying the proved smooth Pauli group homomorphism to the actual Spin transitions gives a matrix cocycle on the identical open cover. -/
def toMatrixData (D : Data I B ι n) : PolarTransitionCocycle.Data I B ι n where
  domain := D.domain
  covers := D.covers
  transition i j x := CliffordSpinMap.toMatrix (D.transition i j x)
  smooth_transition i j :=
    (CliffordSpinManifold.contMDiff_toMatrix n).comp_contMDiffOn (D.smooth_transition i j)
  identity i x hx := by rw [D.identity i x hx, map_one]
  comp i j k x hi hj hk := by rw [← map_mul, D.comp i j k x hi hj hk]

/-- Applying the actual smooth inverse Clifford identification to every matrix transition gives genuine Spin cocycle data on exactly the same open cover. -/
def ofMatrixData (D : PolarTransitionCocycle.Data I B ι n) : Data I B ι n where
  domain := D.domain
  covers := D.covers
  transition i j x := spinEquiv.symm (D.transition i j x)
  smooth_transition i j :=
    (CliffordSpinManifold.contMDiff_spinEquiv_symm n).comp_contMDiffOn (D.smooth_transition i j)
  identity i x hx := by rw [D.identity i x hx, map_one]
  comp i j k x hi hj hk := by rw [← map_mul, D.comp i j k x hi hj hk]

private theorem spin_data_ext {D₁ D₂ : Data I B ι n}
    (hd : D₁.domain = D₂.domain) (ht : D₁.transition = D₂.transition) : D₁ = D₂ := by
  cases D₁
  cases D₂
  cases hd
  cases ht
  rfl

private theorem matrix_data_ext {D₁ D₂ : PolarTransitionCocycle.Data I B ι n}
    (hd : D₁.domain = D₂.domain) (ht : D₁.transition = D₂.transition) : D₁ = D₂ := by
  cases D₁
  cases D₂
  cases hd
  cases ht
  rfl

/-- Matrix conversion followed by genuine inverse Spin conversion returns the full original data, including its exact supplied cover. -/
theorem ofMatrixData_toMatrixData (D : Data I B ι n) : ofMatrixData (toMatrixData D) = D := by
  apply spin_data_ext (D₁ := ofMatrixData (toMatrixData D)) (D₂ := D) rfl
  funext i j x
  exact spinEquiv.symm_apply_apply (D.transition i j x)

/-- Genuine inverse Spin conversion followed by matrix conversion returns the full original matrix cocycle data. -/
theorem toMatrixData_ofMatrixData (D : PolarTransitionCocycle.Data I B ι n) :
    toMatrixData (ofMatrixData D) = D := by
  apply matrix_data_ext (D₁ := toMatrixData (ofMatrixData D)) (D₂ := D) rfl
  funext i j x
  exact spinEquiv.apply_symm_apply (D.transition i j x)

/-- Genuine Spin and matrix cocycles correspond bijectively as full data on the same supplied cover, by the proved smooth group identification. -/
def dataEquiv : Data I B ι n ≃ PolarTransitionCocycle.Data I B ι n where
  toFun := toMatrixData
  invFun := ofMatrixData
  left_inv := ofMatrixData_toMatrixData
  right_inv := toMatrixData_ofMatrixData

/-- The converted transition is exactly the actual Pauli matrix of the supplied Clifford Spin element. -/
theorem toMatrixData_transition (D : Data I B ι n) (i j : ι) (x : B) :
    (toMatrixData D).transition i j x = CliffordSpinMap.toMatrix (D.transition i j x) := rfl

/-- The inverse-converted transition is exactly the actual Clifford Spin inverse identification of the supplied matrix. -/
theorem ofMatrixData_transition (D : PolarTransitionCocycle.Data I B ι n) (i j : ι) (x : B) :
    (ofMatrixData D).transition i j x = spinEquiv.symm (D.transition i j x) := rfl

/-- Every supplied open cover carries a literal identity Spin cocycle, proving the independent transition premises have genuine instances. -/
def identityData (U : ι → TopologicalSpace.Opens B) (hU : ∀ x : B, ∃ i, x ∈ U i) :
    Data I B ι n where
  domain := U
  covers := hU
  transition _ _ _ := 1
  smooth_transition _ _ := contMDiff_const.contMDiffOn
  identity _ _ _ := rfl
  comp _ _ _ _ _ _ _ := one_mul 1

/-- The explicit identity cocycle has literal identity Spin transitions on and off every chart overlap. -/
theorem identityData_transition (U : ι → TopologicalSpace.Opens B)
    (hU : ∀ x : B, ∃ i, x ∈ U i) (i j : ι) (x : B) :
    (identityData (I := I) (n := n) U hU).transition i j x = 1 := rfl

variable (D : Data I B ι n)

/-- On an actual overlap, the reverse Clifford Spin transition is the group inverse of the forward transition. -/
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

/-- The actual polar coordinate change preserves density and acts by the supplied genuine Clifford Spin element on its literal frame class. -/
def polarChange (i j : ι) (x : B) (p : Product) : Product :=
  CliffordSpinPolarAction.productAction (D.transition i j x) p

/-- The represented coordinate change is the independently defined direct universal Clifford Dirac action. -/
def spinorChange (i j : ι) (x : B) (q : RegularSpinor) : RegularSpinor :=
  CliffordSpinPolarAction.act (D.transition i j x) q

/-- The actual represented transition acts literally by the universal Clifford Dirac matrix on the original spinor. -/
theorem spinorChange_val (i j : ι) (x : B) (q : RegularSpinor) :
    (spinorChange D i j x q).val =
      (CliffordMinkowski.dirac (D.transition i j x).val).mulVec q.val := rfl

/-- The actual source change is the identity on its own chart domain. -/
theorem polarChange_self (i : ι) (x : B) (hx : x ∈ D.domain i) (p : Product) :
    polarChange D i i x p = p := by
  simp only [polarChange, D.identity i x hx, CliffordSpinPolarAction.productAction_one]

/-- The actual universal Dirac change is the identity on its own chart domain. -/
theorem spinorChange_self (i : ι) (x : B) (hx : x ∈ D.domain i) (q : RegularSpinor) :
    spinorChange D i i x q = q := by
  simp only [spinorChange, D.identity i x hx, CliffordSpinPolarAction.act_one]

/-- Actual Clifford polar transitions compose in the supplied chart-change order on every triple overlap. -/
theorem polarChange_comp (i j k : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) (hk : x ∈ D.domain k) (p : Product) :
    polarChange D j k x (polarChange D i j x p) = polarChange D i k x p := by
  simp only [polarChange, ← CliffordSpinPolarAction.productAction_mul, D.comp i j k x hi hj hk]

/-- Actual universal Dirac transitions obey the same chart-change composition order on triple overlaps. -/
theorem spinorChange_comp (i j k : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) (hk : x ∈ D.domain k) (q : RegularSpinor) :
    spinorChange D j k x (spinorChange D i j x q) = spinorChange D i k x q := by
  simp only [spinorChange, ← CliffordSpinPolarAction.act_mul, D.comp i j k x hi hj hk]

/-- Genuine Clifford polar realization intertwines the independently specified polar and universal Dirac coordinate changes. -/
theorem change_equivariant (i j : ι) (x : B) (p : Product) :
    CliffordSpinPolarQuotient.productRegularHomeomorph (polarChange D i j x p) =
      spinorChange D i j x (CliffordSpinPolarQuotient.productRegularHomeomorph p) :=
  CliffordSpinPolarAction.realization_equivariant (D.transition i j x) p

/-- The actual Clifford polar transition is smooth jointly in its base and quotient-fiber variables on exactly the supplied pair overlap. -/
theorem contMDiffOn_polarChange (i j : ι) :
    ContMDiffOn (I.prod model) model n
      (fun p : B × Product => polarChange D i j p.1 p.2)
      (((D.domain i : Set B) ∩ (D.domain j : Set B)) ×ˢ univ) := by
  have hg : ContMDiffOn (I.prod model) 𝓘(ℝ, CliffordSpinManifold.Model) n
      (fun p : B × Product => D.transition i j p.1)
      (((D.domain i : Set B) ∩ (D.domain j : Set B)) ×ˢ univ) :=
    (D.smooth_transition i j).comp contMDiff_fst.contMDiffOn (fun _ hx => hx.1)
  exact (CliffordSpinPolarAction.contMDiff_productAction n).comp_contMDiffOn
    (hg.prodMk contMDiff_snd.contMDiffOn)

/-- The actual universal Dirac transition is smooth jointly in base and regular-spinor variables on the supplied pair overlap. -/
theorem contMDiffOn_spinorChange (i j : ι) :
    ContMDiffOn (I.prod 𝓘(ℝ, Spinor)) 𝓘(ℝ, Spinor) n
      (fun p : B × RegularSpinor => spinorChange D i j p.1 p.2)
      (((D.domain i : Set B) ∩ (D.domain j : Set B)) ×ˢ univ) := by
  have hg : ContMDiffOn (I.prod 𝓘(ℝ, Spinor)) 𝓘(ℝ, CliffordSpinManifold.Model) n
      (fun p : B × RegularSpinor => D.transition i j p.1)
      (((D.domain i : Set B) ∩ (D.domain j : Set B)) ×ˢ univ) :=
    (D.smooth_transition i j).comp contMDiff_fst.contMDiffOn (fun _ hx => hx.1)
  exact (CliffordSpinPolarAction.contMDiff_act n).comp_contMDiffOn
    (hg.prodMk contMDiff_snd.contMDiffOn)

/-- Matrix polar coordinates intertwine the actual Clifford transition with the corresponding independently defined matrix cocycle transition. -/
theorem polarChange_matrix (i j : ι) (x : B) (p : Product) :
    productMatrixDiffeomorph n (polarChange D i j x p) =
      PolarTransitionCocycle.polarChange (toMatrixData D) i j x (productMatrixDiffeomorph n p) :=
  CliffordSpinPolarAction.productMatrixDiffeomorph_action n (D.transition i j x) p

/-- The direct universal Clifford Dirac transition agrees exactly with the represented transition of its actual matrix cocycle. -/
theorem spinorChange_eq_matrix (i j : ι) (x : B) (q : RegularSpinor) :
    spinorChange D i j x q = PolarTransitionCocycle.spinorChange (toMatrixData D) i j x q :=
  CliffordSpinPolarAction.act_eq_matrix (D.transition i j x) q

end FoliationQM.CliffordSpinPolarCocycle
