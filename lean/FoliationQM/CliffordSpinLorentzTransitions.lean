module
public import FoliationQM.CliffordSpinLorentzSmooth
public import FoliationQM.CliffordSpinCocycleFields

/-!
# Smooth Lorentz transitions of supplied genuine Spin cocycles

Source scope: the spin-frame interpretation of v13 `prop:takabayasi`.
Lorentz transition data are specified independently on an actual open
cover, with smoothness on pair overlaps and correctly ordered composition
on triple overlaps. A supplied genuine Clifford Spin cocycle projects to
these data through the original physical Lorentz homomorphism. The target
uses the independently constructed Lorentz Cayley atlas.

The actual chiral frame and regular-spinor Lorentz projections are
intrinsically smooth. Compatible actual polar and spinor families give
compatible Lorentz frame families, and realization commutes with this
projection. These are forward consequences of supplied Spin data. They
do not lift an arbitrary Lorentz cocycle, identify the seven-dimensional
chiral frame quotient with the six-dimensional Lorentz group, assert a
spacetime Spin structure, or derive variational dynamics.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Operator Manifold
open Set Topology
namespace FoliationQM.CliffordSpinLorentzTransitions
open LorentzMatrixGroup CliffordSpinLorentz CliffordSpinPolarQuotient
open CliffordSpinPolarReconstruction PolarSignQuotient DiracMatrices

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (B : Type*) [TopologicalSpace B] [ChartedSpace H B]

/-- Independent smooth proper future Lorentz transition data, with the original chart i to chart j orientation and explicit overlap domains. -/
structure Data (ι : Type*) (n : WithTop ℕ∞) where
  /-- The supplied actual open chart domains. -/
  domain : ι → TopologicalSpace.Opens B
  /-- The domains cover the supplied base. -/
  covers : ∀ x : B, ∃ i, x ∈ domain i
  /-- The actual Lorentz element taking chart i frame coordinates to chart j. -/
  transition : ι → ι → B → ProperFutureLorentz
  /-- Intrinsic smoothness is required precisely on each pair overlap. -/
  smooth_transition : ∀ i j, ContMDiffOn I LorentzManifold.model n
    (transition i j) ((domain i : Set B) ∩ (domain j : Set B))
  /-- Self-transitions are the identity on their chart. -/
  identity : ∀ i x, x ∈ domain i → transition i i x = 1
  /-- Composition follows the actual chart i to j to k order. -/
  comp : ∀ i j k x, x ∈ domain i → x ∈ domain j → x ∈ domain k →
    transition j k x * transition i j x = transition i k x

variable {I B} {ι : Type*} {n : WithTop ℕ∞}

/-- The original Clifford Lorentz homomorphism sends a supplied smooth Spin cocycle to independent Lorentz transition data on exactly the same open cover. -/
def ofSpinData (D : CliffordSpinPolarCocycle.Data I B ι n) : Data I B ι n where
  domain := D.domain
  covers := D.covers
  transition i j x := lorentzHom (D.transition i j x)
  smooth_transition i j :=
    (CliffordSpinLorentzSmooth.contMDiff_lorentzHom n).comp_contMDiffOn
      (D.smooth_transition i j)
  identity i x hx := by rw [D.identity i x hx, map_one]
  comp i j k x hi hj hk := by rw [← map_mul, D.comp i j k x hi hj hk]

/-- Projection retains the exact original open chart domains, not merely an equivalent covering. -/
theorem ofSpinData_domain (D : CliffordSpinPolarCocycle.Data I B ι n) :
    (ofSpinData D).domain = D.domain := rfl

/-- Every projected transition is literally the original genuine Clifford Lorentz image. -/
theorem ofSpinData_transition (D : CliffordSpinPolarCocycle.Data I B ι n)
    (i j : ι) (x : B) :
    (ofSpinData D).transition i j x = lorentzHom (D.transition i j x) := rfl

/-- The real entries of each projected transition are exactly the physical matrix of the supplied faithful Spin representative. -/
theorem ofSpinData_transition_matrix (D : CliffordSpinPolarCocycle.Data I B ι n)
    (i j : ι) (x : B) :
    matrix ((ofSpinData D).transition i j x).val =
      SpinLorentzAction.lorentzMatrix (CliffordSpinMap.toMatrix (D.transition i j x)).val :=
  lorentzHom_matrix _

/-- The reverse transition of any independent Lorentz cocycle is the actual group inverse on the pair overlap. -/
theorem transition_reverse (D : Data I B ι n) (i j : ι) (x : B)
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

/-- The literal real transition matrices compose in the same ordered triple-overlap law. -/
theorem transition_matrix_comp (D : Data I B ι n) (i j k : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) (hk : x ∈ D.domain k) :
    matrix (D.transition j k x).val * matrix (D.transition i j x).val =
      matrix (D.transition i k x).val :=
  congrArg (fun L : ProperFutureLorentz => matrix L.val) (D.comp i j k x hi hj hk)

/-- A Lorentz transition changes a Lorentz frame by actual ordered left multiplication. -/
def change (D : Data I B ι n) (i j : ι) (x : B) (L : ProperFutureLorentz) :
    ProperFutureLorentz := D.transition i j x * L

/-- Actual Lorentz frame changes compose in the supplied chart-change order on every triple overlap. -/
theorem change_comp (D : Data I B ι n) (i j k : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) (hk : x ∈ D.domain k)
    (L : ProperFutureLorentz) :
    change D j k x (change D i j x L) = change D i k x L := by
  simp only [change, ← mul_assoc, D.comp i j k x hi hj hk]

/-- Lorentz frame change is intrinsically smooth jointly in base and frame variables on the exact supplied pair overlap. -/
theorem contMDiffOn_change (D : Data I B ι n) (i j : ι) :
    ContMDiffOn (I.prod LorentzManifold.model) LorentzManifold.model n
      (fun p : B × ProperFutureLorentz => change D i j p.1 p.2)
      (((D.domain i : Set B) ∩ (D.domain j : Set B)) ×ˢ univ) := by
  have ht : ContMDiffOn (I.prod LorentzManifold.model) LorentzManifold.model n
      (fun p : B × ProperFutureLorentz => D.transition i j p.1)
      (((D.domain i : Set B) ∩ (D.domain j : Set B)) ×ˢ univ) :=
    (D.smooth_transition i j).comp contMDiff_fst.contMDiffOn (fun _ hx => hx.1)
  exact (LorentzGroupManifold.contMDiff_mul n).comp_contMDiffOn
    (ht.prodMk contMDiff_snd.contMDiffOn)

/-- Forgetting the chiral angle of an actual Clifford frame class is intrinsically smooth into the independent six-dimensional Lorentz atlas. -/
theorem contMDiff_frameLorentz (n : WithTop ℕ∞) :
    ContMDiff CliffordSpinPolarManifold.model LorentzManifold.model n
      CliffordSpinPolarAction.frameLorentz :=
  LorentzManifold.contMDiff_iff_value.mpr
    (CliffordSpinPolarAction.contMDiff_frameLorentz_matrix n)

/-- The physical Lorentz frame reconstructed from a regular spinor is intrinsically smooth in the independent Lorentz atlas. -/
theorem contMDiff_regularLorentz (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℝ, Spinor) LorentzManifold.model n
      SpinLorentzPolarCompatibility.regularLorentz :=
  LorentzManifold.contMDiff_iff_value.mpr
    (SpinLorentzPolarCompatibility.contMDiff_regularLorentz_matrix n)

/-- The physical Lorentz projection of actual Clifford polar data forgets density and chiral angle while retaining the genuine frame class. -/
def polarLorentz (p : Product) : ProperFutureLorentz :=
  CliffordSpinPolarAction.frameLorentz p.2

/-- The actual polar Lorentz projection is intrinsically smooth in the independent target atlas. -/
theorem contMDiff_polarLorentz (n : WithTop ℕ∞) :
    ContMDiff CliffordSpinPolarReconstruction.model LorentzManifold.model n polarLorentz :=
  (contMDiff_frameLorentz n).comp contMDiff_snd

/-- Actual polar realization and the regular-spinor reconstruction produce exactly the same physical Lorentz frame. -/
theorem regularLorentz_realization (p : Product) :
    SpinLorentzPolarCompatibility.regularLorentz (productRegularHomeomorph p) = polarLorentz p :=
  CliffordSpinPolarAction.regularLorentz_product p

/-- The genuine Clifford polar transition projects to its actual Lorentz transition acting on the physical frame. -/
theorem polarChange_projection (D : CliffordSpinPolarCocycle.Data I B ι n)
    (i j : ι) (x : B) (p : Product) :
    polarLorentz (CliffordSpinPolarCocycle.polarChange D i j x p) =
      change (ofSpinData D) i j x (polarLorentz p) :=
  CliffordSpinPolarAction.frameLorentz_action (D.transition i j x) p.2

/-- Direct universal Clifford Dirac transition projects to the same actual ordered Lorentz frame change. -/
theorem spinorChange_projection (D : CliffordSpinPolarCocycle.Data I B ι n)
    (i j : ι) (x : B) (q : RegularSpinor) :
    SpinLorentzPolarCompatibility.regularLorentz (CliffordSpinPolarCocycle.spinorChange D i j x q) =
      change (ofSpinData D) i j x (SpinLorentzPolarCompatibility.regularLorentz q) :=
  CliffordSpinPolarAction.regularLorentz_action (D.transition i j x) q

/-- Bundled smooth physical Lorentz fields on the original open chart subtypes of independently specified transition data. -/
abbrev RawFamily (D : Data I B ι n) :=
  ∀ i : ι, C^n⟮I, ↥(D.domain i); LorentzManifold.model, ProperFutureLorentz⟯

/-- Independent physical frame compatibility uses actual ordered Lorentz multiplication on the exact overlap. -/
def Compatible (D : Data I B ι n) (f : RawFamily D) : Prop :=
  ∀ (i j : ι) (x : B) (hi : x ∈ D.domain i) (hj : x ∈ D.domain j),
    f j ⟨x, hj⟩ = change D i j x (f i ⟨x, hi⟩)

/-- Independently compatible bundled smooth Lorentz frame families on the supplied cover. -/
def SmoothFamily (D : Data I B ι n) := {f : RawFamily D // Compatible D f}

/-- A compatible genuine Clifford polar family projects to an independently compatible smooth physical Lorentz frame family. -/
def polarFamily (D : CliffordSpinPolarCocycle.Data I B ι n)
    (f : CliffordSpinCocycleFields.SmoothPolarFamily D) : SmoothFamily (ofSpinData D) :=
  ⟨fun i => ⟨polarLorentz ∘ f.val i, (contMDiff_polarLorentz n).comp (f.val i).contMDiff⟩, by
    intro i j x hi hj
    change polarLorentz (f.val j ⟨x, hj⟩) = change (ofSpinData D) i j x (polarLorentz (f.val i ⟨x, hi⟩))
    rw [f.property i j x hi hj]
    exact polarChange_projection D i j x _⟩

/-- A compatible actual universal-Dirac spinor family reconstructs an independently compatible smooth physical Lorentz frame family. -/
def spinorFamily (D : CliffordSpinPolarCocycle.Data I B ι n)
    (f : CliffordSpinCocycleFields.SmoothSpinorFamily D) : SmoothFamily (ofSpinData D) :=
  ⟨fun i => ⟨SpinLorentzPolarCompatibility.regularLorentz ∘ f.val i,
    (contMDiff_regularLorentz n).comp (f.val i).contMDiff⟩, by
    intro i j x hi hj
    change SpinLorentzPolarCompatibility.regularLorentz (f.val j ⟨x, hj⟩) =
      change (ofSpinData D) i j x (SpinLorentzPolarCompatibility.regularLorentz (f.val i ⟨x, hi⟩))
    rw [f.property i j x hi hj]
    exact spinorChange_projection D i j x _⟩

/-- The projected polar family retains exactly the physical Lorentz frame of each original local quotient value. -/
theorem polarFamily_apply (D : CliffordSpinPolarCocycle.Data I B ι n)
    (f : CliffordSpinCocycleFields.SmoothPolarFamily D) (i : ι) (x : D.domain i) :
    (polarFamily D f).val i x = polarLorentz (f.val i x) := rfl

/-- The projected spinor family uses precisely the original regular spinor's reconstructed physical Lorentz frame. -/
theorem spinorFamily_apply (D : CliffordSpinPolarCocycle.Data I B ι n)
    (f : CliffordSpinCocycleFields.SmoothSpinorFamily D) (i : ι) (x : D.domain i) :
    (spinorFamily D f).val i x = SpinLorentzPolarCompatibility.regularLorentz (f.val i x) := rfl

/-- Genuine local Clifford realization commutes exactly with projection to independently compatible smooth Lorentz frame families. -/
theorem spinorFamily_realization (D : CliffordSpinPolarCocycle.Data I B ι n)
    (f : CliffordSpinCocycleFields.SmoothPolarFamily D) :
    spinorFamily D (CliffordSpinCocycleFields.realizationEquiv D f) = polarFamily D f := by
  apply Subtype.ext
  funext i
  apply ContMDiffMap.ext
  intro x
  rw [spinorFamily_apply, polarFamily_apply, CliffordSpinCocycleFields.realizationEquiv_apply]
  exact regularLorentz_realization _

/-- Genuine quotient-valued inverse Clifford reconstruction recovers the same compatible physical Lorentz frame family. -/
theorem polarFamily_reconstruction (D : CliffordSpinPolarCocycle.Data I B ι n)
    (f : CliffordSpinCocycleFields.SmoothSpinorFamily D) :
    polarFamily D ((CliffordSpinCocycleFields.realizationEquiv D).symm f) = spinorFamily D f := by
  rw [← spinorFamily_realization, (CliffordSpinCocycleFields.realizationEquiv D).apply_symm_apply]

end FoliationQM.CliffordSpinLorentzTransitions
