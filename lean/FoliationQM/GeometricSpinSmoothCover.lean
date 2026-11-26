module
public import FoliationQM.GeometricSpinCovering
public import FoliationQM.GeometricPrincipalSmoothAtlas
public import FoliationQM.CliffordSpinLorentzSmooth
public import FoliationQM.LorentzGroupManifold
public import FoliationQM.SmoothLocalDescent
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Smooth covering theorem for independent geometric Spin lifts

Source scope: the geometric Spin-frame bridge underlying v13
`prop:takabayasi`. The original Spin and Lorentz principal total spaces
retain independently supplied smooth atlases. A supplied actual smooth
equivariant geometric map is proved locally diffeomorphic, rather than
having this conclusion or an inverse derivative assumed as bundle data.

Its actual coefficient in a pair of original principal charts is smooth
on their genuine common base domain. There, varying left multiplication
is a real partial diffeomorphism with the explicit inverse group formula.
Composing original principal charts, the actual physical Spin-cover local
diffeomorphism, and this partial diffeomorphism gives a genuine local
inverse for the original map. The independently proved covering and exact
two-sign fibers complete the smooth two-sheeted covering statement.
No total topology or atlas is transported, and no geometric Spin lift of
an arbitrary Lorentz bundle or universal-cover conclusion is asserted.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Bundle Topology
open scoped Manifold Topology
namespace FoliationQM.GeometricSpinLift.Map
open CliffordSpinMap CliffordSpinLorentz CliffordSpinLorentzSmooth LorentzMatrixGroup

variable {EB EQ EP HB HQ HP B Q P : Type*}
  [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [NormedAddCommGroup EQ] [NormedSpace ℝ EQ]
  [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  [TopologicalSpace HB] [TopologicalSpace HQ] [TopologicalSpace HP]
  [TopologicalSpace B] [ChartedSpace HB B]
  [TopologicalSpace Q] [ChartedSpace HQ Q]
  [TopologicalSpace P] [ChartedSpace HP P]
  {I : ModelWithCorners ℝ EB HB} {KQ : ModelWithCorners ℝ EQ HQ}
  {KP : ModelWithCorners ℝ EP HP}
  {spinProj : Q → B} {frameProj : P → B} {ι κ : Type*}
  {S : GeometricPrincipalAtlas.Data (G := Spin) spinProj ι}
  {L : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) frameProj κ}
  {n : WithTop ℕ∞} (F : GeometricSpinLift.Map S L)
  (SF : GeometricPrincipalSmoothAtlas.Data I spinModel KQ S n)
  (LF : GeometricPrincipalSmoothAtlas.Data I lorentzModel KP L n)
  (hF : ContMDiff KQ KP n F)

include SF LF hF

/-- The actual varying Lorentz coefficient of a smooth geometric Spin map is smooth precisely on the true common domain of the independent source and target principal charts. -/
theorem contMDiffOn_localCoefficient (i : ι) (j : κ) :
    ContMDiffOn I lorentzModel n (F.localCoefficient i j)
      ((S.triv i).baseSet ∩ (L.triv j).baseSet) := by
  have hs : ContMDiffOn I KP n (fun x => F (S.localSection i x))
      ((S.triv i).baseSet ∩ (L.triv j).baseSet) :=
    hF.comp_contMDiffOn ((SF.contMDiffOn_localSection i).mono inter_subset_left)
  have ht := (LF.smooth_triv j).comp hs (by
    intro x hx
    apply (L.triv j).mem_source.mpr
    rw [F.proj, S.proj_localSection i x hx.1]
    exact hx.2)
  intro x hx
  exact (ht x hx).snd

/-- Varying multiplication by the actual local coefficient is a genuine partial diffeomorphism on the common base-chart product, with inverse left multiplication by the inverse coefficient. -/
def localCoefficientDiffeomorph (i : ι) (j : κ) :
    PartialDiffeomorph (I.prod lorentzModel) (I.prod lorentzModel)
      (B × ProperFutureLorentz) (B × ProperFutureLorentz) n where
  toFun z := (z.1, F.localCoefficient i j z.1 * z.2)
  invFun z := (z.1, (F.localCoefficient i j z.1)⁻¹ * z.2)
  source := ((S.triv i).baseSet ∩ (L.triv j).baseSet) ×ˢ univ
  target := ((S.triv i).baseSet ∩ (L.triv j).baseSet) ×ˢ univ
  map_source' _ hz := hz
  map_target' _ hz := hz
  left_inv' z _ := by simp
  right_inv' z _ := by simp
  open_source := ((S.triv i).open_baseSet.inter (L.triv j).open_baseSet).prod isOpen_univ
  open_target := ((S.triv i).open_baseSet.inter (L.triv j).open_baseSet).prod isOpen_univ
  contMDiffOn_toFun := by
    have ha : ContMDiffOn (I.prod lorentzModel) lorentzModel n
        (fun z : B × ProperFutureLorentz => F.localCoefficient i j z.1)
        (((S.triv i).baseSet ∩ (L.triv j).baseSet) ×ˢ univ) :=
      (F.contMDiffOn_localCoefficient SF LF hF i j).comp contMDiff_fst.contMDiffOn
        (fun _ hz => hz.1)
    exact contMDiffOn_fst.prodMk
      ((LorentzGroupManifold.contMDiff_mul n).comp_contMDiffOn
        (ha.prodMk contMDiff_snd.contMDiffOn))
  contMDiffOn_invFun := by
    have ha : ContMDiffOn (I.prod lorentzModel) lorentzModel n
        (fun z : B × ProperFutureLorentz => F.localCoefficient i j z.1)
        (((S.triv i).baseSet ∩ (L.triv j).baseSet) ×ˢ univ) :=
      (F.contMDiffOn_localCoefficient SF LF hF i j).comp contMDiff_fst.contMDiffOn
        (fun _ hz => hz.1)
    exact contMDiffOn_fst.prodMk
      ((LorentzGroupManifold.contMDiff_mul n).comp_contMDiffOn
        (((LorentzGroupManifold.contMDiff_inv n).comp_contMDiffOn ha).prodMk
          contMDiff_snd.contMDiffOn))

/-- The local coefficient partial diffeomorphism is defined on exactly the genuine common base-chart product. -/
theorem localCoefficientDiffeomorph_source (i : ι) (j : κ) :
    (F.localCoefficientDiffeomorph SF LF hF i j).source =
      ((S.triv i).baseSet ∩ (L.triv j).baseSet) ×ˢ (univ : Set ProperFutureLorentz) := rfl

/-- The actual coefficient partial diffeomorphism has its literal varying left-multiplication formula. -/
theorem localCoefficientDiffeomorph_apply (i : ι) (j : κ) (z : B × ProperFutureLorentz) :
    F.localCoefficientDiffeomorph SF LF hF i j z =
      (z.1, F.localCoefficient i j z.1 * z.2) := rfl

/-- Its actual inverse is literal multiplication by the inverse varying Lorentz coefficient. -/
theorem localCoefficientDiffeomorph_symm_apply (i : ι) (j : κ) (z : B × ProperFutureLorentz) :
    (F.localCoefficientDiffeomorph SF LF hF i j).symm z =
      (z.1, (F.localCoefficient i j z.1)⁻¹ * z.2) := rfl

/-- Every actual smooth equivariant geometric Spin lift is a local diffeomorphism for its independently supplied original total-space atlases, by true principal-chart conjugation to the physical Spin covering. -/
theorem isLocalDiffeomorph : IsLocalDiffeomorph KQ KP n F := by
  intro q
  obtain ⟨i, hi⟩ := S.covers (spinProj q)
  obtain ⟨j, hj⟩ := L.covers (spinProj q)
  have hrho := SmoothLocalDescent.isLocalDiffeomorph_id_prodMap (P := I) (X := B)
    (lorentzHom_isLocalDiffeomorph n)
  obtain ⟨e, he, heq⟩ := hrho (S.triv i q)
  let es := SF.localTrivDiffeomorph i
  let ea := F.localCoefficientDiffeomorph SF LF hF i j
  let et := LF.localTrivDiffeomorph j
  let d := ((es.trans e).trans ea).trans et.symm
  have hsource : q ∈ es.source := (S.triv i).mem_source.mpr hi
  have hfirst : (S.triv i q).1 = spinProj q := (S.triv i).coe_fst' hi
  have heqpoint : e (S.triv i q) = (spinProj q, lorentzHom (S.triv i q).2) := by
    rw [← heq he]
    exact Prod.ext hfirst rfl
  have hea : e (es q) ∈ ea.source := by
    change e (S.triv i q) ∈ ((S.triv i).baseSet ∩ (L.triv j).baseSet) ×ˢ univ
    rw [heqpoint]
    exact ⟨⟨hi, hj⟩, mem_univ _⟩
  have het : ea (e (es q)) ∈ et.symm.source := by
    change (F.localCoefficientDiffeomorph SF LF hF i j (e (S.triv i q))) ∈ (L.triv j).target
    rw [heqpoint]
    exact (L.triv j).mem_target.mpr hj
  refine ⟨d, ⟨⟨⟨hsource, he⟩, hea⟩, het⟩, ?_⟩
  intro p hp
  change ((p ∈ es.source ∧ es p ∈ e.source) ∧ e (es p) ∈ ea.source) ∧
    ea (e (es p)) ∈ et.symm.source at hp
  have hpi : spinProj p ∈ (S.triv i).baseSet := (S.triv i).mem_source.mp hp.1.1.1
  have hpρ : S.triv i p ∈ e.source := hp.1.1.2
  have heqp : e (S.triv i p) = (spinProj p, lorentzHom (S.triv i p).2) := by
    rw [← heq hpρ]
    exact Prod.ext ((S.triv i).coe_fst' hpi) rfl
  have hpj : spinProj p ∈ (L.triv j).baseSet := by
    have hcommon := hp.1.2
    change e (S.triv i p) ∈ ((S.triv i).baseSet ∩ (L.triv j).baseSet) ×ˢ univ at hcommon
    rw [heqp] at hcommon
    exact hcommon.1.2
  have hformula := F.local_formula i j (spinProj p) (S.triv i p).2 hpi hpj
  rw [(S.triv i).symm_apply_mk_proj ((S.triv i).mem_source.mpr hpi)] at hformula
  change F p = (L.triv j).toOpenPartialHomeomorph.symm
    (F.localCoefficientDiffeomorph SF LF hF i j (e (S.triv i p)))
  rw [heqp, localCoefficientDiffeomorph_apply, ← hformula]
  exact ((L.triv j).left_inv ((L.triv j).mem_source.mpr (by rw [F.proj]; exact hpj))).symm

/-- A supplied smooth geometric Spin lift is simultaneously a genuine covering, a local diffeomorphism in the original atlases, and exactly two-to-one over every original Lorentz frame. -/
theorem smooth_two_sheeted :
    IsCoveringMap F ∧ IsLocalDiffeomorph KQ KP n F ∧
      ∀ p : P, Nat.card (F ⁻¹' {p}) = 2 :=
  ⟨F.isCoveringMap, F.isLocalDiffeomorph SF LF hF, F.fiber_card⟩

end FoliationQM.GeometricSpinLift.Map
