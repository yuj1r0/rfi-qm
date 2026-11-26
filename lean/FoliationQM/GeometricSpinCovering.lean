module
public import FoliationQM.GeometricSpinLift
public import FoliationQM.ProductCovering
public import FoliationQM.CliffordSpinCovering

/-!
# Covering theorem for independent geometric Spin lifts

Source scope: the geometric Spin-frame component of v13 `prop:takabayasi`.
For any supplied continuous equivariant lift between independently topologized
principal Spin and Lorentz atlases, the actual map is a covering. On each
common base chart its literal formula is the product of the original Clifford
cover with the base, followed by continuous varying left multiplication.
Actual restricted trivializations conjugate this genuine product covering to
the original map. The existing exact sign fibers then give neighborhoods with
precisely two sheets. Neither existence of a geometric Spin lift nor simple
connectivity of either total bundle space is assumed or concluded.
-/

@[expose] public section
noncomputable section
open Set Topology Function
open scoped Topology
namespace FoliationQM.GeometricSpinLift.Map
open CliffordSpinMap CliffordSpinLorentz CliffordSpinSignKernel LorentzMatrixGroup

variable {B Q P : Type*} [TopologicalSpace B] [TopologicalSpace Q] [TopologicalSpace P]
  {spinProj : Q → B} {frameProj : P → B} {ι κ : Type*}
  {S : GeometricPrincipalAtlas.Data (G := Spin) spinProj ι}
  {L : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) frameProj κ}
  (F : GeometricSpinLift.Map S L)

/-- The actual target group coordinate of the image of a source unit section. -/
def localCoefficient (i : ι) (j : κ) (x : B) : ProperFutureLorentz :=
  (L.triv j (F (S.localSection i x))).2

/-- The varying coefficient is continuous on the actual common base domain of the two independently supplied charts. -/
theorem continuousOn_localCoefficient (i : ι) (j : κ) :
    ContinuousOn (F.localCoefficient i j) ((S.triv i).baseSet ∩ (L.triv j).baseSet) := by
  have hs : ContinuousOn (fun x => F (S.localSection i x))
      ((S.triv i).baseSet ∩ (L.triv j).baseSet) :=
    F.continuous_toFun.comp_continuousOn
      ((S.continuousOn_localSection i).mono inter_subset_left)
  have ht := (L.triv j).toOpenPartialHomeomorph.continuousOn.comp hs (by
    intro x hx
    apply (L.triv j).mem_source.mpr
    rw [F.proj, S.proj_localSection i x hx.1]
    exact hx.2)
  exact ht.snd

/-- The actual map in independent principal charts is the original Clifford cover followed by its varying target coefficient. -/
theorem local_formula (i : ι) (j : κ) (x : B) (s : Spin)
    (hi : x ∈ (S.triv i).baseSet) (hj : x ∈ (L.triv j).baseSet) :
    L.triv j (F ((S.triv i).toOpenPartialHomeomorph.symm (x, s))) =
      (x, F.localCoefficient i j x * lorentzHom s) := by
  have hsec : spinProj (S.localSection i x) ∈ (S.triv i).baseSet := by
    rw [S.proj_localSection i x hi]
    exact hi
  have he : S.right (S.localSection i x) s =
      (S.triv i).toOpenPartialHomeomorph.symm (x, s) := by
    rw [S.right_eq_symm i _ _ hsec, S.proj_localSection i x hi,
      S.localSection_coordinate i x hi, one_mul]
  have hjsec : frameProj (F (S.localSection i x)) ∈ (L.triv j).baseSet := by
    rw [F.proj, S.proj_localSection i x hi]
    exact hj
  rw [← he, F.equivariant]
  apply Prod.ext
  · rw [(L.triv j).coe_fst' (by rw [L.proj_right]; exact hjsec),
      L.proj_right, F.proj, S.proj_localSection i x hi]
  · exact L.right_local j _ _ hjsec

/-- On the inverse image of a common base chart, the original geometric lift is a covering by actual chart conjugation to a product covering. -/
theorem isCoveringMap_restrict_overlap (i : ι) (j : κ) :
    IsCoveringMap ((frameProj ⁻¹' ((S.triv i).baseSet ∩ (L.triv j).baseSet)).restrictPreimage F) := by
  let U : Set B := (S.triv i).baseSet ∩ (L.triv j).baseSet
  let V : Set P := frameProj ⁻¹' U
  have hpre : F ⁻¹' V = spinProj ⁻¹' U := by
    ext q
    change frameProj (F q) ∈ U ↔ spinProj q ∈ U
    rw [F.proj]
  let eS : (F ⁻¹' V) ≃ₜ U × Spin :=
    (Homeomorph.setCongr hpre).trans
      ((S.triv i).preimageHomeomorph (show U ⊆ (S.triv i).baseSet from inter_subset_left))
  let eL : V ≃ₜ U × ProperFutureLorentz :=
    (L.triv j).preimageHomeomorph (show U ⊆ (L.triv j).baseSet from inter_subset_right)
  let a : U → ProperFutureLorentz := fun x => F.localCoefficient i j x.val
  have ha : Continuous a := (F.continuousOn_localCoefficient i j).comp_continuous
    continuous_subtype_val (fun x => x.property)
  let eA : U × ProperFutureLorentz ≃ₜ U × ProperFutureLorentz :=
    ProductCovering.skewMul a ha
  have hc := (ProductCovering.isCoveringMap_id_prodMap (T := U)
    CliffordSpinCovering.lorentzHom_isCoveringMap).homeomorph_comp eA
  have hcover := (hc.comp_homeomorph eS).homeomorph_comp eL.symm
  have he : V.restrictPreimage F =
      eL.symm ∘ ((eA ∘ Prod.map (id : U → U) lorentzHom) ∘ eS) := by
    funext q
    apply eL.injective
    simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
    have hq : spinProj q.val ∈ U := by
      rw [← F.proj]
      exact q.property
    have hsi : spinProj q.val ∈ (S.triv i).baseSet := hq.1
    have hlj : spinProj q.val ∈ (L.triv j).baseSet := hq.2
    have hformula := F.local_formula i j (spinProj q.val) (S.triv i q.val).2 hsi hlj
    rw [(S.triv i).symm_apply_mk_proj ((S.triv i).mem_source.mpr hsi)] at hformula
    have hLcoord : eL (V.restrictPreimage F q) =
        (⟨frameProj (F q.val), q.property⟩, (L.triv j (F q.val)).2) :=
      (L.triv j).preimageHomeomorph_apply
        (show U ⊆ (L.triv j).baseSet from inter_subset_right) _
    have hScoord : eS q = (⟨spinProj q.val, hq⟩, (S.triv i q.val).2) :=
      (S.triv i).preimageHomeomorph_apply
        (show U ⊆ (S.triv i).baseSet from inter_subset_left) ((Homeomorph.setCongr hpre) q)
    rw [hLcoord, hScoord]
    change ((⟨frameProj (F q.val), q.property⟩ : U), (L.triv j (F q.val)).2) =
      ((⟨spinProj q.val, hq⟩ : U), F.localCoefficient i j (spinProj q.val) *
        lorentzHom (S.triv i q.val).2)
    apply Prod.ext
    · apply Subtype.ext
      exact F.proj q.val
    · exact congrArg (fun z : B × ProperFutureLorentz => z.2) hformula
  rw [he]
  exact hcover

/-- Every supplied independent geometric Spin lift is genuinely a covering map, proved on its actual base-chart neighborhoods. -/
theorem isCoveringMap : IsCoveringMap F := by
  intro p
  obtain ⟨i, hi⟩ := S.covers (frameProj p)
  obtain ⟨j, hj⟩ := L.covers (frameProj p)
  let V : Set P := frameProj ⁻¹' ((S.triv i).baseSet ∩ (L.triv j).baseSet)
  have hV : IsOpen V := ((S.triv i).open_baseSet.inter (L.triv j).open_baseSet).preimage
    L.continuous_proj
  have hc : IsCoveringMapOn F V :=
    IsCoveringMapOn.of_isCoveringMap_restrictPreimage V hV
      (hV.preimage F.continuous_toFun) (F.isCoveringMap_restrict_overlap i j)
  exact hc p ⟨hi, hj⟩

/-- Each actual geometric lift fiber is equivalent to the literal two-element type. -/
def fiberEquivTwo (p : P) : (F ⁻¹' {p}) ≃ Fin 2 := by
  let q := Classical.choose (F.surjective p)
  have hq : F q = p := Classical.choose_spec (F.surjective p)
  rw [← hq]
  exact (F.kernelFiberEquiv q).symm.trans (CliffordSpinCovering.lorentzFiberEquiv 1)

/-- Every actual Lorentz frame has an evenly covered neighborhood with precisely the discrete sheets Fin 2. -/
theorem isEvenlyCovered_two (p : P) : IsEvenlyCovered F p (Fin 2) := by
  let := (F.isCoveringMap p).discreteTopology_fiber
  exact (F.isCoveringMap p).of_fiber_homeomorph (F.fiberEquivTwo p).toHomeomorphOfDiscrete

/-- A supplied independent geometric Spin lift is a genuine covering with exactly two points over every actual target frame. -/
theorem two_sheeted : IsCoveringMap F ∧ ∀ p : P, Nat.card (F ⁻¹' {p}) = 2 :=
  ⟨F.isCoveringMap, F.fiber_card⟩

end FoliationQM.GeometricSpinLift.Map
