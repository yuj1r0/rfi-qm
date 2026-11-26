module
public import FoliationQM.PresentedLorentzBundle

/-!
# Transport of Lorentz atlases along a homeomorphism of total spaces

For the geometric frame component of v13 `prop:takabayasi`, transporting the
actual principal trivializations over the same base preserves their transition
functions. A fiber-preserving equivariant homeomorphism therefore preserves
existence of a path presentation and its native degree-two obstruction.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LorentzAtlasHomeomorphism
open LorentzMatrixGroup PathTransitionData PrincipalAtlasCrossGauge PresentedLorentzBundle

variable {B T U ι : Type*} [TopologicalSpace B] [TopologicalSpace T] [TopologicalSpace U]
  {proj : T → B} {act : T → ProperFutureLorentz → T}

/-- The action conjugated by the homeomorphism of total spaces. -/
def right (act : T → ProperFutureLorentz → T) (e : U ≃ₜ T) (u : U) (g : ProperFutureLorentz) : U :=
  e.symm (act (e u) g)

/-- Precompose every actual trivialization with the homeomorphism. -/
def atlas (A : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι) (e : U ≃ₜ T) :
    GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) (proj ∘ e) ι where
  triv i := (A.triv i).compHomeomorph e
  covers := A.covers
  right := right A.right e
  proj_right u g := by
    change proj (e (e.symm (A.right (e u) g))) = proj (e u)
    rw [e.apply_symm_apply, A.proj_right]
  right_local i u g hu := by
    change (A.triv i (e (e.symm (A.right (e u) g)))).2 = (A.triv i (e u)).2 * g
    rw [e.apply_symm_apply]
    exact A.right_local i (e u) g hu

variable (A : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι) (e : U ≃ₜ T)

/-- The chart domains on the base are unchanged. -/
theorem baseSet (i : ι) : ((atlas A e).triv i).baseSet = (A.triv i).baseSet := rfl

/-- The canonical section is the inverse image of the original unit section. -/
theorem localSection (i : ι) (x : B) : (atlas A e).localSection i x = e.symm (A.localSection i x) := rfl

/-- The transported representatives of the transitions agree on the entire base. -/
theorem transition (i j : ι) (x : B) : (atlas A e).transition i j x = A.transition i j x := by
  change (A.triv j (e (e.symm (A.localSection i x)))).2 = (A.triv j (A.localSection i x)).2
  rw [e.apply_symm_apply]

/-- The transported atlas has the same extracted transition data. -/
theorem data_eq : data (atlas A e) = data A := by
  unfold data
  congr 1
  funext i j x
  exact transition A e i j x

/-- View the same normalized path family as a family of the transported atlas. -/
def family (P : Family (data A)) : Family (data (atlas A e)) :=
  (data_eq A e).symm ▸ P

/-- Transport a presentation while retaining its point-indexed cover and anchors. -/
def presentation (p : Presentation proj act) (e : U ≃ₜ T) :
    Presentation (proj ∘ e) (right act e) where
  atlas := atlas p.atlas e
  anchor := p.anchor
  right_eq := congrArg (fun a => right a e) p.right_eq
  family := family p.atlas e p.family

variable {q : U → B} {actU : U → ProperFutureLorentz → U}

/-- A fiber-preserving equivariant homeomorphism transports a presented action
to any prescribed compatible projection and right action on its domain. -/
theorem hasPresentation_of_equivariant (h : HasPresentation proj act) (e : U ≃ₜ T)
    (hq : ∀ u, q u = proj (e u)) (he : ∀ u g, e (actU u g) = act (e u) g) :
    HasPresentation q actU := by
  have hright : actU = right act e := funext₂ fun u g => e.injective (by simpa [right] using he u g)
  have hproj : q = proj ∘ e := funext hq
  rw [hproj, hright]
  exact ⟨presentation h.some e⟩

/-- In either direction the same bundle isomorphism preserves existence of a presentation. -/
theorem hasPresentation_iff (e : U ≃ₜ T) (hq : ∀ u, q u = proj (e u))
    (he : ∀ u g, e (actU u g) = act (e u) g) :
    HasPresentation q actU ↔ HasPresentation proj act := by
  refine ⟨fun h => hasPresentation_of_equivariant h e.symm (fun t => ?_) (fun t g => ?_),
    fun h => hasPresentation_of_equivariant h e hq he⟩
  · simpa using (hq (e.symm t)).symm
  · apply e.injective
    simpa using (he (e.symm t) g).symm

variable [LocallyPathConnectedSpace B]

/-- The transported family has the same intrinsic all-cover obstruction. -/
theorem family_obstruction (P : Family (data A)) :
    GlobalIntrinsicPathObstruction.obstruction LorentzPathCoefficient.character (family A e P) =
      GlobalIntrinsicPathObstruction.obstruction LorentzPathCoefficient.character P := by
  have h {D E : PathTransitionData.Data ProperFutureLorentz B ι} (hDE : D = E) (Q : Family E) :
      GlobalIntrinsicPathObstruction.obstruction LorentzPathCoefficient.character (hDE.symm ▸ Q : Family D) =
        GlobalIntrinsicPathObstruction.obstruction LorentzPathCoefficient.character Q := by
    cases hDE
    rfl
  exact h (data_eq A e) P

/-- Independence of the native obstruction under a change of total space by an
equivariant homeomorphism over the base, allowing independently charted presentations. -/
theorem obstruction_eq (hU : HasPresentation q actU) (hT : HasPresentation proj act) (e : U ≃ₜ T)
    (hq : ∀ u, q u = proj (e u)) (he : ∀ u g, e (actU u g) = act (e u) g) :
    obstruction hU = obstruction hT := by
  have hproj : q = proj ∘ e := funext hq
  subst q
  let p := hT.some
  have hr : (atlas p.atlas e).right = actU := by
    funext u g
    change e.symm (p.atlas.right (e u) g) = actU u g
    apply e.injective
    rw [e.apply_symm_apply, p.right_eq]
    exact (he u g).symm
  exact (PresentedLorentzBundle.obstruction_eq hU _ hr (family p.atlas e p.family)).trans
    ((family_obstruction p.atlas e p.family).trans
      (PresentedLorentzBundle.obstruction_eq hT p.atlas p.right_eq p.family).symm)

end FoliationQM.LorentzAtlasHomeomorphism
