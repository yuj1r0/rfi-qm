module
public import FoliationQM.CliffordSpinSignManifold
public import Mathlib.Geometry.Manifold.ContMDiffMap

/-!
# Smooth genuine Clifford Spin sign fields and anchored Lorentz lifts

Source scope: the actual Spin/Lorentz field correspondence in v13
`prop:takabayasi` and `eq:tetrad_rotor_map`.  The genuine sign quotient
provides global quotient-valued fields.  Individual Spin representatives
are instead constructed on the explicit preimages of actual smooth
inverse domains, through any prescribed lift of a field value.

The actual smooth covering also detects regularity of an existing
continuous individual lift, including arbitrary within-set domains.
Uniqueness on preconnected subsets uses the genuine covering topology.
No global individual lift is selected or asserted for arbitrary fields,
and no geometric spacetime Spin structure is assumed or constructed.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Operator Manifold
open Function Set Filter Topology
namespace FoliationQM.CliffordSpinLorentzFields
open CliffordSpinMap CliffordSpinLorentz LorentzMatrixGroup CliffordSpinCovering

/-- The actual Clifford Spin source manifold model used for individual representatives. -/
abbrev spinModel := CliffordSpinLorentzSmooth.spinModel

/-- The independent real Lorentz Cayley manifold model used for physical fields. -/
abbrev lorentzModel := CliffordSpinLorentzSmooth.lorentzModel

/-- The global recovered actual Clifford sign class of a Lorentz element, with no individual lift choice. -/
def classOf (L : ProperFutureLorentz) : SignQuotient := quotientMulHomeomorph.symm L

/-- The global recovered class of a displayed actual Spin image is exactly its genuine sign quotient class. -/
theorem classOf_image (s : Spin) : classOf (lorentzHom s) = QuotientGroup.mk s :=
  quotientMulHomeomorph_symm_image s

/-- The physical Lorentz image of the recovered actual sign class is the original Lorentz element. -/
theorem image_classOf (L : ProperFutureLorentz) : quotientMulHomeomorph (classOf L) = L :=
  quotientMulHomeomorph.apply_symm_apply L

/-- The actual global sign-class reconstruction is smooth for the independently constructed sign quotient and Lorentz atlases. -/
theorem contMDiff_classOf (n : WithTop ℕ∞) :
    ContMDiff lorentzModel CliffordSpinSignManifold.model n classOf :=
  CliffordSpinSignManifold.contMDiff_quotientMulHomeomorph_symm n

section Fields
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- The actual physical quotient diffeomorphism gives an equivalence between bundled smooth genuine sign-class fields and Lorentz fields on any charted base. -/
def fieldEquiv (n : WithTop ℕ∞) :
    C^n⟮I, M; CliffordSpinSignManifold.model, SignQuotient⟯ ≃
      C^n⟮I, M; lorentzModel, ProperFutureLorentz⟯ where
  toFun q := (CliffordSpinSignManifold.quotientDiffeomorph n).toContMDiffMap.comp q
  invFun L := (CliffordSpinSignManifold.quotientDiffeomorph n).symm.toContMDiffMap.comp L
  left_inv q := by
    apply ContMDiffMap.ext
    intro x
    exact (CliffordSpinSignManifold.quotientDiffeomorph n).symm_apply_apply (q x)
  right_inv L := by
    apply ContMDiffMap.ext
    intro x
    exact (CliffordSpinSignManifold.quotientDiffeomorph n).apply_symm_apply (L x)

/-- Bundled sign-class field realization is pointwise the original actual Clifford quotient homomorphism. -/
theorem fieldEquiv_apply (n : WithTop ℕ∞)
    (q : C^n⟮I, M; CliffordSpinSignManifold.model, SignQuotient⟯) (x : M) :
    fieldEquiv n q x = quotientMulHomeomorph (q x) :=
  CliffordSpinSignManifold.quotientDiffeomorph_apply n (q x)

/-- Bundled inverse field correspondence recovers exactly the global actual Clifford sign class pointwise. -/
theorem fieldEquiv_symm_apply (n : WithTop ℕ∞)
    (L : C^n⟮I, M; lorentzModel, ProperFutureLorentz⟯) (x : M) :
    (fieldEquiv n).symm L x = classOf (L x) :=
  CliffordSpinSignManifold.quotientDiffeomorph_symm_apply n (L x)

/-- At every displayed genuine Spin representative, the bundled quotient field has exactly the actual physical Lorentz image. -/
theorem fieldEquiv_mk (n : WithTop ℕ∞)
    (q : C^n⟮I, M; CliffordSpinSignManifold.model, SignQuotient⟯)
    (x : M) (s : Spin) (hx : q x = QuotientGroup.mk s) :
    fieldEquiv n q x = lorentzHom s := by
  rw [fieldEquiv_apply, hx, quotientMulHomeomorph_mk]

/-- Any displayed actual representative of a bundled Lorentz value determines precisely its recovered sign class. -/
theorem fieldEquiv_symm_image (n : WithTop ℕ∞)
    (L : C^n⟮I, M; lorentzModel, ProperFutureLorentz⟯)
    (x : M) (s : Spin) (hx : L x = lorentzHom s) :
    (fieldEquiv n).symm L x = QuotientGroup.mk s := by
  rw [fieldEquiv_symm_apply, hx, classOf_image]

/-- Every smooth Lorentz field has exactly one bundled smooth actual Spin sign-class field with that physical realization. -/
theorem existsUnique_field (n : WithTop ℕ∞)
    (L : C^n⟮I, M; lorentzModel, ProperFutureLorentz⟯) :
    ∃! q : C^n⟮I, M; CliffordSpinSignManifold.model, SignQuotient⟯,
      ∀ x, quotientMulHomeomorph (q x) = L x := by
  refine ⟨(fieldEquiv n).symm L, ?_, ?_⟩
  · intro x
    rw [fieldEquiv_symm_apply, image_classOf]
  · intro q hq
    apply ContMDiffMap.ext
    intro x
    apply quotientMulHomeomorph.injective
    rw [hq x, fieldEquiv_symm_apply, image_classOf]

/-- On every within-set source domain, Lorentz smoothness is equivalent to smoothness of its globally recovered genuine Spin sign class. -/
theorem contMDiffWithinAt_iff_classOf {n : WithTop ℕ∞}
    {L : M → ProperFutureLorentz} {U : Set M} {x : M} :
    ContMDiffWithinAt I lorentzModel n L U x ↔
      ContMDiffWithinAt I CliffordSpinSignManifold.model n (classOf ∘ L) U x := by
  constructor
  · intro h
    exact (contMDiff_classOf n).contMDiffAt.comp_contMDiffWithinAt x h
  · intro h
    have hc := (CliffordSpinSignManifold.contMDiff_quotientMulHomeomorph n).contMDiffAt.comp_contMDiffWithinAt x h
    simpa only [Function.comp_def, image_classOf] using hc

/-- At every point, Lorentz smoothness is exactly smoothness of the actual quotient-valued sign-class field. -/
theorem contMDiffAt_iff_classOf {n : WithTop ℕ∞} {L : M → ProperFutureLorentz} {x : M} :
    ContMDiffAt I lorentzModel n L x ↔
      ContMDiffAt I CliffordSpinSignManifold.model n (classOf ∘ L) x :=
  contMDiffWithinAt_iff_classOf

/-- On any subset, Lorentz smoothness is exactly smoothness of its genuine quotient-valued sign-class field. -/
theorem contMDiffOn_iff_classOf {n : WithTop ℕ∞} {L : M → ProperFutureLorentz} {U : Set M} :
    ContMDiffOn I lorentzModel n L U ↔
      ContMDiffOn I CliffordSpinSignManifold.model n (classOf ∘ L) U := by
  simp only [ContMDiffOn, contMDiffWithinAt_iff_classOf]

/-- Global Lorentz smoothness is exactly global smoothness of the genuine actual Spin sign-class field. -/
theorem contMDiff_iff_classOf {n : WithTop ℕ∞} {L : M → ProperFutureLorentz} :
    ContMDiff I lorentzModel n L ↔
      ContMDiff I CliffordSpinSignManifold.model n (classOf ∘ L) := by
  simp only [ContMDiff, contMDiffAt_iff_classOf]

end Fields

variable {X : Type*}

/-- The actual anchored field lift domain is the preimage of the chosen smooth inverse's genuine open source. -/
def liftDomain (n : WithTop ℕ∞) (L : X → ProperFutureLorentz) (s : Spin) : Set X :=
  L ⁻¹' (CliffordSpinLorentzSmooth.localInverse n s).source

/-- The anchored individual Spin field is the supplied Lorentz field composed with its actual smooth local inverse. -/
def lift (n : WithTop ℕ∞) (L : X → ProperFutureLorentz) (s : Spin) : X → Spin :=
  CliffordSpinLorentzSmooth.localInverse n s ∘ L

/-- A continuous Lorentz field gives an open explicit anchored lift domain in the original base topology. -/
theorem liftDomain_isOpen [TopologicalSpace X] {L : X → ProperFutureLorentz}
    (hL : Continuous L) (n : WithTop ℕ∞) (s : Spin) : IsOpen (liftDomain n L s) :=
  (CliffordSpinLorentzSmooth.localInverse n s).open_source.preimage hL

/-- Any prescribed actual Spin representative of the base value places that point in its explicit lift domain. -/
theorem mem_liftDomain {n : WithTop ℕ∞} {L : X → ProperFutureLorentz} {x : X} {s : Spin}
    (hx : L x = lorentzHom s) : x ∈ liftDomain n L s := by
  change L x ∈ (CliffordSpinLorentzSmooth.localInverse n s).source
  rw [hx]
  exact CliffordSpinLorentzSmooth.image_mem_localInverse_source n s

/-- The actual local field lift returns precisely its prescribed Clifford Spin anchor. -/
theorem lift_at {n : WithTop ℕ∞} {L : X → ProperFutureLorentz} {x : X} {s : Spin}
    (hx : L x = lorentzHom s) : lift n L s x = s := by
  change CliffordSpinLorentzSmooth.localInverse n s (L x) = s
  rw [hx, CliffordSpinLorentzSmooth.localInverse_image]

/-- On its genuine domain, the anchored actual Spin lift projects exactly to the original Lorentz field. -/
theorem projection_lift {n : WithTop ℕ∞} {L : X → ProperFutureLorentz} {s : Spin} {x : X}
    (hx : x ∈ liftDomain n L s) : lorentzHom (lift n L s x) = L x :=
  CliffordSpinLorentzSmooth.image_localInverse hx

/-- Every individual local lift represents exactly the globally recovered sign class of the Lorentz field. -/
theorem quotient_lift {n : WithTop ℕ∞} {L : X → ProperFutureLorentz} {s : Spin} {x : X}
    (hx : x ∈ liftDomain n L s) :
    (QuotientGroup.mk (lift n L s x) : SignQuotient) = classOf (L x) := by
  rw [← classOf_image, projection_lift hx]

section SmoothLifts
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  {n : WithTop ℕ∞} {L : M → ProperFutureLorentz}

/-- Every smooth Lorentz field has a smooth actual Spin lift on the full explicit inverse preimage domain through each prescribed representative. -/
theorem contMDiffOn_lift (hL : ContMDiff I lorentzModel n L) (s : Spin) :
    ContMDiffOn I spinModel n (lift n L s) (liftDomain n L s) :=
  (CliffordSpinLorentzSmooth.contMDiffOn_localInverse n s).comp hL.contMDiffOn
    (fun _ hx => hx)

/-- Every specified actual Spin representative extends to an anchored smooth local field with its exact open domain and physical projection. -/
theorem anchored_lift (hL : ContMDiff I lorentzModel n L)
    (x : M) (s : Spin) (hx : L x = lorentzHom s) :
    IsOpen (liftDomain n L s) ∧ x ∈ liftDomain n L s ∧
      ContMDiffOn I spinModel n (lift n L s) (liftDomain n L s) ∧
      lift n L s x = s ∧ ∀ y ∈ liftDomain n L s, lorentzHom (lift n L s y) = L y :=
  ⟨liftDomain_isOpen hL.continuous n s, mem_liftDomain hx,
    contMDiffOn_lift hL s, lift_at hx, fun _ hy => projection_lift hy⟩

/-- Within any source set, an existing continuous actual Spin field is smooth exactly when its physical Lorentz projection is smooth. -/
theorem contMDiffWithinAt_iff_projection {f : M → Spin} {U : Set M} {x : M}
    (hf : ContinuousWithinAt f U x) :
    ContMDiffWithinAt I spinModel n f U x ↔
      ContMDiffWithinAt I lorentzModel n (lorentzHom ∘ f) U x := by
  constructor
  · intro h
    exact (CliffordSpinLorentzSmooth.contMDiff_lorentzHom n).contMDiffAt.comp_contMDiffWithinAt x h
  · intro h
    have hp := CliffordSpinLorentzSmooth.lorentzHom_isLocalDiffeomorph n (f x)
    have hi := hp.contMDiffAt_localInverse.comp_contMDiffWithinAt x h
    apply hi.congr_of_eventuallyEq
    · exact (hp.localInverse_eventuallyEq_left.comp_tendsto hf).symm
    · exact (hp.localInverse_left_inv hp.localInverse_mem_target).symm

/-- At any source point, continuity of an actual Spin field makes its smoothness equivalent to smoothness of its physical Lorentz projection. -/
theorem contMDiffAt_iff_projection {f : M → Spin} {x : M} (hf : ContinuousAt f x) :
    ContMDiffAt I spinModel n f x ↔ ContMDiffAt I lorentzModel n (lorentzHom ∘ f) x :=
  contMDiffWithinAt_iff_projection hf.continuousWithinAt

/-- On any source subset, a continuous actual Spin field is smooth exactly when its physical projection is smooth on that subset. -/
theorem contMDiffOn_iff_projection {f : M → Spin} {U : Set M} (hf : ContinuousOn f U) :
    ContMDiffOn I spinModel n f U ↔ ContMDiffOn I lorentzModel n (lorentzHom ∘ f) U := by
  constructor
  · intro h x hx
    exact (contMDiffWithinAt_iff_projection (hf x hx)).mp (h x hx)
  · intro h x hx
    exact (contMDiffWithinAt_iff_projection (hf x hx)).mpr (h x hx)

/-- An existing globally continuous actual Spin field is smooth exactly when its actual Lorentz projection is smooth. -/
theorem contMDiff_iff_projection {f : M → Spin} (hf : Continuous f) :
    ContMDiff I spinModel n f ↔ ContMDiff I lorentzModel n (lorentzHom ∘ f) := by
  constructor
  · intro h x
    exact (contMDiffAt_iff_projection hf.continuousAt).mp (h x)
  · intro h x
    exact (contMDiffAt_iff_projection hf.continuousAt).mpr (h x)

/-- Every existing continuous individual Spin lift of a smooth Lorentz field is itself smooth; no global lift existence is assumed or concluded. -/
theorem continuous_lift_contMDiff {f : M → Spin} (hf : Continuous f)
    (hL : ContMDiff I lorentzModel n L) (he : lorentzHom ∘ f = L) :
    ContMDiff I spinModel n f :=
  (contMDiff_iff_projection hf).mpr (he.symm ▸ hL)

end SmoothLifts

/-- Continuous individual Spin lifts on an arbitrary preconnected subset agree throughout that subset when their projections and one anchor agree. -/
theorem continuousOn_lift_unique [TopologicalSpace X] {U : Set X} (hU : IsPreconnected U)
    {f g : X → Spin} (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    (he : EqOn (lorentzHom ∘ f) (lorentzHom ∘ g) U)
    {x : X} (hx : x ∈ U) (hfg : f x = g x) : EqOn f g U := by
  let : PreconnectedSpace U := Subtype.preconnectedSpace hU
  have he' : lorentzHom ∘ U.domRestrict f = lorentzHom ∘ U.domRestrict g := by
    funext y
    exact he y.property
  have h := CliffordSpinCovering.continuous_lift_unique hf.domRestrict hg.domRestrict he'
    (⟨x, hx⟩ : U) hfg
  intro y hy
  exact congrFun h (⟨y, hy⟩ : U)

end FoliationQM.CliffordSpinLorentzFields
