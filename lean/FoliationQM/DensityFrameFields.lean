module
public import FoliationQM.DensityFrameManifold
public import Mathlib.Geometry.Manifold.ContMDiffMap

/-!
# Smooth density and frame-class fields with local representatives

Source: the literal density-separated polar coordinates in v13
`prop:takabayasi` and `eq:takabayasi_polar`. The genuine intrinsic product
realization gives a bundled equivalence of smooth fields on any supplied
real charted base. Its inverse recovers the actual bilinear invariant
density and the actual angle-matrix sign class. Both recovered components
are smooth, and their smoothness characterizes that of the regular-spinor
field using the independently constructed factor atlases.

For any chosen point of an individual frame fiber, the actual frame
covering inverse produces a smooth local representative on an explicit
open preimage neighborhood. Combining it with the recovered density
reconstructs the original spinor exactly and is smooth as a literal source
field on that domain. The anchor and all realization claims are local;
no global individual frame representative or real angle is selected.
These are fixed-representation field statements, without a new action,
abstract Spin identification, or twisted bundle assumption.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Operator Manifold
open Set Topology Function
namespace FoliationQM.DensityFrameFields
open DiracMatrices PolarSignQuotient PolarAmplitudeTopology SourcePolarDatum
open SourcePolarProductQuotient

/-- The positive density recovered by the actual inverse density-frame realization. -/
def density (q : RegularSpinor) : PositiveDensity := (productRegularHomeomorph.symm q).1

/-- The natural angle-matrix sign class recovered by the actual inverse density-frame realization. -/
def frameClass (q : RegularSpinor) : FrameQuotient := (productRegularHomeomorph.symm q).2

/-- The recovered positive-density coordinate is exactly the original spinor bilinear invariant density. -/
theorem density_value_eq_invariantDensity (q : RegularSpinor) :
    (density q : ℝ) = SpinorRegularity.invariantDensity q.val :=
  productRegularHomeomorph_symm_density q

/-- Realizing the actual recovered density and frame class returns the original strict regular spinor. -/
theorem realize_components (q : RegularSpinor) :
    productRegularHomeomorph (density q, frameClass q) = q :=
  productRegularHomeomorph.apply_symm_apply q

/-- Actual positive-density recovery is manifold-smooth to every order for the independently specified atlases. -/
theorem contMDiff_density (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℝ, Spinor) 𝓘(ℝ, ℝ) n density :=
  (DensityFrameManifold.productRegularDiffeomorph n).symm.contMDiff.fst

/-- Actual frame-class recovery is manifold-smooth to every order for the intrinsic seven-dimensional quotient atlas. -/
theorem contMDiff_frameClass (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℝ, Spinor) FrameQuotientManifold.model n frameClass :=
  (DensityFrameManifold.productRegularDiffeomorph n).symm.contMDiff.snd

/-- The actual real-valued bilinear invariant density is smooth on the strict regular-spinor manifold. -/
theorem contMDiff_invariantDensity (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℝ, Spinor) 𝓘(ℝ, ℝ) n
      (fun q : RegularSpinor => SpinorRegularity.invariantDensity q.val) := by
  have h := (PolarScalarManifolds.contMDiff_density_value n).comp (contMDiff_density n)
  simpa only [Function.comp_def, density_value_eq_invariantDensity] using h

section Fields
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- The genuine product realization induces an equivalence of bundled smooth density-frame fields and bundled smooth regular-spinor fields on any supplied real charted base. -/
def fieldEquiv (n : WithTop ℕ∞) :
    C^n⟮I, M; DensityFrameManifold.model, DensityFrameManifold.Product⟯ ≃
      C^n⟮I, M; 𝓘(ℝ, Spinor), RegularSpinor⟯ where
  toFun f := (DensityFrameManifold.productRegularDiffeomorph n).toContMDiffMap.comp f
  invFun psi := (DensityFrameManifold.productRegularDiffeomorph n).symm.toContMDiffMap.comp psi
  left_inv f := by
    apply ContMDiffMap.ext
    intro x
    exact (DensityFrameManifold.productRegularDiffeomorph n).symm_apply_apply (f x)
  right_inv psi := by
    apply ContMDiffMap.ext
    intro x
    exact (DensityFrameManifold.productRegularDiffeomorph n).apply_symm_apply (psi x)

/-- The forward bundled-field equivalence realizes exactly the existing density-frame product at each base point. -/
theorem fieldEquiv_apply (n : WithTop ℕ∞)
    (f : C^n⟮I, M; DensityFrameManifold.model, DensityFrameManifold.Product⟯) (x : M) :
    fieldEquiv n f x = productRegularHomeomorph (f x) := rfl

/-- The inverse bundled-field equivalence recovers exactly the positive density and natural frame sign class at each base point. -/
theorem fieldEquiv_symm_apply (n : WithTop ℕ∞)
    (psi : C^n⟮I, M; 𝓘(ℝ, Spinor), RegularSpinor⟯) (x : M) :
    (fieldEquiv n).symm psi x = (density (psi x), frameClass (psi x)) := rfl

/-- At any literal real-angle representative, bundled field realization is exactly the actual source polar spinor expression. -/
theorem fieldEquiv_mk_real (n : WithTop ℕ∞)
    (f : C^n⟮I, M; DensityFrameManifold.model, DensityFrameManifold.Product⟯) (x : M)
    (rho : PositiveDensity) (beta : ℝ) (A : SpecialLinearMatrix)
    (hx : f x = (rho, Quotient.mk frameSetoid ((beta : ChiralAngleCircle.Angle), A))) :
    (fieldEquiv n f x).val =
      PolarSpinorBilinears.polarSpinor rho beta (SpecialLinearSpin.spin A) := by
  rw [fieldEquiv_apply, hx]
  exact DensityFrameManifold.productRegularDiffeomorph_mk_real n rho beta A

/-- At a point of any supplied real charted base, intrinsic spinor-field smoothness is equivalent to smoothness of its actual real invariant density and intrinsic frame class. -/
theorem contMDiffAt_iff_density_frame {n : WithTop ℕ∞} {psi : M → RegularSpinor} {x : M} :
    ContMDiffAt I 𝓘(ℝ, Spinor) n psi x ↔
      ContMDiffAt I 𝓘(ℝ, ℝ) n
        (fun y => SpinorRegularity.invariantDensity (psi y).val) x ∧
      ContMDiffAt I FrameQuotientManifold.model n (frameClass ∘ psi) x := by
  have h := (DensityFrameManifold.productRegularDiffeomorph n).symm.contMDiffAt_diffeomorph_comp_iff (I' := I) (f := psi) (x := x) le_rfl
  rw [← h, contMDiffAt_prod_iff]
  change ContMDiffAt I 𝓘(ℝ, ℝ) n (density ∘ psi) x ∧
    ContMDiffAt I FrameQuotientManifold.model n (frameClass ∘ psi) x ↔ _
  rw [PolarScalarManifolds.contMDiffAt_density_iff]
  simp only [Function.comp_def, density_value_eq_invariantDensity]

/-- On any supplied real charted base, intrinsic spinor-field smoothness is equivalent to smoothness of the actual real invariant density and intrinsic frame class. -/
theorem contMDiff_iff_density_frame {n : WithTop ℕ∞} {psi : M → RegularSpinor} :
    ContMDiff I 𝓘(ℝ, Spinor) n psi ↔
      ContMDiff I 𝓘(ℝ, ℝ) n
        (fun y => SpinorRegularity.invariantDensity (psi y).val) ∧
      ContMDiff I FrameQuotientManifold.model n (frameClass ∘ psi) := by
  constructor
  · intro h
    exact ⟨fun x => (contMDiffAt_iff_density_frame.mp (h x)).1,
      fun x => (contMDiffAt_iff_density_frame.mp (h x)).2⟩
  · rintro ⟨hr, hf⟩ x
    exact contMDiffAt_iff_density_frame.mpr ⟨hr x, hf x⟩

end Fields

variable {X : Type*}

/-- The anchored individual-frame lift domain is the actual preimage of the chosen frame covering inverse source under the recovered frame-class field. -/
def frameLiftDomain (psi : X → RegularSpinor) (p : FrameDatum) : Set X :=
  (frameClass ∘ psi) ⁻¹' (FrameQuotientCovering.frame_mk_isLocalHomeomorph.localInverseAt p).source

/-- The actual anchored individual-frame lift is the chosen frame covering inverse applied to the recovered frame-class field. -/
def frameLift (psi : X → RegularSpinor) (p : FrameDatum) : X → FrameDatum :=
  (FrameQuotientCovering.frame_mk_isLocalHomeomorph.localInverseAt p) ∘ frameClass ∘ psi

/-- A continuous regular-spinor field gives the actual individual-frame lift an open preimage domain. -/
theorem frameLiftDomain_isOpen [TopologicalSpace X] {psi : X → RegularSpinor}
    (hpsi : Continuous psi) (p : FrameDatum) : IsOpen (frameLiftDomain psi p) :=
  (FrameQuotientCovering.frame_mk_isLocalHomeomorph.localInverseAt p).open_source.preimage
    ((continuous_snd.comp productRegularHomeomorph.symm.continuous).comp hpsi)

/-- A prescribed frame representative of the recovered class places the base point in the actual individual-frame lift domain. -/
theorem mem_frameLiftDomain {psi : X → RegularSpinor} {x : X} {p : FrameDatum}
    (hx : frameClass (psi x) = Quotient.mk frameSetoid p) : x ∈ frameLiftDomain psi p := by
  change frameClass (psi x) ∈ (FrameQuotientCovering.frame_mk_isLocalHomeomorph.localInverseAt p).source
  rw [hx]
  exact FrameQuotientCovering.frame_mk_isLocalHomeomorph.apply_self_mem_localInverseAt_source

/-- The actual individual-frame lift takes the prescribed representative at the anchored base point. -/
theorem frameLift_at {psi : X → RegularSpinor} {x : X} {p : FrameDatum}
    (hx : frameClass (psi x) = Quotient.mk frameSetoid p) : frameLift psi p x = p := by
  change FrameQuotientCovering.frame_mk_isLocalHomeomorph.localInverseAt p (frameClass (psi x)) = p
  rw [hx]
  exact FrameQuotientCovering.frame_mk_isLocalHomeomorph.localInverseAt_apply_self

/-- On the actual lift domain, projecting the lifted individual frame returns exactly the original recovered frame class. -/
theorem frameClass_frameLift {psi : X → RegularSpinor} {p : FrameDatum} {x : X}
    (hx : x ∈ frameLiftDomain psi p) :
    Quotient.mk frameSetoid (frameLift psi p x) = frameClass (psi x) :=
  FrameQuotientCovering.frame_mk_isLocalHomeomorph.apply_localInverseAt_of_mem hx

/-- On the actual lift domain, the recovered invariant density and lifted individual frame reconstruct the original spinor exactly. -/
theorem realize_frameLift {psi : X → RegularSpinor} {p : FrameDatum} {x : X}
    (hx : x ∈ frameLiftDomain psi p) :
    SourcePolarRealization.realizeSource (density (psi x), frameLift psi p x) = psi x := by
  rw [← productRegularHomeomorph_mk, frameClass_frameLift hx]
  exact realize_components (psi x)

section SmoothLifts
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  {n : WithTop ℕ∞} {psi : M → RegularSpinor}

/-- A manifold-smooth regular-spinor field has a smooth anchored individual-frame lift on the exact open preimage domain. -/
theorem contMDiffOn_frameLift (hpsi : ContMDiff I 𝓘(ℝ, Spinor) n psi) (p : FrameDatum) :
    ContMDiffOn I FrameDatumManifold.model n (frameLift psi p) (frameLiftDomain psi p) :=
  (FrameQuotientManifold.contMDiffOn_quotient_localInverse n p).comp
    ((contMDiff_frameClass n).comp hpsi).contMDiffOn (fun _ hx => hx)

/-- Combining the recovered positive density with the anchored frame lift gives a genuine smooth literal source field on the actual local domain. -/
theorem contMDiffOn_liftedSource (hpsi : ContMDiff I 𝓘(ℝ, Spinor) n psi) (p : FrameDatum) :
    ContMDiffOn I SourceDatumManifold.model n
      (fun x => (density (psi x), frameLift psi p x)) (frameLiftDomain psi p) :=
  (((contMDiff_density n).comp hpsi).contMDiffOn).prodMk (contMDiffOn_frameLift hpsi p)

/-- Through every prescribed point of the recovered frame fiber, the explicit lift has an open neighborhood domain, the prescribed anchor, actual smoothness and exact spinor reconstruction. -/
theorem anchored_frame_lift (hpsi : ContMDiff I 𝓘(ℝ, Spinor) n psi)
    (x : M) (p : FrameDatum) (hx : frameClass (psi x) = Quotient.mk frameSetoid p) :
    IsOpen (frameLiftDomain psi p) ∧ x ∈ frameLiftDomain psi p ∧
      ContMDiffOn I FrameDatumManifold.model n (frameLift psi p) (frameLiftDomain psi p) ∧
      frameLift psi p x = p ∧
      ∀ y ∈ frameLiftDomain psi p,
        SourcePolarRealization.realizeSource (density (psi y), frameLift psi p y) = psi y :=
  ⟨frameLiftDomain_isOpen hpsi.continuous p, mem_frameLiftDomain hx,
    contMDiffOn_frameLift hpsi p, frameLift_at hx, fun _ hy => realize_frameLift hy⟩

end SmoothLifts
end FoliationQM.DensityFrameFields
