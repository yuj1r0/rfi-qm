module
public import FoliationQM.CliffordSpinPolarReconstruction
public import FoliationQM.FrameRepresentativeObstruction
public import Mathlib.Geometry.Manifold.ContMDiffMap

/-!
# Smooth actual Clifford polar fields and universal section obstructions

Source scope: the actual Spin quotient-valued field content of v13
`prop:takabayasi` and `eq:takabayasi_polar`. The established genuine
product and full-source quotient diffeomorphisms induce equivalences of
bundled smooth fields on any real charted base. The inverse recovers the
actual invariant bilinear density and the genuine full-angle/Clifford
frame sign class. Their smoothness characterizes regular-spinor
smoothness, including arbitrary within-set domains.

The previously proved explicit-loop obstruction transfers through the
actual coordinate homeomorphisms: there is no universal continuous or
smooth section of the full frame quotient, full source quotient, or
regular-spinor realization covering. This does not prohibit global
individual lifts for particular liftable fields, including constant
fields. Quotient-valued reconstruction is global and smooth. No new
local lifting theorem, spacetime spin structure, or dynamical assertion
is introduced here.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Operator Manifold
open Function Set Topology
namespace FoliationQM.CliffordSpinPolarFields
open CliffordSpinPolarDatum CliffordSpinPolarQuotient CliffordSpinPolarReconstruction
open DiracMatrices PolarSignQuotient PolarAmplitudeTopology

/-- The positive density recovered by the actual inverse Clifford polar quotient realization. -/
def density (q : RegularSpinor) : PositiveDensity := (productRegularHomeomorph.symm q).1

/-- The genuine full-angle/Clifford-Spin sign class recovered by the actual inverse polar quotient realization. -/
def frameClass (q : RegularSpinor) : FrameQuotient := (productRegularHomeomorph.symm q).2

/-- The recovered positive density is exactly the actual scalar-pseudoscalar bilinear invariant density. -/
theorem density_value_eq_invariantDensity (q : RegularSpinor) :
    (density q : ℝ) = SpinorRegularity.invariantDensity q.val :=
  productRegularHomeomorph_symm_density q

/-- Realizing the actual recovered density and genuine Clifford frame class gives the original strict regular spinor. -/
theorem realize_components (q : RegularSpinor) :
    productRegularHomeomorph (density q, frameClass q) = q :=
  productRegularHomeomorph.apply_symm_apply q

/-- The actual natural quotient reconstruction is smooth to every order for the independently specified product atlas. -/
theorem contMDiff_productInverse (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℝ, Spinor) model n productRegularHomeomorph.symm := by
  rw [← productRegularDiffeomorph_toHomeomorph n]
  exact (productRegularDiffeomorph n).symm.contMDiff

/-- Actual positive-density recovery is smooth on the strict regular-spinor manifold to every order. -/
theorem contMDiff_density (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℝ, Spinor) 𝓘(ℝ, ℝ) n density := (contMDiff_productInverse n).fst

/-- Actual Clifford frame-class recovery is smooth into the compatible seven-dimensional quotient atlas to every order. -/
theorem contMDiff_frameClass (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℝ, Spinor) CliffordSpinPolarManifold.model n frameClass :=
  (contMDiff_productInverse n).snd

section Fields
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- Actual Clifford polar realization gives an equivalence of bundled smooth density/frame-class fields and regular-spinor fields on every real charted base. -/
def fieldEquiv (n : WithTop ℕ∞) :
    C^n⟮I, M; model, Product⟯ ≃ C^n⟮I, M; 𝓘(ℝ, Spinor), RegularSpinor⟯ where
  toFun f := (productRegularDiffeomorph n).toContMDiffMap.comp f
  invFun psi := (productRegularDiffeomorph n).symm.toContMDiffMap.comp psi
  left_inv f := by
    apply ContMDiffMap.ext
    intro x
    exact (productRegularDiffeomorph n).symm_apply_apply (f x)
  right_inv psi := by
    apply ContMDiffMap.ext
    intro x
    exact (productRegularDiffeomorph n).apply_symm_apply (psi x)

/-- Forward bundled-field correspondence realizes the actual density and genuine Clifford frame class pointwise. -/
theorem fieldEquiv_apply (n : WithTop ℕ∞)
    (f : C^n⟮I, M; model, Product⟯) (x : M) :
    fieldEquiv n f x = productRegularHomeomorph (f x) := by
  change (productRegularDiffeomorph n).toHomeomorph (f x) = _
  rw [productRegularDiffeomorph_toHomeomorph]

/-- Inverse bundled-field correspondence recovers exactly the actual density and genuine Clifford frame class pointwise. -/
theorem fieldEquiv_symm_apply (n : WithTop ℕ∞)
    (psi : C^n⟮I, M; 𝓘(ℝ, Spinor), RegularSpinor⟯) (x : M) :
    (fieldEquiv n).symm psi x = (density (psi x), frameClass (psi x)) := by
  change (productRegularDiffeomorph n).toHomeomorph.symm (psi x) = _
  rw [productRegularDiffeomorph_toHomeomorph]
  rfl

/-- At every real-angle representative, the bundled actual Clifford polar field is the physical source expression with the literal universal Dirac rotor. -/
theorem fieldEquiv_mk_real (n : WithTop ℕ∞)
    (f : C^n⟮I, M; model, Product⟯) (x : M)
    (rho : PositiveDensity) (beta : ℝ) (s : CliffordSpinMap.Spin)
    (hx : f x = (rho, Quotient.mk frameSetoid ((beta : ChiralAngleCircle.Angle), s))) :
    (fieldEquiv n f x).val =
      PolarSpinorBilinears.polarSpinor rho beta (CliffordMinkowski.dirac s.val) := by
  change (productRegularDiffeomorph n (f x)).val = _
  rw [hx]
  exact productRegularDiffeomorph_mk_real n rho beta s

/-- Every bundled smooth regular-spinor field has exactly one bundled smooth density/genuine-Clifford-frame-class field with that actual realization. -/
theorem existsUnique_field (n : WithTop ℕ∞)
    (psi : C^n⟮I, M; 𝓘(ℝ, Spinor), RegularSpinor⟯) :
    ∃! f : C^n⟮I, M; model, Product⟯,
      ∀ x, productRegularHomeomorph (f x) = psi x := by
  refine ⟨(fieldEquiv n).symm psi, ?_, ?_⟩
  · intro x
    rw [fieldEquiv_symm_apply]
    exact realize_components (psi x)
  · intro f hf
    apply ContMDiffMap.ext
    intro x
    apply productRegularHomeomorph.injective
    rw [hf x, fieldEquiv_symm_apply, realize_components]

/-- The full actual Clifford source quotient likewise gives an equivalence of bundled smooth quotient fields and regular-spinor fields. -/
def quotientFieldEquiv (n : WithTop ℕ∞) :
    C^n⟮I, M; model, SourceQuotient⟯ ≃ C^n⟮I, M; 𝓘(ℝ, Spinor), RegularSpinor⟯ where
  toFun f := (regularDiffeomorph n).toContMDiffMap.comp f
  invFun psi := (regularDiffeomorph n).symm.toContMDiffMap.comp psi
  left_inv f := by
    apply ContMDiffMap.ext
    intro x
    exact (regularDiffeomorph n).symm_apply_apply (f x)
  right_inv psi := by
    apply ContMDiffMap.ext
    intro x
    exact (regularDiffeomorph n).apply_symm_apply (psi x)

/-- Forward full-source-quotient field correspondence is pointwise the actual genuine Clifford quotient realization. -/
theorem quotientFieldEquiv_apply (n : WithTop ℕ∞)
    (f : C^n⟮I, M; model, SourceQuotient⟯) (x : M) :
    quotientFieldEquiv n f x = regularHomeomorph (f x) := by
  change (regularDiffeomorph n).toHomeomorph (f x) = _
  rw [regularDiffeomorph_toHomeomorph]

/-- Inverse full-source-quotient field correspondence is pointwise the actual genuine Clifford quotient reconstruction. -/
theorem quotientFieldEquiv_symm_apply (n : WithTop ℕ∞)
    (psi : C^n⟮I, M; 𝓘(ℝ, Spinor), RegularSpinor⟯) (x : M) :
    (quotientFieldEquiv n).symm psi x = regularHomeomorph.symm (psi x) := by
  change (regularDiffeomorph n).toHomeomorph.symm (psi x) = _
  rw [regularDiffeomorph_toHomeomorph]

/-- Every bundled smooth regular-spinor field has exactly one bundled smooth actual full-source quotient field with the specified realization. -/
theorem existsUnique_quotientField (n : WithTop ℕ∞)
    (psi : C^n⟮I, M; 𝓘(ℝ, Spinor), RegularSpinor⟯) :
    ∃! f : C^n⟮I, M; model, SourceQuotient⟯,
      ∀ x, regularHomeomorph (f x) = psi x := by
  refine ⟨(quotientFieldEquiv n).symm psi, ?_, ?_⟩
  · intro x
    rw [quotientFieldEquiv_symm_apply, regularHomeomorph.apply_symm_apply]
  · intro f hf
    apply ContMDiffMap.ext
    intro x
    apply regularHomeomorph.injective
    rw [hf x, quotientFieldEquiv_symm_apply, regularHomeomorph.apply_symm_apply]

/-- On any charted base and within any subset, regular-spinor smoothness is equivalent to smoothness of the actual real invariant density and actual Clifford frame class. -/
theorem contMDiffWithinAt_iff_density_frame
    {n : WithTop ℕ∞} {psi : M → RegularSpinor} {s : Set M} {x : M} :
    ContMDiffWithinAt I 𝓘(ℝ, Spinor) n psi s x ↔
      ContMDiffWithinAt I 𝓘(ℝ, ℝ) n
        (fun y => SpinorRegularity.invariantDensity (psi y).val) s x ∧
      ContMDiffWithinAt I CliffordSpinPolarManifold.model n (frameClass ∘ psi) s x := by
  constructor
  · intro h
    have hd := (contMDiff_density n).contMDiffAt.comp_contMDiffWithinAt x h
    have hv := PolarScalarManifolds.contMDiffWithinAt_density_iff.mp hd
    refine ⟨?_, (contMDiff_frameClass n).contMDiffAt.comp_contMDiffWithinAt x h⟩
    simpa only [Function.comp_def, density_value_eq_invariantDensity] using hv
  · rintro ⟨hr, hf⟩
    have hd : ContMDiffWithinAt I 𝓘(ℝ, ℝ) n (density ∘ psi) s x := by
      apply PolarScalarManifolds.contMDiffWithinAt_density_iff.mpr
      simpa only [Function.comp_def, density_value_eq_invariantDensity] using hr
    have hp := (productRegularDiffeomorph n).contMDiffAt.comp_contMDiffWithinAt x (hd.prodMk hf)
    have he : (productRegularDiffeomorph n) ∘
        (fun y => (density (psi y), frameClass (psi y))) = psi := by
      funext y
      change (productRegularDiffeomorph n).toHomeomorph (density (psi y), frameClass (psi y)) = _
      rw [productRegularDiffeomorph_toHomeomorph, realize_components]
    simpa only [Function.comp_def] using he ▸ hp

/-- At any point of any charted base, smoothness of a regular-spinor field is exactly smoothness of its actual invariant density and genuine Clifford frame class. -/
theorem contMDiffAt_iff_density_frame
    {n : WithTop ℕ∞} {psi : M → RegularSpinor} {x : M} :
    ContMDiffAt I 𝓘(ℝ, Spinor) n psi x ↔
      ContMDiffAt I 𝓘(ℝ, ℝ) n
        (fun y => SpinorRegularity.invariantDensity (psi y).val) x ∧
      ContMDiffAt I CliffordSpinPolarManifold.model n (frameClass ∘ psi) x :=
  contMDiffWithinAt_iff_density_frame

/-- On any subset of any charted base, smoothness of a regular-spinor field is exactly smoothness of its actual invariant density and genuine Clifford frame class. -/
theorem contMDiffOn_iff_density_frame
    {n : WithTop ℕ∞} {psi : M → RegularSpinor} {s : Set M} :
    ContMDiffOn I 𝓘(ℝ, Spinor) n psi s ↔
      ContMDiffOn I 𝓘(ℝ, ℝ) n
        (fun y => SpinorRegularity.invariantDensity (psi y).val) s ∧
      ContMDiffOn I CliffordSpinPolarManifold.model n (frameClass ∘ psi) s := by
  constructor
  · intro h
    exact ⟨fun x hx => (contMDiffWithinAt_iff_density_frame.mp (h x hx)).1,
      fun x hx => (contMDiffWithinAt_iff_density_frame.mp (h x hx)).2⟩
  · rintro ⟨hr, hf⟩ x hx
    exact contMDiffWithinAt_iff_density_frame.mpr ⟨hr x hx, hf x hx⟩

/-- Global smoothness of a regular-spinor field is exactly global smoothness of its actual invariant density and genuine Clifford frame class. -/
theorem contMDiff_iff_density_frame {n : WithTop ℕ∞} {psi : M → RegularSpinor} :
    ContMDiff I 𝓘(ℝ, Spinor) n psi ↔
      ContMDiff I 𝓘(ℝ, ℝ) n
        (fun y => SpinorRegularity.invariantDensity (psi y).val) ∧
      ContMDiff I CliffordSpinPolarManifold.model n (frameClass ∘ psi) := by
  constructor
  · intro h
    exact ⟨fun x => (contMDiffAt_iff_density_frame.mp (h x)).1,
      fun x => (contMDiffAt_iff_density_frame.mp (h x)).2⟩
  · rintro ⟨hr, hf⟩ x
    exact contMDiffAt_iff_density_frame.mpr ⟨hr x, hf x⟩

end Fields

/-- The entire actual Clifford frame quotient admits no universal continuous individual representative section of its quotient projection. -/
theorem no_continuous_frame_section :
    ¬ ∃ s : FrameQuotient → FrameDatum, Continuous s ∧
      RightInverse s (Quotient.mk frameSetoid) := by
  rintro ⟨s, hs, hr⟩
  apply FrameRepresentativeObstruction.no_continuous_frame_section
  refine ⟨frameHomeomorph ∘ s ∘ frameQuotientHomeomorph.symm,
    frameHomeomorph.continuous.comp (hs.comp frameQuotientHomeomorph.symm.continuous), ?_⟩
  intro q
  change Quotient.mk SourcePolarProductQuotient.frameSetoid
    (frameHomeomorph (s (frameQuotientHomeomorph.symm q))) = q
  rw [← frameQuotientHomeomorph_mk, hr, frameQuotientHomeomorph.apply_symm_apply]

/-- The full actual frame quotient projection admits no universal smooth individual representative section, at any order including zero. -/
theorem no_contMDiff_frame_section (n : WithTop ℕ∞) :
    ¬ ∃ s : FrameQuotient → FrameDatum,
      ContMDiff CliffordSpinPolarManifold.model frameModel n s ∧
        RightInverse s (Quotient.mk frameSetoid) := by
  rintro ⟨s, hs, hr⟩
  exact no_continuous_frame_section ⟨s, hs.continuous, hr⟩

/-- Actual Clifford polar realization over the entire regular-spinor domain admits no universal continuous source representative section. -/
theorem no_continuous_source_section :
    ¬ ∃ s : RegularSpinor → SourceDatum, Continuous s ∧
      RightInverse s CliffordSpinPolarRealization.realizeSource := by
  rintro ⟨s, hs, hr⟩
  apply PolarNoGlobalSection.no_continuous_source_section
  exact ⟨sourceHomeomorph ∘ s, sourceHomeomorph.continuous.comp hs, hr⟩

/-- Actual Clifford realization over the entire regular-spinor domain admits no universal smooth source representative section, at any order. -/
theorem no_contMDiff_source_section (n : WithTop ℕ∞) :
    ¬ ∃ s : RegularSpinor → SourceDatum,
      ContMDiff 𝓘(ℝ, Spinor) sourceModel n s ∧
        RightInverse s CliffordSpinPolarRealization.realizeSource := by
  rintro ⟨s, hs, hr⟩
  exact no_continuous_source_section ⟨s, hs.continuous, hr⟩

/-- The entire natural actual source sign quotient admits no universal continuous section of its original representative projection. -/
theorem no_continuous_sourceQuotient_section :
    ¬ ∃ s : SourceQuotient → SourceDatum, Continuous s ∧
      RightInverse s (Quotient.mk sourceSetoid) := by
  rintro ⟨s, hs, hr⟩
  apply no_continuous_source_section
  refine ⟨s ∘ regularHomeomorph.symm, hs.comp regularHomeomorph.symm.continuous, ?_⟩
  intro q
  have h := congrArg regularHomeomorph (hr (regularHomeomorph.symm q))
  simpa only [Function.comp_def, regularHomeomorph_mk, regularHomeomorph.apply_symm_apply] using h

/-- The full actual source quotient projection admits no universal smooth individual representative section, at any order. -/
theorem no_contMDiff_sourceQuotient_section (n : WithTop ℕ∞) :
    ¬ ∃ s : SourceQuotient → SourceDatum,
      ContMDiff model sourceModel n s ∧ RightInverse s (Quotient.mk sourceSetoid) := by
  rintro ⟨s, hs, hr⟩
  exact no_continuous_sourceQuotient_section ⟨s, hs.continuous, hr⟩

end FoliationQM.CliffordSpinPolarFields
