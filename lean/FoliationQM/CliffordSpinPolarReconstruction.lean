module
public import FoliationQM.CliffordSpinPolarManifold
public import FoliationQM.CliffordSpinPolarCovering
public import FoliationQM.DensityFrameManifold

/-!
# Smooth reconstruction from actual Clifford Spin polar quotients

Source scope: the density-separated quotient reconstruction in v13
`prop:takabayasi` and `eq:takabayasi_polar`. Positive density and the
actual four-pi-angle/Clifford-Spin sign quotient carry their already
specified natural topologies and independent factor atlases. Their
ordinary product is smoothly identified with the existing matrix polar
product using only the proved genuine Spin quotient diffeomorphism.
Composition with its independently proved regular-spinor reconstruction
gives a genuine diffeomorphism with the exact physical Clifford formula
and actual invariant-density recovery.

The full actual source sign quotient retains its coinduced topology.
Its atlas is pulled back through the independently constructed density
splitting into the specified product atlas. Smoothness in both directions
is proved from those actual charts. The resulting full quotient realizes
regular spinors by a diffeomorphism, and its original source projection
is a smooth two-sheet covering with a genuine local diffeomorphism at
every point. No individual global representative, global real angle,
Lorentz target atlas, universal covering, or geometric spacetime bundle
is asserted by these quotient reconstruction theorems.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Operator Manifold
open Function Set Topology
namespace FoliationQM.CliffordSpinPolarReconstruction
open CliffordSpinPolarDatum CliffordSpinPolarQuotient
open PolarAmplitudeTopology PolarSignQuotient DiracMatrices

/-- Literal positive density times the genuine four-pi-angle/Clifford-Spin sign quotient in the inherited product topology and atlas. -/
abbrev Product := PositiveDensity × FrameQuotient

/-- The actual product has one density and seven frame model coordinates. -/
abbrev Model := DensityFrameManifold.Model

/-- The actual chart codomain retains the ordinary tagged density and frame chart product. -/
abbrev ChartModel := DensityFrameManifold.ChartModel

/-- The actual independent density and Clifford frame quotient models form the natural product model. -/
abbrev model := DensityFrameManifold.model

/-- The literal actual-Spin density/frame product is a real manifold to every order for its independently specified factor atlases. -/
theorem isManifold_product (n : WithTop ℕ∞) : IsManifold model n Product := inferInstance

/-- The actual density/frame product model has eight real dimensions. -/
theorem model_finrank : Module.finrank ℝ Model = 8 := DensityFrameManifold.model_finrank

/-- Keeping density fixed and applying the genuine Clifford frame quotient diffeomorphism identifies the two independent polar product manifolds. -/
def productMatrixDiffeomorph (n : WithTop ℕ∞) :
    Diffeomorph model DensityFrameManifold.model Product DensityFrameManifold.Product n :=
  (Diffeomorph.refl 𝓘(ℝ, ℝ) PositiveDensity n).prodCongr
    (CliffordSpinPolarManifold.frameQuotientDiffeomorph n)

/-- The actual product diffeomorphism preserves density and applies exactly the established natural frame quotient homeomorphism. -/
theorem productMatrixDiffeomorph_apply (n : WithTop ℕ∞) (p : Product) :
    productMatrixDiffeomorph n p = (p.1, frameQuotientHomeomorph p.2) := rfl

/-- Genuine positive density and Clifford frame classes reconstruct the entire strict regular-spinor manifold by a diffeomorphism. -/
def productRegularDiffeomorph (n : WithTop ℕ∞) :
    Diffeomorph model 𝓘(ℝ, Spinor) Product RegularSpinor n :=
  (productMatrixDiffeomorph n).trans (DensityFrameManifold.productRegularDiffeomorph n)

/-- Every actual Clifford frame representative is realized by the literal positive-density/full-angle/Spin polar formula. -/
theorem productRegularDiffeomorph_mk (n : WithTop ℕ∞)
    (rho : PositiveDensity) (p : FrameDatum) :
    productRegularDiffeomorph n (rho, Quotient.mk frameSetoid p) =
      CliffordSpinPolarRealization.realizeSource (rho, p) := by
  change DensityFrameManifold.productRegularDiffeomorph n
    (rho, frameQuotientHomeomorph (Quotient.mk frameSetoid p)) = _
  rw [frameQuotientHomeomorph_mk, DensityFrameManifold.productRegularDiffeomorph_mk]
  rfl

/-- The smooth actual Clifford density/frame reconstruction retains exactly the earlier natural-topology realization homeomorphism. -/
theorem productRegularDiffeomorph_toHomeomorph (n : WithTop ℕ∞) :
    (productRegularDiffeomorph n).toHomeomorph = productRegularHomeomorph := by
  apply Homeomorph.ext
  rintro ⟨rho, q⟩
  induction q using Quotient.inductionOn with | h p =>
    exact (productRegularDiffeomorph_mk n rho p).trans (productRegularHomeomorph_mk rho p).symm

/-- On each real angle representative, smooth quotient reconstruction is the source polar spinor with the literal universal Clifford Dirac representation. -/
theorem productRegularDiffeomorph_mk_real (n : WithTop ℕ∞)
    (rho : PositiveDensity) (beta : ℝ) (s : CliffordSpinMap.Spin) :
    (productRegularDiffeomorph n
      (rho, Quotient.mk frameSetoid ((beta : ChiralAngleCircle.Angle), s))).val =
      PolarSpinorBilinears.polarSpinor rho beta (CliffordMinkowski.dirac s.val) := by
  rw [productRegularDiffeomorph_mk]
  exact CliffordSpinPolarRealization.realizeSource_coe rho beta s

/-- The actual invariant bilinear density of the reconstructed spinor is precisely its positive-density product coordinate. -/
theorem density_productRegularDiffeomorph (n : WithTop ℕ∞) (p : Product) :
    SpinorRegularity.invariantDensity (productRegularDiffeomorph n p).val = (p.1 : ℝ) := by
  rcases p with ⟨rho, q⟩
  induction q using Quotient.inductionOn with | h p =>
    rw [productRegularDiffeomorph_mk]
    exact CliffordSpinPolarRealization.density_realizeSource (rho, p)

/-- Inverse actual Clifford polar reconstruction recovers the invariant scalar-pseudoscalar density, with no Hilbert-norm substitution. -/
theorem productRegularDiffeomorph_symm_density (n : WithTop ℕ∞) (q : RegularSpinor) :
    (((productRegularDiffeomorph n).symm q).1 : ℝ) =
      SpinorRegularity.invariantDensity q.val := by
  rw [← density_productRegularDiffeomorph n ((productRegularDiffeomorph n).symm q),
    (productRegularDiffeomorph n).apply_symm_apply]

/-- The actual full source quotient is Hausdorff in its existing coinduced topology through the independently proved natural density splitting. -/
instance instT2SpaceSourceQuotient : T2Space SourceQuotient :=
  densityProductHomeomorph.isEmbedding.t2Space

/-- The actual full source quotient is second countable in its existing coinduced topology through the independent density/frame product. -/
instance instSecondCountableTopologySourceQuotient : SecondCountableTopology SourceQuotient :=
  densityProductHomeomorph.secondCountableTopology

/-- The full actual source sign quotient carries the pullback of the independently specified density/frame product atlas through its proved natural density splitting. -/
instance instChartedSpaceSourceQuotient : ChartedSpace ChartModel SourceQuotient where
  atlas := {e | ∃ e' ∈ atlas ChartModel Product,
    e = densityProductHomeomorph.transOpenPartialHomeomorph e'}
  chartAt q := densityProductHomeomorph.transOpenPartialHomeomorph
    (chartAt ChartModel (densityProductHomeomorph q))
  mem_chart_source q := mem_chart_source ChartModel (densityProductHomeomorph q)
  chart_mem_atlas q := ⟨_, chart_mem_atlas ChartModel (densityProductHomeomorph q), rfl⟩

/-- Every preferred actual source quotient chart is exactly its density splitting followed by the corresponding independent product chart. -/
theorem chartAt_sourceQuotient_eq (q : SourceQuotient) :
    chartAt ChartModel q = densityProductHomeomorph.transOpenPartialHomeomorph
      (chartAt ChartModel (densityProductHomeomorph q)) := rfl

/-- The full actual Clifford source sign quotient is a real manifold to every order because its chart transitions are the established product transitions. -/
instance instIsManifoldSourceQuotient (n : WithTop ℕ∞) : IsManifold model n SourceQuotient where
  compatible := by
    rintro e e' ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    rw [Homeomorph.transOpenPartialHomeomorph_symm_trans]
    exact (contDiffGroupoid n model).compatible ha hb

/-- The independently defined natural density splitting is smooth for the actual source-quotient and product atlases. -/
theorem contMDiff_densityProductHomeomorph (n : WithTop ℕ∞) :
    ContMDiff model model n densityProductHomeomorph := by
  intro q
  have hh := (contMDiff_id (I := model) (n := n) :
    ContMDiff model model n (fun p : Product => p)) (densityProductHomeomorph q)
  rw [contMDiffAt_iff] at hh ⊢
  refine ⟨densityProductHomeomorph.continuous.continuousAt, ?_⟩
  convert hh.2 using 1
  all_goals simp [chartAt_sourceQuotient_eq, Function.comp_def]
  all_goals rfl

/-- The natural inverse density splitting is smooth into the full actual Clifford source quotient on its existing coinduced topology. -/
theorem contMDiff_densityProductHomeomorph_symm (n : WithTop ℕ∞) :
    ContMDiff model model n densityProductHomeomorph.symm := by
  intro p
  have hh := (contMDiff_id (I := model) (n := n) :
    ContMDiff model model n (fun q : Product => q)) p
  rw [contMDiffAt_iff] at hh ⊢
  refine ⟨densityProductHomeomorph.symm.continuous.continuousAt, ?_⟩
  convert hh.2 using 1
  all_goals simp [chartAt_sourceQuotient_eq, Function.comp_def]
  all_goals rfl

/-- The genuine natural full-source density splitting is a diffeomorphism to the independently charted positive-density/Clifford-frame product. -/
def densityProductDiffeomorph (n : WithTop ℕ∞) :
    Diffeomorph model model SourceQuotient Product n where
  toEquiv := densityProductHomeomorph.toEquiv
  contMDiff_toFun := contMDiff_densityProductHomeomorph n
  contMDiff_invFun := contMDiff_densityProductHomeomorph_symm n

/-- The actual smooth density splitting retains its original natural homeomorphism exactly. -/
theorem densityProductDiffeomorph_toHomeomorph (n : WithTop ℕ∞) :
    (densityProductDiffeomorph n).toHomeomorph = densityProductHomeomorph := rfl

/-- The actual smooth density splitting extracts exactly the original positive density and genuine Clifford frame sign class. -/
theorem densityProductDiffeomorph_mk (n : WithTop ℕ∞) (d : SourceDatum) :
    densityProductDiffeomorph n (Quotient.mk sourceSetoid d) =
      (d.1, Quotient.mk frameSetoid d.2) := densityProductHomeomorph_mk d

/-- The full actual Clifford source quotient and strict regular spinors are diffeomorphic by genuine density splitting followed by actual polar realization. -/
def regularDiffeomorph (n : WithTop ℕ∞) :
    Diffeomorph model 𝓘(ℝ, Spinor) SourceQuotient RegularSpinor n :=
  (densityProductDiffeomorph n).trans (productRegularDiffeomorph n)

/-- Each full actual source class is realized by precisely its literal density, four-pi angle, and universal Clifford Spin formula. -/
theorem regularDiffeomorph_mk (n : WithTop ℕ∞) (d : SourceDatum) :
    regularDiffeomorph n (Quotient.mk sourceSetoid d) =
      CliffordSpinPolarRealization.realizeSource d := by
  change productRegularDiffeomorph n (densityProductDiffeomorph n (Quotient.mk sourceSetoid d)) = _
  rw [densityProductDiffeomorph_mk, productRegularDiffeomorph_mk]

/-- Smooth full-source reconstruction retains exactly the independently proved natural regular-spinor homeomorphism. -/
theorem regularDiffeomorph_toHomeomorph (n : WithTop ℕ∞) :
    (regularDiffeomorph n).toHomeomorph = regularHomeomorph := by
  apply Homeomorph.ext
  intro q
  induction q using Quotient.inductionOn with | h d =>
    exact (regularDiffeomorph_mk n d).trans (regularHomeomorph_mk d).symm

/-- The actual source-to-density/frame projection is a local diffeomorphism using the independent genuine Clifford frame quotient projection. -/
theorem splitCoordinates_isLocalDiffeomorph (n : WithTop ℕ∞) :
    IsLocalDiffeomorph sourceModel model n splitCoordinates :=
  SmoothLocalDescent.isLocalDiffeomorph_id_prodMap
    (CliffordSpinPolarManifold.quotient_mk_isLocalDiffeomorph n)

/-- The original actual Clifford source sign projection is a local diffeomorphism for its intrinsic product source and independently specified quotient atlas. -/
theorem quotient_mk_isLocalDiffeomorph (n : WithTop ℕ∞) :
    IsLocalDiffeomorph sourceModel model n
      (Quotient.mk sourceSetoid : SourceDatum → SourceQuotient) := by
  have heq : (densityProductDiffeomorph n).symm ∘ splitCoordinates =
      (Quotient.mk sourceSetoid : SourceDatum → SourceQuotient) := by
    funext d
    change densityProductHomeomorph.symm (d.1, Quotient.mk frameSetoid d.2) = _
    rw [← densityProductHomeomorph_mk d]
    exact densityProductHomeomorph.symm_apply_apply _
  intro d
  have h := (splitCoordinates_isLocalDiffeomorph n d).comp model SourceQuotient
    ((densityProductDiffeomorph n).symm.isLocalDiffeomorph (splitCoordinates d))
  rw [heq] at h
  exact h

/-- The actual full-source sign projection is smooth for the genuine Clifford product and quotient atlases to every order. -/
theorem contMDiff_quotient_mk (n : WithTop ℕ∞) :
    ContMDiff sourceModel model n (Quotient.mk sourceSetoid : SourceDatum → SourceQuotient) :=
  (quotient_mk_isLocalDiffeomorph n).contMDiff

/-- The natural actual full-source sign projection is a genuine covering map through its exact regular-spinor realization. -/
theorem quotient_mk_isCoveringMap :
    IsCoveringMap (Quotient.mk sourceSetoid : SourceDatum → SourceQuotient) := by
  have heq : regularHomeomorph.symm ∘ CliffordSpinPolarRealization.realizeSource =
      (Quotient.mk sourceSetoid : SourceDatum → SourceQuotient) := by
    funext d
    rw [Function.comp_apply, ← regularHomeomorph_mk d]
    exact regularHomeomorph.symm_apply_apply _
  rw [← heq]
  exact CliffordSpinPolarCovering.realizeSource_isCoveringMap.homeomorph_comp regularHomeomorph.symm

/-- Every actual source sign-quotient fiber is equivalent to Fin 2 through the genuine regular-spinor reconstruction. -/
def quotientFiberEquiv (q : SourceQuotient) :
    ((Quotient.mk sourceSetoid : SourceDatum → SourceQuotient) ⁻¹' {q}) ≃ Fin 2 :=
  (Equiv.subtypeEquivRight (fun d => show
    Quotient.mk sourceSetoid d = q ↔
      CliffordSpinPolarRealization.realizeSource d = regularHomeomorph q from
    (regularHomeomorph.injective.eq_iff.symm.trans (by rw [regularHomeomorph_mk])))).trans
      (CliffordSpinPolarCovering.realizeFiberEquiv (regularHomeomorph q))

/-- Each actual full-source sign class has exactly two genuine Clifford source representatives. -/
theorem quotient_fiber_card (q : SourceQuotient) :
    Nat.card ((Quotient.mk sourceSetoid : SourceDatum → SourceQuotient) ⁻¹' {q}) = 2 := by
  simpa using Nat.card_congr (quotientFiberEquiv q)

/-- The actual full-source sign projection is a natural two-sheet covering and all-order local diffeomorphism with exactly two representatives in every fiber. -/
theorem quotient_mk_smooth_two_sheeted (n : WithTop ℕ∞) :
    IsCoveringMap (Quotient.mk sourceSetoid : SourceDatum → SourceQuotient) ∧
      IsLocalDiffeomorph sourceModel model n (Quotient.mk sourceSetoid : SourceDatum → SourceQuotient) ∧
      ∀ q : SourceQuotient,
        Nat.card ((Quotient.mk sourceSetoid : SourceDatum → SourceQuotient) ⁻¹' {q}) = 2 :=
  ⟨quotient_mk_isCoveringMap, quotient_mk_isLocalDiffeomorph n, quotient_fiber_card⟩

end FoliationQM.CliffordSpinPolarReconstruction
