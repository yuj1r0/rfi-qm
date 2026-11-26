module
public import FoliationQM.SpinLorentzSurjective
public import FoliationQM.SpinLorentzQuotient
public import FoliationQM.RegularSpinorAction

/-!
# Compatibility of the actual Lorentz identification with polar frame quotients

Source scope: the concrete frame and sign-gluing claims in v13
`prop:takabayasi` and `eq:tetrad_rotor_map`. Forgetting the chiral angle
projects the existing angle-matrix sign quotient to the actual matrix
sign quotient. Its proved Lorentz homeomorphism gives the same physical
Lorentz matrix on every representative, independently of density or
angle. These are projections; no identification of the seven-dimensional
angle-matrix quotient with the six-dimensional Lorentz group is asserted.

The projections commute with the existing source-quotient realization,
regular-spinor reconstruction, and actual matrix/Dirac actions. Their
continuity uses the unchanged quotient topologies. Actual ambient real
Lorentz matrix entries are manifold-smooth to every order, using the
proved polynomial frame map and genuine smooth quotient descent.
No Lorentz target atlas is introduced, no global individual representative
is selected, and no abstract Clifford-spin or spacetime spin-bundle
identification or differentiated field-equation covariance is inferred.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Operator Manifold
open Topology
namespace FoliationQM.SpinLorentzPolarCompatibility
open SourcePolarDatum SourcePolarProductQuotient LorentzMatrixGroup
open SpinLorentzAction SpinLorentzOrientation SpinLorentzKernel SpinLorentzSignQuotient

/-- Forgetting the angle sends a frame sign class to the actual matrix sign quotient. -/
def frameSignProjection : FrameQuotient → SignQuotient :=
  Quotient.lift (fun p : FrameDatum => projection p.2) (by
    intro p q h
    rcases h with h | h
    · rw [h]
    · rw [h]
      have he : (frameShift q).2 = negativeOne * q.2 := by
        apply Subtype.ext
        simp only [negativeOne_mul_val]
        rfl
      rw [he, projection_negativeOne_mul])

/-- The actual frame-to-matrix-sign projection evaluates to the original matrix's sign class. -/
theorem frameSignProjection_mk (p : FrameDatum) :
    frameSignProjection (Quotient.mk frameSetoid p) = projection p.2 := rfl

/-- Forgetting the angle is continuous in the already established natural quotient topologies. -/
theorem continuous_frameSignProjection : Continuous frameSignProjection :=
  (continuous_projection.comp continuous_snd).quotient_lift _

/-- Every matrix sign class is obtained by forgetting the angle of an actual frame class. -/
theorem frameSignProjection_surjective : Function.Surjective frameSignProjection := by
  intro q
  obtain ⟨A, rfl⟩ := projection_surjective q
  exact ⟨Quotient.mk frameSetoid (0, A), rfl⟩

/-- The proper future Lorentz transformation of an actual polar frame sign class. -/
def frameLorentz (q : FrameQuotient) : ProperFutureLorentz :=
  quotientHom (frameSignProjection q)

/-- On an actual angle-matrix representative, the frame projection is precisely the physical Lorentz homomorphism of its matrix. -/
theorem frameLorentz_mk (p : FrameDatum) :
    frameLorentz (Quotient.mk frameSetoid p) = properFutureHom p.2 := rfl

/-- The actual Lorentz matrix of a representative is the established physical signed-transpose frame matrix. -/
theorem frameLorentz_matrix_mk (p : FrameDatum) :
    matrix (frameLorentz (Quotient.mk frameSetoid p)).val = lorentzMatrix p.2.val := rfl

/-- The actual Lorentz frame depends continuously on its polar frame class. -/
theorem continuous_frameLorentz : Continuous frameLorentz :=
  continuous_quotientHom.comp continuous_frameSignProjection

/-- Every independently proper future Lorentz transformation is realized by some actual polar frame class. -/
theorem frameLorentz_surjective : Function.Surjective frameLorentz := by
  intro L
  obtain ⟨A, hA⟩ := SpinLorentzSurjective.properFutureHom_surjective L
  exact ⟨Quotient.mk frameSetoid (0,A), hA⟩

/-- Forgetting the angle intertwines the existing matrix frame action with multiplication in the actual sign quotient. -/
theorem frameSignProjection_action (g : SpecialLinearMatrix) (q : FrameQuotient) :
    frameSignProjection (DensityFrameAction.frameAction g q) =
      projection g * frameSignProjection q := by
  induction q using Quotient.inductionOn with
  | h p => exact projection.map_mul g p.2

/-- The existing polar frame action projects to the correct ordered physical Lorentz action. -/
theorem frameLorentz_action (g : SpecialLinearMatrix) (q : FrameQuotient) :
    frameLorentz (DensityFrameAction.frameAction g q) = properFutureHom g * frameLorentz q := by
  simp only [frameLorentz, frameSignProjection_action, map_mul, quotientHom_projection]

/-- The actual density-frame Lorentz projection factors through its existing frame-class component. -/
def productLorentz (p : DensityFrameManifold.Product) : ProperFutureLorentz := frameLorentz p.2

/-- The density-frame Lorentz projection is continuous in its established product topology. -/
theorem continuous_productLorentz : Continuous productLorentz :=
  continuous_frameLorentz.comp continuous_snd

/-- Its representative formula is independent of the supplied positive density and chiral angle. -/
theorem productLorentz_mk (rho : PolarAmplitudeTopology.PositiveDensity) (p : FrameDatum) :
    productLorentz (rho, Quotient.mk frameSetoid p) = properFutureHom p.2 := rfl

/-- The literal source polar sign quotient has a well-defined actual Lorentz projection through its existing density splitting. -/
def sourceLorentz (q : SourcePolarQuotient.SourceQuotient) : ProperFutureLorentz :=
  productLorentz (densityProductHomeomorph q)

/-- The source-quotient Lorentz projection retains exactly the representative's physical matrix homomorphism. -/
theorem sourceLorentz_mk (d : SourceDatum) :
    sourceLorentz (Quotient.mk SourcePolarQuotient.signSetoid d) = properFutureHom d.2.2 := rfl

/-- The source-quotient Lorentz projection is continuous in its existing natural topology. -/
theorem continuous_sourceLorentz : Continuous sourceLorentz :=
  continuous_productLorentz.comp densityProductHomeomorph.continuous

/-- A strict regular spinor has an actual Lorentz frame obtained from its already proved unique reconstructed frame class. -/
def regularLorentz (q : PolarSignQuotient.RegularSpinor) : ProperFutureLorentz :=
  frameLorentz (DensityFrameFields.frameClass q)

/-- The regular-spinor Lorentz frame is continuous through the actual reconstructed class, without a global individual spin representative. -/
theorem continuous_regularLorentz : Continuous regularLorentz :=
  continuous_frameLorentz.comp (continuous_snd.comp productRegularHomeomorph.symm.continuous)

/-- Realizing any density-frame datum gives exactly its Lorentz projection. -/
theorem regularLorentz_product (p : DensityFrameManifold.Product) :
    regularLorentz (productRegularHomeomorph p) = productLorentz p := by
  change frameLorentz (productRegularHomeomorph.symm (productRegularHomeomorph p)).2 = _
  rw [Homeomorph.symm_apply_apply]
  rfl

/-- Every literal polar representative realizes a regular spinor with its exact actual Lorentz transformation. -/
theorem regularLorentz_realizeSource (d : SourceDatum) :
    regularLorentz (SourcePolarRealization.realizeSource d) = properFutureHom d.2.2 := by
  rw [← productRegularHomeomorph_mk d.1 d.2, regularLorentz_product, productLorentz_mk]

/-- The new physical Lorentz projection commutes with the existing source-quotient regular-spinor realization. -/
theorem regularLorentz_sourceQuotient (q : SourcePolarQuotient.SourceQuotient) :
    regularLorentz (SourcePolarQuotient.regularHomeomorph q) = sourceLorentz q := by
  induction q using Quotient.inductionOn with
  | h d => exact regularLorentz_realizeSource d

/-- Direct Dirac spinor action transforms the recovered actual Lorentz frame by the same ordered physical homomorphism. -/
theorem regularLorentz_action (g : SpecialLinearMatrix) (q : PolarSignQuotient.RegularSpinor) :
    regularLorentz (RegularSpinorAction.act g q) = properFutureHom g * regularLorentz q := by
  simp only [regularLorentz, RegularSpinorAction.frameClass_act, frameLorentz_action]

/-- The actual physical sign-transpose conversion is a real continuous-linear map from row frames to real Lorentz matrices. -/
def physicalFrameCLM : (Fin 4 → Covector) →L[ℝ] LorentzMatrixGroup.Mat4 :=
  LinearMap.toContinuousLinearMap {
    toFun F := fun i j => RealLorentzFrame.sign i * RealLorentzFrame.sign j * F j i
    map_add' := by
      intro F G
      ext i j
      simp only [Pi.add_apply, Matrix.add_apply]
      ring
    map_smul' := by
      intro r F
      ext i j
      simp only [Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]
      ring }

/-- The continuous-linear physical conversion gives precisely the previously established physical Lorentz matrix on every matrix input. -/
theorem physicalFrameCLM_frame (A : SpinorMatrix.Mat2) :
    physicalFrameCLM (SpecialLinearFrame.frame A) = lorentzMatrix A := by
  ext i j
  exact (lorentzMatrix_apply A i j).symm

/-- The physical real matrix map is smooth on the entire complex matrix space, independently of determinant-one restriction. -/
theorem contDiff_lorentzMatrix (n : WithTop ℕ∞) :
    ContDiff ℝ n lorentzMatrix := by
  have h := physicalFrameCLM.contDiff.comp (SpecialLinearFrameSmooth.contDiff_frame n)
  simpa only [Function.comp_def, physicalFrameCLM_frame] using h

/-- Actual physical Lorentz matrix entries descend smoothly through the independently constructed polar frame quotient atlas. -/
theorem contMDiff_frameLorentz_matrix (n : WithTop ℕ∞) :
    ContMDiff FrameQuotientManifold.model 𝓘(ℝ, LorentzMatrixGroup.Mat4) n
      (fun q => matrix (frameLorentz q).val) := by
  apply (SmoothLocalDescent.contMDiff_comp_iff
    (FrameQuotientManifold.quotient_mk_isLocalDiffeomorph n) Quotient.mk_surjective).mp
  exact (contDiff_lorentzMatrix n).contMDiff.comp
    ((SpecialLinearManifold.contMDiff_value n).comp contMDiff_snd)

/-- The actual reconstructed proper Lorentz matrix is smooth on the existing strict regular-spinor manifold to every order. -/
theorem contMDiff_regularLorentz_matrix (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℝ, DiracMatrices.Spinor) 𝓘(ℝ, LorentzMatrixGroup.Mat4) n
      (fun q => matrix (regularLorentz q).val) :=
  (contMDiff_frameLorentz_matrix n).comp (DensityFrameFields.contMDiff_frameClass n)

/-- The actual polar-frame Lorentz projection factors through the proved topological group identification of the matrix sign quotient. -/
theorem frameLorentz_eq_quotientHomeomorph (q : FrameQuotient) :
    frameLorentz q = SpinLorentzQuotient.quotientHomeomorph (frameSignProjection q) := rfl

/-- The inverse Lorentz homeomorphism recovers precisely the matrix sign class of the original polar frame, without choosing an individual matrix. -/
theorem inverse_frameLorentz (q : FrameQuotient) :
    SpinLorentzQuotient.quotientHomeomorph.symm (frameLorentz q) = frameSignProjection q :=
  SpinLorentzQuotient.quotientHomeomorph.symm_apply_apply (frameSignProjection q)

/-- Two actual frame representatives have the same Lorentz projection exactly when their matrices differ by a sign; their chiral angles remain independent forgotten data. -/
theorem frameLorentz_mk_eq_iff (p q : FrameDatum) :
    frameLorentz (Quotient.mk frameSetoid p) = frameLorentz (Quotient.mk frameSetoid q) ↔
      p.2 = q.2 ∨ p.2 = negativeOne * q.2 := properFutureHom_eq_iff p.2 q.2

end FoliationQM.SpinLorentzPolarCompatibility
