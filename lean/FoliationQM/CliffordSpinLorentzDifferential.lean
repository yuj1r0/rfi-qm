module
public import FoliationQM.CliffordSpinLorentzSmooth
public import FoliationQM.CliffordSpinSignManifold
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Actual differentials of the genuine Spin–Lorentz covering

Source scope: the actual Spin/Lorentz frame and differential compatibility
in v13 `prop:takabayasi` and `eq:tetrad_rotor_map`. The independently fixed
Spin and Lorentz atlases give genuine manifold derivatives. The proved
smooth covering makes its actual derivative a continuous-linear tangent
equivalence at every point. Its actual local inverse derivatives and
field derivatives satisfy the genuine inverse and chain rules. The
independently constructed sign quotient has an actual projection tangent
equivalence, whose composition with the quotient-to-Lorentz tangent
equivalence is exactly the covering derivative.

Nonzero differentiability order and field differentiability hypotheses
are explicit. Local inverse conclusions retain their genuine open
domains. Ambient matrix identities use the original physical Lorentz
matrix, without selecting a global individual Spin lift or assuming a
derivative identification. No connection-dependent transport, universal
covering, or dynamical covariance statement is asserted.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Operator Manifold
open Set Filter Topology
namespace FoliationQM.CliffordSpinLorentzDifferential
open CliffordSpinMap CliffordSpinLorentz CliffordSpinLorentzSmooth LorentzMatrixGroup

/-- The actual derivative of the genuine Spin covering is a continuous-linear tangent equivalence at each stated nonzero order. -/
def coverTangentEquiv (n : WithTop ℕ∞) (hn : n ≠ 0) (s : Spin) :
    TangentSpace spinModel s ≃L[ℝ] TangentSpace lorentzModel (lorentzHom s) :=
  (lorentzHom_isLocalDiffeomorph n).mfderivToContinuousLinearEquiv hn s

/-- The covering tangent equivalence has exactly the actual manifold derivative of the original Clifford Lorentz homomorphism as its underlying map. -/
theorem coverTangentEquiv_toContinuousLinearMap (n : WithTop ℕ∞) (hn : n ≠ 0) (s : Spin) :
    (coverTangentEquiv n hn s).toContinuousLinearMap =
      mfderiv spinModel lorentzModel lorentzHom s :=
  (lorentzHom_isLocalDiffeomorph n).mfderivToContinuousLinearEquiv_coe hn s

/-- The actual Clifford Lorentz covering derivative is invertible at every genuine Spin point. -/
theorem cover_mfderiv_isInvertible (n : WithTop ℕ∞) (hn : n ≠ 0) (s : Spin) :
    (mfderiv spinModel lorentzModel lorentzHom s).IsInvertible :=
  (lorentzHom_isLocalDiffeomorph n).isInvertible_mfderiv hn s

/-- At the image of its prescribed anchor, the genuine local inverse derivative is the inverse covering tangent equivalence after identifying its recovered endpoint with that anchor. -/
theorem localInverse_mfderiv_image (n : WithTop ℕ∞) (hn : n ≠ 0) (s : Spin) :
    (tangentSpaceCast spinModel (localInverse n s (lorentzHom s)) s).toContinuousLinearMap.comp
      (mfderiv lorentzModel spinModel (localInverse n s) (lorentzHom s)) =
        (coverTangentEquiv n hn s).symm.toContinuousLinearMap := by
  ext v
  rfl

/-- At every point in its true open domain, a smooth local inverse has the inverse covering derivative, with the Lorentz tangent endpoint identified by the proved projection identity. -/
theorem localInverse_mfderiv (n : WithTop ℕ∞) (hn : n ≠ 0) (s : Spin)
    {L : ProperFutureLorentz} (hL : L ∈ (localInverse n s).source) :
    mfderiv lorentzModel spinModel (localInverse n s) L =
      (coverTangentEquiv n hn (localInverse n s L)).symm.toContinuousLinearMap.comp
        (tangentSpaceCast lorentzModel L (lorentzHom (localInverse n s L))).toContinuousLinearMap := by
  have hg : MDifferentiableAt lorentzModel spinModel (localInverse n s) L :=
    ((contMDiffOn_localInverse n s).contMDiffAt
      ((localInverse n s).open_source.mem_nhds hL)).mdifferentiableAt hn
  have hf := (contMDiff_lorentzHom n).mdifferentiable hn (localInverse n s L)
  have he : lorentzHom ∘ localInverse n s =ᶠ[𝓝 L] id := by
    apply Filter.eventuallyEq_of_mem ((localInverse n s).open_source.mem_nhds hL)
    intro K hK
    exact image_localInverse hK
  have hd := he.mfderiv_eq (I := lorentzModel) (I' := lorentzModel)
  rw [mfderiv_comp L hf hg, mfderiv_id] at hd
  ext v
  apply (coverTangentEquiv n hn (localInverse n s L)).injective
  change coverTangentEquiv n hn (localInverse n s L)
      (mfderiv lorentzModel spinModel (localInverse n s) L v) =
    coverTangentEquiv n hn (localInverse n s L)
      ((coverTangentEquiv n hn (localInverse n s L)).symm
        (tangentSpaceCast lorentzModel L (lorentzHom (localInverse n s L)) v))
  rw [ContinuousLinearEquiv.apply_symm_apply]
  change (coverTangentEquiv n hn (localInverse n s L)).toContinuousLinearMap
      (mfderiv lorentzModel spinModel (localInverse n s) L v) =
    tangentSpaceCast lorentzModel L (lorentzHom (localInverse n s L)) v
  rw [coverTangentEquiv_toContinuousLinearMap]
  exact congrArg (fun T => T v) hd

/-- The actual ambient physical matrix derivative is the Lorentz matrix-inclusion derivative composed with the true covering tangent map. -/
theorem physical_matrix_mfderiv (n : WithTop ℕ∞) (hn : n ≠ 0) (s : Spin) :
    mfderiv spinModel 𝓘(ℝ, Mat4)
      (fun t : Spin => SpinLorentzAction.lorentzMatrix (CliffordSpinMap.toMatrix t).val) s =
      (mfderiv lorentzModel 𝓘(ℝ, Mat4) LorentzManifold.value (lorentzHom s)).comp
        (coverTangentEquiv n hn s).toContinuousLinearMap := by
  have he : (fun t : Spin => SpinLorentzAction.lorentzMatrix (CliffordSpinMap.toMatrix t).val) =
      LorentzManifold.value ∘ lorentzHom := by
    funext t
    exact (lorentzHom_matrix t).symm
  rw [he, coverTangentEquiv_toContinuousLinearMap]
  exact mfderiv_comp s ((LorentzManifold.contMDiff_value n).mdifferentiable hn (lorentzHom s))
    ((contMDiff_lorentzHom n).mdifferentiable hn s)

/-- The genuine projection to the independently constructed Spin sign quotient has an actual continuous-linear tangent equivalence. -/
def projectionTangentEquiv (n : WithTop ℕ∞) (hn : n ≠ 0) (s : Spin) :
    TangentSpace spinModel s ≃L[ℝ]
      TangentSpace CliffordSpinSignManifold.model (CliffordSpinSignManifold.projection s) :=
  (CliffordSpinSignManifold.projection_isLocalDiffeomorph n).mfderivToContinuousLinearEquiv hn s

/-- The projection tangent equivalence is exactly the manifold derivative of the original quotient projection. -/
theorem projectionTangentEquiv_toContinuousLinearMap
    (n : WithTop ℕ∞) (hn : n ≠ 0) (s : Spin) :
    (projectionTangentEquiv n hn s).toContinuousLinearMap =
      mfderiv spinModel CliffordSpinSignManifold.model CliffordSpinSignManifold.projection s :=
  (CliffordSpinSignManifold.projection_isLocalDiffeomorph n).mfderivToContinuousLinearEquiv_coe hn s

/-- The independently smooth quotient-to-Lorentz diffeomorphism induces its actual tangent equivalence at every sign class. -/
def quotientTangentEquiv (n : WithTop ℕ∞) (hn : n ≠ 0)
    (q : CliffordSpinCovering.SignQuotient) :
    TangentSpace CliffordSpinSignManifold.model q ≃L[ℝ]
      TangentSpace lorentzModel (CliffordSpinCovering.quotientMulHomeomorph q) :=
  (CliffordSpinSignManifold.quotientDiffeomorph n).mfderivToContinuousLinearEquiv hn q

/-- The quotient tangent equivalence has exactly the original quotient homeomorphism's manifold derivative as its underlying map. -/
theorem quotientTangentEquiv_toContinuousLinearMap
    (n : WithTop ℕ∞) (hn : n ≠ 0) (q : CliffordSpinCovering.SignQuotient) :
    (quotientTangentEquiv n hn q).toContinuousLinearMap =
      mfderiv CliffordSpinSignManifold.model lorentzModel
        CliffordSpinCovering.quotientMulHomeomorph q :=
  (CliffordSpinSignManifold.quotientDiffeomorph n).mfderivToContinuousLinearEquiv_coe hn

/-- The actual sign projection and quotient identification form a commuting tangent square with the genuine Clifford Spin-to-Lorentz covering. -/
theorem quotient_projection_tangent_square (n : WithTop ℕ∞) (hn : n ≠ 0) (s : Spin) :
    (quotientTangentEquiv n hn (CliffordSpinSignManifold.projection s)).toContinuousLinearMap.comp
      (projectionTangentEquiv n hn s).toContinuousLinearMap =
        (coverTangentEquiv n hn s).toContinuousLinearMap := by
  rw [quotientTangentEquiv_toContinuousLinearMap,
    projectionTangentEquiv_toContinuousLinearMap, coverTangentEquiv_toContinuousLinearMap]
  exact (mfderiv_comp s
    ((CliffordSpinSignManifold.contMDiff_quotientMulHomeomorph n).mdifferentiable hn
      (CliffordSpinSignManifold.projection s))
    ((CliffordSpinSignManifold.contMDiff_quotient_mk n).mdifferentiable hn s)).symm

section Fields
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- Every actually differentiable Spin-valued field projects with the genuine covering tangent equivalence and the manifold chain rule. -/
theorem mfderiv_cover_comp (n : WithTop ℕ∞) (hn : n ≠ 0)
    {f : M → Spin} {x : M} (hf : MDifferentiableAt I spinModel f x) :
    mfderiv I lorentzModel (lorentzHom ∘ f) x =
      (coverTangentEquiv n hn (f x)).toContinuousLinearMap.comp
        (mfderiv I spinModel f x) := by
  rw [coverTangentEquiv_toContinuousLinearMap]
  exact mfderiv_comp x ((contMDiff_lorentzHom n).mdifferentiable hn (f x)) hf

/-- An actually differentiable Lorentz field lifted through a genuine local inverse has the recovered derivative given by the inverse covering tangent equivalence. -/
theorem mfderiv_localInverse_comp (n : WithTop ℕ∞) (hn : n ≠ 0) (s : Spin)
    {f : M → ProperFutureLorentz} {x : M} (hf : MDifferentiableAt I lorentzModel f x)
    (hx : f x ∈ (localInverse n s).source) :
    mfderiv I spinModel (localInverse n s ∘ f) x =
      (coverTangentEquiv n hn (localInverse n s (f x))).symm.toContinuousLinearMap.comp
        ((tangentSpaceCast lorentzModel (f x)
          (lorentzHom (localInverse n s (f x)))).toContinuousLinearMap.comp
            (mfderiv I lorentzModel f x)) := by
  have hg : MDifferentiableAt lorentzModel spinModel (localInverse n s) (f x) :=
    ((contMDiffOn_localInverse n s).contMDiffAt
      ((localInverse n s).open_source.mem_nhds hx)).mdifferentiableAt hn
  rw [mfderiv_comp x hg hf, localInverse_mfderiv n hn s hx]
  rfl

/-- Projecting the actual derivative of a locally reconstructed Spin field recovers the original Lorentz field derivative, with equal Lorentz endpoints explicitly identified. -/
theorem cover_localInverse_derivative (n : WithTop ℕ∞) (hn : n ≠ 0) (s : Spin)
    {f : M → ProperFutureLorentz} {x : M} (hf : MDifferentiableAt I lorentzModel f x)
    (hx : f x ∈ (localInverse n s).source) (v : TangentSpace I x) :
    coverTangentEquiv n hn (localInverse n s (f x))
      (mfderiv I spinModel (localInverse n s ∘ f) x v) =
      tangentSpaceCast lorentzModel (f x) (lorentzHom (localInverse n s (f x)))
        (mfderiv I lorentzModel f x v) := by
  rw [mfderiv_localInverse_comp n hn s hf hx]
  exact (coverTangentEquiv n hn (localInverse n s (f x))).apply_symm_apply _

/-- The actual physical matrix of any differentiable Spin field has the derivative obtained by its covering tangent map and the genuine Lorentz matrix inclusion. -/
theorem physical_matrix_mfderiv_comp (n : WithTop ℕ∞) (hn : n ≠ 0)
    {f : M → Spin} {x : M} (hf : MDifferentiableAt I spinModel f x) :
    mfderiv I 𝓘(ℝ, Mat4)
      (fun y => SpinLorentzAction.lorentzMatrix (CliffordSpinMap.toMatrix (f y)).val) x =
      (mfderiv lorentzModel 𝓘(ℝ, Mat4) LorentzManifold.value (lorentzHom (f x))).comp
        ((coverTangentEquiv n hn (f x)).toContinuousLinearMap.comp
          (mfderiv I spinModel f x)) := by
  have he : (fun y => SpinLorentzAction.lorentzMatrix (CliffordSpinMap.toMatrix (f y)).val) =
      LorentzManifold.value ∘ (lorentzHom ∘ f) := by
    funext y
    exact (lorentzHom_matrix (f y)).symm
  rw [he, mfderiv_comp x
    ((LorentzManifold.contMDiff_value n).mdifferentiable hn (lorentzHom (f x)))
    (((contMDiff_lorentzHom n).mdifferentiable hn (f x)).comp x hf),
    mfderiv_cover_comp n hn hf]
  rfl

end Fields
end FoliationQM.CliffordSpinLorentzDifferential
