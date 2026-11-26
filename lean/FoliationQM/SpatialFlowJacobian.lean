module

public import FoliationQM.SpatialFlowDifferential
public import FoliationQM.RNCDeterminantDifferential
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Actual spatial flow Jacobians and Liouville evolution

The spatial Jacobian is the coordinate matrix of the actual spatial flow
differential. Its evolution follows from the differentiated time equation.
A differentiable local inverse gives a nonzero determinant independently of
Liouville's formula. The actual initial identity germ gives determinant one;
closed-interval continuity and the intermediate value theorem then preserve
positive orientation. The dimension is arbitrary, including zero.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.SpatialFlowJacobian

open Matrix Set Filter SpatialFlowDifferential
open scoped Topology Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

/-- The actual coordinate matrix of a continuous linear spatial map. -/
def coordinateMatrix (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) : Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toMatrix' L.toLinearMap

/-- Taking the coordinate matrix is itself an actual continuous linear map. -/
def coordinateMatrixMap : ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) →L[ℝ]
    Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun := coordinateMatrix
    map_add' := by intro A B; ext i j; rfl
    map_smul' := by intro r A; ext i j; rfl }

/-- The actual spatial flow Jacobian is the coordinate matrix of its restricted joint derivative. -/
def spatialJacobian (Φ : ℝ × (Fin n → ℝ) → (Fin n → ℝ))
    (p : ℝ × (Fin n → ℝ)) : Matrix (Fin n) (Fin n) ℝ :=
  coordinateMatrix (spatialDifferential Φ p)

/-- The spatial flow determinant is the determinant of its actual derivative matrix. -/
def spatialJacobianDet (Φ : ℝ × (Fin n → ℝ) → (Fin n → ℝ))
    (p : ℝ × (Fin n → ℝ)) : ℝ :=
  (spatialJacobian Φ p).det

/-- Each matrix column is the actual differential applied to its coordinate basis vector. -/
theorem coordinateMatrix_apply (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (i j : Fin n) :
    coordinateMatrix L i j = L (Pi.single j 1) i := rfl

/-- The continuous linear matrix assignment has exactly the declared coordinate entries. -/
theorem coordinateMatrixMap_apply (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
    coordinateMatrixMap L = coordinateMatrix L := rfl

/-- Composition of actual spatial differentials gives matrix multiplication in the same order. -/
theorem coordinateMatrix_comp (A B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
    coordinateMatrix (A.comp B) = coordinateMatrix A * coordinateMatrix B :=
  LinearMap.toMatrix'_comp A.toLinearMap B.toLinearMap

/-- The actual identity differential has the identity matrix. -/
theorem coordinateMatrix_id :
    coordinateMatrix (ContinuousLinearMap.id ℝ (Fin n → ℝ)) = 1 :=
  LinearMap.toMatrix'_id

/-- The coordinate matrix acts exactly as the original continuous linear map. -/
theorem coordinateMatrix_mulVec (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (v : Fin n → ℝ) :
    (coordinateMatrix L).mulVec v = L v :=
  LinearMap.toMatrix'_mulVec L.toLinearMap v

/-- The trace is the actual sum of the coordinate directional derivatives. -/
theorem trace_coordinateMatrix (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
    (coordinateMatrix L).trace = ∑ i, L (Pi.single i 1) i := rfl

variable {Φ : ℝ × (Fin n → ℝ) → (Fin n → ℝ)} {b : ℝ → (Fin n → ℝ) → (Fin n → ℝ)}
  {t : ℝ} {a : Fin n → ℝ} {ψ : (Fin n → ℝ) → (Fin n → ℝ)}

/-- The coordinate determinant equals the linear-map determinant of the actual spatial slice derivative. -/
theorem spatialJacobianDet_eq_linearMap_det (hΦ : DifferentiableAt ℝ Φ (t, a)) :
    spatialJacobianDet Φ (t, a) =
      LinearMap.det (fderiv ℝ (fun z => Φ (t, z)) a).toLinearMap := by
  rw [spatialJacobianDet, spatialJacobian, spatialDifferential_eq_fderiv hΦ,
    coordinateMatrix, LinearMap.det_toMatrix']

/-- The actual time equation on a label neighborhood gives the genuine spatial matrix Jacobi equation. -/
theorem hasDerivAt_spatialJacobian (hΦ : ContDiffAt ℝ 2 Φ (t, a))
    (hb : DifferentiableAt ℝ (b t) (Φ (t, a)))
    (hODE : ∀ᶠ z in 𝓝 a, HasDerivAt (fun τ => Φ (τ, z)) (b t (Φ (t, z))) t) :
    HasDerivAt (fun τ => spatialJacobian Φ (τ, a))
      (coordinateMatrix (fderiv ℝ (b t) (Φ (t, a))) * spatialJacobian Φ (t, a)) t := by
  have h := coordinateMatrixMap.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_spatialDifferential hΦ hb hODE)
  simpa only [Function.comp_def, coordinateMatrixMap_apply, coordinateMatrix_comp, spatialJacobian] using! h

/-- Differentiating a genuine local left inverse proves that the actual spatial determinant is a unit. -/
theorem isUnit_det_of_local_left_inverse (hΦ : DifferentiableAt ℝ Φ (t, a))
    (hψ : DifferentiableAt ℝ ψ (Φ (t, a)))
    (hleft : (fun z => ψ (Φ (t, z))) =ᶠ[𝓝 a] id) :
    IsUnit (spatialJacobianDet Φ (t, a)) := by
  have h := congrArg coordinateMatrix (derivative_left_inverse hΦ hψ hleft)
  rw [coordinateMatrix_comp, coordinateMatrix_id] at h
  exact Matrix.isUnit_det_of_left_inverse h

/-- Actual matrix evolution and independently established invertibility give Liouville's determinant derivative. -/
theorem hasDerivAt_spatialJacobianDet_of_isUnit (hΦ : ContDiffAt ℝ 2 Φ (t, a))
    (hb : DifferentiableAt ℝ (b t) (Φ (t, a)))
    (hODE : ∀ᶠ z in 𝓝 a, HasDerivAt (fun τ => Φ (τ, z)) (b t (Φ (t, z))) t)
    (hunit : IsUnit (spatialJacobianDet Φ (t, a))) :
    HasDerivAt (fun τ => spatialJacobianDet Φ (τ, a))
      (spatialJacobianDet Φ (t, a) *
        (coordinateMatrix (fderiv ℝ (b t) (Φ (t, a)))).trace) t := by
  have hm := hasDerivAt_spatialJacobian hΦ hb hODE
  have hdet : DifferentiableAt ℝ (Matrix.det : Matrix (Fin n) (Fin n) ℝ → ℝ)
      (spatialJacobian Φ (t, a)) :=
    (RNCDeterminantDifferential.contDiff_det (Fin n) 1).contDiffAt.differentiableAt_one
  have hd := hdet.hasFDerivAt.comp_hasDerivAt t hm
  have ht : ((spatialJacobian Φ (t, a))⁻¹ *
      (coordinateMatrix (fderiv ℝ (b t) (Φ (t, a))) * spatialJacobian Φ (t, a))).trace =
      (coordinateMatrix (fderiv ℝ (b t) (Φ (t, a)))).trace := by
    rw [Matrix.trace_mul_comm, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hunit, Matrix.mul_one]
  rw [RNCDeterminantDifferential.fderiv_det_apply _ _ hunit, ht] at hd
  exact hd

/-- A genuine differentiable local inverse supplies the invertibility needed for the actual Liouville equation. -/
theorem hasDerivAt_spatialJacobianDet (hΦ : ContDiffAt ℝ 2 Φ (t, a))
    (hb : DifferentiableAt ℝ (b t) (Φ (t, a)))
    (hODE : ∀ᶠ z in 𝓝 a, HasDerivAt (fun τ => Φ (τ, z)) (b t (Φ (t, z))) t)
    (hψ : DifferentiableAt ℝ ψ (Φ (t, a)))
    (hleft : (fun z => ψ (Φ (t, z))) =ᶠ[𝓝 a] id) :
    HasDerivAt (fun τ => spatialJacobianDet Φ (τ, a))
      (spatialJacobianDet Φ (t, a) *
        (coordinateMatrix (fderiv ℝ (b t) (Φ (t, a)))).trace) t :=
  hasDerivAt_spatialJacobianDet_of_isUnit hΦ hb hODE
    (isUnit_det_of_local_left_inverse (hΦ.differentiableAt (by decide)) hψ hleft)

/-- The genuine zero-time identity on a label neighborhood gives the identity spatial Jacobian. -/
theorem spatialJacobian_zero (hΦ : DifferentiableAt ℝ Φ (0, a))
    (hzero : (fun z => Φ (0, z)) =ᶠ[𝓝 a] id) : spatialJacobian Φ (0, a) = 1 := by
  rw [spatialJacobian, spatialDifferential_zero hΦ hzero, coordinateMatrix_id]

/-- The actual initial identity germ gives spatial determinant one. -/
theorem spatialJacobianDet_zero (hΦ : DifferentiableAt ℝ Φ (0, a))
    (hzero : (fun z => Φ (0, z)) =ᶠ[𝓝 a] id) : spatialJacobianDet Φ (0, a) = 1 := by
  rw [spatialJacobianDet, spatialJacobian_zero hΦ hzero, Matrix.det_one]

/-- Joint twice differentiability gives actual time continuity of the spatial determinant, including endpoints. -/
theorem continuousAt_spatialJacobianDet (hΦ : ContDiffAt ℝ 2 Φ (t, a)) :
    ContinuousAt (fun τ => spatialJacobianDet Φ (τ, a)) t := by
  have hm : ContinuousAt (spatialJacobian Φ) (t, a) :=
    coordinateMatrixMap.continuous.continuousAt.comp (contDiffAt_spatialDifferential hΦ).continuousAt
  have hd : ContinuousAt (spatialJacobianDet Φ) (t, a) :=
    (RNCDeterminantDifferential.contDiff_det (Fin n) 1).continuous.continuousAt.comp hm
  have hpath : ContinuousAt (fun τ : ℝ => (τ, a)) t :=
    continuousAt_id.prodMk continuousAt_const
  exact ContinuousAt.comp (f := fun τ : ℝ => (τ, a)) hd hpath

/-- Closed-time local inverse data and the actual initial identity preserve positive spatial orientation. -/
theorem spatialJacobianDet_pos {T : ℝ} (hT : 0 ≤ T)
    (hΦ : ∀ t ∈ Icc 0 T, ContDiffAt ℝ 2 Φ (t, a))
    (hinv : ∀ t ∈ Icc 0 T, ∃ ψ : (Fin n → ℝ) → (Fin n → ℝ),
      DifferentiableAt ℝ ψ (Φ (t, a)) ∧ (fun z => ψ (Φ (t, z))) =ᶠ[𝓝 a] id)
    (hzero : (fun z => Φ (0, z)) =ᶠ[𝓝 a] id) :
    ∀ t ∈ Icc 0 T, 0 < spatialJacobianDet Φ (t, a) := by
  have hn : ∀ s ∈ Icc 0 T, spatialJacobianDet Φ (s, a) ≠ 0 := by
    intro s hs
    obtain ⟨ψ, hψ, hleft⟩ := hinv s hs
    exact (isUnit_det_of_local_left_inverse ((hΦ s hs).differentiableAt (by decide))
      hψ hleft).ne_zero
  have h0 := spatialJacobianDet_zero
    ((hΦ 0 ⟨le_rfl, hT⟩).differentiableAt (by decide)) hzero
  intro t ht
  by_contra hp
  have hnonpos : spatialJacobianDet Φ (t, a) ≤ 0 := le_of_not_gt hp
  have hc : ContinuousOn (fun s => spatialJacobianDet Φ (s, a)) (Icc 0 t) := by
    intro s hs
    exact (continuousAt_spatialJacobianDet (hΦ s ⟨hs.1, hs.2.trans ht.2⟩)).continuousWithinAt
  obtain ⟨s, hs, hz⟩ := intermediate_value_Icc' ht.1 hc
    (show 0 ∈ Icc (spatialJacobianDet Φ (t, a)) (spatialJacobianDet Φ (0, a)) from
      ⟨hnonpos, by rw [h0]; exact zero_le_one⟩)
  exact hn s ⟨hs.1, hs.2.trans ht.2⟩ hz

end FoliationQM.SpatialFlowJacobian
