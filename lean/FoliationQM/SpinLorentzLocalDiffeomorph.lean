module
public import FoliationQM.SpinLorentzCayleyDerivative
public import FoliationQM.SpinLorentzCovering
public import FoliationQM.SpinLorentzPolarCompatibility
public import FoliationQM.LorentzGroupManifold
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
import all Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Genuine smooth local inverses of the Spin–Lorentz map

Source scope: the concrete Spin/Lorentz frame map in v13
`prop:takabayasi` and `eq:tetrad_rotor_map`. The proper future Lorentz
manifold has its independently constructed matrix Cayley atlas. The
existing actual topological local inverse is conjugated by genuine
source and target charts. Its inverse regularity is derived from the
explicit invertible real Jacobian and the analytic inverse theorem.
An analytic neighborhood supplies one open domain for every requested
smoothness order. Actual group translations then give local
diffeomorphisms everywhere. No inverse smoothness follows merely from
the covering, and no simply-connectedness assertion is made.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Operator Manifold
open Set Topology
namespace FoliationQM.SpinLorentzLocalDiffeomorph
open SourcePolarDatum LorentzMatrixGroup SpinLorentzOrientation
open SpinLorentzCayleyLinear

/-- The actual special-linear Lorentz homomorphism is smooth for the independent Lorentz Cayley atlas. -/
theorem properFutureHom_contMDiff (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℝ, SourceModel) LorentzManifold.model n properFutureHom := by
  apply LorentzManifold.contMDiff_iff_value.mpr
  exact (SpinLorentzPolarCompatibility.contDiff_lorentzMatrix n).contMDiff.comp
    (SpecialLinearManifold.contMDiff_value n)

/-- The existing actual topological inverse is anchored at the identity special-linear lift. -/
def identityLocalInverse : OpenPartialHomeomorph ProperFutureLorentz SpecialLinearMatrix :=
  SpinLorentzCovering.localInverseAt 1

/-- Its total inverse function is exactly the actual Lorentz homomorphism. -/
theorem identityLocalInverse_symm :
    (identityLocalInverse.symm : SpecialLinearMatrix → ProperFutureLorentz) = properFutureHom :=
  SpinLorentzCovering.properFutureHom_isLocalHomeomorph.localInverseAt_symm 1

/-- The identity Lorentz element belongs to the actual local inverse domain. -/
theorem one_mem_identityLocalInverse_source : (1 : ProperFutureLorentz) ∈ identityLocalInverse.source := by
  simpa only [map_one, identityLocalInverse] using SpinLorentzCovering.image_mem_localInverseAt_source 1

/-- The actual local inverse returns identity at identity. -/
theorem identityLocalInverse_one : identityLocalInverse (1 : ProperFutureLorentz) = 1 := by
  simpa only [map_one, identityLocalInverse] using SpinLorentzCovering.localInverseAt_image 1

private theorem one_mem_identityLocalInverse_target :
    (1 : SpecialLinearMatrix) ∈ identityLocalInverse.target := by
  have h := identityLocalInverse.map_source one_mem_identityLocalInverse_source
  simpa only [identityLocalInverse_one] using h

private theorem chartA_one : SpecialLinearCharts.chartA (1 : SpecialLinearMatrix) = basePoint := by
  ext i
  fin_cases i <;>
    simp [SpecialLinearCharts.chartA_apply, SpecialLinearCharts.coordinatesA,
      SpecialLinearCharts.coordinatesACLM_apply, basePoint]

private theorem one_mem_chartA_source : (1 : SpecialLinearMatrix) ∈ SpecialLinearCharts.chartA.source := by
  change (1 : SpinorMatrix.Mat2) 0 0 ≠ 0
  simp

private theorem chartA_symm_basePoint : SpecialLinearCharts.chartA.symm basePoint = 1 := by
  rw [← chartA_one]
  exact SpecialLinearCharts.chartA.left_inv one_mem_chartA_source

private def euclidean : OpenPartialHomeomorph SourceModel TargetModel :=
  (SpecialLinearCharts.chartA.symm.trans identityLocalInverse.symm).trans
    (LorentzCayleyCharts.chart 1)

private theorem euclidean_apply (z : SourceModel) : euclidean z =
    LorentzCayleyCharts.chart 1 (properFutureHom (SpecialLinearCharts.chartA.symm z)) := by
  change LorentzCayleyCharts.chart 1
    (identityLocalInverse.symm (SpecialLinearCharts.chartA.symm z)) = _
  rw [identityLocalInverse_symm]

private theorem euclidean_basePoint : euclidean basePoint = 0 := by
  rw [euclidean_apply, chartA_symm_basePoint, map_one, LorentzCayleyCharts.chart_self]

private theorem basePoint_mem_euclidean_source : basePoint ∈ euclidean.source := by
  change (basePoint ∈ SpecialLinearCharts.chartA.target ∧
    SpecialLinearCharts.chartA.symm basePoint ∈ identityLocalInverse.target) ∧
    identityLocalInverse.symm (SpecialLinearCharts.chartA.symm basePoint) ∈
      (LorentzCayleyCharts.chart 1).source
  rw [chartA_symm_basePoint, identityLocalInverse_symm, map_one]
  exact ⟨⟨basePoint_zero_ne, one_mem_identityLocalInverse_target⟩,
    LorentzCayleyCharts.mem_chart_source 1⟩

private theorem zero_mem_euclidean_target : (0 : TargetModel) ∈ euclidean.target := by
  simpa only [euclidean_basePoint] using euclidean.map_source basePoint_mem_euclidean_source

private theorem euclidean_symm_zero : euclidean.symm (0 : TargetModel) = basePoint := by
  rw [← euclidean_basePoint]
  exact euclidean.left_inv basePoint_mem_euclidean_source

private theorem euclidean_eventuallyEq_ambient :
    (euclidean : SourceModel → TargetModel) =ᶠ[𝓝 basePoint]
      (fun z => LorentzCayleyCoordinates.coordinatesOf
        (LorentzCayleyAlgebra.inverseCayley
          (SpinLorentzAction.lorentzMatrix (SpecialLinearCharts.matrixA z)))) := by
  have hp : ∀ᶠ z : SourceModel in 𝓝 basePoint, z 0 ≠ 0 :=
    (isOpen_ne_fun (continuous_apply 0) continuous_const).mem_nhds basePoint_zero_ne
  filter_upwards [hp] with z hz
  rw [euclidean_apply, LorentzCayleyCharts.chart_apply]
  change LorentzCayleyCoordinates.coordinatesOf
    (LorentzCayleyAlgebra.inverseCayley
      (matrix ((1 : ProperFutureLorentz)⁻¹).val *
        matrix (properFutureHom (SpecialLinearCharts.chartA.symm z)).val)) = _
  rw [inv_one]
  change LorentzCayleyCoordinates.coordinatesOf
    (LorentzCayleyAlgebra.inverseCayley
      ((1 : Mat4) * matrix (properFutureHom (SpecialLinearCharts.chartA.symm z)).val)) = _
  rw [one_mul, properFutureHom_matrix, SpecialLinearCharts.chartA_symm_val hz]

private theorem identityLocalInverse_smooth_of_derivative
    (hd : HasFDerivAt euclidean jacobian.toContinuousLinearMap basePoint)
    (hs : ContDiffAt ℝ (⊤ : WithTop ℕ∞) euclidean basePoint) :
    ContMDiffAt LorentzManifold.model 𝓘(ℝ, SourceModel) ⊤ identityLocalInverse 1 := by
  have hi : ContDiffAt ℝ (⊤ : WithTop ℕ∞) euclidean.symm (0 : TargetModel) := by
    apply euclidean.contDiffAt_symm (f₀' := jacobian) zero_mem_euclidean_target
    · simpa only [euclidean_symm_zero] using hd
    · simpa only [euclidean_symm_zero] using hs
  have ha : chartAt SourceModel (1 : SpecialLinearMatrix) = SpecialLinearCharts.chartA :=
    SpecialLinearManifold.chartAt_eq_chartA 1 (by simp)
  have ht : identityLocalInverse 1 ∈ (chartAt SourceModel (1 : SpecialLinearMatrix)).source := by
    rw [identityLocalInverse_one, ha]
    exact one_mem_chartA_source
  apply (contMDiffAt_iff_of_mem_source
    (show (1 : ProperFutureLorentz) ∈
      (chartAt TargetModel (1 : ProperFutureLorentz)).source from
      LorentzCayleyCharts.mem_chart_source 1) ht).mpr
  refine ⟨identityLocalInverse.continuousOn.continuousAt
    (identityLocalInverse.open_source.mem_nhds one_mem_identityLocalInverse_source), ?_⟩
  have he : (euclidean.symm : TargetModel → SourceModel) =
      SpecialLinearCharts.chartA ∘ identityLocalInverse ∘ (LorentzCayleyCharts.chart 1).symm := rfl
  rw [he] at hi
  simpa only [mfld_simps, LorentzManifold.chartAt_eq_chart, ha,
    LorentzCayleyCharts.chart_self, contDiffWithinAt_univ] using hi

private theorem isLocalDiffeomorphAt_one_of_smooth
    (hi : ContMDiffAt LorentzManifold.model 𝓘(ℝ, SourceModel) ⊤ identityLocalInverse 1)
    (n : WithTop ℕ∞) :
    IsLocalDiffeomorphAt 𝓘(ℝ, SourceModel) LorentzManifold.model n properFutureHom 1 := by
  obtain ⟨u, hu, hsu⟩ := (contMDiffAt_iff_contMDiffOn_nhds (by simp)).mp hi
  obtain ⟨v, hvu, hv, h1v⟩ := mem_nhds_iff.mp hu
  let e := identityLocalInverse.restrOpen v hv
  have h1s : (1 : ProperFutureLorentz) ∈ e.source :=
    ⟨one_mem_identityLocalInverse_source, h1v⟩
  have h1t : (1 : SpecialLinearMatrix) ∈ e.target := by
    have h := e.map_source h1s
    simpa only [e, OpenPartialHomeomorph.coe_restrOpen, identityLocalInverse_one] using h
  have he : (e.symm : SpecialLinearMatrix → ProperFutureLorentz) = properFutureHom :=
    identityLocalInverse_symm
  let p : PartialDiffeomorph 𝓘(ℝ, SourceModel) LorentzManifold.model
      SpecialLinearMatrix ProperFutureLorentz n := {
    toPartialEquiv := e.symm.toPartialEquiv
    open_source := e.open_target
    open_target := e.open_source
    contMDiffOn_toFun := by
      change ContMDiffOn 𝓘(ℝ, SourceModel) LorentzManifold.model n e.symm e.target
      rw [he]
      exact (properFutureHom_contMDiff n).contMDiffOn
    contMDiffOn_invFun := by
      change ContMDiffOn LorentzManifold.model 𝓘(ℝ, SourceModel) n identityLocalInverse
        (identityLocalInverse.source ∩ v)
      exact (hsu.of_le le_top).mono (fun _ hy => hvu hy.2) }
  have hp := p.isLocalDiffeomorphAt 𝓘(ℝ, SourceModel) LorentzManifold.model n h1t
  change IsLocalDiffeomorphAt 𝓘(ℝ, SourceModel) LorentzManifold.model n e.symm 1 at hp
  rw [he] at hp
  exact hp

private theorem global_of_identity (n : WithTop ℕ∞)
    (h1 : IsLocalDiffeomorphAt 𝓘(ℝ, SourceModel) LorentzManifold.model n properFutureHom 1) :
    IsLocalDiffeomorph 𝓘(ℝ, SourceModel) LorentzManifold.model n properFutureHom := by
  intro A
  let a := SpecialLinearGroupManifold.leftMulDiffeomorph n A⁻¹
  let b := LorentzGroupManifold.leftMulDiffeomorph n (properFutureHom A)
  have h1' : IsLocalDiffeomorphAt 𝓘(ℝ, SourceModel) LorentzManifold.model n properFutureHom (a A) := by
    simpa only [a, SpecialLinearGroupManifold.leftMulDiffeomorph_apply, inv_mul_cancel] using h1
  have h := ((a.isLocalDiffeomorph A).comp LorentzManifold.model ProperFutureLorentz h1').comp
    LorentzManifold.model ProperFutureLorentz (b.isLocalDiffeomorph (properFutureHom (a A)))
  have he : (b ∘ properFutureHom ∘ a : SpecialLinearMatrix → ProperFutureLorentz) = properFutureHom := by
    funext B
    simp [a, b, Function.comp_def, map_mul, map_inv, ← mul_assoc]
  convert h using 1
  exact he.symm

/-- The actual topological inverse at identity is analytic in the two independently constructed atlases, by the proved invertible physical Cayley Jacobian. -/
theorem identityLocalInverse_contMDiffAt_analytic :
    ContMDiffAt LorentzManifold.model 𝓘(ℝ, SourceModel) ⊤ identityLocalInverse 1 := by
  have he : (euclidean : SourceModel → TargetModel) =ᶠ[𝓝 basePoint]
      SpinLorentzCayleyDerivative.F := euclidean_eventuallyEq_ambient
  exact identityLocalInverse_smooth_of_derivative
    (SpinLorentzCayleyDerivative.hasFDerivAt_F.congr_of_eventuallyEq he)
    ((SpinLorentzCayleyDerivative.contDiffAt_F ⊤).congr_of_eventuallyEq he)

/-- The actual identity local inverse is smooth to every requested order at identity, as a consequence of its proved analytic regularity. -/
theorem identityLocalInverse_contMDiffAt (n : WithTop ℕ∞) :
    ContMDiffAt LorentzManifold.model 𝓘(ℝ, SourceModel) n identityLocalInverse 1 :=
  identityLocalInverse_contMDiffAt_analytic.of_le le_top

/-- The actual inverse has one genuine open analytic neighborhood contained in its original topological inverse domain. -/
theorem exists_identityLocalInverse_analytic_neighborhood :
    ∃ U : Set ProperFutureLorentz, IsOpen U ∧ (1 : ProperFutureLorentz) ∈ U ∧
      U ⊆ identityLocalInverse.source ∧
      ContMDiffOn LorentzManifold.model 𝓘(ℝ, SourceModel) ⊤ identityLocalInverse U := by
  obtain ⟨u, hu, hsu⟩ := (contMDiffAt_iff_contMDiffOn_nhds (by simp)).mp
    identityLocalInverse_contMDiffAt_analytic
  obtain ⟨v, hvu, hv, h1v⟩ := mem_nhds_iff.mp hu
  exact ⟨identityLocalInverse.source ∩ v, identityLocalInverse.open_source.inter hv,
    ⟨one_mem_identityLocalInverse_source, h1v⟩, inter_subset_left,
    hsu.mono (fun _ hy => hvu hy.2)⟩

/-- The actual special-linear Lorentz homomorphism is a local diffeomorphism at identity, with inverse smoothness derived from its actual Jacobian. -/
theorem properFutureHom_isLocalDiffeomorphAt_one (n : WithTop ℕ∞) :
    IsLocalDiffeomorphAt 𝓘(ℝ, SourceModel) LorentzManifold.model n properFutureHom 1 :=
  isLocalDiffeomorphAt_one_of_smooth identityLocalInverse_contMDiffAt_analytic n

/-- Actual group translations extend the proved identity local diffeomorphism to every special-linear matrix, in the independently constructed Lorentz manifold. -/
theorem properFutureHom_isLocalDiffeomorph (n : WithTop ℕ∞) :
    IsLocalDiffeomorph 𝓘(ℝ, SourceModel) LorentzManifold.model n properFutureHom :=
  global_of_identity n (properFutureHom_isLocalDiffeomorphAt_one n)

end FoliationQM.SpinLorentzLocalDiffeomorph
