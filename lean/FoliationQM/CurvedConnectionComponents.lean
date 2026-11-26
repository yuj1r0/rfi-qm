module

public import FoliationQM.CurvedScalarAtlasOverlap
public import FoliationQM.CurvedFluxRegularity
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear

/-!
# Vector and component descriptions of chart curvature

The bilinear connection on constant coordinate vector fields is determined by
the coordinate Christoffel symbols. Differentiating this connection gives the
Riemann tensor with the derivative slots and sign convention of v13.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
namespace FoliationQM.CurvedConnectionComponents

open LorentzMatrixGroup CurvedScalarAtlasOverlap RNCCoordinateConnection RNCCoordinateCurvature
  ContinuousLinearMap

/-- The Koszul connection as a curried continuous bilinear map in the vector slots. -/
def connectionBilin (g : Covector → Mat4) (x : Covector) :
    Covector →L[ℝ] Covector →L[ℝ] Covector := by
  apply LinearMap.toContinuousBilinearMap
  apply LinearMap.mk₂ ℝ (connection g x)
  all_goals
    intros
    ext r
    simp only [Pi.add_apply, Pi.smul_apply, connection_components, smul_eq_mul,
      add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  all_goals apply Finset.sum_congr rfl; intros; apply Finset.sum_congr rfl; intros; ring

/-- The bundled form evaluates to the original coordinate connection. -/
theorem connectionBilin_apply (g : Covector → Mat4) (x u v : Covector) :
    connectionBilin g x u v = connection g x u v := rfl

private theorem expand {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : Covector →L[ℝ] F) (u : Covector) : L u = ∑ a, u a • L (axis a) := by
  calc
    _ = L (∑ a, u a • axis a) := congrArg L (pi_eq_sum_univ' u)
    _ = _ := by simp

/-- The connection of arbitrary vectors is the finite expansion of its Christoffel components. -/
theorem connection_expansion (g : Covector → Mat4) (x u v : Covector) :
    connection g x u v = ∑ a, ∑ b, (u a * v b) • (fun r => christoffel g x r a b) := by
  ext r
  simp only [connection_components, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]

variable {g : Covector → Mat4} {x : Covector}

/-- A C² metric gives a C¹ field of actual bilinear chart connections at an invertible point. -/
theorem contDiffAt_connectionBilin (hg : ContDiffAt ℝ 2 g x) (hu : IsUnit (g x)) :
    ContDiffAt ℝ 1 (connectionBilin g) x := by
  rw [← contDiffWithinAt_univ, contDiffWithinAt_clm_apply]
  intro u
  rw [contDiffWithinAt_clm_apply]
  intro v
  rw [contDiffWithinAt_univ]
  simp only [connectionBilin_apply, connection_expansion]
  exact ContDiffAt.sum fun a _ => ContDiffAt.sum fun b _ => (contDiffAt_const (c := u a * v b)).smul
    (contDiffAt_pi.mpr fun r => contDiffAt_christoffel hg hu r a b)

/-- Curvature of constant vector fields, acting on `u` in the two directions `v,w`. -/
def curvature (g : Covector → Mat4) (x u v w : Covector) : Covector :=
  fderiv ℝ (fun y => connection g y w u) x v - fderiv ℝ (fun y => connection g y v u) x w +
    connection g x v (connection g x w u) - connection g x w (connection g x v u)

/-- Differentiating a fixed pair of vector slots evaluates the derivative of the bilinear connection. -/
theorem connection_derivative (hg : ContDiffAt ℝ 2 g x) (hu : IsUnit (g x)) (u v w : Covector) :
    fderiv ℝ (fun y => connection g y u v) x w =
      fderiv ℝ (connectionBilin g) x w u v := by
  let L := (apply ℝ Covector v).comp (apply ℝ (Covector →L[ℝ] Covector) u)
  exact congrArg (fun T : Covector →L[ℝ] Covector => T w)
    (L.hasFDerivAt.comp x (contDiffAt_connectionBilin hg hu).differentiableAt_one.hasFDerivAt).fderiv

/-- Coordinate basis slots reproduce the Riemann components of the metric with the v13 sign. -/
theorem curvature_axis (hg : ContDiffAt ℝ 2 g x) (hu : IsUnit (g x)) (s a b r : Fin 4) :
    curvature g x (axis s) (axis a) (axis b) r = riemann g x r s a b := by
  have hd (j k l : Fin 4) : fderiv ℝ (fun y => connection g y (axis j) (axis k)) x (axis l) r =
      dGamma g x r j k l := by
    let P : Covector →L[ℝ] ℝ := proj r
    have hc := ((contDiffAt_connectionBilin hg hu).clm_apply
      (contDiffAt_const (c := axis j))).clm_apply (contDiffAt_const (c := axis k))
    have he : (fun y => christoffel g y r j k) =
        P ∘ (fun y => connectionBilin g y (axis j) (axis k)) := funext fun y => (connection_axis g y j k r).symm
    rw [dGamma, he]
    exact (congrArg (fun T : Covector →L[ℝ] ℝ => T (axis l))
      (P.hasFDerivAt.comp x hc.differentiableAt_one.hasFDerivAt).fderiv).symm
  have ha (i : Fin 4) (v : Covector) : connection g x (axis i) v r =
      ∑ l, v l * christoffel g x r i l := by
    change (proj r : Covector →L[ℝ] ℝ) (connectionBilin g x (axis i) v) = _
    rw [expand (connectionBilin g x (axis i)) v, map_sum]
    apply Finset.sum_congr rfl
    intro l _
    exact congrArg (v l * ·) (connection_axis g x i l r)
  simp only [curvature, Pi.sub_apply, Pi.add_apply, hd, ha, connection_axis, riemann, Finset.sum_sub_distrib]
  simp only [mul_comm (christoffel g x _ _ s)]
  abel

private theorem expandLinear (f : Covector → Covector) (u : Covector)
    (ha : ∀ v w, f (v + w) = f v + f w) (hs : ∀ (t : ℝ) v, f (t • v) = t • f v) :
    f u = ∑ a, u a • f (axis a) :=
  expand (({toFun := f, map_add' := ha, map_smul' := hs} :
    Covector →ₗ[ℝ] Covector).toContinuousLinearMap) u

/-- Expansion of the full vector-valued curvature in all three tensor arguments.
The indices `s,a,b` are respectively the transported vector and the two curvature directions. -/
theorem curvature_expansion (hg : ContDiffAt ℝ 2 g x) (hu : IsUnit (g x)) (u v w : Covector) :
    curvature g x u v w = ∑ s, ∑ a, ∑ b, ((u s * v a) * w b) •
      (fun r => riemann g x r s a b) := by
  let C := connectionBilin g x
  let T := fderiv ℝ (connectionBilin g) x
  let R (p q z : Covector) := T q z p - T z q p + C q (C z p) - C z (C q p)
  have he (p q z) : curvature g x p q z = R p q z := by
    simp only [curvature, connection_derivative hg hu]
    rfl
  have h₁ (p q z) : R p q z = ∑ s, p s • R (axis s) q z := by
    apply expandLinear (fun p => R p q z) p
    · intros; simp only [R, map_add]; abel
    · intros; simp only [R, map_smul, smul_add, smul_sub]
  have h₂ (p q z) : R p q z = ∑ a, q a • R p (axis a) z := by
    apply expandLinear (fun q => R p q z) q
    · intros; simp only [R, map_add, add_apply]; abel
    · intros; simp only [R, map_smul, smul_apply, smul_add, smul_sub]
  have h₃ (p q z) : R p q z = ∑ b, z b • R p q (axis b) := by
    apply expandLinear (fun z => R p q z) z
    · intros; simp only [R, map_add, add_apply]; abel
    · intros; simp only [R, map_smul, smul_apply, smul_add, smul_sub]
  have hb (s a b : Fin 4) : R (axis s) (axis a) (axis b) = fun r => riemann g x r s a b :=
    funext fun r => (congrFun (he (axis s) (axis a) (axis b)).symm r).trans
      (curvature_axis hg hu s a b r)
  rw [he, h₁ u v w]
  simp only [fun s => h₂ (axis s) v w, fun s a => h₃ (axis s) (axis a) w, hb,
    Finset.smul_sum, smul_smul, mul_assoc]

end FoliationQM.CurvedConnectionComponents
