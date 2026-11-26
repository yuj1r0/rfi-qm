module
public import FoliationQM.CliffordSpinLoopMonodromy
public import FoliationQM.SpinSignLocalCoefficients

/-!
# Monodromy of the actual triangular Lorentz boundary

For the Spin-frame component of v13 `prop:takabayasi`, three paths
from the identity to compatible Lorentz transitions form a closed
boundary by concatenation. Its mod-two homotopy class is computed from
the endpoints of their actual Clifford Spin lifts.
-/

@[expose] public section
noncomputable section
open scoped Topology unitInterval
namespace FoliationQM.LorentzTriangleMonodromy
open CliffordSpinMap CliffordSpinLorentz CliffordSpinCovering LorentzMatrixGroup
open CliffordSpinSignKernel CliffordSpinPathLifting CliffordSpinLoopMonodromy
open LorentzFundamentalGroup SpinSignLocalCoefficients

variable {a b c : ProperFutureLorentz}

/-- The endpoint of the genuine lift of a Lorentz path starting at the identity. -/
def endpoint (p : Path (1 : ProperFutureLorentz) a) : Spin :=
  pathLift p 1 (p.source.trans (map_one lorentzHom).symm) 1

/-- The lifted endpoint projects to the supplied actual Lorentz endpoint. -/
theorem endpoint_projects (p : Path (1 : ProperFutureLorentz) a) : lorentzHom (endpoint p) = a :=
  (congrFun (pathLift_projects p 1 (p.source.trans (map_one lorentzHom).symm)) 1).trans p.target

/-- The actual lifted path, with both of its genuine Spin endpoints retained. -/
def liftedPath (p : Path (1 : ProperFutureLorentz) a) : Path (1 : Spin) (endpoint p) where
  toFun := pathLift p 1 (p.source.trans (map_one lorentzHom).symm)
  continuous_toFun := (pathLift p 1 _).continuous
  source' := pathLift_zero _ _ _
  target' := rfl

/-- Every point of the lifted path projects to the given physical Lorentz path. -/
theorem liftedPath_projects (p : Path (1 : ProperFutureLorentz) a) (t : unitInterval) :
    lorentzHom (liftedPath p t) = p t :=
  congrFun (pathLift_projects p 1 (p.source.trans (map_one lorentzHom).symm)) t

/-- Follow the first transition path, the right translate of the second, and the
reverse of the direct path, producing an actual closed triangular boundary. -/
def triangle (p : Path (1 : ProperFutureLorentz) a) (q : Path (1 : ProperFutureLorentz) b)
    (r : Path (1 : ProperFutureLorentz) c) (h : b * a = c) : Path (1 : ProperFutureLorentz) 1 :=
  (p.trans ((q.mul (Path.refl a)).cast (one_mul a).symm rfl)).trans (r.symm.cast h rfl)

/-- The product of lifted endpoints has its actual membership in the physical sign kernel. -/
def defect (p : Path (1 : ProperFutureLorentz) a) (q : Path (1 : ProperFutureLorentz) b)
    (r : Path (1 : ProperFutureLorentz) c) (h : b * a = c) : Kernel :=
  ⟨endpoint q * endpoint p * (endpoint r)⁻¹, by
    change lorentzHom (endpoint q * endpoint p * (endpoint r)⁻¹) = 1
    rw [map_mul, map_mul, map_inv, endpoint_projects, endpoint_projects, endpoint_projects, h, mul_inv_cancel]⟩

/-- The kernel defect is the ordered ratio of the three actual lifted endpoints. -/
theorem defect_val (p : Path (1 : ProperFutureLorentz) a) (q : Path (1 : ProperFutureLorentz) b)
    (r : Path (1 : ProperFutureLorentz) c) (h : b * a = c) :
    (defect p q r h).val = endpoint q * endpoint p * (endpoint r)⁻¹ := rfl

/-- An explicit Spin path over the three boundary segments, whose final endpoint is the defect. -/
def liftedTriangle (p : Path (1 : ProperFutureLorentz) a) (q : Path (1 : ProperFutureLorentz) b)
    (r : Path (1 : ProperFutureLorentz) c) (h : b * a = c) : Path (1 : Spin) (defect p q r h).val :=
  ((liftedPath p).trans (((liftedPath q).mul (Path.refl (endpoint p))).cast
    (one_mul (endpoint p)).symm rfl)).trans
      (((Path.refl (defect p q r h).val).mul (liftedPath r).symm).cast
        (by rw [defect_val, inv_mul_cancel_right]) (mul_one _).symm)

/-- The explicit lifted triangle projects to each point of the independently defined boundary. -/
theorem liftedTriangle_projects (p : Path (1 : ProperFutureLorentz) a)
    (q : Path (1 : ProperFutureLorentz) b) (r : Path (1 : ProperFutureLorentz) c)
    (h : b * a = c) :
    lorentzHom ∘ liftedTriangle p q r h = triangle p q r h := by
  have hk : lorentzHom (defect p q r h).val = 1 := (defect p q r h).property
  funext t
  simp only [Function.comp_apply, liftedTriangle, triangle, Path.trans_apply]
  split_ifs <;>
    simp only [Path.cast_coe, Path.mul_apply, Path.refl_apply, Path.symm_apply,
      Function.comp_apply, map_mul, liftedPath_projects, endpoint_projects, hk, one_mul]

/-- Path-lift uniqueness identifies the constructed three-segment Spin path with
the genuine anchored lift of the boundary loop. -/
theorem liftLoop_triangle (p : Path (1 : ProperFutureLorentz) a)
    (q : Path (1 : ProperFutureLorentz) b) (r : Path (1 : ProperFutureLorentz) c)
    (h : b * a = c) :
    liftLoop (triangle p q r h) = (liftedTriangle p q r h).toContinuousMap :=
  ((eq_pathLift_iff (triangle p q r h) 1 _ (liftedTriangle p q r h).toContinuousMap).mpr
    ⟨liftedTriangle_projects p q r h, (liftedTriangle p q r h).source⟩).symm

/-- The actual boundary monodromy is precisely its central triple-transition defect. -/
theorem triangle_lift_endpoint (p : Path (1 : ProperFutureLorentz) a)
    (q : Path (1 : ProperFutureLorentz) b) (r : Path (1 : ProperFutureLorentz) c)
    (h : b * a = c) :
    liftLoop (triangle p q r h) 1 = (defect p q r h).val := by
  rw [liftLoop_triangle]
  exact (liftedTriangle p q r h).target

/-- The triangular coefficient is the actual Lorentz fundamental-group class
expressed in the normalized additive group ZMod 2. -/
def coefficient (p : Path (1 : ProperFutureLorentz) a)
    (q : Path (1 : ProperFutureLorentz) b) (r : Path (1 : ProperFutureLorentz) c)
    (h : b * a = c) : ZMod 2 :=
  Multiplicative.toAdd (fundamentalGroupEquiv (loopClass (triangle p q r h)))

/-- The independently defined Lorentz loop coefficient equals the encoded physical defect. -/
theorem coefficient_eq_encode (p : Path (1 : ProperFutureLorentz) a)
    (q : Path (1 : ProperFutureLorentz) b) (r : Path (1 : ProperFutureLorentz) c)
    (h : b * a = c) : coefficient p q r h = encode (defect p q r h) :=
  congrArg Multiplicative.toAdd
    ((fundamentalGroupEquiv_eq_kernel_iff (loopClass (triangle p q r h)) (defect p q r h)).mpr
      (triangle_lift_endpoint p q r h))

/-- Zero triangular coefficient is equivalent to a nullhomotopy of the actual based boundary. -/
theorem coefficient_eq_zero_iff (p : Path (1 : ProperFutureLorentz) a)
    (q : Path (1 : ProperFutureLorentz) b) (r : Path (1 : ProperFutureLorentz) c)
    (h : b * a = c) :
    coefficient p q r h = 0 ↔ (triangle p q r h).Homotopic (Path.refl 1) := by
  change fundamentalGroupEquiv (loopClass (triangle p q r h)) = 1 ↔ _
  rw [fundamentalGroupEquiv.map_eq_one_iff, loopClass_eq_one_iff]

end FoliationQM.LorentzTriangleMonodromy
