module

public import FoliationQM.SpacelikeSliceGeometry
public import FoliationQM.CurvedCoordinateCurrent
public import FoliationQM.GeometricLorentzNormalization
public import FoliationQM.CurvedNormalizedQuantumForce

/-!
# Future normal geometry and the actual physical current density

An actual future Lorentz frame, compatible with coordinate time, identifies
the computed unit slice normal as future. Its pairing with every actual
future timelike current is positive. The current used below is literally
amplitude squared times the phase velocity. The induced spatial Gram volume
then identifies its normal flux with the coordinate continuity density.
These are pointwise statements; total flux and measure normalization are
separate constructions.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GeometricCurrentFlux

open Matrix LorentzMatrixGroup GeometricLorentzFrame GeometricLorentzFrameRecognition
  GeometricLorentzNormalization SpacelikeSliceGeometry

section Frame

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
  {B : LinearMap.BilinForm ℝ V} {orientation : Orientation ℝ V (Fin 4)}
  {future : Set V}

/-- Two vectors in the supplied actual future timelike cone have strictly positive metric pairing. -/
theorem metric_pos_of_mem_future (e : Frame B orientation future) {u v : V}
    (hu : u ∈ future) (hv : v ∈ future) : 0 < B u v := by
  have hu' := (mem_future_iff_coordinates e u).mp hu
  have hv' := (mem_future_iff_coordinates e v).mp hv
  have hm := metric_coordinates e (e.basis.equivFun u) (e.basis.equivFun v)
  simp only [LinearEquiv.symm_apply_apply] at hm
  rw [hm]
  exact LorentzFutureCone.minkowski_pos_of_future hu'.1 hu'.2 hv'.1 hv'.2

end Frame

section Normal

variable {G : Mat4} {orientation : Orientation ℝ Covector (Fin 4)} {future : Set Covector}

/-- The supplied actual Lorentz frame derives symmetry of the coordinate metric matrix. -/
theorem matrix_isSymm (e : Frame G.toBilin' orientation future) : G.IsSymm :=
  Matrix.isSymm_toBilin'_iff_isSymm.mp (metric_symm e)

/-- Coordinate coorientation identifies the actual computed unit slice normal with the selected future cone. -/
theorem normal_mem_future (e : Frame G.toBilin' orientation future)
    (htime : 0 < (e.basis 0) 0) (hd : G.det < 0) (hsp : (spatialGram G).PosDef) :
    normalVector G ∈ future := by
  have hs : 0 < Real.sqrt ((G⁻¹) 0 0) := Real.sqrt_pos.mpr (inverse_time_pos hd hsp)
  have hp : 0 < G.toBilin' (e.basis 0) (normalVector G) := by
    rw [normal_lowering (isUnit_iff_ne_zero.mpr hd.ne)]
    exact div_pos htime hs
  have ht : 0 < (e.basis.equivFun (normalVector G)) 0 := by
    rw [metric_basis_left e (normalVector G) 0] at hp
    simpa [RealLorentzFrame.sign, Module.Basis.equivFun_apply] using hp
  have hm := metric_coordinates e
    (e.basis.equivFun (normalVector G)) (e.basis.equivFun (normalVector G))
  simp only [LinearEquiv.symm_apply_apply, normal_unit hd hsp] at hm
  apply (mem_future_iff_coordinates e (normalVector G)).mpr
  exact ⟨ht, by rw [← hm]; exact zero_lt_one⟩

/-- Symmetry and actual lowering identify the vector-normal pairing with its normalized covector contraction. -/
theorem normal_pairing_eq (e : Frame G.toBilin' orientation future)
    (hd : G.det < 0) (J : Covector) :
    G.toBilin' (normalVector G) J = normalCovector G ⬝ᵥ J := by
  rw [(metric_symm e).eq (normalVector G) J,
    normal_lowering (isUnit_iff_ne_zero.mpr hd.ne), normal_pairing]

/-- A future current has strictly positive pairing with the actual future unit slice normal. -/
theorem normal_pairing_pos (e : Frame G.toBilin' orientation future)
    (htime : 0 < (e.basis 0) 0) (hd : G.det < 0) (hsp : (spatialGram G).PosDef)
    {J : Covector} (hJ : J ∈ future) : 0 < G.toBilin' (normalVector G) J :=
  metric_pos_of_mem_future e (normal_mem_future e htime hd hsp) hJ

/-- The actual normalized normal covector has positive contraction with each future current. -/
theorem normal_covector_pairing_pos (e : Frame G.toBilin' orientation future)
    (htime : 0 < (e.basis 0) 0) (hd : G.det < 0) (hsp : (spatialGram G).PosDef)
    {J : Covector} (hJ : J ∈ future) : 0 < normalCovector G ⬝ᵥ J := by
  rw [← normal_pairing_eq e hd J]
  exact normal_pairing_pos e htime hd hsp hJ

/-- Future membership implies positive coordinate time only after the actual frame coorientation is supplied. -/
theorem time_pos_of_mem_future (e : Frame G.toBilin' orientation future)
    (htime : 0 < (e.basis 0) 0) (hd : G.det < 0) (hsp : (spatialGram G).PosDef)
    {J : Covector} (hJ : J ∈ future) : 0 < J 0 := by
  have hp := normal_covector_pairing_pos e htime hd hsp hJ
  rw [normal_pairing] at hp
  exact (div_pos_iff_of_pos_right (Real.sqrt_pos.mpr (inverse_time_pos hd hsp))).mp hp

/-- The actual normal current flux is positive for a positive speed scale. -/
theorem normal_flux_pos (e : Frame G.toBilin' orientation future)
    (htime : 0 < (e.basis 0) 0) (hd : G.det < 0) (hsp : (spatialGram G).PosDef)
    {c : ℝ} (hc : 0 < c) {J : Covector} (hJ : J ∈ future) :
    0 < (normalCovector G ⬝ᵥ J) / c :=
  div_pos (normal_covector_pairing_pos e htime hd hsp hJ) hc

/-- Positive actual normal flux remains positive after multiplication by the induced spatial Gram volume. -/
theorem geometric_flux_density_pos (e : Frame G.toBilin' orientation future)
    (htime : 0 < (e.basis 0) 0) (hd : G.det < 0) (hsp : (spatialGram G).PosDef)
    {c : ℝ} (hc : 0 < c) {J : Covector} (hJ : J ∈ future) :
    0 < ((normalCovector G ⬝ᵥ J) / c) * sliceVolumeFactor G :=
  mul_pos (normal_flux_pos e htime hd hsp hc hJ) (slice_volume_pos hsp)

end Normal

section Physical

/-- The physical current is the actual amplitude square times the actual raised phase velocity. -/
def physicalCurrent (p : MassiveParameters) (g : Covector → Mat4) (R S : Covector → ℝ)
    (x : Covector) : Covector :=
  R x ^ 2 • CurvedQuantumVelocity.velocity p g S x

variable {p : MassiveParameters} {g : Covector → Mat4} {R S : Covector → ℝ}
  {x : Covector} {orientation : Orientation ℝ Covector (Fin 4)} {future : Set Covector}

/-- Positive amplitude and the actual future phase velocity give a future physical current. -/
theorem physicalCurrent_mem_future (e : Frame (g x).toBilin' orientation future)
    (hR : 0 < R x) (hw : CurvedQuantumVelocity.velocity p g S x ∈ future) :
    physicalCurrent p g R S x ∈ future :=
  (mem_future_smul_iff e (sq_pos_of_pos hR) _).mpr hw

/-- Positive normalization transfers actual future membership from the normalized velocity to the physical current. -/
theorem physicalCurrent_mem_future_of_normalized
    (e : Frame (g x).toBilin' orientation future) (hR : 0 < R x)
    (hq : 0 < 1 + CurvedPolarKG.defect p g R x)
    (hU : CurvedNormalizedQuantumForce.normalizedVelocity p g R S x ∈ future) :
    physicalCurrent p g R S x ∈ future :=
  physicalCurrent_mem_future e hR
    ((CurvedNormalizedQuantumForce.future_iff p g R S x e hq).mp hU)

/-- The actual Gram-volume normal flux of the physical current equals the coordinate continuity density. -/
theorem physical_flux_density_eq (p : MassiveParameters) (g : Covector → Mat4)
    (R S : Covector → ℝ) (q : ℝ × (Fin 3 → ℝ))
    (hd : (g (CurvedCoordinateCurrent.eventMap p.c q)).det < 0)
    (hsp : (spatialGram (g (CurvedCoordinateCurrent.eventMap p.c q))).PosDef) :
    let x := CurvedCoordinateCurrent.eventMap p.c q
    ((normalCovector (g x) ⬝ᵥ physicalCurrent p g R S x) / p.c) *
      sliceVolumeFactor (g x) = CurvedCoordinateCurrent.density p g R S q := by
  dsimp only
  rw [flux_density_eq p.c _ _ hd hsp, CurvedCoordinateCurrent.density_eq]
  simp only [physicalCurrent, Pi.smul_apply, smul_eq_mul]
  ring

/-- Actual future current geometry makes the literal physical coordinate density strictly positive. -/
theorem physical_density_pos (q : ℝ × (Fin 3 → ℝ))
    (e : Frame (g (CurvedCoordinateCurrent.eventMap p.c q)).toBilin' orientation future)
    (htime : 0 < (e.basis 0) 0)
    (hd : (g (CurvedCoordinateCurrent.eventMap p.c q)).det < 0)
    (hsp : (spatialGram (g (CurvedCoordinateCurrent.eventMap p.c q))).PosDef)
    (hR : 0 < R (CurvedCoordinateCurrent.eventMap p.c q))
    (hw : CurvedQuantumVelocity.velocity p g S (CurvedCoordinateCurrent.eventMap p.c q) ∈ future) :
    0 < CurvedCoordinateCurrent.density p g R S q := by
  rw [← physical_flux_density_eq p g R S q hd hsp]
  exact geometric_flux_density_pos e htime hd hsp p.c_pos
    (physicalCurrent_mem_future e hR hw)

/-- A future normalized physical velocity gives positive coordinate density through the genuine positive normalization. -/
theorem physical_density_pos_of_normalized (q : ℝ × (Fin 3 → ℝ))
    (e : Frame (g (CurvedCoordinateCurrent.eventMap p.c q)).toBilin' orientation future)
    (htime : 0 < (e.basis 0) 0)
    (hd : (g (CurvedCoordinateCurrent.eventMap p.c q)).det < 0)
    (hsp : (spatialGram (g (CurvedCoordinateCurrent.eventMap p.c q))).PosDef)
    (hR : 0 < R (CurvedCoordinateCurrent.eventMap p.c q))
    (hq : 0 < 1 + CurvedPolarKG.defect p g R (CurvedCoordinateCurrent.eventMap p.c q))
    (hU : CurvedNormalizedQuantumForce.normalizedVelocity p g R S
      (CurvedCoordinateCurrent.eventMap p.c q) ∈ future) :
    0 < CurvedCoordinateCurrent.density p g R S q :=
  physical_density_pos q e htime hd hsp hR
    ((CurvedNormalizedQuantumForce.future_iff p g R S _ e hq).mp hU)

end Physical
end FoliationQM.GeometricCurrentFlux
