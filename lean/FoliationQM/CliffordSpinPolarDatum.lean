module
public import FoliationQM.CliffordSpinManifold
public import FoliationQM.FrameDatumManifold
public import FoliationQM.SourceDatumManifold

/-!
# Literal Clifford Spin polar products and their simultaneous sign

Source scope: the density, four-pi full angle, and actual Spin factor in
v13 `prop:takabayasi` and `eq:takabayasi_polar`. The frame and source
products use the literal generated Clifford Spin group, its canonical
subtype topology and compatible smooth atlas. The ordinary product
manifolds are smoothly identified with the previously constructed
angle-matrix and density-angle-matrix products through the actual Pauli
Spin diffeomorphism. The density and full-angle factors are unchanged.

The simultaneous sign is literally the two-pi angle shift and left
multiplication by the genuine Clifford negative identity. Its matrix
image is the established matrix sign operation, and it is a smooth free
involution. No representative of the four-pi angle quotient or of a
simultaneous sign class is chosen. Quotient atlases, covering results,
and geometric spacetime bundle identification are separate obligations.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Operator Manifold
namespace FoliationQM.CliffordSpinPolarDatum
open CliffordSpinMap CliffordSpinEquivalence CliffordSpinTopology
open ChiralAngleCircle PolarAmplitudeTopology SpinorMatrix

/-- The literal full four-pi angle and actual Clifford Spin product, with its inherited product topology and atlas. -/
abbrev FrameDatum := Angle × Spin

/-- Literal positive density, full four-pi angle, and actual Clifford Spin data in the ordinary product topology and atlas. -/
abbrev SourceDatum := PositiveDensity × FrameDatum

/-- The frame model is the existing one-angle plus six-rotor real model. -/
abbrev frameModel := FrameDatumManifold.model

/-- The source model is the existing one-density, one-angle, and six-rotor real model. -/
abbrev sourceModel := SourceDatumManifold.model

/-- The genuine angle-Spin product is a real manifold to every order for its inherited product atlas. -/
theorem isManifold_frame (n : WithTop ℕ∞) : IsManifold frameModel n FrameDatum := inferInstance

/-- The genuine density-angle-Spin product is a real manifold to every order for its inherited product atlas. -/
theorem isManifold_source (n : WithTop ℕ∞) : IsManifold sourceModel n SourceDatum := inferInstance

/-- The intrinsic actual Spin frame model has real dimension seven. -/
theorem frame_model_finrank : Module.finrank ℝ FrameDatumManifold.Model = 7 :=
  FrameDatumManifold.model_finrank

/-- The intrinsic actual Spin source model has real dimension eight. -/
theorem source_model_finrank : Module.finrank ℝ SourceDatumManifold.Model = 8 :=
  SourceDatumManifold.model_finrank

/-- The ordinary full-angle and actual Spin product is homeomorphic to the existing angle-matrix product through the actual Pauli map. -/
def frameHomeomorph : FrameDatum ≃ₜ SourcePolarProductQuotient.FrameDatum :=
  (Homeomorph.refl Angle).prodCongr spinHomeomorph

/-- The ordinary density-angle-Spin product is homeomorphic to the existing source matrix product, preserving density and full angle. -/
def sourceHomeomorph : SourceDatum ≃ₜ SourcePolarDatum.SourceDatum :=
  (Homeomorph.refl PositiveDensity).prodCongr frameHomeomorph

/-- The actual frame homeomorphism preserves the full angle and applies precisely the Pauli homomorphism to the genuine Spin element. -/
theorem frameHomeomorph_apply (p : FrameDatum) :
    frameHomeomorph p = (p.1, CliffordSpinMap.toMatrix p.2) := rfl

/-- The inverse frame homeomorphism preserves the full angle and uses the proved actual Clifford inverse identification. -/
theorem frameHomeomorph_symm_apply (p : SourcePolarProductQuotient.FrameDatum) :
    frameHomeomorph.symm p = (p.1, spinEquiv.symm p.2) := rfl

/-- The actual source homeomorphism preserves density and full angle and applies precisely the Pauli Spin homomorphism. -/
theorem sourceHomeomorph_apply (d : SourceDatum) :
    sourceHomeomorph d = (d.1, d.2.1, CliffordSpinMap.toMatrix d.2.2) := rfl

/-- The inverse source homeomorphism preserves density and full angle and recovers the actual Clifford Spin element. -/
theorem sourceHomeomorph_symm_apply (d : SourcePolarDatum.SourceDatum) :
    sourceHomeomorph.symm d = (d.1, d.2.1, spinEquiv.symm d.2.2) := rfl

/-- The product of the full-angle identity with the genuine Spin diffeomorphism identifies the actual Spin and matrix frame manifolds. -/
def frameDiffeomorph (n : WithTop ℕ∞) :
    Diffeomorph frameModel FrameDatumManifold.model
      FrameDatum SourcePolarProductQuotient.FrameDatum n :=
  (Diffeomorph.refl (𝓡 1) Angle n).prodCongr (CliffordSpinManifold.spinDiffeomorph n)

/-- The product of the density identity with the actual frame diffeomorphism identifies the genuine Spin and matrix source manifolds. -/
def sourceDiffeomorph (n : WithTop ℕ∞) :
    Diffeomorph sourceModel SourceDatumManifold.model
      SourceDatum SourcePolarDatum.SourceDatum n :=
  (Diffeomorph.refl 𝓘(ℝ, ℝ) PositiveDensity n).prodCongr (frameDiffeomorph n)

/-- The actual frame diffeomorphism evaluates to the unchanged natural product homeomorphism. -/
theorem frameDiffeomorph_apply (n : WithTop ℕ∞) (p : FrameDatum) :
    frameDiffeomorph n p = frameHomeomorph p := rfl

/-- The actual frame diffeomorphism retains the natural product homeomorphism exactly. -/
theorem frameDiffeomorph_toHomeomorph (n : WithTop ℕ∞) :
    (frameDiffeomorph n).toHomeomorph = frameHomeomorph := rfl

/-- The actual source diffeomorphism evaluates to the unchanged natural product homeomorphism. -/
theorem sourceDiffeomorph_apply (n : WithTop ℕ∞) (d : SourceDatum) :
    sourceDiffeomorph n d = sourceHomeomorph d := rfl

/-- The actual source diffeomorphism retains the natural product homeomorphism exactly. -/
theorem sourceDiffeomorph_toHomeomorph (n : WithTop ℕ∞) :
    (sourceDiffeomorph n).toHomeomorph = sourceHomeomorph := rfl

/-- The literal frame sign adds two pi to the full angle and multiplies the actual Spin element by the genuine Clifford negative identity. -/
def frameShift (p : FrameDatum) : FrameDatum :=
  (p.1 + ((2 * Real.pi : ℝ) : Angle), negativeOne * p.2)

/-- The literal source sign preserves density and performs the actual full-angle and Clifford sign change. -/
def shiftNeg (d : SourceDatum) : SourceDatum := (d.1, frameShift d.2)

/-- The Pauli image of the literal Clifford frame sign is exactly the existing angle and matrix sign operation. -/
theorem frameHomeomorph_frameShift (p : FrameDatum) :
    frameHomeomorph (frameShift p) =
      SourcePolarProductQuotient.frameShift (frameHomeomorph p) := by
  apply Prod.ext
  · rfl
  apply Subtype.ext
  change (spinEquiv (negativeOne * p.2)).val = -(spinEquiv p.2).val
  rw [map_mul]
  change (spinEquiv negativeOne).val * (spinEquiv p.2).val = -(spinEquiv p.2).val
  rw [spinEquiv_negativeOne]
  simp

/-- The Pauli image of the literal Clifford source sign is exactly the existing density-preserving source sign operation. -/
theorem sourceHomeomorph_shiftNeg (d : SourceDatum) :
    sourceHomeomorph (shiftNeg d) = SourcePolarDatum.shiftNeg (sourceHomeomorph d) := by
  apply Prod.ext
  · rfl
  exact frameHomeomorph_frameShift d.2

/-- The actual full-angle and Clifford frame sign is an involution. -/
theorem frameShift_involutive (p : FrameDatum) : frameShift (frameShift p) = p := by
  apply frameHomeomorph.injective
  rw [frameHomeomorph_frameShift, frameHomeomorph_frameShift,
    SourcePolarProductQuotient.frameShift_involutive]

/-- The actual full-angle and Clifford frame sign has no fixed point. -/
theorem frameShift_ne_self (p : FrameDatum) : frameShift p ≠ p := by
  intro h
  have he := congrArg frameHomeomorph h
  rw [frameHomeomorph_frameShift] at he
  exact FrameDatumManifold.frameShift_ne_self (frameHomeomorph p) he

/-- The literal density-angle-Clifford source sign is an involution. -/
theorem shiftNeg_involutive (d : SourceDatum) : shiftNeg (shiftNeg d) = d := by
  change (d.1, frameShift (frameShift d.2)) = d
  rw [frameShift_involutive]

/-- The literal density-angle-Clifford source sign has no fixed point. -/
theorem shiftNeg_ne_self (d : SourceDatum) : shiftNeg d ≠ d := by
  intro h
  exact frameShift_ne_self d.2 (congrArg Prod.snd h)

/-- The literal Clifford frame sign is smooth by smooth circle translation and actual Spin multiplication. -/
theorem contMDiff_frameShift (n : WithTop ℕ∞) : ContMDiff frameModel frameModel n frameShift := by
  have hm : ContMDiff 𝓘(ℝ, CliffordSpinManifold.Model) 𝓘(ℝ, CliffordSpinManifold.Model) n
      (fun s : Spin => negativeOne * s) :=
    (CliffordSpinManifold.contMDiff_mul n).comp (contMDiff_const.prodMk contMDiff_id)
  exact ((ChiralAngleManifold.contMDiff_shift_two_pi n).comp contMDiff_fst).prodMk
    (hm.comp contMDiff_snd)

/-- The literal Clifford source sign is smooth in the actual inherited density-angle-Spin product atlas. -/
theorem contMDiff_shiftNeg (n : WithTop ℕ∞) : ContMDiff sourceModel sourceModel n shiftNeg :=
  contMDiff_fst.prodMk ((contMDiff_frameShift n).comp contMDiff_snd)

/-- The actual free Clifford frame sign is a bundled diffeomorphism whose inverse is the same literal sign operation. -/
def frameShiftDiffeomorph (n : WithTop ℕ∞) :
    Diffeomorph frameModel frameModel FrameDatum FrameDatum n where
  toFun := frameShift
  invFun := frameShift
  left_inv := frameShift_involutive
  right_inv := frameShift_involutive
  contMDiff_toFun := contMDiff_frameShift n
  contMDiff_invFun := contMDiff_frameShift n

/-- The actual free Clifford source sign is a bundled diffeomorphism whose inverse is the same literal sign operation. -/
def shiftNegDiffeomorph (n : WithTop ℕ∞) :
    Diffeomorph sourceModel sourceModel SourceDatum SourceDatum n where
  toFun := shiftNeg
  invFun := shiftNeg
  left_inv := shiftNeg_involutive
  right_inv := shiftNeg_involutive
  contMDiff_toFun := contMDiff_shiftNeg n
  contMDiff_invFun := contMDiff_shiftNeg n

end FoliationQM.CliffordSpinPolarDatum
