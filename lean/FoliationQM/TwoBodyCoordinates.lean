module

public import FoliationQM.ObserverGaussianFisher
public import FoliationQM.PolarRegularity

/-!
# Physical time and Cartesian coordinates for two particles

The first pair is physical time and the retained position. The final
coordinate is the remote position. Each partial derivative is a real
Fréchet derivative evaluated at its constant Cartesian direction.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.TwoBodyCoordinates

open LorentzCoordinates ObserverGaussianFisher
open scoped Topology BigOperators

/-- Physical time together with the first spatial position. -/
abbrev Base := ℝ × Spatial

/-- Two spatial positions and one common physical time. -/
abbrev Point := Base × Spatial

/-- Unit physical-time direction on the retained spacetime. -/
def baseTime : Base := (1, 0)

/-- A retained Cartesian direction at fixed physical time. -/
def baseAxis (i : Fin 3) : Base := (0, axes i)

/-- Joint unit physical-time direction at fixed particle positions. -/
def timeAxis : Point := (baseTime, 0)

/-- Move the first particle in Cartesian direction `i`. -/
def leftAxis (i : Fin 3) : Point := (baseAxis i, 0)

/-- Move the second particle in Cartesian direction `i`. -/
def rightAxis (i : Fin 3) : Point := (0, axes i)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Real Fréchet derivative of a joint field in a constant direction. -/
def D (v : Point) (f : Point → E) (p : Point) : E := fderiv ℝ f p v

/-- Physical time derivative at fixed positions. -/
def Dt (f : Point → E) : Point → E := D timeAxis f

/-- First-particle spatial partial derivative. -/
def D₁ (i : Fin 3) (f : Point → E) : Point → E := D (leftAxis i) f

/-- Second-particle spatial partial derivative. -/
def D₂ (i : Fin 3) (f : Point → E) : Point → E := D (rightAxis i) f

/-- Cartesian Laplacian acting on the first spatial position. -/
def lap₁ (f : Point → E) (p : Point) : E := ∑ i, D₁ i (D₁ i f) p

/-- Cartesian Laplacian acting on the second spatial position. -/
def lap₂ (f : Point → E) (p : Point) : E := ∑ i, D₂ i (D₂ i f) p

variable {f : Point → E} {b : Base} {t : ℝ} {x y : Spatial}

/-- Fixing the remote position gives the joint derivative in any retained spacetime direction. -/
theorem base_fderiv (hf : DifferentiableAt ℝ f (b,y)) (v : Base) :
    fderiv ℝ (fun s => f (s,y)) b v = D (v,0) f (b,y) := by
  change fderiv ℝ (f ∘ fun s => (s,y)) _ _ = _
  rw [(hf.hasFDerivAt.comp b (hasFDerivAt_prodMk_left b y)).fderiv]
  rfl

/-- Fixing the retained spacetime point gives the joint derivative in the remote direction. -/
theorem remote_fderiv (hf : DifferentiableAt ℝ f (b,y)) (v : Spatial) :
    fderiv ℝ (fun w => f (b,w)) y v = D (0,v) f (b,y) := by
  change fderiv ℝ (f ∘ fun w => (b,w)) _ _ = _
  rw [(hf.hasFDerivAt.comp y (hasFDerivAt_prodMk_right b y)).fderiv]
  rfl

/-- Holding both positions fixed identifies the usual one-variable time derivative. -/
theorem hasDerivAt_time (hf : DifferentiableAt ℝ f ((t,x),y)) :
    HasDerivAt (fun s => f ((s,x),y)) (Dt f ((t,x),y)) t := by
  have h := (hasFDerivAt_prodMk_left (𝕜 := ℝ) t x).prodMk (hasFDerivAt_const y t)
  exact (hf.hasFDerivAt.comp t h).hasDerivAt

private theorem left_embedding (t : ℝ) (u y : Spatial) :
    HasFDerivAt (fun w : Spatial => ((t,w),y)) ((ContinuousLinearMap.inr ℝ ℝ Spatial).prod 0) u :=
  (hasFDerivAt_prodMk_right (𝕜 := ℝ) t u).prodMk (hasFDerivAt_const y u)

/-- Varying the first position with time and the second position fixed. -/
theorem left_fderiv (hf : DifferentiableAt ℝ f ((t,x),y)) (v : Spatial) :
    fderiv ℝ (fun w => f ((t,w),y)) x v = D ((0,v),0) f ((t,x),y) := by
  have h := hf.hasFDerivAt.comp x (left_embedding t x y)
  change fderiv ℝ (f ∘ fun w => ((t,w),y)) _ _ = _
  rw [h.fderiv]
  rfl

/-- A fixed-time spatial pair has the same differential as the joint wave along spatial directions. -/
theorem spatial_fderiv (hf : DifferentiableAt ℝ f ((t,x),y)) (v : Spatial × Spatial) :
    fderiv ℝ (fun w : Spatial × Spatial => f ((t,w.1),w.2)) (x,y) v =
      D ((0,v.1),v.2) f ((t,x),y) := by
  have h := ((hasFDerivAt_const (𝕜 := ℝ) t (x,y)).prodMk hasFDerivAt_fst).prodMk hasFDerivAt_snd
  change fderiv ℝ (f ∘ fun w : Spatial × Spatial => ((t,w.1),w.2)) _ _ = _
  rw [(hf.hasFDerivAt.comp (x,y) h).fderiv]
  rfl

private theorem second_slice {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {g : A → Point} {L : A →L[ℝ] Point} (hg : ∀ a, HasFDerivAt g L a) {a : A}
    (hf : ContDiffAt ℝ 2 f (g a)) (v : A) :
    fderiv ℝ (fun z => fderiv ℝ (f ∘ g) z v) a v = D (L v) (D (L v) f) (g a) := by
  have hnear := (hg a).continuousAt.eventually (PolarRegularity.eventually_differentiableAt_of_contDiffAt_two hf)
  have he : (fun z => fderiv ℝ (f ∘ g) z v) =ᶠ[𝓝 a] (D (L v) f ∘ g) := by
    filter_upwards [hnear] with z hz
    rw [(hz.hasFDerivAt.comp z (hg z)).fderiv]
    rfl
  have hd : DifferentiableAt ℝ (D (L v) f) (g a) :=
    ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by norm_num)
  rw [he.fderiv_eq, (hd.hasFDerivAt.comp a (hg a)).fderiv]
  rfl

/-- The iterated first-particle partial equals the second derivative of the actual fixed-time slice. -/
theorem left_second (hf : ContDiffAt ℝ 2 f ((t,x),y)) (i : Fin 3) :
    fderiv ℝ (fun w => fderiv ℝ (fun u => f ((t,u),y)) w (axes i)) x (axes i) =
      D₁ i (D₁ i f) ((t,x),y) :=
  second_slice (g := fun u => ((t,u),y)) (fun u => left_embedding t u y) hf (axes i)

/-- The iterated second-particle partial equals the second derivative of the remote slice. -/
theorem right_second (hf : ContDiffAt ℝ 2 f (b,y)) (i : Fin 3) :
    fderiv ℝ (fun w => fderiv ℝ (fun u => f (b,u)) w (axes i)) y (axes i) =
      D₂ i (D₂ i f) (b,y) :=
  second_slice (g := fun u => (b,u)) (fun u => hasFDerivAt_prodMk_right b u) hf (axes i)

end FoliationQM.TwoBodyCoordinates
