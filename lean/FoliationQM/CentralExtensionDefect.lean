module
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Tactic.Group

/-!
# Defect algebra for an independent central extension

For the geometric component of v13 `prop:takabayasi`, this module uses
only a group homomorphism with central kernel. Triple defects, their
quadruple equation, and change under different pair representatives are
proved by group algebra. Neither a Spin group nor a characteristic class
is part of the input. Surjectivity is not needed for these identities.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CentralExtensionDefect

variable {K G : Type*} [Group K] [Group G] (p : K →* G)

/-- The kernel lies in the center of the source group. -/
def Central : Prop := ∀ z : p.ker, ∀ a : K, z.val * a = a * z.val

/-- The ordered triple defect, with its kernel membership proved from projected composition. -/
def defect (a b c : K) (h : p b * p a = p c) : p.ker :=
  ⟨b * a * c⁻¹, by simp only [MonoidHom.mem_ker, map_mul, map_inv]; rw [h, mul_inv_cancel]⟩

/-- The kernel element is the actual ordered ratio of the three representatives. -/
theorem defect_val (a b c : K) (h : p b * p a = p c) :
    (defect p a b c h).val = b * a * c⁻¹ := rfl

/-- Multiplying the direct representative by its defect recovers the composite. -/
theorem defect_mul (a b c : K) (h : p b * p a = p c) :
    (defect p a b c h).val * c = b * a := by
  simp [defect, mul_assoc]

/-- A trivial first edge contributes no defect. -/
theorem defect_one_left (b : K) (h : p b * p 1 = p b) : defect p 1 b b h = 1 := by
  apply Subtype.ext
  simp [defect]

/-- A trivial second edge contributes no defect. -/
theorem defect_one_right (a : K) (h : p 1 * p a = p a) : defect p a 1 a h = 1 := by
  apply Subtype.ext
  simp [defect]

/-- Centrality gives the ordered degree-two equation without a cocycle assumption. -/
theorem quadruple (hc : Central p) (a b c d e f : K)
    (hab : p b * p a = p c) (hbe : p e * p b = p d)
    (had : p d * p a = p f) (hce : p e * p c = p f) :
    defect p b e d hbe * defect p a d f had =
      defect p a b c hab * defect p c e f hce := by
  apply Subtype.ext
  change (e * b * d⁻¹) * (d * a * f⁻¹) =
    (b * a * c⁻¹) * (e * c * f⁻¹)
  have he := hc (defect p a b c hab) e
  change (b * a * c⁻¹) * e = e * (b * a * c⁻¹) at he
  calc
    _ = e * (b * a * c⁻¹) * c * f⁻¹ := by group
    _ = (b * a * c⁻¹) * e * c * f⁻¹ := by rw [he]
    _ = _ := by group

/-- Two representatives over the same target differ by an actual kernel element. -/
def difference (a b : K) (h : p b = p a) : p.ker :=
  ⟨b * a⁻¹, by simp only [MonoidHom.mem_ker, map_mul, map_inv]; rw [h, mul_inv_cancel]⟩

/-- The difference coefficient is the actual ratio in the original group. -/
theorem difference_val (a b : K) (h : p b = p a) :
    (difference p a b h).val = b * a⁻¹ := rfl

/-- The ratio reconstructs the new representative. -/
theorem difference_mul (a b : K) (h : p b = p a) :
    (difference p a b h).val * a = b := by simp [difference, mul_assoc]

/-- The ratio of an unchanged representative is trivial. -/
theorem difference_self (a : K) (h : p a = p a) : difference p a a h = 1 := by
  apply Subtype.ext
  simp [difference]

/-- Changing the three representatives changes the defect by the kernel pair coboundary. -/
theorem defect_change (hc : Central p) (a b c a' b' c' : K)
    (ha : p a' = p a) (hb : p b' = p b) (hc' : p c' = p c)
    (h : p b * p a = p c) (h' : p b' * p a' = p c') :
    defect p a' b' c' h' =
      difference p b b' hb * difference p a a' ha *
        defect p a b c h * (difference p c c' hc')⁻¹ := by
  apply Subtype.ext
  change b' * a' * c'⁻¹ =
    (b' * b⁻¹) * (a' * a⁻¹) * (b * a * c⁻¹) * (c' * c⁻¹)⁻¹
  have he := hc (difference p a a' ha) b
  change (a' * a⁻¹) * b = b * (a' * a⁻¹) at he
  calc
    _ = (b' * b⁻¹) * (b * (a' * a⁻¹)) * a * c'⁻¹ := by group
    _ = (b' * b⁻¹) * ((a' * a⁻¹) * b) * a * c'⁻¹ := by rw [he]
    _ = _ := by group

/-- A commuting homomorphism of extensions maps the actual kernels. -/
def kernelMap {K' : Type*} [Group K'] (p' : K' →* G) (f : K →* K')
    (hf : ∀ a, p' (f a) = p a) : p.ker →* p'.ker where
  toFun z := ⟨f z.val, (hf z.val).trans z.property⟩
  map_one' := Subtype.ext (map_one f)
  map_mul' a b := Subtype.ext (map_mul f a.val b.val)

/-- Naturality of the triple defect follows from the actual source homomorphism. -/
theorem defect_natural {K' : Type*} [Group K'] (p' : K' →* G) (f : K →* K')
    (hf : ∀ a, p' (f a) = p a) (a b c : K) (h : p b * p a = p c)
    (h' : p' (f b) * p' (f a) = p' (f c)) :
    kernelMap p p' f hf (defect p a b c h) = defect p' (f a) (f b) (f c) h' := by
  apply Subtype.ext
  change f (b * a * c⁻¹) = f b * f a * (f c)⁻¹
  rw [map_mul, map_mul, map_inv]

/-- Naturality also preserves the actual difference between two representatives. -/
theorem difference_natural {K' : Type*} [Group K'] (p' : K' →* G) (f : K →* K')
    (hf : ∀ a, p' (f a) = p a) (a b : K) (h : p b = p a)
    (h' : p' (f b) = p' (f a)) :
    kernelMap p p' f hf (difference p a b h) = difference p' (f a) (f b) h' := by
  apply Subtype.ext
  change f (b * a⁻¹) = f b * (f a)⁻¹
  rw [map_mul, map_inv]

end FoliationQM.CentralExtensionDefect
