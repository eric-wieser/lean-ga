/-
Copyright (c) 2020 Utensil Song. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Utensil Song

This file is based on https://arxiv.org/abs/1205.5935
-/
import algebra.group.hom
import algebra.algebra.basic
import data.real.basic
import data.complex.basic

import tactic.apply_fun
import tactic

universes u u₀ u₁

/- Needed for zero_pairwise_ortho_vector -/
-- lemma pairwise_of_repeat {X : Type*} {x : X} {n : ℕ} {r : X → X → Prop} (hr : r x x) :
--   list.pairwise r (list.repeat x n) :=
-- begin
--   induction n with d hd,
--   { exact list.pairwise.nil},
--   { apply list.pairwise.cons _ hd,
--     intros a ha,
--     convert hr,
--     exact list.eq_of_mem_repeat ha,
--   }
-- end

class geometric_algebra
-- Axiom 2: G contains a field G0 of characteristic zero which includes 0 and 1.
(G₀ : Type*) [field G₀]
-- Axiom 3: G contains a subset G1 closed under addition, 
-- and λ ∈ G0, v ∈ G1 implies λv = vλ ∈ G1.
(G₁ : Type*) [add_comm_group G₁] [vector_space G₀ G₁]
-- Axiom 1: G is a ring with unit. 
-- The additive identity is called 0 and the multiplicative identity is called 1.
(G : Type*) [ring G]
[algebra G₀ G]
:=
(f₁ : G₁ →+ G)
-- Axiom 4: The square of every vector is a scalar.
-- TODO clearly this should be nameed following "contraction rule", I'm thinking maybe `contract`?
(vec_sq_scalar : ∀ v : G₁, ∃ k : G₀, f₁ v * f₁ v = algebra_map _ _ k )

namespace geometric_algebra

section basic


parameters
{G₀ : Type u} [field G₀]
{G₁ : Type u} [add_comm_group G₁] [vector_space G₀ G₁]
{G : Type u} [ring G] [algebra G₀ G] [geometric_algebra G₀ G₁ G]


-- define a blade representation
-- TODO: how to describe the fact that the vector argument to `graded` must be orthogonal?
inductive blade : nat → Type u
| scalar : G₀ → blade 0
| vector : G₁ → blade 1
| graded {n : ℕ} : G₁ → blade (n + 1) → blade (n + 2)
namespace blade
  instance g0_coe : has_coe G₀ (blade 0) := { coe := blade.scalar }
  instance g1_coe : has_coe G₁ (blade 1) := { coe := blade.vector }

  -- define zero and one on the blades
  def zero : Π (n : ℕ), blade n
  | 0 := blade.scalar (0 : G₀)
  | 1 := blade.vector (0 : G₁)
  | (nat.succ $ nat.succ n) := blade.graded (0 : G₁) (zero $ nat.succ n)
  instance has_zero {n : ℕ} : has_zero (blade n) := { zero := zero n }
  instance r0_has_one : has_one (blade 0) := { one := (1 : G₀) }

  -- define add on the blades
  def r0_add (a : blade 0) (b : blade 0) : blade 0 := begin
    cases a with a',
    cases b with b', 
    exact blade.scalar (a' + b')
  end
  instance r0_has_add : has_add (blade 0) := { add := r0_add }
  def r1_add (a : blade 1) (b : blade 1) : blade 1 := begin
    cases a,
    cases b,
    exact blade.vector (a_1 + b_1)
  end
  instance r1_has_add : has_add (blade 1) := { add := r1_add }
end blade

-- define a sum-of-blades representation
inductive hom_mv : nat → Type u
| scalar : blade 0 -> hom_mv 0
| vector : blade 1 -> hom_mv 1
| graded {n : ℕ} : list (blade $ nat.succ $ nat.succ n) → (hom_mv $ nat.succ $ nat.succ n)

namespace hom_mv
  def coe : Π {n : ℕ}, (blade n) → hom_mv n
  | 0 := hom_mv.scalar
  | 1 := hom_mv.vector
  | (r + 2) := λ b, hom_mv.graded [b]
  instance has_blade_coe {r : ℕ} : has_coe (blade r) (hom_mv r) := { coe := coe }
  instance has_g0_coe : has_coe G₀ (hom_mv 0) := { coe := λ s, coe s }
  instance has_g1_coe : has_coe G₁ (hom_mv 1) := { coe := λ s, coe s }

  -- define zero and one on the hom_mvs
  instance has_zero {n : ℕ} : has_zero (hom_mv n) := { zero := (0 : blade n) }
  instance r0_has_one : has_one (hom_mv 0) := { one := (1 : blade 0) }

  def add : Π {n : ℕ}, hom_mv n → hom_mv n → hom_mv n
  | 0 := λ a b, begin
    cases a with a',
    cases b with b',
    exact hom_mv.scalar (a' + b'),
  end
  | 1 := λ a b, begin
    cases a,
    cases b,
    exact hom_mv.vector (a_1 + b_1)
  end
  | (n + 2) := λ a b,begin
    cases a,
    cases b,
    exact hom_mv.graded (a_a ++ b_a),
  end
  instance has_add {n : ℕ} : has_add (hom_mv n) := { add := add }
end hom_mv

inductive multivector : nat → Type u
| scalar : hom_mv 0 → multivector 0
| augment {n : ℕ} : multivector n → hom_mv (nat.succ n) → multivector (nat.succ n)


namespace mv
  -- define zero and one on the multivectors
  def mv_zero : Π (n : ℕ), multivector n
  | 0 := multivector.scalar (0 : G₀)
  | 1 := multivector.augment (mv_zero 0) 0
  | (nat.succ $ nat.succ n) := multivector.augment (mv_zero $ nat.succ n) (hom_mv.graded [])
  def mv_one : Π (n : ℕ), multivector n
  | 0 := multivector.scalar (1 : G₀)
  | 1 := multivector.augment (mv_one 0) 0
  | (nat.succ $ nat.succ n) := multivector.augment (mv_one $ nat.succ n) (hom_mv.graded [])
  instance mv_has_zero {n : ℕ} : has_zero (multivector n) := { zero := mv_zero n }
  instance mv_has_one {n : ℕ} : has_one (multivector n) := { one := mv_one n }

  -- blades are coercible to multivectors
  def hom_mv_coe : Π {n : ℕ}, (hom_mv n) -> (multivector n)
  | nat.zero := λ b, multivector.scalar b
  | (nat.succ n) := λ b, multivector.augment (mv_zero n) b
  instance has_hom_mv_coe  {n : ℕ} : has_coe (hom_mv n) (multivector n) := { coe := hom_mv_coe }
  instance has_g0_coe : has_coe G₀ (multivector 0) := { coe := λ s, hom_mv_coe $ hom_mv.scalar $ blade.scalar s }
  instance has_g1_coe : has_coe G₁ (multivector 1) := { coe := λ v, hom_mv_coe $ hom_mv.vector $ blade.vector v }

  -- multivectors are up-coercible
  def augment_coe {n : ℕ} (mv : multivector n) : multivector (nat.succ n) := multivector.augment mv 0
  instance has_augment_coe {n : ℕ} : has_coe (multivector n) (multivector (nat.succ n)) := { coe := augment_coe }

  def mv_add : Π {n : ℕ}, multivector n → multivector n → multivector n
  | 0 := λ a b, begin
    cases a,
    cases b,
    exact multivector.scalar (a_1 + b_1)
  end
  | (nat.succ n) := λ a b, begin
    cases a with z z a' ar,
    cases b with z z b' br,
    exact multivector.augment (mv_add a' b') (ar + br)
  end
  instance has_add {n: ℕ} : has_add (multivector n) := { add := mv_add }
end mv

parameter v : G₁

--  Addition!
#check ((2 + v) : multivector 1)
#check ((2 + v) : multivector 2)

def fᵥ : G₁ →+ G := f₁ G₀

def fₛ : G₀ →+* G := algebra_map G₀ G

lemma assoc : ∀ A B C : G, (A * B) * C = A * (B * C) := λ A B C, semigroup.mul_assoc A B C

lemma left_distrib : ∀ A B C : G, A * (B + C) = (A * B) + (A * C) := λ A B C, distrib.left_distrib A B C

lemma right_distrib : ∀ A B C : G, (A + B) * C = (A * C) + (B * C) := λ A B C, distrib.right_distrib A B C

def prod_vec (a b : G₁) : G := fᵥ a * fᵥ b

local infix `*ᵥ`:75 := prod_vec

def square_vec (a : G₁) := a *ᵥ a

local postfix `²ᵥ`:80 := square_vec

def sym_prod_vec (a b : G₁) := a *ᵥ b + b *ᵥ a

local infix `*₊ᵥ`:75 := sym_prod_vec

def is_orthogonal (a : G₁) (b : G₁) : Prop := sym_prod_vec a b = 0

theorem zero_is_orthogonal (a : G₁) : is_orthogonal 0 a := begin
  unfold is_orthogonal,
  unfold sym_prod_vec,
  unfold prod_vec,
  simp
end

/- a list of r orthogonal vectors, which may be non-unique -/
def pairwise_ortho_vector (r : ℕ) := {l : vector G₁ r // l.val.pairwise is_orthogonal}

/- need this for later, can't seem to get the type inference to work if I inline it-/
-- def zero_pairwise_ortho_vector (r : ℕ) : pairwise_ortho_vector r := ⟨
--   vector.repeat (0 : G₁) r, begin
--   unfold vector.repeat subtype.val,
--   apply pairwise_of_repeat,
--   apply zero_is_orthogonal,
-- end⟩


-- r-blades
def is_rblade (r : ℕ) (b : G) : Prop :=
  -- a product of orthogonal vectors an a scalar
  (∃ (k: G₀) (v : pairwise_ortho_vector r),
   b = fₛ k * list.prod (v.val.val.map fᵥ))

def Bᵣ (r : ℕ) := set_of (is_rblade r)

namespace Bᵣ
  variables {r : ℕ}

  lemma all_G₀_is_rblade0 (k : G₀) : is_rblade 0 (fₛ k) := begin
    use [k, list.pairwise.nil],
    unfold vector.nil subtype.val list.map,
    rw list.prod_nil,
    simp,
  end
  lemma all_G₁_is_rblade1 (a : G₁) : is_rblade 1 (fᵥ a) := begin
    use 1,
    use ⟨(vector.cons a vector.nil), list.pairwise_singleton _ a⟩,
    unfold vector.cons vector.nil subtype.val list.map,
    rw [list.prod_cons, list.prod_nil],
    simp,
  end

  instance has_coe_from_G₀ : has_coe G₀ (Bᵣ 0) := { coe := λ k, ⟨fₛ k, all_G₀_is_rblade0 k⟩}
  instance has_coe_from_G₁ : has_coe G₁ (Bᵣ 1) := { coe := λ a, ⟨fᵥ a, all_G₁_is_rblade1 a⟩}

  -- these are trivial, but maybe still needed
  instance has_coe_to_G : has_coe (Bᵣ r) G := { coe := subtype.val }
  @[simp]
  lemma coe_is_rblade (b : Bᵣ r) : is_rblade r b := b.property

  /- todo: do we want this? -/
  -- instance has_zero : has_zero (Bᵣ r) := {
  --   zero := ⟨(0 : G), begin
  --     use [0, zero_pairwise_ortho_vector r],
  --     simp,
  --   end⟩ 
  -- }

  /- scalar multiple of an element of Bᵣ is also in Bᵣ -/
  lemma smul_mem_Bᵣ {b : G} {k : G₀} (hb : is_rblade r b) : (is_rblade r ((fₛ k) * b)) := begin
    exact exists.elim hb begin
      intros a ha,
      use k*a,
      exact exists.elim ha begin
        intros a_1 ha_1,
        use a_1,
        rw ha_1,
        rw ring_hom.map_mul,
        rw mul_assoc
      end
    end
  end

  /- now show via trivial proofs that Bᵣ is a mul_action and has_neg -/
  def smul (k : G₀) (b : Bᵣ r) : Bᵣ r := ⟨(fₛ k) * b.val, smul_mem_Bᵣ b.property⟩ 
  instance has_scalar (r : ℕ) : has_scalar G₀ (Bᵣ r) := { smul := smul }
  
  def one_smul (b : Bᵣ r) : smul (1 : G₀) b = b := by simp [smul]
  def mul_smul (k1 k2 : G₀) (b : Bᵣ r) : smul (k1 * k2) b =  smul k1 (smul k2 b) := by simp [smul, mul_assoc]
  instance mul_action : mul_action G₀ (Bᵣ r) := {one_smul := one_smul, mul_smul := mul_smul, ..has_scalar r}

  def neg (b : Bᵣ r) : Bᵣ r := smul (-1 : G₀) b
  instance has_neg (r : ℕ) : has_neg (Bᵣ r) := { neg := neg}

end Bᵣ

-- r-vectors
def Gᵣ (r : ℕ) := add_subgroup.closure (Bᵣ r)

example (r : ℕ) : add_comm_group (Gᵣ r) := by apply_instance
namespace Gᵣ
  variables {r : ℕ}

  -- this is trivial, but maybe needed
  -- instance has_coe_from_Bᵣ : has_coe (Bᵣ r) (Gᵣ r) := { coe := λ b, ⟨b.val, add_subgroup.subset_closure b.property⟩ }

  -- scalar multiple of an element of Gᵣ is also in Gᵣ
  lemma smul_mem_Gᵣ {v : G} {k : G₀} (hv : v ∈ Gᵣ r) : ((fₛ k) * v) ∈ Gᵣ r := begin
    apply add_subgroup.closure_induction hv,
    {
      intros x hx,
      apply add_subgroup.subset_closure,
      exact Bᵣ.smul_mem_Bᵣ hx,
    },
    {
      rw mul_zero,
      exact (0 : Gᵣ r).property,
    },
    {
      intros a b,
      rw mul_add,
      exact add_subgroup.add_mem (Gᵣ r)
    },
    {
      intros a,
      rw ← neg_mul_eq_mul_neg,
      exact add_subgroup.neg_mem (Gᵣ r)
    }
  end

  -- now show via trivial proofs that Gᵣ is a semimodule (basically a vector space)
  def smul (k : G₀) (v : Gᵣ r) : Gᵣ r := ⟨fₛ k * v, smul_mem_Gᵣ v.property⟩
  instance has_scalar (r : ℕ) : has_scalar G₀ (Gᵣ r) := { smul := smul }
  
  def one_smul (v : Gᵣ r) : smul (1 : G₀) v = v := by simp [smul]
  def mul_smul (k1 k2 : G₀) (v : Gᵣ r) : smul (k1 * k2) v =  smul k1 (smul k2 v) := by simp [smul, mul_assoc]
  instance mul_action : mul_action G₀ (Gᵣ r) := {one_smul := one_smul, mul_smul := mul_smul, ..has_scalar r}

  def smul_add (k : G₀) (x y : Gᵣ r) : smul k (x + y) = smul k x + smul k y := by {simp [smul, mul_add], refl}
  def smul_zero (k : G₀) : smul k (0 : Gᵣ r) = 0 := by {simp [smul], refl}
  instance distrib_mul_action : distrib_mul_action G₀ (Gᵣ r) := { smul_add := smul_add, smul_zero := smul_zero, ..mul_action }
    
  def add_smul (k1 k2 : G₀) (v : Gᵣ r) : smul (k1 + k2) v = smul k1 v + smul k2 v := by {simp [smul, add_mul], refl}
  def zero_smul (v : Gᵣ r) : smul (0 : G₀) v = 0 := by {simp [smul], refl}
  instance semimodule (r : ℕ) : semimodule G₀ (Gᵣ r) := {add_smul := add_smul, zero_smul := zero_smul, ..distrib_mul_action }
end Gᵣ

-- multi-vectors
def Mᵣ (r : ℕ) := add_subgroup.closure (⋃ (r' : fin r), (Gᵣ r').carrier)
example (r : ℕ) : add_comm_group (Mᵣ r) := by apply_instance

@[simp]
def is_scalar : G → Prop := is_rblade 0

/-
  Symmetrised product of two vectors must be a scalar
-/
lemma vec_sym_prod_scalar (a b : G₁) : is_scalar (a *₊ᵥ b) :=
have h1 : (a + b)²ᵥ = a²ᵥ + b²ᵥ + a *₊ᵥ b, from begin
  unfold square_vec sym_prod_vec prod_vec,
  rw add_monoid_hom.map_add fᵥ a b,
  rw left_distrib,
  repeat {rw right_distrib},
  abel,
end,
have vec_sq_scalar : ∀ v : G₁, ∃ k : G₀, v²ᵥ = fₛ k, from
  λ v, geometric_algebra.vec_sq_scalar(v),
begin
  apply exists.elim (vec_sq_scalar (a + b)),
  intro kab,
  apply exists.elim (vec_sq_scalar a),
  intro ka,
  apply exists.elim (vec_sq_scalar b),
  intro kb,
  intros hb ha hab,
  rw [hb, ha, hab] at h1,
  have h2 : (fₛ (kab - ka - kb : G₀) : G) = sym_prod_vec a b, by {
    repeat {rw ring_hom.map_sub},
    rw h1,
    abel,
  },
  rw ← h2,
  rw is_scalar,
  apply Bᵣ.all_G₀_is_rblade0, -- this feels clumsy, can I make this automatic?
end

end basic

end geometric_algebra
