/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Wieser
-/
import data.finsupp.basic
import algebra.algebra.basic
import algebra.monoid_algebra
import algebra.algebra.operations
import algebra.algebra.subalgebra

/-! Random theorems that belong in mathlib which are not related to GA

Upstream PRS:

* #4321

-/

namespace finsupp

variables {α : Type*} {M : Type*} [has_zero M]

lemma single_of_single_apply (a a' : α) (b : M) :
  single a ((single a' b) a) = single a' (single a' b) a :=
begin
  rw [single_apply, single_apply],
  ext,
  split_ifs,
  { rw h, },
  { rw [zero_apply, single_apply, if_t_t], },
end

end finsupp

namespace add_monoid_algebra

variables (k : Type*) {G : Type*}
/--
The `alg_hom` which maps from a grading of an algebra `A` back to that algebra.
-/
noncomputable def sum_id {A : Type*} [comm_semiring k] [semiring A] [algebra k A] [add_monoid G] :
  add_monoid_algebra A G →ₐ[k] A :=
lift_nc_alg_hom (alg_hom.id k A) ⟨λ g, 1, by simp, λ a b, by simp⟩ (by simp)

lemma sum_id_apply {A : Type*} [comm_semiring k] [semiring A] [algebra k A] [add_monoid G] (g : add_monoid_algebra A G) :
  sum_id k g = g.sum (λ _ gi, gi) :=
by simp [sum_id, lift_nc_alg_hom, lift_nc_ring_hom, lift_nc, alg_hom.id, ring_hom.id]

end add_monoid_algebra

namespace opposite

variables (R : Type*) {M : Type*} [comm_semiring R] [semiring M] [algebra R M]

@[simps apply]
def op_linear_equiv : M ≃ₗ[R] Mᵒᵖ :=
{ map_smul' := opposite.op_smul, .. op_add_equiv }

@[simp] lemma coe_op_linear_equiv : (op_linear_equiv R : M → Mᵒᵖ) = op := rfl
@[simp] lemma coe_op_linear_equiv_symm :
  ((op_linear_equiv R).symm : Mᵒᵖ → M) = unop := rfl

@[simp] lemma coe_op_linear_equiv_to_linear_map : ((op_linear_equiv R).to_linear_map : M → Mᵒᵖ) = op := rfl
@[simp] lemma coe_op_linear_equiv_symm_to_linear_map :
  ((op_linear_equiv R).symm.to_linear_map : Mᵒᵖ → M) = unop := rfl

end opposite

namespace submonoid

lemma mul_subset_closure {A : Type*} [monoid A] (s : set A) : s * s ⊆ submonoid.closure s :=
begin
  rw set.subset_def,
  intros x hx,
  rw submonoid.mem_coe,
  obtain ⟨p, q, hp, hq, rfl⟩ := set.mem_mul.mp hx,
  exact submonoid.mul_mem _ (submonoid.subset_closure hp) (submonoid.subset_closure hq),
end

end submonoid

namespace submodule

variables {R : Type*} {A : Type*} [comm_semiring R] [semiring A] [algebra R A]

def one_eq_algebra_of_id_range : (1 : submodule R A) = (algebra.of_id R A).range :=
begin
  dunfold has_one.one,
  ext,
  simp,
end

@[simp]
def algebra_map_mem (r : R) : algebra_map R A r ∈ (1 : submodule R A) :=
by simp [one_eq_algebra_of_id_range, algebra.of_id_apply]


end submodule

namespace set

@[simp]
lemma top_eq_univ (A : Type*) : (⊤ : set A) = set.univ := rfl

end set

namespace algebra

/-- A filtration is an indexed family of submodules such that `i ≤ j → S i ≤ S j` and `S i * S j = S (i + j)` -/
structure filtration (R : Type*) (A : Type*) (ι : Type*) [preorder ι] [has_add ι] [comm_semiring R] [semiring A] [algebra R A] :=
(to_fun : ι → submodule R A)
(mono' : monotone to_fun)
(complete' : ∀ x, ∃ i, x ∈ to_fun i)
(map_add' : ∀ n m, to_fun (n + m) = to_fun n * to_fun m)

namespace filtration

variables {R : Type*} {A : Type*} {ι : Type*} [preorder ι] [has_add ι] [comm_semiring R] [semiring A] [algebra R A]

instance : has_coe_to_fun (filtration R A ι) := ⟨_, λ f, f.to_fun⟩

variables (f : filtration R A ι)

-- the normal bundled function tricks, to hide the `to_fun`
@[simp] lemma to_fun_eq_coe : f.to_fun = f := rfl
@[simp] lemma mk_coe (f : ι → submodule R A) (h1 h2 h3) : ⇑(filtration.mk f h1 h2 h3) = f := rfl
lemma mono : monotone f := f.mono'
lemma map_add {n m} : f (n + m) = f n * f m := f.map_add' n m
lemma complete : ∀ x, ∃ i, x ∈ f i := f.complete'

lemma supr_eq_top (x : A) : supr f = ⊤ :=
begin
  rw submodule.supr_eq_span,
  suffices : (⋃ (i : ι), (f i : set A)) = ⊤,
  { simp [this] },
  refine set.eq_univ_of_forall (λ x, _),
  simp only [set.mem_Union, submodule.mem_coe],
  exact f.complete' x,
end

end filtration

end algebra