/-
Copyright (c) 2024 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Finsupp.PWO
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!

# Gröbner Bases of ideals in the ring of polynomials over a field

-/
namespace MvPolynomial

variable {σ K α : Type*} [Field K]

class MonomialOrder (σ : Type*) (α : outParam (Type*)) [LinearOrder α] [OrderBot α] where
  ( size : (σ →₀ ℕ) ↪ α )
  ( size_monotone : Monotone size )
  ( size_injective : Function.Injective size )
  ( size_zero : size 0 = ⊥ )
  ( le_iff_add_le_add' {m n p} : size m ≤ size n ↔ size (m + p) ≤ size (n + p) )

namespace MonomialOrder

attribute [simp] size_zero

variable [LinearOrder α] [OrderBot α] [MonomialOrder σ α]

@[simp]
theorem size_add_le_size_add_right_iff {m n p : σ →₀ ℕ} :
    size (m + p) ≤ size (n + p) ↔ size m ≤ size n :=
  le_iff_add_le_add'.symm

@[simp]
theorem size_add_le_size_add_left_iff {m n p : σ →₀ ℕ} :
    size (p + m) ≤ size (p + n) ↔ size m ≤ size n := by
  rw [add_comm, add_comm p n, size_add_le_size_add_right_iff]

theorem size_add_le_size_add {m n p q : σ →₀ ℕ}
    (hmp : size m ≤ size p) (hnq : size n ≤ size q) :
    size (m + n) ≤ size (p + q) :=
  calc size (m + n) ≤ size (p + n) := size_add_le_size_add_right_iff.2 hmp
    _ ≤ size (p + q) := size_add_le_size_add_left_iff.2 hnq

@[simp]
theorem size_eq_bot_iff {m : σ →₀ ℕ} : size m = ⊥ ↔ m = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ size_zero⟩
  rw [← size_zero (σ := σ)] at h
  exact size_injective h

noncomputable def leadingMonomial (f : MvPolynomial σ K) : σ →₀ ℕ :=
  (f.support.toList.argmax size).getD 0

noncomputable def mleadingCoeff (f : MvPolynomial σ K) : K :=
  f.coeff (leadingMonomial f)

@[simp]
theorem leadingMonomial_zero : leadingMonomial (0 : MvPolynomial σ K) = 0 := by
  simp [leadingMonomial]

@[simp]
theorem mleadingCoeff_zero : mleadingCoeff (0 : MvPolynomial σ K) = 0 := by
  simp [mleadingCoeff]

theorem leadingMonomial_mem_support {f : MvPolynomial σ K} (hf0 : f ≠ 0) :
    leadingMonomial f ∈ f.support := by
  rw [leadingMonomial]
  cases h : f.support.toList.argmax size with
  | none => simp_all
  | some m =>
    classical rw [List.argmax_eq_some_iff] at h
    simp_all

@[simp]
theorem mleadingCoeff_eq_zero_iff {p : MvPolynomial σ K} :
     mleadingCoeff p = 0 ↔ p = 0 := by
  rw [mleadingCoeff]
  by_cases hp0 : p = 0
  · simp [hp0]
  · simp only [hp0, iff_false]
    exact mem_support_iff.1 (leadingMonomial_mem_support hp0)

noncomputable def norm (f : MvPolynomial σ K) : WithBot α :=
  f.support.sup (fun m => (size m : α))

@[simp]
theorem norm_eq_bot_iff {f : MvPolynomial σ K} : norm f = ⊥ ↔ f = 0 := by
  simp [norm, MvPolynomial.ext_iff]

@[simp]
theorem norm_zero : norm (0 : MvPolynomial σ K) = ⊥ := by
  rw [norm_eq_bot_iff]

theorem size_le_leadingMonomial_of_mem_support {f : MvPolynomial σ K} {m : σ →₀ ℕ}
    (hm : m ∈ f.support) : size m ≤ size (leadingMonomial f) := by
  rw [leadingMonomial]
  cases h : f.support.toList.argmax size with
  | none => simp_all
  | some n =>
    classical rw [List.argmax_eq_some_iff] at h
    simp_all

theorem size_leadingMonomial_le_iff_forall_le {p : MvPolynomial σ K} {a : α} :
    size (leadingMonomial p) ≤ a ↔ ∀ n ∈ p.support, size n ≤ a := by
  refine ⟨?_, ?_⟩
  · intro h q hq
    exact le_trans (size_le_leadingMonomial_of_mem_support hq) h
  · intro h
    by_cases hp0 : p = 0
    · simp_all only [support_zero, Finset.not_mem_empty, IsEmpty.forall_iff, implies_true,
        leadingMonomial_zero, bot_le, size_zero]
    · exact h _ (leadingMonomial_mem_support hp0)

theorem norm_le_iff_forall_le {p : MvPolynomial σ K} {a : WithBot α} :
    norm p ≤ a ↔ ∀ n ∈ p.support, ((size n : α) : WithBot α) ≤ a := by
  rw [norm, Finset.sup_le_iff]

theorem le_norm_of_mem_support {p : MvPolynomial σ K} {m : σ →₀ ℕ} (hm : m ∈ p.support) :
    size m ≤ norm p :=
  Finset.le_sup (f := fun m => ((size m : α) : WithBot α)) hm

def monomialIdeal (S : Set (MvPolynomial σ K)) : Ideal (MvPolynomial σ K) :=
  Ideal.span ((fun p => monomial (leadingMonomial p) 1) '' (S \ {0}))

theorem mem_monomialIdeal_iff {p : MvPolynomial σ K} {S : Set (MvPolynomial σ K)} :
    p ∈ monomialIdeal S ↔ ∀ m ∈ p.support, ∃ q ∈ S, q ≠ 0 ∧
      leadingMonomial q ≤ m := by
  refine Iff.trans ?_ (Iff.trans (mem_ideal_span_monomial_image (x := p) (s :=
    leadingMonomial '' (S \ {0}))) ?_)
  · rw [Set.image_image, monomialIdeal]
  · simp only [Set.exists_mem_image, Set.mem_diff, Set.mem_singleton_iff, and_assoc]

theorem norm_add_le {p q : MvPolynomial σ K} :
    norm (p + q) ≤ max (norm p) (norm q) := by
  classical
  rw [norm_le_iff_forall_le]
  intro m hm
  rcases (Finset.mem_union.1 (MvPolynomial.support_add hm)) with hmp | hmq
  · exact le_max_of_le_left (le_norm_of_mem_support hmp)
  · exact le_max_of_le_right (le_norm_of_mem_support hmq)

@[simp]
theorem leadingMonomial_neg {p : MvPolynomial σ K} :
    leadingMonomial (-p) = leadingMonomial p := by
  simp [leadingMonomial]

theorem leadingMonomial_monomial [DecidableEq K] (m : σ →₀ ℕ) (a : K) :
    leadingMonomial (monomial m a) = if a = 0 then 0 else m := by
  simp [leadingMonomial, support_monomial]
  split_ifs
  · simp
  · simp

@[simp]
theorem mleadingCoeff_monomial (m : σ →₀ ℕ) (a : K) :
    mleadingCoeff (monomial m a) = a := by
  classical
    rw [mleadingCoeff, leadingMonomial_monomial]
    split_ifs <;> simp_all

theorem coeff_leadingMonomial_add_mul {p q : MvPolynomial σ K} :
    coeff (leadingMonomial p + leadingMonomial q) (p * q) = mleadingCoeff p * mleadingCoeff q := by
  by_cases hpq0 : p * q = 0
  · rw [hpq0]; simp_all
  classical rw [coeff_mul]
  rw [Finset.sum_eq_single (leadingMonomial p, leadingMonomial q)]
  · rfl
  · simp only [Finset.mem_antidiagonal, ne_eq, mul_eq_zero, Prod.forall, Prod.mk.injEq, not_and]
    intro m n hmn h
    rw [or_iff_not_imp_left, ← Ne, ← mem_support_iff]
    intro hm
    have := size_le_leadingMonomial_of_mem_support hm
    have := (size_add_le_size_add_right_iff (p := n)).2 this
    rw [hmn, size_add_le_size_add_left_iff] at this
    by_contra hnq
    rw [← Ne, ← mem_support_iff] at hnq
    have := size_injective (le_antisymm this (size_le_leadingMonomial_of_mem_support hnq))
    simp_all
  · simp

theorem leadingMonomial_mul (p q : MvPolynomial σ K) [Decidable (p * q = 0)] :
    leadingMonomial (p * q) = if (p * q) = 0 then 0 else
      leadingMonomial p + leadingMonomial q := by
  by_cases hpq0 : p * q = 0
  · simp [hpq0]
  simp only [hpq0, ↓reduceIte]
  apply size_injective
  refine le_antisymm ?_ ?_
  · rw [size_leadingMonomial_le_iff_forall_le]
    intro m hm
    classical rcases Finset.mem_add.1 (support_mul _ _ hm) with ⟨x, hx, y, hy, rfl⟩
    refine size_add_le_size_add ?_ ?_
    · exact size_le_leadingMonomial_of_mem_support hx
    · exact size_le_leadingMonomial_of_mem_support hy
  · refine size_le_leadingMonomial_of_mem_support ?_
    classical rw [mem_support_iff, coeff_leadingMonomial_add_mul]
    simp only [ne_eq, mul_eq_zero, not_or, ← mem_support_iff, mleadingCoeff]
    rw [mul_eq_zero, not_or] at hpq0
    exact ⟨leadingMonomial_mem_support hpq0.1, leadingMonomial_mem_support hpq0.2⟩

theorem mleadingCoeff_mul (p q : MvPolynomial σ K) : mleadingCoeff (p * q) =
    mleadingCoeff p * mleadingCoeff q := by
  classical
  rw [mleadingCoeff, leadingMonomial_mul]
  split_ifs with hpq
  · simp [hpq]; simp_all
  · rw [coeff_leadingMonomial_add_mul]

@[simp]
theorem norm_neg {p : MvPolynomial σ K} : norm (-p) = norm p := by
  simp [norm]

theorem norm_eq_ite (p : MvPolynomial σ K) [Decidable (p = 0)] :
    norm p = if p = 0 then (⊥ : WithBot α) else (size (leadingMonomial p) : α) := by
  simp [norm]
  split_ifs with hp0
  · simp_all
  · refine le_antisymm ?_ ?_
    · simp only [Finset.sup_le_iff, WithBot.coe_le_coe]
      intro m hm
      exact size_le_leadingMonomial_of_mem_support hm
    · refine (Finset.le_sup_iff (WithBot.bot_lt_coe _)).2 ?_
      use leadingMonomial p
      exact ⟨leadingMonomial_mem_support hp0, le_rfl⟩

theorem norm_sub_lt {p q : MvPolynomial σ K}
    (hp0 : p ≠ 0)
    (hm : leadingMonomial p = leadingMonomial q)
    (hc : mleadingCoeff p = mleadingCoeff q) :
    norm (p - q) < norm p := by
  have hq0 : q ≠ 0 := by rintro rfl; simp_all
  have hnpq : norm p = norm q := by classical simp_all [norm_eq_ite]
  by_cases hpq : p = q
  · simp [hpq, bot_lt_iff_ne_bot, hq0]
  refine lt_of_le_of_ne ?_ ?_
  · rw [sub_eq_add_neg]
    exact le_trans norm_add_le (by simp_all)
  · classical simp only [norm_eq_ite, sub_eq_zero, hpq, ↓reduceIte, hp0, WithBot.coe_lt_coe,
      gt_iff_lt]
    intro h
    have hp0 : p ≠ 0 := by rintro rfl; simp_all
    by_cases hpq : p = q
    · subst q; simp_all [@eq_comm _ ⊥]
    rw [WithBot.coe_inj, size_injective.eq_iff] at h
    simp only [mleadingCoeff] at hc
    have hpq : (p - q).coeff (leadingMonomial p) = 0 := by
      rw [coeff_sub, hc, hm, sub_self]
    have hp : (p - q).coeff (leadingMonomial p) ≠ 0 := by
      rw [← h, ← mem_support_iff]
      exact leadingMonomial_mem_support (by rwa [Ne, sub_eq_zero])
    exact hp hpq

/-- A Groebner set is a Groebner basis for its span. -/
structure IsGroebnerBasis (G : Set (MvPolynomial σ K)) : Prop where
  ( monomialIdeal_eq : monomialIdeal (Ideal.span G) = monomialIdeal G )

variable {size} {G : Set (MvPolynomial σ K)}

def IsReduced (G : Set (MvPolynomial σ K)) (p : MvPolynomial σ K) : Prop :=
  p = 0 ∨ ∀ g ∈ G, g ≠ 0 → ¬ leadingMonomial g ≤ leadingMonomial p

theorem IsGroebnerBasis_iff_monomialIdeal_eq :
    IsGroebnerBasis G ↔ monomialIdeal (Ideal.span G) = monomialIdeal G := by
  refine ⟨fun h => h.monomialIdeal_eq, fun h => ⟨h⟩⟩

theorem IsGroebnerBasis_iff_leadingMonomial_le :
    IsGroebnerBasis G ↔ ∀ f ∈ Ideal.span G, f ≠ 0 → ∃ g ∈ G, g ≠ 0 ∧
      leadingMonomial g ≤ leadingMonomial f := by
  simp only [Ideal.ext_iff, IsGroebnerBasis_iff_monomialIdeal_eq, mem_monomialIdeal_iff]
  refine ⟨?_, ?_⟩
  · intro h f hfI hf0
    classical
    exact (h (monomial (leadingMonomial f) 1)).1 (fun m hm => ⟨f, hfI, hf0, (by
      simp only [one_ne_zero, ↓reduceIte, Finset.mem_singleton, support_monomial] at hm
      rw [hm])⟩) (leadingMonomial f) (by simp)
  · intro h f
    refine ⟨?_, ?_⟩
    · intro h1 m hmf
      rcases h1 m hmf with ⟨g, hg, hg0, hgm⟩
      rcases h g hg hg0 with ⟨g', hg', hg0', hgg'⟩
      exact ⟨g', hg', hg0', le_trans hgg' hgm⟩
    · intro h1 m hmf
      rcases h1 m hmf with ⟨g, hg, hgm⟩
      exact ⟨g, Ideal.subset_span hg, hgm⟩

theorem IsGroebnerBasis_iff_isReduced_eq_zero  :
    IsGroebnerBasis G ↔ ∀ f ∈ Ideal.span G, IsReduced G f → f = 0 := by
  simp only [IsGroebnerBasis_iff_leadingMonomial_le, IsReduced]
  refine forall_congr' fun f => forall_congr' fun hf => ?_
  by_cases hf0 : f = 0
  · subst hf0; simp
  · simp [hf0]

variable (G)

@[simp]
theorem isReduced_zero : IsReduced G 0 := Or.inl rfl

/-- This means that `p` lead reduces to `q` in a single step.  -/
def IsSingleStepLeadReduction (p q : MvPolynomial σ K) : Prop :=
  ∃ g m x, g ∈ G ∧ q = p - monomial m x * g ∧ norm q < norm p

structure LeadReduction (p q : MvPolynomial σ K) : Type _ where
  ( toList : List (MvPolynomial σ K) )
  ( chain : toList.Chain (IsSingleStepLeadReduction G) p )
  ( last_eq : (p::toList).getLast (List.cons_ne_nil _ _) = q )

variable {G}

@[refl]
def LeadReduction.refl (p : MvPolynomial σ K) : LeadReduction G p p :=
  ⟨[], List.Chain.nil, rfl⟩

@[trans]
def LeadReduction.trans {p q r : MvPolynomial σ K} (l : LeadReduction G p q)
    (l' : LeadReduction G q r) : LeadReduction G p r := by
  rcases l' with ⟨l', hl', rfl⟩
  rcases l with ⟨l, hl, rfl⟩
  refine ⟨l ++ l', ?_, ?_⟩
  · induction l generalizing p with
    | nil => simpa
    | cons a l ih =>
      simp only [List.cons_append]
      rw [List.chain_cons] at hl
      exact List.Chain.cons hl.1 (ih hl.2 hl')
  · cases l' <;> simp

theorem LeadReduction.sub_mem_span {p q : MvPolynomial σ K} (l : LeadReduction G p q) :
    p - q ∈ Ideal.span G := by
  rcases l with ⟨l, hl, rfl⟩
  induction l generalizing p with
  | nil => simp
  | cons q l ih =>
    rw [List.chain_cons] at hl
    rw [← Ideal.add_mem_iff_left _ ((Ideal.neg_mem_iff _).2 (ih hl.2))]
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, List.getLast_cons]
    rcases hl.1 with ⟨g, m, x, hgG, rfl, hn⟩
    ring_nf
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span hgG)

@[simp]
theorem LeadReduction.mem_span_iff {p q : MvPolynomial σ K} {l : LeadReduction G p q} :
    p ∈ Ideal.span G ↔ q ∈ Ideal.span G := by
  rw [← Ideal.add_mem_iff_left _ ((Ideal.neg_mem_iff _).2 (sub_mem_span l)), ← l.last_eq]
  simp

open Pointwise

theorem mem_span_iff_mem_span_monomial {p : MvPolynomial σ K} :
    p ∈ Ideal.span G ↔ p ∈ Submodule.span K
      (Set.range (fun m : (σ →₀ ℕ) => monomial m (1 : K)) * G) := by
  have := Submodule.span_smul_of_span_eq_top (MvPolynomial.basisMonomials σ K).span_eq G
  simp only [coe_basisMonomials, smul_eq_mul, Ideal.submodule_span_eq, Submodule.ext_iff,
    Submodule.restrictScalars_mem] at this
  simp [this]

section

attribute [local instance] WellFoundedLT.toWellFoundedRelation

theorem exists_leadReduction [WellFoundedLT α] : ∀ p : MvPolynomial σ K,
    ∃ (q : MvPolynomial σ K) (_l : LeadReduction G p q), IsReduced G q := by
  intro p
  by_cases hp : IsReduced G p
  · exact ⟨p, LeadReduction.refl p, hp⟩
  · simp only [IsReduced, ne_eq, not_or, not_forall, Classical.not_imp, Decidable.not_not] at hp
    rcases hp.2 with ⟨g, hg, hg0, hgp⟩
    let k := (p -
      monomial (leadingMonomial p - leadingMonomial g) (mleadingCoeff p / mleadingCoeff g) * g)
    have wf : norm k < norm p := by
      refine norm_sub_lt ?_ ?_ ?_
      · rintro rfl; simp_all
      · classical rw [leadingMonomial_mul]
        split_ifs
        simp_all
        classical rw [leadingMonomial_monomial]
        split_ifs
        simp_all
        simp_all
        rw [tsub_add_cancel_of_le hgp]
      · rw [mleadingCoeff_mul, mleadingCoeff_monomial]
        rw [div_mul_cancel₀]
        simpa
    rcases exists_leadReduction k with ⟨q, l, hq⟩
    refine ⟨q, ?_, hq⟩
    refine ⟨k::l.toList, ?_, ?_⟩
    · rw [List.chain_cons]
      refine ⟨?_, l.2⟩
      refine ⟨g, _, _, hg, rfl, wf⟩
    · simp [l.3]
  termination_by p => norm p

open Relation

theorem exists_leadingMonomial_mem_eqvGen_leadReduction [WellFoundedLT α] {p : MvPolynomial σ K}
     (G : Set (MvPolynomial σ K)) (hp : p ∈ Ideal.span G) : ∃ (q : MvPolynomial σ K), norm p = norm q ∧
       Relation.EqvGen (fun p q => Nonempty (LeadReduction G p q)) q 0 := by
  rw [mem_span_iff_mem_span_monomial] at hp
  rcases Submodule.mem_span_finite_of_mem_span hp with ⟨s, hsG, hsp⟩
  induction s using Finset.induction_on generalizing p with
  | empty =>
    refine ⟨0, ?_⟩
    simp_all only [Finset.coe_empty, Submodule.span_empty, Submodule.mem_bot, norm_zero, true_and]
    exact EqvGen.refl _
  | @insert a s has ih =>
    simp only [← Ideal.submodule_span_eq, Finset.coe_insert, Submodule.mem_span_insert] at hsp
    rcases hsp with ⟨x, y, hy, rfl⟩
    simp only [Finset.coe_insert, Set.insert_subset_iff, Set.mem_mul, Set.mem_range,
      exists_exists_eq_and] at hsG
    rcases hsG.1 with ⟨m, g, hg, rfl⟩
    replace hsG := hsG.2
    simp only [← smul_mul_assoc, smul_monomial, smul_eq_mul, mul_one] at hp ⊢
    have hxy : norm (monomial m x * g + y) ≤ max (norm (monomial m x * g)) (norm y) := norm_add_le
    rcases ih (Submodule.span_mono hsG hy) hsG hy with ⟨q, hq, hqe⟩
    rcases lt_or_eq_of_le hxy with hxy | hxy
    · refine ⟨(monomial m x) * g + q, ?_, ?_⟩
      · admit
      · refine EqvGen.trans _ _ _ ?_ hqe
        refine EqvGen.rel _ _ ⟨?_⟩
        refine ⟨[q], ?_, by simp⟩
        simp only [List.chain_cons, IsSingleStepLeadReduction, ne_eq, List.Chain.nil, and_true]
        use g, hg
        ring_nf




    · admit

end



end MonomialOrder

end MvPolynomial
