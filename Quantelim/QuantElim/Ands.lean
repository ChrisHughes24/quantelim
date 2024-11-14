import QuantElim.Poly.Zeros

variable {n : ℕ}

-- Invariants to maintain. No constant polys in any list. Eqs has smallest by lex leadingMon degree at head
structure Ands (n : ℕ) : Type where
  (eqs : List (Poly n))
  (neq : Poly n)
  deriving DecidableEq

def Ands.eval {n : ℕ} (φ : Ands n) : Set (Fin n → ℂ) :=
  { x | (∀ p ∈ φ.eqs, p.eval x = 0) ∧ (φ.neq.eval x ≠ 0) }

def Ands.sumDegs (φ : Ands n) : ℕ :=
  List.sum <| φ.eqs.map Poly.natDegree

-- none is `True`, false is `some []`
structure QuantFreeFormula (n : ℕ) where
  toList : Option (List (Ands n))

def QuantFreeFormula.eval {n : ℕ} (φ : QuantFreeFormula n) : Set (Fin n → ℂ) :=
  { x | ∀ l ∈ φ.toList, ∃ a ∈ l, x ∈ Ands.eval a }

namespace Ands

open Poly QuantFreeFormula

def and (φ ψ : Ands n) : Ands n :=
  { eqs := φ.eqs ++ ψ.eqs,
    neq := lcm φ.neq ψ.neq }

def eval_and (φ ψ : Ands n) :
    (φ.and ψ).eval = φ.eval ∩ ψ.eval := by
  ext x
  simp [eval, and, forall_and, or_imp]
  tauto

def reduceWith (φ : Ands (n+1)) (i : Fin φ.eqs.length) : Ands (n + 1) where
  eqs := φ.eqs.mapIdx (fun j p => if i = j then p else pMod p (φ.eqs[i]))
  neq := φ.neq

theorem mem_reduceWith {φ : Ands (n+1)} {i : Fin φ.eqs.length}
    {x : Fin (n+1) → ℂ} (hx : (φ.eqs[i]).leadingCoeff.eval (fun i => x i.succ) ≠ 0) :
    x ∈ (φ.reduceWith i).eval ↔ x ∈ φ.eval := by
  simp only [eval, reduceWith, Fin.getElem_fin, List.get_eq_getElem,
    forall_exists_index, ne_eq, Set.mem_setOf_eq, List.forall_mem_iff_getElem,
    List.length_mapIdx, List.getElem_mapIdx]
  simp only [Fin.getElem_fin, ne_eq] at hx
  refine ⟨?_, ?_⟩
  · intro h
    have := h.1 i i.prop
    simp only [↓reduceIte] at this
    simp only [h.2, not_false_eq_true, and_true]
    intro j hj
    replace h := h.1 j hj
    split_ifs at h
    · assumption
    · rwa [eval_pMod_eq_zero hx this] at h
  · intro h
    have := h.1 i i.prop
    simp only [↓reduceIte] at this
    simp only [h.2, not_false_eq_true, and_true]
    intro j hj
    replace h := h.1 j hj
    split_ifs
    · assumption
    · rwa [eval_pMod_eq_zero hx this]

theorem sumDegs_le_of_forall_le {φ ψ : Ands n}
    (h₁ : φ.eqs.length = ψ.eqs.length)
    (h : ∀ i : Fin φ.eqs.length, (φ.eqs[i]).natDegree ≤ (ψ.eqs[i]).natDegree) :
    φ.sumDegs ≤ ψ.sumDegs := by
  unfold sumDegs
  rw [← Fin.sum_univ_get', ← Fin.sum_univ_get', ← Fin.sum_congr' _ h₁]
  exact Finset.sum_le_sum fun i hi => h i

theorem sumDegs_lt_of_forall_le_of_lt {φ ψ : Ands n}
    (h₁ : φ.eqs.length = ψ.eqs.length)
    (h : ∀ i : Fin φ.eqs.length, (φ.eqs[i]).natDegree ≤ (ψ.eqs[i]).natDegree)
    (h₂ : ∃ i : Fin φ.eqs.length, (φ.eqs[i]).natDegree < (ψ.eqs[i]).natDegree) :
    φ.sumDegs < ψ.sumDegs := by
  unfold sumDegs
  rw [← Fin.sum_univ_get', ← Fin.sum_univ_get', ← Fin.sum_congr' _ h₁]
  exact Finset.sum_lt_sum (fun i hi => h i) (by simpa)

theorem sumDegs_reduceWith {φ : Ands (n+1)} {i j : Fin φ.eqs.length}
    (hij : i ≠ j)
    (h₁ : 0 < (φ.eqs[i]).degree)
    (h₂ : (φ.eqs[i]).degree ≤ (φ.eqs[j]).degree) :
    (φ.reduceWith i).sumDegs < φ.sumDegs := by
  refine sumDegs_lt_of_forall_le_of_lt ?_ ?_ ?_
  · simp [reduceWith]
  · intro k
    dsimp [reduceWith]
    erw [List.getElem_mapIdx]
    split_ifs
    · rfl
    · exact natDegree_pMod_le_left
  · use Fin.cast (by simp [reduceWith]) j
    dsimp [reduceWith]
    erw [List.getElem_mapIdx]
    simp only [Fin.val_ne_of_ne hij, ↓reduceIte]
    exact lt_of_lt_of_le (natDegree_pMod_lt h₁)
      (natDegree_le_natDegree_of_degree_le_degree h₂)

def eraseLeadAt (φ : Ands (n+1)) (i : Fin φ.eqs.length) : Ands (n+1) where
  eqs := φ.eqs.modify Poly.eraseLead i
  neq := φ.neq

theorem mem_eraseLeadAt {φ : Ands (n+1)} {i : Fin φ.eqs.length}
    {x : Fin (n+1) → ℂ} (hx : (φ.eqs[i]).leadingCoeff.eval (fun i => x i.succ) = 0) :
    x ∈ (φ.eraseLeadAt i).eval ↔ x ∈ φ.eval := by
  simp only [eval, eraseLeadAt, ne_eq, Set.mem_setOf_eq, and_congr_left_iff]
  intro h
  rw [List.forall_mem_iff_getElem, List.forall_mem_iff_getElem]
  simp only [List.length_modify]
  apply forall_congr'; intro j; apply forall_congr'; intro hi
  rw [List.getElem_modify]
  split_ifs with hij
  · subst hij
    simp only [Fin.getElem_fin] at hx
    simp [eraseLead, map_sub, map_mul, eval_const, map_pow, eval_X, hx]
  · rfl

theorem sumDegs_eraseLeadAt {φ : Ands (n+1)} {i : Fin φ.eqs.length}
    (h : 0 < (φ.eqs[i]).degree) :
    (φ.eraseLeadAt i).sumDegs < φ.sumDegs := by
  have h0 : (φ.eqs[i]) ≠ 0 := by intro h; simp_all
  refine sumDegs_lt_of_forall_le_of_lt ?_ ?_ ?_
  · simp [eraseLeadAt]
  · intro j
    simp only [eraseLeadAt]
    erw [List.getElem_modify]
    split_ifs with hij
    · exact natDegree_le_natDegree_of_degree_le_degree (le_of_lt
        (degree_eraseLead_lt (by convert h0; simp [hij])))
    · exact le_rfl
  · use Fin.cast ?_ i
    · simp only [eraseLeadAt]
      erw [List.getElem_modify]
      simp only [List.length_modify, Fin.coe_cast, ↓reduceIte, Fin.getElem_fin]
      exact natDegree_lt_natDegree_of_degree_lt_degree_of_pos h
        (degree_eraseLead_lt h0)
    · simp [eraseLeadAt]

def insertEq (φ : Ands n) (p : Poly n) : Ands n :=
  { eqs := p :: φ.eqs,
    neq := φ.neq }

@[simp]
theorem sumDegs_insertEq (φ : Ands n) (p : Poly n) : (φ.insertEq p).sumDegs = φ.sumDegs + p.natDegree := by
  simp [sumDegs, insertEq, add_comm]

@[simp]
theorem eval_insertEq (φ : Ands n) (p : Poly n) :
    (φ.insertEq p).eval = φ.eval ∩ {x | p.eval x = 0} := by
  simp only [eval, insertEq, Set.ext_iff, List.forall_mem_cons]
  simp; tauto

def insertNeq (φ : Ands n) (p : Poly n) : Ands n :=
  { eqs := φ.eqs,
    neq := lcm φ.neq p }

@[simp]
theorem sumDegs_insertNeq (φ : Ands n) (p : Poly n) : (φ.insertNeq p).sumDegs = φ.sumDegs := rfl

@[simp]
theorem eval_insertNeq (φ : Ands n) (p : Poly n) :
    (φ.insertNeq p).eval = φ.eval ∩ {x | p.eval x ≠ 0} := by
  simp [eval, insertNeq, Set.ext_iff, Set.mem_setOf_eq, Set.mem_inter_iff, Ne,
   and_assoc]

def reduceWithCaseSplit {n : ℕ} (φ : Ands (n+1)) (i : Fin φ.eqs.length) : Ands (n+1) × Ands (n+1) :=
  let nonZeroCase := (φ.reduceWith i).insertNeq (const (φ.eqs.get i).leadingCoeff)
  let zeroCase := (φ.eraseLeadAt i).insertEq (const (φ.eqs.get i).leadingCoeff)
  (nonZeroCase, zeroCase)

theorem eval_reduceWithCaseSplit {n : ℕ} (φ : Ands (n+1)) (i : Fin φ.eqs.length) :
    (reduceWithCaseSplit φ i).1.eval ∪ (reduceWithCaseSplit φ i).2.eval = φ.eval := by
  simp only [reduceWithCaseSplit, QuantFreeFormula.eval, Option.mem_def,
    Option.some.injEq, forall_eq', List.exists_mem_cons_iff,
    List.mem_nil_iff, false_and, exists_false, or_false, eval_insertNeq,
    eval_insertEq]
  apply Set.ext fun x => ?_
  simp only [List.get_eq_getElem, eval_const, ne_eq, Set.mem_inter_iff, Set.mem_setOf_eq]
  by_cases h : (φ.eqs[(i : ℕ)]).leadingCoeff.eval (fun i => x i.succ) = 0
  · simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq, h, not_true_eq_false, and_false,
      mem_eraseLeadAt h, and_true, false_or]
  · simp only [Set.mem_union, Set.mem_inter_iff, mem_reduceWith h, Set.mem_setOf_eq, h,
      not_false_eq_true, and_true, and_false, or_false]

end Ands
