import QuantElim.Poly.Zeros
import QuantElim.QuantFreeFormula.Basic
import QuantElim.forMathlib

variable {n : ℕ}

-- Invariants to maintain. No constant polys in any list. Eqs has smallest by lex leadingMon degree at head
structure Ands (n : ℕ) : Type where
  (eqs : List (Poly n))
  (neq : Poly n)
  deriving DecidableEq

namespace Ands

def eval {n : ℕ} (φ : Ands n) : Set (Fin n → ℂ) :=
  { x | (∀ p ∈ φ.eqs, p.eval x = 0) ∧ (φ.neq.eval x ≠ 0) }

def sumDegs (φ : Ands n) : ℕ :=
  List.sum <| φ.eqs.map Poly.natDegree

def and (φ ψ : Ands n) : Ands n :=
  { eqs := φ.eqs ++ ψ.eqs,
    neq := lcm φ.neq ψ.neq }

@[simp]
def eval_and (φ ψ : Ands n) :
    (φ.and ψ).eval = φ.eval ∩ ψ.eval := by
  ext x
  simp [eval, and, forall_and, or_imp]
  tauto

protected def true (n : ℕ) : Ands n :=
  { eqs := [],
    neq := 1 }

@[simp]
theorem eval_true : (Ands.true n).eval = Set.univ := by
  simp [eval, Ands.true]

protected def false (n : ℕ) : Ands n :=
  { eqs := [],
    neq := 0 }

@[simp]
theorem eval_false : (Ands.false n).eval = ∅ := by
  simp [eval, Ands.false]

open Poly QuantFreeFormula

def toQuantFreeFormula (φ : Ands n) : QuantFreeFormula n :=
  (φ.eqs.foldr (fun p ψ => (eqZero p).and ψ) tru).and (neZero φ.neq)

@[simp]
theorem eval_toQuantFreeFormula (φ : Ands n) :
    φ.toQuantFreeFormula.eval = φ.eval := by
  rcases φ with ⟨eqs, neq⟩
  ext x
  simp only [toQuantFreeFormula, QuantFreeFormula.eval_and, QuantFreeFormula.eval, Set.inter_empty,
    ne_eq, Set.inter_univ, Set.empty_union, Set.mem_inter_iff, Set.mem_setOf_eq, eval,
    and_congr_left_iff]
  intro h
  induction eqs with
  | nil => simp
  | cons p ps ih => simp [ih]

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

theorem sumDegs_reduceWithCaseSplit_fst {n : ℕ} {φ : Ands (n+1)} {i : Fin φ.eqs.length}
    (h : ∃ j, i ≠ j ∧ (φ.eqs[i]).degree ≤ (φ.eqs[j]).degree)
    (h₁ : 0 < (φ.eqs[i]).degree) :
    (reduceWithCaseSplit φ i).1.sumDegs < φ.sumDegs := by
  simp only [reduceWithCaseSplit, sumDegs_insertNeq]
  rcases h with ⟨j, hij, h₂⟩
  exact sumDegs_reduceWith hij h₁ h₂

theorem sumDegs_reduceWithCaseSplit_snd {n : ℕ} {φ : Ands (n+1)} {i : Fin φ.eqs.length}
    (h₁ : 0 < (φ.eqs[i]).degree) :
    (reduceWithCaseSplit φ i).2.sumDegs < φ.sumDegs := by
  simp only [reduceWithCaseSplit, List.get_eq_getElem, sumDegs_insertEq, natDegree_const, add_zero]
  exact sumDegs_eraseLeadAt h₁

def toPolyEqZero (p : Poly (n+1)) : Ands n where
  eqs := (List.range (p.natDegree+1)).map p.coeff
  neq := 1

@[simp]
theorem eval_toPolyEqZero : ∀ (p : Poly (n+1)), (toPolyEqZero p).eval =
    { x | toPoly ℂ x p = 0 } := fun p => by
  simp only [toPolyEqZero, eval, List.forall_mem_map, List.mem_range, map_one,
    ne_eq, one_ne_zero, not_false_eq_true, and_true]
  simp only [Nat.lt_add_one_iff, Set.ext_iff, Set.mem_setOf_eq, Polynomial.ext_iff,
    Polynomial.coeff_zero]
  intro x
  refine ⟨?_, ?_⟩
  · intro h i
    by_cases hi : i ≤ p.natDegree
    · rw [toPoly_coeff]
      rw [h i hi]
    · apply Polynomial.coeff_eq_zero_of_natDegree_lt
      refine lt_of_le_of_lt (natDegree_toPoly_le) (lt_of_not_le hi)
  · intro h i _
    simp only [toPoly_coeff] at h
    exact h i

def toPolyNeZero (p : Poly (n+1)) : QuantFreeFormula n :=
  iOrs (List.range (p.natDegree+1)) (fun i => neZero (p.coeff i))

@[simp]
theorem eval_toPolyNeZero (p : Poly (n+1)) : (toPolyNeZero p).eval =
    { x | toPoly ℂ x p ≠ 0 } := by
  simp [toPolyNeZero, Set.ext_iff]
  intro x
  rw [← not_iff_not]; simp only [not_exists, not_and, Decidable.not_not]
  simp only [Nat.lt_add_one_iff, Set.ext_iff, Set.mem_setOf_eq, Polynomial.ext_iff,
    Polynomial.coeff_zero]
  refine ⟨?_, ?_⟩
  · intro h i
    by_cases hi : i ≤ p.natDegree
    · rw [toPoly_coeff]
      rw [h i hi]
    · apply Polynomial.coeff_eq_zero_of_natDegree_lt
      refine lt_of_le_of_lt (natDegree_toPoly_le) (lt_of_not_le hi)
  · intro h i _
    simp only [toPoly_coeff] at h
    exact h i

def toPolyDivides : ∀ (p _q : Poly (n+1)), QuantFreeFormula n := fun p q =>
  if hp0 : p = 0 then (toPolyEqZero q).toQuantFreeFormula
  else have : degree p.eraseLead < p.degree := degree_eraseLead_lt hp0
      ((toPolyEqZero (pMod q p)).insertNeq p.leadingCoeff).toQuantFreeFormula.or
      ((toPolyDivides (p.eraseLead) q).and (toPolyEqZero (const p.leadingCoeff)).toQuantFreeFormula)
  termination_by p => p.degree

theorem eval_toPolyDivides : ∀ (p q : Poly (n+1)),
    (toPolyDivides p q).eval = { x | toPoly ℂ x p ∣ toPoly ℂ x q } := fun p q =>
  if hp0 : p = 0 then by rw [toPolyDivides]; simp [hp0]
  else by
    have : degree p.eraseLead < p.degree := degree_eraseLead_lt hp0
    have ih := eval_toPolyDivides (p.eraseLead) q
    rw [toPolyDivides, dite_cond_eq_false (eq_false_intro hp0)]
    dsimp only
    simp [ih]
    ext x
    by_cases hpl : p.leadingCoeff.eval x = 0
    · simp [hpl, eraseLead]
    · simp [hpl, toPoly_pMod_eq_zero_iff hpl]
  termination_by p => p.degree

def elimConstantPolys (φ : Ands (n+1)) (i : Fin φ.eqs.length) : QuantFreeFormula n × Poly (n+1) × Poly (n+1) :=
  (QuantFreeFormula.iAnds (List.finRange φ.eqs.length)
    fun j => if j = i then tru else eqZero ((φ.eqs[j]).eval (Fin.cases 0 Poly.X)), φ.eqs[i], φ.neq)

@[simp]
theorem eval_elimConstantPolys (φ : Ands (n+1)) (i : Fin φ.eqs.length)
    (h : ∀ j ≠ i, (φ.eqs.get j).degree ≤ 0) :
    let (ψ, p, q) := elimConstantPolys φ i
    {x | ∃ y : ℂ, (Fin.cons y x) ∈ φ.eval } = ψ.eval ∩ { x | ∃ y : ℂ, p.eval (Fin.cons y x) = 0 ∧
      q.eval (Fin.cons y x) ≠ 0 } := by
  rcases φ with ⟨eqs, neq⟩
  simp only [elimConstantPolys, Fin.getElem_fin, eval_iAnds, List.mem_map, QuantFreeFormula.eval,
    Set.inter_univ, ne_eq, Set.inter_empty, Set.union_empty, Set.iInter_exists, Set.biInter_and',
    Set.iInter_iInter_eq_right, Set.ext_iff, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  simp only [eval, ne_eq, Set.mem_setOf_eq]
  intro x
  refine ⟨?_, ?_⟩
  · rintro ⟨y, hy⟩
    refine ⟨?_, ⟨y, ?_⟩⟩
    · intro j _
      split_ifs with hij; simp
      simp only [QuantFreeFormula.eval, Set.inter_univ, ne_eq, Set.inter_empty, Set.union_empty,
        Set.mem_setOf_eq]
      rcases degree_le_zero_iff.1 (h j hij) with ⟨c, hc⟩
      simp only [List.get_eq_getElem] at hc
      erw [hc, eval_const, apply_eval, ← hy.1 (eqs[j]) (by simp), hc, eval_const]
      congr; ext k
      simp
    · refine ⟨?_, hy.2⟩
      erw [hy.1 (eqs[i]) (by simp)]
  · rintro ⟨h0, y, hy⟩
    use y
    refine ⟨?_, hy.2⟩
    intro p hp
    have := h0 ⟨List.indexOf p eqs, List.indexOf_lt_length.2 hp⟩ (by simp)
    split_ifs at this with hi
    · subst hi
      simp only [List.getElem_indexOf] at hy
      exact hy.1
    · simp at this
      rcases degree_le_zero_iff.1 (h _ hi) with ⟨c, hc⟩
      simp only [List.get_eq_getElem, List.getElem_indexOf] at hc
      subst hc
      rw [← this]
      simp [apply_eval]

/-- Elimates a Quantifier from formulas where exactly one polynomial in `φ.eqs` has positive degree -/
def elimOneNonZeroDegree (φ : Ands (n+1)) (i : Fin φ.eqs.length) : QuantFreeFormula n :=
  let p := φ.eqs.get i
  let dp := (φ.eqs.get i).deriv
  (elimConstantPolys φ i).1.and <|
  (toPolyDivides p (dp * φ.neq)).not.or ((toPolyEqZero p).toQuantFreeFormula.and (toPolyNeZero φ.neq))

theorem eval_elimOneNonZeroDegree {φ : Ands (n+1)} {i : Fin φ.eqs.length}
    (h : ∀ j ≠ i, (φ.eqs.get j).degree ≤ 0) :
    (elimOneNonZeroDegree φ i).eval = {x | ∃ y : ℂ, (Fin.cons y x) ∈ φ.eval } := by
  have := eval_elimConstantPolys φ i h
  dsimp only at this
  rw [this, elimOneNonZeroDegree, QuantFreeFormula.eval_and]; clear this
  congr
  simp only [List.get_eq_getElem, eval_or, eval_not, eval_toPolyDivides, map_mul,
    QuantFreeFormula.eval_and, eval_toQuantFreeFormula, eval_toPolyEqZero, eval_toPolyNeZero, ne_eq,
    Set.ext_iff, Set.mem_union, Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_inter_iff]
  intro x
  simp only [eval_cons_eq_toPoly_eval, Polynomial.key_exists, ← toPoly_deriv,
    elimConstantPolys]
  rfl

/-- Eliminate quantifiers from a formula where all the `eqs` have degree 0 -/
def elimZeroDegrees (φ : Ands (n+1)) : QuantFreeFormula n :=
    (iAnds φ.eqs (fun i => (toPolyEqZero i).toQuantFreeFormula)).and (toPolyNeZero φ.neq)

theorem eval_elimZeroDegrees (φ : Ands (n+1)) (h : ∀ p ∈ φ.eqs, p.degree ≤ 0) :
    (elimZeroDegrees φ).eval = { x | ∃ y : ℂ, (Fin.cons y x) ∈ φ.eval } := by
  rcases φ with ⟨eqs, neq⟩
  simp only [elimZeroDegrees, QuantFreeFormula.eval_and, eval_iAnds, eval_toQuantFreeFormula,
    eval_toPolyEqZero, eval_toPolyNeZero, ne_eq, Set.ext_iff, Set.mem_inter_iff, Set.mem_iInter,
    Set.mem_setOf_eq]
  simp only at h
  simp only [eval, ne_eq, Set.mem_setOf_eq, eval_cons_eq_toPoly_eval]
  intro x
  refine ⟨?_, ?_⟩
  · intro h1
    rcases Finset.exists_not_mem ((toPoly ℂ x) neq).roots.toFinset with ⟨y, hy⟩
    use y
    simp only [Multiset.mem_toFinset, Polynomial.mem_roots', ne_eq, Polynomial.IsRoot.def,
      not_and] at hy
    simp only [hy h1.2, not_false_iff, and_true]
    intro p hp
    rw [h1.1 p hp, Polynomial.eval_zero]
  · rintro ⟨y, hy⟩
    refine ⟨?_, ?_⟩
    · intro p hp
      rcases degree_le_zero_iff.1 (h p hp) with ⟨c, hc⟩
      have := hy.1 p hp
      subst hc
      simp_all
    · intro h; simp_all

inductive Idxs (φ : Ands n) : Type
  | none : (∀ p ∈ φ.eqs, p.degree ≤ 0) → Idxs φ
  | one : (i : Fin φ.eqs.length) → 0 < (φ.eqs[i]).degree → (∀ j ≠ i, (φ.eqs[j]).degree ≤ 0) → Idxs φ
  | two : (i j : Fin φ.eqs.length) → (hij : i ≠ j) → 0 < (φ.eqs[i]).degree → (φ.eqs[i]).degree ≤ (φ.eqs[j]).degree → Idxs φ

def getIdxs (φ : Ands n) : Idxs φ := by
  rcases φ with ⟨eqs, neq⟩
  induction eqs with
  | nil => exact Idxs.none (by simp)
  | cons p eqs ih =>
    by_cases h : p.degree ≤ 0
    · match ih with
      | Idxs.none h => exact Idxs.none (by simp_all)
      | Idxs.one i h₁ h₂ =>
        refine Idxs.one i.succ h₁ ?_
        intro j hj
        simp at h₂ ⊢
        induction j using Fin.cases with
        | zero => simpa
        | succ j => simpa using h₂ j (mt (congr_arg _) hj)
      | Idxs.two i j hij h₁ h₂ =>
        refine Idxs.two i.succ j.succ (by simpa) h₁ h₂
    · rw [not_le] at h
      match ih with
      | Idxs.none h1 =>
        refine Idxs.one (by dsimp; exact 0) (by simpa) ?_
        intro j hj
        induction j using Fin.cases with
        | zero => simp_all
        | succ j => simp; exact h1 _ (by simp)
      | Idxs.one i h₁ h₂ =>
        simp at *
        by_cases hij : degree (eqs[i]) ≤ degree p
        · refine Idxs.two i.succ (by dsimp; exact 0) (by simp [Fin.succ_ne_zero]) h₁ (by simpa)
        · refine Idxs.two (by dsimp; exact 0) i.succ (Ne.symm (Fin.succ_ne_zero _))
            (by simpa) (le_of_not_le (by simpa using hij))
      | Idxs.two i j hij h₁ h₂ =>
        simp at *
        by_cases hij : degree (eqs[i]) ≤ degree p
        · refine Idxs.two i.succ (by dsimp; exact 0) (Fin.succ_ne_zero _) h₁ (by simpa)
        · refine Idxs.two (by dsimp; exact 0) i.succ (Fin.succ_ne_zero _).symm
            (by simpa) (le_of_not_le (by simpa using hij))

open Idxs

def elimQuant : ∀ (φ : Ands (n+1)),
  { ψ : QuantFreeFormula n // ψ.eval = { x | ∃ y : ℂ, (Fin.cons y x) ∈ φ.eval } } := fun φ =>
  match getIdxs φ with
  | Idxs.none h => ⟨elimZeroDegrees φ, by
    rw [eval_elimZeroDegrees]
    simpa using h⟩
  | Idxs.one i h₁ h₂ => ⟨elimOneNonZeroDegree φ i, by rw [eval_elimOneNonZeroDegree h₂]⟩
  | Idxs.two i j hij h₁ h₂ =>
    let ψ := reduceWithCaseSplit φ i
    have wf₁ := sumDegs_reduceWithCaseSplit_fst ⟨j, hij, h₂⟩ h₁
    have wf₂ := sumDegs_reduceWithCaseSplit_snd h₁
    ⟨(elimQuant ψ.1).1.or (elimQuant ψ.2).1, by
      rw [QuantFreeFormula.eval_or, (elimQuant ψ.1).2, (elimQuant ψ.2).2]
      ext x
      conv_rhs => rw [← eval_reduceWithCaseSplit φ i]
      simp [ψ, exists_or]⟩
  termination_by φ => sumDegs φ

end Ands
