import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.Polynomial.Derivative

namespace Polynomial

open Polynomial

variable {K : Type*} [Field K]

theorem Splits.dvd_of_roots_le_roots {p q : K[X]} (hp : p.Splits (RingHom.id _)) (hp0 : p ≠ 0)
    (hq : p.roots ≤ q.roots) : p ∣ q := by
  by_cases hq0 : q = 0
  · simp [hq0]
  · rw [eq_prod_roots_of_splits_id hp, C_mul_dvd (leadingCoeff_ne_zero.2 hp0)]
    exact dvd_trans (Multiset.prod_dvd_prod_of_le
           (Multiset.map_le_map hq)) (prod_multiset_X_sub_C_dvd _)

theorem Splits.dvd_iff_roots_le_roots {p q : K[X]}
    (hp : p.Splits (RingHom.id _)) (hp0 : p ≠ 0) (hq0 : q ≠ 0) :
    p ∣ q ↔ p.roots ≤ q.roots := by
  refine ⟨?_, Splits.dvd_of_roots_le_roots hp hp0⟩
  · rintro ⟨r, rfl⟩
    rw [roots_mul hq0]; exact le_add_right le_rfl

theorem rootMultiplicity_derivative {R : Type*} [CommRing R] [CharZero R] [IsDomain R]
    {p : R[X]} {t : R} (hpt : Polynomial.IsRoot p t) :
    (derivative p).rootMultiplicity t = p.rootMultiplicity t - 1 := by
  by_cases hp0 : p = 0
  · simp [hp0]
  · exact derivative_rootMultiplicity_of_root_of_mem_nonZeroDivisors hpt
      (mem_nonZeroDivisors_iff_ne_zero.2 (Nat.cast_ne_zero.2 (Nat.ne_zero_iff_zero_lt.2
        ((rootMultiplicity_pos hp0).2 hpt))))

theorem key_one_way {R : Type*} [CommRing R] [IsDomain R] [CharZero R] {f g : R[X]} (hf0 : f ≠ 0)
    (hfd : f ∣ f.derivative * g) : ∀ x, f.eval x = 0 → g.eval x = 0 := by
  intro a haf
  rcases hfd with ⟨r, hr⟩
  by_cases hdf0 : derivative f = 0
  · have := natDegree_eq_zero_of_derivative_eq_zero hdf0
    rw [eq_C_of_derivative_eq_zero hdf0] at haf
    simp only [eval_C, derivative_C, zero_mul, dvd_zero, iff_true] at haf
    refine False.elim (hf0 (Polynomial.ext ?_))
    intro n
    cases n
    · rw [haf]; simp
    · rw [eq_C_of_derivative_eq_zero hdf0]; simp
  by_contra hg
  have hdfg0 : f.derivative * g ≠ 0 := mul_ne_zero hdf0 (by rintro rfl; simp_all)
  have hr' := congr_arg (rootMultiplicity a) hr
  rw [rootMultiplicity_mul hdfg0, derivative_rootMultiplicity_of_root haf,
    rootMultiplicity_eq_zero hg, add_zero, rootMultiplicity_mul (hr ▸ hdfg0), add_comm,
    Nat.sub_eq_iff_eq_add (Nat.succ_le_iff.2 ((rootMultiplicity_pos hf0).2 haf))] at hr'
  refine lt_irrefl (rootMultiplicity a f) ?_
  refine lt_of_lt_of_le (Nat.lt_succ_self _)
    (le_trans (le_add_of_nonneg_left (Nat.zero_le (rootMultiplicity a r))) ?_)
  conv_rhs => rw [hr']
  simp [add_assoc]

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

theorem key {f g : K[X]} (hf0 : f ≠ 0) :
    (∀ x, f.eval x = 0 → g.eval x = 0) ↔ f ∣ f.derivative * g := by
  refine ⟨?_, key_one_way hf0⟩
  by_cases hg0 : g = 0
  · simp [hg0]
  by_cases hdf0 : derivative f = 0
  · rw [eq_C_of_derivative_eq_zero hdf0]
    simp only [eval_C, derivative_C, zero_mul, dvd_zero, implies_true]
  have hdg :  f.derivative * g ≠ 0 := mul_ne_zero hdf0 hg0
  classical rw [Splits.dvd_iff_roots_le_roots (IsAlgClosed.splits f) hf0 hdg, Multiset.le_iff_count]
  simp only [count_roots, rootMultiplicity_mul hdg]
  refine forall_imp fun a => ?_
  by_cases haf : f.eval a = 0
  · have h0 : 0 < f.rootMultiplicity a := (rootMultiplicity_pos hf0).2 haf
    rw [derivative_rootMultiplicity_of_root haf]
    intro h
    calc rootMultiplicity a f
        = rootMultiplicity a f - 1 + 1 := (Nat.sub_add_cancel (Nat.succ_le_iff.1 h0)).symm
      _ ≤ rootMultiplicity a f - 1 + rootMultiplicity a g := add_le_add le_rfl (Nat.succ_le_iff.1
        ((rootMultiplicity_pos hg0).2 (h haf)))
  · simp [haf, rootMultiplicity_eq_zero haf]

theorem key_forall {f g : K[X]} :
     (∀ x, f.eval x = 0 → g.eval x = 0) ↔ f ∣ f.derivative * g ∧ (f = 0 → g = 0) := by
  by_cases hf0 : f = 0
  · simp only [hf0, eval_zero, forall_const, derivative_zero, zero_mul, dvd_refl, true_and]
    exact ⟨zero_of_eval_zero _, by rintro rfl; simp⟩
  · rw [key hf0]
    simp [hf0]

theorem key_exists {f g : K[X]} :
    (∃ x, f.eval x = 0 ∧ g.eval x ≠ 0) ↔ ((¬ (f ∣ f.derivative * g) ∨ (f = 0 ∧ g ≠ 0)) ):= by
  simp only [← not_forall_not, not_and_not_right, key_forall]; tauto

theorem square_free_key {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    {f g a : R[X]} {hf0 : f ≠ 0} (hgf : g * a = f) (hgdf : g ∣ f.derivative) :
    (∀ x, f.eval x = 0 ↔ a.eval x = 0) := by
  have hg0 : g ≠ 0 := by rintro rfl; simp_all
  subst hgf
  rw [derivative_mul, dvd_add_left (dvd_mul_right _ _)] at hgdf
  have := key_one_way hg0 hgdf
  simpa only [eval_mul, mul_eq_zero, or_iff_right_iff_imp]

end Polynomial
