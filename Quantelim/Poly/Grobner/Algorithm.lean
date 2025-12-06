import QuantElim.Poly.Basic
import Mathlib.Data.Vector.Basic

namespace QuantElim.Poly.Grobner

open Mathlib

@[inline]
def size {others bounds : ℕ} : Vector ℕ (others + bounds) → List ℕ := fun v =>
  let l₁ := v.drop others
  let l₂ := v.take others
  let s₁ := (l₁.map (fun x => x^2)).toList.sum
  let s₂ := (l₂.map (fun x => x^2)).toList.sum
  s₁ :: l₁.toList.map (fun n => s₁ - n) ++ s₂ :: l₂.toList.map (fun n => s₂ - n)

@[inline]
def lt {others bounds : ℕ} : Vector ℕ (others + bounds) → Vector ℕ (others + bounds) → Bool :=
  fun v₁ v₂ => List.Lex (. < .) (size v₁) (size v₂)

def leadingMonomialAux (others bounds : ℕ) : PolyAux (others + bounds) → Vector ℕ (others + bounds) := fun p =>
  match others, bounds, p with
  | 0, 0, _ => Vector.nil
  | m+1, 0, PolyAux.const c => Vector.cons 0 <| @leadingMonomialAux m 0 c
  | m+1, 0, PolyAux.constAddXMul p q =>
    let m₁ := Vector.cons 0 <| @leadingMonomialAux m 0 p
    let m₂ := ⟨(@leadingMonomialAux (m+1) 0 q).toList.modify Nat.succ 0, by simp⟩
    if lt m₁ m₂ then m₂ else m₁
  | m, n+1, PolyAux.const c => Vector.cons 0 <| @leadingMonomialAux m n c
  | m, n+1, PolyAux.constAddXMul p q =>
    let m₁ := Vector.cons 0 <| @leadingMonomialAux m n p
    let m₂ := ⟨(@leadingMonomialAux m (n+1) q).toList.modify Nat.succ 0, by simp⟩
    if lt m₁ m₂ then m₂ else m₁

def leadingMonomial {others bounds : ℕ} : Poly (others + bounds) → Vector ℕ (others + bounds) := fun p =>
  leadingMonomialAux others bounds p.1

def monomialsAux {n : ℕ} : PolyAux n → List (ℤ × Vector ℕ n)
  | PolyAux.ofInt' k => [(k, Vector.nil)]
  | PolyAux.const c => (monomialsAux c).map (fun v => (v.1, Vector.cons 0 v.2))
  | PolyAux.constAddXMul p q =>
    (monomialsAux p).map (fun v => (v.1, Vector.cons 0 v.2)) ++ (monomialsAux q).map
      (fun v => (v.1, ⟨v.2.toList.modify Nat.succ 0, by simp⟩))

def monomials {n : ℕ} : Poly n → List (ℤ × Vector ℕ n) := fun p =>
  monomialsAux p.1

def reduce {others bounds : ℕ} (G : List (Poly (others + bounds))) :
    Vector ℕ (others + bounds) → Poly (others + bounds) → Poly (others + bounds) := fun m p =>
  let l := monomials p.1

end QuantElim.Poly.Grobner

#print Acc

universe u

inductive Acc2 {α : Sort u} (r : α → α → Prop) : α → Prop where
  /--
  A value is accessible if for all `y` such that `r y x`, `y` is also accessible.
  Note that if there exists no `y` such that `r y x`, then `x` is accessible. Such an `x` is called a
  _base case_.
  -/
  | intro (x : α) (h : (y : α) → r y x → Acc2 r y) : Acc2 r x

def n : {  x : ℕ // x = 1 } := Acc2.rec (r := fun (_ _ : ℕ) => False) 
  (fun n _ _ => ⟨1, rfl⟩) (show Acc2 _ 0 from Acc2.intro _ (by simp))
