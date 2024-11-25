import QuantElim.Poly.Basic

namespace Poly

namespace Grobner

open Mathlib

structure Rel (n : ℕ) : Type where
  ( r : (Fin n → ℕ) → (Fin n → ℕ) → Prop )
  ( add_le_add : ∀ m n p, r m n → r (m + p) (n + p) )
  ( le_add : ∀ m p, r m (m + p) )

variable {n : ℕ} (r : Rel n)

def _root_.Poly.leadingMonAndCoeff : ∀ {n : ℕ}, Poly n → ℤ × (Fin n → ℕ)
  | 0, p => (toInt p, Fin.elim0)
  | _+1, p =>
    let a := p.leadingCoeff.leadingMonAndCoeff
    (a.1, Fin.cons (p.natDegree) a.2)

def _root_.Poly.leadingMon (p : Poly n) : Fin n → ℕ :=
  p.leadingMonAndCoeff.2

def _root_.Poly.leadingCoeffInt (p : Poly n) : ℤ :=
  p.leadingMonAndCoeff.1

def toPoly : ∀ {n : ℕ} (_mon : Fin n → ℕ), Poly n
  | 0, _ => 1
  | _+1, mon => const (toPoly (Fin.tail mon)) * Poly.X 0 ^ (mon 0)

def S (p q : Poly n) : Poly n :=
  let m := p.leadingMon ⊔ q.leadingMon
  let g := Int.gcd p.leadingCoeffInt q.leadingCoeffInt
  (p.leadingCoeffInt / (g : ℤ) : ℤ) * toPoly (m - q.leadingMon) -
  (q.leadingCoeffInt / (g : ℤ) : ℤ) * toPoly (m - q.leadingMon)

def reduceWith (l : List (Poly n)) (p : Poly n) : Poly n :=
  l.foldl (fun q r => S r q) p

end Grobner

end Poly
