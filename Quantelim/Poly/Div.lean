import QuantElim.Poly.Basic

namespace Poly

variable {n : ℕ}

theorem modDiv_wf_aux {p q : Poly (n+1)} {lq lp : Poly n}
    (hlq : lq ≠ 0) (h : q.degree ≤ p.degree)
    (hlplq : (toPoly p).leadingCoeff * toMvPoly lq = toMvPoly lp * (toPoly q).leadingCoeff)
    (hq0 : q ≠ 0) : (const lq * p - const lp * X 0 ^
      (p.natDegree - q.natDegree) * q).degree < p.degree := by
  have hlp : lp ≠ 0 := by rintro rfl; simp_all
  have hp0 : p ≠ 0 := by rintro rfl; simp_all
  have hlt : natDegree q ≤ natDegree p :=
    (Nat.cast_le (α := WithBot ℕ)).1
      (by rw [← degree_eq_natDegree hp0, ← degree_eq_natDegree hq0]; exact h)
  refine lt_of_lt_of_le (degree_sub_lt ?_ ?_ ?_) ?_
  · rw [mul_comm, degree_mul, degree_mul, degree_const_mul_X_pow hlp, degree_eq_natDegree hp0,
        degree_eq_natDegree hq0, ← Nat.cast_add, tsub_add_cancel_of_le hlt,
        degree_const_of_ne_zero hlq, add_zero]
  · rw [mul_ne_zero_iff, Ne, const_eq_zero_iff]
    tauto
  · rw [← toMvPoly.injective.eq_iff, leadingCoeff_toPoly, leadingCoeff_toPoly,
       map_mul, toPoly_const, map_mul, map_mul,
       map_pow, toPoly_X_zero, mul_right_comm, Polynomial.leadingCoeff_mul_X_pow,
       Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, mul_comm,
       toPoly_const, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hlplq]
  · rw [degree_mul, degree_const_of_ne_zero hlq, zero_add]

theorem modDiv_wf {p q : Poly (n+1)} (h : q.degree ≤ p.degree)
     (hq0 : q ≠ 0) : (const q.leadingCoeff * p - const p.leadingCoeff * X 0 ^
      (p.natDegree - q.natDegree) * q).degree < p.degree := by
  have hq : leadingCoeff q ≠ 0 := leadingCoeff_ne_zero.2 hq0
  exact modDiv_wf_aux hq h (by simp [mul_comm, leadingCoeff_toPoly]) hq0

theorem div_wf {p q : Poly (n+1)} (l : Poly n) (hq0 : q ≠ 0) (h : q.degree ≤ p.degree)
    (hl : p.leadingCoeff  = q.leadingCoeff * l) :
    (p - const l * X 0 ^ (p.natDegree - q.natDegree) * q).degree < p.degree := by
  suffices h : (const 1 * p - const l * X 0 ^ (p.natDegree - q.natDegree) * q).degree < p.degree by
    simpa using h
  apply modDiv_wf_aux one_ne_zero h _ hq0
  rw [← leadingCoeff_toPoly, hl, map_mul, map_one, mul_one, leadingCoeff_toPoly, mul_comm]

/-- returns `m`, `h` and `r`such that `leadingCoeff q ^ m * p = h * q + r` -/
def pseudoModDiv : ∀ {n : ℕ} (p q : Poly (n+1)), Σ (m : ℕ) (h : Poly (n+1)),
    { r : Poly (n+1) // (q ≠ 0 → r.degree < q.degree) ∧
      const (leadingCoeff q) ^ m * p = h * q + r } :=
  fun p q =>
  let dp := natDegree p
  let dq := natDegree q
  let lp := p.leadingCoeff
  let lq := q.leadingCoeff
  if h : degree q ≤ degree p then
  if hp0 : p = 0 then ⟨0, 0, ⟨0, by simp [WithBot.bot_lt_iff_ne_bot], by simp [*]⟩⟩
  else if hq0 : q = 0 then ⟨1, 0, ⟨0, by simp_all⟩⟩
  else
    let z := (const lp * X 0 ^ (dp - dq) * q)
    have wf := modDiv_wf h hq0
    let ⟨n, h, ⟨r, hr₁, hr₂⟩⟩ := pseudoModDiv (const lq * p - z) q
    ⟨n+1, h + const (lq ^ n * lp) * X 0 ^(dp - dq), ⟨r, hr₁, by
      rw [add_mul, add_right_comm _ _ r, ← hr₂]
      simp [z]
      ring⟩⟩
  else ⟨0, 0, ⟨p, fun _ => lt_of_not_le h, by simp⟩⟩
  termination_by n p => (n+1, degree p)

def pMod {n : ℕ} (p q : Poly (n+1)) : Poly (n+1) := (pseudoModDiv p q).2.2.1

def pDiv {n : ℕ} (p q : Poly (n+1)) : Poly (n+1) := (pseudoModDiv p q).2.1

def pModDivNat {n : ℕ} (p q : Poly (n+1)) : ℕ := (pseudoModDiv p q).1

theorem degree_pMod_lt {p q : Poly (n+1)} (hq0 : q ≠ 0) : (pMod p q).degree < q.degree :=
  (pseudoModDiv p q).2.2.2.1 hq0

theorem pMod_add_pDiv {p q : Poly (n+1)} : const (leadingCoeff q) ^ pModDivNat p q* p = pDiv p q * q + pMod p q :=
  (pseudoModDiv p q).2.2.2.2

/-- returns `p / q` if it exists, otherwise nonsense -/
def divDvd : ∀ {n : ℕ} (p q : Poly n), { r : Poly n // q ∣ p → p = q * r }
  | 0, ⟨PolyAux.ofInt' x, _⟩, ⟨PolyAux.ofInt' y, _⟩ =>
    ⟨x.tdiv y, by
      show ((y : Poly 0) ∣ (x : Poly 0) → (x : Poly 0) = y * (_ : Poly 0))
      simp only [intCast_dvd_intCast, ← Int.cast_mul]
      intro hyx
      rw [Int.mul_tdiv_cancel' hyx]⟩
  | _+1, p, q =>
    let dp := natDegree p
    let dq := natDegree q
    let lp := p.leadingCoeff
    let lq := q.leadingCoeff
    have ⟨l,hl⟩ := divDvd lp lq
    have hld : q ∣ p → lp = lq * l :=
      fun h => hl (leadingCoeff_dvd_of_dvd h)
    if hq0 : q = 0 then ⟨0, by simp [hq0]⟩
    else if h : degree q ≤ degree p then
      if hl0 : lp = lq * l
      then
        have hlqp : lq ∣ lp := by by_contra h; simp_all
        let z := (const l * X 0 ^ (p.natDegree - q.natDegree) * q)
        have wf := div_wf l hq0 h hl0
        have v := divDvd (p - z) q
        ⟨v.1 + const l * X 0 ^ (p.natDegree - q.natDegree), by
          rcases v with ⟨v, hv⟩
          dsimp only
          intro hqp
          have := hv (dvd_sub hqp (by simp [z]))
          rw [sub_eq_iff_eq_add] at this
          conv_lhs => rw [this]
          simp [z]
          ring⟩
      else ⟨0, by intro h; simp_all⟩
    else ⟨0, by
      intro hqp
      rcases exists_eq_mul_right_of_dvd hqp with ⟨r, hr⟩
      subst hr
      rw [degree_mul] at h
      by_cases hr : r = 0
      · simp_all
      · exfalso
        exact h (le_add_of_nonneg_right (degree_nonneg_iff_ne_zero.2 hr))⟩
  termination_by n p => (n, degree p)

instance : Div (Poly n) := ⟨fun p q => divDvd p q⟩

theorem div_def {n : ℕ} (p q : Poly n) : p / q = divDvd p q := rfl

theorem div_mul_cancel_of_dvd {p q : Poly n} (h : q ∣ p) : (p / q) * q = p := by
  rw [div_def]
  rw [mul_comm, ← (divDvd p q).2 h]

theorem mul_div_cancel_of_dvd {p q : Poly n} (h : q ∣ p) : q * (p / q) = p := by
  rw [mul_comm, div_mul_cancel_of_dvd h]

instance (p q : Poly n) : Decidable (p ∣ q) := decidable_of_iff (q / p * p = q) <| by
  refine ⟨?_, div_mul_cancel_of_dvd⟩
  intro h
  rw [← h]
  simp

@[simp]
theorem mul_div_cancel {p q : Poly n} (hp0 : p ≠ 0) : (p * q) / p = q :=
  mul_right_injective₀ hp0 (by simp only [mul_div_cancel_of_dvd (dvd_mul_right _ _)])

@[simp]
theorem mul_div_cancel' {p q : Poly n} (hp0 : p ≠ 0) : (q * p) / p = q := by
  rw [mul_comm, mul_div_cancel hp0]

theorem zero_div_zero : (0 : Poly n) / 0 = 0 := by
  cases n
  · simp only [OfNat.ofNat]
    simp only [Zero.zero, PolyAux.zero_def]
    simp only [OfNat.ofNat, Int.ofNat, Int.cast, IntCast.intCast,
      PolyAux.ofInt]
    rw [div_def, Poly.divDvd]
    simp; rfl
  · rw [div_def, Poly.divDvd]
    simp

@[simp]
theorem zero_div {p : Poly n} : 0 / p = 0 := by
  by_cases hp0 : p = 0
  · simp_all [zero_div_zero]
  · exact mul_right_injective₀ hp0 (by simp [mul_div_cancel_of_dvd (dvd_zero _)])

theorem div_eq_zero_iff {p q : Poly n} (h : p ∣ q) :
    q / p = 0 ↔ q = 0 := by
  rcases exists_eq_mul_right_of_dvd h with ⟨r, rfl⟩
  by_cases hp0 : p = 0
  · simp_all
  · rw [mul_div_cancel]
    simp_all
    assumption

theorem degree_div_le {p q : Poly (n+1)} (h : q ∣ p) : (p / q).degree ≤ p.degree := by
  rcases exists_eq_mul_right_of_dvd h with ⟨r, rfl⟩
  by_cases hq0 : q = 0
  · subst hq0; simp
  · rw [mul_div_cancel hq0, degree_mul]
    exact le_add_of_nonneg_left (degree_nonneg_iff_ne_zero.2 (by rintro rfl; simp_all))

def IsPrimitive (p : Poly (n+1)) : Prop :=
  ∀ q, const q ∣ p → IsUnit q

theorem isPrimitive_of_cont {c : Poly n} {p : Poly (n+1)} (hc0 : c ≠ 0)
    (hc : const c ∣ p ∧ ∀ c': Poly n, const c' ∣ p → c' ∣ c) : IsPrimitive (p / const c) := by
  intro a ha
  have := hc.2 (c * a)
  rw [map_mul, ← mul_div_cancel_of_dvd hc.1, mul_dvd_mul_iff_left] at this
  have : c * a ∣ c * 1 := by simpa using this ha
  rw [mul_dvd_mul_iff_left hc0] at this
  exact isUnit_of_dvd_one this
  simp_all

theorem IsPrimitive.IsRelPrime_const {p : Poly (n+1)} (hp : IsPrimitive p) {c : Poly n}
    (hc0 : c ≠ 0) : IsRelPrime (const c) p := by
  intro a ha hc
  rcases (dvd_const_iff hc0).1 ha with ⟨a, rfl, ha⟩
  rw [const_dvd_const] at ha
  rw [isUnit_iff_dvd_one, ← map_one (@const n), const_dvd_const, ← isUnit_iff_dvd_one]
  exact hp _ hc

mutual

def cont : ∀ {n : ℕ} (p : Poly (n+1)), { c : Poly n //
    const c ∣ p ∧ ∀ c': Poly n, const c' ∣ p → c' ∣ c } :=
  fun {n} p => @recOnSucc _ (fun {m} (p : Poly (m+1)) => m < n+1 →
    { c : Poly m // const c ∣ p ∧ ∀ c': Poly m, const c' ∣ p → c' ∣ c }) p
  (fun p _ => ⟨p, by simp⟩)
  (fun m p q hq0 ih hm => by
    simp only at ih
    replace ih := ih hm
    rcases ih with ⟨c, hc⟩
    rcases gCd c p with ⟨g, ⟨hgc, hgp, hg⟩⟩
    refine ⟨g, ?_, ?_⟩
    · rw [const_dvd_constAddXMul]
      refine ⟨hgp, dvd_trans (const_dvd_const.2 hgc) hc.1⟩
    · intro c' hc'
      rw [const_dvd_constAddXMul] at hc'
      refine hg _ (hc.2 _ hc'.2) hc'.1) (Nat.lt_succ_self n)
  termination_by n p => (n+1, 0, degree p)

-- This returns the gcd
def gCd : ∀ {n : ℕ} (p q : Poly n),
    { g : Poly n // g ∣ p ∧ g ∣ q ∧ ∀ g' : Poly n, g' ∣ p → g' ∣ q → g' ∣ g }
  | 0, ⟨PolyAux.ofInt' x, _⟩, ⟨PolyAux.ofInt' y, _⟩ => ⟨Int.gcd x y, by
      show _ ∣ (x : Poly 0) ∧ _ ∣ (y : Poly 0) ∧ ∀ _ : Poly 0, _ ∣ (x : Poly 0) → _ ∣ (y : Poly 0) → _ ∣ _
      rw [←Int.cast_natCast, intCast_dvd_intCast, intCast_dvd_intCast]
      simp only [Int.gcd_dvd_left, Int.gcd_dvd_right, Int.cast_natCast, true_and]
      intro p hpx hpy
      by_cases hx0 : x = 0
      · subst hx0
        by_cases hy0 : y = 0
        · simp_all
        · rw [dvd_intCast_iff hy0] at hpy
          rcases hpy with ⟨g, rfl, hg⟩
          rw [← Int.cast_natCast, intCast_dvd_intCast]
          simpa
      rw [dvd_intCast_iff hx0] at hpx
      rcases hpx with ⟨g, rfl, hg⟩
      rw [← Int.cast_natCast, intCast_dvd_intCast]
      exact Int.dvd_gcd hg (intCast_dvd_intCast.1 hpy)⟩
  | n+1, p, q =>
  if hq0 : q = 0 then ⟨p, by subst hq0; simp⟩
  else if hp0 : p = 0 then ⟨q, by subst hp0; simp⟩
  else
    have ⟨cq, hcq⟩ := cont q
    have ⟨cp, hcp⟩ := cont p
    let ⟨k, h, ⟨r, hr⟩⟩ := pseudoModDiv (p / const cp) (q / const cq)
    have _wf : r.degree < q.degree := by
      simp only [Ne, div_eq_zero_iff hcq.1, hq0] at hr
      simp only [not_false_eq_true, forall_const] at hr
      refine lt_of_lt_of_le hr.1 (degree_div_le hcq.1)
    have ⟨g, hg⟩ := gCd (q / const cq) r
    have ⟨cg, hcg⟩ := gCd cp cq
    ⟨const cg * g, by
      generalize hq : q / const cq = q'
      generalize hp : p / const cp = p'
      have hcq0 : cq ≠ 0 := by rintro rfl; simp_all
      have hcp0 : cp ≠ 0 := by rintro rfl; simp_all
      have hq'P : (q / const cq).IsPrimitive := isPrimitive_of_cont hcq0 hcq
      have hp'P : (p / const cp).IsPrimitive := isPrimitive_of_cont hcp0 hcp
      have hp' := mul_div_cancel_of_dvd hcq.1
      have hq' := mul_div_cancel_of_dvd hcp.1
      simp only [hq, hp] at *; clear hp hq
      simp only [← hp', ← hq'] at *
      simp only [ne_eq, mul_eq_zero, const_eq_zero_iff, not_or, dvd_mul_right, true_and] at *
      clear hp' hq'
      have hcq0 : cq ≠ 0 := by rintro rfl; simp_all
      have : ∀ g', g' ∣ q' → (g' ∣ r → g' ∣ p') := by
        intro g' hgq hgr
        have : IsRelPrime g' (const q'.leadingCoeff) := by
          intro a hag halq
          rw [dvd_const_iff] at halq
          rcases halq with ⟨a, rfl, halq⟩
          have haq : const a ∣ q' := dvd_trans hag hgq
          have hacq : cq * a ∣ cq := hcq _ <| by
            rw [map_mul, mul_dvd_mul_iff_left]
            exact haq
            simpa
          have hacq : cq * a ∣ cq * 1 := by simpa
          rw [mul_dvd_mul_iff_left hcq0, ← const_dvd_const, map_one] at hacq
          exact isUnit_of_dvd_one hacq
          simp_all
        have hg1 : g' ∣ const q'.leadingCoeff ^k * p' := by
          rw [hr.2]; exact dvd_add (dvd_mul_of_dvd_right hgq _) hgr
        exact IsRelPrime.dvd_of_dvd_mul_left (IsRelPrime.pow_right this) hg1
      refine ⟨mul_dvd_mul (const_dvd_const.2 hcg.1) (this g hg.1 hg.2.1),
        mul_dvd_mul (const_dvd_const.2 hcg.2.1) hg.1, ?_⟩
      intro g'' hgp hgq
      have ⟨cg', hcg'⟩ := cont g''
      have hcg'0 : cg' ≠ 0 := by rintro rfl; simp_all
      have hg'P : IsPrimitive (g'' / const cg') := isPrimitive_of_cont hcg'0 hcg'
      generalize hmn : g'' / const cg' = g'
      have hg' := mul_div_cancel_of_dvd hcg'.1
      simp only [hmn] at *; clear hmn
      simp only [← hg'] at *; clear g'' hg'
      refine mul_dvd_mul ?_ ?_
      · rw [const_dvd_const]
        refine hcg.2.2 _ ?_ ?_
        · rw [← const_dvd_const]
          refine IsRelPrime.dvd_of_dvd_mul_right ?_ (dvd_trans (dvd_mul_right _ _) hgp)
          exact hp'P.IsRelPrime_const hcg'0
        · rw [← const_dvd_const]
          refine IsRelPrime.dvd_of_dvd_mul_right ?_ (dvd_trans (dvd_mul_right _ _) hgq)
          exact hq'P.IsRelPrime_const hcg'0
      · have hg'q : g' ∣ q' := by
          refine IsRelPrime.dvd_of_dvd_mul_left ?_ (dvd_trans (dvd_mul_left _ _) hgq)
          apply IsRelPrime.symm
          exact hg'P.IsRelPrime_const hcq0
        refine hg.2.2 _ hg'q ?_
        · have hcp0 : cp ≠ 0 := by rintro rfl; simp_all
          have hg'p : g' ∣ p' := by
            refine IsRelPrime.dvd_of_dvd_mul_left ?_ (dvd_trans (dvd_mul_left _ _) hgp)
            apply IsRelPrime.symm
            exact hg'P.IsRelPrime_const hcp0
          rw [add_comm _ r, ← sub_eq_iff_eq_add] at hr
          rw [← hr.2]
          exact dvd_sub (dvd_mul_of_dvd_right hg'p _) (dvd_mul_of_dvd_right hg'q _)⟩
  termination_by n _ q => (n, 2, degree q)

end

instance : GCDMonoid (Poly n) where
  gcd := fun p q => (gCd p q).1
  lcm := fun p q => p * q / (gCd p q).1
  gcd_dvd_left := fun p q => (gCd p q).2.1
  gcd_dvd_right := fun p q => (gCd p q).2.2.1
  dvd_gcd := fun h1 h2 => (gCd _ _).2.2.2  _ h1 h2
  gcd_mul_lcm := fun p q => by
    simp only
    rw [mul_div_cancel_of_dvd]
    exact dvd_mul_of_dvd_left (gCd p q).2.1 _
  lcm_zero_left := fun p => by simp
  lcm_zero_right := fun p => by simp

end Poly
