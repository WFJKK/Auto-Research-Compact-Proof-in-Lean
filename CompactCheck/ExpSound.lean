import Mathlib.Analysis.Complex.Exponential
import CompactCheck.Exp

/-!
# The bounds on `exp` are right

`expBounds_spec`: if `expBounds x = some (L, H)`, then
`L ≤ exp x * 2^120 ≤ H`, for the real exponential. The steps follow
`expBoundsParts`:

1. `y = |x| / 2^m` lies between the rounded `ylo / 2^W` and `yhi / 2^W`, and
   `yhi / 2^W ≤ 1` (`yBounds`).
2. The lower sum is at most `2^W * exp (ylo / 2^W)`: its terms are rounded
   down, and a partial sum of the series is at most `exp`
   (`Real.sum_le_exp_of_nonneg`). The upper sum is at least
   `2^W * exp (yhi / 2^W)`: its terms are rounded up, and the rest of the
   series is at most twice the next term (`Real.exp_bound'`).
   (`expSeries_spec`.)
3. For `x < 0`, `exp (-y) = 1 / exp y`, with the divisions rounded outwards.
4. Each squaring, rounded outwards, bounds `exp (2 z)` from bounds on
   `exp z` (`expSquare_spec`), and `m` of them give `exp x`.
5. Arguments of `2^12` or more: below `-2^12`, `exp x * 2^120 < 1`
   (`exp_le_of_le_neg`); above, the checker gives no bounds.
-/

namespace CompactCheck

open Real Finset

/-! ## Rounding -/

theorem ediv_le_div {a b : ℤ} (hb : 0 < b) : ((a / b : ℤ) : ℝ) ≤ (a : ℝ) / b := by
  rw [le_div_iff₀ (by exact_mod_cast hb)]
  exact_mod_cast Int.ediv_mul_le a (ne_of_gt hb)

theorem div_le_ceilDiv {a b : ℤ} (hb : 0 < b) : (a : ℝ) / b ≤ ((ceilDiv a b : ℤ) : ℝ) := by
  have h := ediv_le_div (a := -a) hb
  unfold ceilDiv
  push_cast at h ⊢
  rw [neg_div] at h
  linarith

theorem ceilDiv_le {a b : ℤ} (hb : 0 < b) : ((ceilDiv a b : ℤ) : ℝ) ≤ (a : ℝ) / b + 1 := by
  have h := Int.lt_ediv_add_one_mul_self (-a) hb
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have h' : (-(a : ℝ)) < (((-a) / b : ℤ) + 1 : ℝ) * b := by exact_mod_cast h
  unfold ceilDiv
  push_cast
  have : -(a : ℝ) / b < ((-a) / b : ℤ) + 1 := by rwa [div_lt_iff₀ hb']
  rw [neg_div] at this
  linarith

/-! ## The series -/

theorem two_pow_pos (W : ℕ) : (0 : ℝ) < 2 ^ W := by positivity

theorem two_zpow_pos (n : ℤ) : (0 : ℝ) < 2 ^ n := zpow_pos (by norm_num) n

/-- The two sums of `expSeries`, with all terms rounded the right way, bound
    `exp` at the two rounded arguments. -/
theorem expSeries_spec (W : ℕ) (ylo yhi : ℤ) (hylo : 0 ≤ ylo) (hyhi : 0 ≤ yhi)
    (hy1 : (yhi : ℝ) / 2 ^ W ≤ 1) :
    ∀ (fuel k : ℕ) (tlo thi loSum hiSum lo hi : ℤ),
      expSeries W ylo yhi fuel k tlo thi loSum hiSum = some (lo, hi) → 0 ≤ tlo →
      (tlo : ℝ) ≤ 2 ^ W * ((ylo : ℝ) / 2 ^ W) ^ k / k.factorial →
      2 ^ W * ((yhi : ℝ) / 2 ^ W) ^ k / k.factorial ≤ thi →
      (loSum : ℝ) ≤ 2 ^ W * ∑ i ∈ range k, ((ylo : ℝ) / 2 ^ W) ^ i / i.factorial →
      2 ^ W * ∑ i ∈ range k, ((yhi : ℝ) / 2 ^ W) ^ i / i.factorial ≤ hiSum →
      (lo : ℝ) ≤ 2 ^ W * exp ((ylo : ℝ) / 2 ^ W) ∧ 2 ^ W * exp ((yhi : ℝ) / 2 ^ W) ≤ hi ∧
        loSum + tlo ≤ lo := by
  intro fuel
  induction fuel with
  | zero =>
    intro k tlo thi loSum hiSum lo hi h
    simp [expSeries] at h
  | succ fuel ih =>
    intro k tlo thi loSum hiSum lo hi h htlo0 htlo hthi hlo hhi
    have h2W := two_pow_pos W
    have ha0 : (0 : ℝ) ≤ (ylo : ℝ) / 2 ^ W := div_nonneg (by exact_mod_cast hylo) h2W.le
    have hb0 : (0 : ℝ) ≤ (yhi : ℝ) / 2 ^ W := div_nonneg (by exact_mod_cast hyhi) h2W.le
    have hden : (0 : ℤ) < ((k + 1 : ℕ) : ℤ) * 2 ^ W := by positivity
    have hD : (((((k + 1 : ℕ) : ℤ) * 2 ^ W : ℤ)) : ℝ) = ((k : ℝ) + 1) * 2 ^ W := by
      push_cast
      ring
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hfact : ((k + 1).factorial : ℝ) = ((k : ℝ) + 1) * k.factorial := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have hkf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    -- the next lower term
    have htlo'0 : 0 ≤ tlo * ylo / (((k + 1 : ℕ) : ℤ) * 2 ^ W) :=
      Int.ediv_nonneg (mul_nonneg htlo0 hylo) hden.le
    have htlo' : (((tlo * ylo / (((k + 1 : ℕ) : ℤ) * 2 ^ W)) : ℤ) : ℝ) ≤
        2 ^ W * ((ylo : ℝ) / 2 ^ W) ^ (k + 1) / (k + 1).factorial := by
      calc (((tlo * ylo / (((k + 1 : ℕ) : ℤ) * 2 ^ W)) : ℤ) : ℝ)
          ≤ ((tlo * ylo : ℤ) : ℝ) / ((((k + 1 : ℕ) : ℤ) * 2 ^ W : ℤ) : ℝ) := ediv_le_div hden
        _ = (tlo : ℝ) * ((ylo : ℝ) / 2 ^ W) / ((k : ℝ) + 1) := by
          rw [hD]
          push_cast
          field_simp
        _ ≤ (2 ^ W * ((ylo : ℝ) / 2 ^ W) ^ k / k.factorial) * ((ylo : ℝ) / 2 ^ W) /
            ((k : ℝ) + 1) := by gcongr
        _ = 2 ^ W * ((ylo : ℝ) / 2 ^ W) ^ (k + 1) / (k + 1).factorial := by
          rw [hfact, pow_succ]
          field_simp
    -- the next upper term
    have hthi' : 2 ^ W * ((yhi : ℝ) / 2 ^ W) ^ (k + 1) / (k + 1).factorial ≤
        ((ceilDiv (thi * yhi) (((k + 1 : ℕ) : ℤ) * 2 ^ W) : ℤ) : ℝ) := by
      set b : ℝ := (yhi : ℝ) / 2 ^ W with hb
      have heq : 2 ^ W * b ^ (k + 1) / (k + 1).factorial =
          (2 ^ W * b ^ k / k.factorial) * b / ((k : ℝ) + 1) := by
        rw [hfact, pow_succ]
        field_simp
      rw [heq]
      calc (2 ^ W * b ^ k / k.factorial) * b / ((k : ℝ) + 1)
          ≤ (thi : ℝ) * b / ((k : ℝ) + 1) := by gcongr
        _ = ((thi * yhi : ℤ) : ℝ) / ((((k + 1 : ℕ) : ℤ) * 2 ^ W : ℤ) : ℝ) := by
          rw [hD, hb]
          push_cast
          field_simp
        _ ≤ _ := div_le_ceilDiv hden
    have hlo' : ((loSum + tlo : ℤ) : ℝ) ≤
        2 ^ W * ∑ i ∈ range (k + 1), ((ylo : ℝ) / 2 ^ W) ^ i / i.factorial := by
      rw [sum_range_succ, mul_add]
      push_cast
      have : (tlo : ℝ) ≤ 2 ^ W * (((ylo : ℝ) / 2 ^ W) ^ k / k.factorial) := by
        rw [← mul_div_assoc]
        exact htlo
      linarith
    have hhi' : 2 ^ W * ∑ i ∈ range (k + 1), ((yhi : ℝ) / 2 ^ W) ^ i / i.factorial ≤
        ((hiSum + thi : ℤ) : ℝ) := by
      rw [sum_range_succ, mul_add]
      push_cast
      have : 2 ^ W * (((yhi : ℝ) / 2 ^ W) ^ k / k.factorial) ≤ (thi : ℝ) := by
        rw [← mul_div_assoc]
        exact hthi
      linarith
    simp only [expSeries] at h
    split_ifs at h with hstop
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨?_, ?_, le_refl _⟩
      · calc ((loSum + tlo : ℤ) : ℝ)
            ≤ 2 ^ W * ∑ i ∈ range (k + 1), ((ylo : ℝ) / 2 ^ W) ^ i / i.factorial := hlo'
          _ ≤ 2 ^ W * exp ((ylo : ℝ) / 2 ^ W) := by
            gcongr
            exact Real.sum_le_exp_of_nonneg ha0 _
      · set b : ℝ := (yhi : ℝ) / 2 ^ W
        set c : ℤ := ceilDiv (thi * yhi) (((k + 1 : ℕ) : ℤ) * 2 ^ W) with hc
        have hexp := Real.exp_bound' hb0 hy1 (Nat.succ_pos k)
        simp only [Nat.succ_eq_add_one] at hexp
        have htail : b ^ (k + 1) * (((k + 1 : ℕ) : ℝ) + 1) /
            ((k + 1).factorial * ((k + 1 : ℕ) : ℝ)) ≤
            2 * (b ^ (k + 1) / (k + 1).factorial) := by
          have hf : (0 : ℝ) < (k + 1).factorial := by exact_mod_cast Nat.factorial_pos (k + 1)
          have hbk : (0 : ℝ) ≤ b ^ (k + 1) := pow_nonneg hb0 _
          rw [div_le_iff₀ (by positivity)]
          have : (((k + 1 : ℕ) : ℝ) + 1) ≤ 2 * ((k + 1 : ℕ) : ℝ) := by
            push_cast
            linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
          calc b ^ (k + 1) * (((k + 1 : ℕ) : ℝ) + 1)
              ≤ b ^ (k + 1) * (2 * ((k + 1 : ℕ) : ℝ)) := by gcongr
            _ = 2 * (b ^ (k + 1) / (k + 1).factorial) *
                ((k + 1).factorial * ((k + 1 : ℕ) : ℝ)) := by
              field_simp
        have hthi'2 : 2 ^ W * (2 * (b ^ (k + 1) / (k + 1).factorial)) ≤ 2 * (c : ℝ) := by
          have : 2 ^ W * (2 * (b ^ (k + 1) / (k + 1).factorial)) =
              2 * (2 ^ W * b ^ (k + 1) / (k + 1).factorial) := by ring
          rw [this]
          linarith
        calc 2 ^ W * exp b
            ≤ 2 ^ W * (∑ i ∈ range (k + 1), b ^ i / i.factorial +
                2 * (b ^ (k + 1) / (k + 1).factorial)) := by
              gcongr
              linarith
          _ = 2 ^ W * ∑ i ∈ range (k + 1), b ^ i / i.factorial +
                2 ^ W * (2 * (b ^ (k + 1) / (k + 1).factorial)) := by ring
          _ ≤ ((hiSum + thi + 2 * c : ℤ) : ℝ) := by
              push_cast at hhi' ⊢
              linarith
    · obtain ⟨h1, h2, h3⟩ := ih (k + 1) _ _ _ _ lo hi h htlo'0 htlo' hthi' hlo' hhi'
      refine ⟨h1, h2, ?_⟩
      linarith

/-! ## Squaring -/

/-- Squaring bounds on `exp z`, rounded outwards, bounds `exp (2 z)`; `n`
    squarings bound `exp (z * 2^n)`. -/
theorem expSquare_spec (W : ℕ) : ∀ (n : ℕ) (z : ℝ) (L H : ℤ), 0 ≤ L →
    (L : ℝ) ≤ 2 ^ W * exp z → 2 ^ W * exp z ≤ H →
    0 ≤ (expSquare W n (L, H)).1 ∧ ((expSquare W n (L, H)).1 : ℝ) ≤ 2 ^ W * exp (z * 2 ^ n) ∧
      2 ^ W * exp (z * 2 ^ n) ≤ (expSquare W n (L, H)).2
  | 0, z, L, H, h0, hL, hH => by simpa [expSquare] using ⟨h0, hL, hH⟩
  | n + 1, z, L, H, h0, hL, hH => by
    have h2W := two_pow_pos W
    have h2W' : (0 : ℤ) < 2 ^ W := by positivity
    have hez := exp_pos z
    have hsq : (2 : ℝ) ^ W * exp (2 * z) = (2 ^ W * exp z) * (2 ^ W * exp z) / 2 ^ W := by
      rw [show 2 * z = z + z by ring, exp_add]
      field_simp
    have hL' : ((L * L / 2 ^ W : ℤ) : ℝ) ≤ 2 ^ W * exp (2 * z) := by
      calc ((L * L / 2 ^ W : ℤ) : ℝ) ≤ ((L * L : ℤ) : ℝ) / ((2 ^ W : ℤ) : ℝ) := ediv_le_div h2W'
        _ ≤ (2 ^ W * exp z) * (2 ^ W * exp z) / 2 ^ W := by
          push_cast
          have hL0 : (0 : ℝ) ≤ L := by exact_mod_cast h0
          exact div_le_div_of_nonneg_right (mul_le_mul hL hL hL0 (hL0.trans hL)) h2W.le
        _ = _ := hsq.symm
    have hH' : 2 ^ W * exp (2 * z) ≤ ((ceilDiv (H * H) (2 ^ W) : ℤ) : ℝ) := by
      have hH0 : (0 : ℝ) ≤ 2 ^ W * exp z := by positivity
      calc 2 ^ W * exp (2 * z) = (2 ^ W * exp z) * (2 ^ W * exp z) / 2 ^ W := hsq
        _ ≤ ((H * H : ℤ) : ℝ) / ((2 ^ W : ℤ) : ℝ) := by
          push_cast
          exact div_le_div_of_nonneg_right (mul_le_mul hH hH hH0 (hH0.trans hH)) h2W.le
        _ ≤ _ := div_le_ceilDiv h2W'
    have h0' : 0 ≤ L * L / 2 ^ W := Int.ediv_nonneg (mul_nonneg h0 h0) h2W'.le
    have := expSquare_spec W n (2 * z) _ _ h0' hL' hH'
    simp only [expSquare]
    rw [show z * 2 ^ (n + 1) = 2 * z * 2 ^ n by ring]
    exact this

/-! ## The argument -/

/-- `y = |x| / 2^m` and its rounded versions, as `expBoundsParts` computes
    them. -/
theorem yBounds (A : ℕ) (e : ℤ) (m W : ℕ) (hW : 8 ≤ W)
    (hm : ((A.log2 + 1 : ℕ) : ℤ) + e + 8 ≤ m) :
    0 ≤ (scaledArg A (e - m + W)).1 ∧ 0 ≤ (scaledArg A (e - m + W)).2 ∧
      ((scaledArg A (e - m + W)).1 : ℝ) / 2 ^ W ≤ A * (2 : ℝ) ^ e / 2 ^ m ∧
      A * (2 : ℝ) ^ e / 2 ^ m ≤ ((scaledArg A (e - m + W)).2 : ℝ) / 2 ^ W ∧
      ((scaledArg A (e - m + W)).2 : ℝ) / 2 ^ W ≤ 1 := by
  have h2W := two_pow_pos W
  have h2m := two_pow_pos m
  -- y * 2^W = A * 2^s
  have hy : A * (2 : ℝ) ^ e / 2 ^ m * 2 ^ W = A * (2 : ℝ) ^ (e - m + W) := by
    rw [zpow_add₀ (by norm_num), zpow_sub₀ (by norm_num), zpow_natCast, zpow_natCast]
    field_simp
  -- y ≤ 2^-8
  have hA2 : (A : ℝ) < 2 ^ (A.log2 + 1) := by exact_mod_cast Nat.lt_log2_self
  have hysmall : A * (2 : ℝ) ^ e / 2 ^ m ≤ 2 ^ (-8 : ℤ) := by
    rw [div_le_iff₀ h2m]
    calc A * (2 : ℝ) ^ e ≤ 2 ^ (A.log2 + 1) * (2 : ℝ) ^ e :=
          mul_le_mul_of_nonneg_right hA2.le (two_zpow_pos e).le
      _ = (2 : ℝ) ^ (((A.log2 + 1 : ℕ) : ℤ) + e) := by
        rw [zpow_add₀ (by norm_num)]
        norm_cast
      _ ≤ (2 : ℝ) ^ ((m : ℤ) - 8) := by
        apply zpow_le_zpow_right₀ (by norm_num)
        omega
      _ = 2 ^ (-8 : ℤ) * 2 ^ m := by
        rw [zpow_sub₀ (by norm_num)]
        field_simp
        norm_cast
  have hAs0 : (0 : ℝ) ≤ A * (2 : ℝ) ^ (e - m + W) :=
    mul_nonneg (Nat.cast_nonneg A) (two_zpow_pos _).le
  by_cases hs : e - m + W ≥ 0
  · simp only [scaledArg, hs, ↓reduceIte]
    have hcast : (((A : ℤ) * 2 ^ (e - m + W).toNat : ℤ) : ℝ) = A * (2 : ℝ) ^ (e - m + W) := by
      push_cast
      rw [← zpow_natCast, Int.toNat_of_nonneg hs]
    rw [hcast]
    have hq : A * (2 : ℝ) ^ (e - m + W) / 2 ^ W = A * (2 : ℝ) ^ e / 2 ^ m := by
      rw [← hy]
      field_simp
    refine ⟨by positivity, by positivity, hq.le, hq.ge, ?_⟩
    rw [hq]
    calc A * (2 : ℝ) ^ e / 2 ^ m ≤ 2 ^ (-8 : ℤ) := hysmall
      _ ≤ 1 := by
        apply zpow_le_one_of_nonpos₀ (by norm_num)
        norm_num
  · simp only [scaledArg, hs, ↓reduceIte]
    have hk : (0 : ℤ) < 2 ^ (-(e - m + W)).toNat := by positivity
    have hcast : ((A : ℤ) : ℝ) / (((2 : ℤ) ^ (-(e - m + W)).toNat : ℤ) : ℝ) =
        A * (2 : ℝ) ^ (e - m + W) := by
      push_cast
      rw [← zpow_natCast, Int.toNat_of_nonneg (by omega), zpow_neg, div_eq_mul_inv, inv_inv]
    have hlo := ediv_le_div (a := (A : ℤ)) hk
    have hhi := div_le_ceilDiv (a := (A : ℤ)) hk
    have hhi2 := ceilDiv_le (a := (A : ℤ)) hk
    rw [hcast] at hlo hhi hhi2
    have hy' : A * (2 : ℝ) ^ (e - m + W) / 2 ^ W = A * (2 : ℝ) ^ e / 2 ^ m := by
      rw [← hy]
      field_simp
    refine ⟨Int.ediv_nonneg (by positivity) hk.le, ?_, ?_, ?_, ?_⟩
    · have : (0 : ℝ) ≤ ((ceilDiv (A : ℤ) (2 ^ (-(e - m + W)).toNat) : ℤ) : ℝ) := le_trans hAs0 hhi
      exact_mod_cast this
    · rw [← hy']
      exact div_le_div_of_nonneg_right hlo h2W.le
    · rw [← hy']
      exact div_le_div_of_nonneg_right hhi h2W.le
    · -- yhi ≤ y * 2^W + 1 ≤ 2^(W - 8) + 1 ≤ 2^W
      rw [div_le_one h2W]
      have h1 : A * (2 : ℝ) ^ (e - m + W) ≤ 2 ^ (-8 : ℤ) * 2 ^ W := by
        rw [← hy]
        gcongr
      have h2 : (2 : ℝ) ^ (-8 : ℤ) * 2 ^ W + 1 ≤ 2 ^ W := by
        have : (1 : ℝ) ≤ 2 ^ (W - 8) := one_le_pow₀ (by norm_num)
        have hW' : (2 : ℝ) ^ W = 2 ^ (W - 8) * 2 ^ 8 := by
          rw [← pow_add, Nat.sub_add_cancel hW]
        rw [hW', zpow_neg, zpow_ofNat]
        field_simp
        nlinarith
      linarith

/-! ## Large arguments -/

/-- Below `-2^12`, `exp x * 2^120 < 1`. -/
theorem exp_le_of_le_neg {x : ℝ} (hx : x ≤ -4096) : exp x * 2 ^ expPrecision ≤ 1 := by
  have h1 : (2 : ℝ) ≤ exp 1 := by
    have := Real.add_one_le_exp 1
    linarith
  have h2 : (2 : ℝ) ^ 4096 ≤ exp 4096 := by
    have : exp 4096 = exp 1 ^ 4096 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [this]
    gcongr
  have h3 : exp x ≤ exp (-4096) := exp_le_exp.mpr hx
  rw [Real.exp_neg] at h3
  have h4 : (2 : ℝ) ^ expPrecision ≤ 2 ^ 4096 := by
    unfold expPrecision
    exact pow_le_pow_right₀ (by norm_num) (by norm_num)
  have hpos := exp_pos 4096
  calc exp x * 2 ^ expPrecision ≤ (exp 4096)⁻¹ * 2 ^ 4096 := by
        gcongr
    _ ≤ (exp 4096)⁻¹ * exp 4096 := by gcongr
    _ = 1 := inv_mul_cancel₀ hpos.ne'

/-! ## The bounds -/

/-- The main case: the sums bound `exp` at the rounded `±y`, and
    `expFinish` turns them into bounds on `exp x * 2^120`. -/
theorem expFinish_spec (neg : Bool) (A : ℕ) (e : ℤ) (m W : ℕ) (hWdef : W = expPrecision + m + 32)
    (hm : ((A.log2 + 1 : ℕ) : ℤ) + e + 8 ≤ m) (sums : ℤ × ℤ)
    (hs : expSeries W (scaledArg A (e - m + W)).1 (scaledArg A (e - m + W)).2 (W + 2) 0
      (2 ^ W) (2 ^ W) 0 0 = some sums) :
    ((expFinish neg W m sums).1 : ℝ) ≤
        exp ((if neg then -1 else 1) * (A * (2 : ℝ) ^ e)) * 2 ^ expPrecision ∧
      exp ((if neg then -1 else 1) * (A * (2 : ℝ) ^ e)) * 2 ^ expPrecision ≤
        (expFinish neg W m sums).2 := by
  obtain ⟨hylo0, hyhi0, hylo, hyhi, hy1⟩ := yBounds A e m W (by omega) hm
  have h2W := two_pow_pos W
  have hW2 : (0 : ℤ) < 2 ^ W := by positivity
  obtain ⟨hlo, hhi, hlo1⟩ := expSeries_spec W _ _ hylo0 hyhi0 hy1 (W + 2) 0 (2 ^ W) (2 ^ W)
    0 0 sums.1 sums.2 hs hW2.le (by simp) (by simp) (by simp) (by simp)
  have hlo2 : ((sums.1 : ℤ) : ℝ) ≤ 2 ^ W * exp (A * (2 : ℝ) ^ e / 2 ^ m) :=
    hlo.trans (by gcongr)
  have hhi2 : 2 ^ W * exp (A * (2 : ℝ) ^ e / 2 ^ m) ≤ ((sums.2 : ℤ) : ℝ) :=
    le_trans (by gcongr) hhi
  have hlopos : (0 : ℝ) < sums.1 := by
    have : (2 : ℤ) ^ W ≤ sums.1 := by simpa using hlo1
    exact_mod_cast lt_of_lt_of_le hW2 this
  have hhipos : (0 : ℝ) < sums.2 := lt_of_lt_of_le (by positivity) hhi2
  -- bounds on exp (±y) at 2^-W
  have hstart : ∀ start : ℤ × ℤ,
      start = (if neg then (2 ^ (2 * W) / sums.2, ceilDiv (2 ^ (2 * W)) sums.1) else sums) →
      0 ≤ start.1 ∧
        (start.1 : ℝ) ≤ 2 ^ W * exp ((if neg then -1 else 1) * (A * (2 : ℝ) ^ e / 2 ^ m)) ∧
        2 ^ W * exp ((if neg then -1 else 1) * (A * (2 : ℝ) ^ e / 2 ^ m)) ≤ start.2 := by
    intro start hst
    subst hst
    set y : ℝ := A * (2 : ℝ) ^ e / 2 ^ m
    cases neg with
    | true =>
      simp only [↓reduceIte, neg_one_mul, Real.exp_neg]
      have h1 : (0 : ℤ) < sums.2 := by exact_mod_cast hhipos
      have h2 : (0 : ℤ) < sums.1 := by exact_mod_cast hlopos
      have hey := exp_pos y
      have hsq : (2 : ℝ) ^ (2 * W) = 2 ^ W * 2 ^ W := by rw [two_mul, pow_add]
      refine ⟨Int.ediv_nonneg (by positivity) h1.le, ?_, ?_⟩
      · calc (((2 ^ (2 * W) / sums.2 : ℤ)) : ℝ) ≤ (((2 : ℤ) ^ (2 * W) : ℤ) : ℝ) / sums.2 :=
            ediv_le_div h1
          _ ≤ 2 ^ W * 2 ^ W / (2 ^ W * exp y) := by
            push_cast
            rw [hsq]
            gcongr
          _ = 2 ^ W * (exp y)⁻¹ := by field_simp
      · have e1 : 2 ^ W * (exp y)⁻¹ = 2 ^ W * 2 ^ W / (2 ^ W * exp y) := by field_simp
        rw [e1]
        calc 2 ^ W * 2 ^ W / (2 ^ W * exp y) ≤ (((2 : ℤ) ^ (2 * W) : ℤ) : ℝ) / sums.1 := by
              push_cast
              rw [hsq]
              gcongr
          _ ≤ _ := div_le_ceilDiv h2
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
      exact ⟨by exact_mod_cast hlopos.le, hlo2, hhi2⟩
  obtain ⟨hr0, hrlo, hrhi⟩ := hstart _ rfl
  have hsqr := expSquare_spec W m _ _ _ hr0 hrlo hrhi
  -- z * 2^m = x
  have hzx : (if neg then -1 else 1) * (A * (2 : ℝ) ^ e / 2 ^ m) * 2 ^ m =
      (if neg then -1 else 1) * (A * (2 : ℝ) ^ e) := by
    field_simp
  rw [hzx] at hsqr
  obtain ⟨-, hrlo', hrhi'⟩ := hsqr
  set x : ℝ := (if neg then -1 else 1) * (A * (2 : ℝ) ^ e)
  set P := expPrecision
  have hd : (0 : ℤ) < 2 ^ (W - P) := by positivity
  have hWP : (2 : ℝ) ^ W = 2 ^ P * 2 ^ (W - P) := by
    rw [← pow_add]
    congr 1
    omega
  have h2d : (0 : ℝ) < 2 ^ (W - P) := two_pow_pos _
  unfold expFinish
  dsimp only
  set r := expSquare W m
    (if neg then (2 ^ (2 * W) / sums.2, ceilDiv (2 ^ (2 * W)) sums.1) else sums)
  constructor
  · calc (((r.1 / 2 ^ (W - P) : ℤ)) : ℝ) ≤ ((r.1 : ℤ) : ℝ) / (((2 : ℤ) ^ (W - P) : ℤ) : ℝ) :=
        ediv_le_div hd
      _ ≤ 2 ^ W * exp x / 2 ^ (W - P) := by
        push_cast
        gcongr
      _ = exp x * 2 ^ P := by
        rw [hWP]
        field_simp
  · have e1 : exp x * 2 ^ P = 2 ^ W * exp x / 2 ^ (W - P) := by
      rw [hWP]
      field_simp
    rw [e1]
    calc 2 ^ W * exp x / 2 ^ (W - P) ≤ ((r.2 : ℤ) : ℝ) / (((2 : ℤ) ^ (W - P) : ℤ) : ℝ) := by
          push_cast
          gcongr
      _ ≤ _ := div_le_ceilDiv hd

theorem expBoundsParts_spec {neg : Bool} {A : ℕ} {e : ℤ} {L H : ℤ}
    (h : expBoundsParts neg A e = some (L, H)) :
    (L : ℝ) ≤ exp ((if neg then -1 else 1) * (A * (2 : ℝ) ^ e)) * 2 ^ expPrecision ∧
      exp ((if neg then -1 else 1) * (A * (2 : ℝ) ^ e)) * 2 ^ expPrecision ≤ H := by
  unfold expBoundsParts at h
  by_cases hA : A = 0
  · simp only [hA, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [hA]
  simp only [hA, ↓reduceIte] at h
  by_cases hbig : ((A.log2 + 1 : ℕ) : ℤ) + e > maxExpLog2
  · simp only [hbig, ↓reduceIte] at h
    cases neg with
    | false => simp at h
    | true =>
      simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [↓reduceIte, Int.cast_zero, Int.cast_one]
      refine ⟨by positivity, exp_le_of_le_neg ?_⟩
      -- |x| ≥ 2^(bl - 1 + e) ≥ 2^12
      have hA1 : (2 : ℝ) ^ A.log2 ≤ A := by exact_mod_cast Nat.log2_self_le hA
      have : (4096 : ℝ) ≤ A * (2 : ℝ) ^ e := by
        calc (4096 : ℝ) = 2 ^ (12 : ℤ) := by norm_num
          _ ≤ 2 ^ ((A.log2 : ℤ) + e) := by
            apply zpow_le_zpow_right₀ (by norm_num)
            simp only [maxExpLog2] at hbig
            push_cast at hbig
            omega
          _ = 2 ^ A.log2 * (2 : ℝ) ^ e := by
            rw [zpow_add₀ (by norm_num)]
            norm_cast
          _ ≤ A * (2 : ℝ) ^ e := mul_le_mul_of_nonneg_right hA1 (two_zpow_pos e).le
      linarith
  simp only [hbig, ↓reduceIte] at h
  obtain ⟨sums, hs, hLH⟩ := Option.map_eq_some_iff.mp h
  have := expFinish_spec neg A e _ _ rfl (by omega) sums hs
  rw [hLH] at this
  exact this

/-- The value of a dyadic number from its parts. -/
theorem dyadicParts_spec {x : ℚ} {A : ℕ} {e : ℤ} (h : dyadicParts x = some (A, e)) :
    (x : ℝ) = (if x < 0 then -1 else 1) * (A * (2 : ℝ) ^ e) := by
  unfold dyadicParts at h
  split_ifs at h with hden
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hx : (x : ℝ) = x.num / x.den := Rat.cast_def x
  have hd : (x.den : ℝ) = 2 ^ x.den.log2 := by exact_mod_cast hden
  have habs : ((x.num.natAbs : ℕ) : ℝ) = |(x.num : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [hx, hd, habs, zpow_neg, zpow_natCast]
  by_cases hneg : x < 0
  · have : (x.num : ℝ) < 0 := by exact_mod_cast Rat.num_neg.mpr hneg
    simp only [hneg, ↓reduceIte]
    rw [abs_of_neg this]
    field_simp
  · have : (0 : ℝ) ≤ x.num := by exact_mod_cast Rat.num_nonneg.mpr (not_lt.mp hneg)
    simp only [hneg, ↓reduceIte]
    rw [abs_of_nonneg this]
    field_simp

/-- **The exp bounds are right**: `L ≤ exp x * 2^120 ≤ H`. -/
theorem expBounds_spec {x : ℚ} {L H : ℤ} (h : expBounds x = some (L, H)) :
    (L : ℝ) ≤ exp x * 2 ^ expPrecision ∧ exp x * 2 ^ expPrecision ≤ H := by
  unfold expBounds at h
  cases hd : dyadicParts x with
  | none => simp [hd] at h
  | some p =>
    obtain ⟨A, e⟩ := p
    simp only [hd] at h
    have hx := dyadicParts_spec hd
    have := expBoundsParts_spec h
    rw [hx]
    simpa using this

/-- The same, as rationals: `exp x` lies in `expInterval x`. -/
theorem expInterval_spec {x lo hi : ℚ} (h : expInterval x = some (lo, hi)) :
    (lo : ℝ) ≤ exp x ∧ exp x ≤ hi := by
  unfold expInterval at h
  cases hb : expBounds x with
  | none => simp [hb] at h
  | some p =>
    obtain ⟨L, H⟩ := p
    simp only [hb, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨h1, h2⟩ := expBounds_spec hb
    have hP : (0 : ℝ) < 2 ^ expPrecision := two_pow_pos _
    push_cast
    constructor
    · rw [div_le_iff₀ hP]
      exact h1
    · rw [le_div_iff₀ hP]
      exact h2

/-! ## Softmax

The weight of entry `j` is `e_j / (e_j + R_j)` with `R_j` the sum of the
other `e_k`; it grows with `e_j` and shrinks with `R_j`. With `e_k` the
exponential of the shifted entries, `el ≤ e_j ≤ eh` and
`S_lo - el ≤ R_j ≤ S_hi - eh`, which gives the two bounds. -/

theorem mapM_option_spec {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' →
      l'.length = l.length ∧ ∀ k (hk : k < l.length) (hk' : k < l'.length), f l[k] = some l'[k]
  | [], l', h => by
    simp only [List.mapM_nil] at h
    cases h
    simp
  | a :: l, l', h => by
    simp only [List.mapM_cons] at h
    cases ha : f a with
    | none => simp [ha] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [ha, hl] at h
      | some bs =>
        simp only [ha, hl, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        obtain ⟨hlen, hk⟩ := mapM_option_spec hl
        refine ⟨by simp [hlen], fun k hk1 hk2 => ?_⟩
        cases k with
        | zero => simpa using ha
        | succ k => simpa using hk k (by simpa using hk1) (by simpa using hk2)

theorem sum_le_sum_of_le : ∀ {a b : List ℝ}, a.length = b.length →
    (∀ k (h1 : k < a.length) (h2 : k < b.length), a[k] ≤ b[k]) → a.sum ≤ b.sum
  | [], [], _, _ => le_refl _
  | [], _ :: _, hlen, _ => by simp at hlen
  | _ :: _, [], hlen, _ => by simp at hlen
  | x :: a, y :: b, hlen, h => by
    simp only [List.sum_cons]
    have hxy : x ≤ y := h 0 (by simp) (by simp)
    have := sum_le_sum_of_le (a := a) (b := b) (by simpa using hlen)
      (fun k h1 h2 => h (k + 1) (by simpa using h1) (by simpa using h2))
    linarith

/-- In two lists with `a k ≤ b k` everywhere, the difference of the sums is
    at least the difference at any one entry. -/
theorem le_sum_sub_sum : ∀ {a b : List ℝ}, a.length = b.length →
    (∀ k (h1 : k < a.length) (h2 : k < b.length), a[k] ≤ b[k]) →
    ∀ j (h1 : j < a.length) (h2 : j < b.length), b[j] - a[j] ≤ b.sum - a.sum
  | [], _, _, _, j, h1, _ => by simp at h1
  | _ :: _, [], hlen, _, _, _, _ => by simp at hlen
  | x :: a, y :: b, hlen, h, j, h1, h2 => by
    simp only [List.sum_cons]
    have hlen' : a.length = b.length := by simpa using hlen
    have hab : ∀ k (h1 : k < a.length) (h2 : k < b.length), a[k] ≤ b[k] :=
      fun k h1 h2 => h (k + 1) (by simpa using h1) (by simpa using h2)
    have hxy : x ≤ y := h 0 (by simp) (by simp)
    have hsum := sum_le_sum_of_le hlen' hab
    cases j with
    | zero =>
      simp only [List.getElem_cons_zero]
      linarith
    | succ j =>
      simp only [List.getElem_cons_succ]
      have := le_sum_sub_sum hlen' hab j (by simpa using h1) (by simpa using h2)
      linarith

/-- The two bounds on a weight, from bounds on the exponentials: `el ≤ ej ≤ eh`
    for the entry, `0 ≤ R = S - ej` for the others, and
    `S_lo - el ≤ R ≤ S_hi - eh`. -/
theorem softmax_weight_bounds {el ej eh S Slo Shi : ℝ} (hel : el ≤ ej) (heh : ej ≤ eh)
    (hej : 0 < ej) (hS : ej ≤ S) (hlo : Slo - el ≤ S - ej) (hhi : S - ej ≤ Shi - eh) :
    (0 < el + Shi - eh → el / (el + Shi - eh) ≤ ej / S) ∧
      (0 < eh + Slo - el → ej / S ≤ eh / (eh + Slo - el)) := by
  have hSpos : 0 < S := lt_of_lt_of_le hej hS
  have hR : 0 ≤ S - ej := sub_nonneg.mpr hS
  constructor
  · intro hden
    rw [div_le_div_iff₀ hden hSpos]
    nlinarith [mul_le_mul_of_nonneg_right hel hR, mul_le_mul_of_nonneg_left hhi hej.le]
  · intro hden
    rw [div_le_div_iff₀ hSpos hden]
    nlinarith [mul_le_mul_of_nonneg_left hlo hej.le, mul_le_mul_of_nonneg_right heh hR]

/-- The bounds on one row are right: whatever the true entries `z k` in
    `[lo k, hi k]`, the weight of entry `j`, `exp (z j) / Σ exp (z k)`, lies
    between its bounds, at `2^-120`. Any shift `c` will do. -/
theorem softmaxRowBoundsAt_spec {c : ℚ} {n : ℕ} {lo hi : ℕ → ℚ} {z : ℕ → ℝ}
    {bs : List (ℤ × ℤ)}
    (h : softmaxRowBoundsAt c ((List.range n).map lo) ((List.range n).map hi) = some bs)
    (hz : ∀ k < n, (lo k : ℝ) ≤ z k ∧ z k ≤ hi k) {j : ℕ} (hj : j < n) :
    ∃ b, bs[j]? = some b ∧
      (b.1 : ℝ) ≤ exp (z j) / ((List.range n).map fun k => exp (z k)).sum * 2 ^ expPrecision ∧
      exp (z j) / ((List.range n).map fun k => exp (z k)).sum * 2 ^ expPrecision ≤ b.2 := by
  unfold softmaxRowBoundsAt at h
  cases hEl : ((List.range n).map lo).mapM (fun v => (expBounds (v - c)).map (·.1)) with
  | none => simp [hEl] at h
  | some El =>
  cases hEh : ((List.range n).map hi).mapM (fun v => (expBounds (v - c)).map (·.2)) with
  | none => simp [hEl, hEh] at h
  | some Eh =>
  simp only [hEl, hEh, Option.some.injEq] at h
  subst h
  obtain ⟨hElLen, hElk⟩ := mapM_option_spec hEl
  obtain ⟨hEhLen, hEhk⟩ := mapM_option_spec hEh
  simp only [List.length_map, List.length_range] at hElLen hEhLen
  set P := expPrecision
  -- the shifted exponentials, at 2^-120
  set e : ℕ → ℝ := fun k => exp (z k - c) * 2 ^ P with he
  have hepos : ∀ k, 0 < e k := fun k => by positivity
  have hEl_le : ∀ k (hk : k < El.length), (El[k] : ℝ) ≤ e k := by
    intro k hk
    have hkn : k < n := hElLen ▸ hk
    have h1 := hElk k (by simpa using hkn) hk
    simp only [List.getElem_map, List.getElem_range] at h1
    obtain ⟨⟨L, H⟩, hb, hL⟩ := Option.map_eq_some_iff.mp h1
    have hL' : L = El[k] := hL
    rw [← hL']
    calc (L : ℝ) ≤ exp ((lo k - c : ℚ) : ℝ) * 2 ^ P := (expBounds_spec hb).1
      _ ≤ e k := by
        simp only [he]
        gcongr
        push_cast
        linarith [(hz k hkn).1]
  have hEh_ge : ∀ k (hk : k < Eh.length), e k ≤ (Eh[k] : ℝ) := by
    intro k hk
    have hkn : k < n := hEhLen ▸ hk
    have h1 := hEhk k (by simpa using hkn) hk
    simp only [List.getElem_map, List.getElem_range] at h1
    obtain ⟨⟨L, H⟩, hb, hH⟩ := Option.map_eq_some_iff.mp h1
    have hH' : H = Eh[k] := hH
    rw [← hH']
    calc e k ≤ exp ((hi k - c : ℚ) : ℝ) * 2 ^ P := by
          simp only [he]
          gcongr
          push_cast
          linarith [(hz k hkn).2]
      _ ≤ (H : ℝ) := (expBounds_spec hb).2
  have hjEl : j < El.length := by omega
  have hjEh : j < Eh.length := by omega
  -- sums over the row, as reals
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ((List.range n).map e).sum := ⟨_, rfl⟩
  have hlo_le : e j - (El[j] : ℝ) ≤ S - (El.sum : ℝ) := by
    have := le_sum_sub_sum (a := El.map (fun v : ℤ => (v : ℝ))) (b := (List.range n).map e)
      (by simp [hElLen])
      (fun k h1 h2 => by
        simp only [List.getElem_map, List.getElem_range]
        exact hEl_le k (by simpa using h1)) j (by simpa using hjEl) (by simpa using hj)
    simpa [hS, Int.cast_list_sum] using this
  have hhi_le : S - e j ≤ (Eh.sum : ℝ) - (Eh[j] : ℝ) := by
    have := le_sum_sub_sum (a := (List.range n).map e) (b := Eh.map (fun v : ℤ => (v : ℝ)))
      (by simp [hEhLen])
      (fun k h1 h2 => by
        simp only [List.getElem_map, List.getElem_range]
        exact hEh_ge k (by simpa using h2)) j (by simpa using hj) (by simpa using hjEh)
    simp only [List.getElem_map, List.getElem_range] at this
    rw [hS]
    push_cast [Int.cast_list_sum]
    linarith
  have hejS : e j ≤ S := by
    rw [hS]
    apply List.single_le_sum
    · intro x hx
      simp only [List.mem_map, List.mem_range] at hx
      obtain ⟨k, -, rfl⟩ := hx
      exact (hepos k).le
    · simp only [List.mem_map, List.mem_range]
      exact ⟨j, hj, rfl⟩
  have hSpos : 0 < S := lt_of_lt_of_le (hepos j) hejS
  -- the true weight is e j / S
  have hweight : exp (z j) / ((List.range n).map fun k => exp (z k)).sum * 2 ^ P =
      e j / S * 2 ^ P := by
    have hmul : S = ((List.range n).map fun k => exp (z k)).sum * (exp (-(c : ℝ)) * 2 ^ P) := by
      rw [hS, ← List.sum_map_mul_right]
      congr 1
      apply List.map_congr_left
      intro k _
      simp only [he, sub_eq_add_neg, exp_add]
      ring
    have hej : e j = exp (z j) * (exp (-(c : ℝ)) * 2 ^ P) := by
      simp only [he, sub_eq_add_neg, exp_add]
      ring
    rw [hej, hmul]
    have : 0 < exp (-(c : ℝ)) * 2 ^ P := by positivity
    have : 0 < ((List.range n).map fun k => exp (z k)).sum := by
      have h2 : 0 < S := hSpos
      rw [hmul] at h2
      exact pos_of_mul_pos_left h2 this.le
    field_simp
  obtain ⟨hlow, hup⟩ := softmax_weight_bounds (Slo := (El.sum : ℝ)) (Shi := (Eh.sum : ℝ))
    (hEl_le j hjEl) (hEh_ge j hjEh) (hepos j) hejS (by linarith) hhi_le
  have hjz : j < ((El.zip Eh).map fun p => (softmaxLower p.1 p.2 Eh.sum,
      softmaxUpper p.1 p.2 El.sum)).length := by simp [hjEl, hjEh]
  refine ⟨(softmaxLower El[j] Eh[j] Eh.sum, softmaxUpper El[j] Eh[j] El.sum), ?_, ?_, ?_⟩
  · rw [List.getElem?_eq_getElem hjz, List.getElem_map, List.getElem_zip]
  · rw [hweight]
    unfold softmaxLower
    split_ifs with hden
    · have hden' : (0 : ℝ) < (El[j] : ℝ) + Eh.sum - Eh[j] := by exact_mod_cast hden
      rw [Int.cast_max, Int.cast_zero]
      apply max_le (by positivity)
      calc ((El[j] * 2 ^ P / (El[j] + Eh.sum - Eh[j]) : ℤ) : ℝ)
          ≤ ((El[j] * 2 ^ P : ℤ) : ℝ) / ((El[j] + Eh.sum - Eh[j] : ℤ) : ℝ) := ediv_le_div hden
        _ = (El[j] : ℝ) / ((El[j] : ℝ) + Eh.sum - Eh[j]) * 2 ^ P := by
          push_cast
          ring
        _ ≤ e j / S * 2 ^ P := mul_le_mul_of_nonneg_right (hlow hden') (by positivity)
    · simp only [Int.cast_zero]
      positivity
  · rw [hweight]
    have hs1 : e j / S ≤ 1 := (div_le_one hSpos).mpr hejS
    have hle1 : e j / S * 2 ^ P ≤ 2 ^ P := by
      calc e j / S * 2 ^ P ≤ 1 * 2 ^ P := mul_le_mul_of_nonneg_right hs1 (by positivity)
        _ = 2 ^ P := one_mul _
    unfold softmaxUpper
    split_ifs with hden
    · have hden' : (0 : ℝ) < (Eh[j] : ℝ) + El.sum - El[j] := by exact_mod_cast hden
      rw [Int.cast_min]
      apply le_min
      · push_cast
        exact hle1
      · calc e j / S * 2 ^ P ≤ (Eh[j] : ℝ) / ((Eh[j] : ℝ) + El.sum - El[j]) * 2 ^ P :=
              mul_le_mul_of_nonneg_right (hup hden') (by positivity)
          _ = ((Eh[j] * 2 ^ P : ℤ) : ℝ) / ((Eh[j] + El.sum - El[j] : ℤ) : ℝ) := by
              push_cast
              ring
          _ ≤ _ := div_le_ceilDiv hden
    · push_cast
      exact hle1

/-- `softmaxRowBounds` (shifted by the largest upper end) is right. -/
theorem softmaxRowBounds_spec {n : ℕ} {lo hi : ℕ → ℚ} {z : ℕ → ℝ} {bs : List (ℤ × ℤ)}
    (h : softmaxRowBounds ((List.range n).map lo) ((List.range n).map hi) = some bs)
    (hz : ∀ k < n, (lo k : ℝ) ≤ z k ∧ z k ≤ hi k) {j : ℕ} (hj : j < n) :
    ∃ b, bs[j]? = some b ∧
      (b.1 : ℝ) ≤ exp (z j) / ((List.range n).map fun k => exp (z k)).sum * 2 ^ expPrecision ∧
      exp (z j) / ((List.range n).map fun k => exp (z k)).sum * 2 ^ expPrecision ≤ b.2 := by
  unfold softmaxRowBounds at h
  split at h
  · cases h
  · rename_i h0 hs heq
    rw [← heq] at h
    exact softmaxRowBoundsAt_spec h hz hj

end CompactCheck
