import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.BigOperators.Group.List
import CompactCheck.Soundness
import CompactCheck.ExpSound
import CompactCheck.General

/-!
# The operations of the checker on attention networks keep enclosures

An interval tensor `v` encloses a real tensor `t` (`DT.Encl`) if they have
the same shape and entry `j` of `t` lies between `lo[j] * 2^e` and
`hi[j] * 2^e`. Each operation of `General.lean`, given interval tensors
that enclose its real arguments, succeeds on the real arguments in the sense
of `Semantics.lean` (with the real exponential) and encloses the real
result: `dbinary_sim`, `dneg_encl`, `dsum_sim`, `dexp_sim`, `dmove_sim`
(indexing, transpose, unsqueeze, expand), `djoin_sim` (cat, stack),
`dsoftmax_sim` and `dmatmul_sim`. The weights are enclosed by their
conversion (`DT.ofRat_encl`).

`GeneralSound.lean` puts these together into the soundness of the whole
checker.
-/

namespace CompactCheck

open Real

/-! ## Dyadic numbers -/

/-- The value of `m * 2^e`. -/
noncomputable def dv (m : ℤ) (e : ℤ) : ℝ := m * (2 : ℝ) ^ e

theorem two_zpow_pos' (e : ℤ) : (0 : ℝ) < 2 ^ e := zpow_pos (by norm_num) e

theorem dv_le_dv {a b : ℤ} (e : ℤ) (h : a ≤ b) : dv a e ≤ dv b e := by
  unfold dv
  have : (a : ℝ) ≤ b := by exact_mod_cast h
  exact mul_le_mul_of_nonneg_right this (two_zpow_pos' e).le

theorem dv_lt_dv {a b : ℤ} (e : ℤ) (h : a < b) : dv a e < dv b e := by
  unfold dv
  have : (a : ℝ) < b := by exact_mod_cast h
  exact mul_lt_mul_of_pos_right this (two_zpow_pos' e)

@[simp] theorem dv_zero (e : ℤ) : dv 0 e = 0 := by simp [dv]

theorem dv_add (a b : ℤ) (e : ℤ) : dv (a + b) e = dv a e + dv b e := by
  unfold dv
  push_cast
  ring

theorem dv_sub (a b : ℤ) (e : ℤ) : dv (a - b) e = dv a e - dv b e := by
  unfold dv
  push_cast
  ring

theorem dv_neg (a : ℤ) (e : ℤ) : dv (-a) e = -dv a e := by
  unfold dv
  push_cast
  ring

theorem dv_mul (a b : ℤ) (ea eb : ℤ) : dv (a * b) (ea + eb) = dv a ea * dv b eb := by
  unfold dv
  rw [zpow_add₀ (by norm_num)]
  push_cast
  ring

theorem dv_shift (a : ℤ) (e : ℤ) (k : ℕ) : dv (a * 2 ^ k) (e - k) = dv a e := by
  unfold dv
  rw [zpow_sub₀ (by norm_num), zpow_natCast]
  push_cast
  field_simp

theorem dv_list_sum (l : List ℤ) (e : ℤ) : dv l.sum e = (l.map (dv · e)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [dv_add, ih]

/-! ## Enclosures -/

/-- The interval tensor `v` encloses the real tensor `t`: same shape, as
    many entries, exact only if the two ends agree, and entry `j` of `t`
    between `lo[j] * 2^e` and `hi[j] * 2^e` (all three 0 past the end). -/
def DT.Encl (v : DT) (t : Tensor ℝ) : Prop :=
  t.shape = v.shape ∧ t.data.size = shapeSize v.shape ∧ v.lo.size = shapeSize v.shape ∧
    v.hi.size = shapeSize v.shape ∧ (v.exact = true → v.lo = v.hi) ∧
    ∀ j, dv (mget v.lo j) v.e ≤ t.get j ∧ t.get j ≤ dv (mget v.hi j) v.e

theorem mget_of_le {a : Array ℤ} {j : ℕ} (h : a.size ≤ j) : mget a j = 0 := by
  simp [mget, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h]

theorem Tensor.get_of_le {α : Type} [Zero α] {t : Tensor α} {j : ℕ} (h : t.data.size ≤ j) :
    t.get j = 0 := by
  simp [Tensor.get, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h]

/-- To show an enclosure, it is enough to check the entries in range. -/
theorem DT.Encl.mk {v : DT} {t : Tensor ℝ} (hs : t.shape = v.shape)
    (ht : t.data.size = shapeSize v.shape) (hlo : v.lo.size = shapeSize v.shape)
    (hhi : v.hi.size = shapeSize v.shape) (hex : v.exact = true → v.lo = v.hi)
    (h : ∀ j < shapeSize v.shape, dv (mget v.lo j) v.e ≤ t.get j ∧ t.get j ≤ dv (mget v.hi j) v.e) :
    v.Encl t := by
  refine ⟨hs, ht, hlo, hhi, hex, fun j => ?_⟩
  by_cases hj : j < shapeSize v.shape
  · exact h j hj
  · rw [mget_of_le (by omega), mget_of_le (by omega), Tensor.get_of_le (by omega)]
    simp

/-- An exact tensor encloses only its own value. -/
theorem DT.Encl.eq_of_exact {v : DT} {t : Tensor ℝ} (h : v.Encl t) (hex : v.exact = true) (j : ℕ) :
    t.get j = dv (mget v.lo j) v.e := by
  obtain ⟨-, -, -, -, he, hj⟩ := h
  have := hj j
  rw [he hex] at this ⊢
  linarith [this.1, this.2]

/-! ## Multi-indices -/

theorem strides_length (s : List ℕ) : (strides s).length = s.length := by
  induction s with
  | nil => rfl
  | cons d s ih => simp [strides, ih]

/-- `ravel` after `unravel` gives the position back, modulo the size. -/
theorem ravel_unravel (s : List ℕ) (j : ℕ) : ravel s (unravel s j) = j % shapeSize s := by
  induction s with
  | nil => simp [ravel, unravel, strides, shapeSize, Nat.mod_one]
  | cons d s ih =>
    have h1 : unravel (d :: s) j = (j / shapeSize s % d) :: unravel s j := by
      simp [unravel, strides]
    have h2 : ∀ (a : ℕ) (i : List ℕ), ravel (d :: s) (a :: i) = shapeSize s * a + ravel s i := by
      intro a i
      simp [ravel, strides]
    rw [h1, h2, ih]
    have : shapeSize (d :: s) = shapeSize s * d := by
      simp [shapeSize, Nat.mul_comm]
    rw [this, Nat.mod_mul]
    ring

theorem ravel_unravel_of_lt {s : List ℕ} {j : ℕ} (h : j < shapeSize s) :
    ravel s (unravel s j) = j := by
  rw [ravel_unravel, Nat.mod_eq_of_lt h]

theorem Tensor.ofFn_data_size {α : Type} (s : List ℕ) (f : List ℕ → α) :
    (Tensor.ofFn s f).data.size = shapeSize s := by
  simp [Tensor.ofFn]

@[simp] theorem Tensor.ofFn_shape {α : Type} (s : List ℕ) (f : List ℕ → α) :
    (Tensor.ofFn s f).shape = s := rfl

theorem Tensor.ofFn_get {α : Type} [Zero α] (s : List ℕ) (f : List ℕ → α) {j : ℕ}
    (hj : j < shapeSize s) : (Tensor.ofFn s f).get j = f (unravel s j) := by
  simp [Tensor.ofFn, Tensor.get, Array.getD_eq_getD_getElem?, hj]

theorem mget_map_range (n : ℕ) (g : ℕ → ℤ) {j : ℕ} (hj : j < n) :
    mget ((Array.range n).map g) j = g j := by
  simp [mget, Array.getD_eq_getD_getElem?, hj]

theorem Tensor.get_mk_map_range {α : Type} [Zero α] (s : List ℕ) (n : ℕ) (g : ℕ → α) {j : ℕ}
    (hj : j < n) : (⟨s, (Array.range n).map g⟩ : Tensor α).get j = g j := by
  simp [Tensor.get, Array.getD_eq_getD_getElem?, hj]

theorem Tensor.entry_eq {α : Type} [Zero α] (t : Tensor α) (i : List ℕ) :
    t.entry i = t.get (ravel t.shape i) := rfl

theorem unravelWith_eq (s : List ℕ) (j : ℕ) : unravelWith (strides s) s j = unravel s j := rfl

theorem ravelWith_eq (s i : List ℕ) : ravelWith (strides s) i = ravel s i := rfl

/-! ## Enclosures of the inputs -/

/-- The same values at another exponent: still an enclosure. -/
theorem DT.shift_encl {v : DT} {t : Tensor ℝ} (h : v.Encl t) (k : ℕ) : (v.shift k).Encl t := by
  by_cases hk : k = 0
  · simp only [DT.shift, hk, ↓reduceIte]
    exact h
  have e1 : v.shift k = ⟨v.shape, v.lo.map (· * 2 ^ k),
      if v.exact then v.lo.map (· * 2 ^ k) else v.hi.map (· * 2 ^ k), v.e - k, v.exact⟩ := by
    simp only [DT.shift, hk, ↓reduceIte]
  rw [e1]
  obtain ⟨hs, ht, hlo, hhi, hex, hj⟩ := h
  have hmap : ∀ (a : Array ℤ) (j : ℕ), mget (a.map (· * 2 ^ k)) j = mget a j * 2 ^ k := by
    intro a j
    simp only [mget, Array.getD_eq_getD_getElem?, Array.getElem?_map]
    cases a[j]? <;> simp
  refine DT.Encl.mk hs ht (by simp [hlo]) ?_ ?_ ?_
  · split_ifs <;> simp [hlo, hhi]
  · intro hx
    simp only at hx
    simp [hx]
  · intro j _
    simp only
    split_ifs with hx
    · rw [hmap, dv_shift]
      have := hj j
      rw [← hex hx] at this
      exact this
    · rw [hmap, hmap, dv_shift, dv_shift]
      exact hj j

/-- An exact tensor of rationals given by an integer array and a power of
    two encloses its own value. -/
theorem DT.ofInts_encl {shape : List ℕ} {m : Array ℤ} {e : ℤ} {t : Tensor ℝ}
    (hs : t.shape = shape) (hsize : m.size = shapeSize shape) (ht : t.data.size = shapeSize shape)
    (hv : ∀ j < shapeSize shape, t.get j = dv (mget m j) e) : (DT.ofInts shape m e).Encl t := by
  refine DT.Encl.mk hs ht hsize hsize (fun _ => rfl) ?_
  intro j hj
  simp only [DT.ofInts]
  rw [hv j hj]
  exact ⟨le_refl _, le_refl _⟩

/-- A weight converted to an interval tensor encloses the weight. -/
theorem DT.ofRat_encl {t : Tensor ℚ} {v : DT} (h : DT.ofRat t = some v) :
    v.Encl (t.map fun q : ℚ => (q : ℝ)) := by
  unfold DT.ofRat at h
  split_ifs at h with hall
  simp only [Option.some.injEq] at h
  subst h
  simp only [Bool.and_eq_true] at hall
  obtain ⟨hwf, hdy⟩ := hall
  have hsize : t.data.size = shapeSize t.shape := by simpa [Tensor.wellFormed] using hwf
  set k := t.data.foldl (fun k q => max k q.den.log2) 0 with hk
  apply DT.ofInts_encl (by simp) (by simp [hsize]) (by simp [hsize])
  intro j hj
  have hj' : j < t.data.size := by omega
  have hmem : t.data[j] ∈ t.data := Array.getElem_mem hj'
  set q := t.data[j] with hq
  have hden : q.den = 2 ^ q.den.log2 := by
    have := Array.all_eq_true.mp hdy j hj'
    simpa using this
  have hle : q.den.log2 ≤ k := by
    rw [hk]
    have key : ∀ (l : List ℚ) (a : ℕ), q ∈ l →
        q.den.log2 ≤ l.foldl (fun k q => max k q.den.log2) a := by
      intro l
      induction l with
      | nil => intro a h; simp at h
      | cons x l ih =>
        intro a h
        simp only [List.foldl_cons]
        rcases List.mem_cons.mp h with rfl | h
        · have : ∀ (l : List ℚ) (b : ℕ), b ≤ l.foldl (fun k q => max k q.den.log2) b := by
            intro l
            induction l with
            | nil => intro b; simp
            | cons y l ih2 =>
              intro b
              simp only [List.foldl_cons]
              exact le_trans (le_max_left _ _) (ih2 _)
          exact le_trans (le_max_right _ _) (this l _)
        · exact ih _ h
    rw [← Array.foldl_toList]
    exact key _ _ (Array.mem_toList_iff.mpr hmem)
  simp only [Tensor.map, Tensor.get, Array.getD_eq_getD_getElem?, hj',
    Array.getElem?_eq_getElem, Option.getD_some, mget, Array.size_map, Array.getElem_map]
  rw [← hq]
  unfold dv
  have hq' : (q : ℝ) = q.num / q.den := Rat.cast_def q
  have hd : (q.den : ℝ) = 2 ^ q.den.log2 := by exact_mod_cast hden
  rw [hq', hd]
  push_cast
  rw [zpow_neg, zpow_natCast]
  have h2 : (2 : ℝ) ^ k = 2 ^ (k - q.den.log2) * 2 ^ q.den.log2 := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  rw [h2]
  field_simp

/-! ## Products of intervals -/

theorem dv_min (a b : ℤ) (e : ℤ) : dv (min a b) e = min (dv a e) (dv b e) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (dv_le_dv e h)]
  · rw [min_eq_right h, min_eq_right (dv_le_dv e h)]

theorem dv_max (a b : ℤ) (e : ℤ) : dv (max a b) e = max (dv a e) (dv b e) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (dv_le_dv e h)]
  · rw [max_eq_left h, max_eq_left (dv_le_dv e h)]

theorem dv_nonneg_iff {a : ℤ} (e : ℤ) : 0 ≤ dv a e ↔ 0 ≤ a := by
  unfold dv
  constructor
  · intro h
    have := (mul_nonneg_iff_of_pos_right (two_zpow_pos' e)).mp h
    exact_mod_cast this
  · intro h
    exact mul_nonneg (by exact_mod_cast h) (two_zpow_pos' e).le

/-- `x * y` lies between the smallest and the largest of the four products
    of the ends. -/
theorem mul_mem_corners {A A' B B' x y : ℝ} (h1 : A ≤ x) (h2 : x ≤ A') (h3 : B ≤ y)
    (h4 : y ≤ B') :
    min (min (A * B) (A * B')) (min (A' * B) (A' * B')) ≤ x * y ∧
      x * y ≤ max (max (A * B) (A * B')) (max (A' * B) (A' * B')) := by
  -- with y fixed, x * y lies between A * y and A' * y
  have hxl : min (A * y) (A' * y) ≤ x * y := by
    rcases le_total 0 y with hy | hy
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right h1 hy)
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_right h2 hy)
  have hxh : x * y ≤ max (A * y) (A' * y) := by
    rcases le_total 0 y with hy | hy
    · exact (mul_le_mul_of_nonneg_right h2 hy).trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonpos_right h1 hy).trans (le_max_left _ _)
  -- and c * y between c * B and c * B'
  have hc : ∀ c : ℝ, min (c * B) (c * B') ≤ c * y ∧ c * y ≤ max (c * B) (c * B') := by
    intro c
    rcases le_total 0 c with hc | hc
    · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left h3 hc),
        (mul_le_mul_of_nonneg_left h4 hc).trans (le_max_right _ _)⟩
    · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left h4 hc),
        (mul_le_mul_of_nonpos_left h3 hc).trans (le_max_left _ _)⟩
  constructor
  · calc min (min (A * B) (A * B')) (min (A' * B) (A' * B'))
        ≤ min (A * y) (A' * y) := min_le_min (hc A).1 (hc A').1
      _ ≤ x * y := hxl
  · calc x * y ≤ max (A * y) (A' * y) := hxh
      _ ≤ max (max (A * B) (A * B')) (max (A' * B) (A' * B')) := max_le_max (hc A).2 (hc A').2

/-- Python's bounds on a product are right. -/
theorem prod_bounds {ea eb : Bool} {al ah bl bh : ℤ} {ex ey : ℤ} {x y : ℝ}
    (hx1 : dv al ex ≤ x) (hx2 : x ≤ dv ah ex) (hy1 : dv bl ey ≤ y) (hy2 : y ≤ dv bh ey)
    (hea : ea = true → al = ah) (heb : eb = true → bl = bh) :
    dv (prodLo ea eb al ah bl bh) (ex + ey) ≤ x * y ∧
      x * y ≤ dv (prodHi ea eb al ah bl bh) (ex + ey) := by
  unfold prodLo prodHi
  cases ea <;> cases eb <;> simp only [Bool.and_true, Bool.and_false, Bool.false_eq_true,
    ↓reduceIte]
  · -- both intervals
    rw [dv_min, dv_min, dv_min, dv_max, dv_max, dv_max, dv_mul, dv_mul, dv_mul, dv_mul]
    exact mul_mem_corners hx1 hx2 hy1 hy2
  · -- y exact
    have hb := heb rfl
    subst hb
    have hy : y = dv bl ey := le_antisymm hy2 hy1
    subst hy
    split_ifs with hs
    · have hs' := (dv_nonneg_iff ey).mpr hs
      rw [dv_mul, dv_mul]
      exact ⟨mul_le_mul_of_nonneg_right hx1 hs', mul_le_mul_of_nonneg_right hx2 hs'⟩
    · have hs' : dv bl ey ≤ 0 := le_of_lt (lt_of_not_ge fun h => hs ((dv_nonneg_iff ey).mp h))
      rw [dv_mul, dv_mul]
      exact ⟨mul_le_mul_of_nonpos_right hx2 hs', mul_le_mul_of_nonpos_right hx1 hs'⟩
  · -- x exact
    have ha := hea rfl
    subst ha
    have hx : x = dv al ex := le_antisymm hx2 hx1
    subst hx
    split_ifs with hs
    · have hs' := (dv_nonneg_iff ex).mpr hs
      rw [dv_mul, dv_mul]
      exact ⟨mul_le_mul_of_nonneg_left hy1 hs', mul_le_mul_of_nonneg_left hy2 hs'⟩
    · have hs' : dv al ex ≤ 0 := le_of_lt (lt_of_not_ge fun h => hs ((dv_nonneg_iff ex).mp h))
      rw [dv_mul, dv_mul]
      exact ⟨mul_le_mul_of_nonpos_left hy2 hs', mul_le_mul_of_nonpos_left hy1 hs'⟩
  · -- both exact
    have ha := hea rfl
    have hb := heb rfl
    subst ha hb
    have hx : x = dv al ex := le_antisymm hx2 hx1
    have hy : y = dv bl ey := le_antisymm hy2 hy1
    rw [dv_mul, hx, hy]
    exact ⟨le_refl _, le_refl _⟩

/-! ## Entrywise operations -/

/-- The bounds of `binLo`, `binHi` are right: sums and differences at a
    common exponent, products at the sum of the exponents. -/
theorem bin_bounds (f : BinOp) {ea eb : Bool} {al ah bl bh : ℤ} {ex ey e : ℤ} {x y : ℝ}
    (he : f = .mul ∧ e = ex + ey ∨ f ≠ .mul ∧ ex = e ∧ ey = e)
    (hx1 : dv al ex ≤ x) (hx2 : x ≤ dv ah ex) (hy1 : dv bl ey ≤ y) (hy2 : y ≤ dv bh ey)
    (hea : ea = true → al = ah) (heb : eb = true → bl = bh) :
    dv (binLo f ea eb al ah bl bh) e ≤ f.apply x y ∧
      f.apply x y ≤ dv (binHi f ea eb al ah bl bh) e := by
  cases f with
  | mul =>
    rcases he with ⟨-, rfl⟩ | ⟨h, -⟩
    · exact prod_bounds hx1 hx2 hy1 hy2 hea heb
    · exact absurd rfl h
  | add =>
    rcases he with ⟨h, -⟩ | ⟨-, rfl, rfl⟩
    · cases h
    simp only [binLo, binHi, BinOp.apply, dv_add]
    constructor <;> linarith
  | sub =>
    rcases he with ⟨h, -⟩ | ⟨-, rfl, rfl⟩
    · cases h
    simp only [binLo, binHi, BinOp.apply, dv_sub]
    constructor <;> linarith

theorem binHi_eq_binLo (f : BinOp) {al bl : ℤ} :
    binHi f true true al al bl bl = binLo f true true al al bl bl := by
  cases f <;> simp [binLo, binHi, prodLo, prodHi]

/-- The entry of a tensor at a broadcast index is the entry the interval
    tensor reads there. -/
theorem DT.Encl.entry {v : DT} {t : Tensor ℝ} (h : v.Encl t) (i : List ℕ) :
    dv (mget v.lo (ravel v.shape i)) v.e ≤ t.entry i ∧
      t.entry i ≤ dv (mget v.hi (ravel v.shape i)) v.e := by
  rw [Tensor.entry_eq, h.1]
  exact h.2.2.2.2.2 _

theorem DT.Encl.lo_eq_hi {v : DT} {t : Tensor ℝ} (h : v.Encl t) (hex : v.exact = true) (j : ℕ) :
    mget v.lo j = mget v.hi j := by
  rw [h.2.2.2.2.1 hex]

theorem bcastPos_eq (s sh : List ℕ) (j : ℕ) :
    bcastPos (strides s) s (strides sh) sh j = ravel sh (broadcastIndex sh (unravel s j)) := rfl

theorem mget_dbinLo (f : BinOp) (a b : DT) (s : List ℕ) {j : ℕ} (hj : j < shapeSize s) :
    mget (dbinLo f a b s) j =
      binLo f a.exact b.exact (mget a.lo (ravel a.shape (broadcastIndex a.shape (unravel s j))))
        (mget a.hi (ravel a.shape (broadcastIndex a.shape (unravel s j))))
        (mget b.lo (ravel b.shape (broadcastIndex b.shape (unravel s j))))
        (mget b.hi (ravel b.shape (broadcastIndex b.shape (unravel s j)))) := by
  unfold dbinLo
  rw [mget_map_range _ _ hj]
  rfl

theorem mget_dbinHi (f : BinOp) (a b : DT) (s : List ℕ) {j : ℕ} (hj : j < shapeSize s)
    (hx : (a.exact && b.exact) = false) :
    mget (dbinHi f a b s) j =
      binHi f a.exact b.exact (mget a.lo (ravel a.shape (broadcastIndex a.shape (unravel s j))))
        (mget a.hi (ravel a.shape (broadcastIndex a.shape (unravel s j))))
        (mget b.lo (ravel b.shape (broadcastIndex b.shape (unravel s j))))
        (mget b.hi (ravel b.shape (broadcastIndex b.shape (unravel s j)))) := by
  unfold dbinHi
  simp only [hx, Bool.false_eq_true, ↓reduceIte]
  rw [mget_map_range _ _ hj]
  rfl

theorem dbinaryAt_encl {f : BinOp} {a b : DT} {ta tb : Tensor ℝ} {s : List ℕ} {e : ℤ}
    (ha : a.Encl ta) (hb : b.Encl tb)
    (he : f = .mul ∧ e = a.e + b.e ∨ f ≠ .mul ∧ a.e = e ∧ b.e = e) :
    (dbinaryAt f a b s e).Encl (Tensor.ofFn s fun i =>
      f.apply (ta.entry (broadcastIndex ta.shape i)) (tb.entry (broadcastIndex tb.shape i))) := by
  have hea : a.exact = true → ∀ j, mget a.lo j = mget a.hi j := fun hx j => ha.lo_eq_hi hx j
  have heb : b.exact = true → ∀ j, mget b.lo j = mget b.hi j := fun hx j => hb.lo_eq_hi hx j
  -- the bounds at each output entry
  have key : ∀ j < shapeSize s,
      dv (mget (dbinLo f a b s) j) e ≤
        (Tensor.ofFn s fun i =>
          f.apply (ta.entry (broadcastIndex ta.shape i))
            (tb.entry (broadcastIndex tb.shape i))).get j ∧
      (Tensor.ofFn s fun i =>
          f.apply (ta.entry (broadcastIndex ta.shape i))
            (tb.entry (broadcastIndex tb.shape i))).get j ≤
        dv (binHi f a.exact b.exact
          (mget a.lo (ravel a.shape (broadcastIndex a.shape (unravel s j))))
          (mget a.hi (ravel a.shape (broadcastIndex a.shape (unravel s j))))
          (mget b.lo (ravel b.shape (broadcastIndex b.shape (unravel s j))))
          (mget b.hi (ravel b.shape (broadcastIndex b.shape (unravel s j))))) e := by
    intro j hj
    rw [mget_dbinLo _ _ _ _ hj, Tensor.ofFn_get _ _ hj, ha.1, hb.1]
    have h1 := ha.entry (broadcastIndex a.shape (unravel s j))
    have h2 := hb.entry (broadcastIndex b.shape (unravel s j))
    exact bin_bounds f he h1.1 h1.2 h2.1 h2.2 (fun hx => hea hx _) (fun hx => heb hx _)
  have hlo_size : (dbinLo f a b s).size = shapeSize s := by simp [dbinLo]
  refine DT.Encl.mk rfl (Tensor.ofFn_data_size _ _) hlo_size ?_ ?_ ?_
  · change (dbinHi f a b s).size = shapeSize s
    unfold dbinHi
    split_ifs
    · exact hlo_size
    · simp
  · intro hx
    have hx' : (a.exact && b.exact) = true := hx
    change dbinLo f a b s = dbinHi f a b s
    unfold dbinHi
    simp only [hx', ↓reduceIte]
  · intro j hj
    have hj : j < shapeSize s := hj
    obtain ⟨k1, k2⟩ := key j hj
    refine ⟨k1, ?_⟩
    change _ ≤ dv (mget (dbinHi f a b s) j) e
    cases hx : (a.exact && b.exact)
    · rw [mget_dbinHi _ _ _ _ hj hx]
      exact k2
    · simp only [Bool.and_eq_true] at hx
      have : dbinHi f a b s = dbinLo f a b s := by
        unfold dbinHi
        simp only [hx.1, hx.2, Bool.and_self, ↓reduceIte]
      rw [this, mget_dbinLo _ _ _ _ hj]
      rw [hea hx.1, heb hx.2, hx.1, hx.2] at k2 ⊢
      rw [← binHi_eq_binLo]
      exact k2

@[simp] theorem DT.shift_shape (v : DT) (k : ℕ) : (v.shift k).shape = v.shape := by
  unfold DT.shift
  split_ifs <;> rfl

theorem DT.shift_e (v : DT) (k : ℕ) : (v.shift k).e = v.e - k := by
  by_cases hk : k = 0
  · simp [DT.shift, hk]
  · simp [DT.shift, hk]

theorem DT.Encl.wf {v : DT} {t : Tensor ℝ} (h : v.Encl t) : t.wellFormed = true := by
  simp [Tensor.wellFormed, h.1, h.2.1]

theorem DT.Encl.ok {v : DT} {t : Tensor ℝ} (h : v.Encl t) : v.ok = true := by
  simp [DT.ok, h.2.2.1, h.2.2.2.1]

/-- **Entrywise operations** keep enclosures. -/
theorem dbinary_sim {f : BinOp} {a b c : DT} {ta tb : Tensor ℝ} (ha : a.Encl ta) (hb : b.Encl tb)
    (h : dbinary f a b = some c) : ∃ tc, broadcastOp f.apply ta tb = some tc ∧ c.Encl tc := by
  unfold dbinary at h
  simp only [ha.ok, hb.ok, Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨s, hs, hc⟩ := Option.map_eq_some_iff.mp h
  subst hc
  refine ⟨Tensor.ofFn s fun i =>
      f.apply (ta.entry (broadcastIndex ta.shape i)) (tb.entry (broadcastIndex tb.shape i)), ?_, ?_⟩
  · unfold broadcastOp
    simp only [ha.wf, hb.wf, Bool.and_self, ↓reduceIte, ha.1, hb.1, hs]
    rfl
  · cases f with
    | mul =>
      exact dbinaryAt_encl ha hb (Or.inl ⟨rfl, rfl⟩)
    | add =>
      have h1 := DT.shift_encl ha (a.e - min a.e b.e).toNat
      have h2 := DT.shift_encl hb (b.e - min a.e b.e).toNat
      have := dbinaryAt_encl (f := .add) (s := s) (e := min a.e b.e) h1 h2
        (Or.inr ⟨by simp, by rw [DT.shift_e]; omega, by rw [DT.shift_e]; omega⟩)
      simpa only [ha.1, hb.1, DT.shift_shape] using this
    | sub =>
      have h1 := DT.shift_encl ha (a.e - min a.e b.e).toNat
      have h2 := DT.shift_encl hb (b.e - min a.e b.e).toNat
      have := dbinaryAt_encl (f := .sub) (s := s) (e := min a.e b.e) h1 h2
        (Or.inr ⟨by simp, by rw [DT.shift_e]; omega, by rw [DT.shift_e]; omega⟩)
      simpa only [ha.1, hb.1, DT.shift_shape] using this

/-! ## Negation, sums, exp -/

theorem Tensor.get_map_zero {α β : Type} [Zero α] [Zero β] (f : α → β) (hf : f 0 = 0)
    (t : Tensor α) (j : ℕ) : (t.map f).get j = f (t.get j) := by
  simp only [Tensor.map, Tensor.get, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases t.data[j]? <;> simp [hf]

theorem mget_map_neg (a : Array ℤ) (j : ℕ) : mget (a.map (- ·)) j = - mget a j := by
  simp only [mget, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases a[j]? <;> simp

theorem dneg_encl {a : DT} {t : Tensor ℝ} (h : a.Encl t) : (dneg a).Encl (t.map Neg.neg) := by
  obtain ⟨hs, ht, hlo, hhi, hex, hj⟩ := h
  have e1 : dneg a = ⟨a.shape, a.hi.map (- ·),
      if a.exact then a.hi.map (- ·) else a.lo.map (- ·), a.e, a.exact⟩ := rfl
  rw [e1]
  refine DT.Encl.mk (by simp [Tensor.map, hs]) (by simp [Tensor.map, ht]) (by simp [hhi])
    (by split_ifs <;> simp [hlo, hhi]) (by intro hx; simp only at hx; simp [hx]) ?_
  intro j _
  rw [Tensor.get_map_zero _ (by simp)]
  simp only
  have := hj j
  split_ifs with hx
  · have hlh := hex hx
    rw [hlh] at this
    rw [mget_map_neg, dv_neg]
    constructor <;> linarith [this.1, this.2]
  · rw [mget_map_neg, mget_map_neg, dv_neg, dv_neg]
    constructor <;> linarith [this.1, this.2]

theorem normDim_lt {dim : ℤ} {r d : ℕ} (h : normDim dim r = some d) : d < r := by
  unfold normDim at h
  split_ifs at h <;> simp only [Option.some.injEq] at h <;> omega

/-- The entries of a sum over dimension `d`. -/
def sumData {α : Type} [Zero α] [Add α] (t : Tensor α) (d : ℕ) : Array α :=
  (Array.range (shapeSize (t.shape.take d) * shapeSize (t.shape.drop (d + 1)))).map fun j =>
    ((List.range (t.shape.getD d 0)).map fun k =>
      t.get ((j / shapeSize (t.shape.drop (d + 1)) * t.shape.getD d 0 + k) *
        shapeSize (t.shape.drop (d + 1)) + j % shapeSize (t.shape.drop (d + 1)))).sum

theorem sumOp_eq {α : Type} [Zero α] [Add α] {dim : ℤ} {t : Tensor α} {d : ℕ}
    (hd : normDim dim t.shape.length = some d)
    (hsize : t.data.size = shapeSize (t.shape.take d) * t.shape.getD d 0 *
      shapeSize (t.shape.drop (d + 1))) :
    sumOp dim t = some ⟨t.shape.eraseIdx d, sumData t d⟩ := by
  unfold sumOp
  rw [hd]
  dsimp only
  simp only [hsize, beq_self_eq_true, ↓reduceIte]
  rfl

theorem sumOp_spec {α : Type} [Zero α] [Add α] {dim : ℤ} {t r : Tensor α}
    (h : sumOp dim t = some r) : ∃ d, normDim dim t.shape.length = some d ∧
      t.data.size = shapeSize (t.shape.take d) * t.shape.getD d 0 *
        shapeSize (t.shape.drop (d + 1)) ∧ r = ⟨t.shape.eraseIdx d, sumData t d⟩ := by
  unfold sumOp at h
  split at h
  · cases h
  · rename_i d hd
    dsimp only at h
    split_ifs at h with hsize
    simp only [Option.some.injEq] at h
    exact ⟨d, hd, by simpa using hsize, by rw [← h]; rfl⟩

theorem shapeSize_append (a b : List ℕ) : shapeSize (a ++ b) = shapeSize a * shapeSize b := by
  induction a with
  | nil => simp [shapeSize]
  | cons x a ih =>
    simp only [List.cons_append, shapeSize, List.foldr_cons] at ih ⊢
    rw [ih]
    ring

theorem shapeSize_eraseIdx_mul (s : List ℕ) (d : ℕ) :
    shapeSize (s.take d) * shapeSize (s.drop (d + 1)) = shapeSize (s.eraseIdx d) := by
  rw [List.eraseIdx_eq_take_drop_succ, shapeSize_append]

theorem sumData_size {α : Type} [Zero α] [Add α] (t : Tensor α) (d : ℕ) :
    (sumData t d).size = shapeSize (t.shape.eraseIdx d) := by
  simp [sumData, shapeSize_eraseIdx_mul]

theorem dsum_sim {dim : ℤ} {a c : DT} {t : Tensor ℝ} (ha : a.Encl t) (h : dsum dim a = some c) :
    ∃ r, sumOp dim t = some r ∧ c.Encl r := by
  unfold dsum at h
  simp only [ha.ok, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  cases hl : sumOp dim (⟨a.shape, a.lo⟩ : Tensor ℤ) with
  | none => simp [hl] at h
  | some lo =>
  simp only [hl, Option.some.injEq] at h
  subst h
  obtain ⟨d, hd, hsize, rfl⟩ := sumOp_spec hl
  simp only at hd hsize
  have hrt := sumOp_eq (t := t) (by rw [ha.1]; exact hd) (by rw [ha.1, ha.2.1, ← hsize, ha.2.2.1])
  refine ⟨_, hrt, ?_⟩
  -- the upper ends
  have hhi : (if a.exact then (⟨a.shape.eraseIdx d, sumData ⟨a.shape, a.lo⟩ d⟩ : Tensor ℤ)
      else (sumOp dim (⟨a.shape, a.hi⟩ : Tensor ℤ)).getD
        ⟨a.shape.eraseIdx d, sumData ⟨a.shape, a.lo⟩ d⟩) =
      ⟨a.shape.eraseIdx d, sumData ⟨a.shape, a.hi⟩ d⟩ := by
    split_ifs with hx
    · rw [ha.2.2.2.2.1 hx]
    · rw [sumOp_eq (t := ⟨a.shape, a.hi⟩) hd (by simp only; rw [ha.2.2.2.1, ← ha.2.2.1, hsize])]
      rfl
  simp only at hhi ⊢
  rw [hhi]
  have hsz := sumData_size (⟨a.shape, a.lo⟩ : Tensor ℤ) d
  simp only at hsz
  refine DT.Encl.mk (by simp [ha.1]) (by rw [sumData_size, ha.1]) hsz
    (by rw [sumData_size]) (by intro hx; simp only at hx ⊢; rw [ha.2.2.2.2.1 hx]) ?_
  intro j hj
  simp only at hj ⊢
  rw [← shapeSize_eraseIdx_mul] at hj
  have hj' : j < shapeSize (t.shape.take d) * shapeSize (t.shape.drop (d + 1)) := by
    rw [ha.1]
    exact hj
  unfold sumData
  rw [mget_map_range _ _ hj, mget_map_range _ _ hj, Tensor.get_mk_map_range _ _ _ hj']
  simp only [ha.1]
  rw [dv_list_sum, dv_list_sum, List.map_map, List.map_map]
  constructor
  · apply List.sum_le_sum
    intro k _
    exact (ha.2.2.2.2.2 _).1
  · apply List.sum_le_sum
    intro k _
    exact (ha.2.2.2.2.2 _).2

/-- The value `X * 2^e` as `expBoundsParts` sees it. -/
theorem signed_parts (X : ℤ) (e : ℤ) :
    (if decide (X < 0) = true then (-1 : ℝ) else 1) * (X.natAbs * (2 : ℝ) ^ e) = dv X e := by
  unfold dv
  by_cases hX : X < 0
  · simp only [hX, decide_true, ↓reduceIte]
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg (by exact_mod_cast hX)]
    ring
  · simp only [hX, decide_false, Bool.false_eq_true, ↓reduceIte, one_mul]
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg (by exact_mod_cast not_lt.mp hX)]

theorem dv_expPrecision (L : ℤ) :
    dv L (-(expPrecision : ℤ)) = (L : ℝ) / 2 ^ expPrecision := by
  unfold dv
  rw [zpow_neg, zpow_natCast, div_eq_mul_inv]

/-- The bounds `expEnd` gives are right. -/
theorem expEnd_lower {X e L : ℤ} (h : expEnd X e false = some L) :
    dv L (-(expPrecision : ℤ)) ≤ Real.exp (dv X e) := by
  unfold expEnd at h
  obtain ⟨⟨L', H'⟩, hb, hL⟩ := Option.map_eq_some_iff.mp h
  simp only [Bool.false_eq_true, ↓reduceIte] at hL
  subst hL
  have := (expBoundsParts_spec hb).1
  rw [signed_parts] at this
  rw [dv_expPrecision, div_le_iff₀ (by positivity)]
  exact this

theorem expEnd_upper {X e H : ℤ} (h : expEnd X e true = some H) :
    Real.exp (dv X e) ≤ dv H (-(expPrecision : ℤ)) := by
  unfold expEnd at h
  obtain ⟨⟨L', H'⟩, hb, hH⟩ := Option.map_eq_some_iff.mp h
  simp only [↓reduceIte] at hH
  subst hH
  have := (expBoundsParts_spec hb).2
  rw [signed_parts] at this
  rw [dv_expPrecision, le_div_iff₀ (by positivity)]
  exact this

theorem Tensor.get_map_lt {α β : Type} [Zero α] [Zero β] (f : α → β) (t : Tensor α) {j : ℕ}
    (hj : j < t.data.size) : (t.map f).get j = f (t.get j) := by
  simp [Tensor.map, Tensor.get, Array.getD_eq_getD_getElem?, hj]

theorem mget_toArray (l : List ℤ) {j : ℕ} (hj : j < l.length) : mget l.toArray j = l[j] := by
  simp [mget, Array.getD_eq_getD_getElem?, hj]

theorem dexp_sim {a c : DT} {t : Tensor ℝ} (ha : a.Encl t) (h : dexp a = some c) :
    c.Encl (t.map Real.exp) := by
  unfold dexp at h
  simp only [ha.ok, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  cases hl : a.lo.toList.mapM (expEnd · a.e false) with
  | none => simp [hl] at h
  | some lo =>
  cases hh : a.hi.toList.mapM (expEnd · a.e true) with
  | none => simp [hl, hh] at h
  | some hi =>
  simp only [hl, hh, Option.some.injEq] at h
  subst h
  obtain ⟨hllen, hlk⟩ := mapM_option_spec hl
  obtain ⟨hhlen, hhk⟩ := mapM_option_spec hh
  simp only [Array.length_toList] at hllen hhlen
  refine DT.Encl.mk (by simp [Tensor.map, ha.1]) (by simp [Tensor.map, ha.2.1])
    (by simp [hllen, ha.2.2.1]) (by simp [hhlen, ha.2.2.2.1]) (by simp) ?_
  intro j hj
  have hjt : j < t.data.size := by rw [ha.2.1]; exact hj
  have hjl : j < lo.length := by rw [hllen, ha.2.2.1]; exact hj
  have hjh : j < hi.length := by rw [hhlen, ha.2.2.2.1]; exact hj
  rw [Tensor.get_map_lt _ _ hjt, mget_toArray _ hjl, mget_toArray _ hjh]
  have h1 := hlk j (by simpa using hjl.trans_eq hllen) hjl
  have h2 := hhk j (by simpa using hjh.trans_eq hhlen) hjh
  simp only [Array.getElem_toList] at h1 h2
  have hb := ha.2.2.2.2.2 j
  have hlo : mget a.lo j = a.lo[j]'(by rw [ha.2.2.1]; exact hj) := by
    simp [mget, Array.getD_eq_getD_getElem?, show j < a.lo.size by rw [ha.2.2.1]; exact hj]
  have hhi : mget a.hi j = a.hi[j]'(by rw [ha.2.2.2.1]; exact hj) := by
    simp [mget, Array.getD_eq_getD_getElem?, show j < a.hi.size by rw [ha.2.2.2.1]; exact hj]
  rw [hlo, hhi] at hb
  constructor
  · exact (expEnd_lower h1).trans (Real.exp_le_exp.mpr hb.1)
  · exact (Real.exp_le_exp.mpr hb.2).trans (expEnd_upper h2)

/-! ## Operations that move entries

Indexing, transposing, `unsqueeze` and `expand` only move entries: each
entry of the result is an entry of the argument (or 0), at a position that
depends on the shape alone. So they commute with entrywise maps that keep
0 (`Mover.natural`). Applied to a tensor of triples (lower end, upper end,
true value), this moves the three together and keeps the enclosure. -/

/-- An operation that only moves entries. -/
structure Mover (F : ∀ {α : Type} [Zero α], Tensor α → Option (Tensor α)) : Prop where
  natural : ∀ {α β : Type} [Zero α] [Zero β] (g : α → β), g 0 = 0 →
    ∀ t : Tensor α, F (t.map g) = (F t).map (Tensor.map g)
  support : ∀ {α : Type} [Zero α] (t r : Tensor α), F t = some r → ∀ j, ∃ k, r.get j = t.get k
  wf : ∀ {α : Type} [Zero α] (t r : Tensor α), t.wellFormed = true → F t = some r →
    r.wellFormed = true

theorem Tensor.map_wellFormed {α β : Type} (g : α → β) (t : Tensor α) :
    (t.map g).wellFormed = t.wellFormed := by
  simp [Tensor.map, Tensor.wellFormed]

theorem Tensor.entry_map {α β : Type} [Zero α] [Zero β] (g : α → β) (hg : g 0 = 0)
    (t : Tensor α) (i : List ℕ) : (t.map g).entry i = g (t.entry i) := by
  simp only [Tensor.entry_eq, Tensor.map_shape']
  exact Tensor.get_map_zero g hg t _

theorem Tensor.ofFn_map {α β : Type} (g : α → β) (S : List ℕ) (F : List ℕ → α) :
    (Tensor.ofFn S F).map g = Tensor.ofFn S (fun i => g (F i)) := by
  simp [Tensor.ofFn, Tensor.map, Array.map_map, Function.comp_def]

theorem Tensor.ofFn_wellFormed {α : Type} (S : List ℕ) (F : List ℕ → α) :
    (Tensor.ofFn S F).wellFormed = true := by
  simp [Tensor.wellFormed, Tensor.ofFn_data_size]

/-- An entry of a tensor built from entries of `t` is an entry of `t`. -/
theorem ofFn_support {α : Type} [Zero α] (t : Tensor α) (S : List ℕ) (σ : List ℕ → List ℕ)
    (j : ℕ) : ∃ k, (Tensor.ofFn S fun i => t.entry (σ i)).get j = t.get k := by
  by_cases hj : j < shapeSize S
  · exact ⟨_, by rw [Tensor.ofFn_get _ _ hj, Tensor.entry_eq]⟩
  · refine ⟨t.data.size, ?_⟩
    rw [Tensor.get_of_le (by rw [Tensor.ofFn_data_size]; omega), Tensor.get_of_le (le_refl _)]

theorem indexOp_mover (items : List IndexItem) : Mover (fun t => indexOp t items) where
  natural g hg t := by
    unfold indexOp
    simp only [Tensor.map_shape', Tensor.map_wellFormed]
    split_ifs with h1 h2 h2 <;> first
      | rfl
      | (simp only [Option.map_some, Tensor.ofFn_map, Tensor.entry_map g hg]; done)
      | (exfalso; exact h2 h1)
      | (exfalso; exact h1 h2)
  support t r h j := by
    unfold indexOp at h
    split_ifs at h
    simp only [Option.some.injEq] at h
    subst h
    exact ofFn_support t _ _ j
  wf t r _ h := by
    unfold indexOp at h
    split_ifs at h
    simp only [Option.some.injEq] at h
    subst h
    exact Tensor.ofFn_wellFormed _ _

theorem transposeOp_mover : Mover (fun t => transposeOp t) where
  natural g hg t := by
    unfold transposeOp
    simp only [Tensor.map_shape']
    split
    · simp only [Tensor.map_wellFormed]
      split_ifs <;> first
        | rfl
        | simp only [Option.map_some, Tensor.ofFn_map, Tensor.entry_map g hg]
    · rfl
    · rfl
    · rfl
  support t r h j := by
    unfold transposeOp at h
    split at h
    · split_ifs at h
      simp only [Option.some.injEq] at h
      subst h
      exact ofFn_support t _ _ j
    · simp only [Option.some.injEq] at h
      subst h
      exact ⟨j, rfl⟩
    · simp only [Option.some.injEq] at h
      subst h
      exact ⟨j, rfl⟩
    · cases h
  wf t r hw h := by
    unfold transposeOp at h
    split at h
    · split_ifs at h
      simp only [Option.some.injEq] at h
      subst h
      exact Tensor.ofFn_wellFormed _ _
    · simp only [Option.some.injEq] at h
      subst h
      exact hw
    · simp only [Option.some.injEq] at h
      subst h
      exact hw
    · cases h

theorem unsqueezeOp_mover (dim : ℤ) : Mover (fun t => unsqueezeOp t dim) where
  natural g hg t := by
    unfold unsqueezeOp
    simp only [Tensor.map_shape']
    cases normDim dim (t.shape.length + 1) <;> rfl
  support t r h j := by
    unfold unsqueezeOp at h
    obtain ⟨d, -, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨j, rfl⟩
  wf t r hw h := by
    unfold unsqueezeOp at h
    obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [Tensor.wellFormed, beq_iff_eq] at hw ⊢
    rw [hw]
    have hd' := normDim_lt hd
    have : ∀ (s : List ℕ) (d : ℕ), d ≤ s.length →
        shapeSize (s.take d ++ [1] ++ s.drop d) = shapeSize s := by
      intro s d _
      rw [shapeSize_append, shapeSize_append]
      have h1 : shapeSize [1] = 1 := by simp [shapeSize]
      rw [h1, mul_one, ← shapeSize_append, List.take_append_drop]
    exact (this t.shape d (by omega)).symm

theorem expandOp_mover (shape : List ℤ) : Mover (fun t => expandOp t shape) where
  natural g hg t := by
    unfold expandOp
    dsimp only [Tensor.map_shape']
    simp only [Tensor.map_wellFormed]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd h1 h2
    · exact absurd h2 h1
    · cases expandShape t.shape shape with
      | none => rfl
      | some full =>
        simp only
        by_cases h3 : (List.zipWith (fun d f => d == f || d == 1) t.shape
            (List.drop (shape.length - t.shape.length) full)).all id = true
        · simp only [h3, ↓reduceIte, Option.map_some, Tensor.ofFn_map, Tensor.entry_map g hg]
        · simp only [h3, Bool.false_eq_true, ↓reduceIte, Option.map_none]
  support t r h j := by
    unfold expandOp at h
    split_ifs at h
    split at h
    · cases h
    · split_ifs at h
      simp only [Option.some.injEq] at h
      subst h
      exact ofFn_support t _ _ j
  wf t r _ h := by
    unfold expandOp at h
    split_ifs at h
    split at h
    · cases h
    · split_ifs at h
      simp only [Option.some.injEq] at h
      subst h
      exact Tensor.ofFn_wellFormed _ _

/-- The tensor of triples (lower end, upper end, true value). -/
def tripleT (a : DT) (t : Tensor ℝ) : Tensor (ℤ × ℤ × ℝ) :=
  ⟨a.shape, (Array.range (shapeSize a.shape)).map fun j => (mget a.lo j, mget a.hi j, t.get j)⟩

theorem Tensor.ext' {α : Type} {t u : Tensor α} (hs : t.shape = u.shape)
    (hd : t.data = u.data) : t = u := by
  cases t
  cases u
  simp_all

theorem array_ext_getD {α : Type} [Zero α] {a b : Array α} (hs : a.size = b.size)
    (h : ∀ j < a.size, a.getD j 0 = b.getD j 0) : a = b := by
  apply Array.ext hs
  intro j h1 h2
  have := h j h1
  simpa [Array.getD_eq_getD_getElem?, h1, h2] using this

theorem tripleT_map_lo {a : DT} {t : Tensor ℝ} (ha : a.Encl t) :
    (tripleT a t).map Prod.fst = ⟨a.shape, a.lo⟩ := by
  refine Tensor.ext' (by rfl) ?_
  apply array_ext_getD (by simp [tripleT, Tensor.map, ha.2.2.1])
  intro j hj
  simp only [tripleT, Tensor.map, Array.size_map, Array.size_range] at hj
  simp [tripleT, Tensor.map, Array.getD_eq_getD_getElem?, hj, mget]

theorem tripleT_map_hi {a : DT} {t : Tensor ℝ} (ha : a.Encl t) :
    (tripleT a t).map (fun z => z.2.1) = ⟨a.shape, a.hi⟩ := by
  refine Tensor.ext' (by rfl) ?_
  apply array_ext_getD (by simp [tripleT, Tensor.map, ha.2.2.2.1])
  intro j hj
  simp only [tripleT, Tensor.map, Array.size_map, Array.size_range] at hj
  simp [tripleT, Tensor.map, Array.getD_eq_getD_getElem?, hj, mget]

theorem tripleT_map_val {a : DT} {t : Tensor ℝ} (ha : a.Encl t) :
    (tripleT a t).map (fun z => z.2.2) = t := by
  apply Tensor.ext' (by simp [tripleT, ha.1])
  apply array_ext_getD (by simp [tripleT, Tensor.map, ha.2.1])
  intro j hj
  simp only [tripleT, Tensor.map, Array.size_map, Array.size_range] at hj
  simp [tripleT, Tensor.map, Array.getD_eq_getD_getElem?, hj, Tensor.get]

/-- Every entry of the tensor of triples is a valid triple. -/
theorem tripleT_get {a : DT} {t : Tensor ℝ} (ha : a.Encl t) (k : ℕ) :
    dv ((tripleT a t).get k).1 a.e ≤ ((tripleT a t).get k).2.2 ∧
      ((tripleT a t).get k).2.2 ≤ dv ((tripleT a t).get k).2.1 a.e ∧
      (a.exact = true → ((tripleT a t).get k).1 = ((tripleT a t).get k).2.1) := by
  by_cases hk : k < shapeSize a.shape
  · have : (tripleT a t).get k = (mget a.lo k, mget a.hi k, t.get k) := by
      simp [tripleT, Tensor.get, Array.getD_eq_getD_getElem?, hk]
    rw [this]
    exact ⟨(ha.2.2.2.2.2 k).1, (ha.2.2.2.2.2 k).2, fun hx => ha.lo_eq_hi hx k⟩
  · have : (tripleT a t).get k = 0 := Tensor.get_of_le (by simp [tripleT]; omega)
    rw [this]
    simp

theorem dmove_sim {F : ∀ {α : Type} [Zero α], Tensor α → Option (Tensor α)} (hF : Mover F)
    {a c : DT} {t : Tensor ℝ} (ha : a.Encl t) (h : dmove (fun x => F x) a = some c) :
    ∃ r, F t = some r ∧ c.Encl r := by
  unfold dmove at h
  simp only [ha.ok, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  cases hlo : F (⟨a.shape, a.lo⟩ : Tensor ℤ) with
  | none => simp [hlo] at h
  | some lo' =>
  simp only [hlo] at h
  -- move the triples
  have hz := hF.natural Prod.fst rfl (tripleT a t)
  rw [tripleT_map_lo ha, hlo] at hz
  cases hzt : F (tripleT a t) with
  | none => rw [hzt] at hz; cases hz
  | some rz =>
  rw [hzt] at hz
  simp only [Option.map_some, Option.some.injEq] at hz
  have hr := hF.natural (fun z => z.2.2) rfl (tripleT a t)
  rw [tripleT_map_val ha, hzt] at hr
  have hh := hF.natural (fun z => z.2.1) rfl (tripleT a t)
  rw [tripleT_map_hi ha, hzt] at hh
  refine ⟨_, hr, ?_⟩
  have hwf : (tripleT a t).wellFormed = true := by simp [tripleT, Tensor.wellFormed]
  have hrz := hF.wf _ _ hwf hzt
  simp only [Tensor.wellFormed, beq_iff_eq] at hrz
  have hsupp := hF.support _ _ hzt
  -- the three components of each moved entry
  have hcomp : ∀ j, dv (rz.map Prod.fst |>.get j) a.e ≤ (rz.map fun z => z.2.2).get j ∧
      (rz.map fun z => z.2.2).get j ≤ dv ((rz.map fun z => z.2.1).get j) a.e ∧
      (a.exact = true → (rz.map Prod.fst).get j = (rz.map fun z => z.2.1).get j) := by
    intro j
    obtain ⟨k, hk⟩ := hsupp j
    rw [Tensor.get_map_zero _ rfl, Tensor.get_map_zero _ rfl, Tensor.get_map_zero _ rfl, hk]
    exact tripleT_get ha k
  have hsz : rz.data.size = shapeSize rz.shape := hrz
  split_ifs at h with hx
  · simp only [Option.some.injEq] at h
    subst h
    subst hz
    refine DT.Encl.mk rfl (by simp [Tensor.map, hsz]) (by simp [Tensor.map, hsz])
      (by simp [Tensor.map, hsz]) (fun _ => rfl) ?_
    intro j _
    obtain ⟨h1, h2, h3⟩ := hcomp j
    rw [← h3 hx] at h2
    exact ⟨h1, h2⟩
  · cases hhi : F (⟨a.shape, a.hi⟩ : Tensor ℤ) with
    | none => simp [hhi] at h
    | some hi' =>
    simp only [hhi, Option.some.injEq] at h
    subst h
    rw [hhi] at hh
    simp only [Option.map_some, Option.some.injEq] at hh
    subst hz hh
    refine DT.Encl.mk rfl (by simp [Tensor.map, hsz]) (by simp [Tensor.map, hsz])
      (by simp [Tensor.map, hsz]) (by simp) ?_
    intro j _
    obtain ⟨h1, h2, -⟩ := hcomp j
    exact ⟨h1, h2⟩

/-! ## Joining tensors -/

/-- An operation on a list of tensors that only moves entries. -/
structure ListMover (F : ∀ {α : Type} [Zero α], List (Tensor α) → Option (Tensor α)) : Prop where
  natural : ∀ {α β : Type} [Zero α] [Zero β] (g : α → β), g 0 = 0 →
    ∀ ts : List (Tensor α), F (ts.map (Tensor.map g)) = (F ts).map (Tensor.map g)
  support : ∀ {α : Type} [Zero α] (ts : List (Tensor α)) (r : Tensor α), F ts = some r →
    ∀ j, r.get j = 0 ∨ ∃ t ∈ ts, ∃ k, r.get j = t.get k
  wf : ∀ {α : Type} [Zero α] (ts : List (Tensor α)) (r : Tensor α), F ts = some r →
    r.wellFormed = true

theorem empty_entry {α : Type} [Zero α] (i : List ℕ) : (⟨[], #[]⟩ : Tensor α).entry i = 0 := by
  simp [Tensor.entry_eq, Tensor.get]

theorem list_getD_lt {γ : Type} {l : List γ} {p : ℕ} {d : γ} (hp : p < l.length) :
    l.getD p d = l[p] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp, Option.getD_some]

theorem list_getD_ge {γ : Type} {l : List γ} {p : ℕ} {d : γ} (hp : l.length ≤ p) :
    l.getD p d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hp, Option.getD_none]

theorem getD_map_entry {α β : Type} [Zero α] [Zero β] (g : α → β) (hg : g 0 = 0)
    (ts : List (Tensor α)) (p : ℕ) (i : List ℕ) :
    ((ts.map (Tensor.map g)).getD p ⟨[], #[]⟩).entry i = g ((ts.getD p ⟨[], #[]⟩).entry i) := by
  by_cases hp : p < ts.length
  · rw [list_getD_lt (by simpa using hp), list_getD_lt hp, List.getElem_map, Tensor.entry_map g hg]
  · rw [list_getD_ge (by simp; omega), list_getD_ge (by omega), empty_entry, empty_entry, hg]

theorem getD_entry_support {α : Type} [Zero α] (ts : List (Tensor α)) (p : ℕ) (i : List ℕ) :
    (ts.getD p ⟨[], #[]⟩).entry i = 0 ∨ ∃ t ∈ ts, ∃ k, (ts.getD p ⟨[], #[]⟩).entry i = t.get k := by
  by_cases hp : p < ts.length
  · right
    refine ⟨ts[p], List.getElem_mem hp, ravel ts[p].shape i, ?_⟩
    rw [list_getD_lt hp, Tensor.entry_eq]
  · left
    rw [list_getD_ge (by omega), empty_entry]

theorem ofFn_support' {α : Type} [Zero α] (S : List ℕ) (F : List ℕ → α) (P : α → Prop)
    (hP : P 0) (hF : ∀ i, P (F i)) (j : ℕ) : P ((Tensor.ofFn S F).get j) := by
  by_cases hj : j < shapeSize S
  · rw [Tensor.ofFn_get _ _ hj]
    exact hF _
  · rw [Tensor.get_of_le (by rw [Tensor.ofFn_data_size]; omega)]
    exact hP

theorem all_wellFormed_map {α β : Type} (g : α → β) (ts : List (Tensor α)) :
    (ts.map (Tensor.map g)).all (·.wellFormed) = ts.all (·.wellFormed) := by
  simp [List.all_map, Function.comp_def, Tensor.map_wellFormed]

theorem shapes_map {α β : Type} (g : α → β) (ts : List (Tensor α)) :
    (ts.map (Tensor.map g)).map (·.shape) = ts.map (·.shape) := by
  simp [List.map_map, Function.comp_def]

theorem catOp_mover (dim : ℤ) : ListMover (fun ts => catOp ts dim) where
  natural g hg ts := by
    unfold catOp
    rw [all_wellFormed_map, shapes_map]
    split_ifs
    · cases catShape (ts.map (·.shape)) dim with
      | none => rfl
      | some r =>
        obtain ⟨d, sizes, shape⟩ := r
        simp only [Option.map_some, Tensor.ofFn_map]
        congr 2
        funext i
        exact getD_map_entry g hg ts _ _
    · rfl
  support ts r h j := by
    unfold catOp at h
    split_ifs at h
    split at h
    · cases h
    · simp only [Option.some.injEq] at h
      subst h
      exact ofFn_support' _ _ (fun v => v = 0 ∨ ∃ t ∈ ts, ∃ k, v = t.get k) (Or.inl rfl)
        (fun i => getD_entry_support _ _ _) j
  wf ts r h := by
    unfold catOp at h
    split_ifs at h
    split at h
    · cases h
    · simp only [Option.some.injEq] at h
      subst h
      exact Tensor.ofFn_wellFormed _ _

theorem stackOp_mover (dim : ℤ) : ListMover (fun ts => stackOp ts dim) where
  natural g hg ts := by
    unfold stackOp
    rw [all_wellFormed_map, shapes_map]
    split_ifs
    · cases stackShape (ts.map (·.shape)) dim with
      | none => rfl
      | some r =>
        obtain ⟨d, shape⟩ := r
        simp only [Option.map_some, Tensor.ofFn_map]
        congr 2
        funext i
        exact getD_map_entry g hg ts _ _
    · rfl
  support ts r h j := by
    unfold stackOp at h
    split_ifs at h
    split at h
    · cases h
    · simp only [Option.some.injEq] at h
      subst h
      exact ofFn_support' _ _ (fun v => v = 0 ∨ ∃ t ∈ ts, ∃ k, v = t.get k) (Or.inl rfl)
        (fun i => getD_entry_support _ _ _) j
  wf ts r h := by
    unfold stackOp at h
    split_ifs at h
    split at h
    · cases h
    · simp only [Option.some.injEq] at h
      subst h
      exact Tensor.ofFn_wellFormed _ _

theorem foldl_min_le_int (l : List ℤ) (a : ℤ) : ∀ x ∈ a :: l, l.foldl min a ≤ x := by
  induction l generalizing a with
  | nil => intro x hx; simp at hx; simp [hx]
  | cons y l ih =>
    intro x hx
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_trans (ih (min x y) (min x y) (by simp)) (min_le_left _ _)
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact le_trans (ih (min a x) (min a x) (by simp)) (min_le_right _ _)
      · exact ih (min a y) x (List.mem_cons_of_mem _ hx)

/-- After aligning, every tensor is at the common exponent and still
    encloses its value. -/
theorem alignAll_spec {as : List DT} {ts : List (Tensor ℝ)} (hrel : List.Forall₂ DT.Encl as ts) :
    List.Forall₂ DT.Encl (alignAll as).2 ts ∧ ∀ a ∈ (alignAll as).2, a.e = (alignAll as).1 := by
  unfold alignAll
  dsimp only
  constructor
  · exact List.forall₂_map_left_iff.mpr (hrel.imp fun a t h => DT.shift_encl h _)
  · intro a ha
    obtain ⟨a1, ha1, rfl⟩ := List.mem_map.mp ha
    rw [DT.shift_e]
    have : (as.map (·.e)).foldl min ((as.headD ⟨[], #[], #[], 0, true⟩).e) ≤ a1.e := by
      cases as with
      | nil => simp at ha1
      | cons a0 rest =>
        simp only [List.headD_cons, List.map_cons, List.foldl_cons]
        apply foldl_min_le_int (rest.map (·.e)) (min a0.e a0.e)
        rcases List.mem_cons.mp ha1 with rfl | ha1
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨a1, ha1, rfl⟩)
    omega

theorem forall₂_get {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) : l₁.length = l₂.length ∧
      ∀ i (h1 : i < l₁.length) (h2 : i < l₂.length), R l₁[i] l₂[i] := by
  induction h with
  | nil => simp
  | cons hab _ ih =>
    refine ⟨by simp [ih.1], fun i h1 h2 => ?_⟩
    cases i with
    | zero => simpa using hab
    | succ i => simpa using ih.2 i (by simpa using h1) (by simpa using h2)

theorem djoin_sim {F : ∀ {α : Type} [Zero α], List (Tensor α) → Option (Tensor α)}
    (hF : ListMover F) {as : List DT} {ts : List (Tensor ℝ)} {c : DT}
    (hrel : List.Forall₂ DT.Encl as ts) (h : djoin (fun l => F l) as = some c) :
    ∃ r, F ts = some r ∧ c.Encl r := by
  unfold djoin at h
  split_ifs at h
  obtain ⟨hrel', he'⟩ := alignAll_spec hrel
  generalize alignAll as = al at h hrel' he'
  obtain ⟨e, as'⟩ := al
  simp only at h hrel' he'
  -- the tensors of triples
  obtain ⟨hlen, hget⟩ := forall₂_get hrel'
  set zs := List.zipWith tripleT as' ts with hzs
  have hzlo : zs.map (Tensor.map Prod.fst) = as'.map fun a => (⟨a.shape, a.lo⟩ : Tensor ℤ) := by
    apply List.ext_getElem (by simp [hzs, hlen])
    intro i h1 h2
    simp only [hzs, List.getElem_map, List.getElem_zipWith]
    exact tripleT_map_lo (hget i (by simpa [hzs] using h2) (by simp [hzs] at h1; omega))
  have hzhi : zs.map (Tensor.map fun z => z.2.1) =
      as'.map fun a => (⟨a.shape, a.hi⟩ : Tensor ℤ) := by
    apply List.ext_getElem (by simp [hzs, hlen])
    intro i h1 h2
    simp only [hzs, List.getElem_map, List.getElem_zipWith]
    exact tripleT_map_hi (hget i (by simpa [hzs] using h2) (by simp [hzs] at h1; omega))
  have hzval : zs.map (Tensor.map fun z => z.2.2) = ts := by
    apply List.ext_getElem (by simp [hzs, hlen])
    intro i h1 h2
    simp only [hzs, List.getElem_map, List.getElem_zipWith]
    exact tripleT_map_val (hget i (by simp [hzs] at h1; omega) h2)
  -- every entry of a tensor of triples is a valid triple
  have hzs_ok : ∀ z ∈ zs, ∀ k, dv (z.get k).1 e ≤ (z.get k).2.2 ∧
      (z.get k).2.2 ≤ dv (z.get k).2.1 e ∧
      (as'.all (·.exact) = true → (z.get k).1 = (z.get k).2.1) := by
    intro z hz k
    rw [hzs, List.mem_iff_getElem] at hz
    obtain ⟨i, hi, rfl⟩ := hz
    simp only [List.length_zipWith] at hi
    have hi1 : i < as'.length := by omega
    have hi2 : i < ts.length := by omega
    simp only [List.getElem_zipWith]
    have henc := hget i hi1 hi2
    have := tripleT_get henc k
    rw [he' _ (List.getElem_mem hi1)] at this
    refine ⟨this.1, this.2.1, fun hall => this.2.2 ?_⟩
    exact List.all_eq_true.mp hall _ (List.getElem_mem hi1)
  -- run the operation
  split at h
  · rename_i lo hi hlo hhi
    simp only [Option.some.injEq] at h
    subst h
    have h1 := hF.natural Prod.fst rfl zs
    rw [hzlo, hlo] at h1
    cases hz : F zs with
    | none => rw [hz] at h1; cases h1
    | some rz =>
    rw [hz] at h1
    simp only [Option.map_some, Option.some.injEq] at h1
    have h2 := hF.natural (fun z => z.2.1) rfl zs
    rw [hzhi, hhi, hz] at h2
    simp only [Option.map_some, Option.some.injEq] at h2
    have h3 := hF.natural (fun z => z.2.2) rfl zs
    rw [hzval, hz] at h3
    refine ⟨_, h3, ?_⟩
    subst h1 h2
    have hrz := hF.wf _ _ hz
    simp only [Tensor.wellFormed, beq_iff_eq] at hrz
    -- the entries of the result
    have hcomp : ∀ j, dv (rz.get j).1 e ≤ (rz.get j).2.2 ∧ (rz.get j).2.2 ≤ dv (rz.get j).2.1 e ∧
        (as'.all (·.exact) = true → (rz.get j).1 = (rz.get j).2.1) := by
      intro j
      rcases hF.support _ _ hz j with h0 | ⟨z, hzm, k, hk⟩
      · rw [h0]
        simp
      · rw [hk]
        exact hzs_ok z hzm k
    refine DT.Encl.mk (by simp [Tensor.map]) (by simp [Tensor.map, hrz])
      (by simp [Tensor.map, hrz]) (by simp [Tensor.map, hrz]) ?_ ?_
    · intro hx
      simp only at hx ⊢
      apply array_ext_getD (by simp)
      intro j _
      have := (hcomp j).2.2 hx
      change (rz.map Prod.fst).get j = (rz.map fun z : ℤ × ℤ × ℝ => z.2.1).get j
      rw [Tensor.get_map_zero _ rfl, Tensor.get_map_zero _ rfl, this]
    · intro j _
      have e1 : mget (rz.map Prod.fst).data j = (rz.get j).1 :=
        Tensor.get_map_zero Prod.fst rfl rz j
      have e2 : mget (rz.map fun z => z.2.1).data j = (rz.get j).2.1 :=
        Tensor.get_map_zero (fun z : ℤ × ℤ × ℝ => z.2.1) rfl rz j
      simp only
      rw [e1, e2, Tensor.get_map_zero (fun z : ℤ × ℤ × ℝ => z.2.2) rfl rz j]
      exact ⟨(hcomp j).1, (hcomp j).2.1⟩
  · cases h

/-! ## Softmax -/

/-- The bounds on one weight of a row are right: whatever the true entries
    `z k`, if `El k`, `Eh k` bound `exp (z k - C)` at `2^-120` (any shift
    `C`), the weight of entry `j0` lies between `softmaxLower` and
    `softmaxUpper` at `2^-120`. -/
theorem softmax_bounds_assemble {n : ℕ} {z : ℕ → ℝ} {C : ℝ} {El Eh : ℕ → ℤ} {j0 : ℕ}
    (hj : j0 < n) (hl : ∀ k < n, (El k : ℝ) ≤ Real.exp (z k - C) * 2 ^ expPrecision)
    (hh : ∀ k < n, Real.exp (z k - C) * 2 ^ expPrecision ≤ Eh k) :
    dv (softmaxLower (El j0) (Eh j0) ((List.range n).map Eh).sum) (-(expPrecision : ℤ)) ≤
        Real.exp (z j0) / ((List.range n).map fun k => Real.exp (z k)).sum ∧
      Real.exp (z j0) / ((List.range n).map fun k => Real.exp (z k)).sum ≤
        dv (softmaxUpper (El j0) (Eh j0) ((List.range n).map El).sum) (-(expPrecision : ℤ)) := by
  set P := expPrecision
  set e : ℕ → ℝ := fun k => Real.exp (z k - C) * 2 ^ P with he
  have hepos : ∀ k, 0 < e k := fun k => by positivity
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ((List.range n).map e).sum := ⟨_, rfl⟩
  have hlo_le : e j0 - (El j0 : ℝ) ≤ S - ((((List.range n).map El).sum : ℤ) : ℝ) := by
    have := le_sum_sub_sum (a := (List.range n).map fun k => (El k : ℝ)) (b := (List.range n).map e)
      (by simp) (fun k h1 h2 => by
        simp only [List.getElem_map, List.getElem_range]
        exact hl k (by simpa using h1)) j0 (by simpa using hj) (by simpa using hj)
    simp only [List.getElem_map, List.getElem_range] at this
    rw [hS]
    push_cast [Int.cast_list_sum, List.map_map]
    simpa [Function.comp_def] using this
  have hhi_le : S - e j0 ≤ ((((List.range n).map Eh).sum : ℤ) : ℝ) - (Eh j0 : ℝ) := by
    have := le_sum_sub_sum (a := (List.range n).map e) (b := (List.range n).map fun k => (Eh k : ℝ))
      (by simp) (fun k h1 h2 => by
        simp only [List.getElem_map, List.getElem_range]
        exact hh k (by simpa using h1)) j0 (by simpa using hj) (by simpa using hj)
    simp only [List.getElem_map, List.getElem_range] at this
    rw [hS]
    push_cast [Int.cast_list_sum, List.map_map]
    simp only [Function.comp_def]
    linarith
  have hejS : e j0 ≤ S := by
    rw [hS]
    apply List.single_le_sum
    · intro x hx
      simp only [List.mem_map, List.mem_range] at hx
      obtain ⟨k, -, rfl⟩ := hx
      exact (hepos k).le
    · simp only [List.mem_map, List.mem_range]
      exact ⟨j0, hj, rfl⟩
  have hSpos : 0 < S := lt_of_lt_of_le (hepos j0) hejS
  have hweight : Real.exp (z j0) / ((List.range n).map fun k => Real.exp (z k)).sum = e j0 / S := by
    have hmul : S = ((List.range n).map fun k => Real.exp (z k)).sum * (Real.exp (-C) * 2 ^ P) := by
      rw [hS, ← List.sum_map_mul_right]
      congr 1
      apply List.map_congr_left
      intro k _
      simp only [he, sub_eq_add_neg, Real.exp_add]
      ring
    have hej : e j0 = Real.exp (z j0) * (Real.exp (-C) * 2 ^ P) := by
      simp only [he, sub_eq_add_neg, Real.exp_add]
      ring
    rw [hej, hmul]
    have : 0 < Real.exp (-C) * 2 ^ P := by positivity
    have : 0 < ((List.range n).map fun k => Real.exp (z k)).sum := by
      have h2 : 0 < S := hSpos
      rw [hmul] at h2
      exact pos_of_mul_pos_left h2 this.le
    field_simp
  obtain ⟨hlow, hup⟩ := softmax_weight_bounds (Slo := ((((List.range n).map El).sum : ℤ) : ℝ))
    (Shi := ((((List.range n).map Eh).sum : ℤ) : ℝ)) (hl j0 hj) (hh j0 hj) (hepos j0) hejS
    (by linarith) hhi_le
  rw [hweight]
  have h2P : (0 : ℝ) < 2 ^ P := by positivity
  have hs1 : e j0 / S ≤ 1 := (div_le_one hSpos).mpr hejS
  constructor
  · unfold softmaxLower
    rw [dv_expPrecision]
    split_ifs with hden
    · have hden' : (0 : ℝ) < (El j0 : ℝ) + (((List.range n).map Eh).sum : ℤ) - Eh j0 := by
        exact_mod_cast hden
      rw [div_le_iff₀ h2P, Int.cast_max, Int.cast_zero]
      apply max_le (by positivity)
      calc ((El j0 * 2 ^ P / (El j0 + ((List.range n).map Eh).sum - Eh j0) : ℤ) : ℝ)
          ≤ ((El j0 * 2 ^ P : ℤ) : ℝ) / ((El j0 + ((List.range n).map Eh).sum - Eh j0 : ℤ) : ℝ) :=
            ediv_le_div hden
        _ = (El j0 : ℝ) / ((El j0 : ℝ) + (((List.range n).map Eh).sum : ℤ) - Eh j0) * 2 ^ P := by
          push_cast
          ring
        _ ≤ e j0 / S * 2 ^ P := mul_le_mul_of_nonneg_right (hlow hden') h2P.le
    · simp only [Int.cast_zero, zero_div]
      positivity
  · unfold softmaxUpper
    rw [dv_expPrecision]
    split_ifs with hden
    · have hden' : (0 : ℝ) < (Eh j0 : ℝ) + (((List.range n).map El).sum : ℤ) - El j0 := by
        exact_mod_cast hden
      rw [le_div_iff₀ h2P, Int.cast_min]
      apply le_min
      · push_cast
        calc e j0 / S * 2 ^ P ≤ 1 * 2 ^ P := mul_le_mul_of_nonneg_right hs1 h2P.le
          _ = 2 ^ P := one_mul _
      · calc e j0 / S * 2 ^ P ≤ (Eh j0 : ℝ) / ((Eh j0 : ℝ) + (((List.range n).map El).sum : ℤ) -
              El j0) * 2 ^ P := mul_le_mul_of_nonneg_right (hup hden') h2P.le
          _ = ((Eh j0 * 2 ^ P : ℤ) : ℝ) /
              ((Eh j0 + ((List.range n).map El).sum - El j0 : ℤ) : ℝ) := by push_cast; ring
          _ ≤ _ := div_le_ceilDiv hden
    · rw [le_div_iff₀ h2P]
      push_cast
      calc e j0 / S * 2 ^ P ≤ 1 * 2 ^ P := mul_le_mul_of_nonneg_right hs1 h2P.le
        _ = 2 ^ P := one_mul _

/-! ### Rows of a tensor -/

theorem unravel_length (s : List ℕ) (j : ℕ) : (unravel s j).length = s.length := by
  simp [unravel, strides_length]

theorem unravel_getD (s : List ℕ) (j : ℕ) {d : ℕ} (hd : d < s.length) :
    (unravel s j).getD d 0 = j / (strides s).getD d 0 % s.getD d 0 := by
  simp only [unravel, List.getD_eq_getElem?_getD]
  rw [List.getElem?_zipWith]
  rw [List.getElem?_eq_getElem (by rw [strides_length]; exact hd), List.getElem?_eq_getElem hd]
  simp

/-- `ravel` is linear in each coordinate. -/
theorem zipWith_mul_set (st i : List ℕ) (d k : ℕ) (hd : d < st.length) (hl : st.length = i.length) :
    (List.zipWith (· * ·) st (i.set d k)).sum + st.getD d 0 * i.getD d 0 =
      (List.zipWith (· * ·) st i).sum + st.getD d 0 * k := by
  induction st generalizing i d with
  | nil => simp at hd
  | cons x st ih =>
    cases i with
    | nil => simp at hl
    | cons y i =>
      cases d with
      | zero => simp; ring
      | succ d =>
        simp only [List.set_cons_succ, List.zipWith_cons_cons, List.sum_cons, List.getD_cons_succ]
        have := ih i d (by simpa using hd) (by simpa using hl)
        omega

theorem ravel_set (s i : List ℕ) (d k : ℕ) (hd : d < s.length) (hl : i.length = s.length) :
    ravel s (i.set d k) + (strides s).getD d 0 * i.getD d 0 =
      ravel s i + (strides s).getD d 0 * k :=
  zipWith_mul_set (strides s) i d k (by rw [strides_length]; exact hd) (by rw [strides_length, hl])

theorem shapeSize_split (s : List ℕ) {d : ℕ} (hd : d < s.length) :
    shapeSize s = shapeSize (s.take d) * (s.getD d 0 * (strides s).getD d 0) := by
  have h1 : (strides s).getD d 0 = shapeSize (s.drop (d + 1)) := by
    induction s generalizing d with
    | nil => simp at hd
    | cons x s ih =>
      cases d with
      | zero => simp [strides]
      | succ d => simpa [strides] using ih (by simpa using hd)
  rw [h1]
  conv_lhs => rw [← List.take_append_drop d s]
  rw [shapeSize_append]
  congr 1
  have hdrop : s.drop d = s[d] :: s.drop (d + 1) := List.drop_eq_getElem_cons hd
  rw [hdrop]
  simp only [shapeSize, List.foldr_cons, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hd,
    Option.getD_some]

theorem rowPosition_eq (sd n j k : ℕ) :
    rowPosition sd n j k = (j / sd / n * n + k) * sd + j % sd := by
  unfold rowPosition
  have h1 : j = (j / sd / n * n + j / sd % n) * sd + j % sd := by
    rw [Nat.div_add_mod' (j / sd) n]
    exact (Nat.div_add_mod' j sd).symm
  generalize hA : j / sd / n * n = A at h1 ⊢
  generalize hI : j / sd % n = I at h1 ⊢
  generalize hR : j % sd = R at h1 ⊢
  rw [h1]
  have e1 : (A + I) * sd + R - I * sd = A * sd + R := by
    rw [Nat.add_mul]
    omega
  rw [e1, Nat.add_mul]
  omega

theorem div_aux {q r sd : ℕ} (hsd : 0 < sd) (hr : r < sd) : (q * sd + r) / sd = q := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hsd, Nat.div_eq_of_lt hr, Nat.zero_add]

theorem mod_aux {q r sd : ℕ} (hr : r < sd) : (q * sd + r) % sd = r := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]

theorem rowPosition_div (sd n j k : ℕ) (hsd : 0 < sd) (hk : k < n) :
    rowPosition sd n j k / sd % n = k := by
  rw [rowPosition_eq, div_aux hsd (Nat.mod_lt _ hsd), Nat.add_comm, Nat.mul_comm,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk]

theorem rowPosition_row (sd n j k0 k : ℕ) (hsd : 0 < sd) (hk0 : k0 < n) :
    rowPosition sd n (rowPosition sd n j k0) k = rowPosition sd n j k := by
  rw [rowPosition_eq sd n (rowPosition sd n j k0), rowPosition_eq sd n j k]
  have h1 : rowPosition sd n j k0 / sd / n = j / sd / n := by
    rw [rowPosition_eq, div_aux hsd (Nat.mod_lt _ hsd), div_aux (by omega) hk0]
  have h2 : rowPosition sd n j k0 % sd = j % sd := by
    rw [rowPosition_eq, mod_aux (Nat.mod_lt _ hsd)]
  rw [h1, h2]

theorem rowPosition_self (sd n j : ℕ) : rowPosition sd n j (j / sd % n) = j := by
  unfold rowPosition
  have : (j / sd % n) * sd ≤ j := by
    calc (j / sd % n) * sd ≤ (j / sd) * sd := Nat.mul_le_mul_right _ (Nat.mod_le _ _)
      _ ≤ j := Nat.div_mul_le_self j sd
  omega

theorem rowPosition_lt (sd n j k M : ℕ) (hsd : 0 < sd) (hk : k < n)
    (hj : j < M * (n * sd)) : rowPosition sd n j k < M * (n * sd) := by
  rw [rowPosition_eq]
  have hq : j / sd / n < M := by
    rw [Nat.div_div_eq_div_mul, Nat.div_lt_iff_lt_mul (Nat.mul_pos hsd (by omega))]
    calc j < M * (n * sd) := hj
      _ = M * (sd * n) := by ring
  have hr : j % sd < sd := Nat.mod_lt _ hsd
  calc (j / sd / n * n + k) * sd + j % sd < (j / sd / n * n + k) * sd + sd := by omega
    _ = (j / sd / n * n + k + 1) * sd := by ring
    _ ≤ (j / sd / n * n + n) * sd := Nat.mul_le_mul_right _ (by omega)
    _ = (j / sd / n + 1) * (n * sd) := by ring
    _ ≤ M * (n * sd) := Nat.mul_le_mul_right _ hq

/-- The entry `i.set d k` of the row of the entry at flat position `j`. -/
theorem ravel_row (s : List ℕ) {d : ℕ} (hd : d < s.length) {j : ℕ} (hj : j < shapeSize s) (k : ℕ) :
    ravel s ((unravel s j).set d k) =
      rowPosition ((strides s).getD d 0) (s.getD d 0) j k := by
  have h1 := ravel_set s (unravel s j) d k hd (unravel_length s j)
  rw [ravel_unravel_of_lt hj, unravel_getD s j hd] at h1
  unfold rowPosition
  have : (j / (strides s).getD d 0 % s.getD d 0) * (strides s).getD d 0 ≤ j := by
    calc (j / (strides s).getD d 0 % s.getD d 0) * (strides s).getD d 0
        ≤ (j / (strides s).getD d 0) * (strides s).getD d 0 :=
          Nat.mul_le_mul_right _ (Nat.mod_le _ _)
      _ ≤ j := Nat.div_mul_le_self _ _
  rw [Nat.mul_comm ((strides s).getD d 0) (j / _ % _), Nat.mul_comm ((strides s).getD d 0) k] at h1
  omega

theorem realExp_eq (x : ℝ) : ExpDiv.exp x = Real.exp x := rfl

theorem realDiv_eq (x y : ℝ) : ExpDiv.div x y = x / y := rfl

theorem strides_pos {s : List ℕ} {d : ℕ} (hd : d < s.length) (hs : 0 < shapeSize s) :
    0 < (strides s).getD d 0 := by
  rw [shapeSize_split s hd] at hs
  rcases Nat.eq_zero_or_pos ((strides s).getD d 0) with h0 | h0
  · rw [h0] at hs
    simp at hs
  · exact h0

/-- The row of an entry has one shift. -/
theorem rowShift_row (a : DT) {sd n j k0 : ℕ} (hsd : 0 < sd) (hk0 : k0 < n) :
    rowShift a sd n (rowPosition sd n j k0) = rowShift a sd n j := by
  unfold rowShift
  simp only [rowPosition_row sd n j k0 _ hsd hk0]

theorem dsoftmax_sim {dim : ℤ} {a c : DT} {t : Tensor ℝ} (ha : a.Encl t)
    (h : dsoftmax dim a = some c) : ∃ r, softmaxOp t dim = some r ∧ c.Encl r := by
  unfold dsoftmax at h
  simp only [ha.ok, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  cases hd : normDim dim a.shape.length with
  | none => simp [hd] at h
  | some d =>
  simp only [hd] at h
  split_ifs at h with hn0
  split at h
  rotate_left
  · cases h
  rename_i El Eh hEl hEh
  simp only [Option.some.injEq] at h
  subst h
  try simp only [← List.getD_eq_getElem?_getD] at hEl hEh hn0 ⊢
  have hdl : d < a.shape.length := normDim_lt hd
  obtain ⟨hElLen, hElk⟩ := mapM_option_spec hEl
  obtain ⟨hEhLen, hEhk⟩ := mapM_option_spec hEh
  simp only [List.length_range] at hElLen hEhLen
  set n := a.shape.getD d 0 with hn
  set sd := (strides a.shape).getD d 0 with hsd
  -- the real softmax
  have hreal : softmaxOp t dim = some (Tensor.ofFn t.shape fun i =>
      ExpDiv.div (ExpDiv.exp (t.entry i))
        ((List.range (t.shape.getD d 0)).map fun k => ExpDiv.exp (t.entry (i.set d k))).sum) := by
    unfold softmaxOp
    rw [ha.1, hd]
    simp only [ha.wf, ↓reduceIte]
  refine ⟨_, hreal, ?_⟩
  refine DT.Encl.mk (by simp [ha.1]) (by rw [Tensor.ofFn_data_size, ha.1]) (by simp) (by simp)
    (by simp) ?_
  intro j hj
  have hj : j < shapeSize a.shape := hj
  have hsdpos : 0 < sd := strides_pos hdl (by omega)
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  set M := shapeSize (a.shape.take d)
  have hsplit : shapeSize a.shape = M * (n * sd) := shapeSize_split a.shape hdl
  have hrow : ∀ k < n, rowPosition sd n j k < shapeSize a.shape := by
    intro k hk
    rw [hsplit]
    exact rowPosition_lt sd n j k M hsdpos hk (by rw [← hsplit]; exact hj)
  -- the real entry, written with the row of entry j
  rw [Tensor.ofFn_get _ _ (by rw [ha.1]; exact hj), realDiv_eq, realExp_eq, ha.1]
  have hent : t.entry (unravel a.shape j) = t.get j := by
    rw [Tensor.entry_eq, ha.1, ravel_unravel_of_lt hj]
  have hents : ∀ k, t.entry ((unravel a.shape j).set d k) = t.get (rowPosition sd n j k) := by
    intro k
    rw [Tensor.entry_eq, ha.1, ravel_row a.shape hdl hj k]
  simp only [hent, hents, realExp_eq]
  set j0 := j / sd % n with hj0
  have hj0n : j0 < n := Nat.mod_lt _ hnpos
  have hself : rowPosition sd n j j0 = j := rowPosition_self sd n j
  set C : ℝ := dv (rowShift a sd n j) a.e
  -- the bounds on the shifted exponentials of the row
  have hl : ∀ k < n, ((mget El.toArray (rowPosition sd n j k) : ℤ) : ℝ) ≤
      Real.exp (t.get (rowPosition sd n j k) - C) * 2 ^ expPrecision := by
    intro k hk
    have hjk := hrow k hk
    have h1 := hElk (rowPosition sd n j k) (by simpa using hjk) (by rw [hElLen]; exact hjk)
    simp only [List.getElem_range] at h1
    rw [rowShift_row a hsdpos hk] at h1
    have h2 := expEnd_lower h1
    rw [dv_expPrecision, div_le_iff₀ (by positivity)] at h2
    rw [mget_toArray _ (by rw [hElLen]; exact hjk)]
    calc ((El[rowPosition sd n j k] : ℤ) : ℝ)
        ≤ Real.exp (dv (mget a.lo (rowPosition sd n j k) - rowShift a sd n j) a.e) *
            2 ^ expPrecision := h2
      _ ≤ Real.exp (t.get (rowPosition sd n j k) - C) * 2 ^ expPrecision := by
        gcongr
        rw [dv_sub]
        linarith [(ha.2.2.2.2.2 (rowPosition sd n j k)).1]
  have hh : ∀ k < n, Real.exp (t.get (rowPosition sd n j k) - C) * 2 ^ expPrecision ≤
      ((mget Eh.toArray (rowPosition sd n j k) : ℤ) : ℝ) := by
    intro k hk
    have hjk := hrow k hk
    have h1 := hEhk (rowPosition sd n j k) (by simpa using hjk) (by rw [hEhLen]; exact hjk)
    simp only [List.getElem_range] at h1
    rw [rowShift_row a hsdpos hk] at h1
    have h2 := expEnd_upper h1
    rw [dv_expPrecision, le_div_iff₀ (by positivity)] at h2
    rw [mget_toArray _ (by rw [hEhLen]; exact hjk)]
    calc Real.exp (t.get (rowPosition sd n j k) - C) * 2 ^ expPrecision
        ≤ Real.exp (dv (mget a.hi (rowPosition sd n j k) - rowShift a sd n j) a.e) *
            2 ^ expPrecision := by
          gcongr
          rw [dv_sub]
          linarith [(ha.2.2.2.2.2 (rowPosition sd n j k)).2]
      _ ≤ _ := h2
  have key := softmax_bounds_assemble (z := fun k => t.get (rowPosition sd n j k)) (C := C)
    (El := fun k => mget El.toArray (rowPosition sd n j k))
    (Eh := fun k => mget Eh.toArray (rowPosition sd n j k)) hj0n hl hh
  simp only [hself] at key
  rw [mget_map_range _ _ hj, mget_map_range _ _ hj]
  exact key

/-! ## Matrix products -/

theorem strides_append (s u : List ℕ) :
    strides (s ++ u) = (strides s).map (· * shapeSize u) ++ strides u := by
  induction s with
  | nil => simp [strides]
  | cons x s ih =>
    simp only [List.cons_append, strides, ih, List.map_cons, shapeSize_append]

theorem zipWith_mul_append (st1 st2 p q : List ℕ) (h : st1.length = p.length) :
    (List.zipWith (· * ·) (st1 ++ st2) (p ++ q)).sum =
      (List.zipWith (· * ·) st1 p).sum + (List.zipWith (· * ·) st2 q).sum := by
  rw [List.zipWith_append h, List.sum_append]

theorem zipWith_mul_map (st p : List ℕ) (U : ℕ) :
    (List.zipWith (· * ·) (st.map (· * U)) p).sum = (List.zipWith (· * ·) st p).sum * U := by
  induction st generalizing p with
  | nil => simp
  | cons x st ih =>
    cases p with
    | nil => simp
    | cons y p =>
      simp only [List.map_cons, List.zipWith_cons_cons, List.sum_cons, ih]
      ring

theorem ravel_append (s u p q : List ℕ) (h : p.length = s.length) :
    ravel (s ++ u) (p ++ q) = ravel s p * shapeSize u + ravel u q := by
  unfold ravel
  rw [strides_append, zipWith_mul_append _ _ _ _ (by rw [List.length_map, strides_length, h]),
    zipWith_mul_map]

theorem ravel_two (ba : List ℕ) (m k : ℕ) (p : List ℕ) (r t : ℕ) (h : p.length = ba.length) :
    ravel (ba ++ [m, k]) (p ++ [r, t]) = (ravel ba p * m + r) * k + t := by
  rw [ravel_append _ _ _ _ h]
  simp [ravel, strides, shapeSize]
  ring

theorem broadcastShape_length {s t u : List ℕ} (h : broadcastShape s t = some u) :
    u.length = max s.length t.length := by
  unfold broadcastShape at h
  obtain ⟨hlen, -⟩ := mapM_option_spec h
  rw [hlen]
  simp only [List.length_zip, List.length_append, List.length_replicate]
  omega

theorem broadcastIndex_length (s i : List ℕ) (h : s.length ≤ i.length) :
    (broadcastIndex s i).length = s.length := by
  simp only [broadcastIndex, List.length_zipWith, List.length_drop]
  omega

/-- The padded shape of a matrix product's argument: its batch dimensions,
    then the two matrix dimensions. -/
theorem take_append_last_two (sa : List ℕ) (h : 2 ≤ sa.length) :
    sa = sa.take (sa.length - 2) ++ [sa.getD (sa.length - 2) 0, sa.getD (sa.length - 1) 0] := by
  conv_lhs => rw [← List.take_append_drop (sa.length - 2) sa]
  congr 1
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp only [List.length_drop] at h1
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  · simp [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show sa.length - 2 < sa.length by omega)]
  · simp only [List.getElem_drop, List.getElem_cons_succ, List.getElem_cons_zero]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    simp only [Option.getD_some]
    congr 1
    omega

theorem padRow_length {s : List ℕ} (h : s ≠ []) : 2 ≤ (padRow s).length := by
  unfold padRow
  split_ifs with h1
  · simp [h1]
  · have : s.length ≠ 0 := by simpa using h
    omega

theorem padCol_length {t : List ℕ} (h : t ≠ []) : 2 ≤ (padCol t).length := by
  unfold padCol
  split_ifs with h1
  · simp [h1]
  · have : t.length ≠ 0 := by simpa using h
    omega

theorem shapeSize_keepDim_row (s : List ℕ) :
    shapeSize (keepDim s ((padRow s).getD ((padRow s).length - 2) 0)) =
      (padRow s).getD ((padRow s).length - 2) 0 := by
  unfold keepDim padRow
  split_ifs with h1
  · simp [shapeSize, h1]
  · simp [shapeSize]

theorem shapeSize_keepDim_col (t : List ℕ) :
    shapeSize (keepDim t ((padCol t).getD ((padCol t).length - 1) 0)) =
      (padCol t).getD ((padCol t).length - 1) 0 := by
  unfold keepDim padCol
  split_ifs with h1
  · simp [shapeSize, h1, List.getD_eq_getElem?_getD]
  · simp [shapeSize]

theorem matmulShape_spec {s t : List ℕ} {p : MatmulShape} (h : matmulShape s t = some p) :
    p.sa = p.ba ++ [p.m, p.k] ∧ p.sb = p.bb ++ [p.k, p.n] ∧
      p.ba.length ≤ p.batch.length ∧ p.bb.length ≤ p.batch.length ∧
      shapeSize p.out = shapeSize (p.batch ++ [p.m, p.n]) := by
  unfold matmulShape at h
  dsimp only at h
  split_ifs at h with h0 hk
  obtain ⟨batch, hb, rfl⟩ := Option.map_eq_some_iff.mp h
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at h0
  obtain ⟨hs0, ht0⟩ := h0
  simp only [ne_eq, not_not] at hk
  have hlen := broadcastShape_length hb
  dsimp only
  refine ⟨take_append_last_two _ (padRow_length hs0), ?_, by rw [hlen]; omega,
    by rw [hlen]; omega, ?_⟩
  · rw [← hk]
    exact take_append_last_two _ (padCol_length ht0)
  · rw [shapeSize_append, shapeSize_append, shapeSize_append, shapeSize_keepDim_row,
      shapeSize_keepDim_col]
    simp [shapeSize]
    ring

theorem mget_matmulEnd (lower : Bool) (p : MatmulShape) (a b : DT) {j : ℕ}
    (hj : j < shapeSize (p.batch ++ [p.m, p.n])) :
    mget (matmulEnd lower p a b) j =
      ((List.range p.k).map fun t =>
        (if lower then prodLo else prodHi) a.exact b.exact
          (mget a.lo ((ravel p.ba (broadcastIndex p.ba ((unravel (p.batch ++ [p.m, p.n]) j).take
            p.batch.length)) * p.m +
              (unravel (p.batch ++ [p.m, p.n]) j).getD p.batch.length 0) * p.k + t))
          (mget a.hi ((ravel p.ba (broadcastIndex p.ba ((unravel (p.batch ++ [p.m, p.n]) j).take
            p.batch.length)) * p.m +
              (unravel (p.batch ++ [p.m, p.n]) j).getD p.batch.length 0) * p.k + t))
          (mget b.lo (ravel p.bb (broadcastIndex p.bb ((unravel (p.batch ++ [p.m, p.n]) j).take
            p.batch.length)) * p.k * p.n +
              (unravel (p.batch ++ [p.m, p.n]) j).getD (p.batch.length + 1) 0 + t * p.n))
          (mget b.hi (ravel p.bb (broadcastIndex p.bb ((unravel (p.batch ++ [p.m, p.n]) j).take
            p.batch.length)) * p.k * p.n +
              (unravel (p.batch ++ [p.m, p.n]) j).getD (p.batch.length + 1) 0 + t * p.n))).sum := by
  unfold matmulEnd
  rw [mget_map_range _ _ hj]
  rfl

theorem dmatmul_sim {a b c : DT} {ta tb : Tensor ℝ} (ha : a.Encl ta) (hb : b.Encl tb)
    (h : dmatmul a b = some c) : ∃ r, matmulOp ta tb = some r ∧ c.Encl r := by
  unfold dmatmul at h
  simp only [ha.ok, hb.ok, Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨hsa, hsb, hba, hbb, hout⟩ := matmulShape_spec hp
  set s := p.batch ++ [p.m, p.n] with hs
  -- the real product
  have hreal : matmulOp ta tb = some ⟨p.out, (Tensor.ofFn s fun i =>
      ((List.range p.k).map fun t =>
        (⟨p.sa, ta.data⟩ : Tensor ℝ).entry (broadcastIndex p.ba (i.take p.batch.length) ++
          [i.getD p.batch.length 0, t]) *
        (⟨p.sb, tb.data⟩ : Tensor ℝ).entry (broadcastIndex p.bb (i.take p.batch.length) ++
          [t, i.getD (p.batch.length + 1) 0])).sum).data⟩ := by
    unfold matmulOp
    simp only [ha.wf, hb.wf, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte, ha.1,
      hb.1, hp, Option.map_some]
    rfl
  refine ⟨_, hreal, ?_⟩
  -- the index arithmetic
  have hidx : ∀ j < shapeSize s, ∀ t,
      ravel p.sa (broadcastIndex p.ba ((unravel s j).take p.batch.length) ++
        [(unravel s j).getD p.batch.length 0, t]) =
        (ravel p.ba (broadcastIndex p.ba ((unravel s j).take p.batch.length)) * p.m +
          (unravel s j).getD p.batch.length 0) * p.k + t ∧
      ravel p.sb (broadcastIndex p.bb ((unravel s j).take p.batch.length) ++
        [t, (unravel s j).getD (p.batch.length + 1) 0]) =
        ravel p.bb (broadcastIndex p.bb ((unravel s j).take p.batch.length)) * p.k * p.n +
          (unravel s j).getD (p.batch.length + 1) 0 + t * p.n := by
    intro j _ t
    have hl : ((unravel s j).take p.batch.length).length = p.batch.length := by
      simp [unravel_length, hs]
    constructor
    · rw [hsa, ravel_two _ _ _ _ _ _ (broadcastIndex_length _ _ (by rw [hl]; exact hba))]
    · rw [hsb, ravel_two _ _ _ _ _ _ (broadcastIndex_length _ _ (by rw [hl]; exact hbb))]
      ring
  have hea : a.exact = true → ∀ j, mget a.lo j = mget a.hi j := fun hx j => ha.lo_eq_hi hx j
  have heb : b.exact = true → ∀ j, mget b.lo j = mget b.hi j := fun hx j => hb.lo_eq_hi hx j
  -- the bounds on each entry
  have key : ∀ (lower : Bool), ∀ j < shapeSize s,
      (lower = true → dv (mget (matmulEnd true p a b) j) (a.e + b.e) ≤
        (Tensor.ofFn s fun i =>
          ((List.range p.k).map fun t =>
            (⟨p.sa, ta.data⟩ : Tensor ℝ).entry (broadcastIndex p.ba (i.take p.batch.length) ++
              [i.getD p.batch.length 0, t]) *
            (⟨p.sb, tb.data⟩ : Tensor ℝ).entry (broadcastIndex p.bb (i.take p.batch.length) ++
              [t, i.getD (p.batch.length + 1) 0])).sum).get j) ∧
      (lower = false → (Tensor.ofFn s fun i =>
          ((List.range p.k).map fun t =>
            (⟨p.sa, ta.data⟩ : Tensor ℝ).entry (broadcastIndex p.ba (i.take p.batch.length) ++
              [i.getD p.batch.length 0, t]) *
            (⟨p.sb, tb.data⟩ : Tensor ℝ).entry (broadcastIndex p.bb (i.take p.batch.length) ++
              [t, i.getD (p.batch.length + 1) 0])).sum).get j ≤
        dv (mget (matmulEnd false p a b) j) (a.e + b.e)) := by
    intro lower j hj
    rw [Tensor.ofFn_get _ _ hj, mget_matmulEnd _ _ _ _ hj, mget_matmulEnd _ _ _ _ hj, dv_list_sum,
      dv_list_sum, List.map_map, List.map_map]
    constructor
    · intro _
      apply List.sum_le_sum
      intro t _
      simp only [Function.comp_apply, Tensor.entry_eq, ↓reduceIte]
      rw [(hidx j hj t).1, (hidx j hj t).2]
      have h1 := ha.2.2.2.2.2 ((ravel p.ba (broadcastIndex p.ba ((unravel s j).take
        p.batch.length)) * p.m + (unravel s j).getD p.batch.length 0) * p.k + t)
      have h2 := hb.2.2.2.2.2 (ravel p.bb (broadcastIndex p.bb ((unravel s j).take
        p.batch.length)) * p.k * p.n + (unravel s j).getD (p.batch.length + 1) 0 + t * p.n)
      exact (prod_bounds h1.1 h1.2 h2.1 h2.2 (fun hx => hea hx _) (fun hx => heb hx _)).1
    · intro _
      apply List.sum_le_sum
      intro t _
      simp only [Function.comp_apply, Tensor.entry_eq, Bool.false_eq_true, ↓reduceIte]
      rw [(hidx j hj t).1, (hidx j hj t).2]
      have h1 := ha.2.2.2.2.2 ((ravel p.ba (broadcastIndex p.ba ((unravel s j).take
        p.batch.length)) * p.m + (unravel s j).getD p.batch.length 0) * p.k + t)
      have h2 := hb.2.2.2.2.2 (ravel p.bb (broadcastIndex p.bb ((unravel s j).take
        p.batch.length)) * p.k * p.n + (unravel s j).getD (p.batch.length + 1) 0 + t * p.n)
      exact (prod_bounds h1.1 h1.2 h2.1 h2.2 (fun hx => hea hx _) (fun hx => heb hx _)).2
  have hlo_size : (matmulEnd true p a b).size = shapeSize s := by simp [matmulEnd, hs]
  have hhi_size : (matmulEnd false p a b).size = shapeSize s := by simp [matmulEnd, hs]
  refine DT.Encl.mk rfl (by rw [Tensor.ofFn_data_size, hout]) (by rw [hlo_size, hout])
    (by split_ifs <;> simp [hlo_size, hhi_size, hout])
    (by intro hx; simp only at hx ⊢; exact (ite_eq_left hx).symm)
    ?_
  intro j hj
  have hj : j < shapeSize s := by rw [hs, ← hout]; exact hj
  refine ⟨(key true j hj).1 rfl, ?_⟩
  change _ ≤ dv (mget (if a.exact && b.exact then matmulEnd true p a b
    else matmulEnd false p a b) j) (a.e + b.e)
  split_ifs with hx
  · -- both exact: the two ends are the same products
    have e : matmulEnd true p a b = matmulEnd false p a b := by
      simp only [Bool.and_eq_true] at hx
      have hpq : ∀ al ah bl bh, prodLo true true al ah bl bh = prodHi true true al ah bl bh := by
        intro al ah bl bh
        simp [prodLo, prodHi]
      simp only [matmulEnd, hx.1, hx.2, hpq, ↓reduceIte, Bool.false_eq_true]
    rw [e]
    exact (key false j hj).2 rfl
  · exact (key false j hj).2 rfl

end CompactCheck
