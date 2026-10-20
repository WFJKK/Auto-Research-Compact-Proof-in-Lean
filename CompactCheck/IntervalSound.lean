import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.Linarith
import CompactCheck.Check

/-!
# Soundness of the interval rule

`intervalLeaf_sound`: if the interval rule accepts a box, every input in the
box passes the single test `singleOk`, which `singleOk_correct` in
`Soundness.lean` turns into a statement about the real network. The proof
follows the evaluation node by node: for every input `x` of the box, what
the interval rule knows about a node (`IVal`) is true of the node's exact
value on `x` (`IRel`).

With an approximation `P` of the output map's weight `W`, the bounds use `P`
and the error `eps`: `W[l, t] - W[j, t]` is at least `P[l, t] - P[j, t]`
minus `2 eps` (`approxTerm_le`).
-/

namespace CompactCheck

/-! ## Lemmas about tensors, sums, minima and boxes -/

theorem Tensor.get_range (s : List Nat) (n : Nat) (f : Nat → ℚ) (i : Nat) :
    (Tensor.mk s ((Array.range n).map f)).get i = if i < n then f i else 0 := by
  unfold Tensor.get
  split_ifs with h
  · simp [Array.getD, h]
  · simp [Array.getD, h]

theorem shapeSize_one : shapeSize [1] = 1 := rfl

theorem shapeSize_pair (m n : Nat) : shapeSize [m, n] = m * n := by simp [shapeSize]

/-- A sum with one nonzero term. -/
theorem sum_range_mul_ite (V a : Nat) (c : Nat → ℚ) :
    ((List.range V).map fun i => c i * (if a = i then 1 else 0)).sum =
      if a < V then c a else 0 := by
  induction V with
  | zero => simp
  | succ V ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    by_cases h1 : a < V
    · have h2 : a ≠ V := by omega
      simp [h1, h2, show a < V + 1 by omega]
    · by_cases h2 : a = V
      · subst h2
        simp
      · simp [h1, h2, show ¬ a < V + 1 by omega]

/-- Swapping two sums. -/
theorem sum_range_swap (n m : Nat) (f : Nat → Nat → ℚ) :
    ((List.range n).map fun i => ((List.range m).map fun k => f i k).sum).sum =
      ((List.range m).map fun k => ((List.range n).map fun i => f i k).sum).sum := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero]
    rw [List.sum_map_add, ih]

theorem mul_list_sum (a : ℚ) (l : List ℚ) : a * l.sum = (l.map (a * ·)).sum := by
  induction l with
  | nil => simp
  | cons b l ih => simp [mul_add, ih]

theorem sum_map_sub' {ι : Type} (l : List ι) (f g : ι → ℚ) :
    (l.map fun i => f i - g i).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp
  | cons b l ih => simp only [List.map_cons, List.sum_cons, ih]; linarith

/-- A sum over the positions of an input, by index. -/
theorem sum_range_getD (x : Input) (f : Nat → ℚ) :
    ((List.range x.length).map fun k => f (x.getD k 0)).sum = (x.map f).sum := by
  induction x with
  | nil => simp
  | cons a x ih =>
    rw [List.length_cons, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, List.sum_cons, List.getD_cons_zero]
    rw [← ih]
    congr 2

theorem min_mul_le {w a v b : ℚ} (h1 : a ≤ v) (h2 : v ≤ b) : min (w * a) (w * b) ≤ w * v := by
  rcases le_total 0 w with hw | hw
  · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left h1 hw)
  · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left h2 hw)

theorem mul_le_max {w a v b : ℚ} (h1 : a ≤ v) (h2 : v ≤ b) : w * v ≤ max (w * a) (w * b) := by
  rcases le_total 0 w with hw | hw
  · exact (mul_le_mul_of_nonneg_left h2 hw).trans (le_max_right _ _)
  · exact (mul_le_mul_of_nonpos_left h1 hw).trans (le_max_left _ _)

theorem foldl_min_le (g : Nat → ℚ) : ∀ (l : List Nat) (m : ℚ),
    l.foldl (fun m k => min m (g k)) m ≤ m ∧ ∀ k ∈ l, l.foldl (fun m k => min m (g k)) m ≤ g k
  | [], m => ⟨le_refl _, by simp⟩
  | k :: l, m => by
    obtain ⟨h1, h2⟩ := foldl_min_le g l (min m (g k))
    simp only [List.foldl_cons]
    refine ⟨h1.trans (min_le_left _ _), ?_⟩
    intro k' hk'
    rcases List.mem_cons.mp hk' with rfl | hk'
    · exact h1.trans (min_le_right _ _)
    · exact h2 k' hk'

theorem le_foldl_max (g : Nat → ℚ) : ∀ (l : List Nat) (m : ℚ),
    m ≤ l.foldl (fun m k => max m (g k)) m ∧ ∀ k ∈ l, g k ≤ l.foldl (fun m k => max m (g k)) m
  | [], m => ⟨le_refl _, by simp⟩
  | k :: l, m => by
    obtain ⟨h1, h2⟩ := le_foldl_max g l (max m (g k))
    simp only [List.foldl_cons]
    refine ⟨(le_max_left _ _).trans h1, ?_⟩
    intro k' hk'
    rcases List.mem_cons.mp hk' with rfl | hk'
    · exact (le_max_right _ _).trans h1
    · exact h2 k' hk'

theorem rangeMin_le (f : Nat → ℚ) (lo hi t : Nat) (h1 : lo ≤ t) (h2 : t ≤ hi) :
    rangeMin f lo hi ≤ f t := by
  unfold rangeMin
  obtain ⟨hm, hk⟩ := foldl_min_le (fun k => f (lo + 1 + k)) (List.range (hi - lo)) (f lo)
  rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
  · exact hm
  · have := hk (t - lo - 1) (List.mem_range.mpr (by omega))
    rwa [show lo + 1 + (t - lo - 1) = t by omega] at this

theorem le_rangeMax (f : Nat → ℚ) (lo hi t : Nat) (h1 : lo ≤ t) (h2 : t ≤ hi) :
    f t ≤ rangeMax f lo hi := by
  unfold rangeMax
  obtain ⟨hm, hk⟩ := le_foldl_max (fun k => f (lo + 1 + k)) (List.range (hi - lo)) (f lo)
  rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
  · exact hm
  · have := hk (t - lo - 1) (List.mem_range.mpr (by omega))
    rwa [show lo + 1 + (t - lo - 1) = t by omega] at this

theorem inBox_length : ∀ {box : Box} {x : Input}, inBox box x = true → x.length = box.length
  | [], [], _ => rfl
  | _ :: rs, _ :: ts, h => by
    simp only [inBox, Bool.and_eq_true] at h
    simp [inBox_length h.2]
  | [], _ :: _, h => by simp [inBox] at h
  | _ :: _, [], h => by simp [inBox] at h

theorem inBox_getD : ∀ {box : Box} {x : Input}, inBox box x = true → ∀ p < box.length,
    (box.getD p ⟨0, 0⟩).lo ≤ x.getD p 0 ∧ x.getD p 0 ≤ (box.getD p ⟨0, 0⟩).hi
  | [], [], _, p, hp => by simp at hp
  | r :: rs, t :: ts, h, p, hp => by
    simp only [inBox, inRange, Bool.and_eq_true, decide_eq_true_eq] at h
    cases p with
    | zero => simpa using h.1
    | succ q => simpa using inBox_getD h.2 q (by simpa using hp)
  | [], _ :: _, h, _, _ => by simp [inBox] at h
  | _ :: _, [], h, _, _ => by simp [inBox] at h

theorem inBox_lt : ∀ {box : Box} {x : Input} {V : Nat}, inBox box x = true →
    (∀ r ∈ box, r.hi < V) → ∀ v ∈ x, v < V
  | [], [], _, _, _, v, hv => by simp at hv
  | r :: rs, t :: ts, V, h, hV, v, hv => by
    simp only [inBox, inRange, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.mp hv with rfl | hv
    · exact lt_of_le_of_lt h.1.2 (hV r (by simp))
    · exact inBox_lt h.2 (fun r' hr' => hV r' (by simp [hr'])) v hv
  | [], _ :: _, _, h, _, _, _ => by simp [inBox] at h
  | _ :: _, [], _, h, _, _, _ => by simp [inBox] at h

/-- Summing a lower bound over the ranges of a box. -/
theorem sum_box_le : ∀ {box : Box} {x : Input}, inBox box x = true →
    ∀ (g : Range → ℚ) (f : Nat → ℚ), (∀ r t, r.lo ≤ t → t ≤ r.hi → g r ≤ f t) →
      (box.map g).sum ≤ (x.map f).sum
  | [], [], _, _, _, _ => by simp
  | r :: rs, t :: ts, h, g, f, hgf => by
    simp only [inBox, inRange, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (hgf r t h.1.1 h.1.2) (sum_box_le h.2 g f hgf)
  | [], _ :: _, h, _, _, _ => by simp [inBox] at h
  | _ :: _, [], h, _, _, _ => by simp [inBox] at h

/-- The same, with the bound needed only for the ranges of the box. -/
theorem sum_box_le' : ∀ {box : Box} {x : Input}, inBox box x = true →
    ∀ (g : Range → ℚ) (f : Nat → ℚ), (∀ r ∈ box, ∀ t, r.lo ≤ t → t ≤ r.hi → g r ≤ f t) →
      (box.map g).sum ≤ (x.map f).sum
  | [], [], _, _, _, _ => by simp
  | r :: rs, t :: ts, h, g, f, hgf => by
    simp only [inBox, inRange, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (hgf r (by simp) t h.1.1 h.1.2)
      (sum_box_le' h.2 g f fun r' hr' => hgf r' (by simp [hr']))
  | [], _ :: _, h, _, _, _ => by simp [inBox] at h
  | _ :: _, [], h, _, _, _ => by simp [inBox] at h

/-! ## Index arithmetic -/

theorem idx_lt {p P V i : Nat} (hp : p < P) (hi : i < V) : p * V + i < P * V := by
  have : (p + 1) * V ≤ P * V := Nat.mul_le_mul_right V hp
  nlinarith

theorem idx_div {p V i : Nat} (hi : i < V) : (p * V + i) / V = p := by
  rw [Nat.add_comm (p * V) i, Nat.add_mul_div_right _ _ (by omega),
    Nat.div_eq_of_lt hi, zero_add]

theorem idx_mod {p V i : Nat} (hi : i < V) : (p * V + i) % V = i := by
  rw [Nat.add_comm (p * V) i, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]

/-! ## What the interval values say -/

/-- What an interval value says about the exact value `t` of a node on the
    input `x`: the one-hot input (or its sum over the positions) of `x`, or
    a tensor between `lo` and `hi`. -/
def IRel (P V : Nat) (box : Box) (x : Input) : IVal → Tensor ℚ → Prop
  | .oneHot false, t => box.length = P ∧ (∀ r ∈ box, r.hi < V) ∧ t.shape = [1, P, V] ∧
      t.data.size = P * V ∧
      ∀ p < P, ∀ i < V, t.get (p * V + i) = if x.getD p 0 = i then 1 else 0
  | .oneHot true, t => box.length = P ∧ (∀ r ∈ box, r.hi < V) ∧ t.shape = [1, V] ∧
      t.data.size = V ∧
      ∀ i < V, t.get i = ((List.range P).map fun k => if x.getD k 0 = i then (1 : ℚ) else 0).sum
  | .bounds lo hi, t => t.shape = lo.shape ∧ hi.shape = lo.shape ∧ t.data.size = lo.data.size ∧
      hi.data.size = lo.data.size ∧ ∀ i, lo.get i ≤ t.get i ∧ t.get i ≤ hi.get i

/-- The same for a node. For a linear map it also says that the value is the
    map applied to a value its argument's interval value describes. -/
def NodeRel (P V : Nat) (box : Box) (x : Input) (n : INode) (t : Tensor ℚ) : Prop :=
  IRel P V box x n.val t ∧
    ∀ a W b, n.lin = some (a, W, b) → ∃ ta, IRel P V box x a ta ∧ linearOp W b ta = some t

theorem xlen_of {P : Nat} {box : Box} {x : Input} (hx : inBox box x = true)
    (hlen : box.length = P) : x.length = P := by
  rw [inBox_length hx, hlen]

theorem getD_lt_of {P V : Nat} {box : Box} {x : Input} (hx : inBox box x = true)
    (hlen : box.length = P) (hV : ∀ r ∈ box, r.hi < V) (k : Nat) (hk : k < P) :
    x.getD k 0 < V := by
  have hk' : k < x.length := by rw [xlen_of hx hlen]; exact hk
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk', Option.getD_some]
  exact inBox_lt hx hV _ (List.getElem_mem hk')

/-- On the summed one-hot input, `Σ_i c_i * t_i` is the sum over the
    positions of `c` at the token there. -/
theorem summed_dot {P V : Nat} {box : Box} {x : Input} {t : Tensor ℚ}
    (hx : inBox box x = true) (h : IRel P V box x (.oneHot true) t) (c : Nat → ℚ) :
    ((List.range V).map fun i => c i * t.get i).sum = (x.map c).sum := by
  obtain ⟨hlen, hV, -, -, hget⟩ := h
  calc ((List.range V).map fun i => c i * t.get i).sum
      = ((List.range V).map fun i =>
          ((List.range P).map fun k => c i * (if x.getD k 0 = i then 1 else 0)).sum).sum := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro i hi
        rw [hget i (List.mem_range.mp hi), mul_list_sum, List.map_map]
        rfl
    _ = ((List.range P).map fun k =>
          ((List.range V).map fun i => c i * (if x.getD k 0 = i then 1 else 0)).sum).sum :=
        sum_range_swap _ _ _
    _ = ((List.range P).map fun k => c (x.getD k 0)).sum := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro k hk
        rw [sum_range_mul_ite]
        simp only [getD_lt_of hx hlen hV k (List.mem_range.mp hk), ↓reduceIte]
    _ = (x.map c).sum := by
        rw [← xlen_of hx hlen]
        exact sum_range_getD x c

/-- On the one-hot input, `Σ_i c_i * t[p, i]` is `c` at the token of
    position `p`. -/
theorem perPos_dot {P V : Nat} {box : Box} {x : Input} {t : Tensor ℚ}
    (hx : inBox box x = true) (h : IRel P V box x (.oneHot false) t) (c : Nat → ℚ)
    (p : Nat) (hp : p < P) :
    ((List.range V).map fun i => c i * t.get (p * V + i)).sum = c (x.getD p 0) := by
  obtain ⟨hlen, hV, -, -, hget⟩ := h
  calc ((List.range V).map fun i => c i * t.get (p * V + i)).sum
      = ((List.range V).map fun i => c i * (if x.getD p 0 = i then 1 else 0)).sum := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro i hi
        rw [hget p hp i (List.mem_range.mp hi)]
    _ = c (x.getD p 0) := by
        rw [sum_range_mul_ite]
        simp only [getD_lt_of hx hlen hV p hp, ↓reduceIte]

/-! ## Each operation keeps the relation -/

theorem input_rel {P V : Nat} {box : Box} {x : Input} (hx : inBox box x = true)
    (hc : (box.length == P && box.all (fun r => r.hi < V)) = true) :
    ∃ t, oneHotInput P V x = some t ∧ IRel P V box x (.oneHot false) t := by
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hc
  obtain ⟨hlen, hV⟩ := hc
  have hcond : (x.length == P && x.all (· < V)) = true := by
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq]
    exact ⟨xlen_of hx hlen, inBox_lt hx hV⟩
  refine ⟨⟨[1, P, V], (Array.range (P * V)).map fun j =>
    if x.getD (j / V) 0 = j % V then 1 else 0⟩, ?_, hlen, hV, rfl, by simp, ?_⟩
  · unfold oneHotInput
    rw [ite_eq_left hcond]
  · intro p hp i hi
    rw [Tensor.get_range, ite_eq_left (idx_lt hp hi), idx_div hi, idx_mod hi]

theorem sum_onehot_rel {P V : Nat} {box : Box} {x : Input} {t : Tensor ℚ} {dim : Int}
    (h : IRel P V box x (.oneHot false) t) (hd : normDim dim 3 = some 1) :
    ∃ t', sumOp dim t = some t' ∧ IRel P V box x (.oneHot true) t' := by
  obtain ⟨hlen, hV, hshape, hsize, hget⟩ := h
  simp only [sumOp, hshape, List.length_cons, List.length_nil, hd]
  simp only [hsize, shapeSize, List.take_succ_cons, List.take_zero, List.foldr_cons,
    List.foldr_nil, mul_one, List.getD_eq_getElem?_getD, List.length_cons, List.length_nil,
    zero_add, Nat.reduceAdd, Nat.one_lt_ofNat, getElem?_pos, List.getElem_cons_succ,
    List.getElem_cons_zero, Option.getD_some, one_mul, List.drop_succ_cons, List.drop_zero,
    BEq.rfl, ↓reduceIte, List.eraseIdx_cons_succ, List.eraseIdx_zero, List.tail_cons,
    Option.some.injEq, exists_eq_left']
  refine ⟨hlen, hV, rfl, by simp, ?_⟩
  intro i hi
  rw [Tensor.get_range, ite_eq_left hi, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]
  apply congrArg List.sum
  apply List.map_congr_left
  intro k hk
  rw [zero_mul, zero_add, hget k (List.mem_range.mp hk) i hi]

theorem sum_bounds_rel {P V : Nat} {box : Box} {x : Input} {lo hi t lo' hi' : Tensor ℚ}
    {dim : Int} (h : IRel P V box x (.bounds lo hi) t) (hlo : sumOp dim lo = some lo')
    (hhi : sumOp dim hi = some hi') :
    ∃ t', sumOp dim t = some t' ∧ IRel P V box x (.bounds lo' hi') t' := by
  obtain ⟨hs, hhs, hsz, hhsz, hb⟩ := h
  unfold sumOp at hlo hhi ⊢
  rw [hs, hsz]
  rw [hhs, hhsz] at hhi
  cases hn : normDim dim lo.shape.length with
  | none => simp [hn] at hlo
  | some d =>
    simp only [hn] at hlo hhi ⊢
    split_ifs at hlo with hc
    rw [ite_eq_left hc] at hhi
    rw [ite_eq_left hc]
    cases hlo
    cases hhi
    refine ⟨_, rfl, rfl, rfl, by simp, by simp, ?_⟩
    intro j
    simp only [Tensor.get_range]
    split_ifs
    · exact ⟨List.sum_le_sum (fun k _ => (hb _).1), List.sum_le_sum (fun k _ => (hb _).2)⟩
    · exact ⟨le_refl _, le_refl _⟩

theorem add_rel {P V : Nat} {box : Box} {x : Input} {lo1 hi1 lo2 hi2 lo hi ta tb : Tensor ℚ}
    (ha : IRel P V box x (.bounds lo1 hi1) ta) (hb : IRel P V box x (.bounds lo2 hi2) tb)
    (hlo : addOp lo1 lo2 = some lo) (hhi : addOp hi1 hi2 = some hi) :
    ∃ t, addOp ta tb = some t ∧ IRel P V box x (.bounds lo hi) t := by
  obtain ⟨hs1, hhs1, hsz1, hhsz1, hb1⟩ := ha
  obtain ⟨hs2, hhs2, hsz2, hhsz2, hb2⟩ := hb
  unfold addOp at hlo hhi ⊢
  rw [hs1, hs2, hsz1, hsz2]
  rw [hhs1, hhs2, hhsz1, hhsz2] at hhi
  split_ifs at hlo with hc
  rw [ite_eq_left hc] at hhi
  rw [ite_eq_left hc]
  cases hlo
  cases hhi
  refine ⟨_, rfl, rfl, rfl, by simp, by simp, ?_⟩
  intro j
  simp only [Tensor.get_range]
  split_ifs
  · exact ⟨add_le_add (hb1 j).1 (hb2 j).1, add_le_add (hb1 j).2 (hb2 j).2⟩
  · exact ⟨le_refl _, le_refl _⟩

/-! ### Linear maps -/

/-- The bias fits `out` outputs. -/
def biasFits (b : Option (Tensor ℚ)) (out : Nat) : Prop :=
  match b with
  | some b => b.shape = [out] ∧ b.data.size = out
  | none => True

/-- What `linearOp` computes when the shapes fit. -/
theorem linearOp_some {W t : Tensor ℚ} {b : Option (Tensor ℚ)} {out inn : Nat} {pre : List Nat}
    (hW : W.shape = [out, inn]) (hWs : W.data.size = out * inn) (ht : t.shape = pre ++ [inn])
    (hts : t.data.size = shapeSize pre * inn) (hb : biasFits b out) :
    linearOp W b t = some ⟨pre ++ [out], (Array.range (shapeSize pre * out)).map fun j =>
      ((List.range inn).map fun i => W.get (j % out * inn + i) * t.get (j / out * inn + i)).sum +
        biasAt b (j % out)⟩ := by
  cases b with
  | none => simp [linearOp, hW, hWs, ht, hts, biasAt]
  | some bb =>
    obtain ⟨hb1, hb2⟩ := hb
    simp [linearOp, hW, hWs, ht, hts, biasAt, hb1, hb2]

/-- What a successful `linearOp` computed. -/
theorem linearOp_inv {W t out : Tensor ℚ} {b : Option (Tensor ℚ)} (h : linearOp W b t = some out) :
    ∃ o inn pre, W.shape = [o, inn] ∧ W.data.size = o * inn ∧ t.shape = pre ++ [inn] ∧
      t.data.size = shapeSize pre * inn ∧ biasFits b o ∧
      out = ⟨pre ++ [o], (Array.range (shapeSize pre * o)).map fun j =>
        ((List.range inn).map fun i => W.get (j % o * inn + i) * t.get (j / o * inn + i)).sum +
          biasAt b (j % o)⟩ := by
  have key : ∃ o inn pre, W.shape = [o, inn] ∧ W.data.size = o * inn ∧ t.shape = pre ++ [inn] ∧
      t.data.size = shapeSize pre * inn ∧ biasFits b o := by
    cases b with
    | none =>
      simp only [linearOp] at h
      split_ifs at h with hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨⟨⟨hW, hlast⟩, hWs⟩, hts⟩, -⟩ := hc
      obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hlast
      refine ⟨_, _, ys, hW, hWs, hys, ?_, trivial⟩
      rw [hts, hys, List.dropLast_concat]
    | some bb =>
      simp only [linearOp] at h
      split_ifs at h with hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨⟨⟨hW, hlast⟩, hWs⟩, hts⟩, hb1, hb2⟩ := hc
      obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hlast
      refine ⟨_, _, ys, hW, hWs, hys, ?_, hb1, hb2⟩
      rw [hts, hys, List.dropLast_concat]
  obtain ⟨o, inn, pre, hW, hWs, ht, hts, hb⟩ := key
  refine ⟨o, inn, pre, hW, hWs, ht, hts, hb, ?_⟩
  rw [linearOp_some hW hWs ht hts hb] at h
  exact (Option.some.inj h).symm

/-- What a successful `ilinearBounds` computed. -/
theorem ilinearBounds_inv {W lo hi : Tensor ℚ} {b : Option (Tensor ℚ)} {v : IVal}
    (h : ilinearBounds W b lo hi = some v) :
    ∃ o inn pre, W.shape = [o, inn] ∧ W.data.size = o * inn ∧ lo.shape = pre ++ [inn] ∧
      lo.data.size = shapeSize pre * inn ∧ biasFits b o ∧
      v = .bounds
        ⟨pre ++ [o], (Array.range (shapeSize pre * o)).map fun j =>
          ((List.range inn).map fun i => min (W.get (j % o * inn + i) * lo.get (j / o * inn + i))
            (W.get (j % o * inn + i) * hi.get (j / o * inn + i))).sum + biasAt b (j % o)⟩
        ⟨pre ++ [o], (Array.range (shapeSize pre * o)).map fun j =>
          ((List.range inn).map fun i => max (W.get (j % o * inn + i) * lo.get (j / o * inn + i))
            (W.get (j % o * inn + i) * hi.get (j / o * inn + i))).sum + biasAt b (j % o)⟩ := by
  cases b with
  | none =>
    simp only [ilinearBounds] at h
    split_ifs at h with hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨hW, hlast⟩, hWs⟩, hlos⟩, -⟩, -⟩, -⟩ := hc
    obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hlast
    refine ⟨_, _, ys, hW, hWs, hys, by rw [hlos, hys, List.dropLast_concat], trivial, ?_⟩
    rw [hys, List.dropLast_concat] at h
    exact (Option.some.inj h).symm
  | some bb =>
    simp only [ilinearBounds] at h
    split_ifs at h with hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨hW, hlast⟩, hWs⟩, hlos⟩, hb1, hb2⟩, -⟩, -⟩ := hc
    obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hlast
    refine ⟨_, _, ys, hW, hWs, hys, by rw [hlos, hys, List.dropLast_concat], ⟨hb1, hb2⟩, ?_⟩
    rw [hys, List.dropLast_concat] at h
    exact (Option.some.inj h).symm

/-- What a successful `ilinearOneHot` computed on the summed one-hot input. -/
theorem ilinearOneHot_summed_inv {box : Box} {P V : Nat} {W : Tensor ℚ}
    {b : Option (Tensor ℚ)} {v : IVal} (h : ilinearOneHot box P V true W b = some v) :
    ∃ o, W.shape = [o, V] ∧ W.data.size = o * V ∧ biasFits b o ∧
      v = .bounds
        ⟨[1, o], (Array.range o).map fun j =>
          (box.map fun r => rangeMin (fun t => W.get (j * V + t)) r.lo r.hi).sum + biasAt b j⟩
        ⟨[1, o], (Array.range o).map fun j =>
          (box.map fun r => rangeMax (fun t => W.get (j * V + t)) r.lo r.hi).sum + biasAt b j⟩ := by
  cases b with
  | none =>
    simp only [ilinearOneHot, ↓reduceIte] at h
    split_ifs at h with hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact ⟨_, hc.1.1, hc.1.2, trivial, (Option.some.inj h).symm⟩
  | some bb =>
    simp only [ilinearOneHot, ↓reduceIte] at h
    split_ifs at h with hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact ⟨_, hc.1.1, hc.1.2, hc.2, (Option.some.inj h).symm⟩

/-- What a successful `ilinearOneHot` computed on the one-hot input. -/
theorem ilinearOneHot_perPos_inv {box : Box} {P V : Nat} {W : Tensor ℚ}
    {b : Option (Tensor ℚ)} {v : IVal} (h : ilinearOneHot box P V false W b = some v) :
    ∃ o, W.shape = [o, V] ∧ W.data.size = o * V ∧ biasFits b o ∧
      v = .bounds
        ⟨[1, P, o], (Array.range (P * o)).map fun j =>
          rangeMin (fun t => W.get (j % o * V + t)) (box.getD (j / o) ⟨0, 0⟩).lo
            (box.getD (j / o) ⟨0, 0⟩).hi + biasAt b (j % o)⟩
        ⟨[1, P, o], (Array.range (P * o)).map fun j =>
          rangeMax (fun t => W.get (j % o * V + t)) (box.getD (j / o) ⟨0, 0⟩).lo
            (box.getD (j / o) ⟨0, 0⟩).hi + biasAt b (j % o)⟩ := by
  cases b with
  | none =>
    simp only [ilinearOneHot, Bool.false_eq_true, ↓reduceIte] at h
    split_ifs at h with hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact ⟨_, hc.1.1, hc.1.2, trivial, (Option.some.inj h).symm⟩
  | some bb =>
    simp only [ilinearOneHot, Bool.false_eq_true, ↓reduceIte] at h
    split_ifs at h with hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact ⟨_, hc.1.1, hc.1.2, hc.2, (Option.some.inj h).symm⟩

/-- Summing an upper bound over the ranges of a box. -/
theorem sum_le_box : ∀ {box : Box} {x : Input}, inBox box x = true →
    ∀ (g : Range → ℚ) (f : Nat → ℚ), (∀ r t, r.lo ≤ t → t ≤ r.hi → f t ≤ g r) →
      (x.map f).sum ≤ (box.map g).sum
  | [], [], _, _, _, _ => by simp
  | r :: rs, t :: ts, h, g, f, hgf => by
    simp only [inBox, inRange, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (hgf r t h.1.1 h.1.2) (sum_le_box h.2 g f hgf)
  | [], _ :: _, h, _, _, _ => by simp [inBox] at h
  | _ :: _, [], h, _, _, _ => by simp [inBox] at h

theorem linear_bounds_rel {P V : Nat} {box : Box} {x : Input} {lo hi t W : Tensor ℚ}
    {b : Option (Tensor ℚ)} {v : IVal} (h : IRel P V box x (.bounds lo hi) t)
    (hv : ilinearBounds W b lo hi = some v) :
    ∃ t', linearOp W b t = some t' ∧ IRel P V box x v t' := by
  obtain ⟨o, inn, pre, hW, hWs, hlo, hlos, hb, rfl⟩ := ilinearBounds_inv hv
  obtain ⟨hs, -, hsz, -, hbd⟩ := h
  refine ⟨_, linearOp_some hW hWs (hs.trans hlo) (hsz.trans hlos) hb, rfl, rfl, by simp,
    by simp, ?_⟩
  intro j
  simp only [Tensor.get_range]
  split_ifs
  · exact ⟨add_le_add (List.sum_le_sum fun i _ => min_mul_le (hbd _).1 (hbd _).2) le_rfl,
      add_le_add (List.sum_le_sum fun i _ => mul_le_max (hbd _).1 (hbd _).2) le_rfl⟩
  · exact ⟨le_refl _, le_refl _⟩

theorem linear_summed_rel {P V : Nat} {box : Box} {x : Input} (hx : inBox box x = true)
    {ta W : Tensor ℚ} {b : Option (Tensor ℚ)} {v : IVal}
    (h : IRel P V box x (.oneHot true) ta) (hv : ilinearOneHot box P V true W b = some v) :
    ∃ t, linearOp W b ta = some t ∧ IRel P V box x v t := by
  obtain ⟨o, hW, hWs, hb, rfl⟩ := ilinearOneHot_summed_inv hv
  have h' := h
  obtain ⟨hlen, hV, hshape, hsize, -⟩ := h'
  refine ⟨_, linearOp_some (pre := [1]) hW hWs (by rw [hshape]; rfl)
    (by rw [hsize, shapeSize_one, one_mul]) hb, rfl, rfl, by simp [shapeSize], by simp, ?_⟩
  intro j
  simp only [Tensor.get_range, shapeSize_one, one_mul]
  split_ifs with hj
  · rw [Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj]
    simp only [zero_mul, zero_add]
    rw [summed_dot hx h (fun i => W.get (j * V + i))]
    exact ⟨add_le_add (sum_box_le hx _ _ fun r t h1 h2 =>
        rangeMin_le (fun t => W.get (j * V + t)) _ _ _ h1 h2) le_rfl,
      add_le_add (sum_le_box hx _ _ fun r t h1 h2 =>
        le_rangeMax (fun t => W.get (j * V + t)) _ _ _ h1 h2) le_rfl⟩
  · exact ⟨le_refl _, le_refl _⟩

theorem linear_perPos_rel {P V : Nat} {box : Box} {x : Input} (hx : inBox box x = true)
    {ta W : Tensor ℚ} {b : Option (Tensor ℚ)} {v : IVal}
    (h : IRel P V box x (.oneHot false) ta) (hv : ilinearOneHot box P V false W b = some v) :
    ∃ t, linearOp W b ta = some t ∧ IRel P V box x v t := by
  obtain ⟨o, hW, hWs, hb, rfl⟩ := ilinearOneHot_perPos_inv hv
  have h' := h
  obtain ⟨hlen, hV, hshape, hsize, -⟩ := h'
  refine ⟨_, linearOp_some (pre := [1, P]) hW hWs (by rw [hshape]; rfl)
    (by rw [hsize, shapeSize_pair, one_mul]) hb, rfl, rfl, by simp [shapeSize], by simp, ?_⟩
  intro j
  simp only [Tensor.get_range, shapeSize_pair, one_mul]
  split_ifs with hj
  · have ho : 0 < o := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hj
    have hp : j / o < P := (Nat.div_lt_iff_lt_mul ho).mpr hj
    rw [perPos_dot hx h (fun i => W.get (j % o * V + i)) (j / o) hp]
    obtain ⟨h1, h2⟩ := inBox_getD hx (j / o) (by rw [hlen]; exact hp)
    exact ⟨add_le_add (rangeMin_le (fun t => W.get (j % o * V + t)) _ _ _ h1 h2) le_rfl,
      add_le_add (le_rangeMax (fun t => W.get (j % o * V + t)) _ _ _ h1 h2) le_rfl⟩
  · exact ⟨le_refl _, le_refl _⟩

theorem ilinear_rel {P V : Nat} {box : Box} {x : Input} (hx : inBox box x = true)
    {iv : IVal} {t W : Tensor ℚ} {b : Option (Tensor ℚ)} {v : IVal}
    (h : IRel P V box x iv t) (hv : ilinear box P V W b iv = some v) :
    ∃ t', linearOp W b t = some t' ∧ IRel P V box x v t' := by
  cases iv with
  | oneHot s =>
    cases s
    · exact linear_perPos_rel hx h hv
    · exact linear_summed_rel hx h hv
  | bounds lo hi => exact linear_bounds_rel h hv

theorem isum_rel {P V : Nat} {box : Box} {x : Input} {iv : IVal} {t : Tensor ℚ} {dim : Int}
    {v : IVal} (h : IRel P V box x iv t) (hv : isum dim iv = some v) :
    ∃ t', sumOp dim t = some t' ∧ IRel P V box x v t' := by
  cases iv with
  | oneHot s =>
    cases s
    · simp only [isum] at hv
      split_ifs at hv with hd
      cases hv
      exact sum_onehot_rel h (by simpa using hd)
    · simp [isum] at hv
  | bounds lo hi =>
    simp only [isum] at hv
    cases hlo : sumOp dim lo with
    | none => simp [hlo] at hv
    | some lo' =>
      cases hhi : sumOp dim hi with
      | none => simp [hlo, hhi] at hv
      | some hi' =>
        simp only [hlo, hhi, Option.some.injEq] at hv
        subst hv
        exact sum_bounds_rel h hlo hhi

theorem iadd_rel {P V : Nat} {box : Box} {x : Input} {iv1 iv2 : IVal} {t1 t2 : Tensor ℚ}
    {v : IVal} (h1 : IRel P V box x iv1 t1) (h2 : IRel P V box x iv2 t2)
    (hv : iadd iv1 iv2 = some v) : ∃ t, addOp t1 t2 = some t ∧ IRel P V box x v t := by
  cases iv1 with
  | oneHot s => simp [iadd] at hv
  | bounds lo1 hi1 =>
    cases iv2 with
    | oneHot s => simp [iadd] at hv
    | bounds lo2 hi2 =>
      simp only [iadd] at hv
      cases hlo : addOp lo1 lo2 with
      | none => simp [hlo] at hv
      | some lo =>
        cases hhi : addOp hi1 hi2 with
        | none => simp [hlo, hhi] at hv
        | some hi =>
          simp only [hlo, hhi, Option.some.injEq] at hv
          subst hv
          exact add_rel h1 h2 hlo hhi

/-! ## Following the whole network -/

/-- The interval nodes computed so far describe the exact values computed so
    far, node by node. -/
def ArrRel (P V : Nat) (box : Box) (x : Input) (nodes : Array INode)
    (vals : Array (Tensor ℚ)) : Prop :=
  nodes.size = vals.size ∧
    ∀ k (h1 : k < nodes.size) (h2 : k < vals.size), NodeRel P V box x nodes[k] vals[k]

theorem ArrRel.get? {P V : Nat} {box : Box} {x : Input} {nodes : Array INode}
    {vals : Array (Tensor ℚ)} (h : ArrRel P V box x nodes vals) {a : Nat} {n : INode}
    (ha : nodes[a]? = some n) : ∃ t, vals[a]? = some t ∧ NodeRel P V box x n t := by
  obtain ⟨hsize, hrel⟩ := h
  obtain ⟨h1, rfl⟩ := Array.getElem?_eq_some_iff.mp ha
  have h2 : a < vals.size := hsize ▸ h1
  exact ⟨vals[a], Array.getElem?_eq_getElem h2, hrel a h1 h2⟩

theorem ArrRel.push {P V : Nat} {box : Box} {x : Input} {nodes : Array INode}
    {vals : Array (Tensor ℚ)} {n : INode} {t : Tensor ℚ} (h : ArrRel P V box x nodes vals)
    (hr : NodeRel P V box x n t) : ArrRel P V box x (nodes.push n) (vals.push t) := by
  obtain ⟨hsize, hrel⟩ := h
  refine ⟨by simp [hsize], ?_⟩
  intro k h1 h2
  simp only [Array.getElem_push]
  split_ifs with hk1 hk2 hk2
  · exact hrel k hk1 hk2
  · omega
  · omega
  · exact hr

theorem ievalOp_sim {g : Graph} {w : Weights ℚ} {box : Box} {x : Input}
    (hx : inBox box x = true) {nodes : Array INode} {vals : Array (Tensor ℚ)}
    (hrel : ArrRel g.positions g.values box x nodes vals) {op : Op} {n : INode}
    (h : ievalOp g w box nodes op = some n) :
    ∃ t, evalOp g w x vals op = some t ∧ NodeRel g.positions g.values box x n t := by
  cases op with
  | input =>
    simp only [ievalOp] at h
    split_ifs at h with hc
    cases h
    obtain ⟨t, ht, hr⟩ := input_rel hx hc
    exact ⟨t, ht, hr, by simp⟩
  | linear a wn bn =>
    cases ha : nodes[a]? with
    | none => simp [ievalOp, ha] at h
    | some na =>
      obtain ⟨ta, hta, hra⟩ := hrel.get? ha
      cases hW : List.lookup wn w with
      | none => simp [ievalOp, ha, hW] at h
      | some W =>
        cases bn with
        | none =>
          simp only [ievalOp, ha, hW, Option.map_eq_some_iff] at h
          obtain ⟨v, hv, rfl⟩ := h
          obtain ⟨t, ht, hr⟩ := ilinear_rel hx hra.1 hv
          refine ⟨t, ?_, hr, ?_⟩
          · simp only [evalOp, hta, hW]
            exact ht
          · intro a' W' b' he
            simp only [Option.some.injEq, Prod.mk.injEq] at he
            obtain ⟨rfl, rfl, rfl⟩ := he
            exact ⟨ta, hra.1, ht⟩
        | some bn =>
          cases hb : List.lookup bn w with
          | none => simp [ievalOp, ha, hW, hb] at h
          | some bb =>
            simp only [ievalOp, ha, hW, hb, Option.map_eq_some_iff] at h
            obtain ⟨v, hv, rfl⟩ := h
            obtain ⟨t, ht, hr⟩ := ilinear_rel hx hra.1 hv
            refine ⟨t, ?_, hr, ?_⟩
            · simp only [evalOp, hta, hW, hb]
              exact ht
            · intro a' W' b' he
              simp only [Option.some.injEq, Prod.mk.injEq] at he
              obtain ⟨rfl, rfl, rfl⟩ := he
              exact ⟨ta, hra.1, ht⟩
  | sum a d =>
    cases ha : nodes[a]? with
    | none => simp [ievalOp, ha] at h
    | some na =>
      obtain ⟨ta, hta, hra⟩ := hrel.get? ha
      simp only [ievalOp, ha, Option.map_eq_some_iff] at h
      obtain ⟨v, hv, rfl⟩ := h
      obtain ⟨t, ht, hr⟩ := isum_rel hra.1 hv
      refine ⟨t, ?_, hr, by simp⟩
      simp only [evalOp, hta]
      exact ht
  | add a b =>
    cases ha : nodes[a]? with
    | none => simp [ievalOp, ha] at h
    | some na =>
      cases hb : nodes[b]? with
      | none => simp [ievalOp, ha, hb] at h
      | some nb =>
        obtain ⟨ta, hta, hra⟩ := hrel.get? ha
        obtain ⟨tb, htb, hrb⟩ := hrel.get? hb
        simp only [ievalOp, ha, hb, Option.map_eq_some_iff] at h
        obtain ⟨v, hv, rfl⟩ := h
        obtain ⟨t, ht, hr⟩ := iadd_rel hra.1 hrb.1 hv
        refine ⟨t, ?_, hr, by simp⟩
        simp only [evalOp, hta, htb]
        exact ht
  | _ => simp [ievalOp] at h

theorem ievalOps_sim {g : Graph} {w : Weights ℚ} {box : Box} {x : Input}
    (hx : inBox box x = true) :
    ∀ (ops : List Op) (nodes : Array INode) (vals : Array (Tensor ℚ)) (nodes' : Array INode),
      ArrRel g.positions g.values box x nodes vals → ievalOps g w box ops nodes = some nodes' →
      ∃ vals', evalOps g w x ops vals = some vals' ∧ ArrRel g.positions g.values box x nodes' vals'
  | [], nodes, vals, nodes', hrel, h => by
    simp only [ievalOps, Option.some.injEq] at h
    subst h
    exact ⟨vals, rfl, hrel⟩
  | op :: ops, nodes, vals, nodes', hrel, h => by
    simp only [ievalOps] at h
    cases hn : ievalOp g w box nodes op with
    | none => simp [hn] at h
    | some n =>
      simp only [hn] at h
      obtain ⟨t, ht, hr⟩ := ievalOp_sim hx hrel hn
      obtain ⟨vals', h1, h2⟩ := ievalOps_sim hx ops _ _ _ (hrel.push hr) h
      refine ⟨vals', ?_, h2⟩
      simp only [evalOps, ht]
      exact h1

/-- A linear map in interval mode records its weight, looked up by name. -/
theorem ievalOp_lin {g : Graph} {w : Weights ℚ} {box : Box} {nodes : Array INode} {op : Op}
    {n : INode} {arg : IVal} {W : Tensor ℚ} {b : Option (Tensor ℚ)}
    (h : ievalOp g w box nodes op = some n) (hlin : n.lin = some (arg, W, b)) :
    ∃ a wn bn, op = .linear a wn bn ∧ List.lookup wn w = some W := by
  cases op with
  | input =>
    simp only [ievalOp] at h
    split_ifs at h
    cases h
    simp at hlin
  | linear a wn bn =>
    refine ⟨a, wn, bn, rfl, ?_⟩
    cases ha : nodes[a]? with
    | none => simp [ievalOp, ha] at h
    | some na =>
      cases hW : List.lookup wn w with
      | none => simp [ievalOp, ha, hW] at h
      | some W' =>
        cases bn with
        | none =>
          simp only [ievalOp, ha, hW, Option.map_eq_some_iff] at h
          obtain ⟨v, -, rfl⟩ := h
          simp only [Option.some.injEq, Prod.mk.injEq] at hlin
          rw [hlin.2.1]
        | some bn =>
          cases hb : List.lookup bn w with
          | none => simp [ievalOp, ha, hW, hb] at h
          | some bb =>
            simp only [ievalOp, ha, hW, hb, Option.map_eq_some_iff] at h
            obtain ⟨v, -, rfl⟩ := h
            simp only [Option.some.injEq, Prod.mk.injEq] at hlin
            rw [hlin.2.1]
  | sum a d =>
    cases ha : nodes[a]? with
    | none => simp [ievalOp, ha] at h
    | some na =>
      simp only [ievalOp, ha, Option.map_eq_some_iff] at h
      obtain ⟨v, -, rfl⟩ := h
      simp at hlin
  | add a c =>
    cases ha : nodes[a]? with
    | none => simp [ievalOp, ha] at h
    | some na =>
      cases hc : nodes[c]? with
      | none => simp [ievalOp, ha, hc] at h
      | some nc =>
        simp only [ievalOp, ha, hc, Option.map_eq_some_iff] at h
        obtain ⟨v, -, rfl⟩ := h
        simp at hlin
  | _ => simp [ievalOp] at h

/-- The weight a node records is the weight its operation names. -/
theorem ievalOps_lin {g : Graph} {w : Weights ℚ} {box : Box} :
    ∀ (ops : List Op) (acc nodes : Array INode), ievalOps g w box ops acc = some nodes →
      ∀ k n arg W b, nodes[k]? = some n → n.lin = some (arg, W, b) →
        acc[k]? = some n ∨ ∃ a wn bn, acc.size ≤ k ∧ ops[k - acc.size]? = some (.linear a wn bn) ∧
          List.lookup wn w = some W
  | [], acc, nodes, h, k, n, arg, W, b, hk, _ => by
    simp only [ievalOps, Option.some.injEq] at h
    subst h
    exact Or.inl hk
  | op :: ops, acc, nodes, h, k, n, arg, W, b, hk, hlin => by
    simp only [ievalOps] at h
    cases hn : ievalOp g w box acc op with
    | none => simp [hn] at h
    | some n' =>
      simp only [hn] at h
      rcases ievalOps_lin ops (acc.push n') nodes h k n arg W b hk hlin with h1 | h1
      · rw [Array.getElem?_push] at h1
        split_ifs at h1 with hka
        · simp only [Option.some.injEq] at h1
          subst h1
          obtain ⟨a, wn, bn, rfl, hW⟩ := ievalOp_lin hn hlin
          exact Or.inr ⟨a, wn, bn, by omega, by simp [hka], hW⟩
        · exact Or.inl h1
      · obtain ⟨a, wn, bn, hle, hop, hW⟩ := h1
        simp only [Array.size_push] at hle hop
        refine Or.inr ⟨a, wn, bn, by omega, ?_, hW⟩
        rw [show k - acc.size = (k - (acc.size + 1)) + 1 by omega, List.getElem?_cons_succ]
        exact hop

/-! ## The margins -/

theorem vecGet_toList (t : Tensor ℚ) (i : Nat) : vecGet t.data.toList i = t.get i := by
  simp [vecGet, Tensor.get, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem toList_getElem (t : Tensor ℚ) (j : Nat) (hj : j < t.data.toList.length) :
    t.data.toList[j] = t.get j := by
  rw [← vecGet_toList]
  simp [vecGet, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

theorem allPosExcept_spec {m : List ℚ} {l : Nat} (h : allPosExcept m l = true) :
    ∀ j (hj : j < m.length), j ≠ l → 0 < m[j] := by
  intro j hj hne
  unfold allPosExcept at h
  rw [List.all_eq_true] at h
  have hmem : (j, m[j]) ∈ (List.range m.length).zip m := by
    rw [List.mem_iff_getElem]
    exact ⟨j, by simp [hj], by simp [List.getElem_zip, List.getElem_range]⟩
  have := h _ hmem
  simpa [hne] using this

theorem strictMaxAt_of {v : List ℚ} {l : Nat} (hl : l < v.length)
    (h : ∀ j (hj : j < v.length), j ≠ l → v[j] < vecGet v l) : strictMaxAt v l = true := by
  simp only [strictMaxAt, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨hl, ?_⟩
  unfold allPosExcept marginsAt
  rw [List.all_eq_true]
  intro p hp
  obtain ⟨k, hk, hkp⟩ := List.mem_iff_getElem.mp hp
  simp only [List.length_zip, List.length_range, List.length_map, min_self] at hk
  simp only [List.getElem_zip, List.getElem_range, List.getElem_map] at hkp
  subst hkp
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
  by_cases hkl : k = l
  · exact Or.inl hkl
  · exact Or.inr (sub_pos.mpr (h k hk hkl))

theorem pre_eq_one {pre : List Nat} {inn V : Nat} (h : pre ++ [inn] = [1, V]) :
    pre = [1] ∧ inn = V := by
  rcases pre with _ | ⟨a, _ | ⟨c, rest⟩⟩
  · simp at h
  · simp only [List.cons_append, List.nil_append, List.cons.injEq, and_true] at h
    exact ⟨by rw [h.1], h.2⟩
  · simp at h

/-! ## Approximations -/

theorem getD_range_map {α : Type} (f : Nat → α) (d : α) {n k : Nat} (h : k < n) :
    ((Array.range n).map f).getD k d = f k := by
  simp [Array.getD_eq_getD_getElem?, h]

theorem getD_map_of_lt {α β : Type} (a : Array α) (f : α → β) (da : α) (db : β) {k : Nat}
    (h : k < a.size) : (a.map f).getD k db = f (a.getD k da) := by
  simp [Array.getD_eq_getD_getElem?, h]

theorem rowBounds_size (f : ApproxForm) (inn o l lo hi : Nat) :
    (f.rowBounds inn o l lo hi).size = o := by
  cases f <;> simp [ApproxForm.rowBounds]

/-- The approximation's bounds hold for its matrix `P`. -/
theorem rowBounds_le (f : ApproxForm) (inn o l j lo hi t : Nat) (hj : j < o) (h1 : lo ≤ t)
    (h2 : t ≤ hi) : (f.rowBounds inn o l lo hi).getD j 0 ≤ f.entry inn l t - f.entry inn j t := by
  cases f with
  | dense P =>
    simp only [ApproxForm.rowBounds, ApproxForm.entry, getD_range_map _ _ hj]
    exact rangeMin_le (fun t => P.get (l * inn + t) - P.get (j * inn + t)) lo hi t h1 h2
  | lowRank F G =>
    simp only [ApproxForm.rowBounds, ApproxForm.entry, getD_range_map _ _ hj]
    rw [← sum_map_sub']
    apply List.sum_le_sum
    intro k hk
    have hk' := List.mem_range.mp hk
    rw [getD_range_map _ _ hk', getD_range_map _ _ hk', ← sub_mul]
    split_ifs with hc
    · exact mul_le_mul_of_nonneg_left
        (rangeMin_le (fun t => G.get (k * inn + t)) lo hi t h1 h2) hc
    · exact mul_le_mul_of_nonpos_left
        (le_rangeMax (fun t => G.get (k * inn + t)) lo hi t h1 h2) (le_of_lt (not_le.mp hc))

/-- `a.eps` bounds the approximation's error at every entry of `a.W`. -/
def ApproxErrOk (a : Approx) : Prop :=
  ∀ o < a.W.shape.getD 0 0, ∀ t < a.W.shape.getD 1 0,
    |a.W.get (o * a.W.shape.getD 1 0 + t) - a.form.entry (a.W.shape.getD 1 0) o t| ≤ a.eps

/-- With an approximation of `W` whose error is at most `eps`, the bounds of
    one position hold for the differences of `W`'s columns at every token of
    its range. -/
theorem approxTerm_le {W : Tensor ℚ} {inn o l j : Nat} {a : Approx} (hWa : a.W = W)
    (hW : W.shape = [o, inn]) (herr : ApproxErrOk a) (hl : l < o) (hj : j < o) {r : Range}
    {t : Nat} (h1 : r.lo ≤ t) (h2 : t ≤ r.hi) (ht : t < inn) :
    (approxTerm W inn o l a r).getD j 0 ≤ W.get (l * inn + t) - W.get (j * inn + t) := by
  unfold approxTerm
  split_ifs with hr
  · rw [getD_range_map _ _ hj, show t = r.lo by omega]
  · rw [getD_map_of_lt _ _ 0 0 (by rw [rowBounds_size]; exact hj)]
    have hb := rowBounds_le a.form inn o l j r.lo r.hi t hj h1 h2
    have hs0 : a.W.shape.getD 0 0 = o := by rw [hWa, hW]; rfl
    have hs1 : a.W.shape.getD 1 0 = inn := by rw [hWa, hW]; rfl
    have he1 := herr l (by rw [hs0]; exact hl) t (by rw [hs1]; exact ht)
    have he2 := herr j (by rw [hs0]; exact hj) t (by rw [hs1]; exact ht)
    rw [hs1, hWa] at he1 he2
    have := abs_le.mp he1
    have := abs_le.mp he2
    linarith

/-- At a linear output, the margin bounds hold for the exact output. -/
theorem linearMargins_sound {P V : Nat} {box : Box} {x : Input} (hx : inBox box x = true)
    {arg : IVal} {ta W out : Tensor ℚ} {b : Option (Tensor ℚ)} {l : Nat} {m : List ℚ}
    {approx : Option Approx} {output : Nat}
    (happrox : ∀ a, approx = some a → a.of = output → a.W = W ∧ ApproxErrOk a)
    (harg : IRel P V box x arg ta) (hout : linearOp W b ta = some out)
    (hm : linearMargins box V W b l approx output arg = .ok m) (hl : l < m.length) :
    out.shape = [1, out.data.size] ∧ out.data.size = m.length ∧
      ∀ j (hj : j < m.length), m[j] ≤ out.get l - out.get j := by
  obtain ⟨o, inn, pre, hW, hWs, hta, htas, hb, rfl⟩ := linearOp_inv hout
  have hgo : W.shape.getD 0 0 = o := by rw [hW]; rfl
  have hgi : W.shape.getD 1 0 = inn := by rw [hW]; rfl
  cases arg with
  | oneHot s =>
    cases s with
    | false => simp [linearMargins] at hm
    | true =>
      have harg' := harg
      obtain ⟨-, hV, hshape, -, -⟩ := harg'
      obtain ⟨rfl, rfl⟩ := pre_eq_one (hta.symm.trans hshape)
      cases approx with
      | none =>
        simp only [linearMargins, hgo, Except.ok.injEq] at hm
        subst hm
        simp only [List.length_map, List.length_range] at hl ⊢
        refine ⟨by simp [shapeSize], by simp [shapeSize], ?_⟩
        intro j hj
        simp only [List.getElem_map, List.getElem_range, Tensor.get_range, shapeSize_one,
          one_mul, hl, hj, ite_eq_left, Nat.div_eq_of_lt hl, Nat.div_eq_of_lt hj,
          Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hj, zero_mul, zero_add]
        rw [summed_dot hx harg (fun i => W.get (l * inn + i)),
          summed_dot hx harg (fun i => W.get (j * inn + i))]
        have hsum := sum_box_le hx
          (fun r => rangeMin (fun t => W.get (l * inn + t) - W.get (j * inn + t)) r.lo r.hi)
          (fun t => W.get (l * inn + t) - W.get (j * inn + t))
          (fun r t h1 h2 =>
            rangeMin_le (fun t => W.get (l * inn + t) - W.get (j * inn + t)) _ _ _ h1 h2)
        rw [sum_map_sub'] at hsum
        linarith
      | some a =>
        simp only [linearMargins] at hm
        split_ifs at hm with hof
        obtain ⟨hWa, herr⟩ := happrox a rfl hof
        simp only [Except.ok.injEq] at hm
        subst hm
        simp only [approxMargins, hgo, List.length_map, List.length_range] at hl ⊢
        refine ⟨by simp [shapeSize], by simp [shapeSize], ?_⟩
        intro j hj
        simp only [List.getElem_map, List.getElem_range, Tensor.get_range, shapeSize_one,
          one_mul, hl, hj, ite_eq_left, Nat.div_eq_of_lt hl, Nat.div_eq_of_lt hj,
          Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hj, zero_mul, zero_add, List.map_map,
          Function.comp_def]
        rw [summed_dot hx harg (fun i => W.get (l * inn + i)),
          summed_dot hx harg (fun i => W.get (j * inn + i))]
        have hsum := sum_box_le' hx (fun r => (approxTerm W inn o l a r).getD j 0)
          (fun t => W.get (l * inn + t) - W.get (j * inn + t))
          (fun r hr t h1 h2 =>
            approxTerm_le hWa hW herr hl hj h1 h2 (lt_of_le_of_lt h2 (hV r hr)))
        rw [sum_map_sub'] at hsum
        linarith
  | bounds lo hi =>
    obtain ⟨hs, -, -, -, hbd⟩ := harg
    simp only [linearMargins, hgo, hgi] at hm
    split_ifs at hm with hlo
    simp only [beq_iff_eq] at hlo
    obtain ⟨rfl, -⟩ := pre_eq_one (hta.symm.trans (hs.trans hlo))
    simp only [Except.ok.injEq] at hm
    subst hm
    simp only [List.length_map, List.length_range] at hl ⊢
    refine ⟨by simp [shapeSize], by simp [shapeSize], ?_⟩
    intro j hj
    simp only [List.getElem_map, List.getElem_range, Tensor.get_range, shapeSize_one, one_mul,
      hl, hj, ite_eq_left, Nat.div_eq_of_lt hl, Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hl,
      Nat.mod_eq_of_lt hj, zero_mul, zero_add]
    have hsum : ((List.range inn).map fun i =>
        min ((W.get (l * inn + i) - W.get (j * inn + i)) * lo.get i)
          ((W.get (l * inn + i) - W.get (j * inn + i)) * hi.get i)).sum ≤
        ((List.range inn).map fun i => W.get (l * inn + i) * ta.get i -
          W.get (j * inn + i) * ta.get i).sum := by
      apply List.sum_le_sum
      intro i _
      rw [← sub_mul]
      exact min_mul_le (hbd i).1 (hbd i).2
    rw [sum_map_sub'] at hsum
    linarith

/-- At an output that is not a linear map, the margin bounds hold for the
    exact output. -/
theorem valueMargins_sound {P V : Nat} {box : Box} {x : Input} {iv : IVal} {out : Tensor ℚ}
    {l : Nat} {m : List ℚ} (h : IRel P V box x iv out) (hm : valueMargins l iv = .ok m) :
    out.shape = [1, out.data.size] ∧ out.data.size = m.length ∧
      ∀ j (hj : j < m.length), m[j] ≤ out.get l - out.get j := by
  cases iv with
  | oneHot s => simp [valueMargins] at hm
  | bounds lo hi =>
    obtain ⟨hs, -, hsz, -, hbd⟩ := h
    simp only [valueMargins] at hm
    split_ifs at hm with hlo
    simp only [beq_iff_eq] at hlo
    simp only [Except.ok.injEq] at hm
    subst hm
    refine ⟨by rw [hs, hlo, hsz], by simp [hsz], ?_⟩
    intro j hj
    simp only [List.getElem_map, List.getElem_range]
    linarith [(hbd l).1, (hbd j).2]

/-- The single test passes for an output whose margins have positive lower
    bounds. -/
theorem singleOk_of_margins {g : Graph} {w : Weights ℚ} {task : Task} {x : Input}
    {out : Tensor ℚ} {l : Nat} {m : List ℚ} (heval : evalGraph g w x = some out)
    (hlab : task.label x = l) (hshape : out.shape = [1, out.data.size])
    (hsize : out.data.size = m.length) (hl : l < m.length)
    (hm : ∀ j (hj : j < m.length), m[j] ≤ out.get l - out.get j)
    (hpos : allPosExcept m l = true) : singleOk g w task x = true := by
  unfold singleOk
  rw [heval]
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨hshape, ?_⟩
  rw [hlab]
  apply strictMaxAt_of
  · simpa [hsize] using hl
  · intro j hj hne
    have hj' : j < m.length := by simpa [hsize] using hj
    have h1 := allPosExcept_spec hpos j hj' hne
    have h2 := hm j hj'
    rw [toList_getElem out j hj, vecGet_toList]
    linarith

/-- What the checker knows about an approximation it built for this
    network: it is of the linear map at position `a.of`, whose weight is
    `a.W`, and `a.eps` bounds its error. -/
def ApproxOk (g : Graph) (w : Weights ℚ) (a : Approx) : Prop :=
  (∃ arg wn bn, g.nodes[a.of]? = some (.linear arg wn bn) ∧ List.lookup wn w = some a.W) ∧
    ApproxErrOk a

/-- **interval_sound**: if the interval rule accepts a box, every input in
    the box passes the single test. With an approximation, for every
    approximation the checker builds. -/
theorem intervalLeaf_sound (g : Graph) (w : Weights ℚ) (task : Task) (box : Box)
    (approx : Option Approx) (happrox : ∀ a, approx = some a → ApproxOk g w a)
    (h : intervalLeaf g w task box approx = .ok true) (x : Input) (hx : inBox box x = true) :
    singleOk g w task x = true := by
  unfold intervalLeaf at h
  cases hl : task.constantLabel box with
  | none => simp [hl] at h
  | some l =>
    have hlab : task.label x = l := task.constantLabel_spec box l x hl hx
    simp only [hl] at h
    cases hn : ievalOps g w box g.nodes #[] with
    | none => simp [hn] at h
    | some nodes =>
      simp only [hn] at h
      cases ho : nodes[g.output]? with
      | none => simp [ho] at h
      | some node =>
        simp only [ho] at h
        obtain ⟨vals, hvals, hrel⟩ := ievalOps_sim hx g.nodes #[] #[] nodes
          ⟨rfl, fun k h1 => absurd h1 (by simp)⟩ hn
        obtain ⟨out, hout, hnr⟩ := hrel.get? ho
        have heval : evalGraph g w x = some out := by
          simp only [evalGraph, hvals]
          exact hout
        cases hlin : node.lin with
        | none =>
          simp only [hlin] at h
          cases hmg : valueMargins l node.val with
          | error e => simp [hmg] at h
          | ok m =>
            simp only [hmg] at h
            split_ifs at h with hlm
            obtain ⟨hs, hsz, hmo⟩ := valueMargins_sound hnr.1 hmg
            exact singleOk_of_margins heval hlab hs hsz hlm hmo (Except.ok.inj h)
        | some p =>
          obtain ⟨arg, W, b⟩ := p
          simp only [hlin] at h
          cases hmg : linearMargins box g.values W b l approx g.output arg with
          | error e => simp [hmg] at h
          | ok m =>
            simp only [hmg] at h
            split_ifs at h with hlm
            obtain ⟨ta, hta, hlinop⟩ := hnr.2 arg W b hlin
            -- the approximation is of the output map, whose weight is `W`
            have hW : ∀ a, approx = some a → a.of = g.output → a.W = W ∧ ApproxErrOk a := by
              intro a ha hof
              obtain ⟨⟨arg', wn, bn, hop, hwn⟩, herr⟩ := happrox a ha
              refine ⟨?_, herr⟩
              rcases ievalOps_lin g.nodes #[] nodes hn g.output node arg W b ho hlin with h1 | h1
              · simp at h1
              · obtain ⟨a', wn', bn', -, hop', hwn'⟩ := h1
                rw [hof] at hop
                simp only [Array.size_empty, Nat.sub_zero, hop, Option.some.injEq,
                  Op.linear.injEq] at hop'
                rw [← hop'.2.1, hwn] at hwn'
                exact Option.some.inj hwn'
            obtain ⟨hs, hsz, hmo⟩ := linearMargins_sound hx hW hta hlinop hmg hlm
            exact singleOk_of_margins heval hlab hs hsz hlm hmo (Except.ok.inj h)

end CompactCheck
