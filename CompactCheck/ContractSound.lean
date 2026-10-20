import Mathlib.Tactic.Ring
import CompactCheck.IntervalSound

/-!
# Soundness of the contract rule

`contractAll_sound`: if the contracted network gives the output `out` on an
input, so does the original network. So the contracted network answers no
more inputs correctly than the original one, and counting on it is safe.

The heart is associativity (`linearOp_compose`): applying `W1, b1` and then
`W2, b2` is applying `W2 W1` with bias `W2 b1 + b2`. The rest follows the
evaluation node by node: the contraction replaces one operation by another
that computes the same value, and leaves every other operation alone.
-/

namespace CompactCheck

/-! ## Products of weights -/

theorem matMul_inv {A B M : Tensor ℚ} (h : A.matMul B = some M) :
    ∃ m k n, A.shape = [m, k] ∧ B.shape = [k, n] ∧ A.data.size = m * k ∧ B.data.size = k * n ∧
      M = ⟨[m, n], (Array.range (m * n)).map fun j =>
        ((List.range k).map fun i => A.get (j / n * k + i) * B.get (i * n + j % n)).sum⟩ := by
  simp only [Tensor.matMul] at h
  split_ifs at h with hc
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨⟨hA, hB⟩, hAs⟩, hBs⟩ := hc
  exact ⟨_, _, _, hA, hB, hAs, hBs, (Option.some.inj h).symm⟩

theorem matVec_inv {A v c : Tensor ℚ} (h : A.matVec v = some c) :
    ∃ m k, A.shape = [m, k] ∧ v.shape = [k] ∧ A.data.size = m * k ∧ v.data.size = k ∧
      c = ⟨[m], (Array.range m).map fun o =>
        ((List.range k).map fun i => A.get (o * k + i) * v.get i).sum⟩ := by
  simp only [Tensor.matVec] at h
  split_ifs at h with hc
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨⟨hA, hv⟩, hAs⟩, hvs⟩ := hc
  exact ⟨_, _, hA, hv, hAs, hvs, (Option.some.inj h).symm⟩

theorem addOp_inv {a b c : Tensor ℚ} (h : addOp a b = some c) :
    a.shape = b.shape ∧ a.data.size = b.data.size ∧
      c = ⟨a.shape, (Array.range a.data.size).map fun j => a.get j + b.get j⟩ := by
  simp only [addOp] at h
  split_ifs at h with hc
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  exact ⟨hc.1, hc.2, (Option.some.inj h).symm⟩

theorem list_sum_mul (l : List ℚ) (a : ℚ) : l.sum * a = (l.map (· * a)).sum := by
  induction l with
  | nil => simp
  | cons b l ih => simp [add_mul, ih]

/-- What `composeLinear` computes: the product of the weights, and a bias
    whose entry `o` is `Σ_q W2[o, q] * b1[q] + b2[o]`. The composed bias fits
    exactly when `b2` does. -/
theorem composeLinear_inv {W1 W2 M : Tensor ℚ} {b1 b2 bM : Option (Tensor ℚ)}
    (h : composeLinear W1 b1 W2 b2 = some (M, bM)) (hb1 : biasFits b1 (W1.shape.getD 0 0)) :
    ∃ m k n, W2.shape = [m, k] ∧ W1.shape = [k, n] ∧ W2.data.size = m * k ∧
      W1.data.size = k * n ∧
      M = ⟨[m, n], (Array.range (m * n)).map fun j =>
        ((List.range k).map fun i => W2.get (j / n * k + i) * W1.get (i * n + j % n)).sum⟩ ∧
      (biasFits bM m ↔ biasFits b2 m) ∧
      ∀ o < m, biasAt bM o =
        ((List.range k).map fun q => W2.get (o * k + q) * biasAt b1 q).sum + biasAt b2 o := by
  simp only [composeLinear] at h
  cases hmm : W2.matMul W1 with
  | none => simp [hmm] at h
  | some M0 =>
    obtain ⟨m, k, n, hW2, hW1, hW2s, hW1s, rfl⟩ := matMul_inv hmm
    simp only [hmm] at h
    have hk : W1.shape.getD 0 0 = k := by rw [hW1]; rfl
    rw [hk] at hb1
    cases b1 with
    | none =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨m, k, n, hW2, hW1, hW2s, hW1s, rfl, Iff.rfl, fun o _ => ?_⟩
      simp [biasAt]
    | some v1 =>
      obtain ⟨hv1s, hv1z⟩ := hb1
      cases hmv : W2.matVec v1 with
      | none => simp [hmv] at h
      | some c =>
        obtain ⟨m', k', hW2', hv1', hW2s', hv1s', rfl⟩ := matVec_inv hmv
        obtain ⟨hm, hk2⟩ : m = m' ∧ k = k' := by
          rw [hW2] at hW2'
          simp only [List.cons.injEq, and_true] at hW2'
          exact hW2'
        subst hm
        subst hk2
        cases b2 with
        | none =>
          simp only [hmv, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨m, k, n, hW2, hW1, hW2s, hW1s, rfl, ?_, fun o ho => ?_⟩
          · simp [biasFits]
          · simp [biasAt, Tensor.get_range, ho]
        | some v2 =>
          cases had : addOp ⟨[m], (Array.range m).map fun o =>
              ((List.range k).map fun i => W2.get (o * k + i) * v1.get i).sum⟩ v2 with
          | none => simp [hmv, had] at h
          | some d =>
            simp only [hmv, had, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨hcs, hcz, rfl⟩ := addOp_inv had
            simp only [Array.size_map, Array.size_range] at hcs hcz ⊢
            refine ⟨m, k, n, hW2, hW1, hW2s, hW1s, rfl, ?_, fun o ho => ?_⟩
            · simp [biasFits, ← hcs, ← hcz]
            · simp [biasAt, Tensor.get_range, ho]

/-- A linear map whose bias does not fit gives nothing. -/
theorem linearOp_none_of_bias {W t : Tensor ℚ} {b : Option (Tensor ℚ)} {m k : Nat}
    (hW : W.shape = [m, k]) (hb : ¬biasFits b m) : linearOp W b t = none := by
  cases h : linearOp W b t with
  | none => rfl
  | some v =>
    obtain ⟨o, inn, pre, hW', -, -, -, hbo, -⟩ := linearOp_inv h
    rw [hW] at hW'
    simp only [List.cons.injEq, and_true] at hW'
    exact absurd (hW'.1 ▸ hbo) hb

/-- **Associativity**: the second map applied to the first map's output is
    the composed map applied to the input. -/
theorem linearOp_compose {W1 W2 t u M : Tensor ℚ} {b1 b2 bM : Option (Tensor ℚ)}
    (hu : linearOp W1 b1 t = some u) (hc : composeLinear W1 b1 W2 b2 = some (M, bM)) :
    linearOp W2 b2 u = linearOp M bM t := by
  obtain ⟨o1, i1, pre, hW1, hW1s, ht, hts, hb1, rfl⟩ := linearOp_inv hu
  have hgo : W1.shape.getD 0 0 = o1 := by rw [hW1]; rfl
  obtain ⟨m, k, n, hW2, hW1', hW2s, -, rfl, hbM, hbMv⟩ := composeLinear_inv hc (hgo ▸ hb1)
  have hkn : o1 = k ∧ i1 = n := by
    rw [hW1] at hW1'
    simpa using hW1'
  obtain ⟨hk, hn⟩ := hkn
  subst hk
  subst hn
  by_cases hb2 : biasFits b2 m
  · rw [linearOp_some hW2 hW2s rfl (by simp) hb2, linearOp_some rfl (by simp) ht hts (hbM.mpr hb2)]
    congr 2
    apply Array.map_congr_left
    intro j hj
    rw [Array.mem_range] at hj
    have hm : 0 < m := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hj
    have hp : j / m < shapeSize pre := (Nat.div_lt_iff_lt_mul hm).mpr hj
    have ho : j % m < m := Nat.mod_lt j hm
    -- the first map's output, entry by entry
    have hu' : ∀ q < o1, Tensor.get ⟨pre ++ [o1], (Array.range (shapeSize pre * o1)).map fun j =>
        ((List.range i1).map fun i => W1.get (j % o1 * i1 + i) * t.get (j / o1 * i1 + i)).sum +
          biasAt b1 (j % o1)⟩ (j / m * o1 + q) =
        ((List.range i1).map fun i => W1.get (q * i1 + i) * t.get (j / m * i1 + i)).sum +
          biasAt b1 q := by
      intro q hq
      rw [Tensor.get_range, ite_eq_left (idx_lt hp hq), idx_mod hq, idx_div hq]
    -- the product's entries
    have hM : ∀ i < i1, Tensor.get ⟨[m, i1], (Array.range (m * i1)).map fun j =>
        ((List.range o1).map fun q => W2.get (j / i1 * o1 + q) * W1.get (q * i1 + j % i1)).sum⟩
        (j % m * i1 + i) =
        ((List.range o1).map fun q => W2.get (j % m * o1 + q) * W1.get (q * i1 + i)).sum := by
      intro i hi
      rw [Tensor.get_range, ite_eq_left (idx_lt ho hi), idx_mod hi, idx_div hi]
    rw [hbMv _ ho]
    have lhs : ((List.range o1).map fun q => W2.get (j % m * o1 + q) *
        Tensor.get ⟨pre ++ [o1], (Array.range (shapeSize pre * o1)).map fun j =>
          ((List.range i1).map fun i => W1.get (j % o1 * i1 + i) * t.get (j / o1 * i1 + i)).sum +
            biasAt b1 (j % o1)⟩ (j / m * o1 + q)).sum =
        ((List.range o1).map fun q => ((List.range i1).map fun i =>
          W2.get (j % m * o1 + q) * W1.get (q * i1 + i) * t.get (j / m * i1 + i)).sum).sum +
        ((List.range o1).map fun q => W2.get (j % m * o1 + q) * biasAt b1 q).sum := by
      rw [← List.sum_map_add]
      apply congrArg List.sum
      apply List.map_congr_left
      intro q hq
      rw [hu' q (List.mem_range.mp hq), mul_add, mul_list_sum, List.map_map]
      congr 2
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply]
      ring
    have rhs : ((List.range i1).map fun i =>
        Tensor.get ⟨[m, i1], (Array.range (m * i1)).map fun j =>
          ((List.range o1).map fun q => W2.get (j / i1 * o1 + q) * W1.get (q * i1 + j % i1)).sum⟩
          (j % m * i1 + i) * t.get (j / m * i1 + i)).sum =
        ((List.range o1).map fun q => ((List.range i1).map fun i =>
          W2.get (j % m * o1 + q) * W1.get (q * i1 + i) * t.get (j / m * i1 + i)).sum).sum := by
      rw [sum_range_swap]
      apply congrArg List.sum
      apply List.map_congr_left
      intro i hi
      rw [hM i (List.mem_range.mp hi), list_sum_mul, List.map_map]
      rfl
    rw [lhs, rhs]
    ring
  · rw [linearOp_none_of_bias hW2 hb2, linearOp_none_of_bias rfl (fun h => hb2 (hbM.mp h))]

/-! ## Evaluating a graph, operation by operation -/

/-- `evalOp` on a linear map, with the bias looked up by `lookupBias`. -/
theorem evalOp_linear (g : Graph) (w : Weights ℚ) (x : Input) (arr : Array (Tensor ℚ)) (a : Nat)
    (wn : String) (bn : Option String) :
    evalOp g w x arr (.linear a wn bn) =
      match arr[a]?, List.lookup wn w, lookupBias w bn with
      | some t, some W, some b => linearOp W b t
      | _, _, _ => none := by
  cases bn with
  | none =>
    simp only [evalOp, lookupBias]
    cases arr[a]? <;> cases List.lookup wn w <;> rfl
  | some n =>
    simp only [evalOp, lookupBias]
    cases arr[a]? <;> cases List.lookup wn w <;> cases List.lookup n w <;> rfl

/-- An operation that gives a value reads only earlier values. -/
theorem evalOp_args_lt {g : Graph} {w : Weights ℚ} {x : Input} {arr : Array (Tensor ℚ)}
    {op : Op} {v : Tensor ℚ} (h : evalOp g w x arr op = some v) : ∀ a ∈ op.args, a < arr.size := by
  intro a ha
  by_contra hlt
  have hnone : arr[a]? = none := Array.getElem?_eq_none (by omega)
  cases op with
  | input => simp [Op.args] at ha
  | linear b wn bn =>
    simp only [Op.args, List.mem_singleton] at ha
    subst ha
    rw [evalOp_linear, hnone] at h
    simp at h
  | sum b d =>
    simp only [Op.args, List.mem_singleton] at ha
    subst ha
    simp [evalOp, hnone] at h
  | add b c =>
    simp only [Op.args, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · simp [evalOp, hnone] at h
    · cases hb : arr[b]? <;> simp [evalOp, hnone, hb] at h
  | _ => simp [evalOp] at h

/-- An operation reads only the values of its arguments. -/
theorem evalOp_congr {g : Graph} {w : Weights ℚ} {x : Input} {arr1 arr2 : Array (Tensor ℚ)}
    {op : Op} (h : ∀ a ∈ op.args, arr1[a]? = arr2[a]?) :
    evalOp g w x arr1 op = evalOp g w x arr2 op := by
  cases op with
  | input => rfl
  | linear a wn bn => simp only [evalOp, h a (by simp [Op.args])]
  | sum a d => simp only [evalOp, h a (by simp [Op.args])]
  | add a b => simp only [evalOp, h a (by simp [Op.args]), h b (by simp [Op.args])]
  | _ => simp [evalOp]

/-- The values `vals` are the evaluation of `ops` after the values `acc`
    exactly when each operation reads earlier values and gives its value. -/
theorem evalOps_spec (g : Graph) (w : Weights ℚ) (x : Input) :
    ∀ (ops : List Op) (acc vals : Array (Tensor ℚ)),
      evalOps g w x ops acc = some vals ↔
        vals.size = acc.size + ops.length ∧ (∀ i < acc.size, vals[i]? = acc[i]?) ∧
          ∀ j (hj : j < ops.length), (∀ a ∈ ops[j].args, a < acc.size + j) ∧
            evalOp g w x vals ops[j] = vals[acc.size + j]?
  | [], acc, vals => by
    simp only [evalOps, Option.some.injEq, List.length_nil, Nat.add_zero]
    constructor
    · rintro rfl
      exact ⟨rfl, fun _ _ => rfl, fun j hj => absurd hj (by simp)⟩
    · rintro ⟨hs, hag, -⟩
      apply Array.ext_getElem?
      intro i
      by_cases hi : i < acc.size
      · exact (hag i hi).symm
      · rw [Array.getElem?_eq_none (by omega), Array.getElem?_eq_none (by omega)]
  | op :: ops, acc, vals => by
    rw [evalOps]
    constructor
    · intro h
      cases hv : evalOp g w x acc op with
      | none => simp [hv] at h
      | some v =>
        simp only [hv] at h
        obtain ⟨hs, hag, hev⟩ := (evalOps_spec g w x ops (acc.push v) vals).mp h
        simp only [Array.size_push] at hs hag hev
        have hag' : ∀ i < acc.size, vals[i]? = acc[i]? := by
          intro i hi
          rw [hag i (by omega), Array.getElem?_push, ite_eq_right (by omega)]
        have hv' : vals[acc.size]? = some v := by
          rw [hag acc.size (by omega), Array.getElem?_push, ite_eq_left rfl]
        refine ⟨by simp only [List.length_cons]; omega, hag', ?_⟩
        intro j hj
        cases j with
        | zero =>
          have hlt := evalOp_args_lt hv
          refine ⟨fun a ha => by simpa using hlt a ha, ?_⟩
          simp only [List.getElem_cons_zero, Nat.add_zero]
          rw [evalOp_congr (fun a ha => hag' a (hlt a ha)), hv, hv']
        | succ j =>
          simp only [List.length_cons] at hj
          obtain ⟨h1, h2⟩ := hev j (by omega)
          simp only [List.getElem_cons_succ]
          refine ⟨fun a ha => by have := h1 a ha; omega, ?_⟩
          rw [show acc.size + (j + 1) = acc.size + 1 + j by omega]
          exact h2
    · rintro ⟨hs, hag, hev⟩
      obtain ⟨hlt0, hev0⟩ := hev 0 (by simp)
      simp only [List.getElem_cons_zero, Nat.add_zero] at hlt0 hev0
      have hsz : acc.size < vals.size := by simp only [List.length_cons] at hs; omega
      have hv : evalOp g w x acc op = some vals[acc.size] := by
        rw [← evalOp_congr (fun a ha => hag a (hlt0 a ha)), hev0]
        exact Array.getElem?_eq_getElem hsz
      rw [hv]
      apply (evalOps_spec g w x ops (acc.push vals[acc.size]) vals).mpr
      refine ⟨by simp only [Array.size_push, List.length_cons] at hs ⊢; omega, ?_, ?_⟩
      · intro i hi
        simp only [Array.size_push] at hi
        rw [Array.getElem?_push]
        split_ifs with h
        · subst h
          exact Array.getElem?_eq_getElem hsz
        · exact hag i (by omega)
      · intro j hj
        obtain ⟨h1, h2⟩ := hev (j + 1) (by simp; omega)
        simp only [List.getElem_cons_succ] at h1 h2
        simp only [Array.size_push]
        refine ⟨fun a ha => by have := h1 a ha; omega, ?_⟩
        rw [show acc.size + 1 + j = acc.size + (j + 1) by omega]
        exact h2

/-! ## Following a contraction chain -/

/-- One step of `composeChain`. -/
theorem composeChain_cons {g : Graph} {w : Weights ℚ} {removed : List Nat} {prev i : Nat}
    {M M' : Tensor ℚ} {bM bM' : Option (Tensor ℚ)} {rest : List Nat} {last : Nat}
    (h : composeChain g w removed prev M bM (i :: rest) = .ok (M', bM', last)) :
    ∃ wn bn W b M1 bM1, g.nodes[i]? = some (.linear prev wn bn) ∧ prev < i ∧
      List.lookup wn w = some W ∧ lookupBias w bn = some b ∧
      composeLinear M bM W b = some (M1, bM1) ∧
      composeChain g w removed i M1 bM1 rest = .ok (M', bM', last) := by
  simp only [composeChain] at h
  cases hi : g.nodes[i]? with
  | none => simp [hi] at h
  | some op =>
    cases op with
    | linear a wn bn =>
      simp only [hi] at h
      split_ifs at h with hc
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨⟨ha, hlt⟩, -⟩, -⟩, -⟩ := hc
      subst ha
      cases hW : List.lookup wn w with
      | none => simp [hW] at h
      | some W =>
        cases hb : lookupBias w bn with
        | none => simp [hW, hb] at h
        | some b =>
          simp only [hW, hb] at h
          cases hcl : composeLinear M bM W b with
          | none => simp [hcl] at h
          | some p =>
            obtain ⟨M1, bM1⟩ := p
            simp only [hcl] at h
            exact ⟨wn, bn, W, b, M1, bM1, rfl, hlt, hW, hb, hcl, h⟩
    | _ => simp [hi] at h

/-- A chain with at least one more map ends after `prev`, at a map of the
    graph. -/
theorem composeChain_lt {g : Graph} {w : Weights ℚ} {removed : List Nat} {M' : Tensor ℚ}
    {bM' : Option (Tensor ℚ)} {last : Nat} :
    ∀ {rest : List Nat} {prev : Nat} {M : Tensor ℚ} {bM : Option (Tensor ℚ)},
      composeChain g w removed prev M bM rest = .ok (M', bM', last) → rest ≠ [] →
        prev < last ∧ last < g.nodes.length
  | [], _, _, _, _, hne => absurd rfl hne
  | i :: rest, prev, M, bM, h, _ => by
    obtain ⟨wn, bn, W, b, M1, bM1, hi, hlt, -, -, -, h'⟩ := composeChain_cons h
    by_cases hrest : rest = []
    · subst hrest
      simp only [composeChain, Except.ok.injEq, Prod.mk.injEq] at h'
      obtain ⟨-, -, rfl⟩ := h'
      exact ⟨hlt, (List.getElem?_eq_some_iff.mp hi).1⟩
    · obtain ⟨h1, h2⟩ := composeChain_lt h' hrest
      exact ⟨lt_trans hlt h1, h2⟩

/-- Along a chain, the original network's value at the chain's last map is
    the composition of the whole chain applied to `t`, provided the value at
    `prev` is the composition so far applied to `t`, and the original network
    gives the values `vals` at every operation but the last map. -/
theorem composeChain_value {g : Graph} {w : Weights ℚ} {removed : List Nat} {x : Input}
    {vals : Array (Tensor ℚ)} {t M' : Tensor ℚ} {bM' : Option (Tensor ℚ)} {last : Nat}
    (hsize : vals.size = g.nodes.length)
    (hold : ∀ j (hj : j < g.nodes.length), j ≠ last → evalOp g w x vals g.nodes[j] = vals[j]?) :
    ∀ (rest : List Nat) (prev : Nat) (M : Tensor ℚ) (bM : Option (Tensor ℚ)),
      composeChain g w removed prev M bM rest = .ok (M', bM', last) → rest ≠ [] →
        prev < vals.size → vals[prev]? = linearOp M bM t →
          ∃ hl : last < g.nodes.length, (∀ a ∈ g.nodes[last].args, a < last) ∧
            evalOp g w x vals g.nodes[last] = linearOp M' bM' t
  | [], _, _, _, _, hne, _, _ => absurd rfl hne
  | i :: rest, prev, M, bM, h, _, hprev, hval => by
    obtain ⟨wn, bn, W, b, M1, bM1, hi, hlt, hW, hb, hcl, h'⟩ := composeChain_cons h
    have hil : i < g.nodes.length := (List.getElem?_eq_some_iff.mp hi).1
    have hnode : g.nodes[i] = .linear prev wn bn := (List.getElem?_eq_some_iff.mp hi).2
    -- the value of the map at `i`, from the value at `prev`
    obtain ⟨u, hu⟩ : ∃ u, vals[prev]? = some u := ⟨vals[prev], Array.getElem?_eq_getElem hprev⟩
    have hstep : evalOp g w x vals (.linear prev wn bn) = linearOp M1 bM1 t := by
      rw [evalOp_linear, hu, hW, hb]
      exact linearOp_compose (hval.symm.trans hu) hcl
    by_cases hrest : rest = []
    · subst hrest
      simp only [composeChain, Except.ok.injEq, Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl, rfl⟩ := h'
      refine ⟨hil, ?_, by rw [hnode]; exact hstep⟩
      rw [hnode]
      simpa [Op.args] using hlt
    · have hlast := (composeChain_lt h' hrest).1
      have hvi : vals[i]? = linearOp M1 bM1 t := by
        rw [← hold i hil (Nat.ne_of_lt hlast), hnode, hstep]
      exact composeChain_value hsize hold rest i M1 bM1 h' hrest (by omega) hvi

/-! ## A contraction keeps what the network computes -/

/-- What a successful contraction did. -/
theorem contractOne_inv {g : Graph} {w : Weights ℚ} {removed : List Nat} {step : Nat}
    {chain : List Nat} {g' : Graph} {w' : Weights ℚ} {removed' : List Nat}
    (h : contractOne g w removed step chain = .ok (g', w', removed')) :
    ∃ i rest a wn bn W b nameW nameB M bM last,
      rest ≠ [] ∧ g.nodes[i]? = some (.linear a wn bn) ∧ List.lookup wn w = some W ∧
      lookupBias w bn = some b ∧ usesName g.nodes nameW = false ∧
      usesName g.nodes nameB = false ∧
      composeChain g w removed i W b rest = .ok (M, bM, last) ∧
      g' = { g with nodes := g.nodes.set last (.linear a nameW (bM.map fun _ => nameB)) } ∧
      (∀ n, n ≠ nameW → n ≠ nameB → List.lookup n w' = List.lookup n w) ∧
      List.lookup nameW w' = some M ∧ lookupBias w' (bM.map fun _ => nameB) = some bM := by
  match chain, h with
  | [], h => simp [contractOne] at h
  | [_], h => simp [contractOne] at h
  | i :: j :: rest, h =>
    simp only [contractOne] at h
    cases hi : g.nodes[i]? with
    | none => simp [hi] at h
    | some op =>
      cases op with
      | linear a wn bn =>
        simp only [hi] at h
        split_ifs at h with hrm
        cases hW : List.lookup wn w with
        | none => simp [hW] at h
        | some W =>
          cases hb : lookupBias w bn with
          | none => simp [hW, hb] at h
          | some b =>
            simp only [hW, hb, contractOne.finish] at h
            split_ifs at h with hnames
            simp only [Bool.or_eq_true, beq_iff_eq, not_or, Bool.not_eq_true] at hnames
            obtain ⟨⟨hne, huW⟩, huB⟩ := hnames
            cases hcc : composeChain g w removed i W b (j :: rest) with
            | error e => simp [hcc] at h
            | ok r =>
              obtain ⟨M, bM, last⟩ := r
              simp only [hcc, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, -⟩ := h
              refine ⟨i, j :: rest, a, wn, bn, W, b, _, _, M, bM, last, List.cons_ne_nil _ _,
                hi, hW, hb, huW, huB, hcc, rfl, ?_, ?_, ?_⟩
              · intro n h1 h2
                cases bM <;> simp only [List.lookup_cons, beq_false_of_ne h1, beq_false_of_ne h2]
              · cases bM <;> simp only [List.lookup_cons, beq_self_eq_true]
              · cases bM with
                | none => rfl
                | some bv =>
                  simp only [lookupBias, Option.map_some, List.lookup_cons,
                    beq_false_of_ne (Ne.symm hne), beq_self_eq_true]
      | _ => simp [hi] at h

/-- An operation of the original graph computes the same in the contracted
    graph: it does not use the new weights. -/
theorem evalOp_fresh {g g' : Graph} {w w' : Weights ℚ} {x : Input} {arr : Array (Tensor ℚ)}
    {nameW nameB : String} (hpos : g'.positions = g.positions) (hval : g'.values = g.values)
    (hlook : ∀ n, n ≠ nameW → n ≠ nameB → List.lookup n w' = List.lookup n w)
    (huW : usesName g.nodes nameW = false) (huB : usesName g.nodes nameB = false)
    {op : Op} (hop : op ∈ g.nodes) : evalOp g' w' x arr op = evalOp g w x arr op := by
  have hW := List.any_eq_false.mp huW op hop
  have hB := List.any_eq_false.mp huB op hop
  cases op with
  | input => simp only [evalOp, hpos, hval]
  | linear a wn bn =>
    simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hW hB
    rw [evalOp_linear, evalOp_linear, hlook wn hW.1 hB.1]
    cases bn with
    | none => rfl
    | some n =>
      have h1 : n ≠ nameW := fun h => hW.2 (by rw [h])
      have h2 : n ≠ nameB := fun h => hB.2 (by rw [h])
      simp only [lookupBias, hlook n h1 h2]
  | sum a d => rfl
  | add a b => rfl
  | _ => simp [evalOp]

/-- **contract_sound**, one contraction: whatever the contracted network
    outputs on an input, the original network outputs too. -/
theorem contractOne_sound {g : Graph} {w : Weights ℚ} {removed : List Nat} {step : Nat}
    {chain : List Nat} {g' : Graph} {w' : Weights ℚ} {removed' : List Nat}
    (h : contractOne g w removed step chain = .ok (g', w', removed')) (x : Input)
    (out : Tensor ℚ) (hout : evalGraph g' w' x = some out) : evalGraph g w x = some out := by
  obtain ⟨i, rest, a, wn, bn, W, b, nameW, nameB, M, bM, last, hrest, hi, hW, hb, huW, huB, hcc,
    rfl, hlook, hlW, hlB⟩ := contractOne_inv h
  obtain ⟨hil, hlast⟩ := composeChain_lt hcc hrest
  have hi' : i < g.nodes.length := (List.getElem?_eq_some_iff.mp hi).1
  have hnode : g.nodes[i] = .linear a wn bn := (List.getElem?_eq_some_iff.mp hi).2
  unfold evalGraph at hout ⊢
  cases hv : evalOps { g with nodes := g.nodes.set last (.linear a nameW (bM.map fun _ => nameB)) }
      w' x (g.nodes.set last (.linear a nameW (bM.map fun _ => nameB))) #[] with
  | none => simp [hv] at hout
  | some vals =>
    simp only [hv] at hout
    obtain ⟨hs, -, hev⟩ := (evalOps_spec _ w' x _ #[] vals).mp hv
    simp only [List.length_set, Array.size_empty, Nat.zero_add] at hs hev
    -- every operation but the chain's last map computes as before
    have hold : ∀ j (hj : j < g.nodes.length), j ≠ last →
        (∀ c ∈ g.nodes[j].args, c < j) ∧ evalOp g w x vals g.nodes[j] = vals[j]? := by
      intro j hj hne
      obtain ⟨h1, h2⟩ := hev j (by simpa using hj)
      rw [List.getElem_set_ne (Ne.symm hne)] at h1 h2
      refine ⟨h1, ?_⟩
      rw [← evalOp_fresh rfl rfl hlook huW huB (List.getElem_mem hj)]
      exact h2
    -- the value the chain starts from
    obtain ⟨ha, -⟩ := hev last (by simpa using hlast)
    simp only [List.getElem_set_self, Op.args, List.mem_singleton, forall_eq] at ha
    have hat : a < vals.size := by omega
    obtain ⟨t, ht⟩ : ∃ t, vals[a]? = some t := ⟨vals[a], Array.getElem?_eq_getElem hat⟩
    -- the value at the chain's first map
    have hfirst : vals[i]? = linearOp W b t := by
      rw [← (hold i hi' (Nat.ne_of_lt hil)).2, hnode, evalOp_linear, ht, hW, hb]
    obtain ⟨hl, hargs, hval⟩ := composeChain_value hs (fun j hj hne => (hold j hj hne).2) rest i W b
      hcc hrest (by omega) hfirst
    -- the new map at `last` computes the same value
    have hnew : vals[last]? = linearOp M bM t := by
      obtain ⟨-, h2⟩ := hev last (by simpa using hlast)
      rw [List.getElem_set_self, evalOp_linear, ht, hlW, hlB] at h2
      exact h2.symm
    have horig : evalOps g w x g.nodes #[] = some vals := by
      apply (evalOps_spec g w x g.nodes #[] vals).mpr
      refine ⟨by simpa using hs, fun _ h => absurd h (by simp), ?_⟩
      intro j hj
      simp only [Array.size_empty, Nat.zero_add]
      by_cases hjl : j = last
      · subst hjl
        exact ⟨hargs, by rw [hval, hnew]⟩
      · exact hold j hj hjl
    rw [horig]
    exact hout

/-- **contract_sound**: whatever the network outputs after all of a proof's
    contractions, the original network outputs too. -/
theorem contractAll_sound {g : Graph} {w : Weights ℚ} {chains : List (List Nat)} {g' : Graph}
    {w' : Weights ℚ} (h : contractAll g w chains = .ok (g', w')) (x : Input) (out : Tensor ℚ)
    (hout : evalGraph g' w' x = some out) : evalGraph g w x = some out := by
  unfold contractAll at h
  suffices key : ∀ (cs : List (List Nat)) (g0 : Graph) (w0 : Weights ℚ) (removed : List Nat)
      (step : Nat), contractAll.go g0 w0 removed step cs = .ok (g', w') →
        evalGraph g0 w0 x = some out from key chains g w [] 0 h
  intro cs
  induction cs with
  | nil =>
    intro g0 w0 removed step h0
    simp only [contractAll.go, Except.ok.injEq, Prod.mk.injEq] at h0
    obtain ⟨rfl, rfl⟩ := h0
    exact hout
  | cons c cs ih =>
    intro g0 w0 removed step h0
    simp only [contractAll.go] at h0
    cases h1 : contractOne g0 w0 removed step c with
    | error e => simp [h1] at h0
    | ok r =>
      obtain ⟨g1, w1, removed1⟩ := r
      simp only [h1] at h0
      exact contractOne_sound h1 x out (ih g1 w1 removed1 (step + 1) h0)

end CompactCheck
