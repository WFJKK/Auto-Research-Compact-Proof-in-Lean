import Protected.N_max2_tiny_v8_s0_c23
import CompactCheck.Soundness
import CompactCheck.CountedOps

/-!
# Max-of-2 via the columns of `M = U L E`, on five tokens

The network is linear in the summed one-hot: `logits(a, b) = M[:, a] + M[:, b]` with `M = U L E`.
The checker computes each needed column of `M` once (48 multiply-adds), adds two columns per input
pair (8) and compares (7); one `single` call on one input establishes that the weight tensors are
well formed (the counted language cannot read a tensor's size) and certifies that input and its mirror.
This plan covers the tokens `0..4` (all pairs but `(0, 2)`): 23 inputs within the budget 540.
-/

namespace Candidate.Max2Cols23
open CompactCheck Protected.N_max2_tiny_v8_s0_c23

/-! ## Dimensions and names: the literals of the general layer -/
def d0 : Nat := 0
def d1 : Nat := 1
def d2 : Nat := 2
def d4 : Nat := 4
def d8 : Nat := 8
def q0 : ℚ := 0
def q1 : ℚ := 1
def nE : String := "embedding.weight"
def nL : String := "linear.weight"
def nU : String := "unembedding.weight"
def cat : String := "m"

/-! ## The checker (plain structural recursion only) -/

def eqL : List Nat → List Nat → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | a :: as, b :: bs => if a = b then eqL as bs else false

def nth : List Q → Nat → Option Q
  | [], Nat.zero => none
  | [], Nat.succ _ => none
  | q :: _, Nat.zero => some q
  | _ :: qs, Nat.succ k => nth qs k

def readIdx (name : String) : List Nat → CostM (List Q)
  | [] => pure []
  | i :: is => do
    let q ← CostM.weight name i
    let qs ← readIdx name is
    pure (q :: qs)

def dotL : List Q → List Q → Q → CostM Q
  | [], _, acc => pure acc
  | _ :: _, [], acc => pure acc
  | x :: xs, y :: ys, acc => do
    let acc' ← CostM.qmuladd cat acc x y
    dotL xs ys acc'

def matRows (name : String) (inn : Nat) (v : List Q) : List Nat → CostM (List Q)
  | [] => pure []
  | r :: rs => do
    let row ← readIdx name ((List.range inn).map fun i => r * inn + i)
    let z ← CostM.zero
    let q ← dotL row v z
    let qs ← matRows name inn v rs
    pure (q :: qs)

def colM (a : Nat) : CostM (List Q) := do
  let e ← readIdx nE ((List.range d4).map fun k => k * d8 + a)
  let h ← matRows nL d4 e (List.range d4)
  matRows nU d4 h (List.range d8)

def addL : List Q → List Q → CostM (List Q)
  | [], _ => pure []
  | _ :: _, [] => pure []
  | x :: xs, y :: ys => do
    let s ← CostM.qadd cat x y
    let ss ← addL xs ys
    pure (s :: ss)

def belowAll (top : Q) (lab : Nat) : List Q → Nat → CostM Bool
  | [], _ => pure true
  | q :: qs, i =>
    if i = lab then belowAll top lab qs i.succ
    else do
      let b ← CostM.qlt cat q top
      let r ← belowAll top lab qs i.succ
      pure (b && r)

def argmaxAt (v : List Q) (lab : Nat) : CostM Bool :=
  match nth v lab with
  | none => pure false
  | some top => belowAll top lab v d0

def lookupCol : List (Nat × List Q) → Nat → Option (List Q)
  | [], _ => none
  | (t, c) :: cs, a => if t = a then some c else lookupCol cs a

/-- Input `[a, b]` with `a ≤ b`: the label is `b`. -/
def checkPair (cols : List (Nat × List Q)) (a b : Nat) : CostM Bool :=
  match lookupCol cols a with
  | none => pure false
  | some ca =>
    match lookupCol cols b with
    | none => pure false
    | some cb =>
      if a = b then argmaxAt ca a
      else do
        let s ← addL ca cb
        argmaxAt s b

def pairInputs : List (Nat × Nat) → List Input
  | [] => []
  | (a, b) :: ps => (if a = b then [[a, a]] else [[a, b], [b, a]]) ++ pairInputs ps

def runPairs (cols : List (Nat × List Q)) : List (Nat × Nat) → CostM Nat
  | [] => pure Nat.zero
  | (a, b) :: ps => do
    let ok ← checkPair cols a b
    let n ← runPairs cols ps
    pure (if ok then (pairInputs [(a, b)]).length + n else n)

def computeCols : List Nat → CostM (List (Nat × List Q))
  | [] => pure []
  | a :: as => do
    let c ← colM a
    let cs ← computeCols as
    pure ((a, c) :: cs)

def shapesOk : CostM Bool := do
  let sE ← CostM.weightShape nE
  let sL ← CostM.weightShape nL
  let sU ← CostM.weightShape nU
  pure (eqL sE [d4, d8] && eqL sL [d4, d4] && eqL sU [d8, d4])

def x0Inputs : Input → List Input
  | [] => []
  | [_] => []
  | [a, b] => if a = b then [[a, a]] else [[a, b], [b, a]]
  | _ :: _ :: _ :: _ => []

/-- The checker on a plan: one `single` on `x0` (well-formedness, and `x0` with its mirror), then the
    columns of `M` for `toks` and the exact check of every pair `(a, b)`, `a ≤ b`. -/
def DPlan (x0 : Input) (toks : List Nat) (pairs : List (Nat × Nat)) : CostM Nat := do
  let ok0 ← CostM.single graph task x0
  let sh ← shapesOk
  if ok0 && sh then
    let cols ← computeCols toks
    let n ← runPairs cols pairs
    pure (n + (x0Inputs x0).length)
  else pure Nat.zero

/-- All `(a, b)` with `a ≤ b < n`. -/
def pairsUpTo : Nat → List (Nat × Nat)
  | Nat.zero => []
  | Nat.succ n => pairsUpTo n ++ (List.range n.succ).map fun a => (a, n)

def removePair (qa qb : Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => []
  | (a, b) :: ps =>
    if a = qa then (if b = qb then removePair qa qb ps else (a, b) :: removePair qa qb ps)
    else (a, b) :: removePair qa qb ps

/-! ## The forward pass, symbolically -/

theorem get_map_range {s : List Nat} {f : Nat → ℚ} {n j : Nat} (hj : j < n) :
    (Tensor.mk s ((Array.range n).map f)).get j = f j := by
  simp [Tensor.get, Array.getD, hj]

theorem linearOp_eq {W t : Tensor ℚ} {out inn : Nat}
    (hWs : W.shape = [out, inn]) (hWn : W.data.size = out * inn)
    (hts : t.shape = [d1, inn]) (htn : t.data.size = inn) :
    linearOp W none t = some ⟨[d1, out], (Array.range out).map fun j =>
      ((List.range inn).map fun i => W.get (j % out * inn + i) * t.get (j / out * inn + i)).sum⟩ := by
  unfold linearOp
  simp [hWs, hts, hWn, htn, shapeSize, d1]

theorem linearOp_spec {W t : Tensor ℚ} {out inn : Nat}
    (hWs : W.shape = [out, inn]) (hWn : W.data.size = out * inn)
    (hts : t.shape = [d1, inn]) (htn : t.data.size = inn) :
    ∃ r, linearOp W none t = some r ∧ r.shape = [d1, out] ∧ r.data.size = out ∧
      ∀ j, j < out → r.get j = ((List.range inn).map fun i => W.get (j * inn + i) * t.get i).sum := by
  refine ⟨_, linearOp_eq hWs hWn hts htn, rfl, by simp, fun j hj => ?_⟩
  rw [get_map_range hj]
  simp [Nat.mod_eq_of_lt hj, Nat.div_eq_of_lt hj]

theorem linearOp_size {W t : Tensor ℚ} {b : Option (Tensor ℚ)} {r : Tensor ℚ} {out inn : Nat}
    (hWs : W.shape = [out, inn]) (h : linearOp W b t = some r) : W.data.size = out * inn := by
  unfold linearOp at h
  rw [Option.ite_none_right_eq_some] at h
  have hc := h.1
  simp only [hWs, Bool.and_eq_true, beq_iff_eq, List.getD_cons_zero, List.getD_cons_succ] at hc
  exact hc.1.1.2

theorem oneHot_spec {a b : Nat} (ha : a < d8) (hb : b < d8) :
    ∃ oh : Tensor ℚ, oneHotInput d2 d8 [a, b] = some oh ∧ oh.shape = [d1, d2, d8] ∧
      oh.data.size = d2 * d8 ∧
      (∀ l, l < d8 → oh.get l = if a = l then q1 else q0) ∧
      (∀ l, l < d8 → oh.get (d8 + l) = if b = l then q1 else q0) := by
  simp only [d8] at ha hb
  refine ⟨⟨[d1, d2, d8], (Array.range (d2 * d8)).map fun j =>
      if [a, b].getD (j / d8) d0 = j % d8 then q1 else q0⟩, ?_, rfl, by simp, ?_, ?_⟩
  · unfold oneHotInput
    simp [ha, hb, d1, d2, d8, d0, q0, q1]
  · intro l hl
    simp only [d8] at hl
    rw [get_map_range (by simp [d2, d8]; omega)]
    simp [d8, d0, Nat.div_eq_of_lt hl, Nat.mod_eq_of_lt hl]
  · intro l hl
    simp only [d8] at hl
    rw [get_map_range (by simp [d2, d8]; omega)]
    have h1 : (8 + l) / 8 = 1 := by omega
    have h2 : (8 + l) % 8 = l := by omega
    simp [d8, d0, h1, h2]

theorem sumOp_spec {t : Tensor ℚ} (hts : t.shape = [d1, d2, d8]) (htn : t.data.size = d2 * d8) :
    ∃ r, sumOp 1 t = some r ∧ r.shape = [d1, d8] ∧ r.data.size = d8 ∧
      ∀ j, j < d8 → r.get j = t.get j + t.get (d8 + j) := by
  simp only [d1, d2, d8] at hts htn ⊢
  refine ⟨⟨[1, 8], (Array.range 8).map fun j =>
      ((List.range 2).map fun k => t.get ((j / 8 * 2 + k) * 8 + j % 8)).sum⟩, ?_, rfl, by simp, ?_⟩
  · unfold sumOp
    simp [hts, htn, normDim, shapeSize]
  · intro j hj
    rw [get_map_range hj]
    simp [Nat.mod_eq_of_lt hj, Nat.div_eq_of_lt hj, List.range_succ]

theorem sum_onehot_zero (f : Nat → ℚ) : ∀ (n a : Nat), n ≤ a →
    ((List.range n).map fun l => f l * (if a = l then q1 else q0)).sum = q0
  | 0, _, _ => by simp [q0]
  | n + 1, a, h => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_onehot_zero f n a (by omega)]
    simp [show a ≠ n by omega, q0]

theorem sum_onehot (f : Nat → ℚ) : ∀ (n a : Nat), a < n →
    ((List.range n).map fun l => f l * (if a = l then q1 else q0)).sum = f a
  | 0, a, h => absurd h (Nat.not_lt_zero _)
  | n + 1, a, h => by
    rw [List.range_succ, List.map_append, List.sum_append]
    rcases Nat.lt_or_ge a n with h' | h'
    · rw [sum_onehot f n a h']; simp [show a ≠ n by omega, q0]
    · have : a = n := by omega
      subst this; rw [sum_onehot_zero f a a le_rfl]; simp [q0, q1]

/-- The well-formed weights of the network. -/
structure WF (w : Weights ℚ) (tE tL tU : Tensor ℚ) : Prop where
  hE : List.lookup nE w = some tE
  hEs : tE.shape = [d4, d8]
  hEn : tE.data.size = d4 * d8
  hL : List.lookup nL w = some tL
  hLs : tL.shape = [d4, d4]
  hLn : tL.data.size = d4 * d4
  hU : List.lookup nU w = some tU
  hUs : tU.shape = [d8, d4]
  hUn : tU.data.size = d8 * d4

def embF (tE : Tensor ℚ) (a b i' : Nat) : ℚ := tE.get (i' * d8 + a) + tE.get (i' * d8 + b)

def outF (tE tL tU : Tensor ℚ) (a b j : Nat) : ℚ :=
  ((List.range d4).map fun i => tU.get (j * d4 + i) *
    ((List.range d4).map fun i' => tL.get (i * d4 + i') * embF tE a b i').sum).sum

theorem eval_formula {w : Weights ℚ} {tE tL tU : Tensor ℚ} (hw : WF w tE tL tU)
    {a b : Nat} (ha : a < d8) (hb : b < d8) :
    ∃ out, evalGraph graph w [a, b] = some out ∧ out.shape = [d1, d8] ∧ out.data.size = d8 ∧
      ∀ j, j < d8 → out.get j = outF tE tL tU a b j := by
  obtain ⟨oh, h0, hohs, hohn, hoha, hohb⟩ := oneHot_spec ha hb
  obtain ⟨s, hs, hss, hsn, hsg⟩ := sumOp_spec hohs hohn
  obtain ⟨e1, he1, he1s, he1n, he1g⟩ := linearOp_spec hw.hEs hw.hEn hss hsn
  obtain ⟨e2, he2, he2s, he2n, he2g⟩ := linearOp_spec hw.hLs hw.hLn he1s he1n
  obtain ⟨e3, he3, he3s, he3n, he3g⟩ := linearOp_spec hw.hUs hw.hUn he2s he2n
  have hE : List.lookup "embedding.weight" w = some tE := hw.hE
  have hL : List.lookup "linear.weight" w = some tL := hw.hL
  have hU : List.lookup "unembedding.weight" w = some tU := hw.hU
  have h0' : oneHotInput 2 8 [a, b] = some oh := h0
  refine ⟨e3, ?_, he3s, he3n, ?_⟩
  · simp [evalGraph, evalOps, evalOp, graph, h0', hs, hE, hL, hU, he1, he2, he3]
  · intro j hj
    have hemb : ∀ i', i' < d4 → e1.get i' = embF tE a b i' := by
      intro i' hi'
      rw [he1g i' hi']
      have : ((List.range d8).map fun l => tE.get (i' * d8 + l) * s.get l) =
          (List.range d8).map fun l => tE.get (i' * d8 + l) *
            ((if a = l then q1 else q0) + (if b = l then q1 else q0)) := by
        apply List.map_congr_left
        intro l hl
        rw [List.mem_range] at hl
        rw [hsg l hl, hoha l hl, hohb l hl]
      rw [this]
      simp only [mul_add, List.sum_map_add]
      rw [sum_onehot _ d8 a ha, sum_onehot _ d8 b hb]
      rfl
    rw [he3g j hj]
    unfold outF
    have hr4 : List.range d4 = [0, 1, 2, 3] := rfl
    simp only [hr4, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [he2g 0 (by decide), he2g 1 (by decide), he2g 2 (by decide), he2g 3 (by decide)]
    simp only [hr4, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [hemb 0 (by decide), hemb 1 (by decide), hemb 2 (by decide), hemb 3 (by decide)]

theorem eval_sizes {w : Weights ℚ} {tE tL tU : Tensor ℚ}
    (hE : List.lookup nE w = some tE) (hEs : tE.shape = [d4, d8])
    (hL : List.lookup nL w = some tL) (hLs : tL.shape = [d4, d4])
    (hU : List.lookup nU w = some tU) (hUs : tU.shape = [d8, d4])
    {a b : Nat} (ha : a < d8) (hb : b < d8) {out : Tensor ℚ}
    (h : evalGraph graph w [a, b] = some out) : WF w tE tL tU := by
  obtain ⟨oh, h0, hohs, hohn, -, -⟩ := oneHot_spec ha hb
  obtain ⟨s, hs, -, -, -⟩ := sumOp_spec hohs hohn
  have hE' : List.lookup "embedding.weight" w = some tE := hE
  have hL' : List.lookup "linear.weight" w = some tL := hL
  have hU' : List.lookup "unembedding.weight" w = some tU := hU
  have h0' : oneHotInput 2 8 [a, b] = some oh := h0
  simp [evalGraph, evalOps, evalOp, graph, h0', hs, hE', hL', hU'] at h
  cases h1 : linearOp tE none s with
  | none => simp [h1] at h
  | some v1 =>
    cases h2 : linearOp tL none v1 with
    | none => simp [h1, h2] at h
    | some v2 =>
      cases h3 : linearOp tU none v2 with
      | none => simp [h1, h2, h3] at h
      | some v3 =>
        exact ⟨hE, hEs, linearOp_size hEs h1, hL, hLs, linearOp_size hLs h2, hU, hUs, linearOp_size hUs h3⟩

/-! ## What the checker's numbers are -/

def dotQ : List ℚ → List ℚ → ℚ → ℚ
  | x :: xs, y :: ys, acc => dotQ xs ys (acc + x * y)
  | _, _, acc => acc

def colE (tE : Tensor ℚ) (a : Nat) : List ℚ := (List.range d4).map fun k => tE.get (k * d8 + a)

def hcol (tE tL : Tensor ℚ) (a k : Nat) : ℚ :=
  dotQ ((List.range d4).map fun i => tL.get (k * d4 + i)) (colE tE a) q0

def Ment (tE tL tU : Tensor ℚ) (a j : Nat) : ℚ :=
  dotQ ((List.range d4).map fun i => tU.get (j * d4 + i)) ((List.range d4).map (hcol tE tL a)) q0

theorem outF_eq (tE tL tU : Tensor ℚ) (a b j : Nat) :
    outF tE tL tU a b j = Ment tE tL tU a j + Ment tE tL tU b j := by
  have hr4 : List.range d4 = [0, 1, 2, 3] := rfl
  simp only [outF, Ment, hcol, colE, embF, hr4, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, dotQ, q0]
  ring

theorem bind_some {α β : Type} {x : CostM α} {f : α → CostM β} {env : Env} {c c' : Cost} {b : β}
    (h : (x >>= f).run env c = some (b, c')) :
    ∃ a c1, x.run env c = some (a, c1) ∧ (f a).run env c1 = some (b, c') := by
  rw [CostM.run_bind] at h
  split at h
  · rename_i a c1 ha; exact ⟨a, c1, ha, h⟩
  · cases h

theorem pure_some {α : Type} {a b : α} {env : Env} {c c' : Cost}
    (h : (pure a : CostM α).run env c = some (b, c')) : b = a ∧ c' = c := by
  rw [CostM.run_pure] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

theorem weight_spec {name : String} {i : Nat} {env : Env} {c c' : Cost} {q : Q}
    (h : (CostM.weight name i).run env c = some (q, c')) :
    ∃ t, List.lookup name env.weights = some t ∧ q.val = t.get i := by
  simp only [CostM.weight] at h
  split at h
  · rename_i t ht
    split at h
    · rename_i hi
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      refine ⟨t, ht, ?_⟩
      rw [← h.1]
      simp [Tensor.get, getElem!_pos, hi, Array.getD]
    · cases h
  · cases h

theorem weightShape_spec {name : String} {env : Env} {c c' : Cost} {s : List Nat}
    (h : (CostM.weightShape name).run env c = some (s, c')) :
    ∃ t, List.lookup name env.weights = some t ∧ t.shape = s := by
  simp only [CostM.weightShape] at h
  split at h
  · rename_i t ht
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨t, ht, h.1⟩
  · cases h

theorem zero_spec {env : Env} {c c' : Cost} {q : Q} (h : CostM.zero.run env c = some (q, c')) :
    q.val = q0 := by
  simp only [CostM.zero, Option.some.injEq, Prod.mk.injEq] at h
  rw [← h.1]; rfl

theorem qmuladd_spec {s : String} {acc x y q : Q} {env : Env} {c c' : Cost}
    (h : (CostM.qmuladd s acc x y).run env c = some (q, c')) : q.val = acc.val + x.val * y.val := by
  simp only [CostM.qmuladd, Option.some.injEq, Prod.mk.injEq] at h
  rw [← h.1]

theorem qadd_spec {s : String} {x y q : Q} {env : Env} {c c' : Cost}
    (h : (CostM.qadd s x y).run env c = some (q, c')) : q.val = x.val + y.val := by
  simp only [CostM.qadd, Option.some.injEq, Prod.mk.injEq] at h
  rw [← h.1]

theorem qlt_spec {s : String} {x y : Q} {b : Bool} {env : Env} {c c' : Cost}
    (h : (CostM.qlt s x y).run env c = some (b, c')) : b = decide (x.val < y.val) := by
  simp only [CostM.qlt, Option.some.injEq, Prod.mk.injEq] at h
  exact h.1.symm

theorem eqL_spec : ∀ {xs ys : List Nat}, eqL xs ys = true → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [eqL] at h
  | _ :: _, [], h => by simp [eqL] at h
  | a :: as, b :: bs, h => by
    simp only [eqL] at h
    split at h
    · rename_i hab; rw [hab, eqL_spec h]
    · cases h

theorem nth_spec : ∀ {v : List Q} {k : Nat} {q : Q}, nth v k = some q → ∃ hk : k < v.length, v[k] = q
  | [], Nat.zero, q, h => by simp [nth] at h
  | [], Nat.succ _, q, h => by simp [nth] at h
  | x :: _, Nat.zero, q, h => by
    simp only [nth, Option.some.injEq] at h
    exact ⟨Nat.succ_pos _, h⟩
  | _ :: xs, Nat.succ k, q, h => by
    simp only [nth] at h
    obtain ⟨hk, hv⟩ := nth_spec h
    exact ⟨Nat.succ_lt_succ hk, hv⟩

theorem readIdx_spec {name : String} {env : Env} {t : Tensor ℚ}
    (ht : List.lookup name env.weights = some t) :
    ∀ {is : List Nat} {c c' : Cost} {qs : List Q}, (readIdx name is).run env c = some (qs, c') →
      qs.map Q.val = is.map t.get
  | [], c, c', qs, h => by
    simp only [readIdx] at h
    obtain ⟨hq, -⟩ := pure_some h
    subst hq; rfl
  | i :: is, c, c', qs, h => by
    simp only [readIdx] at h
    obtain ⟨q, c1, hq, h⟩ := bind_some h
    obtain ⟨qs', c2, hqs, h⟩ := bind_some h
    obtain ⟨hq', -⟩ := pure_some h
    subst hq'
    obtain ⟨t', ht', hv⟩ := weight_spec hq
    rw [ht] at ht'
    cases ht'
    simp only [List.map_cons, hv, readIdx_spec ht hqs]

theorem dotL_spec {env : Env} : ∀ {xs ys : List Q} {acc : Q} {c c' : Cost} {q : Q},
    (dotL xs ys acc).run env c = some (q, c') → q.val = dotQ (xs.map Q.val) (ys.map Q.val) acc.val
  | [], ys, acc, c, c', q, h => by
    simp only [dotL] at h
    obtain ⟨hq, -⟩ := pure_some h
    subst hq; simp [dotQ]
  | x :: xs, [], acc, c, c', q, h => by
    simp only [dotL] at h
    obtain ⟨hq, -⟩ := pure_some h
    subst hq; simp [dotQ]
  | x :: xs, y :: ys, acc, c, c', q, h => by
    simp only [dotL] at h
    obtain ⟨acc', c1, hm, h⟩ := bind_some h
    have hv := qmuladd_spec hm
    simp only [List.map_cons, dotQ]
    rw [← hv]
    exact dotL_spec h

theorem matRows_spec {env : Env} {name : String} {inn : Nat} {v : List Q} {t : Tensor ℚ}
    (ht : List.lookup name env.weights = some t) :
    ∀ {rs : List Nat} {c c' : Cost} {qs : List Q}, (matRows name inn v rs).run env c = some (qs, c') →
      qs.map Q.val = rs.map fun r => dotQ ((List.range inn).map fun i => t.get (r * inn + i)) (v.map Q.val) q0
  | [], c, c', qs, h => by
    simp only [matRows] at h
    obtain ⟨hq, -⟩ := pure_some h
    subst hq; rfl
  | r :: rs, c, c', qs, h => by
    simp only [matRows] at h
    obtain ⟨row, c1, hrow, h⟩ := bind_some h
    obtain ⟨z, c2, hz, h⟩ := bind_some h
    obtain ⟨q, c3, hq, h⟩ := bind_some h
    obtain ⟨qs', c4, hqs, h⟩ := bind_some h
    obtain ⟨hq', -⟩ := pure_some h
    subst hq'
    have h1 := readIdx_spec ht hrow
    have h2 := dotL_spec hq
    have h3 := zero_spec hz
    rw [h1, h3, List.map_map] at h2
    simp only [List.map_cons, h2, matRows_spec ht hqs, Function.comp_def]

theorem colM_spec {env : Env} {tE tL tU : Tensor ℚ} (hE : List.lookup nE env.weights = some tE)
    (hL : List.lookup nL env.weights = some tL) (hU : List.lookup nU env.weights = some tU)
    {a : Nat} {c c' : Cost} {qs : List Q} (h : (colM a).run env c = some (qs, c')) :
    qs.map Q.val = (List.range d8).map (Ment tE tL tU a) := by
  unfold colM at h
  obtain ⟨e, c1, he, h⟩ := bind_some h
  obtain ⟨hh, c2, hhh, h⟩ := bind_some h
  have he' := readIdx_spec hE he
  have hh' := matRows_spec hL hhh
  have hq := matRows_spec hU h
  rw [hq, hh', he']
  simp only [List.map_map, Function.comp_def]
  rfl

theorem computeCols_spec {env : Env} {tE tL tU : Tensor ℚ} (hE : List.lookup nE env.weights = some tE)
    (hL : List.lookup nL env.weights = some tL) (hU : List.lookup nU env.weights = some tU) :
    ∀ {toks : List Nat} {c c' : Cost} {cols : List (Nat × List Q)},
      (computeCols toks).run env c = some (cols, c') →
      ∀ p ∈ cols, p.2.map Q.val = (List.range d8).map (Ment tE tL tU p.1)
  | [], c, c', cols, h, p, hp => by
    simp only [computeCols] at h
    obtain ⟨hc, -⟩ := pure_some h
    subst hc; simp at hp
  | a :: as, c, c', cols, h, p, hp => by
    simp only [computeCols] at h
    obtain ⟨col, c1, hcol, h⟩ := bind_some h
    obtain ⟨cs, c2, hcs, h⟩ := bind_some h
    obtain ⟨hc, -⟩ := pure_some h
    subst hc
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact colM_spec hE hL hU hcol
    · exact computeCols_spec hE hL hU hcs p hp'

theorem addL_spec {env : Env} : ∀ {xs ys : List Q} {c c' : Cost} {s : List Q},
    (addL xs ys).run env c = some (s, c') →
      s.map Q.val = List.zipWith (· + ·) (xs.map Q.val) (ys.map Q.val)
  | [], ys, c, c', s, h => by
    simp only [addL] at h
    obtain ⟨hs, -⟩ := pure_some h
    subst hs; simp
  | x :: xs, [], c, c', s, h => by
    simp only [addL] at h
    obtain ⟨hs, -⟩ := pure_some h
    subst hs; simp
  | x :: xs, y :: ys, c, c', s, h => by
    simp only [addL] at h
    obtain ⟨q, c1, hq, h⟩ := bind_some h
    obtain ⟨ss, c2, hss, h⟩ := bind_some h
    obtain ⟨hs, -⟩ := pure_some h
    subst hs
    simp only [List.map_cons, List.zipWith_cons_cons, qadd_spec hq, addL_spec hss]

theorem belowAll_spec {env : Env} {top : Q} {lab : Nat} : ∀ {qs : List Q} {i : Nat} {c c' : Cost},
    (belowAll top lab qs i).run env c = some (true, c') →
    ∀ k (hk : k < qs.length), i + k ≠ lab → (qs[k]).val < top.val
  | [], i, c, c', h, k, hk, _ => absurd hk (Nat.not_lt_zero _)
  | q :: qs, i, c, c', h, k, hk, hne => by
    simp only [belowAll] at h
    split at h
    · rename_i hi
      cases k with
      | zero => exact absurd hi (by simpa using hne)
      | succ k =>
        have := belowAll_spec h k (by simpa using hk) (by omega)
        simpa using this
    · rename_i hi
      obtain ⟨b, c1, hb, h⟩ := bind_some h
      obtain ⟨r, c2, hr, h⟩ := bind_some h
      obtain ⟨hbr, -⟩ := pure_some h
      have hand : b = true ∧ r = true := by simpa using hbr.symm
      cases k with
      | zero =>
        simp only [List.getElem_cons_zero]
        have hb' := qlt_spec hb
        rw [hand.1] at hb'
        exact of_decide_eq_true hb'.symm
      | succ k =>
        rw [hand.2] at hr
        have := belowAll_spec hr k (by simpa using hk) (by omega)
        simpa using this

theorem argmaxAt_spec {env : Env} {v : List Q} {lab : Nat} {c c' : Cost}
    (h : (argmaxAt v lab).run env c = some (true, c')) :
    ∃ hl : lab < v.length, ∀ k (hk : k < v.length), k ≠ lab → (v[k]).val < (v[lab]).val := by
  unfold argmaxAt at h
  split at h
  · simp [CostM.run_pure] at h
  · rename_i top htop
    obtain ⟨hl, hv⟩ := nth_spec htop
    refine ⟨hl, fun k hk hne => ?_⟩
    have := belowAll_spec h k hk (by simp [d0]; omega)
    rw [hv]
    exact this

theorem lookupCol_mem : ∀ {cols : List (Nat × List Q)} {a : Nat} {ca : List Q},
    lookupCol cols a = some ca → (a, ca) ∈ cols
  | [], a, ca, h => by simp [lookupCol] at h
  | (t, c) :: cs, a, ca, h => by
    simp only [lookupCol] at h
    split at h
    · rename_i hta
      simp only [Option.some.injEq] at h
      subst hta; subst h
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookupCol_mem h)

theorem val_of_map_eq {v : List Q} {f : Nat → ℚ} {n : Nat} (h : v.map Q.val = (List.range n).map f) :
    v.length = n ∧ ∀ k (hk : k < v.length), (v[k]).val = f k := by
  have hlen : v.length = n := by
    have := congrArg List.length h
    simpa using this
  refine ⟨hlen, fun k hk => ?_⟩
  have hk' : k < (v.map Q.val).length := by simpa using hk
  have h1 := List.getElem_of_eq h hk'
  simp only [List.getElem_map, List.getElem_range] at h1
  exact h1

theorem val_of_zip {s ca cb : List Q}
    (h : s.map Q.val = List.zipWith (· + ·) (ca.map Q.val) (cb.map Q.val)) :
    s.length = min ca.length cb.length ∧
      ∀ k (hk : k < s.length) (hka : k < ca.length) (hkb : k < cb.length),
        (s[k]).val = (ca[k]).val + (cb[k]).val := by
  have hlen : s.length = min ca.length cb.length := by
    have := congrArg List.length h
    simpa using this
  refine ⟨hlen, fun k hk hka hkb => ?_⟩
  have hk' : k < (s.map Q.val).length := by simpa using hk
  have h1 := List.getElem_of_eq h hk'
  simp only [List.getElem_map, List.getElem_zipWith] at h1
  exact h1

theorem checkPair_spec {env : Env} {tE tL tU : Tensor ℚ} {cols : List (Nat × List Q)}
    (hcols : ∀ p ∈ cols, p.2.map Q.val = (List.range d8).map (Ment tE tL tU p.1))
    {a b : Nat} {c c' : Cost} (h : (checkPair cols a b).run env c = some (true, c')) :
    b < d8 ∧ ∀ j, j < d8 → j ≠ b →
      Ment tE tL tU a j + Ment tE tL tU b j < Ment tE tL tU a b + Ment tE tL tU b b := by
  unfold checkPair at h
  split at h
  · simp [CostM.run_pure] at h
  · rename_i ca hA
    split at h
    · simp [CostM.run_pure] at h
    · rename_i cb hB
      have hA' := hcols (a, ca) (lookupCol_mem hA)
      have hB' := hcols (b, cb) (lookupCol_mem hB)
      dsimp only at hA' hB'
      obtain ⟨hca, hcak⟩ := val_of_map_eq hA'
      obtain ⟨hcb, hcbk⟩ := val_of_map_eq hB'
      split at h
      · rename_i hab
        subst hab
        obtain ⟨hl, hall⟩ := argmaxAt_spec h
        refine ⟨by omega, fun j hj hne => ?_⟩
        have := hall j (by omega) hne
        rw [hcak j (by omega), hcak a (by omega)] at this
        exact add_lt_add this this
      · rename_i hab
        obtain ⟨s, c1, hs, h⟩ := bind_some h
        obtain ⟨hsl, hsk⟩ := val_of_zip (addL_spec hs)
        obtain ⟨hl, hall⟩ := argmaxAt_spec h
        have hs8 : s.length = d8 := by rw [hsl, hca, hcb]; simp
        refine ⟨by omega, fun j hj hne => ?_⟩
        have := hall j (by omega) hne
        rw [hsk j (by omega) (by omega) (by omega), hsk b (by omega) (by omega) (by omega),
          hcak j (by omega), hcbk j (by omega), hcak b (by omega), hcbk b (by omega)] at this
        exact this

theorem correct_of_margins {w : Weights ℚ} {tE tL tU : Tensor ℚ} (hw : WF w tE tL tU) {a b : Nat}
    (hab : a ≤ b) (hb : b < d8)
    (hm : ∀ j, j < d8 → j ≠ b →
      Ment tE tL tU a j + Ment tE tL tU b j < Ment tE tL tU a b + Ment tE tL tU b b) :
    Correct graph w task [a, b] ∧ Correct graph w task [b, a] := by
  have ha : a < d8 := lt_of_le_of_lt hab hb
  constructor
  · obtain ⟨out, hout, hs, hn, hg⟩ := eval_formula hw ha hb
    have hlab : task.label [a, b] = b := by
      simp only [task, maxTask, List.foldl_cons, List.foldl_nil]
      omega
    refine ⟨out.map (fun q : ℚ => (q : ℝ)), realOutput_of_evalGraph hout, ?_, ?_, ?_⟩
    · simp [hs, hn, d1, d8]
    · simp [hlab, hn]; simpa [d8] using hb
    · intro j hj hne
      simp only [Tensor.map_data_size, hn] at hj
      rw [hlab] at hne ⊢
      rw [Tensor.get_map_cast, Tensor.get_map_cast, Rat.cast_lt, hg j hj, hg b hb, outF_eq, outF_eq]
      exact hm j hj hne
  · obtain ⟨out, hout, hs, hn, hg⟩ := eval_formula hw hb ha
    have hlab : task.label [b, a] = b := by
      simp only [task, maxTask, List.foldl_cons, List.foldl_nil]
      omega
    refine ⟨out.map (fun q : ℚ => (q : ℝ)), realOutput_of_evalGraph hout, ?_, ?_, ?_⟩
    · simp [hs, hn, d1, d8]
    · simp [hlab, hn]; simpa [d8] using hb
    · intro j hj hne
      simp only [Tensor.map_data_size, hn] at hj
      rw [hlab] at hne ⊢
      rw [Tensor.get_map_cast, Tensor.get_map_cast, Rat.cast_lt, hg j hj, hg b hb, outF_eq, outF_eq]
      rw [add_comm (Ment tE tL tU b j), add_comm (Ment tE tL tU b b)]
      exact hm j hj hne

open Classical in
theorem runPairs_le {env : Env} {tE tL tU : Tensor ℚ} (hw : WF env.weights tE tL tU)
    {cols : List (Nat × List Q)}
    (hcols : ∀ p ∈ cols, p.2.map Q.val = (List.range d8).map (Ment tE tL tU p.1)) :
    ∀ {ps : List (Nat × Nat)} {c c' : Cost} {n : Nat}, (∀ p ∈ ps, p.1 ≤ p.2) →
      (runPairs cols ps).run env c = some (n, c') →
      n ≤ (pairInputs ps).countP fun x => decide (Correct graph env.weights task x)
  | [], c, c', n, _, h => by
    simp only [runPairs] at h
    obtain ⟨hn, -⟩ := pure_some h
    subst hn; exact Nat.zero_le _
  | (a, b) :: ps, c, c', n, hps, h => by
    simp only [runPairs] at h
    obtain ⟨ok, c1, hok, h⟩ := bind_some h
    obtain ⟨m, c2, hm, h⟩ := bind_some h
    obtain ⟨hn, -⟩ := pure_some h
    subst hn
    have ih := runPairs_le hw hcols (fun p hp => hps p (List.mem_cons_of_mem _ hp)) hm
    have hab : a ≤ b := hps (a, b) List.mem_cons_self
    simp only [pairInputs, List.countP_append]
    cases ok with
    | false => simp only [Bool.false_eq_true, ite_false]; omega
    | true =>
      simp only [ite_true]
      obtain ⟨hb, hmarg⟩ := checkPair_spec hcols hok
      obtain ⟨h1, h2⟩ := correct_of_margins hw hab hb hmarg
      by_cases hab' : a = b
      · subst hab'; simp [h1]; omega
      · simp [hab', h1, h2]; omega

theorem shapesOk_spec {env : Env} {c c' : Cost} (h : shapesOk.run env c = some (true, c')) :
    ∃ tE tL tU : Tensor ℚ, List.lookup nE env.weights = some tE ∧ tE.shape = [d4, d8] ∧
      List.lookup nL env.weights = some tL ∧ tL.shape = [d4, d4] ∧
      List.lookup nU env.weights = some tU ∧ tU.shape = [d8, d4] := by
  unfold shapesOk at h
  obtain ⟨sE, c1, hsE, h⟩ := bind_some h
  obtain ⟨sL, c2, hsL, h⟩ := bind_some h
  obtain ⟨sU, c3, hsU, h⟩ := bind_some h
  obtain ⟨hb, -⟩ := pure_some h
  obtain ⟨tE, hE, hEs⟩ := weightShape_spec hsE
  obtain ⟨tL, hL, hLs⟩ := weightShape_spec hsL
  obtain ⟨tU, hU, hUs⟩ := weightShape_spec hsU
  have hb' : (eqL sE [d4, d8] && eqL sL [d4, d4] && eqL sU [d8, d4]) = true := hb.symm
  simp only [Bool.and_eq_true] at hb'
  exact ⟨tE, tL, tU, hE, hEs.trans (eqL_spec hb'.1.1), hL, hLs.trans (eqL_spec hb'.1.2), hU,
    hUs.trans (eqL_spec hb'.2)⟩

theorem evalGraph_of_singleOk {g : Graph} {w : Weights ℚ} {task : Task} {x : Input}
    (h : singleOk g w task x = true) : ∃ out, evalGraph g w x = some out := by
  unfold singleOk at h
  split at h
  · rename_i out hout; exact ⟨out, hout⟩
  · cases h

open Classical in
theorem DPlan_le {a b : Nat} (ha : a < d8) (hb : b < d8) {toks : List Nat} {pairs : List (Nat × Nat)}
    (hps : ∀ p ∈ pairs, p.1 ≤ p.2) {env : Env} {n : Nat} {c' : Cost}
    (h : (DPlan [a, b] toks pairs).run env [] = some (n, c')) :
    n ≤ (x0Inputs [a, b] ++ pairInputs pairs).countP fun x => decide (Correct graph env.weights task x) := by
  unfold DPlan at h
  obtain ⟨ok0, c1, hok0, h⟩ := bind_some h
  obtain ⟨sh, c2, hsh, h⟩ := bind_some h
  cases ok0 <;> cases sh <;>
    simp only [Bool.true_and, Bool.false_and, Bool.and_true, Bool.false_eq_true, ite_false, ite_true] at h
  · obtain ⟨hn, -⟩ := pure_some h; subst hn; exact Nat.zero_le _
  · obtain ⟨hn, -⟩ := pure_some h; subst hn; exact Nat.zero_le _
  · obtain ⟨hn, -⟩ := pure_some h; subst hn; exact Nat.zero_le _
  · obtain ⟨cols, c3, hcols, h⟩ := bind_some h
    obtain ⟨m, c4, hm, h⟩ := bind_some h
    obtain ⟨hn, -⟩ := pure_some h
    subst hn
    have hsingle := CostM.single_spec hok0
    obtain ⟨tE, tL, tU, hE, hEs, hL, hLs, hU, hUs⟩ := shapesOk_spec hsh
    obtain ⟨out, hout⟩ := evalGraph_of_singleOk hsingle
    have hw : WF env.weights tE tL tU := eval_sizes hE hEs hL hLs hU hUs ha hb hout
    have hc := computeCols_spec hE hL hU hcols
    have hle := runPairs_le hw hc hps hm
    have h1 : Correct graph env.weights task [a, b] := singleOk_correct _ _ _ _ hsingle
    have h2 : Correct graph env.weights task [b, a] :=
      singleOk_correct _ _ _ _ (singleOk_perm (by decide) rfl (List.Perm.swap b a []) hsingle)
    rw [List.countP_append]
    by_cases hab : a = b
    · subst hab; simp [x0Inputs, h1]; omega
    · simp [x0Inputs, hab, h1, h2]; omega

/-! ## The plan: tokens `0..4`, the single on `[0, 1]`, every pair but `(0, 2)` -/

def plan : List (Nat × Nat) := removePair d0 d2 (removePair d0 d1 (pairsUpTo d4.succ))

def D : CostM Nat := DPlan [d0, d1] (List.range d4.succ) plan

theorem D_sound : ∀ (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),
    CostM.exec D ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task := by
  intro w c n cost h
  have h1 := DPlan_le (a := d0) (b := d1) (by decide) (by decide) (by decide +kernel) h
  unfold numCorrect
  refine le_trans h1 (List.Subperm.countP_le _ (List.subperm_of_subset ?_ ?_))
  · decide +kernel
  · have hall : ∀ x ∈ x0Inputs [d0, d1] ++ pairInputs plan, x ∈ allInputs task.space := by
      decide +kernel
    exact fun x hx => hall x hx

/-! ## Specific layer -/

theorem D_instance : CostM.billed D ⟨weights, cert⟩ = some (23, 458) := by
  decide +kernel

theorem performance : Target := by
  show claimedCount ≤ numCorrect graph weights task
  obtain ⟨cost, h⟩ := CostM.exec_of_billed D_instance
  exact D_sound weights cert 23 cost h

end Candidate.Max2Cols23
