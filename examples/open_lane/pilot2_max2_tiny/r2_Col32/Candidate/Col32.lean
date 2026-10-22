import Protected.N_max2_tiny_v8_s0_c32
import CompactCheck.Soundness
import CompactCheck.IntervalSound
import CompactCheck.CountedOps
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# 32 inputs of max2_tiny-v8-s0 from six columns of the product matrix

The network is linear: its logits on `[a, b]` are column `a` plus column `b` of `M = U L E`. The checker
computes six columns of `M` (48 operations each), the maximum of each column off its diagonal entry (`mx`),
the maximum of the whole column (`cmf`), and certifies the diagonal input `[m, m]` by `mx_m < M[m,m]` and a
pair `[a, m]`, `[m, a]` (`a < m`) by the decoupled bound `cmf_a + mx_m < M[m,a] + M[m,m]` (4 operations a
pair). One `single` on `[6, 7]` guards the well-formedness of the weights and counts its two inputs.
-/

namespace Candidate.Col32

open CompactCheck Protected.N_max2_tiny_v8_s0_c32

/-! ## The checker -/

def dotRow (I : Interp) (name : String) (base : Nat) : List I.V → Nat → I.V → I.M I.V
  | [], _, acc => pure acc
  | v :: vs, i, acc => do
    let x ← I.weight name (base + i)
    let acc' ← I.muladd "mac" acc x v
    dotRow I name base vs (i + 1) acc'

def rows (I : Interp) (name : String) (n : Nat) (v : List I.V) : List Nat → I.M (List I.V)
  | [] => pure []
  | r :: rs => do
    let d ← dotRow I name (r * n) v 0 I.zero
    let ds ← rows I name n v rs
    pure (d :: ds)

def readCol (I : Interp) (a : Nat) : List Nat → I.M (List I.V)
  | [] => pure []
  | i :: is => do
    let x ← I.weight "embedding.weight" (i * 8 + a)
    let xs ← readCol I a is
    pure (x :: xs)

def column (I : Interp) (a : Nat) : I.M (List I.V) := do
  let e ← readCol I a (List.range 4)
  let h ← rows I "linear.weight" 4 e (List.range 4)
  rows I "unembedding.weight" 4 h (List.range 8)

def maxFrom (I : Interp) : I.V → List I.V → I.M I.V
  | acc, [] => pure acc
  | acc, y :: ys => do
    let acc' ← I.max "max" acc y
    maxFrom I acc' ys

def maxList (I : Interp) : List I.V → I.M I.V
  | [] => pure I.zero
  | y :: ys => maxFrom I y ys

def others (m : Nat) : List Nat := (List.range 8).filter fun j => j != m

def maxOthers (I : Interp) (L : List I.V) (a : Nat) : I.M I.V :=
  maxList I ((others a).map fun j => L.getD j I.zero)

structure ColInfo (I : Interp) where
  col : List I.V
  mx : I.V
  cmf : I.V
  dg : I.B

def colInfo (I : Interp) (G : I.B) (a : Nat) : I.M (ColInfo I) := do
  let col ← column I a
  let mx ← maxOthers I col a
  let top := col.getD a I.zero
  let cmf ← I.max "max" mx top
  let d ← I.lt "cmp" mx top
  let dg ← I.band "gate" G d
  pure ⟨col, mx, cmf, dg⟩

def columns (I : Interp) (G : I.B) : List Nat → I.M (List (Nat × ColInfo I))
  | [] => pure []
  | a :: as => do
    let c ← colInfo I G a
    let cs ← columns I G as
    pure ((a, c) :: cs)

def defaultInfo (I : Interp) : ColInfo I := ⟨[], I.zero, I.zero, I.bfalse⟩

inductive Term where
  | diag (m : Nat)
  | pair (a m : Nat)

def Term.inputs : Term → List Input
  | .diag m => [[m, m]]
  | .pair a m => [[a, m], [m, a]]

def runTerm (I : Interp) (cv : List (Nat × ColInfo I)) (G : I.B) : Term → I.M I.N
  | .diag m => pure (I.nscale 1 ((cv.lookup m).getD (defaultInfo I)).dg)
  | .pair a m => do
    let ca := (cv.lookup a).getD (defaultInfo I)
    let cm := (cv.lookup m).getD (defaultInfo I)
    let v1 ← I.add "add" (ca.col.getD m I.zero) (cm.col.getD m I.zero)
    let v2 ← I.add "add" ca.cmf cm.mx
    let b ← I.lt "cmp" v2 v1
    let b' ← I.band "gate" G b
    pure (I.nscale 2 b')

def runTerms (I : Interp) (cv : List (Nat × ColInfo I)) (G : I.B) : List Term → I.M I.N
  | [] => pure I.nzero
  | t :: ts => do
    let n ← runTerm I cv G t
    let ns ← runTerms I cv G ts
    pure (I.nadd n ns)

structure Plan where
  cols : List Nat
  guard : Nat × Nat
  terms : List Term

def guardInputs (g : Nat × Nat) : List Input :=
  if g.1 = g.2 then [[g.1, g.2]] else [[g.1, g.2], [g.2, g.1]]

def shapesOk (I : Interp) : I.M Bool := do
  let s1 ← I.weightShape "embedding.weight"
  let s2 ← I.weightShape "linear.weight"
  let s3 ← I.weightShape "unembedding.weight"
  pure (s1 == [4, 8] && s2 == [4, 4] && s3 == [8, 4])

def runPlan (I : Interp) (p : Plan) : I.M I.N := do
  let ok ← shapesOk I
  if ok then
    let G ← I.single graph task [p.guard.1, p.guard.2]
    let cv ← columns I G p.cols
    let n ← runTerms I cv G p.terms
    pure (I.nadd (I.nscale (guardInputs p.guard).length G) n)
  else pure I.nzero

def thePlan : Plan where
  cols := [0, 1, 2, 4, 6, 7]
  guard := (6, 7)
  terms := [.diag 0, .diag 1, .diag 2, .diag 4, .diag 6, .diag 7,
    .pair 0 1, .pair 1 2, .pair 0 4, .pair 1 4, .pair 2 4, .pair 0 6, .pair 1 6, .pair 4 6,
    .pair 0 7, .pair 1 7, .pair 2 7, .pair 4 7]

def D : Checker := fun I => runPlan I thePlan

/-! ## Plans that count correctly (proof side only) -/

def Plan.inputs (p : Plan) : List Input := guardInputs p.guard ++ p.terms.flatMap Term.inputs

def termOk (cols : List Nat) : Term → Bool
  | .diag m => decide (m < 8) && decide (m ∈ cols)
  | .pair a m => decide (a < m) && decide (m < 8) && decide (a ∈ cols) && decide (m ∈ cols)

def planOk (p : Plan) : Bool :=
  decide (p.guard.1 < 8) && decide (p.guard.2 < 8) && p.terms.all (termOk p.cols) &&
  p.inputs.all (fun x => decide (x ∈ allInputs [8, 8])) && decide p.inputs.Nodup

/-! ## Pure semantics -/

def wget (w : Weights ℚ) (name : String) (i : Nat) : ℚ :=
  match List.lookup name w with
  | some t => t.get i
  | none => 0

def hid (w : Weights ℚ) (a i : Nat) : ℚ :=
  ((List.range 4).map fun k => wget w "linear.weight" (i * 4 + k) * wget w "embedding.weight" (k * 8 + a)).sum

def logit (w : Weights ℚ) (a j : Nat) : ℚ :=
  ((List.range 4).map fun i => wget w "unembedding.weight" (j * 4 + i) * hid w a i).sum

def dotVal (w : Weights ℚ) (name : String) (base : Nat) : List ℚ → Nat → ℚ → ℚ
  | [], _, acc => acc
  | v :: vs, i, acc => dotVal w name base vs (i + 1) (acc + wget w name (base + i) * v)

def rowsVal (w : Weights ℚ) (name : String) (n : Nat) (v : List ℚ) : List Nat → List ℚ
  | [] => []
  | r :: rs => dotVal w name (r * n) v 0 0 :: rowsVal w name n v rs

def colVal (w : Weights ℚ) (a : Nat) : List ℚ :=
  rowsVal w "unembedding.weight" 4
    (rowsVal w "linear.weight" 4 ((List.range 4).map fun i => wget w "embedding.weight" (i * 8 + a))
      (List.range 4))
    (List.range 8)

def maxFromVal : ℚ → List ℚ → ℚ
  | acc, [] => acc
  | acc, y :: ys => maxFromVal (max acc y) ys

def maxListVal : List ℚ → ℚ
  | [] => 0
  | y :: ys => maxFromVal y ys

def maxOthersVal (L : List ℚ) (a : Nat) : ℚ := maxListVal ((others a).map fun j => L.getD j 0)

theorem colVal_getD (w : Weights ℚ) (a j : Nat) (hj : j < 8) : (colVal w a).getD j 0 = logit w a j := by
  have h4 : List.range 4 = [0, 1, 2, 3] := rfl
  have h8 : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := rfl
  simp only [colVal, logit, hid, h4, h8, List.map_cons, List.map_nil, rowsVal, dotVal,
    List.sum_cons, List.sum_nil]
  interval_cases j <;> simp <;> ring

theorem le_maxFromVal_acc : ∀ (ys : List ℚ) (acc : ℚ), acc ≤ maxFromVal acc ys
  | [], _ => le_refl _
  | y :: ys, acc => le_trans (le_max_left acc y) (le_maxFromVal_acc ys _)

theorem le_maxFromVal_mem : ∀ (ys : List ℚ) (acc y : ℚ), y ∈ ys → y ≤ maxFromVal acc ys
  | [], _, _, h => absurd h (List.not_mem_nil)
  | z :: zs, acc, y, h => by
    simp only [maxFromVal]
    rcases List.mem_cons.mp h with rfl | h'
    · exact le_trans (le_max_right acc y) (le_maxFromVal_acc zs _)
    · exact le_maxFromVal_mem zs _ y h'

theorem le_maxOthersVal (L : List ℚ) (a j : Nat) (hj : j < 8) (hne : j ≠ a) :
    L.getD j 0 ≤ maxOthersVal L a := by
  have hmem : L.getD j 0 ∈ (others a).map (fun j => L.getD j 0) :=
    List.mem_map.mpr ⟨j, by simp [others, List.mem_filter, hj, hne], rfl⟩
  unfold maxOthersVal
  generalize hl : (others a).map (fun j => L.getD j 0) = l at hmem
  cases l with
  | nil => simp at hmem
  | cons y ys =>
    simp only [maxListVal]
    rcases List.mem_cons.mp hmem with h1 | h1
    · rw [h1]; exact le_maxFromVal_acc ys y
    · exact le_maxFromVal_mem ys y _ h1

theorem getD_val : ∀ (L : List Q) (j : Nat), (L.map Q.val).getD j 0 = (L.getD j ⟨0⟩).val
  | [], j => by simp
  | x :: xs, 0 => by simp
  | x :: xs, j + 1 => by simp [getD_val xs j]

/-! ## The network on `[a, b]`: column `a` plus column `b` -/

structure WF (w : Weights ℚ) : Prop where
  E : ∃ t, List.lookup "embedding.weight" w = some t ∧ t.shape = [4, 8] ∧ t.data.size = 32
  L : ∃ t, List.lookup "linear.weight" w = some t ∧ t.shape = [4, 4] ∧ t.data.size = 16
  U : ∃ t, List.lookup "unembedding.weight" w = some t ∧ t.shape = [8, 4] ∧ t.data.size = 32

theorem get_map_range {s : List Nat} {n : Nat} {f : Nat → ℚ} {j : Nat} (hj : j < n) :
    Tensor.get ⟨s, (Array.range n).map f⟩ j = f j := by
  simp [Tensor.get, Array.getD_eq_getD_getElem?, hj]

def ind (a v : Nat) : ℚ := if a = v then 1 else 0

theorem ind_sum (f : Nat → ℚ) (a b : Nat) (ha : a < 8) (hb : b < 8) :
    ((List.range 8).map fun v => f v * (ind a v + ind b v)).sum = f a + f b := by
  have h8 : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := rfl
  simp only [h8, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ind]
  interval_cases a <;> interval_cases b <;> simp <;> ring

theorem onehot_spec (a b : Nat) (ha : a < 8) (hb : b < 8) :
    ∃ t : Tensor ℚ, oneHotInput 2 8 [a, b] = some t ∧ t.shape = [1, 2, 8] ∧ t.data.size = 16 ∧
      ∀ i < 16, t.get i = if [a, b].getD (i / 8) 0 = i % 8 then 1 else 0 := by
  simp only [oneHotInput, List.length_cons, List.length_nil, List.all_cons, List.all_nil, ha, hb,
    decide_true, Bool.and_self, beq_self_eq_true, ite_true, Nat.reduceMul, Nat.reduceAdd]
  refine ⟨_, rfl, rfl, by simp, ?_⟩
  intro i hi
  rw [get_map_range hi]

theorem sum_spec (t : Tensor ℚ) (a b : Nat) (hs : t.shape = [1, 2, 8]) (hn : t.data.size = 16)
    (ht : ∀ i < 16, t.get i = if [a, b].getD (i / 8) 0 = i % 8 then 1 else 0) :
    ∃ r, sumOp 1 t = some r ∧ r.shape = [1, 8] ∧ r.data.size = 8 ∧
      ∀ v < 8, r.get v = ind a v + ind b v := by
  have h1 : normDim 1 3 = some 1 := rfl
  have h2 : shapeSize (List.take 1 [1, 2, 8]) = 1 := rfl
  have h3 : shapeSize (List.drop (1 + 1) [1, 2, 8]) = 8 := rfl
  have h4 : ([1, 2, 8] : List Nat).getD 1 0 = 2 := rfl
  have h5 : ([1, 2, 8] : List Nat).eraseIdx 1 = [1, 8] := rfl
  simp only [sumOp, hs, hn, List.length_cons, List.length_nil, Nat.reduceAdd, h1, h2, h3, h4, h5,
    Nat.reduceMul, Nat.one_mul, beq_self_eq_true, ite_true]
  refine ⟨_, rfl, rfl, by simp, ?_⟩
  intro v hv
  rw [get_map_range hv]
  have e1 : v / 8 = 0 := Nat.div_eq_of_lt hv
  have e2 : v % 8 = v := Nat.mod_eq_of_lt hv
  have e3 : (8 + v) / 8 = 1 := by omega
  have e4 : (8 + v) % 8 = v := by omega
  simp only [List.range_succ, List.range_zero, List.nil_append, List.cons_append, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, e1, e2, Nat.zero_mul, Nat.zero_add, Nat.one_mul]
  rw [ht v (by omega), ht (8 + v) (by omega), e1, e2, e3, e4]
  simp [ind]

theorem linearOp_spec (W t : Tensor ℚ) (out inn : Nat) (hWs : W.shape = [out, inn])
    (hWn : W.data.size = out * inn) (hts : t.shape = [1, inn]) (htn : t.data.size = inn) :
    ∃ r, linearOp W none t = some r ∧ r.shape = [1, out] ∧ r.data.size = out ∧
      ∀ j < out, r.get j = ((List.range inn).map fun i => W.get (j * inn + i) * t.get i).sum := by
  have hl : ([1, inn] : List Nat).getLast? = some inn := rfl
  have hd : ([1, inn] : List Nat).dropLast = [1] := rfl
  have hp : shapeSize [1] = 1 := rfl
  simp only [linearOp, hWs, hts, hWn, htn, hl, hd, hp, List.getD_cons_zero, List.getD_cons_succ,
    Nat.one_mul, beq_self_eq_true, Bool.and_self, ite_true]
  refine ⟨_, rfl, rfl, by simp, ?_⟩
  intro j hj
  rw [get_map_range hj]
  simp [Nat.mod_eq_of_lt hj, Nat.div_eq_of_lt hj]

theorem bind_some_iff {α β : Type} {o : Option α} {f : α → Option β} {b : β} :
    o.bind f = some b ↔ ∃ a, o = some a ∧ f a = some b := by
  cases o with
  | none => simp
  | some a => simp

theorem evalOps_cons (g : Graph) (w : Weights ℚ) (x : Input) (op : Op) (ops : List Op)
    (vals : Array (Tensor ℚ)) :
    evalOps g w x (op :: ops) vals = (evalOp g w x vals op).bind fun v => evalOps g w x ops (vals.push v) := by
  simp only [evalOps]
  cases evalOp g w x vals op <;> rfl

theorem evalOps_nil (g : Graph) (w : Weights ℚ) (x : Input) (vals : Array (Tensor ℚ)) :
    evalOps g w x [] vals = some vals := rfl

theorem evalGraph_eq (g : Graph) (w : Weights ℚ) (x : Input) :
    evalGraph g w x = (evalOps g w x g.nodes #[]).bind fun vals => vals[g.output]? := by
  simp only [evalGraph]
  cases evalOps g w x g.nodes #[] <;> rfl

theorem chain {w : Weights ℚ} {x : Input} {E L U : Tensor ℚ} {out : Tensor ℚ}
    (hE : List.lookup "embedding.weight" w = some E)
    (hL : List.lookup "linear.weight" w = some L)
    (hU : List.lookup "unembedding.weight" w = some U)
    (hout : evalGraph graph w x = some out) :
    ∃ t0 t1 t2 t3, oneHotInput 2 8 x = some t0 ∧ sumOp 1 t0 = some t1 ∧ linearOp E none t1 = some t2 ∧
      linearOp L none t2 = some t3 ∧ linearOp U none t3 = some out := by
  rw [evalGraph_eq] at hout
  simp only [Protected.N_max2_tiny_v8_s0_c32.graph, evalOps_cons, evalOps_nil, evalOp,
    List.push_toArray, List.nil_append, List.cons_append, List.getElem?_toArray,
    List.getElem?_cons_zero, List.getElem?_cons_succ, hE, hL, hU, bind_some_iff,
    Option.some.injEq] at hout
  obtain ⟨vals, ⟨t0, h0, t1, h1, t2, h2, t3, h3, t4, h4, hv⟩, hout'⟩ := hout
  subst hv
  simp only [List.getElem?_toArray, List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.some.injEq] at hout'
  subst hout'
  exact ⟨t0, t1, t2, t3, h0, h1, h2, h3, h4⟩

theorem chain_fwd {w : Weights ℚ} {x : Input} {E L U : Tensor ℚ} {t0 t1 t2 t3 t4 : Tensor ℚ}
    (hE : List.lookup "embedding.weight" w = some E)
    (hL : List.lookup "linear.weight" w = some L)
    (hU : List.lookup "unembedding.weight" w = some U)
    (h0 : oneHotInput 2 8 x = some t0) (h1 : sumOp 1 t0 = some t1) (h2 : linearOp E none t1 = some t2)
    (h3 : linearOp L none t2 = some t3) (h4 : linearOp U none t3 = some t4) :
    evalGraph graph w x = some t4 := by
  rw [evalGraph_eq]
  simp only [Protected.N_max2_tiny_v8_s0_c32.graph, evalOps_cons, evalOps_nil, evalOp,
    hE, hL, hU, h0, h1, h2, h3, h4, List.push_toArray, List.nil_append, List.cons_append,
    List.getElem?_toArray, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.bind]

theorem linearOp_size {W t r : Tensor ℚ} (h : linearOp W none t = some r) :
    W.data.size = W.shape.getD 0 0 * W.shape.getD 1 0 := by
  simp only [linearOp] at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact hc.1.1.2
  · cases h

theorem wf_of_single {w : Weights ℚ} {x : Input} {E L U : Tensor ℚ}
    (hE : List.lookup "embedding.weight" w = some E) (hEs : E.shape = [4, 8])
    (hL : List.lookup "linear.weight" w = some L) (hLs : L.shape = [4, 4])
    (hU : List.lookup "unembedding.weight" w = some U) (hUs : U.shape = [8, 4])
    (hs : singleOk graph w task x = true) : WF w := by
  unfold singleOk at hs
  split at hs
  · rename_i out hout
    obtain ⟨t0, t1, t2, t3, -, -, h2, h3, h4⟩ := chain hE hL hU hout
    have e2 := linearOp_size h2
    have e3 := linearOp_size h3
    have e4 := linearOp_size h4
    rw [hEs] at e2
    rw [hLs] at e3
    rw [hUs] at e4
    exact ⟨⟨E, hE, hEs, by simpa using e2⟩, ⟨L, hL, hLs, by simpa using e3⟩,
      ⟨U, hU, hUs, by simpa using e4⟩⟩
  · cases hs

theorem eval_entries (w : Weights ℚ) (hw : WF w) (a b : Nat) (ha : a < 8) (hb : b < 8) :
    ∃ out, evalGraph graph w [a, b] = some out ∧ out.shape = [1, 8] ∧ out.data.size = 8 ∧
      ∀ j < 8, out.get j = logit w a j + logit w b j := by
  obtain ⟨E, hE, hEs, hEn⟩ := hw.E
  obtain ⟨L, hL, hLs, hLn⟩ := hw.L
  obtain ⟨U, hU, hUs, hUn⟩ := hw.U
  obtain ⟨t0, h0, h0s, h0n, h0e⟩ := onehot_spec a b ha hb
  obtain ⟨t1, h1, h1s, h1n, h1e⟩ := sum_spec t0 a b h0s h0n h0e
  obtain ⟨t2, h2, h2s, h2n, h2e⟩ := linearOp_spec E t1 4 8 hEs hEn h1s h1n
  obtain ⟨t3, h3, h3s, h3n, h3e⟩ := linearOp_spec L t2 4 4 hLs hLn h2s h2n
  obtain ⟨t4, h4, h4s, h4n, h4e⟩ := linearOp_spec U t3 8 4 hUs hUn h3s h3n
  refine ⟨t4, chain_fwd hE hL hU h0 h1 h2 h3 h4, h4s, h4n, ?_⟩
  have h4' : List.range 4 = [0, 1, 2, 3] := rfl
  have h2e' : ∀ k < 4, t2.get k = E.get (k * 8 + a) + E.get (k * 8 + b) := by
    intro k hk
    rw [h2e k hk, ← ind_sum (fun v => E.get (k * 8 + v)) a b ha hb]
    apply congrArg List.sum
    apply List.map_congr_left
    intro v hv
    rw [h1e v (List.mem_range.mp hv)]
  have h3e' : ∀ i < 4, t3.get i = hid w a i + hid w b i := by
    intro i hi
    rw [h3e i hi]
    simp only [hid, wget, hL, hE, h4', List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [h2e' 0 (by decide), h2e' 1 (by decide), h2e' 2 (by decide), h2e' 3 (by decide)]
    ring
  intro j hj
  rw [h4e j hj]
  simp only [logit, wget, hU, h4', List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [h3e' 0 (by decide), h3e' 1 (by decide), h3e' 2 (by decide), h3e' 3 (by decide)]
  ring

theorem label_eq (a b : Nat) : task.label [a, b] = max a b := by
  show (maxTask 2 8).label [a, b] = max a b
  simp [maxTask, List.foldl]

theorem singleOk_of_margins (w : Weights ℚ) (hw : WF w) (a b m : Nat) (ha : a < 8) (hb : b < 8)
    (hm : m < 8) (hlab : task.label [a, b] = m)
    (hlt : ∀ j < 8, j ≠ m → logit w a j + logit w b j < logit w a m + logit w b m) :
    singleOk graph w task [a, b] = true := by
  obtain ⟨out, hout, hs, hn, he⟩ := eval_entries w hw a b ha hb
  unfold singleOk
  rw [hout, hlab]
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨by rw [hs, hn], ?_⟩
  apply strictMaxAt_of
  · simp [hn, hm]
  · intro j hj hne
    have hj8 : j < 8 := by simpa [hn] using hj
    have e1 : out.data.toList[j] = out.get j := by
      simp [Tensor.get, Array.getD_eq_getD_getElem?, hn, hj8]
    have e2 : vecGet out.data.toList m = out.get m := by
      simp [vecGet, Tensor.get, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
    rw [e1, e2, he j hj8, he m hm]
    exact hlt j hj8 hne

theorem correct_swap (w : Weights ℚ) (a b : Nat) (h : singleOk graph w task [a, b] = true) :
    Correct graph w task [b, a] :=
  singleOk_correct graph w task [b, a]
    (singleOk_perm (by decide) rfl (List.Perm.swap b a []) h)

theorem diag_correct (w : Weights ℚ) (hw : WF w) (m : Nat) (hm : m < 8) (mx : ℚ)
    (hmx : ∀ j < 8, j ≠ m → logit w m j ≤ mx) (hlt : mx < logit w m m) :
    Correct graph w task [m, m] :=
  singleOk_correct graph w task [m, m] (singleOk_of_margins w hw m m m hm hm hm
    (by rw [label_eq]; simp) fun j hj hne => by
      have := hmx j hj hne; linarith)

theorem pair_correct (w : Weights ℚ) (hw : WF w) (a m : Nat) (ham : a < m) (hm : m < 8) (cmf mx : ℚ)
    (hcmf : ∀ j < 8, logit w a j ≤ cmf) (hmx : ∀ j < 8, j ≠ m → logit w m j ≤ mx)
    (hlt : cmf + mx < logit w a m + logit w m m) :
    Correct graph w task [a, m] ∧ Correct graph w task [m, a] := by
  have hs : singleOk graph w task [a, m] = true :=
    singleOk_of_margins w hw a m m (by omega) hm hm (by rw [label_eq]; omega) fun j hj hne => by
      have h1 := hcmf j hj
      have h2 := hmx j hj hne
      linarith
  exact ⟨singleOk_correct graph w task [a, m] hs, correct_swap w a m hs⟩

/-! ## The partial-correctness relation -/

def Sem {α : Type} (x : CostM α) (env : Env) (P : α → Prop) : Prop :=
  ∀ c a c', x.run env c = some (a, c') → P a

theorem Sem.pure {α : Type} {env : Env} {P : α → Prop} {a : α} (h : P a) :
    Sem (pure a : CostM α) env P := by
  intro c a' c' hr
  rw [CostM.run_pure] at hr
  simp only [Option.some.injEq, Prod.mk.injEq] at hr
  obtain ⟨h1, _⟩ := hr
  subst h1
  exact h

theorem Sem.bind {α β : Type} {env : Env} {x : CostM α} {f : α → CostM β} {P : α → Prop}
    {Q : β → Prop} (hx : Sem x env P) (hf : ∀ a, P a → Sem (f a) env Q) : Sem (x >>= f) env Q := by
  intro c b c' hr
  rw [CostM.run_bind] at hr
  split at hr
  · rename_i a c1 h1
    exact hf a (hx c a c1 h1) c1 b c' hr
  · cases hr

theorem Sem.mono {α : Type} {env : Env} {x : CostM α} {P Q : α → Prop} (hx : Sem x env P)
    (h : ∀ a, P a → Q a) : Sem x env Q :=
  fun c a c' hr => h a (hx c a c' hr)

theorem Sem.weight {env : Env} (name : String) (i : Nat) :
    Sem (CostM.weight name i) env
      (fun v => ∃ t, List.lookup name env.weights = some t ∧ i < t.data.size ∧ v.val = t.get i) := by
  intro c v c' hr
  simp only [CostM.weight] at hr
  split at hr
  · rename_i t ht
    split at hr
    · rename_i hi
      simp only [Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨h1, _⟩ := hr
      subst h1
      refine ⟨t, ht, hi, ?_⟩
      simp [Tensor.get, Array.getD_eq_getD_getElem?, getElem!_pos, hi]
    · cases hr
  · cases hr

theorem Sem.weightShape {env : Env} (name : String) :
    Sem (CostM.weightShape name) env
      (fun s => ∃ t, List.lookup name env.weights = some t ∧ t.shape = s) := by
  intro c v c' hr
  simp only [CostM.weightShape] at hr
  split at hr
  · rename_i t ht
    simp only [Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨h1, _⟩ := hr
    subst h1
    exact ⟨t, ht, rfl⟩
  · cases hr

theorem Sem.muladd {env : Env} (cat : String) (acc a b : Q) :
    Sem (CostM.qmuladd cat acc a b) env (fun v => v.val = acc.val + a.val * b.val) := by
  intro c v c' hr
  simp only [CostM.qmuladd, Option.some.injEq, Prod.mk.injEq] at hr
  obtain ⟨h1, _⟩ := hr
  subst h1
  rfl

theorem Sem.add {env : Env} (cat : String) (a b : Q) :
    Sem (CostM.qadd cat a b) env (fun v => v.val = a.val + b.val) := by
  intro c v c' hr
  simp only [CostM.qadd, Option.some.injEq, Prod.mk.injEq] at hr
  obtain ⟨h1, _⟩ := hr
  subst h1
  rfl

theorem Sem.max {env : Env} (cat : String) (a b : Q) :
    Sem (CostM.qmax cat a b) env (fun v => v.val = max a.val b.val) := by
  intro c v c' hr
  simp only [CostM.qmax, Option.some.injEq, Prod.mk.injEq] at hr
  obtain ⟨h1, _⟩ := hr
  subst h1
  rfl

theorem Sem.lt {env : Env} (cat : String) (a b : Q) :
    Sem (CostM.qlt cat a b) env (fun r => r = decide (a.val < b.val)) := by
  intro c v c' hr
  simp only [CostM.qlt, Option.some.injEq, Prod.mk.injEq] at hr
  obtain ⟨h1, _⟩ := hr
  subst h1
  rfl

theorem Sem.band {env : Env} (cat : String) (a b : Bool) :
    Sem (Interp.counting.band cat a b) env (fun r => r = (a && b)) := by
  intro c v c' hr
  rw [Interp.counting_band_run] at hr
  simp only [Option.some.injEq, Prod.mk.injEq] at hr
  obtain ⟨h1, _⟩ := hr
  subst h1
  rfl

theorem Sem.single {env : Env} (g : Graph) (task : Task) (x : Input) :
    Sem (CostM.single g task x) env (fun b => b = true → singleOk g env.weights task x = true) :=
  fun c b c' hr hb => by
    subst hb
    exact CostM.single_spec hr

/-! ## Semantics of the helpers -/

theorem dotRow_sem (env : Env) (name : String) (base : Nat) :
    ∀ (vs : List Q) (i : Nat) (acc : Q),
    Sem (dotRow Interp.counting name base vs i acc) env
      (fun v => v.val = dotVal env.weights name base (vs.map Q.val) i acc.val)
  | [], i, acc => by
    simp only [dotRow, List.map_nil, dotVal, Interp.counting_pure]
    exact Sem.pure rfl
  | v :: vs, i, acc => by
    simp only [dotRow, Interp.counting_bind, List.map_cons, dotVal]
    refine Sem.bind (Sem.weight name (base + i)) fun x hx => ?_
    obtain ⟨t, ht, _, hx⟩ := hx
    refine Sem.bind (Sem.muladd _ _ _ _) fun acc' hacc' => ?_
    refine Sem.mono (dotRow_sem env name base vs (i + 1) acc') fun r hr => ?_
    rw [hr, hacc', hx]
    simp [wget, ht]

theorem rows_sem (env : Env) (name : String) (n : Nat) (v : List Q) :
    ∀ (rs : List Nat),
    Sem (rows Interp.counting name n v rs) env
      (fun ds => ds.map Q.val = rowsVal env.weights name n (v.map Q.val) rs)
  | [] => by
    simp only [rows, Interp.counting_pure, rowsVal]
    exact Sem.pure rfl
  | r :: rs => by
    simp only [rows, Interp.counting_bind, Interp.counting_pure, rowsVal]
    refine Sem.bind (dotRow_sem env name (r * n) v 0 Interp.counting.zero) fun d hd => ?_
    refine Sem.bind (rows_sem env name n v rs) fun ds hds => ?_
    refine Sem.pure ?_
    simp only [List.map_cons, hds, hd]

theorem readCol_sem (env : Env) (a : Nat) :
    ∀ (is : List Nat),
    Sem (readCol Interp.counting a is) env
      (fun xs => xs.map Q.val = is.map fun i => wget env.weights "embedding.weight" (i * 8 + a))
  | [] => by
    simp only [readCol, Interp.counting_pure, List.map_nil]
    exact Sem.pure rfl
  | i :: is => by
    simp only [readCol, Interp.counting_bind, Interp.counting_pure, List.map_cons]
    refine Sem.bind (Sem.weight _ _) fun x hx => ?_
    obtain ⟨t, ht, _, hx⟩ := hx
    refine Sem.bind (readCol_sem env a is) fun xs hxs => ?_
    refine Sem.pure ?_
    simp only [List.map_cons, hxs, hx]
    simp [wget, ht]

theorem column_sem (env : Env) (a : Nat) :
    Sem (column Interp.counting a) env (fun col => col.map Q.val = colVal env.weights a) := by
  simp only [column, Interp.counting_bind]
  refine Sem.bind (readCol_sem env a _) fun e he => ?_
  refine Sem.bind (rows_sem env _ _ _ _) fun h hh => ?_
  refine Sem.mono (rows_sem env _ _ _ _) fun col hcol => ?_
  rw [hcol, hh, he]
  rfl

theorem maxFrom_sem (env : Env) : ∀ (ys : List Q) (acc : Q),
    Sem (maxFrom Interp.counting acc ys) env (fun v => v.val = maxFromVal acc.val (ys.map Q.val))
  | [], acc => by
    simp only [maxFrom, maxFromVal, List.map_nil, Interp.counting_pure]
    exact Sem.pure rfl
  | y :: ys, acc => by
    simp only [maxFrom, Interp.counting_bind, List.map_cons, maxFromVal]
    refine Sem.bind (Sem.max _ _ _) fun acc' hacc' => ?_
    refine Sem.mono (maxFrom_sem env ys acc') fun r hr => ?_
    rw [hr, hacc']

theorem maxList_sem (env : Env) : ∀ (ys : List Q),
    Sem (maxList Interp.counting ys) env (fun v => v.val = maxListVal (ys.map Q.val))
  | [] => by
    simp only [maxList, maxListVal, List.map_nil, Interp.counting_pure]
    exact Sem.pure rfl
  | y :: ys => by
    simp only [maxList, maxListVal, List.map_cons]
    exact maxFrom_sem env ys y

theorem maxOthers_sem (env : Env) (L : List Q) (a : Nat) :
    Sem (maxOthers Interp.counting L a) env (fun v => v.val = maxOthersVal (L.map Q.val) a) := by
  simp only [maxOthers, maxOthersVal]
  refine Sem.mono (maxList_sem env _) fun v hv => ?_
  rw [hv]
  simp [List.map_map, Function.comp_def, getD_val]

def InfoOk (w : Weights ℚ) (G : Bool) (a : Nat) (ci : ColInfo Interp.counting) : Prop :=
  ci.col.map Q.val = colVal w a ∧ ci.mx.val = maxOthersVal (colVal w a) a ∧
  ci.cmf.val = max ci.mx.val ((colVal w a).getD a 0) ∧
  (ci.dg = true → G = true ∧ ci.mx.val < (colVal w a).getD a 0)

def CvOk (w : Weights ℚ) (G : Bool) (cols : List Nat) (cv : List (Nat × ColInfo Interp.counting)) : Prop :=
  ∀ a ∈ cols, ∃ ci, cv.lookup a = some ci ∧ InfoOk w G a ci

theorem colInfo_sem (env : Env) (G : Bool) (a : Nat) :
    Sem (colInfo Interp.counting G a) env (fun ci => InfoOk env.weights G a ci) := by
  simp only [colInfo, Interp.counting_bind, Interp.counting_pure]
  refine Sem.bind (column_sem env a) fun col hcol => ?_
  refine Sem.bind (maxOthers_sem env col a) fun mx hmx => ?_
  refine Sem.bind (Sem.max _ _ _) fun cmf hcmf => ?_
  refine Sem.bind (Sem.lt _ _ _) fun d hd => ?_
  refine Sem.bind (Sem.band _ _ _) fun dg hdg => ?_
  refine Sem.pure ?_
  have hget : (col.getD a Interp.counting.zero).val = (colVal env.weights a).getD a 0 := by
    rw [← hcol, getD_val]
  refine ⟨hcol, by rw [hmx, hcol], by rw [hcmf, hget], ?_⟩
  intro h
  rw [hdg] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hG, hd'⟩ := h
  rw [hd] at hd'
  simp only [decide_eq_true_eq] at hd'
  rw [hget] at hd'
  exact ⟨hG, hd'⟩

theorem columns_sem (env : Env) (G : Bool) : ∀ (cols : List Nat),
    Sem (columns Interp.counting G cols) env (fun cv => CvOk env.weights G cols cv)
  | [] => by
    simp only [columns, Interp.counting_pure]
    exact Sem.pure (by intro a ha; simp at ha)
  | a :: as => by
    simp only [columns, Interp.counting_bind, Interp.counting_pure]
    refine Sem.bind (colInfo_sem env G a) fun c hc => ?_
    refine Sem.bind (columns_sem env G as) fun cs hcs => ?_
    refine Sem.pure ?_
    intro b hb
    by_cases hba : b = a
    · subst hba
      exact ⟨c, by simp [List.lookup], hc⟩
    · have hb' : b ∈ as := by
        rcases List.mem_cons.mp hb with h | h
        · exact absurd h hba
        · exact h
      obtain ⟨ci, h1, h2⟩ := hcs b hb'
      refine ⟨ci, ?_, h2⟩
      have hb2 : (b == a) = false := beq_eq_false_iff_ne.mpr hba
      simp [List.lookup, h1, hb2]

theorem info_mx {w : Weights ℚ} {G : Bool} {a : Nat} {ci : ColInfo Interp.counting}
    (h : InfoOk w G a ci) : ∀ j < 8, j ≠ a → logit w a j ≤ ci.mx.val := by
  intro j hj hne
  rw [h.2.1, ← colVal_getD w a j hj]
  exact le_maxOthersVal _ a j hj hne

theorem info_cmf {w : Weights ℚ} {G : Bool} {a : Nat} {ci : ColInfo Interp.counting} (ha : a < 8)
    (h : InfoOk w G a ci) : ∀ j < 8, logit w a j ≤ ci.cmf.val := by
  intro j hj
  rw [h.2.2.1]
  by_cases hja : j = a
  · subst hja
    rw [colVal_getD w j j hj]
    exact le_max_right _ _
  · exact le_trans (info_mx h j hj hja) (le_max_left _ _)

theorem info_col {w : Weights ℚ} {G : Bool} {a : Nat} {ci : ColInfo Interp.counting}
    (h : InfoOk w G a ci) (m : Nat) (hm : m < 8) :
    (ci.col.getD m Interp.counting.zero).val = logit w a m := by
  rw [← colVal_getD w a m hm, ← h.1, getD_val]

open Classical in
theorem runTerm_sem (env : Env) (cols : List Nat) (cv : List (Nat × ColInfo Interp.counting)) (G : Bool)
    (hcv : CvOk env.weights G cols cv) (hwf : G = true → WF env.weights) :
    ∀ (t : Term), termOk cols t = true →
    Sem (runTerm Interp.counting cv G t) env
      (fun n => n ≤ t.inputs.countP fun x => decide (Correct graph env.weights task x))
  | .diag m, ht => by
    simp only [termOk, Bool.and_eq_true, decide_eq_true_eq] at ht
    obtain ⟨hm, hmem⟩ := ht
    obtain ⟨ci, hci, hok⟩ := hcv m hmem
    simp only [runTerm, Interp.counting_pure, hci, Option.getD_some, Term.inputs]
    refine Sem.pure ?_
    show cond ci.dg 1 0 ≤ _
    cases hdg : ci.dg with
    | false => exact Nat.zero_le _
    | true =>
      obtain ⟨hG, hlt⟩ := hok.2.2.2 hdg
      rw [colVal_getD env.weights m m hm] at hlt
      have hc : Correct graph env.weights task [m, m] :=
        diag_correct env.weights (hwf hG) m hm ci.mx.val (info_mx hok) hlt
      simp [hc]
  | .pair a m, ht => by
    simp only [termOk, Bool.and_eq_true, decide_eq_true_eq] at ht
    obtain ⟨⟨⟨ham, hm⟩, hamem⟩, hmmem⟩ := ht
    obtain ⟨ca, hca, hoka⟩ := hcv a hamem
    obtain ⟨cm, hcm, hokm⟩ := hcv m hmmem
    simp only [runTerm, Interp.counting_bind, Interp.counting_pure, hca, hcm, Option.getD_some,
      Term.inputs]
    refine Sem.bind (Sem.add _ _ _) fun v1 hv1 => ?_
    refine Sem.bind (Sem.add _ _ _) fun v2 hv2 => ?_
    refine Sem.bind (Sem.lt _ _ _) fun b hb => ?_
    refine Sem.bind (Sem.band _ _ _) fun b' hb' => ?_
    refine Sem.pure ?_
    show cond b' 2 0 ≤ _
    rw [hb', hb]
    cases G with
    | false => exact Nat.zero_le _
    | true =>
      by_cases hlt : v2.val < v1.val
      · have hd : decide (v2.val < v1.val) = true := decide_eq_true hlt
        rw [hv1, hv2, info_col hoka m hm, info_col hokm m hm] at hlt
        have ha8 : a < 8 := by omega
        obtain ⟨hc1, hc2⟩ := pair_correct env.weights (hwf rfl) a m ham hm ca.cmf.val cm.mx.val
          (info_cmf ha8 hoka) (info_mx hokm) hlt
        rw [hd]
        simp [hc1, hc2]
      · have hd : decide (v2.val < v1.val) = false := decide_eq_false hlt
        rw [hd]
        exact Nat.zero_le _

open Classical in
theorem runTerms_sem (env : Env) (cols : List Nat) (cv : List (Nat × ColInfo Interp.counting)) (G : Bool)
    (hcv : CvOk env.weights G cols cv) (hwf : G = true → WF env.weights) :
    ∀ (ts : List Term), (∀ t ∈ ts, termOk cols t = true) →
    Sem (runTerms Interp.counting cv G ts) env
      (fun n => n ≤ (ts.flatMap Term.inputs).countP fun x => decide (Correct graph env.weights task x))
  | [], _ => by
    simp only [runTerms, Interp.counting_pure, List.flatMap_nil, List.countP_nil]
    exact Sem.pure (Nat.le_refl 0)
  | t :: ts, hts => by
    simp only [runTerms, Interp.counting_bind, Interp.counting_pure, List.flatMap_cons,
      List.countP_append]
    refine Sem.bind (runTerm_sem env cols cv G hcv hwf t (hts t (by simp))) fun n hn => ?_
    refine Sem.bind (runTerms_sem env cols cv G hcv hwf ts (fun t' ht' => hts t' (by simp [ht'])))
      fun ns hns => ?_
    refine Sem.pure ?_
    exact Nat.add_le_add hn hns

theorem shapesOk_sem (env : Env) :
    Sem (shapesOk Interp.counting) env (fun ok => ok = true →
      ∃ E, List.lookup "embedding.weight" env.weights = some E ∧ E.shape = [4, 8] ∧
      ∃ L, List.lookup "linear.weight" env.weights = some L ∧ L.shape = [4, 4] ∧
      ∃ U, List.lookup "unembedding.weight" env.weights = some U ∧ U.shape = [8, 4]) := by
  simp only [shapesOk, Interp.counting_bind, Interp.counting_pure]
  refine Sem.bind (Sem.weightShape _) fun s1 h1 => ?_
  refine Sem.bind (Sem.weightShape _) fun s2 h2 => ?_
  refine Sem.bind (Sem.weightShape _) fun s3 h3 => ?_
  refine Sem.pure ?_
  intro h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨e1, e2⟩, e3⟩ := h
  obtain ⟨E, hE, hEs⟩ := h1
  obtain ⟨L, hL, hLs⟩ := h2
  obtain ⟨U, hU, hUs⟩ := h3
  exact ⟨E, hE, by rw [hEs, e1], L, hL, by rw [hLs, e2], U, hU, by rw [hUs, e3]⟩

open Classical in
theorem guard_le (env : Env) (g : Nat × Nat) (G : Bool)
    (hG : G = true → singleOk graph env.weights task [g.1, g.2] = true) :
    cond G (guardInputs g).length 0 ≤
      (guardInputs g).countP fun x => decide (Correct graph env.weights task x) := by
  cases G with
  | false => simp
  | true =>
    simp only [Bool.cond_true]
    apply le_of_eq
    symm
    rw [List.countP_eq_length]
    intro x hx
    simp only [decide_eq_true_eq]
    have hs := hG rfl
    unfold guardInputs at hx
    split at hx
    · simp only [List.mem_singleton] at hx
      subst hx
      exact singleOk_correct _ _ _ _ hs
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact singleOk_correct _ _ _ _ hs
      · exact correct_swap _ _ _ hs

open Classical in
theorem runPlan_sound (env : Env) (p : Plan) (hp : planOk p = true) :
    Sem (runPlan Interp.counting p) env (fun n => n ≤ numCorrect graph env.weights task) := by
  simp only [planOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hp
  obtain ⟨⟨⟨⟨_, _⟩, hterms⟩, hsub⟩, hnodup⟩ := hp
  simp only [runPlan, Interp.counting_bind, Interp.counting_pure]
  refine Sem.bind (shapesOk_sem env) fun ok hok => ?_
  cases ok with
  | false =>
    rw [if_neg Bool.false_ne_true]
    exact Sem.pure (Nat.zero_le _)
  | true =>
    rw [if_pos rfl]
    obtain ⟨E, hE, hEs, L, hL, hLs, U, hU, hUs⟩ := hok rfl
    refine Sem.bind (Sem.single _ _ _) fun G hG => ?_
    have hwf : G = true → WF env.weights := fun h => wf_of_single hE hEs hL hLs hU hUs (hG h)
    refine Sem.bind (columns_sem env G p.cols) fun cv hcv => ?_
    refine Sem.bind (runTerms_sem env p.cols cv G hcv hwf p.terms hterms) fun n hn => ?_
    refine Sem.pure ?_
    show Nat.add (cond G (guardInputs p.guard).length 0) n ≤ _
    have hguard := guard_le env p.guard G hG
    have hall : p.inputs.Subperm (allInputs task.space) := by
      apply List.Nodup.subperm hnodup
      intro x hx
      exact hsub x hx
    calc Nat.add (cond G (guardInputs p.guard).length 0) n
        ≤ ((guardInputs p.guard).countP fun x => decide (Correct graph env.weights task x)) +
          ((p.terms.flatMap Term.inputs).countP fun x => decide (Correct graph env.weights task x)) :=
          Nat.add_le_add hguard hn
      _ = p.inputs.countP fun x => decide (Correct graph env.weights task x) := by
          rw [Plan.inputs, List.countP_append]
      _ ≤ (allInputs task.space).countP fun x => decide (Correct graph env.weights task x) :=
          hall.countP_le _
      _ = numCorrect graph env.weights task := rfl

theorem D_sound : ∀ (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),
    CostM.exec (D Interp.counting) ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task := by
  intro w c n cost h
  exact runPlan_sound ⟨w, c⟩ thePlan (by decide) [] n cost h

/-! ## Specific layer -/

theorem D_instance : CostM.billed (D Interp.counting) ⟨weights, cert⟩ = some (32, 453) := by
  decide +kernel

theorem performance : Target := by
  show claimedCount ≤ numCorrect graph weights task
  obtain ⟨cost, h⟩ := CostM.exec_of_billed D_instance
  exact D_sound weights cert 32 cost h

end Candidate.Col32
