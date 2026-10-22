import Protected.N_max2_tiny_v8_s0_c64
import CompactCheck.Soundness
import CompactCheck.IntervalSound
import CompactCheck.CountedOps
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace Candidate.ColFull

open CompactCheck Protected.N_max2_tiny_v8_s0_c64

/-! ## General layer: the checker -/

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

def columns (I : Interp) : List Nat → I.M (List (Nat × List I.V))
  | [] => pure []
  | a :: as => do
    let c ← column I a
    let cs ← columns I as
    pure ((a, c) :: cs)

def addLists (I : Interp) : List I.V → List I.V → I.M (List I.V)
  | x :: xs, y :: ys => do
    let z ← I.add "add" x y
    let zs ← addLists I xs ys
    pure (z :: zs)
  | _, _ => pure []

def maxFrom (I : Interp) : I.V → List I.V → I.M I.V
  | acc, [] => pure acc
  | acc, y :: ys => do
    let acc' ← I.max "max" acc y
    maxFrom I acc' ys

def others (m : Nat) : List Nat := (List.range 8).filter fun j => j != m

def strictAt (I : Interp) (L : List I.V) (m : Nat) : I.M I.B :=
  match (others m).map (fun j => L.getD j I.zero) with
  | [] => pure I.bfalse
  | y :: ys => do
    let mx ← maxFrom I y ys
    I.lt "cmp" mx (L.getD m I.zero)

inductive Term where
  | single (a b : Nat)
  | diag (m : Nat)
  | pair (a m : Nat)

def Term.inputs : Term → List Input
  | .single a b => if a = b then [[a, b]] else [[a, b], [b, a]]
  | .diag m => [[m, m]]
  | .pair a m => [[a, m], [m, a]]

def Term.valid (cols : List Nat) : Term → Bool
  | .single a b => a < 8 && b < 8
  | .diag m => m < 8 && cols.contains m
  | .pair a m => a < m && m < 8 && cols.contains a && cols.contains m

def runTerm (I : Interp) (cols : List Nat) (cv : List (Nat × List I.V)) (G : I.B) (t : Term) : I.M I.N :=
  if t.valid cols then
    match t with
    | .single a b => do
      let ok ← I.single graph task [a, b]
      pure (I.nscale (Term.single a b).inputs.length ok)
    | .diag m => do
      let b ← strictAt I ((cv.lookup m).getD []) m
      let b' ← I.band "gate" G b
      pure (I.nscale 1 b')
    | .pair a m => do
      let L ← addLists I ((cv.lookup a).getD []) ((cv.lookup m).getD [])
      let b ← strictAt I L m
      let b' ← I.band "gate" G b
      pure (I.nscale 2 b')
  else pure I.nzero

def runTerms (I : Interp) (cols : List Nat) (cv : List (Nat × List I.V)) (G : I.B) : List Term → I.M I.N
  | [] => pure I.nzero
  | t :: ts => do
    let n ← runTerm I cols cv G t
    let ns ← runTerms I cols cv G ts
    pure (I.nadd n ns)

structure Plan where
  cols : List Nat
  guard : Nat × Nat
  terms : List Term

def guardInputs (g : Nat × Nat) : List Input :=
  if g.1 < 8 && g.2 < 8 then (if g.1 = g.2 then [[g.1, g.2]] else [[g.1, g.2], [g.2, g.1]]) else []

def shapesOk (I : Interp) : I.M Bool := do
  let s1 ← I.weightShape "embedding.weight"
  let s2 ← I.weightShape "linear.weight"
  let s3 ← I.weightShape "unembedding.weight"
  pure (s1 == [4, 8] && s2 == [4, 4] && s3 == [8, 4])

def runPlan (I : Interp) (p : Plan) : I.M I.N := do
  let ok ← shapesOk I
  if ok then
    let G ← I.single graph task [p.guard.1, p.guard.2]
    let cv ← columns I p.cols
    let n ← runTerms I p.cols cv G p.terms
    pure (I.nadd (I.nscale (guardInputs p.guard).length G) n)
  else pure I.nzero

def pairTerms (cols : List Nat) : List Term :=
  cols.flatMap fun m => (cols.filter fun a => a < m).map fun a => Term.pair a m

def diagTerms (cols : List Nat) : List Term := cols.map Term.diag

def fullPlan : Plan where
  cols := List.range 8
  guard := (6, 7)
  terms := diagTerms (List.range 8) ++
    (pairTerms (List.range 8)).filter (fun t => match t with | .pair 6 7 => false | _ => true)

def D : Checker := fun I => runPlan I fullPlan

/-! ## Pure semantics -/

def wget (w : Weights ℚ) (name : String) (i : Nat) : ℚ :=
  match List.lookup name w with
  | some t => t.get i
  | none => 0

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

def addVals : List ℚ → List ℚ → List ℚ
  | x :: xs, y :: ys => (x + y) :: addVals xs ys
  | _, _ => []

def maxFromVal : ℚ → List ℚ → ℚ
  | acc, [] => acc
  | acc, y :: ys => maxFromVal (max acc y) ys

def strictVal (Qv : List ℚ) (m : Nat) : Bool :=
  match (others m).map (fun j => Qv.getD j 0) with
  | [] => false
  | y :: ys => decide (maxFromVal y ys < Qv.getD m 0)

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

theorem columns_sem (env : Env) :
    ∀ (cols : List Nat),
    Sem (columns Interp.counting cols) env
      (fun cv => ∀ a ∈ cols, ∃ ca, cv.lookup a = some ca ∧ ca.map Q.val = colVal env.weights a)
  | [] => by
    simp only [columns, Interp.counting_pure]
    exact Sem.pure (by simp)
  | a :: as => by
    simp only [columns, Interp.counting_bind, Interp.counting_pure]
    refine Sem.bind (column_sem env a) fun c hc => ?_
    refine Sem.bind (columns_sem env as) fun cs hcs => ?_
    refine Sem.pure ?_
    intro b hb
    by_cases hba : b = a
    · subst hba
      exact ⟨c, by simp [List.lookup], hc⟩
    · have hb' : b ∈ as := by
        cases List.mem_cons.mp hb with
        | inl h => exact absurd h hba
        | inr h => exact h
      obtain ⟨ca, h1, h2⟩ := hcs b hb'
      refine ⟨ca, ?_, h2⟩
      have hbeq : (b == a) = false := beq_eq_false_iff_ne.mpr hba
      simp [List.lookup, hbeq, h1]

theorem addLists_sem (env : Env) :
    ∀ (xs ys : List Q),
    Sem (addLists Interp.counting xs ys) env
      (fun zs => zs.map Q.val = addVals (xs.map Q.val) (ys.map Q.val))
  | x :: xs, y :: ys => by
    simp only [addLists, Interp.counting_bind, Interp.counting_pure, List.map_cons, addVals]
    refine Sem.bind (Sem.add _ _ _) fun z hz => ?_
    refine Sem.bind (addLists_sem env xs ys) fun zs hzs => ?_
    refine Sem.pure ?_
    simp only [List.map_cons, hz, hzs]
  | [], ys => by
    simp only [addLists, Interp.counting_pure, List.map_nil, addVals]
    exact Sem.pure rfl
  | x :: xs, [] => by
    simp only [addLists, Interp.counting_pure, List.map_nil, List.map_cons, addVals]
    exact Sem.pure rfl

theorem maxFrom_sem (env : Env) :
    ∀ (acc : Q) (ys : List Q),
    Sem (maxFrom Interp.counting acc ys) env (fun r => r.val = maxFromVal acc.val (ys.map Q.val))
  | acc, [] => by
    simp only [maxFrom, Interp.counting_pure, List.map_nil, maxFromVal]
    exact Sem.pure rfl
  | acc, y :: ys => by
    simp only [maxFrom, Interp.counting_bind, List.map_cons, maxFromVal]
    refine Sem.bind (Sem.max _ _ _) fun acc' hacc' => ?_
    refine Sem.mono (maxFrom_sem env acc' ys) fun r hr => ?_
    rw [hr, hacc']

theorem getD_map_val (L : List Q) (j : Nat) :
    (L.map Q.val).getD j 0 = (L.getD j Interp.counting.zero).val := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases L[j]? <;> rfl

theorem strictAt_sem (env : Env) (L : List Q) (m : Nat) :
    Sem (strictAt Interp.counting L m) env (fun b => b = strictVal (L.map Q.val) m) := by
  unfold strictAt strictVal
  have hmap : (others m).map (fun j => (L.map Q.val).getD j 0) =
      ((others m).map (fun j => L.getD j Interp.counting.zero)).map Q.val := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro j _
    exact getD_map_val L j
  rw [hmap]
  cases h : (others m).map (fun j => L.getD j Interp.counting.zero) with
  | nil =>
    simp only [List.map_nil, Interp.counting_pure]
    exact Sem.pure rfl
  | cons y ys =>
    simp only [List.map_cons, Interp.counting_bind]
    refine Sem.bind (maxFrom_sem env y ys) fun mx hmx => ?_
    refine Sem.mono (Sem.lt _ _ _) fun r hr => ?_
    rw [hr, hmx, getD_map_val]

theorem shapesOk_sem (env : Env) :
    Sem (shapesOk Interp.counting) env (fun ok => ok = true → ∃ We Wl Wu : Tensor ℚ,
      List.lookup "embedding.weight" env.weights = some We ∧ We.shape = [4, 8] ∧
      List.lookup "linear.weight" env.weights = some Wl ∧ Wl.shape = [4, 4] ∧
      List.lookup "unembedding.weight" env.weights = some Wu ∧ Wu.shape = [8, 4]) := by
  simp only [shapesOk, Interp.counting_bind, Interp.counting_pure]
  refine Sem.bind (Sem.weightShape _) fun s1 hs1 => ?_
  obtain ⟨We, hWe, hs1⟩ := hs1
  refine Sem.bind (Sem.weightShape _) fun s2 hs2 => ?_
  obtain ⟨Wl, hWl, hs2⟩ := hs2
  refine Sem.bind (Sem.weightShape _) fun s3 hs3 => ?_
  obtain ⟨Wu, hWu, hs3⟩ := hs3
  refine Sem.pure fun h => ?_
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨We, Wl, Wu, hWe, hs1.trans h.1.1, hWl, hs2.trans h.1.2, hWu, hs3.trans h.2⟩

/-! ## The network, evaluated symbolically -/

def WF (w : Weights ℚ) : Prop := ∃ We Wl Wu : Tensor ℚ,
  List.lookup "embedding.weight" w = some We ∧ We.shape = [4, 8] ∧ We.data.size = 32 ∧
  List.lookup "linear.weight" w = some Wl ∧ Wl.shape = [4, 4] ∧ Wl.data.size = 16 ∧
  List.lookup "unembedding.weight" w = some Wu ∧ Wu.shape = [8, 4] ∧ Wu.data.size = 32

theorem getD_map_range {α : Type} (n : Nat) (f : Nat → α) (j : Nat) (hj : j < n) (d : α) :
    ((Array.range n).map f).getD j d = f j := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  have hj' : j < (Array.range n).size := by simpa using hj
  rw [Array.getElem?_eq_getElem hj']
  simp [Array.getElem_range]

theorem get_mk (s : List Nat) (d : Array ℚ) (i : Nat) : Tensor.get ⟨s, d⟩ i = d.getD i 0 := rfl

def OH (a b : Nat) : Tensor ℚ :=
  ⟨[1, 2, 8], (Array.range 16).map fun j => if [a, b].getD (j / 8) 0 = j % 8 then 1 else 0⟩

theorem oneHot_eq (a b : Nat) (ha : a < 8) (hb : b < 8) :
    (oneHotInput 2 8 [a, b] : Option (Tensor ℚ)) = some (OH a b) := by
  simp [oneHotInput, ha, hb, OH]

theorem OH_get (a b : Nat) (j : Nat) (hj : j < 16) :
    (OH a b).get j = if [a, b].getD (j / 8) 0 = j % 8 then 1 else 0 := by
  rw [OH, get_mk, getD_map_range 16 _ j hj]

theorem sum_eq (a b : Nat) (ha : a < 8) (hb : b < 8) :
    ∃ S : Tensor ℚ, sumOp 1 (OH a b) = some S ∧ S.shape = [1, 8] ∧ S.data.size = 8 ∧
      ∀ i < 8, S.get i = (if a = i then 1 else 0) + (if b = i then 1 else 0) := by
  have hsh : (OH a b).shape = [1, 2, 8] := rfl
  have hsz : (OH a b).data.size = 16 := by simp [OH]
  have hn : normDim 1 ([1, 2, 8] : List Nat).length = some 1 := by decide
  refine ⟨⟨[1, 8], (Array.range 8).map fun j =>
    ((List.range 2).map fun k => (OH a b).get ((j / 8 * 2 + k) * 8 + j % 8)).sum⟩, ?_, rfl, by simp, ?_⟩
  · simp only [sumOp, hsh, hn, hsz]
    rfl
  · intro i hi
    rw [get_mk, getD_map_range 8 _ i hi]
    have r2 : List.range 2 = [0, 1] := rfl
    rw [r2]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.div_eq_of_lt hi,
      Nat.mod_eq_of_lt hi]
    have e0 : (0 * 2 + 0) * 8 + i = i := by omega
    have e1 : (0 * 2 + 1) * 8 + i = 8 + i := by omega
    rw [e0, e1, OH_get a b i (by omega), OH_get a b (8 + i) (by omega)]
    have h1 : (8 + i) / 8 = 1 := by omega
    have h2 : (8 + i) % 8 = i := by omega
    simp only [Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi, h1, h2, List.getD_cons_zero, List.getD_cons_succ]
    ring

theorem linear_vec (W t : Tensor ℚ) (out inn : Nat) (hW : W.shape = [out, inn])
    (hWs : W.data.size = out * inn) (ht : t.shape = [1, inn]) (hts : t.data.size = inn) :
    ∃ r : Tensor ℚ, linearOp W none t = some r ∧ r.shape = [1, out] ∧ r.data.size = out ∧
      ∀ j < out, r.get j = ((List.range inn).map fun i => W.get (j * inn + i) * t.get i).sum := by
  have hlast : ([1, inn] : List Nat).getLast? = some inn := rfl
  have hdrop : ([1, inn] : List Nat).dropLast = [1] := rfl
  refine ⟨⟨[1, out], (Array.range out).map fun j =>
    ((List.range inn).map fun i => W.get (j % out * inn + i) * t.get (j / out * inn + i)).sum + 0⟩,
    ?_, rfl, by simp, ?_⟩
  · simp only [linearOp, hW, ht, hWs, hts, hlast, hdrop, List.getD_cons_zero, List.getD_cons_succ,
      shapeSize, List.foldr, Nat.mul_one, Nat.one_mul, beq_self_eq_true, Bool.and_true, Bool.and_self,
      List.singleton_append]
    rfl
  · intro j hj
    rw [get_mk, getD_map_range out _ j hj]
    simp [Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj]

theorem evalOps_cons {g : Graph} {w : Weights ℚ} {x : Input} {op : Op} {ops : List Op}
    {vals out : Array (Tensor ℚ)} (h : evalOps g w x (op :: ops) vals = some out) :
    ∃ v, evalOp g w x vals op = some v ∧ evalOps g w x ops (vals.push v) = some out := by
  simp only [evalOps] at h
  split at h
  · rename_i v hv
    exact ⟨v, hv, h⟩
  · cases h

theorem evalOps_cons_of {g : Graph} {w : Weights ℚ} {x : Input} {op : Op} {ops : List Op}
    {vals : Array (Tensor ℚ)} {v : Tensor ℚ} (hv : evalOp g w x vals op = some v) :
    evalOps g w x (op :: ops) vals = evalOps g w x ops (vals.push v) := by
  simp [evalOps, hv]

theorem push1 {α : Type} (x : α) : (#[].push x)[0]? = some x := rfl
theorem push2 {α : Type} (x y : α) : ((#[].push x).push y)[1]? = some y := rfl
theorem push3 {α : Type} (x y z : α) : (((#[].push x).push y).push z)[2]? = some z := rfl
theorem push4 {α : Type} (x y z u : α) : ((((#[].push x).push y).push z).push u)[3]? = some u := rfl
theorem push5 {α : Type} (x y z u v : α) : (((((#[].push x).push y).push z).push u).push v)[4]? = some v := rfl

theorem graph_nodes : graph.nodes = [.input, .sum 0 1, .linear 1 "embedding.weight" none,
    .linear 2 "linear.weight" none, .linear 3 "unembedding.weight" none] := rfl
theorem graph_output : graph.output = 4 := rfl
theorem graph_positions : graph.positions = 2 := rfl
theorem graph_values : graph.values = 8 := rfl

theorem rowsVal_map (w : Weights ℚ) (name : String) (n : Nat) (v : List ℚ) :
    ∀ rs : List Nat, rowsVal w name n v rs = rs.map fun r => dotVal w name (r * n) v 0 0
  | [] => rfl
  | r :: rs => by simp [rowsVal, rowsVal_map w name n v rs]

theorem sum_onehot1 (f : Nat → ℚ) (a : Nat) (ha : a < 8) :
    ((List.range 8).map fun i => f i * (if a = i then 1 else 0)).sum = f a := by
  have r8 : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := rfl
  rw [r8]
  interval_cases a <;> simp

theorem sum_onehot2 (f : Nat → ℚ) (a b : Nat) (ha : a < 8) (hb : b < 8) :
    ((List.range 8).map fun i => f i * ((if a = i then 1 else 0) + (if b = i then 1 else 0))).sum
      = f a + f b := by
  simp only [mul_add, List.sum_map_add]
  rw [sum_onehot1 f a ha, sum_onehot1 f b hb]

theorem netEval (w : Weights ℚ) (hwf : WF w) (a b : Nat) (ha : a < 8) (hb : b < 8) :
    ∃ out : Tensor ℚ, evalGraph graph w [a, b] = some out ∧ out.shape = [1, 8] ∧
      out.data.size = 8 ∧ ∀ j < 8, out.get j = (colVal w a).getD j 0 + (colVal w b).getD j 0 := by
  obtain ⟨We, Wl, Wu, hWe, hWes, hWez, hWl, hWls, hWlz, hWu, hWus, hWuz⟩ := hwf
  obtain ⟨S, hS, hSs, hSz, hSg⟩ := sum_eq a b ha hb
  obtain ⟨E, hE, hEs, hEz, hEg⟩ := linear_vec We S 4 8 hWes hWez hSs hSz
  obtain ⟨H, hH, hHs, hHz, hHg⟩ := linear_vec Wl E 4 4 hWls hWlz hEs hEz
  obtain ⟨O, hO, hOs, hOz, hOg⟩ := linear_vec Wu H 8 4 hWus hWuz hHs hHz
  have h0 : evalOp graph w [a, b] #[] .input = some (OH a b) := by
    simp only [evalOp, graph_positions, graph_values]
    exact oneHot_eq a b ha hb
  have h1 : evalOp graph w [a, b] (#[].push (OH a b)) (.sum 0 1) = some S := by
    simp only [evalOp, push1]
    exact hS
  have h2 : evalOp graph w [a, b] ((#[].push (OH a b)).push S) (.linear 1 "embedding.weight" none) = some E := by
    simp only [evalOp, push2, hWe]
    exact hE
  have h3 : evalOp graph w [a, b] (((#[].push (OH a b)).push S).push E) (.linear 2 "linear.weight" none) = some H := by
    simp only [evalOp, push3, hWl]
    exact hH
  have h4 : evalOp graph w [a, b] ((((#[].push (OH a b)).push S).push E).push H) (.linear 3 "unembedding.weight" none) = some O := by
    simp only [evalOp, push4, hWu]
    exact hO
  refine ⟨O, ?_, hOs, hOz, ?_⟩
  · unfold evalGraph
    rw [graph_nodes, graph_output, evalOps_cons_of h0, evalOps_cons_of h1, evalOps_cons_of h2,
      evalOps_cons_of h3, evalOps_cons_of h4]
    simp only [evalOps, push5]
  · intro j hj
    have hEg' : ∀ i < 4, E.get i = We.get (i * 8 + a) + We.get (i * 8 + b) := by
      intro i hi
      rw [hEg i hi]
      have : ((List.range 8).map fun i' => We.get (i * 8 + i') * S.get i') =
          (List.range 8).map fun i' => We.get (i * 8 + i') * ((if a = i' then 1 else 0) + (if b = i' then 1 else 0)) := by
        apply List.map_congr_left
        intro i' hi'
        rw [hSg i' (List.mem_range.mp hi')]
      rw [this, sum_onehot2 (fun i' => We.get (i * 8 + i')) a b ha hb]
    rw [hOg j hj]
    have r4 : List.range 4 = [0, 1, 2, 3] := rfl
    simp only [r4, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [hHg 0 (by norm_num), hHg 1 (by norm_num), hHg 2 (by norm_num), hHg 3 (by norm_num)]
    simp only [r4, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [hEg' 0 (by norm_num), hEg' 1 (by norm_num), hEg' 2 (by norm_num), hEg' 3 (by norm_num)]
    simp [colVal, rowsVal_map, hj, r4, dotVal, wget, hWe, hWl, hWu] <;> ring

/-! ## From the guard to well-formed weights -/

theorem linearOp_size {W t r : Tensor ℚ} (h : linearOp W none t = some r) :
    W.data.size = W.shape.getD 0 0 * W.shape.getD 1 0 := by
  simp only [linearOp] at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact hc.1.1.2
  · cases h

theorem wf_of_single (w : Weights ℚ) (We Wl Wu : Tensor ℚ)
    (hWe : List.lookup "embedding.weight" w = some We) (hWes : We.shape = [4, 8])
    (hWl : List.lookup "linear.weight" w = some Wl) (hWls : Wl.shape = [4, 4])
    (hWu : List.lookup "unembedding.weight" w = some Wu) (hWus : Wu.shape = [8, 4])
    (x : Input) (h : singleOk graph w task x = true) : WF w := by
  unfold singleOk at h
  split at h
  · rename_i out hout
    unfold evalGraph at hout
    split at hout
    · rename_i vals hvals
      rw [graph_nodes] at hvals
      obtain ⟨v0, _, hvals⟩ := evalOps_cons hvals
      obtain ⟨v1, _, hvals⟩ := evalOps_cons hvals
      obtain ⟨v2, h2, hvals⟩ := evalOps_cons hvals
      obtain ⟨v3, h3, hvals⟩ := evalOps_cons hvals
      obtain ⟨v4, h4, _⟩ := evalOps_cons hvals
      simp only [evalOp, push2, hWe] at h2
      simp only [evalOp, push3, hWl] at h3
      simp only [evalOp, push4, hWu] at h4
      have s2 := linearOp_size h2
      have s3 := linearOp_size h3
      have s4 := linearOp_size h4
      rw [hWes] at s2
      rw [hWls] at s3
      rw [hWus] at s4
      exact ⟨We, Wl, Wu, hWe, hWes, by simpa using s2, hWl, hWls, by simpa using s3, hWu, hWus,
        by simpa using s4⟩
    · cases hout
  · cases h

/-! ## Margins -/

theorem le_maxFromVal (acc : ℚ) : ∀ ys : List ℚ, acc ≤ maxFromVal acc ys
  | [] => le_refl _
  | y :: ys => le_trans (le_max_left acc y) (le_maxFromVal _ ys)

theorem mem_le_maxFromVal (acc : ℚ) : ∀ (ys : List ℚ) (y : ℚ), y ∈ ys → y ≤ maxFromVal acc ys
  | [], y, h => by simp at h
  | z :: ys, y, h => by
    simp only [maxFromVal]
    rcases List.mem_cons.mp h with rfl | h'
    · exact le_trans (le_max_right acc y) (le_maxFromVal _ ys)
    · exact mem_le_maxFromVal _ ys y h'

theorem strictVal_spec (Qv : List ℚ) (m : Nat) (h : strictVal Qv m = true) :
    ∀ j < 8, j ≠ m → Qv.getD j 0 < Qv.getD m 0 := by
  intro j hj hjm
  unfold strictVal at h
  have hmem : Qv.getD j 0 ∈ (others m).map (fun j => Qv.getD j 0) := by
    apply List.mem_map.mpr
    refine ⟨j, ?_, rfl⟩
    simp [others, List.mem_filter, hj, hjm]
  split at h
  · rename_i hnil
    rw [hnil] at hmem
    simp at hmem
  · rename_i y ys hcons
    rw [hcons] at hmem
    have hlt := of_decide_eq_true h
    rcases List.mem_cons.mp hmem with heq | hmem'
    · rw [heq]
      exact lt_of_le_of_lt (le_maxFromVal _ _) hlt
    · exact lt_of_le_of_lt (mem_le_maxFromVal _ _ _ hmem') hlt

theorem addVals_getD : ∀ (X Y : List ℚ) (j : Nat), j < X.length → j < Y.length →
    (addVals X Y).getD j 0 = X.getD j 0 + Y.getD j 0
  | x :: xs, y :: ys, 0, _, _ => by simp [addVals]
  | x :: xs, y :: ys, j + 1, hx, hy => by
    simp only [addVals, List.getD_cons_succ]
    exact addVals_getD xs ys j (by simpa using hx) (by simpa using hy)
  | [], _, j, hx, _ => by simp at hx
  | _ :: _, [], j, _, hy => by simp at hy

theorem colVal_length (w : Weights ℚ) (a : Nat) : (colVal w a).length = 8 := by
  simp [colVal, rowsVal_map]

theorem label_eq (a b : Nat) : task.label [a, b] = max (max 0 a) b := rfl

theorem correct_of_margins (w : Weights ℚ) (hwf : WF w) (a b m : Nat) (ha : a < 8) (hb : b < 8)
    (hm : m < 8) (hlab : task.label [a, b] = m)
    (hlt : ∀ j < 8, j ≠ m → (colVal w a).getD j 0 + (colVal w b).getD j 0 <
      (colVal w a).getD m 0 + (colVal w b).getD m 0) :
    Correct graph w task [a, b] := by
  obtain ⟨out, hout, hs, hz, hg⟩ := netEval w hwf a b ha hb
  apply singleOk_correct
  unfold singleOk
  rw [hout]
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨by rw [hs, hz], ?_⟩
  rw [hlab]
  apply strictMaxAt_of
  · simp [hz, hm]
  · intro j hj hne
    have hj8 : j < 8 := by simpa [hz] using hj
    rw [toList_getElem out j hj, vecGet_toList, hg j hj8, hg m hm]
    exact hlt j hj8 hne

theorem pair_correct (w : Weights ℚ) (hwf : WF w) (a m : Nat) (ham : a ≤ m) (hm : m < 8)
    (hs : strictVal (addVals (colVal w a) (colVal w m)) m = true) :
    Correct graph w task [a, m] ∧ Correct graph w task [m, a] := by
  have hsp := strictVal_spec _ _ hs
  have hl8 := colVal_length w a
  have hm8 := colVal_length w m
  have key : ∀ j < 8, j ≠ m → (colVal w a).getD j 0 + (colVal w m).getD j 0 <
      (colVal w a).getD m 0 + (colVal w m).getD m 0 := by
    intro j hj hne
    have := hsp j hj hne
    rwa [addVals_getD _ _ j (by omega) (by omega), addVals_getD _ _ m (by omega) (by omega)] at this
  constructor
  · exact correct_of_margins w hwf a m m (by omega) hm hm (by rw [label_eq]; omega) key
  · refine correct_of_margins w hwf m a m hm (by omega) hm (by rw [label_eq]; omega) ?_
    intro j hj hne
    have := key j hj hne
    linarith

theorem diag_correct (w : Weights ℚ) (hwf : WF w) (m : Nat) (hm : m < 8)
    (hs : strictVal (colVal w m) m = true) : Correct graph w task [m, m] := by
  have hsp := strictVal_spec _ _ hs
  refine correct_of_margins w hwf m m m hm hm hm (by rw [label_eq]; omega) ?_
  intro j hj hne
  have := hsp j hj hne
  linarith

theorem symmetric_graph : symmetricNet graph = true := by decide

theorem singleOk_swap (w : Weights ℚ) (a b : Nat) (h : singleOk graph w task [a, b] = true) :
    singleOk graph w task [b, a] = true := by
  unfold singleOk at *
  rw [evalGraph_perm symmetric_graph (List.Perm.swap a b [])]
  rw [task.labelSymmetric_spec rfl [b, a] [a, b] (List.Perm.swap a b [])]
  exact h

/-! ## The terms -/

open Classical in
theorem runTerm_sem (env : Env) (cols : List Nat) (cv : List (Nat × List Q)) (G : Bool)
    (hcv : ∀ a ∈ cols, ∃ ca, cv.lookup a = some ca ∧ ca.map Q.val = colVal env.weights a)
    (hG : G = true → WF env.weights) (t : Term) :
    Sem (runTerm Interp.counting cols cv G t) env
      (fun n => n ≤ t.inputs.countP fun x => decide (Correct graph env.weights task x)) := by
  by_cases hv : t.valid cols = true
  · cases t with
    | single a b =>
      simp only [Term.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
      simp only [runTerm, Term.valid, hv, decide_true, Bool.and_self, ↓reduceIte, Interp.counting_bind,
        Interp.counting_pure, Interp.counting_nscale]
      refine Sem.bind (Sem.single _ _ _) fun ok hok => ?_
      refine Sem.pure ?_
      cases ok with
      | false => simp
      | true =>
        have hc1 := singleOk_correct _ _ _ _ (hok rfl)
        have hc2 := singleOk_correct _ _ _ _ (singleOk_swap _ _ _ (hok rfl))
        by_cases hab : a = b
        · subst hab
          simp [Term.inputs, hc1]
        · simp [Term.inputs, hab, hc1, hc2]
    | diag m =>
      simp only [Term.valid, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hv
      obtain ⟨cm, hcm, hcmv⟩ := hcv m hv.2
      have hv' : (Term.diag m).valid cols = true := by
        simp [Term.valid, hv.1, List.contains_iff_mem, hv.2]
      simp only [runTerm, hv', ↓reduceIte, hcm, Option.getD_some, Interp.counting_bind,
        Interp.counting_pure, Interp.counting_nscale]
      refine Sem.bind (strictAt_sem env cm m) fun b hb => ?_
      refine Sem.bind (Sem.band _ _ _) fun b' hb' => ?_
      refine Sem.pure ?_
      subst hb'
      cases G with
      | false => simp
      | true =>
        cases b with
        | false => simp
        | true =>
          have hc := diag_correct _ (hG rfl) m hv.1 (by rw [← hcmv]; exact hb.symm)
          simp [Term.inputs, hc]
    | pair a m =>
      simp only [Term.valid, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hv
      obtain ⟨ca, hca, hcav⟩ := hcv a hv.1.2
      obtain ⟨cm, hcm, hcmv⟩ := hcv m hv.2
      have hv' : (Term.pair a m).valid cols = true := by
        simp [Term.valid, hv.1.1.1, hv.1.1.2, List.contains_iff_mem, hv.1.2, hv.2]
      simp only [runTerm, hv', ↓reduceIte, hca, hcm, Option.getD_some, Interp.counting_bind,
        Interp.counting_pure, Interp.counting_nscale]
      refine Sem.bind (addLists_sem env ca cm) fun L hL => ?_
      refine Sem.bind (strictAt_sem env L m) fun b hb => ?_
      refine Sem.bind (Sem.band _ _ _) fun b' hb' => ?_
      refine Sem.pure ?_
      subst hb'
      cases G with
      | false => simp
      | true =>
        cases b with
        | false => simp
        | true =>
          have hs : strictVal (addVals (colVal env.weights a) (colVal env.weights m)) m = true := by
            rw [← hcav, ← hcmv, ← hL]; exact hb.symm
          obtain ⟨hc1, hc2⟩ := pair_correct _ (hG rfl) a m (by omega) hv.1.1.2 hs
          simp [Term.inputs, hc1, hc2]
  · simp only [runTerm, hv, Bool.false_eq_true, ↓reduceIte, Interp.counting_pure, Interp.counting_nzero]
    exact Sem.pure (Nat.zero_le _)

open Classical in
theorem runTerms_sem (env : Env) (cols : List Nat) (cv : List (Nat × List Q)) (G : Bool)
    (hcv : ∀ a ∈ cols, ∃ ca, cv.lookup a = some ca ∧ ca.map Q.val = colVal env.weights a)
    (hG : G = true → WF env.weights) : ∀ ts : List Term,
    Sem (runTerms Interp.counting cols cv G ts) env
      (fun n => n ≤ (ts.flatMap Term.inputs).countP fun x => decide (Correct graph env.weights task x))
  | [] => by
    simp only [runTerms, Interp.counting_pure]
    exact Sem.pure (Nat.zero_le _)
  | t :: ts => by
    simp only [runTerms, Interp.counting_bind, Interp.counting_pure]
    refine Sem.bind (runTerm_sem env cols cv G hcv hG t) fun n hn => ?_
    refine Sem.bind (runTerms_sem env cols cv G hcv hG ts) fun ns hns => ?_
    refine Sem.pure ?_
    rw [List.flatMap_cons, List.countP_append]
    exact Nat.add_le_add hn hns

open Classical in
theorem guard_count (w : Weights ℚ) (g : Nat × Nat) (h : singleOk graph w task [g.1, g.2] = true) :
    (guardInputs g).length ≤ (guardInputs g).countP fun x => decide (Correct graph w task x) := by
  have hc1 := singleOk_correct _ _ _ _ h
  have hc2 := singleOk_correct _ _ _ _ (singleOk_swap _ _ _ h)
  unfold guardInputs
  split
  · split
    · simp [hc1]
    · simp [hc1, hc2]
  · simp

def certInputs (p : Plan) : List Input := guardInputs p.guard ++ p.terms.flatMap Term.inputs

open Classical in
theorem runPlan_sound (p : Plan) (env : Env) (hnd : (certInputs p).Nodup)
    (hsub : ∀ x ∈ certInputs p, x ∈ allInputs task.space) :
    Sem (runPlan Interp.counting p) env (fun n => n ≤ numCorrect graph env.weights task) := by
  unfold runPlan
  simp only [Interp.counting_bind, Interp.counting_pure]
  refine Sem.bind (shapesOk_sem env) fun ok hok => ?_
  cases ok with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact Sem.pure (Nat.zero_le _)
  | true =>
    simp only [↓reduceIte]
    obtain ⟨We, Wl, Wu, hWe, hWes, hWl, hWls, hWu, hWus⟩ := hok rfl
    refine Sem.bind (Sem.single _ _ _) fun G hG => ?_
    have hG' : G = true → WF env.weights := fun h =>
      wf_of_single env.weights We Wl Wu hWe hWes hWl hWls hWu hWus _ (hG h)
    refine Sem.bind (columns_sem env p.cols) fun cv hcv => ?_
    refine Sem.bind (runTerms_sem env p.cols cv G hcv hG' p.terms) fun n hn => ?_
    refine Sem.pure ?_
    have hL : (certInputs p).countP (fun x => decide (Correct graph env.weights task x)) ≤
        numCorrect graph env.weights task := by
      unfold numCorrect
      exact List.Subperm.countP_le _ (List.Nodup.subperm hnd hsub)
    have hsplit : (certInputs p).countP (fun x => decide (Correct graph env.weights task x)) =
        (guardInputs p.guard).countP (fun x => decide (Correct graph env.weights task x)) +
        (p.terms.flatMap Term.inputs).countP (fun x => decide (Correct graph env.weights task x)) := by
      unfold certInputs
      rw [List.countP_append]
    have hg : cond G (guardInputs p.guard).length 0 ≤
        (guardInputs p.guard).countP (fun x => decide (Correct graph env.weights task x)) := by
      cases G with
      | false => simp
      | true =>
        simp only [Bool.cond_true]
        exact guard_count env.weights p.guard (hG rfl)
    rw [hsplit] at hL
    exact le_trans (Nat.add_le_add hg hn) hL

theorem D_sound : ∀ (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),
    CostM.exec (D Interp.counting) ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task := by
  intro w c n cost h
  exact runPlan_sound fullPlan ⟨w, c⟩ (by decide) (by decide) [] n cost h

theorem D_instance : CostM.billed (D Interp.counting) ⟨weights, cert⟩ = some (64, 943) := by
  decide +kernel

theorem performance : Target := by
  show claimedCount ≤ numCorrect graph weights task
  obtain ⟨cost, h⟩ := CostM.exec_of_billed D_instance
  exact D_sound weights cert 64 cost h

end Candidate.ColFull
