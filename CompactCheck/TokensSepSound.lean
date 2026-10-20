import CompactCheck.TokensIndex

/-!
# The token rules keep their values related to the real values

On an input `x` of a token_interval leaf, every value of `Tokens.lean` is
related to the real value the network computes on `x` (`TRel`):

* an interval tensor encloses it;
* a `Sep` holds it exactly: entry `q` of position `p` is entry `q` of the
  row of `x`'s token at `p` (`SepW`, with weight 1);
* a `WSep` is a real weight per position times such rows; the weight is
  enclosed by the `WSep`'s weight tensor;
* a `Mix` is a real tensor enclosed by its constant plus, per term, a real
  weight enclosed by the term's weight times the row of `x`'s token
  (`MixR`);
* values per input hold one interval tensor per input of the leaf, and the
  one of `x` encloses the real value (`VarR`).

This file proves that the rules that keep the tokens apart keep these
relations: the lookup, sums and products with constants, sums over the
positions or over a dimension of the rows, indexing a position, and
products with matrices.
-/

namespace CompactCheck

/-! ## The inputs of a leaf -/

/-- The row of input `x`'s token at position `p`: its offset from the first
    allowed token. -/
def rowOf (box : Box) (x : Input) (p : ℕ) : ℕ := x.getD p 0 - (box.getD p ⟨0, 0⟩).lo

/-- The number of tokens allowed at position `p`. -/
def nTok (box : Box) (p : ℕ) : ℕ := (box.getD p ⟨0, 0⟩).hi + 1 - (box.getD p ⟨0, 0⟩).lo

/-- Which of the leaf's inputs `x` is, for values kept per input. -/
def inputIdx (ctx : TCtx) (x : Input) : ℕ :=
  match ctx.pstar with
  | some p => rowOf ctx.box x p
  | none => 0

/-- What the token rules use of an input of the leaf. -/
structure LeafFacts (ctx : TCtx) (x : Input) : Prop where
  inbox : inBox ctx.box x = true
  row_lt : ∀ p < ctx.box.length, rowOf ctx.box x p < nTok ctx.box p
  one_row : ∀ p < ctx.box.length, nTok ctx.box p = 1 → rowOf ctx.box x p = 0
  idx_lt : inputIdx ctx x < ctx.k
  varying : ctx.aligned = true → ∀ p < ctx.box.length, nTok ctx.box p ≠ 1 →
    rowOf ctx.box x p = inputIdx ctx x ∧ nTok ctx.box p = ctx.k

/-- The varying positions of a box, as `TCtx.ofBox` finds them. -/
def varyOf (box : Box) : List ℕ :=
  (List.range box.length).filter fun p => (box.getD p ⟨0, 0⟩).lo < (box.getD p ⟨0, 0⟩).hi

theorem ofBox_box (box : Box) (V : ℕ) : (TCtx.ofBox box V).box = box := rfl

theorem ofBox_pstar (box : Box) (V : ℕ) : (TCtx.ofBox box V).pstar =
    if (varyOf box).length == 1 then (varyOf box).head? else none := rfl

theorem ofBox_aligned (box : Box) (V : ℕ) :
    (TCtx.ofBox box V).aligned = decide ((varyOf box).length ≤ 1) := rfl

theorem ofBox_k (box : Box) (V : ℕ) : (TCtx.ofBox box V).k =
    match (TCtx.ofBox box V).pstar with
    | some p => nTok box p
    | none => 1 := rfl

theorem leafFacts {box : Box} {V : ℕ} {x : Input} (hx : inBox box x = true) :
    LeafFacts (TCtx.ofBox box V) x := by
  have hget := inBox_getD hx
  have hrow : ∀ p < box.length, rowOf box x p < nTok box p := by
    intro p hp
    have := hget p hp
    unfold rowOf nTok
    omega
  have hmem : ∀ p < box.length, nTok box p ≠ 1 → p ∈ varyOf box := by
    intro p hp hn
    have := hget p hp
    rw [varyOf, List.mem_filter]
    refine ⟨List.mem_range.mpr hp, ?_⟩
    unfold nTok at hn
    simp only [decide_eq_true_eq]
    omega
  have hlt : ∀ p ∈ varyOf box, p < box.length := by
    intro p hp
    rw [varyOf, List.mem_filter] at hp
    exact List.mem_range.mp hp.1
  -- the varying position, if exactly one varies
  have hstar : ∀ p, (TCtx.ofBox box V).pstar = some p → p < box.length ∧ varyOf box = [p] := by
    intro p hp
    rw [ofBox_pstar] at hp
    split_ifs at hp with h1
    simp only [beq_iff_eq] at h1
    obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp h1
    rw [ha] at hp
    simp only [List.head?_cons, Option.some.injEq] at hp
    subst hp
    exact ⟨hlt _ (by rw [ha]; exact List.mem_cons_self), ha⟩
  refine ⟨hx, hrow, ?_, ?_, ?_⟩
  · intro p hp hn
    simp only [ofBox_box] at hp hn ⊢
    have := hget p hp
    unfold rowOf
    unfold nTok at hn
    omega
  · unfold inputIdx
    rw [ofBox_k]
    cases hps : (TCtx.ofBox box V).pstar with
    | none => simp
    | some p => exact hrow p (hstar p hps).1
  · intro hal p hp hn
    rw [ofBox_aligned, decide_eq_true_eq] at hal
    have hpv := hmem p hp hn
    have hlen : (varyOf box).length = 1 := by
      have := List.length_pos_of_mem hpv
      omega
    obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hlen
    rw [ha, List.mem_singleton] at hpv
    subst hpv
    have hps : (TCtx.ofBox box V).pstar = some p := by
      rw [ofBox_pstar, ha]
      simp
    unfold inputIdx
    rw [ofBox_k, hps]
    exact ⟨rfl, rfl⟩

/-! ## Real rows -/

/-- The real value of the lower ends of an interval tensor: its value if it
    is exact. -/
noncomputable def DT.real (v : DT) : Tensor ℝ := ⟨v.shape, v.lo.map (dv · v.e)⟩

theorem DT.real_get (v : DT) (j : ℕ) : v.real.get j = dv (mget v.lo j) v.e := by
  simp only [DT.real, Tensor.get, mget, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases v.lo[j]? <;> simp

/-- The rows of position `p` of a `Sep` or a term: an exact interval tensor
    with one row per allowed token. -/
def RowsOk (box : Box) (p : ℕ) (rest : List ℕ) (r : DT) : Prop :=
  r.ok = true ∧ r.exact = true ∧ r.lo = r.hi ∧ r.shape = nTok box p :: rest

theorem RowsOk.encl {box : Box} {p : ℕ} {rest : List ℕ} {r : DT} (h : RowsOk box p rest r) :
    r.Encl r.real := by
  obtain ⟨hok, hex, hlh, -⟩ := h
  simp only [DT.ok, Bool.and_eq_true, beq_iff_eq] at hok
  refine DT.Encl.mk rfl (by simp [DT.real, hok.1]) hok.1 hok.2 (fun _ => hlh) ?_
  intro j _
  rw [DT.real_get, ← hlh]
  exact ⟨le_refl _, le_refl _⟩

/-- An exact interval tensor encloses only its real value. -/
theorem DT.Encl.get_real {v : DT} {t : Tensor ℝ} (h : v.Encl t) (hex : v.exact = true) (j : ℕ) :
    t.get j = v.real.get j := by
  rw [h.eq_of_exact hex, DT.real_get]

/-! ## The relations -/

/-- A value kept per token on input `x`: entry `q` of position `p` is
    `wt p` times entry `q` of the row of `x`'s token at `p` (`wt` is 1 for a
    `Sep`, the real weight of position `p` for a `WSep`). -/
def SepW (box : Box) (x : Input) (wt : ℕ → ℝ) (s : Sep) (t : Tensor ℝ) : Prop :=
  0 < box.length ∧ s.rows.length = box.length ∧ t.shape = 1 :: box.length :: s.rest ∧
    t.data.size = box.length * shapeSize s.rest ∧
    (∀ p < box.length, RowsOk box p s.rest (s.rows.getD p emptyDT)) ∧
    ∀ p < box.length, ∀ q < shapeSize s.rest, t.get (p * shapeSize s.rest + q) =
      wt p * (s.rows.getD p emptyDT).real.get (rowOf box x p * shapeSize s.rest + q)

/-- The entry of a term's weight for input `x`: its only entry, or `x`'s
    among the leaf's inputs. -/
def wIdx (ctx : TCtx) (x : Input) (w : DT) : ℕ := if w.shape = [] then 0 else inputIdx ctx x

/-- A term and its real weight on input `x`. -/
def TermR (ctx : TCtx) (x : Input) (rest : List ℕ) (τ : Term) (ω : ℝ) : Prop :=
  τ.pos < ctx.box.length ∧ RowsOk ctx.box τ.pos rest τ.rows ∧
    (τ.w.shape = [] ∨ τ.w.shape = [ctx.k]) ∧ ∃ Ω : Tensor ℝ, τ.w.Encl Ω ∧ ω = Ω.get (wIdx ctx x τ.w)

/-- The value of terms with real weights, entry `q` (`S` the size of a row). -/
noncomputable def termsVal (box : Box) (x : Input) (S : ℕ) (terms : List Term) (ωs : List ℝ)
    (q : ℕ) : ℝ :=
  (List.zipWith (fun τ ω => ω * τ.rows.real.get (rowOf box x τ.pos * S + q)) terms ωs).sum

/-- A `Mix` on input `x`. -/
def MixR (ctx : TCtx) (x : Input) (m : Mix) (t : Tensor ℝ) : Prop :=
  ∃ rest, m.const.shape = 1 :: rest ∧ t.shape = 1 :: rest ∧ t.data.size = shapeSize rest ∧
    ∃ c, m.const.Encl c ∧ ∃ ωs, List.Forall₂ (TermR ctx x rest) m.terms ωs ∧
      ∀ q < shapeSize rest, t.get q = c.get q + termsVal ctx.box x (shapeSize rest) m.terms ωs q

/-- Values per input: one for each input of the leaf, each enclosing a real
    value; the one of `x` encloses `t`. -/
def VarR (ctx : TCtx) (x : Input) (vs : Array DT) (t : Tensor ℝ) : Prop :=
  vs.size = ctx.k ∧ (∀ i < ctx.k, ∃ T, (vs.getD i emptyDT).Encl T) ∧
    (vs.getD (inputIdx ctx x) emptyDT).Encl t

/-- A `WSep` with one weight tensor. -/
def WSepR (ctx : TCtx) (x : Input) (w : DT) (s : Sep) (t : Tensor ℝ) : Prop :=
  w.shape = weightShape ctx.box.length s.rest ∧
    ∃ W, w.Encl W ∧ SepW ctx.box x (fun p => W.get p) s t

/-- A `WSep` with one weight tensor per input. -/
def WSepVR (ctx : TCtx) (x : Input) (ws : Array DT) (s : Sep) (t : Tensor ℝ) : Prop :=
  ws.size = ctx.k ∧
    (∀ i < ctx.k, (ws.getD i emptyDT).shape = weightShape ctx.box.length s.rest ∧
      ∃ W, (ws.getD i emptyDT).Encl W) ∧
    ∃ W, (ws.getD (inputIdx ctx x) emptyDT).Encl W ∧ SepW ctx.box x (fun p => W.get p) s t

/-- A value of a token_interval leaf and the real value on input `x`. -/
def TRel (g : Graph) (ctx : TCtx) (x : Input) : TV → Tensor ℝ → Prop
  | .box, t => inBox ctx.box x = true ∧ oneHotInput g.positions g.values x = some t
  | .dt v, t => v.Encl t
  | .sep s, t => SepW ctx.box x (fun _ => 1) s t
  | .mix m, t => MixR ctx x m t
  | .wsep w s, t => WSepR ctx x w s t
  | .wsepv ws s, t => WSepVR ctx x ws s t
  | .var vs, t => VarR ctx x vs t

/-! ## Helpers -/

theorem mapM_forall₂ {β γ : Type} {f : β → Option γ} :
    ∀ {l : List β} {l' : List γ}, l.mapM f = some l' → List.Forall₂ (fun a b => f a = some b) l l'
  | [], l', h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact List.Forall₂.nil
  | a :: l, l', h => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | none => simp [ha] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [ha, hl] at h
      | some bs =>
        simp only [ha, hl, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        exact List.Forall₂.cons ha (mapM_forall₂ hl)

theorem forall₂_getD {β γ : Type} {R : β → γ → Prop} {l : List β} {l' : List γ}
    (h : List.Forall₂ R l l') {i : ℕ} (hi : i < l.length) (d : β) (d' : γ) :
    R (l.getD i d) (l'.getD i d') := by
  have hl := h.length_eq
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hl ▸ hi), Option.getD_some]
  exact List.forall₂_iff_get.mp h |>.2 i hi (hl ▸ hi)

theorem getD_zip_range {β : Type} (l : List β) {p : ℕ} (hp : p < l.length) (d : ℕ × β) :
    ((List.range l.length).zip l).getD p d = (p, l.getD p (d.2)) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega), Option.getD_some]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp]

theorem length_zip_range {β : Type} (l : List β) :
    ((List.range l.length).zip l).length = l.length := by
  simp

theorem list_getD_map {β γ : Type} (f : β → γ) {l : List β} {p : ℕ} (hp : p < l.length)
    (d : β) (d' : γ) : (l.map f).getD p d' = f (l.getD p d) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hp), Option.getD_some,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp, Option.getD_some, List.getElem_map]

theorem dmove_exact {F : Tensor ℤ → Option (Tensor ℤ)} {a c : DT} (h : dmove F a = some c) :
    c.exact = a.exact ∧ c.e = a.e := by
  unfold dmove at h
  by_cases hok : a.ok = true
  · simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    cases hlo : F ⟨a.shape, a.lo⟩ with
    | none => simp [hlo] at h
    | some lo =>
      simp only [hlo] at h
      by_cases hx : a.exact = true
      · simp only [hx, ↓reduceIte, Option.some.injEq] at h
        subst h
        exact ⟨hx.symm, rfl⟩
      · simp only [hx, Bool.false_eq_true, ↓reduceIte] at h
        cases hhi : F ⟨a.shape, a.hi⟩ with
        | none => simp [hhi] at h
        | some hi =>
          simp only [hhi, Option.some.injEq] at h
          subst h
          simp [hx]
  · simp [hok] at h

theorem dbinary_exact {f : BinOp} {a b c : DT} (h : dbinary f a b = some c) :
    c.exact = (a.exact && b.exact) := by
  unfold dbinary at h
  split_ifs at h
  obtain ⟨s, -, rfl⟩ := Option.map_eq_some_iff.mp h
  cases f <;> simp [dbinaryAt, DT.shift]
  all_goals split_ifs <;> rfl

theorem dsum_exact {d : ℤ} {a c : DT} (h : dsum d a = some c) : c.exact = a.exact := by
  unfold dsum at h
  by_cases hok : a.ok = true
  · simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    cases hlo : sumOp d (⟨a.shape, a.lo⟩ : Tensor ℤ) with
    | none => simp [hlo] at h
    | some lo =>
      simp only [hlo, Option.some.injEq] at h
      subst h
      rfl
  · simp [hok] at h

theorem dmatmul_exact {a b c : DT} (h : dmatmul a b = some c) :
    c.exact = (a.exact && b.exact) := by
  unfold dmatmul at h
  by_cases hok : (a.ok && b.ok) = true
  · simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.mp h
    rfl
  · simp [hok] at h

theorem dtBroadcastTo_sim {c b : DT} {tc : Tensor ℝ} {s : List ℕ} (hc : c.Encl tc)
    (h : dtBroadcastTo c s = some b) : ∃ Cb, expandOp tc (s.map Int.ofNat) = some Cb ∧ b.Encl Cb :=
  dmove_sim (expandOp_mover (s.map Int.ofNat)) hc h

theorem dtIndex_sim {c b : DT} {tc : Tensor ℝ} {items : List IndexItem} (hc : c.Encl tc)
    (h : dtIndex items c = some b) : ∃ r, indexOp tc items = some r ∧ b.Encl r :=
  dmove_sim (indexOp_mover items) hc h

theorem dtUnsqueeze_sim {c b : DT} {tc : Tensor ℝ} {d : ℤ} (hc : c.Encl tc)
    (h : dtUnsqueeze d c = some b) : ∃ r, unsqueezeOp tc d = some r ∧ b.Encl r :=
  dmove_sim (unsqueezeOp_mover d) hc h

theorem BinOp.apply_comm {f : BinOp} (hf : f = .add ∨ f = .mul) (a b : ℝ) :
    f.apply a b = f.apply b a := by
  rcases hf with rfl | rfl
  · simp only [BinOp.apply]; ring
  · simp only [BinOp.apply]; ring

/-- A shape broadcasts with itself after one more leading dimension. -/
theorem broadcastShape_cons_rest (n : ℕ) (rest : List ℕ) :
    broadcastShape (n :: rest) rest = some (n :: rest) := by
  apply (broadcastShape_of_fits (by simp) _).1
  simp only [List.length_cons]
  apply List.all_eq_true.mpr
  intro b hb
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
  simp

/-- The real result of an entrywise operation with the full shape on the
    left. -/
theorem broadcastOp_full_left {f : ℝ → ℝ → ℝ} {a b r : Tensor ℝ} {s : List ℕ}
    (hs : a.shape = s) (h : broadcastOp f a b = some r)
    (hbs : broadcastShape a.shape b.shape = some s) :
    r.shape = s ∧ r.data.size = shapeSize s ∧ ∀ j < shapeSize s,
      r.get j = f (a.get j) (b.entry (broadcastIndex b.shape (unravel s j))) := by
  obtain ⟨s', hs', rfl, -, -⟩ := broadcastOp_spec h
  rw [hbs] at hs'
  simp only [Option.some.injEq] at hs'
  subst hs'
  refine ⟨rfl, Tensor.ofFn_data_size _ _, fun j hj => ?_⟩
  rw [Tensor.ofFn_get _ _ hj, entry_broadcast_self hs hj]

theorem broadcastOp_full_right {f : ℝ → ℝ → ℝ} {a b r : Tensor ℝ} {s : List ℕ}
    (hs : b.shape = s) (h : broadcastOp f a b = some r)
    (hbs : broadcastShape a.shape b.shape = some s) :
    r.shape = s ∧ r.data.size = shapeSize s ∧ ∀ j < shapeSize s,
      r.get j = f (a.entry (broadcastIndex a.shape (unravel s j))) (b.get j) := by
  obtain ⟨s', hs', rfl, -, -⟩ := broadcastOp_spec h
  rw [hbs] at hs'
  simp only [Option.some.injEq] at hs'
  subst hs'
  refine ⟨rfl, Tensor.ofFn_data_size _ _, fun j hj => ?_⟩
  rw [Tensor.ofFn_get _ _ hj, entry_broadcast_self hs hj]

theorem SepW.wf {box : Box} {x : Input} {wt : ℕ → ℝ} {s : Sep} {t : Tensor ℝ}
    (h : SepW box x wt s t) : t.wellFormed = true := by
  simp [Tensor.wellFormed, h.2.2.1, h.2.2.2.1, shapeSize_one_cons]

theorem SepW.shape_eq {box : Box} {x : Input} {wt : ℕ → ℝ} {s : Sep} {t : Tensor ℝ}
    (h : SepW box x wt s t) : t.shape = s.shape := by
  rw [h.2.2.1, Sep.shape, h.2.1]

/-! ## The lookup -/

theorem onehot_get {P V : ℕ} {x : Input} {ta : Tensor ℝ} (hoh : oneHotInput P V x = some ta) :
    ta.shape = [1, P, V] ∧ ta.wellFormed = true ∧ x.length = P ∧ (∀ p < P, x.getD p 0 < V) ∧
      ∀ p < P, ∀ t < V, ta.get (p * V + t) = if x.getD p 0 = t then 1 else 0 := by
  obtain ⟨hlen, hall, rfl⟩ := oneHotInput_eq hoh
  refine ⟨rfl, by simp [Tensor.wellFormed, shapeSize], hlen, fun p hp => ?_, fun p hp t ht => ?_⟩
  · have hpx : p < x.length := by rw [hlen]; exact hp
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpx, Option.getD_some]
    simpa using List.all_eq_true.mp hall _ (List.getElem_mem hpx)
  · rw [Tensor.get_mk_map_range _ _ _ (lt_mul_of_row hp ht), div_aux (by omega) ht, mod_aux ht]

/-- The product of the one-hot input with a matrix: at position `p`, the
    row of the matrix at `x`'s token. -/
theorem onehot_matmul {P V d : ℕ} {x : Input} {ta tb : Tensor ℝ}
    (hoh : oneHotInput P V x = some ta) (htb : tb.shape = [V, d]) (hwb : tb.wellFormed = true) :
    ∃ R, matmulOp ta tb = some R ∧ R.shape = [1, P, d] ∧ R.data.size = P * d ∧
      ∀ p < P, ∀ q < d, R.get (p * d + q) = tb.get (x.getD p 0 * d + q) := by
  obtain ⟨hs, hw, -, hxV, hget⟩ := onehot_get hoh
  obtain ⟨R, hR, hRs, hRsz, hRget⟩ := matmulOp_three hs htb hw hwb
  refine ⟨R, hR, hRs, hRsz, fun p hp q hq => ?_⟩
  rw [hRget p hp q hq]
  rw [List.map_congr_left (g := fun t => (if x.getD p 0 = t then (1 : ℝ) else 0) *
    tb.get (t * d + q)) ?_, onehot_sum _ _ (hxV p hp)]
  intro t ht
  rw [hget p hp t (List.mem_range.mp ht)]

/-- **The lookup** keeps each position's rows exactly. -/
theorem tLookup_sim {g : Graph} {ctx : TCtx} {x : Input} (hf : LeafFacts ctx x)
    (hval : ctx.values = g.values) {ta tb : Tensor ℝ} {w : DT} {s : Sep}
    (hbox : oneHotInput g.positions g.values x = some ta) (hw : w.Encl tb)
    (h : tLookup ctx w = some s) :
    ∃ t, matmulOp ta tb = some t ∧ SepW ctx.box x (fun _ => 1) s t := by
  unfold tLookup at h
  split at h
  · rename_i V d hws
    split_ifs at h with hcond
    simp only [Option.some.injEq] at h
    subst h
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
    obtain ⟨⟨⟨⟨hex, -⟩, hV⟩, -⟩, hpos⟩ := hcond
    have hlen := inBox_length hf.inbox
    obtain ⟨-, -, hxP, -, -⟩ := onehot_get hbox
    have hP : ctx.box.length = g.positions := by rw [← hlen, hxP]
    have htb : tb.shape = [g.values, d] := by rw [hw.1, hws, hV, hval]
    obtain ⟨R, hR, hRs, hRsz, hRget⟩ := onehot_matmul hbox htb hw.wf
    have hd : shapeSize [d] = d := by simp [shapeSize]
    refine ⟨R, hR, hpos, by simp, by rw [hRs, hP], by rw [hRsz, hP, hd], ?_, ?_⟩
    · intro p hp
      rw [list_getD_map _ hp ⟨0, 0⟩]
      exact ⟨by simp [DT.ok, shapeSize], rfl, rfl, by simp [nTok]⟩
    · intro p hp q hq
      rw [hd] at hq ⊢
      rw [hRget p (by rw [← hP]; exact hp) q hq, hw.eq_of_exact hex, list_getD_map _ hp ⟨0, 0⟩,
        DT.real_get, one_mul]
      have hrow := hf.row_lt p hp
      have hx := inBox_getD hf.inbox p hp
      simp only [nTok] at hrow
      simp only [rowOf] at hrow ⊢
      have hj : (x.getD p 0 - (ctx.box.getD p ⟨0, 0⟩).lo) * d + q <
          ((ctx.box.getD p ⟨0, 0⟩).hi + 1 - (ctx.box.getD p ⟨0, 0⟩).lo) * d :=
        lt_mul_of_row hrow hq
      rw [mget_map_range _ _ hj, div_aux (by omega) hq, mod_aux hq]
      have hxl : (ctx.box.getD p ⟨0, 0⟩).lo + (x.getD p 0 - (ctx.box.getD p ⟨0, 0⟩).lo) =
          x.getD p 0 := by omega
      rw [hxl]
  · cases h

/-! ## Outcomes -/

theorem Step.bind_eq_val {β γ : Type} {x : Step β} {f : β → Step γ} {b : γ}
    (h : (x >>= f) = .val b) : ∃ a, x = .val a ∧ f a = .val b := by
  cases x with
  | val a => exact ⟨a, rfl, h⟩
  | decline => cases h
  | fail => cases h

theorem Step.bind_eq_val' {β γ : Type} {x : Step β} {f : β → Step γ} {b : γ}
    (h : x.bind f = .val b) : ∃ a, x = .val a ∧ f a = .val b := by
  cases x with
  | val a => exact ⟨a, rfl, h⟩
  | decline => cases h
  | fail => cases h

theorem Step.ofOption_eq_val {β : Type} {o : Option β} {a : β} (h : Step.ofOption o = .val a) :
    o = some a := by
  cases o with
  | none => cases h
  | some b => cases h; rfl

theorem mapM_zip_range {β γ : Type} {F : ℕ × β → Option γ} {l : List β} {l' : List γ}
    (h : ((List.range l.length).zip l).mapM F = some l') :
    l'.length = l.length ∧
      ∀ p < l.length, ∀ (d : β) (d' : γ), F (p, l.getD p d) = some (l'.getD p d') := by
  have h2 := mapM_forall₂ h
  have hl := h2.length_eq
  rw [length_zip_range] at hl
  refine ⟨hl.symm, fun p hp d d' => ?_⟩
  have := forall₂_getD h2 (by rw [length_zip_range]; exact hp) (0, d) d'
  rwa [getD_zip_range _ hp] at this

/-! ## Rows combined with a constant -/

/-- The value of a `Sep` combined entrywise with a constant broadcast to its
    shape, from the rows combined with the constant's slice at each
    position. -/
theorem sep_of_rows {ctx : TCtx} {x : Input} (hf : LeafFacts ctx x) {s : Sep}
    {t t' Cb : Tensor ℝ} {rows : List DT} {F : ℝ → ℝ → ℝ} (hs : SepW ctx.box x (fun _ => 1) s t)
    (ht' : t'.shape = s.shape) (ht'sz : t'.data.size = shapeSize s.shape)
    (hget : ∀ j < shapeSize s.shape, t'.get j = F (t.get j) (Cb.get j))
    (hlen : rows.length = s.rows.length)
    (hrows : ∀ p < ctx.box.length, (rows.getD p emptyDT).exact = true ∧
      ∃ R', (rows.getD p emptyDT).Encl R' ∧ R'.shape = nTok ctx.box p :: s.rest ∧
        ∀ j < nTok ctx.box p, ∀ q < shapeSize s.rest,
          R'.get (j * shapeSize s.rest + q) =
            F ((s.rows.getD p emptyDT).real.get (j * shapeSize s.rest + q))
              (Cb.get (p * shapeSize s.rest + q))) :
    SepW ctx.box x (fun _ => 1) ⟨rows, s.rest⟩ t' := by
  obtain ⟨hpos, hrl, -, -, -, hval⟩ := hs
  have hsh : s.shape = 1 :: ctx.box.length :: s.rest := by rw [Sep.shape, hrl]
  refine ⟨hpos, by rw [hlen, hrl], by rw [ht', hsh], by rw [ht'sz, hsh, shapeSize_one_cons],
    fun p hp => ?_, fun p hp q hq => ?_⟩
  · obtain ⟨hex, R', hR', hR's, -⟩ := hrows p hp
    exact ⟨hR'.ok, hex, hR'.2.2.2.2.1 hex, by rw [← hR'.1, hR's]⟩
  · obtain ⟨hex, R', hR', -, hR'get⟩ := hrows p hp
    have hj : p * shapeSize s.rest + q < shapeSize s.shape := by
      rw [hsh, shapeSize_one_cons]
      exact lt_mul_of_row hp hq
    have hval' := hval p hp q hq
    rw [one_mul] at hval'
    rw [hget _ hj, hval', one_mul, ← hR'.get_real hex, hR'get _ (hf.row_lt p hp) q hq]

/-- Rows combined entrywise (`+` or `*`) with an exact constant, position by
    position: the value of the sum or product, in either order. -/
theorem rowsConst_sim {f : BinOp} (hf2 : f = .add ∨ f = .mul) {ctx : TCtx} {x : Input}
    (hf : LeafFacts ctx x) {s : Sep} {t tc : Tensor ℝ} {c b : DT} {rows : List DT}
    (hs : SepW ctx.box x (fun _ => 1) s t) (hc : c.Encl tc) (hcx : c.exact = true)
    (hb : dtBroadcastTo c s.shape = some b) {F : ℕ × DT → Option DT}
    (hF : ∀ p r, F (p, r) = (dtIndex [.one 0, .one p] b).bind fun cp => dbinary f r cp)
    (hrows : ((List.range s.rows.length).zip s.rows).mapM F = some rows) :
    (∃ t', broadcastOp f.apply t tc = some t' ∧ SepW ctx.box x (fun _ => 1) ⟨rows, s.rest⟩ t') ∧
    (∃ t', broadcastOp f.apply tc t = some t' ∧ SepW ctx.box x (fun _ => 1) ⟨rows, s.rest⟩ t') := by
  obtain ⟨Cb, hCb, hbCb⟩ := dtBroadcastTo_sim hc hb
  obtain ⟨hCbeq, hle, hfit⟩ := expandOp_nat_spec hCb
  obtain ⟨hbs1, hbs2⟩ := broadcastShape_of_fits hle hfit
  have hts := hs.shape_eq
  have hsh : s.shape = 1 :: ctx.box.length :: s.rest := by rw [Sep.shape, hs.2.1]
  have hCbget : ∀ j < shapeSize s.shape,
      Cb.get j = tc.entry (broadcastIndex tc.shape (unravel s.shape j)) := by
    intro j hj
    rw [hCbeq, Tensor.ofFn_get _ _ hj]
  obtain ⟨hlen, hper⟩ := mapM_zip_range hrows
  -- each position's rows
  have hrows' : ∀ p < ctx.box.length, (rows.getD p emptyDT).exact = true ∧
      ∃ R', (rows.getD p emptyDT).Encl R' ∧ R'.shape = nTok ctx.box p :: s.rest ∧
        ∀ j < nTok ctx.box p, ∀ q < shapeSize s.rest,
          R'.get (j * shapeSize s.rest + q) =
            f.apply ((s.rows.getD p emptyDT).real.get (j * shapeSize s.rest + q))
              (Cb.get (p * shapeSize s.rest + q)) := by
    intro p hp
    have hp' : p < s.rows.length := by rw [hs.2.1]; exact hp
    have h1 := hper p hp' emptyDT emptyDT
    rw [hF] at h1
    obtain ⟨cp, hcp, hrow⟩ := Option.bind_eq_some_iff.mp h1
    obtain ⟨Cp, hCp, hcpCp⟩ := dtIndex_sim hbCb hcp
    have hCbs : Cb.shape = 1 :: ctx.box.length :: s.rest := by rw [hCbeq, Tensor.ofFn_shape, hsh]
    obtain ⟨hCps, -, hCpget⟩ := indexOp_pos hCbs hCp
    have hrok := hs.2.2.2.2.1 p hp
    obtain ⟨R', hR', hR'enc⟩ := dbinary_sim hrok.encl hcpCp hrow
    have hexb : b.exact = true := by rw [(dmove_exact hb).1, hcx]
    have hexcp : cp.exact = true := by rw [(dmove_exact hcp).1, hexb]
    have hex : (rows.getD p emptyDT).exact = true := by
      rw [dbinary_exact hrow, hexcp, hrok.2.1]
      rfl
    have hRs : (s.rows.getD p emptyDT).real.shape = nTok ctx.box p :: s.rest := hrok.2.2.2
    have hbs : broadcastShape (s.rows.getD p emptyDT).real.shape Cp.shape =
        some (nTok ctx.box p :: s.rest) := by
      rw [hRs, hCps, broadcastShape_cons_rest]
    obtain ⟨hR's, -, hR'get⟩ := broadcastOp_full_left hRs hR' hbs
    refine ⟨hex, R', hR'enc, hR's, fun j hj q hq => ?_⟩
    have hjq : j * shapeSize s.rest + q < shapeSize (nTok ctx.box p :: s.rest) := by
      rw [shapeSize_cons]
      exact lt_mul_of_row hj hq
    rw [hR'get _ hjq, unravel_cons hq hj, hCps,
      broadcastIndex_cons _ _ _ (by rw [unravel_length]), broadcastIndex_unravel,
      entry_unravel hCps hq, hCpget q hq]
  have hj' : ∀ j < shapeSize s.shape,
      t.get j = t.entry (broadcastIndex t.shape (unravel s.shape j)) :=
    fun j hj => (entry_broadcast_self hts hj).symm
  constructor
  · have hbs : broadcastShape t.shape tc.shape = some s.shape := by rw [hts]; exact hbs1
    refine ⟨_, broadcastOp_eq f.apply hs.wf hc.wf hbs, ?_⟩
    have h1 := broadcastOp_full_left hts (broadcastOp_eq f.apply hs.wf hc.wf hbs) hbs
    refine sep_of_rows hf hs h1.1 h1.2.1 (fun j hj => ?_) hlen hrows'
    rw [h1.2.2 j hj, hCbget j hj]
  · have hbs : broadcastShape tc.shape t.shape = some s.shape := by rw [hts]; exact hbs2
    refine ⟨_, broadcastOp_eq f.apply hc.wf hs.wf hbs, ?_⟩
    have h1 := broadcastOp_full_right hts (broadcastOp_eq f.apply hc.wf hs.wf hbs) hbs
    refine sep_of_rows hf hs h1.1 h1.2.1 (fun j hj => ?_) hlen hrows'
    rw [h1.2.2 j hj, hCbget j hj, BinOp.apply_comm hf2]

theorem addConst_sim {ctx : TCtx} {x : Input} (hf : LeafFacts ctx x) {s s' : Sep}
    {t tc : Tensor ℝ} {c : DT} (hs : SepW ctx.box x (fun _ => 1) s t) (hc : c.Encl tc)
    (h : addConst s c = .val s') :
    (∃ t', broadcastOp BinOp.add.apply t tc = some t' ∧ SepW ctx.box x (fun _ => 1) s' t') ∧
    (∃ t', broadcastOp BinOp.add.apply tc t = some t' ∧ SepW ctx.box x (fun _ => 1) s' t') := by
  unfold addConst at h
  by_cases hcx : c.exact = true
  · simp only [hcx, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    split at h
    · cases h
    · rename_i b hb
      obtain ⟨rows, hrows, h2⟩ := Step.bind_eq_val h
      cases h2
      exact rowsConst_sim (Or.inl rfl) hf hs hc hcx hb (fun _ _ => rfl)
        (Step.ofOption_eq_val hrows)
  · simp [hcx] at h

/-! ## One weight per position -/

theorem array_getD_toList {β : Type} (a : Array β) (i : ℕ) (d : β) :
    a.toList.getD i d = a.getD i d := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem list_getD_toArray {β : Type} (l : List β) (i : ℕ) (d : β) :
    l.toArray.getD i d = l.getD i d := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

/-- One weight per position: the constant broadcast to the value's shape
    holds at each position the same real number along `rest`, which its
    first entries hold. -/
theorem onePerPosition_real {c b w : DT} {tc Cb : Tensor ℝ} {P : ℕ} {rest : List ℕ}
    (hc : c.Encl tc) (hb : dtBroadcastTo c (1 :: P :: rest) = some b)
    (hCb : expandOp tc ((1 :: P :: rest).map Int.ofNat) = some Cb) (hbCb : b.Encl Cb)
    (hone : onePerPosition b rest (1 :: P :: rest) = some (some w))
    (hcond : (c.exact || c.shape == weightShape P rest) = true) :
    ∃ W, w.Encl W ∧ W.shape = weightShape P rest ∧
      ∀ p < P, ∀ q < shapeSize rest, Cb.get (p * shapeSize rest + q) = W.get p := by
  unfold onePerPosition at hone
  cases hw : dtIndex (firstItems rest) b with
  | none => simp [hw] at hone
  | some w' =>
    cases hback : dtBroadcastTo w' (1 :: P :: rest) with
    | none => simp [hw, hback] at hone
    | some back =>
      simp only [hw, hback, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq] at hone
      split_ifs at hone with heq
      simp only [Option.some.injEq] at hone
      subst hone
      obtain ⟨hCbeq, -, -⟩ := expandOp_nat_spec hCb
      have hCbs : Cb.shape = 1 :: P :: rest := by rw [hCbeq, Tensor.ofFn_shape]
      obtain ⟨W, hW, hwW⟩ := dtIndex_sim hbCb hw
      obtain ⟨hWs, hWget⟩ := indexOp_first hCbs hW
      refine ⟨W, hwW, hWs, fun p hp q hq => ?_⟩
      have hj : p * shapeSize rest + q < shapeSize (1 :: P :: rest) := by
        rw [shapeSize_one_cons]
        exact lt_mul_of_row hp hq
      have hCbget : ∀ j < shapeSize (1 :: P :: rest),
          Cb.get j = tc.entry (broadcastIndex tc.shape (unravel (1 :: P :: rest) j)) := by
        intro j hj
        rw [hCbeq, Tensor.ofFn_get _ _ hj]
      simp only [Bool.or_eq_true, beq_iff_eq] at hcond
      rcases hcond with hex | hshape
      · -- an exact constant: the broadcast first entries are its entries
        have hbx : b.exact = true := by rw [(dmove_exact hb).1, hex]
        obtain ⟨hwx, hwe⟩ := dmove_exact hw
        obtain ⟨hbackx, hbacke⟩ := dmove_exact hback
        obtain ⟨Back, hBack, hbackB⟩ := dtBroadcastTo_sim hwW hback
        obtain ⟨hBackeq, -, -⟩ := expandOp_nat_spec hBack
        simp only [Bool.and_eq_true, beq_iff_eq] at heq
        have h1 : Cb.get (p * shapeSize rest + q) = Back.get (p * shapeSize rest + q) := by
          rw [hbCb.eq_of_exact hbx, hbackB.eq_of_exact (by rw [hbackx, hwx, hbx]), heq.1, hbacke,
            hwe]
        rw [h1, hBackeq, Tensor.ofFn_get _ _ hj, entry_broadcast_weight hWs hp hq]
      · -- a weight of the shape `[1, P, 1, ..., 1]`
        have htcs : tc.shape = weightShape P rest := by rw [hc.1, hshape]
        have hS : 0 < shapeSize rest := by omega
        rw [hWget p hp, hCbget _ hj,
          hCbget _ (by rw [shapeSize_one_cons]; exact lt_mul_of_row hp hS)]
        have := entry_broadcast_weight htcs hp hq
        rw [← Nat.add_zero (p * shapeSize rest), entry_broadcast_weight htcs hp hS]
        exact this

/-- A `Sep` times real weights per position. -/
theorem sepW_of_scaled {box : Box} {x : Input} {s : Sep} {t t' : Tensor ℝ} {wt : ℕ → ℝ}
    (hs : SepW box x (fun _ => 1) s t) (ht' : t'.shape = s.shape)
    (ht'sz : t'.data.size = shapeSize s.shape)
    (hget : ∀ p < box.length, ∀ q < shapeSize s.rest,
      t'.get (p * shapeSize s.rest + q) = wt p * t.get (p * shapeSize s.rest + q)) :
    SepW box x wt s t' := by
  obtain ⟨hpos, hrl, -, -, hrok, hval⟩ := hs
  have hsh : s.shape = 1 :: box.length :: s.rest := by rw [Sep.shape, hrl]
  refine ⟨hpos, hrl, by rw [ht', hsh], by rw [ht'sz, hsh, shapeSize_one_cons], hrok,
    fun p hp q hq => ?_⟩
  rw [hget p hp q hq, hval p hp q hq, one_mul]

theorem mulSep_sim {g : Graph} {ctx : TCtx} {x : Input} (hf : LeafFacts ctx x) {s : Sep}
    {t tc : Tensor ℝ} {c : DT} {v : TV} (hs : SepW ctx.box x (fun _ => 1) s t) (hc : c.Encl tc)
    (h : mulSep s c = .val v) :
    (∃ t', broadcastOp BinOp.mul.apply t tc = some t' ∧ TRel g ctx x v t') ∧
    (∃ t', broadcastOp BinOp.mul.apply tc t = some t' ∧ TRel g ctx x v t') := by
  have hts := hs.shape_eq
  have hsh : s.shape = 1 :: ctx.box.length :: s.rest := by rw [Sep.shape, hs.2.1]
  unfold mulSep at h
  split at h
  · cases h
  · rename_i b hb
    obtain ⟨Cb, hCb, hbCb⟩ := dtBroadcastTo_sim hc hb
    obtain ⟨hCbeq, hle, hfit⟩ := expandOp_nat_spec hCb
    obtain ⟨hbs1, hbs2⟩ := broadcastShape_of_fits hle hfit
    have hCbget : ∀ j < shapeSize s.shape,
        Cb.get j = tc.entry (broadcastIndex tc.shape (unravel s.shape j)) := by
      intro j hj
      rw [hCbeq, Tensor.ofFn_get _ _ hj]
    split at h
    · cases h
    · rename_i w hone
      split_ifs at h with hcond
      cases h
      rw [hsh] at hb hCb hone
      rw [Sep.shape, hs.2.1] at hbs1 hbs2 hCbget
      obtain ⟨W, hwW, hWs, hCbW⟩ := onePerPosition_real hc hb hCb hbCb hone (by
        rw [hs.2.1] at hcond; exact hcond)
      have hwsh : w.shape = weightShape ctx.box.length s.rest := by rw [← hwW.1, hWs]
      have hts' : t.shape = 1 :: ctx.box.length :: s.rest := hs.2.2.1
      constructor
      · have hbs : broadcastShape t.shape tc.shape = some (1 :: ctx.box.length :: s.rest) := by
          rw [hts']; exact hbs1
        refine ⟨_, broadcastOp_eq BinOp.mul.apply hs.wf hc.wf hbs, hwsh, W, hwW, ?_⟩
        have h1 := broadcastOp_full_left hts' (broadcastOp_eq BinOp.mul.apply hs.wf hc.wf hbs) hbs
        refine sepW_of_scaled hs (by rw [h1.1, hsh]) (by rw [h1.2.1, hsh]) (fun p hp q hq => ?_)
        have hj : p * shapeSize s.rest + q < shapeSize (1 :: ctx.box.length :: s.rest) := by
          rw [shapeSize_one_cons]; exact lt_mul_of_row hp hq
        rw [h1.2.2 _ hj, ← hCbget _ hj, hCbW p hp q hq]
        simp only [BinOp.apply]
        ring
      · have hbs : broadcastShape tc.shape t.shape = some (1 :: ctx.box.length :: s.rest) := by
          rw [hts']; exact hbs2
        refine ⟨_, broadcastOp_eq BinOp.mul.apply hc.wf hs.wf hbs, hwsh, W, hwW, ?_⟩
        have h1 := broadcastOp_full_right hts' (broadcastOp_eq BinOp.mul.apply hc.wf hs.wf hbs) hbs
        refine sepW_of_scaled hs (by rw [h1.1, hsh]) (by rw [h1.2.1, hsh]) (fun p hp q hq => ?_)
        have hj : p * shapeSize s.rest + q < shapeSize (1 :: ctx.box.length :: s.rest) := by
          rw [shapeSize_one_cons]; exact lt_mul_of_row hp hq
        rw [h1.2.2 _ hj, ← hCbget _ hj, hCbW p hp q hq]
        rfl
    · by_cases hcx : c.exact = true
      · simp only [hcx, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
        obtain ⟨rows, hrows, h2⟩ := Step.bind_eq_val h
        cases h2
        exact rowsConst_sim (Or.inr rfl) hf hs hc hcx hb (fun _ _ => rfl)
          (Step.ofOption_eq_val hrows)
      · simp [hcx] at h

theorem mulVarSep_sim {g : Graph} {ctx : TCtx} {x : Input} (hf : LeafFacts ctx x)
    {ws : Array DT} {s : Sep} {tw ts : Tensor ℝ} {v : TV} (hw : VarR ctx x ws tw)
    (hs : SepW ctx.box x (fun _ => 1) s ts) (h : mulVarSep ws s = .val v) :
    (∃ t', broadcastOp BinOp.mul.apply tw ts = some t' ∧ TRel g ctx x v t') ∧
    (∃ t', broadcastOp BinOp.mul.apply ts tw = some t' ∧ TRel g ctx x v t') := by
  have hsh : s.shape = 1 :: ctx.box.length :: s.rest := by rw [Sep.shape, hs.2.1]
  have hts' : ts.shape = 1 :: ctx.box.length :: s.rest := hs.2.2.1
  unfold mulVarSep at h
  split at h
  · cases h
  · rename_i bs hbs
    split at h
    · cases h
    · rename_i ws' hws'
      split at h
      · rename_i ws'' hws''
        split_ifs at h with hall
        cases h
        have f1 := mapM_forall₂ hbs
        have f2 := mapM_forall₂ hws'
        have f3 := mapM_forall₂ hws''
        have hl1 := f1.length_eq
        have hl2 := f2.length_eq
        have hl3 := f3.length_eq
        have hsz : ws.toList.length = ctx.k := by simp [hw.1]
        -- each input's weight
        have heach : ∀ i < ctx.k, ∀ T, (ws.getD i emptyDT).Encl T →
            ∃ Cb W, expandOp T (s.shape.map Int.ofNat) = some Cb ∧
              (ws''.toArray.getD i emptyDT).Encl W ∧
              W.shape = weightShape ctx.box.length s.rest ∧
              ∀ p < ctx.box.length, ∀ q < shapeSize s.rest,
                Cb.get (p * shapeSize s.rest + q) = W.get p := by
          intro i hi T hT
          have hi1 : i < ws.toList.length := by simp [hw.1, hi]
          have hb := forall₂_getD f1 hi1 emptyDT emptyDT
          rw [array_getD_toList] at hb
          have hi2 : i < bs.length := by omega
          have ho := forall₂_getD f2 hi2 emptyDT none
          have hi3 : i < ws'.length := by omega
          have hw3 := forall₂_getD f3 hi3 none emptyDT
          simp only [id] at hw3
          rw [hw3] at ho
          obtain ⟨Cb, hCb, hbCb⟩ := dtBroadcastTo_sim hT hb
          have hcond : ((ws.getD i emptyDT).exact ||
              (ws.getD i emptyDT).shape == weightShape ctx.box.length s.rest) = true := by
            have := Array.all_eq_true.mp hall i (by rw [hw.1]; exact hi)
            rw [hs.2.1] at this
            simpa [Array.getD_eq_getD_getElem?, hw.1, hi] using this
          rw [hsh] at hb hCb ho
          obtain ⟨W, hwW, hWs, hCbW⟩ := onePerPosition_real hT hb hCb hbCb ho hcond
          refine ⟨Cb, W, by rw [hsh]; exact hCb, ?_, hWs, hCbW⟩
          rw [list_getD_toArray]
          exact hwW
        obtain ⟨Cb, W, hCb, hwW, hWs, hCbW⟩ := heach _ hf.idx_lt _ hw.2.2
        obtain ⟨hCbeq, hle, hfit⟩ := expandOp_nat_spec hCb
        obtain ⟨hbs1, hbs2⟩ := broadcastShape_of_fits hle hfit
        rw [hsh] at hbs1 hbs2 hCbeq
        have hCbget : ∀ j < shapeSize (1 :: ctx.box.length :: s.rest),
            Cb.get j =
              tw.entry (broadcastIndex tw.shape (unravel (1 :: ctx.box.length :: s.rest) j)) := by
          intro j hj
          rw [hCbeq, Tensor.ofFn_get _ _ hj]
        have hrel : TRel g ctx x (.wsepv ws''.toArray s) =
            WSepVR ctx x ws''.toArray s := rfl
        have hvr : ∀ t', SepW ctx.box x (fun p => W.get p) s t' →
            WSepVR ctx x ws''.toArray s t' := by
          intro t' ht'
          refine ⟨by simp; omega, fun i hi => ?_, W, hwW, ht'⟩
          obtain ⟨T, hT⟩ := hw.2.1 i hi
          obtain ⟨-, W', -, hwW', hW's, -⟩ := heach i hi T hT
          exact ⟨by rw [← hwW'.1, hW's], W', hwW'⟩
        constructor
        · have hbs : broadcastShape tw.shape ts.shape = some (1 :: ctx.box.length :: s.rest) := by
            rw [hts']; exact hbs2
          refine ⟨_, broadcastOp_eq BinOp.mul.apply hw.2.2.wf hs.wf hbs, ?_⟩
          rw [hrel]
          apply hvr
          have h1 :=
            broadcastOp_full_right hts' (broadcastOp_eq BinOp.mul.apply hw.2.2.wf hs.wf hbs) hbs
          refine sepW_of_scaled hs (by rw [h1.1, hsh]) (by rw [h1.2.1, hsh]) (fun p hp q hq => ?_)
          have hj : p * shapeSize s.rest + q < shapeSize (1 :: ctx.box.length :: s.rest) := by
            rw [shapeSize_one_cons]; exact lt_mul_of_row hp hq
          rw [h1.2.2 _ hj, ← hCbget _ hj, hCbW p hp q hq]
          rfl
        · have hbs : broadcastShape ts.shape tw.shape = some (1 :: ctx.box.length :: s.rest) := by
            rw [hts']; exact hbs1
          refine ⟨_, broadcastOp_eq BinOp.mul.apply hs.wf hw.2.2.wf hbs, ?_⟩
          rw [hrel]
          apply hvr
          have h1 :=
            broadcastOp_full_left hts' (broadcastOp_eq BinOp.mul.apply hs.wf hw.2.2.wf hbs) hbs
          refine sepW_of_scaled hs (by rw [h1.1, hsh]) (by rw [h1.2.1, hsh]) (fun p hp q hq => ?_)
          have hj : p * shapeSize s.rest + q < shapeSize (1 :: ctx.box.length :: s.rest) := by
            rw [shapeSize_one_cons]; exact lt_mul_of_row hp hq
          rw [h1.2.2 _ hj, ← hCbget _ hj, hCbW p hp q hq]
          simp only [BinOp.apply]
          ring
      · cases h

/-! ## Sums over a dimension of the rows -/

theorem sum_index_lt {A n inner q' k : ℕ} (hq : q' < A * inner) (hk : k < n) :
    (q' / inner * n + k) * inner + q' % inner < A * (n * inner) := by
  have hinner : 0 < inner := by
    rcases Nat.eq_zero_or_pos inner with h | h
    · rw [h, Nat.mul_zero] at hq; omega
    · exact h
  have h1 : q' / inner < A := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hq)
  have h2 : q' % inner < inner := Nat.mod_lt _ hinner
  calc (q' / inner * n + k) * inner + q' % inner < (q' / inner * n + k) * inner + inner := by omega
    _ = (q' / inner * n + k + 1) * inner := by ring
    _ ≤ ((q' / inner + 1) * n) * inner := Nat.mul_le_mul_right _ (by nlinarith)
    _ ≤ (A * n) * inner := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h1)
    _ = A * (n * inner) := by ring

theorem sumOp_size {α : Type} [Zero α] [Add α] {t : Tensor α} {d : ℕ} (hd : d < t.shape.length)
    (hw : t.data.size = shapeSize t.shape) :
    t.data.size =
      shapeSize (t.shape.take d) * t.shape.getD d 0 * shapeSize (t.shape.drop (d + 1)) := by
  rw [hw, shapeSize_split _ hd, strides_getD _ hd]
  ring

theorem sumRows_sim {ctx : TCtx} {x : Input} (hf : LeafFacts ctx x) {s s' : Sep} {t : Tensor ℝ}
    {dim : ℤ} {d : ℕ} (hs : SepW ctx.box x (fun _ => 1) s t)
    (hd : normDim dim t.shape.length = some d) (hd2 : 2 ≤ d) (h : sumRows s d = .val s') :
    ∃ t', sumOp dim t = some t' ∧ SepW ctx.box x (fun _ => 1) s' t' := by
  obtain ⟨hpos, hrl, hts, htsz, hrok, hval⟩ := hs
  unfold sumRows at h
  obtain ⟨rows, hrows, h2⟩ := Step.bind_eq_val h
  cases h2
  have hrows' := mapM_forall₂ (Step.ofOption_eq_val hrows)
  have hlen := hrows'.length_eq
  have hdlt := normDim_lt hd
  rw [hts] at hdlt
  simp only [List.length_cons] at hdlt
  obtain ⟨e, rfl⟩ : ∃ e, d = 2 + e := ⟨d - 2, by omega⟩
  have hel : e < s.rest.length := by omega
  have hts' : t.shape = [1, ctx.box.length] ++ s.rest := hts
  have hsize := sumOp_size (t := t) (d := 2 + e) (by rw [hts]; simp; omega)
    (by rw [htsz, hts, shapeSize_one_cons])
  have hsum := sumOp_eq hd hsize
  obtain ⟨ht's, ht'get⟩ := sumOp_rows hts' hel (by rw [hd]; simp) hsum
  set S := shapeSize s.rest with hSdef
  set S' := shapeSize (s.rest.eraseIdx e)
  set inner := shapeSize (s.rest.drop (e + 1)) with hinner
  set n := s.rest.getD e 0 with hn
  have hS : S = shapeSize (s.rest.take e) * (n * inner) := by
    rw [hSdef, shapeSize_split s.rest hel, strides_getD _ hel]
  have hS' : S' = shapeSize (s.rest.take e) * inner := (shapeSize_eraseIdx_mul s.rest e).symm
  -- the rows
  have hrow : ∀ p < ctx.box.length, (rows.getD p emptyDT).exact = true ∧
      ∃ R', (rows.getD p emptyDT).Encl R' ∧ R'.shape = [nTok ctx.box p] ++ s.rest.eraseIdx e ∧
        ∀ j < nTok ctx.box p, ∀ q' < S', R'.get (j * S' + q') =
          ((List.range n).map fun k => (s.rows.getD p emptyDT).real.get
            (j * S + ((q' / inner * n + k) * inner + q' % inner))).sum := by
    intro p hp
    have hp' : p < s.rows.length := by rw [hrl]; exact hp
    have h1 := forall₂_getD hrows' hp' emptyDT emptyDT
    have hR := (hrok p hp).encl
    obtain ⟨R', hR', hR'e⟩ := dsum_sim hR h1
    have hRs : (s.rows.getD p emptyDT).real.shape = [nTok ctx.box p] ++ s.rest := (hrok p hp).2.2.2
    have hnd : normDim ((2 + e - 1 : ℕ) : ℤ) (s.rows.getD p emptyDT).real.shape.length =
        some ([nTok ctx.box p].length + e) := by
      rw [hRs, show (2 + e - 1 : ℕ) = 1 + e by omega]
      unfold normDim
      have h1 : ¬ (((1 + e : ℕ) : ℤ) < 0) := by omega
      have h3 : (((1 + e : ℕ) : ℤ)).toNat = 1 + e := Int.toNat_natCast _
      have h2 : (((1 + e : ℕ) : ℤ)).toNat < ([nTok ctx.box p] ++ s.rest).length := by
        rw [h3]; simp; omega
      rw [ite_eq_right h1, ite_eq_left h2, h3]
      simp
    obtain ⟨hR's, hR'get⟩ := sumOp_rows hRs hel hnd hR'
    refine ⟨by rw [dsum_exact h1]; exact (hrok p hp).2.1, R', hR'e, hR's, fun j hj q' hq' => ?_⟩
    exact hR'get j (by simpa [shapeSize] using hj) q' hq'
  have hrowshape : ∀ p < ctx.box.length,
      (rows.getD p emptyDT).shape = nTok ctx.box p :: s.rest.eraseIdx e := by
    intro p hp
    obtain ⟨-, R', hR', hR's, -⟩ := hrow p hp
    rw [← hR'.1, hR's]
    rfl
  have hhead : (rows.headD emptyDT).shape.drop 1 = s.rest.eraseIdx e := by
    have h0 : rows.headD emptyDT = rows.getD 0 emptyDT := by
      cases rows with
      | nil => rw [List.length_nil] at hlen; omega
      | cons a l => rfl
    rw [h0, hrowshape 0 hpos]
    rfl
  refine ⟨_, hsum, hpos, by rw [← hlen, hrl], ?_, ?_, fun p hp => ?_, fun p hp q' hq' => ?_⟩
  · rw [hhead]
    exact ht's
  · rw [hhead]
    simp only [sumData_size, hts',
      List.eraseIdx_append_of_length_le (show [1, ctx.box.length].length ≤ 2 + e by simp)]
    simp [shapeSize_cons]
  · rw [hhead]
    obtain ⟨hex, R', hR', -, -⟩ := hrow p hp
    exact ⟨hR'.ok, hex, hR'.2.2.2.2.1 hex, hrowshape p hp⟩
  · rw [hhead] at hq' ⊢
    obtain ⟨hex, R', hR', -, hR'get⟩ := hrow p hp
    have hp1 : p < shapeSize [1, ctx.box.length] := by simpa [shapeSize] using hp
    rw [ht'get p hp1 q' hq', one_mul, ← hR'.get_real hex, hR'get _ (hf.row_lt p hp) q' hq']
    apply congrArg List.sum
    apply List.map_congr_left
    intro k hk
    have hk' := List.mem_range.mp hk
    have hlt : (q' / inner * n + k) * inner + q' % inner < S := by
      rw [hS]
      exact sum_index_lt (by rw [← hS']; exact hq') hk'
    rw [hval p hp _ hlt, one_mul]

/-! ## Products with a matrix -/

theorem matmulSep_sim {ctx : TCtx} {x : Input} (hf : LeafFacts ctx x) {s s' : Sep}
    {t tb : Tensor ℝ} {b : DT} {dd d' : ℕ} (hs : SepW ctx.box x (fun _ => 1) s t)
    (hb : b.Encl tb) (hbx : b.exact = true) (hrest : s.rest = [dd]) (hbs : b.shape = [dd, d'])
    (h : matmulSep s b = .val s') :
    ∃ t', matmulOp t tb = some t' ∧ SepW ctx.box x (fun _ => 1) s' t' := by
  obtain ⟨hpos, hrl, hts, htsz, hrok, hval⟩ := hs
  unfold matmulSep at h
  obtain ⟨rows, hrows, h2⟩ := Step.bind_eq_val h
  cases h2
  have hrows' := mapM_forall₂ (Step.ofOption_eq_val hrows)
  have hlen := hrows'.length_eq
  rw [hrest] at hts hrok hval htsz
  have hdd : shapeSize [dd] = dd := by simp [shapeSize]
  have htbs : tb.shape = [dd, d'] := by rw [hb.1, hbs]
  have hwf : t.wellFormed = true := by simp [Tensor.wellFormed, hts, htsz, shapeSize_one_cons, hdd]
  obtain ⟨t', ht', ht's, ht'sz, ht'get⟩ := matmulOp_three hts htbs hwf hb.wf
  have hrow : ∀ p < ctx.box.length, (rows.getD p emptyDT).exact = true ∧
      ∃ R', (rows.getD p emptyDT).Encl R' ∧ R'.shape = [nTok ctx.box p, d'] ∧
        ∀ j < nTok ctx.box p, ∀ c < d', R'.get (j * d' + c) =
          ((List.range dd).map fun k => (s.rows.getD p emptyDT).real.get (j * dd + k) *
            tb.get (k * d' + c)).sum := by
    intro p hp
    have hp' : p < s.rows.length := by rw [hrl]; exact hp
    have h1 := forall₂_getD hrows' hp' emptyDT emptyDT
    have hR := (hrok p hp).encl
    obtain ⟨R', hR', hR'e⟩ := dmatmul_sim hR hb h1
    have hRs : (s.rows.getD p emptyDT).real.shape = [nTok ctx.box p, dd] := (hrok p hp).2.2.2
    obtain ⟨R'', hR'', hR''s, -, hR''get⟩ := matmulOp_two hRs htbs hR.wf hb.wf
    rw [hR''] at hR'
    simp only [Option.some.injEq] at hR'
    subst hR'
    refine ⟨by rw [dmatmul_exact h1, (hrok p hp).2.1, hbx]; rfl, R'', hR'e, hR''s,
      fun j hj c hc => ?_⟩
    rw [hR''get j hj c hc]
  have hrowshape : ∀ p < ctx.box.length, (rows.getD p emptyDT).shape = [nTok ctx.box p, d'] := by
    intro p hp
    obtain ⟨-, R', hR', hR's, -⟩ := hrow p hp
    rw [← hR'.1, hR's]
  have hhead : (rows.headD emptyDT).shape.drop 1 = [d'] := by
    have h0 : rows.headD emptyDT = rows.getD 0 emptyDT := by
      cases rows with
      | nil => rw [List.length_nil] at hlen; omega
      | cons a l => rfl
    rw [h0, hrowshape 0 hpos]
    rfl
  have hd' : shapeSize [d'] = d' := by simp [shapeSize]
  refine ⟨t', ht', hpos, by rw [← hlen, hrl], by rw [hhead, ht's], by rw [hhead, ht'sz, hd'],
    fun p hp => ?_, fun p hp c hc => ?_⟩
  · rw [hhead]
    obtain ⟨hex, R', hR', -, -⟩ := hrow p hp
    exact ⟨hR'.ok, hex, hR'.2.2.2.2.1 hex, hrowshape p hp⟩
  · rw [hhead, hd'] at hc ⊢
    obtain ⟨hex, R', hR', -, hR'get⟩ := hrow p hp
    rw [ht'get p hp c hc, one_mul, ← hR'.get_real hex, hR'get _ (hf.row_lt p hp) c hc]
    apply congrArg List.sum
    apply List.map_congr_left
    intro k hk
    have := hval p hp k (by rw [hdd]; exact List.mem_range.mp hk)
    rw [hdd, one_mul] at this
    rw [this]

/-! ## Selecting one position; sums over the positions -/

theorem dtScalar_encl (m : ℤ) : (dtScalar m).Encl ⟨[], #[(m : ℝ)]⟩ := by
  refine DT.Encl.mk rfl rfl rfl rfl (fun _ => rfl) ?_
  intro j hj
  have hj0 : j = 0 := by simpa [shapeSize, dtScalar] using hj
  subst hj0
  simp [dtScalar, dv, mget, Tensor.get]

theorem dtZeros_encl (sh : List ℕ) :
    (dtZeros sh).Encl ⟨sh, Array.replicate (shapeSize sh) 0⟩ := by
  apply DT.ofInts_encl rfl (by simp) (by simp)
  intro j _
  simp only [Tensor.get, mget, getD_replicate, dv_zero]

theorem zeros_get (sh : List ℕ) (j : ℕ) :
    (⟨sh, Array.replicate (shapeSize sh) 0⟩ : Tensor ℝ).get j = 0 := by
  simp only [Tensor.get, getD_replicate]

theorem tGetitem_sim {g : Graph} {ctx : TCtx} {x : Input} {s : Sep} {t : Tensor ℝ}
    {items : List IndexItem} {v : TV} (hs : SepW ctx.box x (fun _ => 1) s t)
    (h : tGetitem s items = .val v) : ∃ t', indexOp t items = some t' ∧ TRel g ctx x v t' := by
  unfold tGetitem at h
  split at h
  · rename_i p
    split_ifs at h with hp
    cases h
    have hp' : p < ctx.box.length := by rw [← hs.2.1]; exact hp
    obtain ⟨R, hR, hRs, hRsz, hRget⟩ := indexOp_getitem hs.2.2.1 hs.wf hp'
    refine ⟨R, hR, s.rest, rfl, hRs, hRsz, _, dtZeros_encl _, [1], ?_, fun q hq => ?_⟩
    · refine List.Forall₂.cons ⟨hp', hs.2.2.2.2.1 p hp', Or.inl rfl, _, dtScalar_encl 1, ?_⟩
        List.Forall₂.nil
      simp [wIdx, dtScalar, Tensor.get]
    · rw [hRget q hq, hs.2.2.2.2.2 p hp' q hq, zeros_get]
      simp [termsVal]
  · cases h

/-- The weight of each term of a sum over the positions. -/
def wOf (w : Option (Sum DT (Array DT))) (p : ℕ) (rest : List ℕ) : Option DT :=
  match w with
  | none => some (dtScalar 1)
  | some (.inl w) => weightAt w p rest
  | some (.inr ws) => weightsAt ws p rest

theorem sumPositions_terms {s : Sep} {w : Option (Sum DT (Array DT))} {m : Mix}
    (h : sumPositions s w = .val m) :
    m.const = dtZeros (1 :: s.rest) ∧ m.terms.length = s.rows.length ∧
      ∀ p < s.rows.length, ∃ wp, wOf w p s.rest = some wp ∧
        m.terms.getD p ⟨emptyDT, 0, emptyDT⟩ = ⟨wp, p, s.rows.getD p emptyDT⟩ := by
  unfold sumPositions at h
  obtain ⟨terms, hterms, h2⟩ := Step.bind_eq_val h
  cases h2
  obtain ⟨hlen, hper⟩ := mapM_zip_range (Step.ofOption_eq_val hterms)
  refine ⟨rfl, hlen, fun p hp => ?_⟩
  have := hper p hp emptyDT ⟨emptyDT, 0, emptyDT⟩
  rcases w with _ | w | ws
  · simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at this
    exact ⟨dtScalar 1, rfl, this.symm⟩
  · cases hw : weightAt w p s.rest with
    | none => simp [hw] at this
    | some wp =>
      simp only [hw, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq] at this
      exact ⟨wp, hw, this.symm⟩
  · cases hw : weightsAt ws p s.rest with
    | none => simp [hw] at this
    | some wp =>
      simp only [hw, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq] at this
      exact ⟨wp, hw, this.symm⟩

theorem sumPositions_sim {ctx : TCtx} {x : Input} {s : Sep} {t : Tensor ℝ}
    {wt : ℕ → ℝ} {w : Option (Sum DT (Array DT))} {m : Mix} {dim : ℤ}
    (hs : SepW ctx.box x wt s t)
    (hw : ∀ p < ctx.box.length, ∀ wp, wOf w p s.rest = some wp →
      (wp.shape = [] ∨ wp.shape = [ctx.k]) ∧ ∃ Ω, wp.Encl Ω ∧ wt p = Ω.get (wIdx ctx x wp))
    (hd : normDim dim t.shape.length = some 1) (h : sumPositions s w = .val m) :
    ∃ t', sumOp dim t = some t' ∧ MixR ctx x m t' := by
  obtain ⟨hpos, hrl, hts, htsz, hrok, hval⟩ := hs
  obtain ⟨hconst, hlen, hterm⟩ := sumPositions_terms h
  have hts' : t.shape = [1] ++ (ctx.box.length :: s.rest) := hts
  have hsize := sumOp_size (t := t) (d := 1) (by rw [hts]; simp)
    (by rw [htsz, hts, shapeSize_one_cons])
  have hsum := sumOp_eq hd hsize
  obtain ⟨ht's, ht'get⟩ := sumOp_rows hts' (e := 0) (by simp) (by rw [hd]; rfl) hsum
  set S := shapeSize s.rest
  have hS' : shapeSize ((ctx.box.length :: s.rest).eraseIdx 0) = S := rfl
  -- the terms and their weights
  have hterm' : ∀ p < ctx.box.length, ∃ wp, wOf w p s.rest = some wp ∧
      m.terms.getD p ⟨emptyDT, 0, emptyDT⟩ = ⟨wp, p, s.rows.getD p emptyDT⟩ := fun p hp =>
    hterm p (by rw [hrl]; exact hp)
  have hforall :
      List.Forall₂ (TermR ctx x s.rest) m.terms ((List.range ctx.box.length).map wt) := by
    apply List.forall₂_iff_get.mpr
    refine ⟨by rw [hlen, hrl]; simp, fun i h1 h2 => ?_⟩
    have hi : i < ctx.box.length := by rw [← hrl, ← hlen]; exact h1
    obtain ⟨wp, hwp, hti⟩ := hterm' i hi
    have hget : m.terms.get ⟨i, h1⟩ = ⟨wp, i, s.rows.getD i emptyDT⟩ := by
      rw [← hti, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some]
      rfl
    rw [hget]
    simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range]
    obtain ⟨hsh, Ω, hΩ, hwt⟩ := hw i hi wp hwp
    exact ⟨hi, hrok i hi, hsh, Ω, hΩ, hwt⟩
  have hsz : (⟨t.shape.eraseIdx 1, sumData t 1⟩ : Tensor ℝ).data.size = S := by
    simp only [sumData_size, hts]
    simp [shapeSize_cons, S]
  refine ⟨_, hsum, s.rest, (by rw [hconst]; rfl), (by rw [ht's]; rfl), hsz, _,
    (by rw [hconst]; exact dtZeros_encl _), _, hforall, fun q hq => ?_⟩
  have := ht'get 0 (by simp [shapeSize]) q (by rw [hS']; exact hq)
  rw [hS', Nat.zero_mul, Nat.zero_add] at this
  rw [this, zeros_get]
  simp only [zero_add, Nat.zero_mul, List.drop_one, List.tail_cons,
    List.getD_cons_zero]
  rw [Nat.div_eq_of_lt hq, Nat.zero_mul, Nat.mod_eq_of_lt hq]
  simp only [Nat.zero_add]
  unfold termsVal
  -- both sides sum over the positions
  have hzip : List.zipWith (fun τ ω => ω * τ.rows.real.get (rowOf ctx.box x τ.pos * S + q))
      m.terms ((List.range ctx.box.length).map wt) = (List.range ctx.box.length).map fun p =>
        wt p * (s.rows.getD p emptyDT).real.get (rowOf ctx.box x p * S + q) := by
    apply List.ext_getElem (by simp [hlen, hrl])
    intro i h1 h2
    have hi : i < ctx.box.length := by simpa using h2
    have hi' : i < m.terms.length := by rw [hlen, hrl]; exact hi
    obtain ⟨wp, -, hti⟩ := hterm' i hi
    have hget : m.terms[i] = ⟨wp, i, s.rows.getD i emptyDT⟩ := by
      rw [← hti, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
    simp only [List.getElem_zipWith, List.getElem_map, List.getElem_range, hget]
  rw [hzip]
  apply congrArg List.sum
  apply List.map_congr_left
  intro k hk
  rw [hval k (List.mem_range.mp hk) q hq]

end CompactCheck
