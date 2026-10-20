import CompactCheck.TokensSound

/-!
# Soundness of token_interval leaves: the margin bound and the leaf

1. `lowestMargin_sound`: the lowest margin bound the checker computes is a
   lower bound on the real margin of the label over every other output.
2. `generalTokenInterval_correct`: every input of a box that a
   token_interval leaf certifies is answered correctly, in the sense of
   `Spec.lean`.
3. `checkGeneral_sound`: the soundness theorem for proofs on general
   networks, now with token_interval leaves.
-/

namespace CompactCheck

/-! ## The margin bound -/

/-- The real logits have their strict maximum at the label. -/
def LabelWins (t : Tensor ℝ) (l : ℕ) : Prop :=
  t.shape = [1, t.data.size] ∧ l < t.data.size ∧
    ∀ j < t.data.size, j ≠ l → t.get j < t.get l

/-- Lower bounds on the margins of the label, one in `all` for every other
    output: if their minimum is positive, the label wins. -/
theorem margin_correct {t : Tensor ℝ} {n l : ℕ} {all : List ℤ} {e : ℤ}
    (hs : t.shape = [1, n]) (hsz : t.data.size = n) (hl : l < n)
    (hb : ∀ o < n, o ≠ l → ∃ a ∈ all, dv a e ≤ t.get l - t.get o)
    (hpos : ∀ m, all.min? = some m → 0 < m) : LabelWins t l := by
  refine ⟨by rw [hs, hsz], by rw [hsz]; exact hl, fun j hj hne => ?_⟩
  rw [hsz] at hj
  obtain ⟨a, ha, hda⟩ := hb j hj hne
  cases hm : all.min? with
  | none =>
    rw [List.min?_eq_none_iff] at hm
    subst hm
    simp at ha
  | some m =>
    have hm0 := hpos m hm
    have hma := (List.min?_eq_some_iff.mp hm).2 a ha
    have h0 : 0 < dv a e := by
      have := dv_lt_dv e (show (0 : ℤ) < a by omega)
      simpa using this
    linarith

/-- An interval value: the label's lower end minus every other output's
    upper end. -/
theorem dtMargin_sound {d : DT} {t : Tensor ℝ} {n l : ℕ} (hd : d.Encl t) (hn : d.shape = [1, n])
    (hl : l < n) {r : Option (ℤ × ℤ)} (h : dtMargin d l = r)
    (hr : ∀ m e, r = some (m, e) → 0 < m) : LabelWins t l := by
  have hsz : shapeSize d.shape = n := by rw [hn]; simp [shapeSize]
  refine margin_correct (all := ((List.range (shapeSize d.shape)).filter (· != l)).map
      fun o => mget d.lo l - mget d.hi o) (e := d.e) (hd.1.trans hn) (hd.2.1.trans hsz) hl ?_ ?_
  · intro o ho hne
    refine ⟨mget d.lo l - mget d.hi o, ?_, ?_⟩
    · simp only [List.mem_map, List.mem_filter, List.mem_range, bne_iff_ne, ne_eq]
      exact ⟨o, ⟨by omega, hne⟩, rfl⟩
    · rw [dv_sub]
      have h1 := (hd.2.2.2.2.2 l).1
      have h2 := (hd.2.2.2.2.2 o).2
      linarith
  · intro m hm
    apply hr m d.e
    rw [← h]
    simp only [dtMargin, hm, Option.map_some]

/-- Per-input values: `x`'s value is one of them, at the lowest exponent. -/
theorem varMargin_sound {ctx : TCtx} {x : Input} (hf : LeafFacts ctx x) {vs : Array DT}
    {t : Tensor ℝ} (hv : VarR ctx x vs t) {n l : ℕ}
    (hn : (vs.getD 0 emptyDT).shape = [1, n] ∨ t.shape = [1, n]) (hl : l < n)
    {r : Option (ℤ × ℤ)} (h : varMargin vs l = some r)
    (hr : ∀ m e, r = some (m, e) → 0 < m) :
    LabelWins t l := by
  obtain ⟨hsize, -, hX⟩ := hv
  have hidx : inputIdx ctx x < vs.size := hsize ▸ hf.idx_lt
  set X := vs.getD (inputIdx ctx x) emptyDT with hXdef
  have hXmem : X ∈ vs.toList := by
    rw [hXdef, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hidx, Option.getD_some]
    exact Array.mem_toList_iff.mpr (Array.getElem_mem hidx)
  unfold varMargin at h
  by_cases hemp : vs.isEmpty = true
  · simp [hemp] at h
  by_cases hall : (vs.all fun y => y.shape == (vs.getD 0 emptyDT).shape) = true
  swap
  · rw [Bool.not_eq_true] at hall
    simp only [hemp, hall, Bool.false_eq_true, ↓reduceIte, Bool.not_false] at h
    cases h
  simp only [hemp, hall, Bool.false_eq_true, ↓reduceIte, Bool.not_true, pure,
    Option.some.injEq] at h
  set e := (vs.toList.map (·.e)).foldl min (vs.getD 0 emptyDT).e with he
  have hXe : e ≤ X.e :=
    foldl_min_le_int _ _ _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hXmem))
  have hX0 : X.shape = (vs.getD 0 emptyDT).shape := by
    have := Array.all_eq_true'.mp hall X (Array.mem_toList_iff.mp hXmem)
    simpa using this
  have hXs : X.shape = [1, n] := by
    rcases hn with hn | hn
    · exact hX0.trans hn
    · exact hX.1.symm.trans hn
  have hY := DT.at_encl hX e
  have hYe : (X.at e).e = e := DT.at_e hXe
  have hn' : shapeSize X.shape = n := by rw [hXs]; simp [shapeSize]
  refine margin_correct (all := (vs.toList.map fun y =>
      ((List.range (shapeSize (y.at e).shape)).filter (· != l)).map fun o =>
        mget (y.at e).lo l - mget (y.at e).hi o).flatten) (e := e)
    (hX.1.trans hXs) (hX.2.1.trans hn') hl (fun o ho hne => ?_)
    (fun m hm => hr m e (by rw [← h, hm]; rfl))
  refine ⟨mget (X.at e).lo l - mget (X.at e).hi o,
    List.mem_flatten.mpr ⟨_, List.mem_map_of_mem hXmem, List.mem_map.mpr ⟨o,
      List.mem_filter.mpr ⟨List.mem_range.mpr (by rw [DT.at_shape, hn']; exact ho),
        by simpa using hne⟩, rfl⟩⟩, ?_⟩
  rw [dv_sub]
  have h1 := (hY.2.2.2.2.2 l).1
  have h2 := (hY.2.2.2.2.2 o).2
  rw [hYe] at h1 h2
  linarith

/-! ### Mixes -/

theorem getD_map_zip_range {β γ : Type} (g : ℕ × β → γ) {l : List β} {n o : ℕ}
    (hl : l.length = n) (ho : o < n) (d : β) (d' : γ) :
    (((List.range n).zip l).map g).getD o d' = g (o, l.getD o d) := by
  subst hl
  rw [list_getD_map g (by rw [length_zip_range]; exact ho) (0, d) d', getD_zip_range l ho (0, d)]

theorem length_map_zip_range {β γ : Type} (g : ℕ × β → γ) {l : List β} {n : ℕ}
    (hl : l.length = n) : (((List.range n).zip l).map g).length = n := by
  simp [hl]

theorem range_getD {n o : ℕ} (ho : o < n) : (List.range n).getD o 0 = o := by
  simp [List.getD_eq_getElem?_getD, ho]

theorem getD_mem_of_lt {β : Type} {l : List β} {i : ℕ} (hi : i < l.length) (d : β) :
    l.getD i d ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact List.getElem_mem hi

theorem mem_zip_range {β : Type} {row : List β} {n o : ℕ} (hrow : row.length = n) (ho : o < n)
    (d : β) : (o, row.getD o d) ∈ (List.range n).zip row := by
  subst hrow
  rw [← getD_zip_range row ho (0, d)]
  exact getD_mem_of_lt (by rw [length_zip_range]; exact ho) _

theorem min_mul_le_real {A A' x y : ℝ} (h1 : A ≤ x) (h2 : x ≤ A') :
    min (A * y) (A' * y) ≤ x * y := by
  rcases le_total 0 y with hy | hy
  · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right h1 hy)
  · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_right h2 hy)

/-- The bounds of `x`'s row: `rowsN` rows, `x`'s with `n` bounds at the
    exponent `e0`, each below `F`. -/
def MarginInv (acc : List (List ℤ)) (rowsN iRow n : ℕ) (e0 : ℤ) (F : ℕ → ℝ) : Prop :=
  acc.length = rowsN ∧ iRow < rowsN ∧ (acc.getD iRow []).length = n ∧
    ∀ o < n, dv ((acc.getD iRow []).getD o 0) e0 ≤ F o

theorem MarginInv.mono {acc : List (List ℤ)} {rowsN iRow n : ℕ} {e0 : ℤ} {F G : ℕ → ℝ}
    (h : MarginInv acc rowsN iRow n e0 F) (hFG : ∀ o < n, F o ≤ G o) :
    MarginInv acc rowsN iRow n e0 G :=
  ⟨h.1, h.2.1, h.2.2.1, fun o ho => (h.2.2.2 o ho).trans (hFG o ho)⟩

/-- An exact weight times a difference of rows, or the lower of its two
    ends times it: below the real weight times the real difference. -/
theorem weighted_bound {w : DT} {Ω : Tensor ℝ} (hΩ : w.Encl Ω) (wi : ℕ) (d eR : ℤ) :
    dv (if w.exact = true then mget w.lo wi * d else min (mget w.lo wi * d) (mget w.hi wi * d))
      (w.e + eR) ≤ Ω.get wi * dv d eR := by
  have hb := hΩ.2.2.2.2.2 wi
  split_ifs with hex
  · have hlh := hΩ.2.2.2.2.1 hex
    rw [hlh] at hb ⊢
    rw [dv_mul, le_antisymm hb.2 hb.1]
  · rw [dv_min, dv_mul, dv_mul]
    exact min_mul_le_real hb.1 hb.2

/-- The lowest of the four corners: below the real weight times the real
    difference of rows, for any row of the box. -/
theorem corner_bound {w : DT} {Ω : Tensor ℝ} (hΩ : w.Encl Ω) {wi : ℕ} (hwi : wi < w.lo.size)
    (hwi' : wi < w.hi.size) (f : ℕ → ℤ) {N r0 : ℕ} (hr0 : r0 < N) (eR : ℤ) :
    dv (min
        (min (w.lo.foldl min (w.lo.getD 0 0) * (List.range N).foldl (fun m r => min m (f r)) (f 0))
          (w.lo.foldl min (w.lo.getD 0 0) * (List.range N).foldl (fun m r => max m (f r)) (f 0)))
        (min (w.hi.foldl max (w.hi.getD 0 0) * (List.range N).foldl (fun m r => min m (f r)) (f 0))
          (w.hi.foldl max (w.hi.getD 0 0) * (List.range N).foldl (fun m r => max m (f r)) (f 0))))
      (w.e + eR) ≤ Ω.get wi * dv (f r0) eR := by
  have hb := hΩ.2.2.2.2.2 wi
  have hmem : r0 ∈ List.range N := List.mem_range.mpr hr0
  have h1 : dv (w.lo.foldl min (w.lo.getD 0 0)) w.e ≤ Ω.get wi := by
    refine le_trans (dv_le_dv _ ?_) hb.1
    have := array_foldl_min_le hwi
    simpa [mget, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hwi] using this
  have h2 : Ω.get wi ≤ dv (w.hi.foldl max (w.hi.getD 0 0)) w.e := by
    refine le_trans hb.2 (dv_le_dv _ ?_)
    have := array_le_foldl_max hwi'
    simpa [mget, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hwi'] using this
  have h3 := dv_le_dv eR (foldl_min_le_mem f (List.range N) (f 0) hmem)
  have h4 := dv_le_dv eR (le_foldl_max_mem f (List.range N) (f 0) hmem)
  rw [dv_min, dv_min, dv_min, dv_mul, dv_mul, dv_mul, dv_mul]
  exact (mul_mem_corners h1 h2 h3 h4).1

/-- **One term**: the bounds go down by at most the term's real share of
    the margin. -/
theorem marginStep_sound {ctx : TCtx} {x : Input} (hf : LeafFacts ctx x) {n l : ℕ} {e0 : ℤ}
    {rowsN iRow : ℕ} (hrowsN : rowsN = if ctx.aligned then ctx.k else 1)
    (hiRow : iRow = if ctx.aligned then inputIdx ctx x else 0)
    {τ : Term} {ω : ℝ} (hτ : TermR ctx x [n] τ ω) (he0 : e0 ≤ τ.w.e + τ.rows.e)
    {acc acc' : List (List ℤ)} {F : ℕ → ℝ} (hinv : MarginInv acc rowsN iRow n e0 F)
    (h : marginStep ctx n l e0 rowsN acc τ = some acc') :
    MarginInv acc' rowsN iRow n e0 (fun o => F o + ω *
      (τ.rows.real.get (rowOf ctx.box x τ.pos * n + l) -
        τ.rows.real.get (rowOf ctx.box x τ.pos * n + o))) := by
  obtain ⟨hpos, ⟨-, -, -, hRs⟩, hwshape, Ω, hΩ, hω⟩ := hτ
  obtain ⟨hlen, hiR, hrowlen, hbound⟩ := hinv
  have hr0 : rowOf ctx.box x τ.pos < nTok ctx.box τ.pos := hf.row_lt _ hpos
  have hlen2 : (τ.rows.shape.length != 2) = false := by simp [hRs]
  have htok : τ.rows.shape.headD 0 = nTok ctx.box τ.pos := by simp [hRs]
  have hshift : ∀ Y : ℤ, dv (Y * 2 ^ (τ.w.e + τ.rows.e - e0).toNat) e0 =
      dv Y (τ.w.e + τ.rows.e) := by
    intro Y
    have := dv_shift Y (τ.w.e + τ.rows.e) (τ.w.e + τ.rows.e - e0).toNat
    rwa [Int.toNat_of_nonneg (by omega), sub_sub_cancel] at this
  have hδ : ∀ o, dv (mget τ.rows.lo (rowOf ctx.box x τ.pos * n + l) -
      mget τ.rows.lo (rowOf ctx.box x τ.pos * n + o)) τ.rows.e =
      τ.rows.real.get (rowOf ctx.box x τ.pos * n + l) -
        τ.rows.real.get (rowOf ctx.box x τ.pos * n + o) := by
    intro o
    rw [dv_sub, DT.real_get, DT.real_get]
  have hwi : wIdx ctx x τ.w < shapeSize τ.w.shape := by
    rcases hwshape with hw | hw
    · simp [wIdx, hw, shapeSize]
    · have := hf.idx_lt
      simp [wIdx, hw, shapeSize]
      omega
  unfold marginStep at h
  simp only [hlen2, htok, Bool.false_eq_true, ↓reduceIte] at h
  by_cases hal : ctx.aligned = true
  · simp only [hal, ↓reduceIte] at h
    by_cases hg : (!(nTok ctx.box τ.pos == ctx.k || nTok ctx.box τ.pos == 1) ||
        !(shapeSize τ.w.shape == ctx.k || shapeSize τ.w.shape == 1)) = true
    · simp only [hg, ↓reduceIte] at h
      simp at h
    simp only [hg, Bool.false_eq_true, ↓reduceIte, pure, Option.some.injEq] at h
    subst h
    have hiRow' : iRow = inputIdx ctx x := by simp [hiRow, hal]
    have hrow : (if (nTok ctx.box τ.pos == 1) = true then 0 else iRow) =
        rowOf ctx.box x τ.pos := by
      by_cases h1 : nTok ctx.box τ.pos = 1
      · simp [h1, hf.one_row _ hpos h1]
      · simp [h1, hiRow', (hf.varying hal _ hpos h1).1]
    have hwi' : (if (shapeSize τ.w.shape == 1) = true then 0 else iRow) = wIdx ctx x τ.w := by
      rcases hwshape with hw | hw
      · simp [hw, wIdx, shapeSize]
      · by_cases hk1 : ctx.k = 1
        · have := hf.idx_lt
          simp [hw, wIdx, shapeSize, hk1]
          omega
        · simp [hw, wIdx, shapeSize, hk1, hiRow']
    refine ⟨by simp [hlen], hiR, ?_, fun o ho => ?_⟩
    · rw [getD_map_zip_range _ hlen hiR [] []]
      exact length_map_zip_range _ hrowlen
    · rw [getD_map_zip_range _ hlen hiR [] []]
      dsimp only
      rw [hrow, hwi', getD_map_zip_range _ hrowlen ho 0 0]
      dsimp only
      rw [dv_add, hshift]
      have hb := hbound o ho
      have ht := weighted_bound hΩ (wIdx ctx x τ.w)
        (mget τ.rows.lo (rowOf ctx.box x τ.pos * n + l) -
          mget τ.rows.lo (rowOf ctx.box x τ.pos * n + o)) τ.rows.e
      rw [hδ o, ← hω] at ht
      linarith
  · simp only [hal, Bool.false_eq_true, ↓reduceIte] at h
    have hn0 : (nTok ctx.box τ.pos == 0) = false := by simp; omega
    have hlo := hΩ.2.2.1
    have hhi := hΩ.2.2.2.1
    have hne : τ.w.lo.isEmpty = false := by
      rw [Bool.eq_false_iff]
      intro hc
      rw [Array.isEmpty_iff_size_eq_zero] at hc
      omega
    simp only [hn0, hne, Bool.false_eq_true, ↓reduceIte, pure, Option.some.injEq] at h
    subst h
    have hrowsN1 : rowsN = 1 := by simp [hrowsN, hal]
    have hiRow0 : iRow = 0 := by simp [hiRow, hal]
    subst hrowsN1 hiRow0
    refine ⟨by simp [hlen], hiR, ?_, fun o ho => ?_⟩
    · rw [list_getD_map _ (by omega) [] []]
      exact length_map_zip_range _ hrowlen
    · rw [list_getD_map _ (by omega) [] [], getD_map_zip_range _ hrowlen ho 0 0]
      dsimp only
      rw [dv_add, hshift]
      have hb := hbound o ho
      have ht := corner_bound hΩ (wi := wIdx ctx x τ.w) (by omega) (by omega)
        (fun r => mget τ.rows.lo (r * n + l) - mget τ.rows.lo (r * n + o)) hr0 τ.rows.e
      beta_reduce at ht
      rw [hδ o, ← hω] at ht
      linarith

/-- **All the terms**: the bounds of `x`'s row stay below the constant's
    margin plus the terms' real margin. -/
theorem marginFold_sound {ctx : TCtx} {x : Input} (hf : LeafFacts ctx x) {n l : ℕ} {e0 : ℤ}
    {rowsN iRow : ℕ} (hrowsN : rowsN = if ctx.aligned then ctx.k else 1)
    (hiRow : iRow = if ctx.aligned then inputIdx ctx x else 0)
    {ts : List Term} {ωs : List ℝ} (hts : List.Forall₂ (TermR ctx x [n]) ts ωs)
    (he0 : ∀ τ ∈ ts, e0 ≤ τ.w.e + τ.rows.e) {acc acc' : List (List ℤ)} {F : ℕ → ℝ}
    (hinv : MarginInv acc rowsN iRow n e0 F)
    (h : ts.foldlM (marginStep ctx n l e0 rowsN) acc = some acc') :
    MarginInv acc' rowsN iRow n e0 (fun o => F o +
      (termsVal ctx.box x n ts ωs l - termsVal ctx.box x n ts ωs o)) := by
  induction hts generalizing acc F with
  | nil =>
    simp only [List.foldlM_nil, pure, Option.some.injEq] at h
    subst h
    refine hinv.mono fun o _ => ?_
    simp [termsVal]
  | @cons τ ω ts ωs hτ hts ih =>
    rw [List.foldlM_cons] at h
    obtain ⟨acc1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    have hinv1 := marginStep_sound hf hrowsN hiRow hτ (he0 τ (by simp)) hinv h1
    refine (ih (fun τ' h' => he0 τ' (by simp [h'])) hinv1 h2).mono fun o _ => ?_
    rw [termsVal_cons, termsVal_cons]
    linarith

/-- A `Mix`: the constant's margin plus the lowest weighted differences of
    rows, input by input or for the whole box. -/
theorem mixMargin_sound {ctx : TCtx} {x : Input} (hf : LeafFacts ctx x) {m : Mix}
    {t : Tensor ℝ} (hm : MixR ctx x m t) {n l : ℕ} (hn : m.const.shape = [1, n]) (hl : l < n)
    {r : Option (ℤ × ℤ)} (h : mixMargin ctx m l = some r)
    (hr : ∀ m e, r = some (m, e) → 0 < m) :
    LabelWins t l := by
  obtain ⟨rest, hcs, hts, htsz, C, hC, ωs, hω, hget⟩ := hm
  have hrest : rest = [n] := by
    rw [hn] at hcs
    exact (List.cons.inj hcs).2.symm
  subst hrest
  have hS : shapeSize [n] = n := by simp [shapeSize]
  rw [hS] at htsz hget
  unfold mixMargin at h
  have hgetD : [1, n].getD 1 0 = n := rfl
  have hge : ¬ (l ≥ n) := by omega
  simp only [hn, hgetD, hge, ↓reduceIte] at h
  obtain ⟨acc, hfold, hfin⟩ := Option.bind_eq_some_iff.mp h
  simp only [pure, Option.some.injEq] at hfin
  set e0 := List.foldl min m.const.e (List.map (fun t ↦ t.w.e + t.rows.e) m.terms) with he0def
  have he0c : e0 ≤ m.const.e := foldl_min_le_int _ _ _ List.mem_cons_self
  have he0t : ∀ τ ∈ m.terms, e0 ≤ τ.w.e + τ.rows.e := fun τ hτ =>
    foldl_min_le_int _ _ _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hτ))
  set rowsN := if ctx.aligned = true then ctx.k else 1 with hrowsN
  set iRow := if ctx.aligned = true then inputIdx ctx x else 0 with hiRow
  have hiR : iRow < rowsN := by
    simp only [hrowsN, hiRow]
    split_ifs
    · exact hf.idx_lt
    · omega
  -- the constant's margins
  have hinv0 : MarginInv ((List.range rowsN).map fun _ => (List.range n).map fun o =>
      (mget m.const.lo l - mget m.const.hi o) * 2 ^ (m.const.e - e0).toNat) rowsN iRow n e0
      (fun o => C.get l - C.get o) := by
    refine ⟨by simp, hiR, ?_, fun o ho => ?_⟩
    · rw [list_getD_map _ (by simpa using hiR) 0 []]
      simp
    · rw [list_getD_map _ (by simpa using hiR) 0 [], list_getD_map _ (by simpa using ho) 0 0,
        range_getD ho]
      have := dv_shift (mget m.const.lo l - mget m.const.hi o) m.const.e (m.const.e - e0).toNat
      rw [Int.toNat_of_nonneg (by omega), sub_sub_cancel] at this
      rw [this, dv_sub]
      have h1 := (hC.2.2.2.2.2 l).1
      have h2 := (hC.2.2.2.2.2 o).2
      linarith
  obtain ⟨hlen, -, hrowlen, hbound⟩ := marginFold_sound hf hrowsN hiRow hω he0t hinv0 hfold
  refine margin_correct (all := List.flatMap (fun row ↦ List.map (fun x ↦ x.2)
      (List.filter (fun x ↦ x.1 != l) ((List.range n).zip row))) acc) (e := e0) hts htsz hl
    (fun o ho hne => ?_) (fun m' hm' => hr m' e0 (by rw [← hfin, hm']; rfl))
  refine ⟨(acc.getD iRow []).getD o 0, List.mem_flatMap.mpr ⟨acc.getD iRow [],
    getD_mem_of_lt (by omega) _, List.mem_map.mpr ⟨(o, (acc.getD iRow []).getD o 0),
      List.mem_filter.mpr ⟨mem_zip_range hrowlen ho 0, by simpa using hne⟩, rfl⟩⟩, ?_⟩
  have := hbound o ho
  rw [hget l hl, hget o ho]
  linarith

/-! ### The value of the output -/

/-- **The margin bound** is a lower bound on the real margin of the label
    over every other output: if it is positive, the label wins. -/
theorem lowestMargin_sound {g : Graph} {ctx : TCtx} {x : Input} (hf : LeafFacts ctx x)
    {v : TV} {t : Tensor ℝ} (hv : TRel g ctx x v t) {n l : ℕ} (hshape : v.shape ctx = [1, n])
    (hl : l < n) {r : Option (ℤ × ℤ)} (h : lowestMargin ctx v l = some r)
    (hr : ∀ m e, r = some (m, e) → 0 < m) : LabelWins t l := by
  -- the values of `Sep` kind leave the domain first
  have hleave : ∀ {v' : TV}, tLeave ctx v = some v' → t.shape = [1, n] →
      (∀ vs, v' = .var vs → varMargin vs l = some r) →
      (∀ d, v' = .dt d → dtMargin d l = r) → LabelWins t l := by
    intro v' hv' hts hvar hdt
    obtain ⟨hrel, hkind⟩ := tLeave_sim hf hv hv'
    rcases hkind with ⟨vs, rfl⟩ | ⟨d, rfl⟩
    · exact varMargin_sound hf hrel (Or.inr hts) hl (hvar vs rfl) hr
    · exact dtMargin_sound hrel (hrel.1.symm.trans hts) hl (hdt d rfl) hr
  unfold lowestMargin at h
  cases v with
  | box => simp at h
  | var vs => exact varMargin_sound hf hv (Or.inl hshape) hl h hr
  | dt d =>
    change some (dtMargin d l) = some r at h
    exact dtMargin_sound hv hshape hl (Option.some.inj h) hr
  | mix m => exact mixMargin_sound hf hv hshape hl h hr
  | sep s =>
    obtain ⟨v', hv', hm⟩ := Option.bind_eq_some_iff.mp h
    refine hleave hv' ((SepW.shape_eq hv).trans hshape) (fun vs hvs => ?_) (fun d hd => ?_)
    · subst hvs
      exact hm
    · subst hd
      simpa using hm
  | wsep w s =>
    obtain ⟨v', hv', hm⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨-, W, -, hW⟩ := id hv
    refine hleave hv' ((SepW.shape_eq hW).trans hshape) (fun vs hvs => ?_) (fun d hd => ?_)
    · subst hvs
      exact hm
    · subst hd
      simpa using hm
  | wsepv ws s =>
    obtain ⟨v', hv', hm⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨-, -, W, -, hW⟩ := id hv
    refine hleave hv' ((SepW.shape_eq hW).trans hshape) (fun vs hvs => ?_) (fun d hd => ?_)
    · subst hvs
      exact hm
    · subst hd
      simpa using hm

/-! ## The leaf -/

/-- **All the operations of a token_interval leaf** keep the relation. -/
theorem tevalOps_sim {g : Graph} {w : Weights ℚ} {dw : DWeights} (hdw : dweights w = some dw)
    {ctx : TCtx} {x : Input} (hf : LeafFacts ctx x) (hval : ctx.values = g.values)
    {deps : Array Bool} :
    ∀ {ops : List Op} {vals vals' : Array TV} {rvals : Array (Tensor ℝ)},
      ARel (TRel g ctx x) vals rvals → tevalOps g dw ctx deps ops vals = some vals' →
      ∃ rvals', semOps g (realWeights w) x ops rvals = some rvals' ∧
        ARel (TRel g ctx x) vals' rvals'
  | [], vals, vals', rvals, hr, h => by
    simp only [tevalOps, Option.some.injEq] at h
    subst h
    exact ⟨rvals, rfl, hr⟩
  | op :: ops, vals, vals', rvals, hr, h => by
    simp only [tevalOps] at h
    cases hv : tevalOp g dw ctx deps vals op with
    | none => simp [hv] at h
    | some v =>
      simp only [hv] at h
      obtain ⟨t, ht, hvt⟩ := tevalOp_sim hdw hf hval hr hv
      obtain ⟨rvals', h', hr'⟩ := tevalOps_sim hdw hf hval (hr.push hvt) h
      exact ⟨rvals', by simp only [semOps, ht]; exact h', hr'⟩

/-- The leaf's output on an input of its box: the label wins if the margin
    bound is positive. -/
theorem tokenLeafBound_sound {g : Graph} {w : Weights ℚ} {dw : DWeights}
    (hdw : dweights w = some dw) {box : Box} {l : ℕ} {r : Option (ℤ × ℤ)}
    (h : tokenLeafBound g dw box l = some r) (hr : ∀ m e, r = some (m, e) → 0 < m)
    (x : Input) (hx : inBox box x = true) :
    ∃ t, realOutput g w x = some t ∧ LabelWins t l := by
  have hf : LeafFacts (TCtx.ofBox box g.values) x := leafFacts hx
  unfold tokenLeafBound at h
  obtain ⟨vals, hvals, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨out, hout, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨rvals, hrv, hrel⟩ := tevalOps_sim hdw hf rfl (ARel.empty _) hvals
  obtain ⟨t, ht, hot⟩ := hrel.get? hout
  refine ⟨t, by simp only [realOutput, semGraph, hrv, ht], ?_⟩
  split at h
  · rename_i n hn
    split_ifs at h with hl
    exact lowestMargin_sound hf hot hn hl h hr
  · cases h

/-- **Every input of a box a token_interval leaf accepts is answered
    correctly.** -/
theorem generalTokenInterval_correct {g : Graph} {w : Weights ℚ} {dw : DWeights}
    (hdw : dweights w = some dw) {task : Task} {box : Box}
    (h : generalTokenInterval g dw task box = some true) (x : Input) (hx : inBox box x = true) :
    Correct g w task x := by
  unfold generalTokenInterval at h
  cases hl : task.constantLabel box with
  | none => simp [hl] at h
  | some l =>
    simp only [hl] at h
    obtain ⟨r, hb, hr⟩ := Option.map_eq_some_iff.mp h
    have hpos : ∀ m e, r = some (m, e) → 0 < m := by
      intro m e hme
      subst hme
      simpa using hr
    obtain ⟨t, ht, hs, hlt, hmax⟩ := tokenLeafBound_sound hdw hb hpos x hx
    have hlab : task.label x = l := task.constantLabel_spec box l x hl hx
    unfold Correct
    rw [hlab]
    exact ⟨t, ht, hs, hlt, hmax⟩

/-! ## Leaves and proofs -/

/-- Every input of a leaf the checker accepts is answered correctly. -/
theorem generalLeafOk_correct {g : Graph} {w : Weights ℚ} {dw : DWeights}
    (hdw : dweights w = some dw) {task : Task} {leaf : Leaf}
    (h : generalLeafOk g dw task leaf = .ok true) (x : Input) (hx : inBox leaf.box x = true) :
    Correct g w task x := by
  unfold generalLeafOk at h
  cases hr : leaf.rule with
  | skip => simp [hr] at h
  | single =>
    simp only [hr] at h
    cases hb : boxInput leaf.box with
    | none => simp [hb] at h
    | some x0 =>
      simp only [hb] at h
      cases hs : generalSingle g dw task x0 with
      | none => simp [hs] at h
      | some ok =>
        simp only [hs, Except.ok.injEq] at h
        subst h
        obtain ⟨_, huniq⟩ := boxInput_spec _ _ hb
        rw [huniq x hx]
        exact generalSingle_correct hdw hs
  | interval a =>
    cases a with
    | none =>
      simp only [hr] at h
      cases hi : generalInterval g dw task leaf.box with
      | none => simp [hi] at h
      | some ok =>
        simp only [hi, Except.ok.injEq] at h
        subst h
        exact generalInterval_correct hdw hi x hx
    | some name => simp [hr] at h
  | tokenInterval =>
    simp only [hr] at h
    cases hi : generalTokenInterval g dw task leaf.box with
    | none => simp [hi] at h
    | some ok =>
      simp only [hi, Except.ok.injEq] at h
      subst h
      exact generalTokenInterval_correct hdw hi x hx

/-! ## Counting -/

/-- A leaf the checker accepts. -/
def generalCertified (g : Graph) (dw : DWeights) (task : Task) (leaf : Leaf) : Bool :=
  match generalLeafOk g dw task leaf with
  | .ok true => true
  | _ => false

theorem generalCertified_ok {g : Graph} {dw : DWeights} {task : Task} {leaf : Leaf}
    (h : generalCertified g dw task leaf = true) : generalLeafOk g dw task leaf = .ok true := by
  unfold generalCertified at h
  split at h
  · assumption
  · cases h

theorem generalCheckLeaves_eq (g : Graph) (dw : DWeights) (task : Task) (leaves : List Leaf)
    (n : ℕ) (h : generalCheckLeaves g dw task leaves = .ok n) :
    n = (leaves.map fun l => if generalCertified g dw task l then boxSize l.box else 0).sum := by
  induction leaves generalizing n with
  | nil =>
    simp only [generalCheckLeaves] at h
    cases h
    simp
  | cons leaf rest ih =>
    simp only [generalCheckLeaves] at h
    cases hr : generalCheckLeaves g dw task rest with
    | error e => simp [hr] at h
    | ok m =>
      simp only [hr] at h
      cases hl : generalLeafOk g dw task leaf with
      | error e => simp [hl] at h
      | ok ok =>
        simp only [hl, Except.ok.injEq] at h
        subst h
        rw [List.map_cons, List.sum_cons, ← ih m hr]
        cases ok
        · simp [generalCertified, hl]
        · simp only [generalCertified, hl, ↓reduceIte]
          omega

/-- **Soundness on attention networks**: if the checker certifies `n`
    inputs, the network answers at least `n` inputs correctly. For every
    network, weights and proof file. -/
theorem checkGeneral_sound (g : Graph) (w : Weights ℚ) (task : Task) (proof : ProofFile) (n : ℕ)
    (h : checkProofGeneral g w task proof = .ok n) : n ≤ numCorrect g w task := by
  unfold checkProofGeneral at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  rename_i hzero
  have hpos : ∀ v ∈ task.space, 0 < v := by
    intro v hv
    have : ¬ (task.space.any (· == 0) = true) := by simpa using hzero
    simp only [List.any_eq_true, beq_iff_eq, not_exists, not_and] at this
    exact Nat.pos_of_ne_zero (this v hv)
  cases hdw : dweights w with
  | none => simp [hdw] at h
  | some dw =>
    simp only [hdw] at h
    split at h
    · cases h
    cases hw : walk proof.tree (rootBox task.space) with
    | error e => simp [hw] at h
    | ok leaves =>
      simp only [hw] at h
      rw [generalCheckLeaves_eq g dw task leaves n h]
      exact leaves_certified_le task (generalCertified g dw task) (Correct g w task)
        (fun l x hl hx => generalLeafOk_correct hdw (generalCertified_ok hl) x hx)
        proof.tree leaves hw hpos


end CompactCheck
