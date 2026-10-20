import CompactCheck.TokensMixSound

/-!
# Leaving the token domain keeps the relation

A `Sep`, `WSep` or `Mix` that meets an operation the token rules do not
cover becomes one interval tensor per input (`toVarSep`, `toVarMix`,
`toVarWSep`) in a leaf where at most one position varies, and an interval
tensor for the whole box otherwise (`collapseSep`, `collapseMix`,
`collapseWSep`, and `collapseVar` for values per input). A `Mix` whose terms
are exact single rows becomes its exact value (`concretize`). Each encloses
the real value.
-/

namespace CompactCheck

/-! ## Arrays of values per input -/

theorem array_mapM_range {β : Type} {f : ℕ → Option β} {k : ℕ} {xs : Array β}
    (h : (Array.range k).mapM f = some xs) :
    xs.size = k ∧ ∀ i < k, ∀ d : β, f i = some (xs.getD i d) := by
  rw [Array.mapM_eq_mapM_toList, Array.toList_range] at h
  cases hl : (List.range k).mapM f with
  | none => simp [hl] at h
  | some l =>
    simp only [hl, Option.map_eq_map, Option.map_some, Option.some.injEq] at h
    subst h
    have h2 := mapM_forall₂ hl
    refine ⟨by simp [← h2.length_eq], fun i hi d => ?_⟩
    have := forall₂_getD h2 (by simpa using hi) 0 d
    rw [list_getD_toArray]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hi),
      Option.getD_some, List.getElem_range] at this
    exact this

/-- The real value of a value kept per token, without weights. -/
noncomputable def sepVal (box : Box) (x : Input) (s : Sep) : Tensor ℝ :=
  ⟨1 :: box.length :: s.rest, (Array.range (box.length * shapeSize s.rest)).map fun j =>
    (s.rows.getD (j / shapeSize s.rest) emptyDT).real.get
      (rowOf box x (j / shapeSize s.rest) * shapeSize s.rest + j % shapeSize s.rest)⟩

/-- A `WSep` is its weights times the value of its rows. -/
theorem SepW.unweight {box : Box} {x : Input} {wt : ℕ → ℝ} {s : Sep} {t : Tensor ℝ}
    (h : SepW box x wt s t) : SepW box x (fun _ => 1) s (sepVal box x s) ∧
      ∀ p < box.length, ∀ q < shapeSize s.rest, t.get (p * shapeSize s.rest + q) =
        wt p * (sepVal box x s).get (p * shapeSize s.rest + q) := by
  obtain ⟨hpos, hrl, hts, htsz, hrok, hval⟩ := h
  have hget : ∀ p < box.length, ∀ q < shapeSize s.rest,
      (sepVal box x s).get (p * shapeSize s.rest + q) =
        (s.rows.getD p emptyDT).real.get (rowOf box x p * shapeSize s.rest + q) := by
    intro p hp q hq
    rw [sepVal, Tensor.get_mk_map_range _ _ _ (lt_mul_of_row hp hq), div_aux (by omega) hq,
      mod_aux hq]
  refine ⟨⟨hpos, hrl, rfl, by simp [sepVal], hrok, fun p hp q hq => ?_⟩, fun p hp q hq => ?_⟩
  · rw [hget p hp q hq, one_mul]
  · rw [hval p hp q hq, hget p hp q hq]

/-! ## Values per input of a `Sep` -/

theorem DT.at_encl {v : DT} {t : Tensor ℝ} (h : v.Encl t) (e : ℤ) : (v.at e).Encl t :=
  DT.shift_encl h _

@[simp] theorem DT.at_shape (v : DT) (e : ℤ) : (v.at e).shape = v.shape := DT.shift_shape _ _

theorem toVarSep_sim {ctx : TCtx} {x : Input} (hf : LeafFacts ctx x) (hal : ctx.aligned = true)
    {s : Sep} {t : Tensor ℝ} {xs : Array DT} (hs : SepW ctx.box x (fun _ => 1) s t)
    (h : toVarSep ctx s = some xs) : VarR ctx x xs t := by
  obtain ⟨hpos, hrl, hts, htsz, hrok, hval⟩ := hs
  unfold toVarSep at h
  by_cases hne : s.rows.isEmpty = true
  · simp [hne] at h
  simp only [hne, Bool.false_eq_true, ↓reduceIte, Option.bind_eq_bind] at h
  obtain ⟨hsz, hper⟩ := array_mapM_range h
  -- the row each input reads at each position
  let ji : ℕ → ℕ → ℕ := fun i p => if nTok ctx.box p = 1 then 0 else i
  -- the value of input `i`
  have hinput : ∀ i < ctx.k, ∃ U : Tensor ℝ, (xs.getD i emptyDT).Encl U ∧
      U.shape = 1 :: ctx.box.length :: s.rest ∧
      ∀ p < ctx.box.length, ∀ q < shapeSize s.rest, U.get (p * shapeSize s.rest + q) =
        (s.rows.getD p emptyDT).real.get (ji i p * shapeSize s.rest + q) := by
    intro i hi
    have h1 := hper i hi emptyDT
    obtain ⟨parts, hparts, h2⟩ := Option.bind_eq_some_iff.mp h1
    obtain ⟨st, hst, h3⟩ := Option.bind_eq_some_iff.mp h2
    have hf2 := mapM_forall₂ hparts
    have hlen : parts.length = ctx.box.length := by rw [← hf2.length_eq]; simp [hrl]
    -- each part: row `ji i p` of position `p`
    have hpart : ∀ p < ctx.box.length, ∃ T : Tensor ℝ, (parts.getD p emptyDT).Encl T ∧
        T.shape = s.rest ∧ ∀ q < shapeSize s.rest,
          T.get q = (s.rows.getD p emptyDT).real.get (ji i p * shapeSize s.rest + q) := by
      intro p hp
      have hp' : p < (s.rows.map (·.at s.minExp)).length := by simp [hrl, hp]
      have h4 := forall₂_getD hf2 hp' emptyDT emptyDT
      rw [list_getD_map _ (by rw [hrl]; exact hp) emptyDT] at h4
      have hR := (hrok p hp).encl
      have hRs := (hrok p hp).2.2.2
      simp only [DT.at_shape, hRs, List.headD_cons] at h4
      have hRs' : (s.rows.getD p emptyDT).real.shape = nTok ctx.box p :: s.rest := hRs
      by_cases h1 : nTok ctx.box p = 1
      · simp only [h1, beq_self_eq_true, ↓reduceIte] at h4
        obtain ⟨T, hT, hpT⟩ := dtIndex_sim (DT.at_encl hR _) h4
        obtain ⟨hTs, -, hTget⟩ := indexOp_one hRs' hT
        refine ⟨T, hpT, hTs, fun q hq => ?_⟩
        simp [hTget q hq, ji, h1]
      · have hk := (hf.varying hal p hp h1).2
        have h1' : (nTok ctx.box p == 1) = false := by simp [h1]
        have hk' : (nTok ctx.box p == ctx.k) = true := by simp [hk]
        simp only [h1', hk', Bool.false_eq_true, ↓reduceIte] at h4
        obtain ⟨T, hT, hpT⟩ := dtIndex_sim (DT.at_encl hR _) h4
        obtain ⟨hTs, -, hTget⟩ := indexOp_one hRs' hT
        refine ⟨T, hpT, hTs, fun q hq => ?_⟩
        simp [hTget q hq, ji, h1]
    have : Nonempty (Tensor ℝ) := ⟨⟨[], #[]⟩⟩
    choose! F hF using hpart
    have hrel : List.Forall₂ DT.Encl parts ((List.range parts.length).map F) :=
      forall₂_range_map parts F emptyDT (fun p hp => (hF p (by omega)).1)
    obtain ⟨ST, hST, hstST⟩ := djoin_sim (stackOp_mover 0) hrel hst
    have hshapes : ∀ T ∈ (List.range parts.length).map F, T.shape = s.rest := by
      intro T hT
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hT
      exact (hF p (by have := List.mem_range.mp hp; omega)).2.1
    have hne' : (List.range parts.length).map F ≠ [] := by
      intro h0
      have := congrArg List.length h0
      simp only [List.length_map, List.length_range, List.length_nil] at this
      omega
    obtain ⟨hSTs, -, hSTget⟩ := stackOp_first hshapes hne' hST
    obtain ⟨U, hU, hxU⟩ := dtUnsqueeze_sim hstST h3
    obtain ⟨hUs, hUd⟩ := unsqueezeOp_zero hU
    refine ⟨U, hxU, by rw [hUs, hSTs]; simp [hlen], fun p hp q hq => ?_⟩
    have : U.get (p * shapeSize s.rest + q) = ST.get (p * shapeSize s.rest + q) := by
      simp [Tensor.get, hUd]
    rw [this, hSTget p (by simp; omega) q hq, list_getD_map _ (by simp; omega) 0,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega), Option.getD_some,
      List.getElem_range]
    exact (hF p hp).2.2 q hq
  refine ⟨hsz, fun i hi => ?_, ?_⟩
  · obtain ⟨U, hU, -, -⟩ := hinput i hi
    exact ⟨U, hU⟩
  · obtain ⟨U, hU, hUs, hUget⟩ := hinput _ hf.idx_lt
    have hUsz : U.data.size = t.data.size := by rw [hU.2.1, ← hU.1, hUs, htsz, shapeSize_one_cons]
    refine hU.congr (by rw [hts, hUs]) hUsz.symm (fun j hj => ?_)
    rw [hU.2.1, ← hU.1, hUs, shapeSize_one_cons] at hj
    have hS : 0 < shapeSize s.rest := by
      rcases Nat.eq_zero_or_pos (shapeSize s.rest) with h0 | h0
      · rw [h0] at hj; omega
      · exact h0
    have hp : j / shapeSize s.rest < ctx.box.length :=
      Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hj)
    have hq : j % shapeSize s.rest < shapeSize s.rest := Nat.mod_lt _ hS
    have hj' : j = j / shapeSize s.rest * shapeSize s.rest + j % shapeSize s.rest :=
      (Nat.div_add_mod' j (shapeSize s.rest)).symm
    have hji : ji (inputIdx ctx x) (j / shapeSize s.rest) =
        rowOf ctx.box x (j / shapeSize s.rest) := by
      simp only [ji]
      split_ifs with h1
      · exact (hf.one_row _ hp h1).symm
      · exact (hf.varying hal _ hp h1).1.symm
    rw [hj', hval _ hp _ hq, hUget _ hp _ hq, one_mul, hji]

/-! ## One term added to a value -/

/-- A step of the folds over the terms: the value so far plus a scalar
    weight times a row. -/
theorem mixStep_sim {rest : List ℕ} {out res w row prod : DT} {OUT Wr ROW : Tensor ℝ}
    (hout : out.Encl OUT) (hOUTs : OUT.shape = 1 :: rest)
    (hrow : row.Encl ROW) (hROWs : ROW.shape = 1 :: rest)
    (hw : w.Encl Wr) (hWs : Wr.shape = [])
    (hprod : dbinary .mul w row = some prod) (hres : dbinary .add out prod = some res) :
    ∃ RES, res.Encl RES ∧ RES.shape = 1 :: rest ∧
      ∀ q < shapeSize rest, RES.get q = OUT.get q + Wr.get 0 * ROW.get q := by
  obtain ⟨PROD, hPROD, hprodP⟩ := dbinary_sim hw hrow hprod
  have hbs1 : broadcastShape Wr.shape ROW.shape = some (1 :: rest) := by
    rw [hWs, hROWs, broadcastShape_comm, broadcastShape_nil_right]
  obtain ⟨hPs, -, hPget⟩ := broadcastOp_full_right hROWs hPROD hbs1
  obtain ⟨RES, hRES, hresR⟩ := dbinary_sim hout hprodP hres
  have hbs2 : broadcastShape OUT.shape PROD.shape = some (1 :: rest) := by
    rw [hOUTs, hPs, broadcastShape_self]
  obtain ⟨hRs, -, hRget⟩ := broadcastOp_full_left hOUTs hRES hbs2
  refine ⟨RES, hresR, hRs, fun q hq => ?_⟩
  have hq' : q < shapeSize (1 :: rest) := by rw [shapeSize_cons]; omega
  rw [hRget q hq', entry_broadcast_self hPs hq', hPget q hq']
  simp [BinOp.apply, broadcastIndex, Tensor.entry, ravel, strides, hWs]

theorem pick_spec {n i k r : ℕ} (h : pick n i k = some r) :
    r = (if n = 1 then 0 else i) ∧ (n = 1 ∨ n = k) := by
  unfold pick at h
  split_ifs at h with h1 h2
  · simp only [beq_iff_eq] at h1
    simp only [Option.some.injEq] at h
    exact ⟨by simp [h1, h], Or.inl h1⟩
  · simp only [beq_iff_eq] at h1 h2
    simp only [Option.some.injEq] at h
    exact ⟨by simp [h1, h], Or.inr h2⟩

/-- The row of input `i` (for the input `x`: `x`'s row). -/
theorem pick_row {ctx : TCtx} {x : Input} (hf : LeafFacts ctx x) (hal : ctx.aligned = true)
    {p r : ℕ} (hp : p < ctx.box.length)
    (h : pick (nTok ctx.box p) (inputIdx ctx x) ctx.k = some r) :
    r = rowOf ctx.box x p := by
  obtain ⟨hr, -⟩ := pick_spec h
  subst hr
  split_ifs with h1
  · exact (hf.one_row p hp h1).symm
  · exact (hf.varying hal p hp h1).1.symm

/-- A term's weight for input `i`. -/
theorem varWeight_sim {ctx : TCtx} {x : Input} (hf : LeafFacts ctx x) {rest : List ℕ} {τ : Term}
    {ω : ℝ} (hτ : TermR ctx x rest τ ω) {i : ℕ} {w : DT} (h : varWeight ctx i τ.w = some w) :
    ∃ Wr, w.Encl Wr ∧ Wr.shape = [] ∧ (i = inputIdx ctx x → Wr.get 0 = ω) := by
  obtain ⟨-, -, hsh, Ω, hΩ, hω⟩ := hτ
  unfold varWeight at h
  rcases hsh with h0 | h0
  · simp only [h0, Option.some.injEq] at h
    subst h
    refine ⟨Ω, hΩ, by rw [hΩ.1, h0], fun _ => ?_⟩
    rw [hω]
    simp [wIdx, h0]
  · simp only [h0] at h
    obtain ⟨j, hj, h2⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨Wr, hWr, hwWr⟩ := dtIndex_sim hΩ h2
    have hΩs : Ω.shape = ctx.k :: [] := by rw [hΩ.1, h0]
    obtain ⟨hWrs, -, hWrget⟩ := indexOp_one hΩs hWr
    refine ⟨Wr, hwWr, hWrs, fun hix => ?_⟩
    rw [hWrget 0 (by simp [shapeSize]), hω]
    have hne : τ.w.shape ≠ [] := by rw [h0]; simp
    simp only [wIdx, hne, ↓reduceIte, shapeSize_nil, Nat.mul_one, Nat.add_zero]
    obtain ⟨hjv, -⟩ := pick_spec hj
    have hjx : j = inputIdx ctx x := by
      rw [hjv]
      split_ifs with hk
      · have := hf.idx_lt
        omega
      · exact hix
    rw [hjx]

/-! ## Values per input of a `Mix` -/

theorem toVarMix_fold {ctx : TCtx} {x : Input} (hf : LeafFacts ctx x) (hal : ctx.aligned = true)
    {rest : List ℕ} {i : ℕ} :
    ∀ {terms : List Term} {ωs : List ℝ} {out res : DT} {OUT : Tensor ℝ},
      List.Forall₂ (TermR ctx x rest) terms ωs → out.Encl OUT → OUT.shape = 1 :: rest →
      terms.foldlM (varMixStep ctx i) out = some res →
      ∃ RES, res.Encl RES ∧ RES.shape = 1 :: rest ∧ (i = inputIdx ctx x →
        ∀ q < shapeSize rest,
          RES.get q = OUT.get q + termsVal ctx.box x (shapeSize rest) terms ωs q)
  | [], [], out, res, OUT, _, hout, hOUTs, h => by
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact ⟨OUT, hout, hOUTs, fun _ q _ => by simp [termsVal]⟩
  | τ :: terms, ω :: ωs, out, res, OUT, hrel, hout, hOUTs, h => by
    cases hrel with
    | cons hτ hrel' =>
      rw [List.foldlM_cons] at h
      obtain ⟨out', hstep, hrest⟩ := Option.bind_eq_some_iff.mp h
      unfold varMixStep at hstep
      obtain ⟨r, hr, h1⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨row, hrow, h2⟩ := Option.bind_eq_some_iff.mp h1
      obtain ⟨w, hw, h3⟩ := Option.bind_eq_some_iff.mp h2
      obtain ⟨prod, hprod, hres⟩ := Option.bind_eq_some_iff.mp h3
      have hτ' := hτ
      obtain ⟨hpos, hrok, -, -⟩ := hτ
      obtain ⟨ROW, hROW, hrowR⟩ := dtIndex_sim hrok.encl hrow
      obtain ⟨hROWs, -, hROWget⟩ := indexOp_range1 hrok.2.2.2 hROW
      obtain ⟨Wr, hwWr, hWrs, hWr⟩ := varWeight_sim hf hτ' hw
      obtain ⟨OUT', hout', hOUT's, hOUT'get⟩ :=
        mixStep_sim hout hOUTs hrowR hROWs hwWr hWrs hprod hres
      obtain ⟨RES, hRES, hRESs, hRESget⟩ := toVarMix_fold hf hal hrel' hout' hOUT's hrest
      refine ⟨RES, hRES, hRESs, fun hix q hq => ?_⟩
      rw [hRESget hix q hq, hOUT'get q hq, termsVal_cons, hROWget q hq, hWr hix]
      have hrs : τ.rows.shape.headD 0 = nTok ctx.box τ.pos := by rw [hrok.2.2.2]; rfl
      rw [hrs, hix] at hr
      rw [pick_row hf hal hpos hr]
      ring
  | [], _ :: _, _, _, _, hrel, _, _, _ => by cases hrel
  | _ :: _, [], _, _, _, hrel, _, _, _ => by cases hrel

theorem toVarMix_sim {ctx : TCtx} {x : Input} (hf : LeafFacts ctx x) (hal : ctx.aligned = true)
    {m : Mix} {t : Tensor ℝ} {xs : Array DT} (hm : MixR ctx x m t) (h : toVarMix ctx m = some xs) :
    VarR ctx x xs t := by
  obtain ⟨rest, hcrest, hts, htsz, C, hC, ωs, hterms, hval⟩ := hm
  unfold toVarMix at h
  obtain ⟨hsz, hper⟩ := array_mapM_range h
  have hCs : C.shape = 1 :: rest := by rw [hC.1, hcrest]
  refine ⟨hsz, fun i hi => ?_, ?_⟩
  · obtain ⟨RES, hRES, -, -⟩ := toVarMix_fold hf hal hterms hC hCs (hper i hi emptyDT)
    exact ⟨RES, hRES⟩
  · obtain ⟨RES, hRES, hRESs, hRESget⟩ :=
      toVarMix_fold hf hal hterms hC hCs (hper _ hf.idx_lt emptyDT)
    have hRESsz : RES.data.size = shapeSize rest := by
      rw [hRES.2.1, ← hRES.1, hRESs, shapeSize_cons, Nat.one_mul]
    refine hRES.congr (by rw [hts, hRESs]) (by rw [htsz, hRESsz]) (fun j hj => ?_)
    rw [hRESsz] at hj
    rw [hval j hj, hRESget rfl j hj]

/-! ## The exact value of a `Mix` -/

theorem concrete_fold {ctx : TCtx} {x : Input} (hf : LeafFacts ctx x) {rest : List ℕ} :
    ∀ {terms : List Term} {ωs : List ℝ} {out res : DT} {OUT : Tensor ℝ},
      List.Forall₂ (TermR ctx x rest) terms ωs →
      (∀ τ ∈ terms, τ.rows.shape.headD 0 = 1 ∧ τ.w.shape = []) →
      out.Encl OUT → OUT.shape = 1 :: rest → terms.foldlM concreteStep out = some res →
      ∃ RES, res.Encl RES ∧ RES.shape = 1 :: rest ∧
        ∀ q < shapeSize rest, RES.get q = OUT.get q + termsVal ctx.box x (shapeSize rest) terms ωs q
  | [], [], out, res, OUT, _, _, hout, hOUTs, h => by
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact ⟨OUT, hout, hOUTs, fun q _ => by simp [termsVal]⟩
  | τ :: terms, ω :: ωs, out, res, OUT, hrel, hone, hout, hOUTs, h => by
    cases hrel with
    | cons hτ hrel' =>
      rw [List.foldlM_cons] at h
      obtain ⟨out', hstep, hrest⟩ := Option.bind_eq_some_iff.mp h
      unfold concreteStep at hstep
      obtain ⟨row, hrow, h1⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨prod, hprod, hres⟩ := Option.bind_eq_some_iff.mp h1
      obtain ⟨hpos, hrok, -, Ω, hΩ, hω⟩ := hτ
      obtain ⟨h1r, hws⟩ := hone τ List.mem_cons_self
      obtain ⟨ROW, hROW, hrowR⟩ := dtIndex_sim hrok.encl hrow
      obtain ⟨hROWs, -, hROWget⟩ := indexOp_range1 (r := 0) hrok.2.2.2 hROW
      obtain ⟨OUT', hout', hOUT's, hOUT'get⟩ :=
        mixStep_sim hout hOUTs hrowR hROWs hΩ (by rw [hΩ.1, hws]) hprod hres
      obtain ⟨RES, hRES, hRESs, hRESget⟩ := concrete_fold hf hrel'
        (fun τ' h' => hone τ' (List.mem_cons_of_mem _ h')) hout' hOUT's hrest
      refine ⟨RES, hRES, hRESs, fun q hq => ?_⟩
      rw [hRESget q hq, hOUT'get q hq, termsVal_cons, hROWget q hq, hω]
      have hn : nTok ctx.box τ.pos = 1 := by rw [hrok.2.2.2] at h1r; exact h1r
      have hrow0 := hf.one_row _ hpos hn
      simp only [wIdx, hws, ↓reduceIte, hrow0, Nat.zero_mul]
      ring
  | [], _ :: _, _, _, _, hrel, _, _, _, _ => by cases hrel
  | _ :: _, [], _, _, _, hrel, _, _, _, _ => by cases hrel

theorem concretize_sim {ctx : TCtx} {x : Input} (hf : LeafFacts ctx x) {m : Mix} {t : Tensor ℝ}
    {d : DT} (hm : MixR ctx x m t) (h : concretize m = some (some d)) : d.Encl t := by
  obtain ⟨rest, hcrest, hts, htsz, C, hC, ωs, hterms, hval⟩ := hm
  unfold concretize at h
  split_ifs at h with hcond
  · cases h
  obtain ⟨d', hd', h2⟩ := Option.map_eq_some_iff.mp h
  simp only [Option.some.injEq] at h2
  subst h2
  simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true, List.all_eq_true,
    beq_iff_eq] at hcond
  have hCs : C.shape = 1 :: rest := by rw [hC.1, hcrest]
  obtain ⟨RES, hRES, hRESs, hRESget⟩ := concrete_fold hf hterms
    (fun τ hτ => ⟨(hcond.2 τ hτ).1.1, (hcond.2 τ hτ).2⟩) hC hCs hd'
  have hRESsz : RES.data.size = shapeSize rest := by
    rw [hRES.2.1, ← hRES.1, hRESs, shapeSize_cons, Nat.one_mul]
  refine hRES.congr (by rw [hts, hRESs]) (by rw [htsz, hRESsz]) (fun j hj => ?_)
  rw [hRESsz] at hj
  rw [hval j hj, hRESget j hj]

/-! ## Boxes of rows -/

theorem foldl_min_row (f : ℕ → ℤ) (n j : ℕ) (hj : j ≤ n) :
    (List.range n).foldl (fun m i => min m (f (i + 1))) (f 0) ≤ f j := by
  rw [← List.foldl_map (f := fun i => f (i + 1)) (g := min)]
  apply foldl_min_le_int
  rcases Nat.eq_zero_or_pos j with h0 | h0
  · subst h0
    exact List.mem_cons_self
  · refine List.mem_cons_of_mem _ (List.mem_map.mpr ⟨j - 1, List.mem_range.mpr (by omega), ?_⟩)
    congr 1
    omega

theorem le_foldl_max_row (f : ℕ → ℤ) (n j : ℕ) (hj : j ≤ n) :
    f j ≤ (List.range n).foldl (fun m i => max m (f (i + 1))) (f 0) := by
  rw [← List.foldl_map (f := fun i => f (i + 1)) (g := max)]
  apply le_foldl_max_int
  rcases Nat.eq_zero_or_pos j with h0 | h0
  · subst h0
    exact List.mem_cons_self
  · refine List.mem_cons_of_mem _ (List.mem_map.mpr ⟨j - 1, List.mem_range.mpr (by omega), ?_⟩)
    congr 1
    omega

/-- The box of the rows encloses each row. -/
theorem dtMinMax_sim {r b : DT} {R : Tensor ℝ} {n : ℕ} {rest : List ℕ} (hr : r.Encl R)
    (hRs : R.shape = n :: rest) {j : ℕ} (hj : j < n) (h : dtMinMax r = some b) :
    ∃ ROW : Tensor ℝ, b.Encl ROW ∧ ROW.shape = 1 :: rest ∧
      ∀ q < shapeSize rest, ROW.get q = R.get (j * shapeSize rest + q) := by
  have hrs : r.shape = n :: rest := by rw [← hr.1, hRs]
  unfold dtMinMax at h
  simp only [hr.ok, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  rw [hrs] at h
  rcases n with _ | n
  · omega
  rcases n with _ | n
  · -- one row: the rows themselves
    simp only [Option.some.injEq] at h
    subst h
    have hj0 : j = 0 := by omega
    subst hj0
    exact ⟨R, hr, hRs, fun q _ => by simp⟩
  · -- the smallest and largest entry of each column
    simp only [Option.some.injEq] at h
    subst h
    have hS : ∀ q, q < shapeSize rest → j * shapeSize rest + q < (n + 1 + 1) * shapeSize rest :=
      fun q hq => lt_mul_of_row hj hq
    refine ⟨⟨1 :: rest, (Array.range (shapeSize rest)).map fun q => R.get (j * shapeSize rest + q)⟩,
      DT.Encl.mk rfl (by simp [shapeSize_cons]) (by simp [shapeSize_cons])
        (by simp [shapeSize_cons]) (by simp) ?_, rfl, fun q hq => ?_⟩
    · intro q hq
      rw [shapeSize_cons, Nat.one_mul] at hq
      simp only
      rw [mget_map_range _ _ hq, mget_map_range _ _ hq, Tensor.get_mk_map_range _ _ _ hq]
      have hb := hr.2.2.2.2.2 (j * shapeSize rest + q)
      constructor
      · refine le_trans (dv_le_dv _ ?_) hb.1
        have := foldl_min_row (fun i => mget r.lo (i * shapeSize rest + q)) (n + 1) j (by omega)
        simpa using this
      · refine le_trans hb.2 (dv_le_dv _ ?_)
        have := le_foldl_max_row (fun i => mget r.hi (i * shapeSize rest + q)) (n + 1) j (by omega)
        simpa using this
    · rw [Tensor.get_mk_map_range _ _ _ hq]

theorem array_foldl_min_le {a : Array ℤ} {i : ℕ} (hi : i < a.size) :
    a.foldl min (a.getD 0 0) ≤ a[i] := by
  rw [← Array.foldl_toList]
  apply foldl_min_le_int
  exact List.mem_cons_of_mem _ (Array.mem_toList_iff.mpr (Array.getElem_mem hi))

theorem array_le_foldl_max {a : Array ℤ} {i : ℕ} (hi : i < a.size) :
    a[i] ≤ a.foldl max (a.getD 0 0) := by
  rw [← Array.foldl_toList]
  apply le_foldl_max_int
  exact List.mem_cons_of_mem _ (Array.mem_toList_iff.mpr (Array.getElem_mem hi))

/-- A term's weight as one interval encloses its real weight. -/
theorem boxWeight_sim {ctx : TCtx} {x : Input} (hf : LeafFacts ctx x) {rest : List ℕ} {τ : Term}
    {ω : ℝ} (hτ : TermR ctx x rest τ ω) {w : DT} (h : boxWeight τ.w = some w) :
    w.Encl ⟨[], #[ω]⟩ := by
  obtain ⟨-, -, hsh, Ω, hΩ, hω⟩ := hτ
  unfold boxWeight at h
  by_cases h0 : τ.w.shape = []
  · simp only [h0, beq_self_eq_true, ↓reduceIte, Option.some.injEq] at h
    subst h
    refine hΩ.congr (by rw [hΩ.1, h0]) (by rw [hΩ.2.1, h0]; rfl) (fun j hj => ?_)
    rw [hΩ.2.1, h0] at hj
    have : j = 0 := by simpa [shapeSize] using hj
    subst this
    rw [hω]
    simp [wIdx, h0, Tensor.get]
  · have h0' : (τ.w.shape == []) = false := by simp [h0]
    simp only [h0', Bool.false_eq_true, ↓reduceIte] at h
    split_ifs at h with hok
    simp only [Option.some.injEq] at h
    subst h
    have hk : τ.w.shape = [ctx.k] := hsh.resolve_left h0
    have hidx := hf.idx_lt
    have hsz : τ.w.lo.size = ctx.k := by rw [hΩ.2.2.1, hk]; simp [shapeSize]
    have hszh : τ.w.hi.size = ctx.k := by rw [hΩ.2.2.2.1, hk]; simp [shapeSize]
    have hw : wIdx ctx x τ.w = inputIdx ctx x := by simp [wIdx, h0]
    have hb := hΩ.2.2.2.2.2 (inputIdx ctx x)
    rw [← hw, ← hω] at hb
    refine DT.Encl.mk rfl rfl rfl rfl (by simp) (fun j hj => ?_)
    have : j = 0 := by simpa [shapeSize] using hj
    subst this
    simp only [mget, Array.getD_eq_getD_getElem?, Array.getElem?_singleton, Tensor.get]
    simp only [↓reduceIte, Option.getD_some]
    rw [hw] at hb
    have h1 : mget τ.w.lo (inputIdx ctx x) = τ.w.lo[inputIdx ctx x] := by
      simp [mget, Array.getD_eq_getD_getElem?, hsz, hidx]
    have h2 : mget τ.w.hi (inputIdx ctx x) = τ.w.hi[inputIdx ctx x] := by
      simp [mget, Array.getD_eq_getD_getElem?, hszh, hidx]
    rw [h1] at hb
    rw [h2] at hb
    exact ⟨le_trans (dv_le_dv _ (by
        have := array_foldl_min_le (a := τ.w.lo) (i := inputIdx ctx x) (by omega)
        simpa [Array.getD_eq_getD_getElem?] using this)) hb.1,
      le_trans hb.2 (dv_le_dv _ (by
        have := array_le_foldl_max (a := τ.w.hi) (i := inputIdx ctx x) (by omega)
        simpa [Array.getD_eq_getD_getElem?] using this))⟩

theorem box_fold {ctx : TCtx} {x : Input} (hf : LeafFacts ctx x) {rest : List ℕ} :
    ∀ {terms : List Term} {ωs : List ℝ} {out res : DT} {OUT : Tensor ℝ},
      List.Forall₂ (TermR ctx x rest) terms ωs →
      out.Encl OUT → OUT.shape = 1 :: rest → terms.foldlM boxMixStep out = some res →
      ∃ RES, res.Encl RES ∧ RES.shape = 1 :: rest ∧
        ∀ q < shapeSize rest, RES.get q = OUT.get q + termsVal ctx.box x (shapeSize rest) terms ωs q
  | [], [], out, res, OUT, _, hout, hOUTs, h => by
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact ⟨OUT, hout, hOUTs, fun q _ => by simp [termsVal]⟩
  | τ :: terms, ω :: ωs, out, res, OUT, hrel, hout, hOUTs, h => by
    cases hrel with
    | cons hτ hrel' =>
      rw [List.foldlM_cons] at h
      obtain ⟨out', hstep, hrest⟩ := Option.bind_eq_some_iff.mp h
      unfold boxMixStep at hstep
      obtain ⟨box, hbox, h1⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨w, hw, h2⟩ := Option.bind_eq_some_iff.mp h1
      obtain ⟨prod, hprod, hres⟩ := Option.bind_eq_some_iff.mp h2
      have hwω := boxWeight_sim hf hτ hw
      obtain ⟨hpos, hrok, -, -⟩ := hτ
      obtain ⟨ROW, hboxR, hROWs, hROWget⟩ :=
        dtMinMax_sim hrok.encl hrok.2.2.2 (hf.row_lt _ hpos) hbox
      obtain ⟨OUT', hout', hOUT's, hOUT'get⟩ :=
        mixStep_sim hout hOUTs hboxR hROWs hwω rfl hprod hres
      obtain ⟨RES, hRES, hRESs, hRESget⟩ := box_fold hf hrel' hout' hOUT's hrest
      refine ⟨RES, hRES, hRESs, fun q hq => ?_⟩
      rw [hRESget q hq, hOUT'get q hq, termsVal_cons, hROWget q hq]
      simp only [Tensor.get, Array.getD_eq_getD_getElem?]
      simp
      ring
  | [], _ :: _, _, _, _, hrel, _, _, _ => by cases hrel
  | _ :: _, [], _, _, _, hrel, _, _, _ => by cases hrel

theorem collapseMix_sim {ctx : TCtx} {x : Input} (hf : LeafFacts ctx x) {m : Mix} {t : Tensor ℝ}
    {d : DT} (hm : MixR ctx x m t) (h : collapseMix m = some d) : d.Encl t := by
  unfold collapseMix at h
  cases hc : concretize m with
  | none => simp [hc] at h
  | some o =>
    cases o with
    | some d' =>
      simp only [hc, Option.some.injEq] at h
      subst h
      exact concretize_sim hf hm hc
    | none =>
      simp only [hc] at h
      obtain ⟨rest, hcrest, hts, htsz, C, hC, ωs, hterms, hval⟩ := hm
      obtain ⟨RES, hRES, hRESs, hRESget⟩ := box_fold hf hterms hC (by rw [hC.1, hcrest]) h
      have hRESsz : RES.data.size = shapeSize rest := by
        rw [hRES.2.1, ← hRES.1, hRESs, shapeSize_cons, Nat.one_mul]
      refine hRES.congr (by rw [hts, hRESs]) (by rw [htsz, hRESsz]) (fun j hj => ?_)
      rw [hRESsz] at hj
      rw [hval j hj, hRESget j hj]

/-! ## Weights times rows -/

theorem get_eq_of_rows {A B : Tensor ℝ} {P S : ℕ}
    (h : ∀ p < P, ∀ q < S, A.get (p * S + q) = B.get (p * S + q)) :
    ∀ j < P * S, A.get j = B.get j := by
  intro j hj
  have hS : 0 < S := by
    rcases Nat.eq_zero_or_pos S with h0 | h0
    · rw [h0, Nat.mul_zero] at hj; omega
    · exact h0
  have hp : j / S < P := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hj)
  rw [← Nat.div_add_mod' j S]
  exact h _ hp _ (Nat.mod_lt _ hS)

/-- One weight per position times a value of the shape `[1, P] ++ rest`. -/
theorem weight_mul_sep {W T Z : Tensor ℝ} {P : ℕ} {rest : List ℕ}
    (hW : W.shape = weightShape P rest) (hT : T.shape = 1 :: P :: rest)
    (h : broadcastOp BinOp.mul.apply W T = some Z) :
    Z.shape = 1 :: P :: rest ∧ Z.data.size = P * shapeSize rest ∧
      ∀ p < P, ∀ q < shapeSize rest,
        Z.get (p * shapeSize rest + q) = W.get p * T.get (p * shapeSize rest + q) := by
  have hfit : (List.zipWith (fun d f => d == f || d == 1) (weightShape P rest)
      ((1 :: P :: rest).drop ((1 :: P :: rest).length - (weightShape P rest).length))).all id
      = true := by
    simp only [weightShape, List.length_cons, List.length_replicate, Nat.sub_self, List.drop_zero,
      List.zipWith_cons_cons, beq_self_eq_true, Bool.true_or, List.all_cons, id, Bool.true_and]
    apply List.all_eq_true.mpr
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    simp
  have hbs : broadcastShape W.shape T.shape = some (1 :: P :: rest) := by
    rw [hW, hT]
    exact (broadcastShape_of_fits (by simp [weightShape]) hfit).2
  obtain ⟨hZs, hZsz, hZget⟩ := broadcastOp_full_right hT h hbs
  refine ⟨hZs, by rw [hZsz, shapeSize_one_cons], fun p hp q hq => ?_⟩
  rw [hZget _ (by rw [shapeSize_one_cons]; exact lt_mul_of_row hp hq),
    entry_broadcast_weight hW hp hq]
  rfl

/-- An enclosure of the weights times the value of the rows encloses a
    `WSep`'s value. -/
theorem encl_wsep {box : Box} {x : Input} {s : Sep} {t Z : Tensor ℝ} {W : Tensor ℝ} {v : DT}
    (hsep : SepW box x (fun p => W.get p) s t) (hW : W.shape = weightShape box.length s.rest)
    (hZ : broadcastOp BinOp.mul.apply W (sepVal box x s) = some Z) (hvZ : v.Encl Z) : v.Encl t := by
  obtain ⟨hT, hTt⟩ := hsep.unweight
  obtain ⟨hZs, hZsz, hZget⟩ := weight_mul_sep hW hT.2.2.1 hZ
  refine hvZ.congr (by rw [hsep.2.2.1, hZs]) (by rw [hsep.2.2.2.1, hZsz]) ?_
  rw [hZsz]
  exact get_eq_of_rows (fun p hp q hq => by rw [hTt p hp q hq, hZget p hp q hq])

theorem toVarWSep_inl_sim {ctx : TCtx} {x : Input} (hf : LeafFacts ctx x)
    (hal : ctx.aligned = true) {w : DT} {s : Sep} {t : Tensor ℝ} {xs : Array DT}
    (hw : WSepR ctx x w s t) (h : toVarWSep ctx (.inl w) s = some xs) : VarR ctx x xs t := by
  obtain ⟨hws, W, hwW, hsep⟩ := hw
  obtain ⟨hT, -⟩ := hsep.unweight
  unfold toVarWSep at h
  obtain ⟨ys, hys, h2⟩ := Option.bind_eq_some_iff.mp h
  have hv := toVarSep_sim hf hal hT hys
  obtain ⟨hsz, hper⟩ := array_mapM_range h2
  rw [hv.1] at hsz hper
  have hWs : W.shape = weightShape ctx.box.length s.rest := by rw [hwW.1, hws]
  refine ⟨hsz, fun i hi => ?_, ?_⟩
  · obtain ⟨U, hU⟩ := hv.2.1 i hi
    have h3 := hper i hi emptyDT
    simp only [Option.bind_eq_bind, Option.bind_some] at h3
    obtain ⟨Z, -, hZ⟩ := dbinary_sim hwW hU h3
    exact ⟨Z, hZ⟩
  · have h3 := hper _ hf.idx_lt emptyDT
    simp only [Option.bind_eq_bind, Option.bind_some] at h3
    obtain ⟨Z, hZ, hxZ⟩ := dbinary_sim hwW hv.2.2 h3
    exact encl_wsep hsep hWs hZ hxZ

theorem toVarWSep_inr_sim {ctx : TCtx} {x : Input} (hf : LeafFacts ctx x)
    (hal : ctx.aligned = true) {ws : Array DT} {s : Sep} {t : Tensor ℝ} {xs : Array DT}
    (hw : WSepVR ctx x ws s t) (h : toVarWSep ctx (.inr ws) s = some xs) : VarR ctx x xs t := by
  obtain ⟨hwsz, hall, W, hwW, hsep⟩ := hw
  obtain ⟨hT, -⟩ := hsep.unweight
  unfold toVarWSep at h
  obtain ⟨ys, hys, h2⟩ := Option.bind_eq_some_iff.mp h
  have hv := toVarSep_sim hf hal hT hys
  obtain ⟨hsz, hper⟩ := array_mapM_range h2
  rw [hv.1] at hsz hper
  have hwi : ∀ i < ctx.k, ws[i]? = some (ws.getD i emptyDT) := by
    intro i hi
    simp [Array.getD_eq_getD_getElem?, hwsz, hi]
  refine ⟨hsz, fun i hi => ?_, ?_⟩
  · obtain ⟨U, hU⟩ := hv.2.1 i hi
    have h3 := hper i hi emptyDT
    simp only [Option.bind_eq_bind, hwi i hi, Option.bind_some] at h3
    obtain ⟨W', hW'⟩ := (hall i hi).2
    obtain ⟨Z, -, hZ⟩ := dbinary_sim hW' hU h3
    exact ⟨Z, hZ⟩
  · have h3 := hper _ hf.idx_lt emptyDT
    simp only [Option.bind_eq_bind, hwi _ hf.idx_lt, Option.bind_some] at h3
    obtain ⟨Z, hZ, hxZ⟩ := dbinary_sim hwW hv.2.2 h3
    exact encl_wsep hsep (by rw [hwW.1, (hall _ hf.idx_lt).1]) hZ hxZ

/-! ## Boxes over the inputs -/

theorem foldl_min_le_mem {β : Type} (f : β → ℤ) (l : List β) (a : ℤ) {b : β} (hb : b ∈ l) :
    l.foldl (fun m v => min m (f v)) a ≤ f b := by
  rw [← List.foldl_map (f := f) (g := min)]
  exact foldl_min_le_int _ _ _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hb))

theorem le_foldl_max_mem {β : Type} (f : β → ℤ) (l : List β) (a : ℤ) {b : β} (hb : b ∈ l) :
    f b ≤ l.foldl (fun m v => max m (f v)) a := by
  rw [← List.foldl_map (f := f) (g := max)]
  exact le_foldl_max_int _ _ _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hb))

theorem DT.at_e {v : DT} {e : ℤ} (h : e ≤ v.e) : (v.at e).e = e := by
  unfold DT.at
  rw [DT.shift_e]
  omega

theorem collapseVar_sim {ctx : TCtx} {x : Input} (hf : LeafFacts ctx x) {vs : Array DT}
    {t : Tensor ℝ} {d : DT} (hv : VarR ctx x vs t) (h : collapseVar vs = some d) : d.Encl t := by
  obtain ⟨hsz, -, hx⟩ := hv
  have hidx := hf.idx_lt
  unfold collapseVar at h
  by_cases h1 : vs.size = 1
  · simp only [h1, beq_self_eq_true, ↓reduceIte] at h
    have hi0 : inputIdx ctx x = 0 := by omega
    rw [hi0] at hx
    have : vs.getD 0 emptyDT = d := by
      simp only [Array.getD_eq_getD_getElem?, h, Option.getD_some]
    rw [← this]
    exact hx
  · have h1' : (vs.size == 1) = false := by simp [h1]
    have hne0 : vs.size ≠ 0 := by omega
    have h0' : (vs.size == 0) = false := by simp [hne0]
    simp only [h1', h0', Bool.false_eq_true, ↓reduceIte] at h
    split_ifs at h with hcheck
    simp only [Option.some.injEq] at h
    subst h
    simp only [Bool.not_eq_true', Bool.not_eq_false, Array.all_eq_true, Bool.and_eq_true,
      beq_iff_eq] at hcheck
    set E := (vs.toList.map (·.e)).foldl min (vs.getD 0 emptyDT).e with hE
    have hEle : ∀ i < vs.size, E ≤ (vs.getD i emptyDT).e := by
      intro i hi
      rw [hE]
      apply foldl_min_le_int
      by_cases hi0 : i = 0
      · subst hi0; exact List.mem_cons_self
      · refine List.mem_cons_of_mem _ (List.mem_map.mpr ⟨vs.getD i emptyDT, ?_, rfl⟩)
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some]
        exact Array.mem_toList_iff.mpr (Array.getElem_mem hi)
    have hsz' : vs.size = ctx.k := hsz
    have hmap : ∀ i < vs.size, (vs.map (·.at E)).getD i emptyDT = (vs.getD i emptyDT).at E :=
      fun i hi => getD_map_of_lt vs (·.at E) emptyDT emptyDT hi
    have hxi : ((vs.map (·.at E)).getD (inputIdx ctx x) emptyDT).Encl t := by
      rw [hmap _ (by omega)]
      exact DT.at_encl hx E
    have hxe : ((vs.map (·.at E)).getD (inputIdx ctx x) emptyDT).e = E := by
      rw [hmap _ (by omega)]
      exact DT.at_e (hEle _ (by omega))
    -- every value has the first one's shape
    have hshape : ((vs.map (·.at E)).getD (inputIdx ctx x) emptyDT).shape =
        ((vs.map (·.at E)).getD 0 emptyDT).shape := by
      have := hcheck (inputIdx ctx x) (by simp; omega)
      simpa [Array.getD_eq_getD_getElem?, show inputIdx ctx x < vs.size by omega] using this.2
    set V := (vs.map (·.at E)).getD (inputIdx ctx x) emptyDT with hV
    have hVmem : V ∈ (vs.map (·.at E)).toList := by
      rw [hV, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simp; omega),
        Option.getD_some]
      exact Array.mem_toList_iff.mpr (Array.getElem_mem _)
    have hVs : V.shape = t.shape := hxi.1.symm
    refine DT.Encl.mk (by rw [← hVs, hshape]) (by rw [hxi.2.1, hshape]) (by simp) (by simp)
      (by simp) (fun j hj => ?_)
    simp only at hj ⊢
    rw [mget_map_range _ _ hj, mget_map_range _ _ hj]
    have hb := hxi.2.2.2.2.2 j
    rw [hxe] at hb
    constructor
    · refine le_trans (dv_le_dv _ ?_) hb.1
      rw [← Array.foldl_toList]
      exact foldl_min_le_mem (fun v => mget v.lo j) _ _ hVmem
    · refine le_trans hb.2 (dv_le_dv _ ?_)
      rw [← Array.foldl_toList]
      exact le_foldl_max_mem (fun v => mget v.hi j) _ _ hVmem

theorem collapseSep_sim {ctx : TCtx} {x : Input} (hf : LeafFacts ctx x) {s : Sep} {t : Tensor ℝ}
    {d : DT} (hs : SepW ctx.box x (fun _ => 1) s t) (h : collapseSep s = some d) : d.Encl t := by
  obtain ⟨hpos, hrl, hts, htsz, hrok, hval⟩ := hs
  unfold collapseSep at h
  by_cases hne : s.rows.isEmpty = true
  · simp [hne] at h
  simp only [hne, Bool.false_eq_true, ↓reduceIte, Option.bind_eq_bind] at h
  obtain ⟨boxes, hboxes, h2⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨c, hc, h3⟩ := Option.bind_eq_some_iff.mp h2
  have hf2 := mapM_forall₂ hboxes
  have hlen : boxes.length = ctx.box.length := by rw [← hf2.length_eq, hrl]
  have hbox : ∀ p < ctx.box.length, ∃ ROW : Tensor ℝ, (boxes.getD p emptyDT).Encl ROW ∧
      ROW.shape = 1 :: s.rest ∧ ∀ q < shapeSize s.rest,
        ROW.get q =
          (s.rows.getD p emptyDT).real.get (rowOf ctx.box x p * shapeSize s.rest + q) := by
    intro p hp
    have h4 := forall₂_getD hf2 (by rw [hrl]; exact hp) emptyDT emptyDT
    exact dtMinMax_sim (DT.at_encl (hrok p hp).encl _) (hrok p hp).2.2.2 (hf.row_lt p hp) h4
  have : Nonempty (Tensor ℝ) := ⟨⟨[], #[]⟩⟩
  choose! F hF using hbox
  have hrel : List.Forall₂ DT.Encl boxes ((List.range boxes.length).map F) :=
    forall₂_range_map boxes F emptyDT (fun p hp => (hF p (by omega)).1)
  obtain ⟨CAT, hCAT, hcCAT⟩ := djoin_sim (catOp_mover 0) hrel hc
  have hshapes : ∀ T ∈ (List.range boxes.length).map F, T.shape = 1 :: s.rest := by
    intro T hT
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hT
    exact (hF p (by have := List.mem_range.mp hp; omega)).2.1
  have hne' : (List.range boxes.length).map F ≠ [] := by
    intro h0
    have := congrArg List.length h0
    simp only [List.length_map, List.length_range, List.length_nil] at this
    omega
  obtain ⟨hCATs, -, hCATget⟩ := catOp_first hshapes hne' hCAT
  obtain ⟨U, hU, hdU⟩ := dtUnsqueeze_sim hcCAT h3
  obtain ⟨hUs, hUd⟩ := unsqueezeOp_zero hU
  have hUs' : U.shape = 1 :: ctx.box.length :: s.rest := by rw [hUs, hCATs]; simp [hlen]
  have hUsz : U.data.size = ctx.box.length * shapeSize s.rest := by
    rw [hdU.2.1, ← hdU.1, hUs', shapeSize_one_cons]
  refine hdU.congr (by rw [hts, hUs']) (by rw [htsz, hUsz]) ?_
  rw [hUsz]
  refine get_eq_of_rows (fun p hp q hq => ?_)
  have hU' : U.get (p * shapeSize s.rest + q) = CAT.get (p * shapeSize s.rest + q) := by
    simp [Tensor.get, hUd]
  have hr : (List.range boxes.length).getD p 0 = p := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega)]
    simp
  rw [hval p hp q hq, hU', hCATget p (by simp; omega) q hq, list_getD_map _ (by simp; omega) 0,
    hr, (hF p hp).2.2 q hq, one_mul]

theorem collapseWSep_inl_sim {ctx : TCtx} {x : Input} (hf : LeafFacts ctx x) {w : DT} {s : Sep}
    {t : Tensor ℝ} {d : DT} (hw : WSepR ctx x w s t) (h : collapseWSep (.inl w) s = some d) :
    d.Encl t := by
  obtain ⟨hws, W, hwW, hsep⟩ := hw
  obtain ⟨hT, -⟩ := hsep.unweight
  unfold collapseWSep at h
  obtain ⟨w', hw', h1⟩ := Option.bind_eq_some_iff.mp h
  simp only [Option.some.injEq] at hw'
  subst hw'
  obtain ⟨box, hbox, h2⟩ := Option.bind_eq_some_iff.mp h1
  have hboxT := collapseSep_sim hf hT hbox
  obtain ⟨Z, hZ, hdZ⟩ := dbinary_sim hwW hboxT h2
  exact encl_wsep hsep (by rw [hwW.1, hws]) hZ hdZ

theorem collapseWSep_inr_sim {ctx : TCtx} {x : Input} (hf : LeafFacts ctx x) {ws : Array DT}
    {s : Sep} {t : Tensor ℝ} {d : DT} (hw : WSepVR ctx x ws s t)
    (h : collapseWSep (.inr ws) s = some d) : d.Encl t := by
  obtain ⟨hwsz, hall, W, hwW, hsep⟩ := hw
  obtain ⟨hT, -⟩ := hsep.unweight
  unfold collapseWSep at h
  simp only [Option.bind_eq_bind] at h
  obtain ⟨w, hw, h1⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨box, hbox, h2⟩ := Option.bind_eq_some_iff.mp h1
  have hwW' := collapseVar_sim hf ⟨hwsz, fun i hi => (hall i hi).2, hwW⟩ hw
  have hboxT := collapseSep_sim hf hT hbox
  obtain ⟨Z, hZ, hdZ⟩ := dbinary_sim hwW' hboxT h2
  exact encl_wsep hsep (by rw [hwW.1, (hall _ hf.idx_lt).1]) hZ hdZ

/-! ## Leaving the domain -/

/-- What a value becomes when it leaves the domain: values per input or an
    interval tensor, still related to the real value. -/
theorem tLeave_sim {g : Graph} {ctx : TCtx} {x : Input} (hf : LeafFacts ctx x) {v v' : TV}
    {t : Tensor ℝ} (hv : TRel g ctx x v t) (h : tLeave ctx v = some v') :
    TRel g ctx x v' t ∧ ((∃ vs, v' = .var vs) ∨ (∃ d, v' = .dt d)) := by
  cases v with
  | box => simp [tLeave] at h
  | var vs =>
    simp only [tLeave, Option.some.injEq] at h
    subst h
    exact ⟨hv, Or.inl ⟨vs, rfl⟩⟩
  | dt d =>
    simp only [tLeave, Option.some.injEq] at h
    subst h
    exact ⟨hv, Or.inr ⟨d, rfl⟩⟩
  | mix m =>
    simp only [tLeave] at h
    cases hc : concretize m with
    | none => simp [hc] at h
    | some o =>
      cases o with
      | some d =>
        simp only [hc, Option.some.injEq] at h
        subst h
        exact ⟨concretize_sim hf hv hc, Or.inr ⟨d, rfl⟩⟩
      | none =>
        simp only [hc] at h
        split_ifs at h with hal
        · obtain ⟨xs, hxs, rfl⟩ := Option.map_eq_some_iff.mp h
          exact ⟨toVarMix_sim hf hal hv hxs, Or.inl ⟨xs, rfl⟩⟩
        · obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp h
          exact ⟨collapseMix_sim hf hv hd, Or.inr ⟨d, rfl⟩⟩
  | sep s =>
    simp only [tLeave] at h
    split_ifs at h with hal
    · obtain ⟨xs, hxs, rfl⟩ := Option.map_eq_some_iff.mp h
      exact ⟨toVarSep_sim hf hal hv hxs, Or.inl ⟨xs, rfl⟩⟩
    · obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp h
      exact ⟨collapseSep_sim hf hv hd, Or.inr ⟨d, rfl⟩⟩
  | wsep w s =>
    simp only [tLeave] at h
    split_ifs at h with hal
    · obtain ⟨xs, hxs, rfl⟩ := Option.map_eq_some_iff.mp h
      exact ⟨toVarWSep_inl_sim hf hal hv hxs, Or.inl ⟨xs, rfl⟩⟩
    · obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp h
      exact ⟨collapseWSep_inl_sim hf hv hd, Or.inr ⟨d, rfl⟩⟩
  | wsepv ws s =>
    simp only [tLeave] at h
    split_ifs at h with hal
    · obtain ⟨xs, hxs, rfl⟩ := Option.map_eq_some_iff.mp h
      exact ⟨toVarWSep_inr_sim hf hal hv hxs, Or.inl ⟨xs, rfl⟩⟩
    · obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp h
      exact ⟨collapseWSep_inr_sim hf hv hd, Or.inr ⟨d, rfl⟩⟩

/-- A value other than an interval tensor as values per input. -/
theorem tToVar_sim {g : Graph} {ctx : TCtx} {x : Input} (hf : LeafFacts ctx x)
    (hal : ctx.aligned = true) {v : TV} {t : Tensor ℝ} {xs : Array DT} (hv : TRel g ctx x v t)
    (hnd : ∀ d, v ≠ .dt d) (h : tToVar ctx v = some xs) : VarR ctx x xs t := by
  cases v with
  | box => simp [tToVar] at h
  | var vs =>
    simp only [tToVar, Option.some.injEq] at h
    subst h
    exact hv
  | dt d => exact absurd rfl (hnd d)
  | mix m => exact toVarMix_sim hf hal hv h
  | sep s => exact toVarSep_sim hf hal hv h
  | wsep w s => exact toVarWSep_inl_sim hf hal hv h
  | wsepv ws s => exact toVarWSep_inr_sim hf hal hv h

end CompactCheck
