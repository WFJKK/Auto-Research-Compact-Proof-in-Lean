import CompactCheck.GeneralSound
import CompactCheck.Tokens

/-!
# Entries of operations on rows, for the token rules

The token rules of `Tokens.lean` hold a value of shape `[1, positions] ++ rest`
as one row per position. This file gives the entries of the operations of
`Semantics.lean` at the flat positions `p * S + q` of such values (`S` the
size of `rest`): broadcasting, `expand`, indexing, `stack`, `cat`, sums and
matrix products. `TokensSound.lean` uses them to show that each token rule
computes what the network computes.
-/

namespace CompactCheck

/-! ## Flat positions -/

theorem shapeSize_cons (n : ℕ) (rest : List ℕ) : shapeSize (n :: rest) = n * shapeSize rest := by
  simp [shapeSize]

theorem shapeSize_nil : shapeSize [] = 1 := rfl

theorem unravel_cons_eq (n : ℕ) (rest : List ℕ) (J : ℕ) :
    unravel (n :: rest) J = (J / shapeSize rest % n) :: unravel rest J := by
  simp [unravel, strides]

theorem unravel_add_mul (s : List ℕ) (m q : ℕ) :
    unravel s (m * shapeSize s + q) = unravel s q := by
  induction s generalizing m with
  | nil => simp [unravel, strides]
  | cons d s ih =>
    rw [unravel_cons_eq, unravel_cons_eq, shapeSize_cons,
      show m * (d * shapeSize s) + q = (m * d) * shapeSize s + q by ring, ih]
    congr 1
    rcases Nat.eq_zero_or_pos (shapeSize s) with h0 | hpos
    · simp [h0]
    · rw [show m * d * shapeSize s + q = q + shapeSize s * (m * d) by ring,
        Nat.add_mul_div_left _ _ hpos, Nat.add_mul_mod_self_right]

theorem unravel_cons {n j q : ℕ} {rest : List ℕ} (hq : q < shapeSize rest) (hj : j < n) :
    unravel (n :: rest) (j * shapeSize rest + q) = j :: unravel rest q := by
  rw [unravel_cons_eq, unravel_add_mul, div_aux (by omega) hq, Nat.mod_eq_of_lt hj]

theorem ravel_cons (n : ℕ) (rest : List ℕ) (j : ℕ) (i : List ℕ) :
    ravel (n :: rest) (j :: i) = j * shapeSize rest + ravel rest i := by
  simp only [ravel, strides, List.zipWith_cons_cons, List.sum_cons]
  ring

theorem entry_cons {α : Type} [Zero α] {t : Tensor α} {n : ℕ} {rest : List ℕ}
    (hs : t.shape = n :: rest) (j : ℕ) (i : List ℕ) :
    t.entry (j :: i) = t.get (j * shapeSize rest + ravel rest i) := by
  rw [Tensor.entry_eq, hs, ravel_cons]

/-- The entry at the multi-index of flat position `q`. -/
theorem entry_unravel {α : Type} [Zero α] {t : Tensor α} {s : List ℕ} (hs : t.shape = s) {q : ℕ}
    (hq : q < shapeSize s) : t.entry (unravel s q) = t.get q := by
  rw [Tensor.entry_eq, hs, ravel_unravel_of_lt hq]

/-- The positions of a value of shape `[1, P] ++ rest`. -/
theorem unravel_three_cons {P p q : ℕ} {rest : List ℕ} (hp : p < P) (hq : q < shapeSize rest) :
    unravel (1 :: P :: rest) (p * shapeSize rest + q) = 0 :: p :: unravel rest q := by
  have h1 : p * shapeSize rest + q < shapeSize (P :: rest) := by
    rw [shapeSize_cons]
    calc p * shapeSize rest + q < p * shapeSize rest + shapeSize rest := by omega
      _ = (p + 1) * shapeSize rest := by ring
      _ ≤ P * shapeSize rest := Nat.mul_le_mul_right _ hp
  have := unravel_cons (n := 1) (j := 0) (rest := P :: rest) h1 (by omega)
  rw [Nat.zero_mul, Nat.zero_add] at this
  rw [this, unravel_cons hq hp]

theorem lt_mul_of_row {p q P S : ℕ} (hp : p < P) (hq : q < S) : p * S + q < P * S := by
  calc p * S + q < p * S + S := by omega
    _ = (p + 1) * S := by ring
    _ ≤ P * S := Nat.mul_le_mul_right _ hp

theorem shapeSize_one_cons (P : ℕ) (rest : List ℕ) :
    shapeSize (1 :: P :: rest) = P * shapeSize rest := by
  simp [shapeSize_cons]

/-! ## Broadcasting -/

theorem broadcastIndex_cons (s i : List ℕ) (k : ℕ) (h : s.length ≤ i.length) :
    broadcastIndex s (k :: i) = broadcastIndex s i := by
  unfold broadcastIndex
  congr 1
  simp only [List.length_cons]
  rw [show i.length + 1 - s.length = (i.length - s.length) + 1 by omega, List.drop_succ_cons]

theorem broadcastOp_spec {α : Type} [Zero α] {f : α → α → α} {a b r : Tensor α}
    (h : broadcastOp f a b = some r) : ∃ s, broadcastShape a.shape b.shape = some s ∧
      r = Tensor.ofFn s (fun i => f (a.entry (broadcastIndex a.shape i))
        (b.entry (broadcastIndex b.shape i))) ∧ a.wellFormed = true ∧ b.wellFormed = true := by
  unfold broadcastOp at h
  split_ifs at h with hw
  obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.mp h
  simp only [Bool.and_eq_true] at hw
  exact ⟨s, hs, rfl, hw.1, hw.2⟩

theorem broadcastOp_eq {α : Type} [Zero α] (f : α → α → α) {a b : Tensor α} {s : List ℕ}
    (ha : a.wellFormed = true) (hb : b.wellFormed = true)
    (hs : broadcastShape a.shape b.shape = some s) :
    broadcastOp f a b = some (Tensor.ofFn s (fun i => f (a.entry (broadcastIndex a.shape i))
        (b.entry (broadcastIndex b.shape i)))) := by
  unfold broadcastOp
  simp [ha, hb, hs]

/-- The entry of a tensor of the full shape, read by broadcasting. -/
theorem entry_broadcast_self {α : Type} [Zero α] {t : Tensor α} {s : List ℕ} (hs : t.shape = s)
    {j : ℕ} (hj : j < shapeSize s) : t.entry (broadcastIndex t.shape (unravel s j)) = t.get j := by
  rw [hs, broadcastIndex_unravel, entry_unravel hs hj]

theorem mapM_zip_fst {f : ℕ × ℕ → Option ℕ} :
    ∀ {l1 l2 : List ℕ}, l1.length = l2.length → (∀ p ∈ List.zip l1 l2, f p = some p.1) →
      (List.zip l1 l2).mapM f = some l1
  | [], [], _, _ => rfl
  | a :: l1, b :: l2, hl, h => by
    simp only [List.zip_cons_cons, List.mapM_cons]
    rw [h (a, b) List.mem_cons_self,
      mapM_zip_fst (by simpa using hl) (fun p hp => h p (List.mem_cons_of_mem _ hp))]
    rfl
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

theorem mapM_zip_snd {f : ℕ × ℕ → Option ℕ} :
    ∀ {l1 l2 : List ℕ}, l1.length = l2.length → (∀ p ∈ List.zip l1 l2, f p = some p.2) →
      (List.zip l1 l2).mapM f = some l2
  | [], [], _, _ => rfl
  | a :: l1, b :: l2, hl, h => by
    simp only [List.zip_cons_cons, List.mapM_cons]
    rw [h (a, b) List.mem_cons_self,
      mapM_zip_snd (by simpa using hl) (fun p hp => h p (List.mem_cons_of_mem _ hp))]
    rfl
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

theorem zipWith_fits_mem {t B : List ℕ}
    (hfit : (List.zipWith (fun d f => d == f || d == 1) t B).all id = true) :
    ∀ p ∈ List.zip B t, p.2 = p.1 ∨ p.2 = 1 := by
  intro p hp
  obtain ⟨i, hi, hpi⟩ := List.getElem_of_mem hp
  have hi1 : i < B.length := by simp at hi; omega
  have hi2 : i < t.length := by simp at hi; omega
  have hz := List.all_eq_true.mp hfit ((List.zipWith (fun d f => d == f || d == 1) t B)[i]'(by
    simp; omega)) (List.getElem_mem _)
  simp only [List.getElem_zipWith, id, Bool.or_eq_true, beq_iff_eq] at hz
  rw [← hpi]
  simp only [List.getElem_zip]
  rcases hz with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- A shape that `expand` can broadcast to `s` broadcasts with `s` to `s`,
    in either order. -/
theorem broadcastShape_of_fits {s t : List ℕ} (hl : t.length ≤ s.length)
    (hfit : (List.zipWith (fun d f => d == f || d == 1) t (s.drop (s.length - t.length))).all id
      = true) :
    broadcastShape s t = some s ∧ broadcastShape t s = some s := by
  obtain ⟨A, B, rfl, hBl⟩ : ∃ A B, s = A ++ B ∧ B.length = t.length :=
    ⟨s.take (s.length - t.length), s.drop (s.length - t.length),
      (List.take_append_drop _ _).symm, by simp; omega⟩
  have hd : (A ++ B).length - t.length = A.length := by simp; omega
  rw [hd, List.drop_left] at hfit
  have hmem := zipWith_fits_mem hfit
  have hrep : ∀ p ∈ List.zip A (List.replicate A.length 1), p.2 = 1 := fun p hp =>
    List.eq_of_mem_replicate (List.of_mem_zip hp).2
  have hrep' : ∀ p ∈ List.zip (List.replicate A.length 1) A, p.1 = 1 := fun p hp =>
    List.eq_of_mem_replicate (List.of_mem_zip hp).1
  unfold broadcastShape
  dsimp only
  have hn : max (A ++ B).length t.length = (A ++ B).length := max_eq_left hl
  have hn' : max t.length (A ++ B).length = (A ++ B).length := max_eq_right hl
  rw [hn, hn', Nat.sub_self, List.replicate_zero, List.nil_append, hd]
  constructor
  · rw [List.zip_append (by rw [List.length_replicate]), List.mapM_append,
      mapM_zip_fst (by simp) ?_, mapM_zip_fst hBl ?_]
    · rfl
    · intro p hp
      rcases hmem p hp with h | h
      · simp [h]
      · by_cases h1 : p.1 = p.2
        · simp [h1]
        · by_cases h2 : p.1 = 1
          · exact absurd (h2.trans h.symm) h1
          · simp [h2, h]
    · intro p hp
      have := hrep p hp
      by_cases h1 : p.1 = p.2
      · simp [h1]
      · by_cases h2 : p.1 = 1
        · exact absurd (h2.trans this.symm) h1
        · simp [h2, this]
  · rw [List.zip_append (by rw [List.length_replicate]), List.mapM_append,
      mapM_zip_snd (by simp) ?_, mapM_zip_snd hBl.symm ?_]
    · rfl
    · intro p hp
      rcases hmem (p.2, p.1) (by rw [← List.zip_swap]; exact List.mem_map_of_mem hp) with h | h
      · simp only at h
        simp [h]
      · simp only at h
        by_cases h1 : p.1 = p.2
        · simp [h1]
        · simp [h]
    · intro p hp
      have := hrep' p hp
      by_cases h1 : p.1 = p.2
      · simp [h1]
      · simp [this]

/-! ## `expand` -/

theorem mapM_range_some {β : Type} (g : ℕ → β) :
    ∀ n, ((List.range n).mapM fun i => (some (g i) : Option β)) = some ((List.range n).map g)
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.mapM_append, mapM_range_some g n]
    simp

theorem map_getD_range (s : List ℕ) : (List.range s.length).map (fun i => s.getD i 0) = s := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

theorem mapM_eq_some_of_forall {β γ : Type} {F : β → Option γ} {g : β → γ} :
    ∀ {l : List β}, (∀ a ∈ l, F a = some (g a)) → l.mapM F = some (l.map g)
  | [], _ => rfl
  | a :: l, h => by
    rw [List.mapM_cons, h a List.mem_cons_self,
      mapM_eq_some_of_forall (fun b hb => h b (List.mem_cons_of_mem _ hb))]
    rfl

theorem expandShape_nat (ts s : List ℕ) : expandShape ts (s.map Int.ofNat) = some s := by
  unfold expandShape
  rw [List.length_map]
  refine (mapM_eq_some_of_forall (g := fun i => s.getD i 0) ?_).trans (by rw [map_getD_range])
  intro i hi
  have hi' := List.mem_range.mp hi
  have hx : (s.map Int.ofNat).getD i 0 = ((s.getD i 0 : ℕ) : ℤ) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
  simp only [hx]
  simp

theorem expandOp_nat_spec {α : Type} [Zero α] {C E : Tensor α} {s : List ℕ}
    (h : expandOp C (s.map Int.ofNat) = some E) :
    E = Tensor.ofFn s (fun i => C.entry (broadcastIndex C.shape i)) ∧
      C.shape.length ≤ s.length ∧
      (List.zipWith (fun d f => d == f || d == 1) C.shape
        (s.drop (s.length - C.shape.length))).all id = true := by
  unfold expandOp at h
  rw [expandShape_nat, List.length_map] at h
  dsimp only at h
  split_ifs at h with h1 h2
  simp only [Option.some.injEq] at h
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, not_or] at h1
  exact ⟨h.symm, by omega, h2⟩

/-! ## Indexing -/

theorem indexOp_spec {α : Type} [Zero α] {T r : Tensor α} {items : List IndexItem}
    (h : indexOp T items = some r) :
    r = Tensor.ofFn ((List.zipWith IndexItem.dims (T.shape.take items.length) items).flatten ++
      T.shape.drop items.length) (fun i => T.entry (sourceIndex items i)) := by
  unfold indexOp at h
  split_ifs at h
  simp only [Option.some.injEq] at h
  exact h.symm

theorem indexOp_eq {α : Type} [Zero α] {T : Tensor α} {items : List IndexItem}
    (hl : items.length ≤ T.shape.length) (hw : T.wellFormed = true)
    (hf : (List.zipWith IndexItem.fits (T.shape.take items.length) items).all id = true) :
    indexOp T items = some (Tensor.ofFn ((List.zipWith IndexItem.dims (T.shape.take items.length)
      items).flatten ++ T.shape.drop items.length) (fun i => T.entry (sourceIndex items i))) := by
  unfold indexOp
  simp [hl, hw, hf]

/-- `t[0, p]` of a value of shape `[1, P] ++ rest`: shape `rest`, the entries
    `p * S + q`. -/
theorem indexOp_pos {α : Type} [Zero α] {T r : Tensor α} {P p : ℕ} {rest : List ℕ}
    (hs : T.shape = 1 :: P :: rest) (h : indexOp T [.one 0, .one p] = some r) :
    r.shape = rest ∧ r.data.size = shapeSize rest ∧
      ∀ q < shapeSize rest, r.get q = T.get (p * shapeSize rest + q) := by
  rw [indexOp_spec h]
  simp only [hs, List.length_cons, List.length_nil, Nat.reduceAdd, List.take_succ_cons,
    List.take_zero, List.zipWith_cons_cons, IndexItem.dims, List.zipWith_nil_left,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.nil_append, List.drop_succ_cons,
    List.drop_zero]
  refine ⟨rfl, Tensor.ofFn_data_size _ _, fun q hq => ?_⟩
  rw [Tensor.ofFn_get _ _ hq]
  simp only [sourceIndex]
  rw [Tensor.entry_eq, hs, ravel_cons, ravel_cons, ravel_unravel_of_lt hq]
  simp

/-- `t[i]` of a value of shape `n :: rest`. -/
theorem indexOp_one {α : Type} [Zero α] {T r : Tensor α} {n i : ℕ} {rest : List ℕ}
    (hs : T.shape = n :: rest) (h : indexOp T [.one i] = some r) :
    r.shape = rest ∧ r.data.size = shapeSize rest ∧
      ∀ q < shapeSize rest, r.get q = T.get (i * shapeSize rest + q) := by
  rw [indexOp_spec h]
  simp only [hs, List.length_cons, List.length_nil, Nat.reduceAdd, List.take_succ_cons,
    List.take_zero, List.zipWith_cons_cons, IndexItem.dims, List.zipWith_nil_left,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.nil_append, List.drop_succ_cons,
    List.drop_zero]
  refine ⟨rfl, Tensor.ofFn_data_size _ _, fun q hq => ?_⟩
  rw [Tensor.ofFn_get _ _ hq]
  simp only [sourceIndex]
  rw [Tensor.entry_eq, hs, ravel_cons, ravel_unravel_of_lt hq]

/-- `t[r : r + 1]` of a value of shape `n :: rest`. -/
theorem indexOp_range1 {α : Type} [Zero α] {T R : Tensor α} {n r : ℕ} {rest : List ℕ}
    (hs : T.shape = n :: rest) (h : indexOp T [.range r (r + 1)] = some R) :
    R.shape = 1 :: rest ∧ R.data.size = shapeSize rest ∧
      ∀ q < shapeSize rest, R.get q = T.get (r * shapeSize rest + q) := by
  rw [indexOp_spec h]
  simp only [hs, List.length_cons, List.length_nil, Nat.reduceAdd, List.take_succ_cons,
    List.take_zero, List.zipWith_cons_cons, IndexItem.dims, List.zipWith_nil_left,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_succ_cons,
    List.drop_zero, Nat.add_sub_cancel_left, List.cons_append, List.nil_append]
  refine ⟨rfl, by rw [Tensor.ofFn_data_size, shapeSize_cons, Nat.one_mul], fun q hq => ?_⟩
  have hq' : q < shapeSize (1 :: rest) := by rw [shapeSize_cons]; omega
  rw [Tensor.ofFn_get _ _ hq']
  have hu := unravel_cons (n := 1) (j := 0) hq (by omega)
  rw [Nat.zero_mul, Nat.zero_add] at hu
  rw [hu]
  simp only [sourceIndex, List.headD_cons, Nat.add_zero, List.tail_cons]
  rw [Tensor.entry_eq, hs, ravel_cons, ravel_unravel_of_lt hq]

/-- `t[:, p]` of a value of shape `[1, P] ++ rest`: shape `1 :: rest`. -/
theorem indexOp_getitem {α : Type} [Zero α] {T : Tensor α} {P p : ℕ} {rest : List ℕ}
    (hs : T.shape = 1 :: P :: rest) (hw : T.wellFormed = true) (hp : p < P) :
    ∃ R, indexOp T [.all, .one p] = some R ∧ R.shape = 1 :: rest ∧
      R.data.size = shapeSize rest ∧
      ∀ q < shapeSize rest, R.get q = T.get (p * shapeSize rest + q) := by
  rw [indexOp_eq (by simp [hs]) hw (by simp [hs, IndexItem.fits, hp])]
  simp only [hs, List.length_cons, List.length_nil, Nat.reduceAdd, List.take_succ_cons,
    List.take_zero, List.zipWith_cons_cons, IndexItem.dims, List.zipWith_nil_left,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_succ_cons,
    List.drop_zero, List.cons_append, List.nil_append]
  refine ⟨_, rfl, rfl, by rw [Tensor.ofFn_data_size, shapeSize_cons, Nat.one_mul],
    fun q hq => ?_⟩
  have hq' : q < shapeSize (1 :: rest) := by rw [shapeSize_cons]; omega
  rw [Tensor.ofFn_get _ _ hq']
  have hu := unravel_cons (n := 1) (j := 0) hq (by omega)
  rw [Nat.zero_mul, Nat.zero_add] at hu
  rw [hu]
  simp only [sourceIndex, List.headD_cons, List.tail_cons]
  rw [Tensor.entry_eq, hs, ravel_cons, ravel_cons, ravel_unravel_of_lt hq]
  simp

/-! ## Weights of one value per position -/

theorem shapeSize_replicate_one (n : ℕ) : shapeSize (List.replicate n 1) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, shapeSize_cons, ih]

theorem shapeSize_weightShape (P : ℕ) (rest : List ℕ) : shapeSize (weightShape P rest) = P := by
  rw [weightShape, shapeSize_cons, shapeSize_cons, shapeSize_replicate_one]
  ring

theorem strides_replicate_one (n : ℕ) : strides (List.replicate n 1) = List.replicate n 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, strides, ih, shapeSize_replicate_one]

theorem zipWith_mul_sum_le (st i : List ℕ) (h : ∀ a ∈ i, a = 0) :
    (List.zipWith (· * ·) st i).sum = 0 := by
  induction st generalizing i with
  | nil => simp
  | cons a st ih =>
    cases i with
    | nil => simp
    | cons k i =>
      simp only [List.zipWith_cons_cons, List.sum_cons]
      rw [h k List.mem_cons_self, ih i (fun b hb => h b (List.mem_cons_of_mem _ hb))]
      simp

theorem ravel_replicate_one (n : ℕ) (i : List ℕ) (h : ∀ a ∈ i, a < 1) :
    ravel (List.replicate n 1) i = 0 := by
  unfold ravel
  apply zipWith_mul_sum_le
  intro a ha
  have := h a ha
  omega

theorem ravel_zeros (s : List ℕ) (n : ℕ) : ravel s (List.replicate n 0) = 0 :=
  zipWith_mul_sum_le _ _ (fun _ ha => List.eq_of_mem_replicate ha)

theorem zipWith_bcast_replicate_one (n : ℕ) (i : List ℕ) (h : i.length = n) :
    List.zipWith (fun d k => if d = 1 then 0 else k) (List.replicate n 1) i =
      List.replicate n 0 := by
  subst h
  induction i with
  | nil => rfl
  | cons k i ih => simp [List.replicate_succ, ih]

/-- Broadcasting one weight per position: entry `p * S + q` reads weight `p`. -/
theorem entry_broadcast_weight {α : Type} [Zero α] {W : Tensor α} {P p : ℕ} {rest : List ℕ}
    (hW : W.shape = weightShape P rest) (hp : p < P) {q : ℕ} (hq : q < shapeSize rest) :
    W.entry (broadcastIndex W.shape (unravel (1 :: P :: rest) (p * shapeSize rest + q))) =
      W.get p := by
  rw [unravel_three_cons hp hq, hW]
  have hlen : (unravel rest q).length = rest.length := unravel_length _ _
  have hb : broadcastIndex (weightShape P rest) (0 :: p :: unravel rest q) =
      0 :: p :: List.replicate rest.length 0 := by
    unfold broadcastIndex weightShape
    simp only [List.length_cons, List.length_replicate, hlen, Nat.sub_self, List.drop_zero,
      List.zipWith_cons_cons, ↓reduceIte]
    rw [zipWith_bcast_replicate_one _ _ hlen]
    have hP : (if P = 1 then 0 else p) = p := by
      split_ifs with h1
      · omega
      · rfl
    rw [hP]
  rw [hb, Tensor.entry_eq, hW, weightShape, ravel_cons, ravel_cons, ravel_zeros,
    shapeSize_replicate_one]
  simp

theorem dims_ranges (rest : List ℕ) :
    (List.zipWith IndexItem.dims rest (List.replicate rest.length (IndexItem.range 0 1))).flatten =
      List.replicate rest.length 1 := by
  induction rest with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.length_cons, List.replicate_succ, List.zipWith_cons_cons, IndexItem.dims,
      List.flatten_cons, ih, Nat.sub_zero, List.singleton_append]

theorem dims_ones (rest : List ℕ) :
    (List.zipWith IndexItem.dims rest (List.replicate rest.length (IndexItem.one 0))).flatten =
      [] := by
  induction rest with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.length_cons, List.replicate_succ, List.zipWith_cons_cons, IndexItem.dims,
      List.flatten_cons, ih, List.nil_append]

theorem sourceIndex_ranges (n : ℕ) (i : List ℕ) (h : i.length = n) :
    sourceIndex (List.replicate n (IndexItem.range 0 1)) i = i := by
  subst h
  induction i with
  | nil => rfl
  | cons k i ih => simp [List.replicate_succ, sourceIndex, ih]

theorem sourceIndex_ones (n : ℕ) :
    sourceIndex (List.replicate n (IndexItem.one 0)) [] = List.replicate n 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, sourceIndex, ih]

theorem firstItems_eq (rest : List ℕ) :
    firstItems rest = .all :: .all :: List.replicate rest.length (IndexItem.range 0 1) := by
  simp [firstItems]

theorem unravel_weight {P p : ℕ} (rest : List ℕ) (hp : p < P) :
    unravel (weightShape P rest) p = 0 :: p :: List.replicate rest.length 0 := by
  have h1 : p = p * shapeSize (List.replicate rest.length 1) + 0 := by
    rw [shapeSize_replicate_one]; ring
  rw [weightShape, h1, unravel_three_cons hp (by rw [shapeSize_replicate_one]; omega)]
  congr 2
  apply List.ext_getElem (by simp [unravel_length])
  intro i h1 h2
  simp only [List.getElem_replicate]
  have := unravel_getD (List.replicate rest.length 1) 0 (d := i)
    (by simpa [unravel_length] using h1)
  simp only [Nat.zero_div, Nat.zero_mod] at this
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some] at this
  exact this

/-- `t[:, :, 0:1, ..., 0:1]`: the first entries along `rest`, one per
    position. -/
theorem indexOp_first {α : Type} [Zero α] {T r : Tensor α} {P : ℕ} {rest : List ℕ}
    (hs : T.shape = 1 :: P :: rest) (h : indexOp T (firstItems rest) = some r) :
    r.shape = weightShape P rest ∧ ∀ p < P, r.get p = T.get (p * shapeSize rest) := by
  rw [indexOp_spec h, hs, firstItems_eq]
  have hlen : (IndexItem.all :: IndexItem.all ::
      List.replicate rest.length (IndexItem.range 0 1)).length = (1 :: P :: rest).length := by
    simp
  rw [hlen, List.take_length, List.drop_length, List.append_nil]
  simp only [List.zipWith_cons_cons, IndexItem.dims, List.flatten_cons, dims_ranges,
    List.singleton_append]
  refine ⟨rfl, fun p hp => ?_⟩
  rw [Tensor.ofFn_get _ _ (by rw [← weightShape, shapeSize_weightShape]; exact hp),
    ← weightShape, unravel_weight rest hp]
  simp only [sourceIndex, List.headD_cons, List.tail_cons]
  rw [sourceIndex_ranges _ _ (by simp), Tensor.entry_eq, hs, ravel_cons, ravel_cons, ravel_zeros]
  simp

/-- The weight of position `p` (`weightAt`): shape `[]`, entry `p`. -/
theorem indexOp_weight {α : Type} [Zero α] {W r : Tensor α} {P p : ℕ} {rest : List ℕ}
    (hW : W.shape = weightShape P rest)
    (h : indexOp W ([.one 0, .one p] ++ rest.map fun _ => .one 0) = some r) :
    r.shape = [] ∧ r.data.size = 1 ∧ r.get 0 = W.get p := by
  rw [indexOp_spec h, hW]
  have hitems : ([IndexItem.one 0, .one p] ++ rest.map fun _ => IndexItem.one 0) =
      .one 0 :: .one p :: List.replicate rest.length (IndexItem.one 0) := by simp
  rw [hitems]
  have hlen : (IndexItem.one 0 :: IndexItem.one p ::
      List.replicate rest.length (IndexItem.one 0)).length = (weightShape P rest).length := by
    simp [weightShape]
  rw [hlen, List.take_length, List.drop_length, List.append_nil, weightShape]
  simp only [List.zipWith_cons_cons, IndexItem.dims, List.flatten_cons, List.nil_append]
  rw [show List.replicate rest.length 1 = List.replicate (List.replicate rest.length 1).length 1 by
    simp] at *
  have hd := dims_ones (List.replicate rest.length 1)
  simp only [List.length_replicate] at hd ⊢
  rw [hd]
  refine ⟨rfl, by rw [Tensor.ofFn_data_size]; rfl, ?_⟩
  rw [Tensor.ofFn_get _ _ (by simp [shapeSize])]
  simp only [unravel, strides, List.zipWith_nil_left, sourceIndex]
  rw [sourceIndex_ones, Tensor.entry_eq, hW, weightShape, ravel_cons, ravel_cons, ravel_zeros,
    shapeSize_replicate_one]
  simp

/-! ## `stack`, `cat` and `unsqueeze` along the first dimension -/

theorem stackOp_first {α : Type} [Zero α] {ts : List (Tensor α)} {r : Tensor α} {rest : List ℕ}
    (hs : ∀ t ∈ ts, t.shape = rest) (hne : ts ≠ []) (h : stackOp ts 0 = some r) :
    r.shape = ts.length :: rest ∧ r.data.size = ts.length * shapeSize rest ∧
      ∀ p < ts.length, ∀ q < shapeSize rest,
        r.get (p * shapeSize rest + q) = (ts.getD p ⟨[], #[]⟩).get q := by
  unfold stackOp at h
  split_ifs at h with hw
  obtain ⟨t0, ts', rfl⟩ := List.exists_cons_of_ne_nil hne
  have h0 : t0.shape = rest := hs t0 List.mem_cons_self
  have hall : ((ts'.map (·.shape)).all fun s => s == rest) = true := by
    simp only [List.all_map, List.all_eq_true, Function.comp_apply, beq_iff_eq]
    exact fun t ht => hs t (List.mem_cons_of_mem _ ht)
  have hnd : normDim 0 (rest.length + 1) = some 0 := by simp [normDim]
  simp only [List.map_cons, stackShape, h0, hnd, List.all_cons, beq_self_eq_true, Bool.true_and,
    hall, ↓reduceIte, Option.some.injEq] at h
  subst h
  simp only [List.take_zero, List.nil_append, List.drop_zero, List.length_cons, List.length_map,
    List.singleton_append]
  refine ⟨rfl, by rw [Tensor.ofFn_data_size, shapeSize_cons], fun p hp q hq => ?_⟩
  rw [Tensor.ofFn_get _ _ (by rw [shapeSize_cons]; exact lt_mul_of_row hp hq),
    unravel_cons hq hp]
  simp only [List.getD_cons_zero, List.eraseIdx_cons_zero]
  have hmem : (t0 :: ts').getD p ⟨[], #[]⟩ ∈ t0 :: ts' := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp, Option.getD_some]
    exact List.getElem_mem hp
  rw [entry_unravel (hs _ hmem) hq]

/-- Locating a position among parts of size 1. -/
theorem locate_ones (n k start : ℕ) (h1 : start ≤ k) (h2 : k < start + n) :
    locate (List.replicate n 1) k start = (k - start, k) := by
  induction n generalizing start with
  | zero => omega
  | succ n ih =>
    rw [List.replicate_succ, locate]
    by_cases hk : k < start + 1
    · rw [ite_eq_left_iff.mpr (fun h => absurd hk h)]
      congr 1 <;> omega
    · rw [ite_eq_right hk]
      rw [ih (start + 1) (by omega) (by omega)]
      simp only [Prod.mk.injEq, and_true]
      omega

theorem catOp_first {α : Type} [Zero α] {ts : List (Tensor α)} {r : Tensor α} {rest : List ℕ}
    (hs : ∀ t ∈ ts, t.shape = 1 :: rest) (hne : ts ≠ []) (h : catOp ts 0 = some r) :
    r.shape = ts.length :: rest ∧ r.data.size = ts.length * shapeSize rest ∧
      ∀ p < ts.length, ∀ q < shapeSize rest,
        r.get (p * shapeSize rest + q) = (ts.getD p ⟨[], #[]⟩).get q := by
  unfold catOp at h
  split_ifs at h with hw
  obtain ⟨t0, ts', rfl⟩ := List.exists_cons_of_ne_nil hne
  have h0 : t0.shape = 1 :: rest := hs t0 List.mem_cons_self
  have hshapes : (t0 :: ts').map (·.shape) = List.replicate (ts'.length + 1) (1 :: rest) := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_replicate]
    exact hs _ (List.getElem_mem _)
  have hcs : catShape ((t0 :: ts').map (·.shape)) 0 =
      some (0, List.replicate (ts'.length + 1) 1, (ts'.length + 1) :: rest) := by
    rw [hshapes, List.replicate_succ]
    have hnd : normDim 0 (1 :: rest).length = some 0 := by simp [normDim]
    simp only [catShape, hnd, List.all_cons, beq_self_eq_true, Bool.and_self,
      List.all_replicate, ite_self, ↓reduceIte, List.map_cons, List.map_replicate,
      List.getD_cons_zero, Option.some.injEq, Prod.mk.injEq, true_and]
    constructor
    · rfl
    · simp [List.set, List.sum_replicate]
      omega
  rw [hcs] at h
  simp only [Option.some.injEq] at h
  subst h
  refine ⟨by simp, by rw [Tensor.ofFn_data_size, shapeSize_cons]; simp, fun p hp q hq => ?_⟩
  have hp' : p < ts'.length + 1 := by simpa using hp
  rw [Tensor.ofFn_get _ _ (by rw [shapeSize_cons]; exact lt_mul_of_row hp' hq),
    unravel_cons hq hp']
  simp only [List.getD_cons_zero]
  rw [locate_ones _ _ _ (Nat.zero_le _) (by omega)]
  simp only [Nat.sub_zero, Nat.sub_self, List.set_cons_zero]
  have hmem : (t0 :: ts').getD p ⟨[], #[]⟩ ∈ t0 :: ts' := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp, Option.getD_some]
    exact List.getElem_mem hp
  rw [entry_cons (hs _ hmem), ravel_unravel_of_lt hq]
  simp


/-! ## Sums over a dimension of the rows -/

theorem strides_getD : ∀ (s : List ℕ) {e : ℕ}, e < s.length →
    (strides s).getD e 0 = shapeSize (s.drop (e + 1))
  | [], _, he => by simp at he
  | x :: s, 0, _ => by simp [strides]
  | x :: s, e + 1, he => by simpa [strides] using strides_getD s (e := e) (by simpa using he)

/-- A sum over dimension `pre.length + e` of a tensor of shape
    `pre ++ rest`: entry `i * S' + q'` of the result sums the entries
    `i * S + q_k` (`S`, `S'` the sizes of `rest` and of `rest` without its
    dimension `e`). -/
theorem sumOp_rows {α : Type} [Zero α] [Add α] {dim : ℤ} {T r : Tensor α} {pre rest : List ℕ}
    {e : ℕ} (hs : T.shape = pre ++ rest) (he : e < rest.length)
    (hd : normDim dim T.shape.length = some (pre.length + e)) (h : sumOp dim T = some r) :
    r.shape = pre ++ rest.eraseIdx e ∧
      ∀ i < shapeSize pre, ∀ q' < shapeSize (rest.eraseIdx e),
        r.get (i * shapeSize (rest.eraseIdx e) + q') =
          ((List.range (rest.getD e 0)).map fun k =>
            T.get (i * shapeSize rest + ((q' / shapeSize (rest.drop (e + 1)) * rest.getD e 0 + k) *
              shapeSize (rest.drop (e + 1)) + q' % shapeSize (rest.drop (e + 1))))).sum := by
  obtain ⟨d, hd', hsize, rfl⟩ := sumOp_spec h
  rw [hd] at hd'
  simp only [Option.some.injEq] at hd'
  subst hd'
  have htake : T.shape.take (pre.length + e) = pre ++ rest.take e := by
    rw [hs, List.take_append, List.take_of_length_le (by omega)]
    congr 2
    omega
  have hget : T.shape.getD (pre.length + e) 0 = rest.getD e 0 := by
    rw [hs, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega)]
    congr 2
    omega
  have hdrop : T.shape.drop (pre.length + e + 1) = rest.drop (e + 1) := by
    rw [hs, List.drop_append, List.drop_of_length_le (by omega), List.nil_append]
    congr 1
    omega
  refine ⟨?_, fun i hi q' hq' => ?_⟩
  · rw [hs, List.eraseIdx_append_of_length_le (by omega), Nat.add_sub_cancel_left]
  · set A := shapeSize (rest.take e)
    set n := rest.getD e 0
    set inner := shapeSize (rest.drop (e + 1))
    have hS' : shapeSize (rest.eraseIdx e) = A * inner := (shapeSize_eraseIdx_mul rest e).symm
    have hS : shapeSize rest = A * (n * inner) := by
      rw [shapeSize_split rest he, strides_getD rest he]
    have hinner : 0 < inner := by
      rcases Nat.eq_zero_or_pos inner with h0 | h0
      · rw [hS', h0, Nat.mul_zero] at hq'
        omega
      · exact h0
    have hj : i * (A * inner) + q' < shapeSize (pre ++ rest.take e) * inner := by
      rw [shapeSize_append]
      calc i * (A * inner) + q' < (i + 1) * (A * inner) := by rw [hS'] at hq'; nlinarith
        _ ≤ shapeSize pre * (A * inner) := Nat.mul_le_mul_right _ hi
        _ = shapeSize pre * A * inner := by ring
    rw [hS']
    unfold sumData
    rw [htake, hget, hdrop, Tensor.get_mk_map_range _ _ _ hj]
    -- the outer index and the inner index of `i * S' + q'`
    have hdiv : (i * (A * inner) + q') / inner = i * A + q' / inner := by
      rw [show i * (A * inner) + q' = q' + inner * (i * A) by ring, Nat.add_mul_div_left _ _ hinner]
      ring
    have hmod : (i * (A * inner) + q') % inner = q' % inner := by
      rw [show i * (A * inner) + q' = q' + inner * (i * A) by ring, Nat.add_mul_mod_self_left]
    rw [hdiv, hmod, hS]
    congr 1
    apply List.map_congr_left
    intro k _
    congr 1
    ring

/-! ## Matrix products of rows -/

theorem matmulShape_two (m k n : ℕ) :
    matmulShape [m, k] [k, n] = some ⟨[m, k], [k, n], m, k, n, [], [], [], [m, n]⟩ := by
  simp [matmulShape, padRow, padCol, keepDim, broadcastShape]

/-- A product of matrices. -/
theorem matmulOp_two {α : Type} [Zero α] [One α] [Add α] [Mul α] {a b : Tensor α} {m k n : ℕ}
    (ha : a.shape = [m, k]) (hb : b.shape = [k, n]) (hwa : a.wellFormed = true)
    (hwb : b.wellFormed = true) :
    ∃ r, matmulOp a b = some r ∧ r.shape = [m, n] ∧ r.data.size = m * n ∧
      ∀ i < m, ∀ c < n, r.get (i * n + c) =
        ((List.range k).map fun t => a.get (i * k + t) * b.get (t * n + c)).sum := by
  unfold matmulOp
  simp only [hwa, hwb, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte, ha, hb,
    matmulShape_two, Option.map_some]
  refine ⟨_, rfl, rfl, by simp [Tensor.ofFn_data_size, shapeSize], fun i hi c hc => ?_⟩
  have hc' : c < shapeSize [n] := by simpa [shapeSize] using hc
  have hsz : shapeSize [n] = n := by simp [shapeSize]
  have hj : i * n + c < shapeSize ([] ++ [m, n]) := by
    simp only [List.nil_append, shapeSize_cons, shapeSize_nil, Nat.mul_one]
    exact lt_mul_of_row hi hc
  rw [Tensor.get_mk_ofFn _ _ _ hj]
  simp only [List.nil_append]
  have hu : unravel [m, n] (i * n + c) = [i, c] := by
    have := unravel_cons (n := m) (rest := [n]) (j := i) (q := c) hc' hi
    rw [hsz] at this
    rw [this]
    simp [unravel, strides, shapeSize, Nat.mod_eq_of_lt hc]
  rw [hu]
  simp only [List.length_nil, List.take_zero, broadcastIndex, List.zipWith_nil_left,
    List.nil_append, List.getD_cons_zero, List.getD_cons_succ, Tensor.entry]
  congr 1
  apply List.map_congr_left
  intro t _
  rw [ravel_cons, ravel_cons]
  simp [ravel, strides, shapeSize, Tensor.get, Nat.mul_comm n t]

/-- A product of a value of shape `[1, m, k]` with a matrix. -/
theorem matmulOp_three {α : Type} [Zero α] [One α] [Add α] [Mul α] {a b : Tensor α}
    {m k n : ℕ} (ha : a.shape = [1, m, k]) (hb : b.shape = [k, n]) (hwa : a.wellFormed = true)
    (hwb : b.wellFormed = true) :
    ∃ r, matmulOp a b = some r ∧ r.shape = [1, m, n] ∧ r.data.size = m * n ∧
      ∀ i < m, ∀ c < n, r.get (i * n + c) =
        ((List.range k).map fun t => a.get (i * k + t) * b.get (t * n + c)).sum := by
  unfold matmulOp
  simp only [hwa, hwb, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte, ha, hb,
    matmulShape_lookup, Option.map_some]
  refine ⟨_, rfl, rfl, by simp [Tensor.ofFn_data_size, shapeSize], fun i hi c hc => ?_⟩
  have hc' : c < shapeSize [n] := by simpa [shapeSize] using hc
  have hsz : shapeSize [n] = n := by simp [shapeSize]
  have hj : i * n + c < shapeSize ([1] ++ [m, n]) := by
    simp only [List.cons_append, List.nil_append, shapeSize_cons, shapeSize_nil, Nat.mul_one,
      Nat.one_mul]
    exact lt_mul_of_row hi hc
  rw [Tensor.get_mk_ofFn _ _ _ hj]
  simp only [List.cons_append, List.nil_append]
  have hu : unravel [1, m, n] (i * n + c) = [0, i, c] := by
    have := unravel_three_cons (P := m) (rest := [n]) (p := i) (q := c) hi hc'
    rw [hsz] at this
    rw [this]
    simp [unravel, strides, shapeSize, Nat.mod_eq_of_lt hc]
  rw [hu]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, List.take_succ_cons,
    List.take_zero, broadcastIndex, List.zipWith_cons_cons, ↓reduceIte,
    List.drop_succ_cons, List.drop_zero, List.nil_append, List.singleton_append,
    List.getD_cons_zero, List.getD_cons_succ, Tensor.entry, Nat.sub_self, Nat.sub_zero,
    List.drop_nil, List.zipWith_nil_right]
  congr 1
  apply List.map_congr_left
  intro t _
  simp [ravel, strides, shapeSize, Tensor.get]
  ring_nf

theorem unsqueezeOp_zero {α : Type} {T r : Tensor α} (h : unsqueezeOp T 0 = some r) :
    r.shape = 1 :: T.shape ∧ r.data = T.data := by
  unfold unsqueezeOp at h
  have hnd : normDim 0 (T.shape.length + 1) = some 0 := by simp [normDim]
  rw [hnd] at h
  simp only [Option.map_some, Option.some.injEq] at h
  subst h
  simp

end CompactCheck
