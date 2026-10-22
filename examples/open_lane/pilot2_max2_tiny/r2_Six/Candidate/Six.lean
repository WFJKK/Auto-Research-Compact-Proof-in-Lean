import Protected.N_max2_tiny_v8_s0_c6
import CompactCheck.Soundness
import CompactCheck.CountedOps

/-!
# 6 inputs of max2_tiny-v8-s0 from three single-input checks

Three `single`s on `[0, 1]`, `[2, 3]`, `[4, 5]` (63 operations each); each certifies its input and, since
the network sums its one-hot tokens before anything else and the label is symmetric, the swapped input too.
-/

namespace Candidate.Six

open CompactCheck Protected.N_max2_tiny_v8_s0_c6

def guardInputs (g : Nat × Nat) : List Input :=
  if g.1 = g.2 then [[g.1, g.2]] else [[g.1, g.2], [g.2, g.1]]

def countSingles (I : Interp) : List (Nat × Nat) → I.M I.N
  | [] => pure I.nzero
  | g :: gs => do
    let ok ← I.single graph task [g.1, g.2]
    let n ← countSingles I gs
    pure (I.nadd (I.nscale (guardInputs g).length ok) n)

def D : Checker := fun I => countSingles I [(0, 1), (2, 3), (4, 5)]

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

theorem Sem.single {env : Env} (g : Graph) (task : Task) (x : Input) :
    Sem (CostM.single g task x) env (fun b => b = true → singleOk g env.weights task x = true) :=
  fun c b c' hr hb => by
    subst hb
    exact CostM.single_spec hr

theorem correct_swap (w : Weights ℚ) (a b : Nat) (h : singleOk graph w task [a, b] = true) :
    Correct graph w task [b, a] :=
  singleOk_correct graph w task [b, a]
    (singleOk_perm (by decide) rfl (List.Perm.swap b a []) h)

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
theorem countSingles_le (env : Env) : ∀ (gs : List (Nat × Nat)),
    Sem (countSingles Interp.counting gs) env
      (fun n => n ≤ (gs.flatMap guardInputs).countP fun x => decide (Correct graph env.weights task x))
  | [] => by
    simp only [countSingles, Interp.counting_pure, List.flatMap_nil, List.countP_nil]
    exact Sem.pure (Nat.le_refl 0)
  | g :: gs => by
    simp only [countSingles, Interp.counting_bind, Interp.counting_pure, List.flatMap_cons,
      List.countP_append]
    refine Sem.bind (Sem.single _ _ _) fun G hG => ?_
    refine Sem.bind (countSingles_le env gs) fun n hn => ?_
    refine Sem.pure ?_
    exact Nat.add_le_add (guard_le env g G hG) hn

theorem D_sound : ∀ (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),
    CostM.exec (D Interp.counting) ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task := by
  intro w c n cost h
  have h1 := countSingles_le ⟨w, c⟩ [(0, 1), (2, 3), (4, 5)] [] n cost h
  have hsub : ([(0, 1), (2, 3), (4, 5)].flatMap guardInputs).Subperm (allInputs task.space) := by
    apply List.Nodup.subperm (by decide)
    intro x hx
    have : x ∈ allInputs [8, 8] := by
      revert x
      decide
    exact this
  unfold numCorrect
  exact le_trans h1 (hsub.countP_le _)

theorem D_instance : CostM.billed (D Interp.counting) ⟨weights, cert⟩ = some (6, 189) := by
  decide +kernel

theorem performance : Target := by
  show claimedCount ≤ numCorrect graph weights task
  obtain ⟨cost, h⟩ := CostM.exec_of_billed D_instance
  exact D_sound weights cert 6 cost h

end Candidate.Six
