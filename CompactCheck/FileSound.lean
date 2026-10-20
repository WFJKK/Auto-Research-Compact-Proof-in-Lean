import CompactCheck.Json
import CompactCheck.TokensLeafSound

/-!
# Soundness of the checker on proof files

`checkProofFile_sound`: if the checker certifies `n` inputs for a network
file and a proof file, the network answers at least `n` inputs correctly.
`checkProofFile` checks a network the Python checker treats as linear with
`checkProof`, and any other network with `checkProofGeneral`; both are
sound (`check_sound` in `Soundness.lean`, `checkGeneral_sound` in
`TokensLeafSound.lean`).
-/

namespace CompactCheck

theorem except_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- **Soundness of the checker**: for every network file and every proof
    file, if the checker certifies `n` inputs, the network answers at least
    `n` inputs correctly. -/
theorem checkProofFile_sound (net : NetworkFile) (j : Lean.Json) (n : ℕ)
    (h : checkProofFile net j = .ok n) : n ≤ numCorrect net.graph net.weights net.task := by
  unfold checkProofFile at h
  dsimp only at h
  split at h
  · obtain ⟨_, h1, _⟩ := except_bind_ok h
    cases h1
  · obtain ⟨proof, -, h2⟩ := except_bind_ok h
    split at h2
    · split at h2
      · exact checkGeneral_sound _ _ _ _ _ h2
      · exact check_sound _ _ _ _ _ h2
    · obtain ⟨_, h3, _⟩ := except_bind_ok h2
      cases h3

end CompactCheck
