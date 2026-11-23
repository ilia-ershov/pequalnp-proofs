import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_184

open PEqualNP.MetaComplexity

-- The seven inputs have binary masks 1, 3, 5, 9, 10, 12 and 14.
-- Each column records the values of one literal on these inputs.
private def column : Fin 4 → BitVec 7 := ![15, 82, 100, 120]

private def sample (j : ℕ) (i : Fin 4) : Bool := (column i).getLsbD j

private def signature : DMFormula 4 → BitVec 7
  | .lit i pos => if pos then column i else ~~~(column i)
  | .and f g => signature f &&& signature g
  | .or f g => signature f ||| signature g

private theorem signature_spec (f : DMFormula 4) (j : ℕ) (hj : j < 7) :
    (signature f).getLsbD j = f.eval (sample j) := by
  induction f with
  | lit i pos => cases pos <;> simp [signature, sample, DMFormula.eval, hj]
  | and f g hf hg => simp [signature, DMFormula.eval, hf, hg]
  | or f g hf hg => simp [signature, DMFormula.eval, hf, hg]

-- Weights are minimum leaf counts on the sample, capped at six.
-- Only the two inequalities and the literal weights are used in the lower bound.
private def weight (v : BitVec 7) : ℕ :=
  (11873388847390224743746691611879063514932850170237666229799923792468149574629341835089682644705567414729711454856346 >>> (3 * v.toNat)) % 8

-- Check each block of eight rows separately to bound the kernel's working memory.
private def checkRow (a b : BitVec 7) : Bool :=
  decide (weight (a &&& b) ≤ weight a + weight b ∧ weight (a ||| b) ≤ weight a + weight b)

private def block (k : ℕ) : Bool :=
  (List.range 8).all fun r => (List.range 128).all fun b =>
    checkRow (BitVec.ofNat 7 (8 * k + r)) (BitVec.ofNat 7 b)

private theorem checked (k : Fin 16) : block k.val = true := by
  fin_cases k <;> decide +kernel

private theorem gate_bounds (a b : BitVec 7) :
    weight (a &&& b) ≤ weight a + weight b ∧ weight (a ||| b) ≤ weight a + weight b := by
  have ha : a.toNat < 128 := a.isLt
  have hb : b.toNat < 128 := b.isLt
  have h := checked ⟨a.toNat / 8, by omega⟩
  simp only [block, List.all_eq_true, List.mem_range] at h
  have e := h (a.toNat % 8) (by omega) b.toNat hb
  rw [show 8 * (a.toNat / 8) + a.toNat % 8 = a.toNat by omega] at e
  simpa [checkRow] using e

private theorem literal_bound : ∀ (i : Fin 4) (pos : Bool),
    weight (if pos then column i else ~~~(column i)) ≤ 1 := by decide

private theorem leaf_bound (f : DMFormula 4) : weight (signature f) ≤ f.leaves := by
  induction f with
  | lit i pos => exact literal_bound i pos
  | and f g hf hg => exact (gate_bounds _ _).1.trans (Nat.add_le_add hf hg)
  | or f g hf hg => exact (gate_bounds _ _).2.trans (Nat.add_le_add hf hg)

private def target (x : Fin 4 → Bool) :=
  (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 0 && x 3)

private theorem target_bits : ∀ j : Fin 7, target (sample j.val) = (78 : BitVec 7).getLsbD j := by
  decide

private def witness : DMFormula 4 :=
  .or (.and (.lit 0 true) (.or (.lit 1 true) (.or (.lit 2 true) (.lit 3 true))))
    (.and (.lit 1 true) (.lit 2 true))

private theorem solution (s : ℕ) : HasLeafSize 4 target s ↔ 6 ≤ s := by
  constructor
  · rintro ⟨f, hs, h⟩
    have he : signature f = 78 := by
      apply BitVec.eq_of_getLsbD_eq
      intro j hj
      rw [signature_spec f j hj, h]
      exact target_bits ⟨j,hj⟩
    have hb := leaf_bound f
    rw [he, show weight 78 = 6 by decide] at hb
    exact hb.trans hs
  · intro hs
    exact ⟨witness, hs, by decide⟩

end PEqualNP.Outside.L_meta_184

theorem PEqualNP.Outside.L_meta_184 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasLeafSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 0 && x 3)) s ↔ 6 ≤ s :=
  PEqualNP.Outside.L_meta_184.solution
