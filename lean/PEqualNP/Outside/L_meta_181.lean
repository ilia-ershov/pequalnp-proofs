import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_181

open PEqualNP.MetaComplexity

-- The seven inputs have binary masks 1, 3, 5, 9, 10, 12 and 14.
-- Each column records the values of one literal on these inputs.
private def column : Fin 5 → BitVec 7 := ![15, 82, 100, 120, 0]

private def sample (j : ℕ) (i : Fin 5) : Bool := (column i).getLsbD j

private def signature : DMFormula 5 → BitVec 7
  | .lit i pos => if pos then column i else ~~~(column i)
  | .and f g => signature f &&& signature g
  | .or f g => signature f ||| signature g

private theorem signature_spec (f : DMFormula 5) (j : ℕ) (hj : j < 7) :
    (signature f).getLsbD j = f.eval (sample j) := by
  induction f with
  | lit i pos => cases pos <;> simp [signature, sample, DMFormula.eval, hj]
  | and f g hf hg => simp [signature, DMFormula.eval, hf, hg]
  | or f g hf hg => simp [signature, DMFormula.eval, hf, hg]

-- Give the two constant columns weight zero. All other weights count leaves
-- on the seven inputs up to a maximum of six.
-- Only the two inequalities and the literal weights are used in the lower bound.
private def weight (v : BitVec 7) : ℕ :=
  (2022887298291604940676931586843160063662915352621304562812850441406719131755039182236116080984338504528054457279640 >>> (3 * v.toNat)) % 8

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

-- These two extra inputs isolate the fifth variable.
private def leftInput : Fin 5 → Bool := ![false, true, false, false, false]
private def rightInput : Fin 5 → Bool := ![false, true, false, false, true]

private def distance (a b : Bool) : ℕ := if a = b then 0 else 1

private theorem distance_and (a b c d : Bool) :
    distance (a && c) (b && d) ≤ distance a b + distance c d := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

private theorem distance_or (a b c d : Bool) :
    distance (a || c) (b || d) ≤ distance a b + distance c d := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

private theorem literal_bound : ∀ (i : Fin 5) (pos : Bool),
    weight (signature (.lit i pos)) +
      distance ((DMFormula.lit i pos).eval leftInput) ((DMFormula.lit i pos).eval rightInput)
        ≤ 1 := by decide

private theorem leaf_bound (f : DMFormula 5) :
    weight (signature f) + distance (f.eval leftInput) (f.eval rightInput) ≤ f.leaves := by
  induction f with
  | lit i pos => exact literal_bound i pos
  | and f g hf hg =>
    have hw := (gate_bounds (signature f) (signature g)).1
    have hd := distance_and (f.eval leftInput) (f.eval rightInput) (g.eval leftInput) (g.eval rightInput)
    simp only [signature, DMFormula.eval, DMFormula.leaves]
    omega
  | or f g hf hg =>
    have hw := (gate_bounds (signature f) (signature g)).2
    have hd := distance_or (f.eval leftInput) (f.eval rightInput) (g.eval leftInput) (g.eval rightInput)
    simp only [signature, DMFormula.eval, DMFormula.leaves]
    omega

private def target (x : Fin 5 → Bool) :=
  (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 0 && x 3) || (x 1 && x 4)

private theorem target_bits : ∀ j : Fin 7, target (sample j.val) = (78 : BitVec 7).getLsbD j := by
  decide

private def witness : DMFormula 5 :=
  .or (.and (.lit 0 true) (.or (.lit 1 true) (.or (.lit 2 true) (.lit 3 true))))
    (.and (.lit 1 true) (.or (.lit 2 true) (.lit 4 true)))

private theorem solution (s : ℕ) : HasLeafSize 5 target s ↔ 7 ≤ s := by
  constructor
  · rintro ⟨f, hs, h⟩
    have he : signature f = 78 := by
      apply BitVec.eq_of_getLsbD_eq
      intro j hj
      rw [signature_spec f j hj, h]
      exact target_bits ⟨j,hj⟩
    have hb := leaf_bound f
    rw [he, show weight 78 = 6 by decide, h, h,
      show distance (target leftInput) (target rightInput) = 1 by decide] at hb
    exact hb.trans hs
  · intro hs
    exact ⟨witness, hs, by decide⟩

end PEqualNP.Outside.L_meta_181

theorem PEqualNP.Outside.L_meta_181 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasLeafSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 0 && x 3) || (x 1 && x 4)) s ↔ 7 ≤ s :=
  PEqualNP.Outside.L_meta_181.solution
