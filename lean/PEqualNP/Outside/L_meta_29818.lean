import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29818

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_snoc (x : List Bool) (a : Bool) (n : ℕ) (h : n < x.length) :
    (x ++ [a]).getD n false = x.getD n false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_ge (x y : List Bool) (a : Bool) (n : ℕ) (hlen : x.length = y.length)
    (h : x.length ≤ n) : (x ++ [a]).getD n false = (y ++ [a]).getD n false := by
  have h' : y.length ≤ n := hlen ▸ h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h, List.getElem?_append_right h', hlen]

theorem agree (v : ℕ) (hv : v ≠ 0) (gs : List Gate)
    (hg : ∀ g ∈ gs, 0 ∈ g.inputs → g.op = GateOp.or ∧ v ∈ g.inputs) :
    ∀ x y : List Bool, x.length = y.length → 0 < x.length →
      (∀ n, n ≠ 0 → x.getD n false = y.getD n false) → x.getD v false = true →
      (∀ n, n ≠ 0 → (gs.foldl step x).getD n false = (gs.foldl step y).getD n false) ∧
        (gs.foldl step x).getD 0 false = x.getD 0 false := by
  induction gs with
  | nil =>
    intro x y _ _ h _
    exact ⟨h, rfl⟩
  | cons g gs ih =>
    intro x y hlen hpos h hxv
    have hvlt : v < x.length := by
      by_contra hc
      rw [List.getD_eq_default _ _ (by omega)] at hxv
      cases hxv
    have hval : g.op.eval (g.inputs.map fun i => x.getD i false) =
        g.op.eval (g.inputs.map fun i => y.getD i false) := by
      by_cases h0 : 0 ∈ g.inputs
      · obtain ⟨hop, hvin⟩ := hg g (by simp) h0
        have hyv : y.getD v false = true := by
          rw [← h v hv]
          exact hxv
        have ex : GateOp.or.eval (g.inputs.map fun i => x.getD i false) = true := by
          show (g.inputs.map fun i => x.getD i false).any id = true
          rw [List.any_eq_true]
          exact ⟨true, List.mem_map.2 ⟨v, hvin, hxv⟩, rfl⟩
        have ey : GateOp.or.eval (g.inputs.map fun i => y.getD i false) = true := by
          show (g.inputs.map fun i => y.getD i false).any id = true
          rw [List.any_eq_true]
          exact ⟨true, List.mem_map.2 ⟨v, hvin, hyv⟩, rfl⟩
        rw [hop, ex, ey]
      · congr 1
        apply List.map_congr_left
        intro i hi
        exact h i (fun hi0 => h0 (hi0 ▸ hi))
    have hstep : ∀ n, n ≠ 0 → (step x g).getD n false = (step y g).getD n false := by
      intro n hn
      unfold step
      rw [hval]
      by_cases hlt : n < x.length
      · rw [getD_snoc x _ n hlt, getD_snoc y _ n (hlen ▸ hlt)]
        exact h n hn
      · exact getD_snoc_ge x y _ n hlen (by omega)
    have hxv' : (step x g).getD v false = true := by
      unfold step
      rw [getD_snoc x _ v hvlt]
      exact hxv
    have key := ih (fun g' hg' => hg g' (by simp [hg'])) (step x g) (step y g)
      (by simp [step, hlen]) (by simp [step]) hstep hxv'
    refine ⟨key.1, ?_⟩
    have h0 : (step x g).getD 0 false = x.getD 0 false := by
      unfold step
      exact getD_snoc x _ 0 hpos
    exact key.2.trans h0

def xa : Fin 7 → Bool := fun i => decide (i = 1 ∨ i = 4)

def xb : Fin 7 → Bool := fun i => decide (i = 0 ∨ i = 1 ∨ i = 4)

def xc : Fin 7 → Bool := fun i => decide (i = 0 ∨ i = 4)

theorem offZero : ∀ n : ℕ, n ≠ 0 → (List.ofFn xa).getD n false = (List.ofFn xb).getD n false := by
  intro n hn
  by_cases h7 : n < 7
  · interval_cases n
    · exact absurd rfl hn
    all_goals decide
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

end PEqualNP.Outside.L_meta_29818

theorem PEqualNP.Outside.L_meta_29818 : (¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), i.val = 3 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧ 0 ∈ (C.gates.get i).inputs ∧ (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧ 4 ∈ (C.gates.get i).inputs ∧ 4 ≠ 0 ∧ 4 < 7 + i.val ∧ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ (C.wires (List.ofFn x)).getD 4 false = true)) := by
  rintro ⟨C, i, k, _, _, _, hcomp, h0, honly, hor, _, _, _, hw, _, _, _⟩
  have hg : ∀ g ∈ C.gates, 0 ∈ g.inputs →
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 4 ∈ g.inputs := by
    intro g hgm hg0
    obtain ⟨j, rfl⟩ := List.mem_iff_get.1 hgm
    have hj := honly j hg0
    subst hj
    exact ⟨hor, hw⟩
  have hab := PEqualNP.Outside.L_meta_29818.agree 4 (by decide) C.gates hg
    (List.ofFn PEqualNP.Outside.L_meta_29818.xa) (List.ofFn PEqualNP.Outside.L_meta_29818.xb)
    (by simp) (by simp) PEqualNP.Outside.L_meta_29818.offZero (by decide)
  have hcc := PEqualNP.Outside.L_meta_29818.agree 4 (by decide) C.gates hg
    (List.ofFn PEqualNP.Outside.L_meta_29818.xc) (List.ofFn PEqualNP.Outside.L_meta_29818.xc)
    rfl (by simp) (fun _ _ => rfl) (by decide)
  by_cases ho : C.output = 0
  · have e := hcomp PEqualNP.Outside.L_meta_29818.xc
    change (C.gates.foldl PEqualNP.Outside.L_meta_29818.step (List.ofFn PEqualNP.Outside.L_meta_29818.xc)).getD
      C.output false = _ at e
    rw [ho, hcc.2] at e
    revert e
    decide
  · have ea := hcomp PEqualNP.Outside.L_meta_29818.xa
    have eb := hcomp PEqualNP.Outside.L_meta_29818.xb
    change (C.gates.foldl PEqualNP.Outside.L_meta_29818.step (List.ofFn PEqualNP.Outside.L_meta_29818.xa)).getD
      C.output false = _ at ea
    change (C.gates.foldl PEqualNP.Outside.L_meta_29818.step (List.ofFn PEqualNP.Outside.L_meta_29818.xb)).getD
      C.output false = _ at eb
    rw [hab.1 C.output ho, eb] at ea
    revert ea
    decide
