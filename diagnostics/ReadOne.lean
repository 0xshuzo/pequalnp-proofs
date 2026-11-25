import PEqualNP.Outside.L_meta_2237
import PEqualNP.Outside.L_meta_3771
import PEqualNP.Outside.L_meta_2880
import Mathlib
import PEqualNP.Defs

namespace Plane2583

lemma pencil_le (N q : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (hq : 1 ≤ q)
    (hN : N = q ^ 2 + q + 1)
    (hL : ∀ (x8 : Fin N), Fintype.card { x9 : Fin N // I x9 x8 } = q + 1)
    (hU : ∀ (x9 x10 : Fin N), x9 ≠ x10 → ∃! x12 : Fin N, I x9 x12 ∧ I x10 x12)
    (p : Fin N) (Lp : Finset (Fin N)) (hLp : ∀ l ∈ Lp, I p l) : Lp.card ≤ q + 1 := by
  have hT : ∀ l ∈ Lp, ((Finset.univ.filter (fun r => I r l)).erase p).card = q := by
    intro l hl
    have hpl : I p l := hLp l hl
    rw [Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ p, hpl⟩)]
    have h1 : (Finset.univ.filter (fun r => I r l)).card = q + 1 := by
      rw [← hL l]
      exact (Fintype.card_of_subtype _ (fun x => by simp)).symm
    omega
  have hdisj : ∀ l ∈ Lp, ∀ l' ∈ Lp, l ≠ l' →
      Disjoint ((Finset.univ.filter (fun r => I r l)).erase p)
        ((Finset.univ.filter (fun r => I r l')).erase p) := by
    intro l hl l' hl' hne
    rw [Finset.disjoint_left]
    intro r hr hr'
    rw [Finset.mem_erase, Finset.mem_filter] at hr hr'
    obtain ⟨m, _, hm⟩ := hU p r (fun e => hr.1 e.symm)
    have e1 := hm l ⟨hLp l hl, hr.2.2⟩
    have e2 := hm l' ⟨hLp l' hl', hr'.2.2⟩
    exact hne (e1.trans e2.symm)
  have hcard : (Lp.biUnion (fun l => (Finset.univ.filter (fun r => I r l)).erase p)).card
      = Lp.card * q := by
    rw [Finset.card_biUnion hdisj, Finset.sum_const_nat hT]
  have hsub : Lp.biUnion (fun l => (Finset.univ.filter (fun r => I r l)).erase p)
      ⊆ Finset.univ.erase p := by
    intro r hr
    rw [Finset.mem_biUnion] at hr
    obtain ⟨l, _, hr⟩ := hr
    rw [Finset.mem_erase] at hr ⊢
    exact ⟨hr.1, Finset.mem_univ r⟩
  have h1 := Finset.card_le_card hsub
  rw [hcard, Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ,
    Fintype.card_fin] at h1
  have h3 : N - 1 = (q + 1) * q := by
    rw [hN]
    have h4 : q ^ 2 + q + 1 - 1 = q ^ 2 + q := by omega
    rw [h4]; ring
  rw [h3] at h1
  exact Nat.le_of_mul_le_mul_right h1 hq

theorem cover_size {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hL : ∀ l, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hU : ∀ p p', p ≠ p' → ∃! l, I p l ∧ I p' l)
    (P L : Finset (Fin N)) (hcov : ∀ p l, I p l → p ∈ P ∨ l ∈ L) :
    N ≤ P.card + L.card := by
  have hL' (l : Fin N) : Fintype.card {p : Fin N // I p l} = q + 1 := by
    rw [← hL l]
    exact Fintype.card_of_subtype _ (fun x => by simp)
  have hbound (p : Fin N) : (Lᶜ.filter (fun l => I p l)).card ≤ q + 1 := by
    apply pencil_le N q I (by omega) hN hL' hU p
    exact fun l hl => (Finset.mem_filter.mp hl).2
  have hfull (l : Fin N) (hl : l ∈ Lᶜ) : (P.filter (fun p => I p l)).card = q + 1 := by
    rw [← hL l]
    apply congrArg Finset.card
    ext p
    simp only [ Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨And.right, fun hi => ⟨(hcov p l hi).resolve_right (Finset.mem_compl.mp hl), hi⟩⟩
  have hcompare : Lᶜ.card * (q + 1) ≤ P.card * (q + 1) := by
    calc Lᶜ.card * (q + 1)
        = ∑ l ∈ Lᶜ, (P.filter (fun p => I p l)).card := (Finset.sum_const_nat hfull).symm
      _ = ∑ p ∈ P, (Lᶜ.filter (fun l => I p l)).card := by
        simp only [Finset.card_filter]
        rw [Finset.sum_comm]
      _ ≤ ∑ _p ∈ P, (q + 1) := Finset.sum_le_sum (fun p _ => hbound p)
      _ = P.card * (q + 1) := by simp
  have hle : Lᶜ.card ≤ P.card := Nat.le_of_mul_le_mul_right hcompare (by omega)
  have htotal : Lᶜ.card + L.card = N := by simp
  omega


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.TopForm PEqualNP.ReadK

variable {N : ℕ} (I : Fin N → Fin N → Prop)

def adjacent : Fin (N+N) → Fin (N+N) → Prop :=
  Fin.addCases (fun p => Fin.addCases (fun _ => False) (fun l => I p l))
    (fun l => Fin.addCases (fun p => I p l) (fun _ => False))

def planeGraph : SimpleGraph (Fin (N+N)) where
  Adj := adjacent I
  symm := ⟨by
    intro a b h
    induction a using Fin.addCases <;> induction b using Fin.addCases <;>
      simpa only [adjacent, Fin.addCases_left, Fin.addCases_right] using h⟩
  loopless := ⟨by
    intro a
    induction a using Fin.addCases <;> simp only [adjacent, Fin.addCases_left, Fin.addCases_right, not_false_eq_true]⟩

theorem plane_four_cycle_free (hU : ∀ p p', p ≠ p' → ∃! l, I p l ∧ I p' l) :
    @NoFourCycle _ (planeGraph I) (Classical.decRel _) := by
  classical
  have quad (p r l m : Fin N) (a : I p l) (b : I p m)
      (c : I r l) (d : I r m) : p = r ∨ l = m := by
    by_cases e : p = r
    · exact Or.inl e
    · obtain ⟨_, _, hh⟩ := hU p r e
      exact Or.inr ((hh l ⟨a,c⟩).trans (hh m ⟨b,d⟩).symm)
  intro a b hab
  apply Finset.card_le_one.mpr
  intro u hu v hv
  replace hu := (Finset.mem_filter.mp hu).2
  replace hv := (Finset.mem_filter.mp hv).2
  change adjacent I a u ∧ adjacent I b u at hu
  change adjacent I a v ∧ adjacent I b v at hv
  induction a using Fin.addCases <;> induction b using Fin.addCases <;>
    induction u using Fin.addCases <;> induction v using Fin.addCases <;>
    simp_all only [adjacent, Fin.addCases_left, Fin.addCases_right, false_and, and_false, Fin.castAdd_inj, Fin.natAdd_inj] <;> grind

theorem edge_function (x : Fin (N+N) → Bool) :
    (∃ u v, (planeGraph I).Adj u v ∧ x u = true ∧ x v = true) ↔
      ∃ p l, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true := by
  constructor
  · rintro ⟨u,v,he,hu,hv⟩
    change adjacent I u v at he
    induction u using Fin.addCases <;> induction v using Fin.addCases <;>
      simp only [adjacent, Fin.addCases_left, Fin.addCases_right] at he <;> exact ⟨_, _, he, by assumption, by assumption⟩
  · rintro ⟨p,l,he,hp,hl⟩
    exact ⟨Fin.castAdd N p, Fin.natAdd N l, by simpa only [planeGraph, adjacent, Fin.addCases_left, Fin.addCases_right] using he,hp,hl⟩

variable [DecidableRel I]
private noncomputable def allEdges : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun e => I e.1 e.2)

private lemma allEdges_card (q : ℕ)
    (hL : ∀ l, (Finset.univ.filter (fun p => I p l)).card = q + 1) :
    (allEdges I).card = N * (q + 1) := by
  classical
  let F (l : Fin N) : Finset (Fin N × Fin N) :=
    (Finset.univ.filter (fun p => I p l)).map ⟨fun p => (p, l), fun _ _ h => congrArg Prod.fst h⟩
  have hF (l : Fin N) (e : Fin N × Fin N) : e ∈ F l ↔ I e.1 l ∧ e.2 = l := by
    constructor
    · intro he
      obtain ⟨p, hp, ht⟩ := Finset.mem_map.mp he
      change (p, l) = e at ht
      rw [← ht]
      exact ⟨(Finset.mem_filter.mp hp).2, rfl⟩
    · rintro ⟨hi, hh⟩
      refine Finset.mem_map.mpr ⟨e.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, ?_⟩
      exact Prod.ext rfl hh.symm
  have heq : allEdges I = Finset.univ.biUnion F := by
    ext e
    simp only [allEdges, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, hF]
    exact ⟨fun h => ⟨e.2, h, rfl⟩, fun ⟨l, hi, he⟩ => he ▸ hi⟩
  rw [heq, Finset.card_biUnion]
  · simp [F, hL]
  · intro l _ l' _ hne
    refine Finset.disjoint_left.mpr ?_
    intro e he he'
    exact hne (((hF l e).mp he).2.symm.trans ((hF l' e).mp he').2)

theorem edge_count_lower (q : ℕ)
    (hL : ∀ l, (Finset.univ.filter (fun p => I p l)).card = q + 1) :
    letI := Classical.decRel (planeGraph I).Adj
    N * (q+1) ≤ (planeGraph I).edgeFinset.card := by
  classical
  rw [← allEdges_card I q hL]
  refine Finset.card_le_card_of_injOn
    (fun e : Fin N × Fin N => Sym2.mk (Fin.castAdd N e.1) (Fin.natAdd N e.2)) ?_ ?_
  · intro e he
    change Sym2.mk (Fin.castAdd N e.1) (Fin.natAdd N e.2) ∈ (planeGraph I).edgeFinset
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    simpa only [planeGraph, adjacent, Fin.addCases_left, Fin.addCases_right] using (Finset.mem_filter.mp he).2
  · intro e _ f _ he
    rcases Sym2.eq_iff.mp he with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exact Prod.ext (by simpa only [Fin.castAdd_inj] using h1)
        (by simpa only [Fin.natAdd_inj] using h2)
    · have h := congrArg Fin.val h1
      change e.1.val = N + f.2.val at h
      have he0 := e.1.isLt
      omega

theorem joined_cover {q : ℕ} (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hL : ∀ l, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hU : ∀ p p', p ≠ p' → ∃! l, I p l ∧ I p' l)
    (T : Finset (Fin (N+N))) (hcov : ∀ a b, (planeGraph I).Adj a b → a ∈ T ∨ b ∈ T) :
    N ≤ T.card := by
  classical
  let P := Finset.univ.filter (fun p : Fin N => Fin.castAdd N p ∈ T)
  let L := Finset.univ.filter (fun l : Fin N => Fin.natAdd N l ∈ T)
  have hsub (p l : Fin N) (hi : I p l) : p ∈ P ∨ l ∈ L := by
    simpa [P, L] using hcov (Fin.castAdd N p) (Fin.natAdd N l)
      (by simpa only [planeGraph, adjacent, Fin.addCases_left, Fin.addCases_right] using hi)
  have hsize : P.card + L.card = T.card := by
    change (Finset.univ.filter _).card + (Finset.univ.filter _).card = T.card
    rw [Finset.card_filter, Finset.card_filter]
    calc _ = ∑ i : Fin (N+N), (if i ∈ T then 1 else 0) := by rw [Fin.sum_univ_add]
         _ = T.card := by simp [Finset.sum_boole]
  simpa only [hsize] using cover_size I hq hN hL hU P L hsub

theorem exact_read_one_lower (h2237 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → (∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → PEqualNP.ReadK.IsReadK n C 1 → ∃ T : Finset (Fin n), (∀ u2 v2 : Fin n, G.Adj u2 v2 → u2 ∈ T ∨ v2 ∈ T) ∧ G.edgeFinset.card + T.card ≤ C.size + 1)
    {q : ℕ} (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hL : ∀ l, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hU : ∀ p p', p ≠ p' → ∃! l, I p l ∧ I p' l)
    (C : Circuit) (hAO : IsAO2 (N+N) C)
    (hC : ∀ x, circuitFun (N+N) C x =
      decide (∃ p l, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true))
    (hR : IsReadK (N+N) C 1) : N*(q+2) ≤ C.size + 1 := by
  classical
  letI := Classical.decRel (planeGraph I).Adj
  have hgraph (x) : circuitFun (N+N) C x =
      decide (∃ u v, (planeGraph I).Adj u v ∧ x u = true ∧ x v = true) := by
    rw [hC]
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using (edge_function I x).symm
  obtain ⟨T,hT,hw⟩ := h2237 _ (planeGraph I) C (plane_four_cycle_free I hU) hAO hgraph hR
  have ht := joined_cover I hq hN hL hU T hT
  have he := edge_count_lower I q hL
  have hh := (Nat.add_le_add he ht).trans hw
  calc N * (q+2) = N*(q+1)+N := by ring
       _ ≤ C.size + 1 := hh

theorem requested_implies_lower (requested : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (N + N) D ∧ (∀ y : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D y = decide (∃ p l : Fin N, I p l ∧ y (Fin.castAdd N p) = true ∧ y (Fin.natAdd N l) = true)) ∧ D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (N + N) D 1)
    (h2237 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → (∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → PEqualNP.ReadK.IsReadK n C 1 → ∃ T : Finset (Fin n), (∀ u2 v2 : Fin n, G.Adj u2 v2 → u2 ∈ T ∨ v2 ∈ T) ∧ G.edgeFinset.card + T.card ≤ C.size + 1)
    {q : ℕ} (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hL : ∀ l, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hU : ∀ p p', p ≠ p' → ∃! l, I p l ∧ I p' l)
    (C : Circuit) (hAO : IsAO2 (N+N) C)
    (hC : ∀ x, circuitFun (N+N) C x =
      decide (∃ p l, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true)) :
    N*(q+2) ≤ C.size + 1 := by
  obtain ⟨D, hDA, hDF, hS, hDR⟩ := requested q N I C hq hN hL hU hAO hC
  exact (exact_read_one_lower I h2237 hq hN hL hU D hDA hDF hDR).trans (by omega)

end Plane2583


namespace Tests3774

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership

abbrev I := Fin 13
abbrev V := Fin (13+13)
def D : Finset I := {0,1,3,9}
def incident (p l : I) : Prop := p+l ∈ D
instance (p l : I) : Decidable (incident p l) := inferInstanceAs (Decidable (p+l∈D))
def pts (x : V → Bool) : Finset I := Finset.univ.filter (fun i => x (i.castAdd 13) = true)
def lines (x : V → Bool) : Finset I := Finset.univ.filter (fun i => x (Fin.natAdd 13 i) = true)
def flag (x : V → Bool) := ∃ p l : I, incident p l ∧ x (p.castAdd 13)=true ∧ x (Fin.natAdd 13 l)=true

def upper (P : Finset I) : V → Bool := Fin.addCases (motive := fun _ => Bool)
  (fun p => decide (p ∈ P)) (fun l => decide (∀ p ∈ P, ¬incident p l))
def lower (L : Finset I) : V → Bool := Fin.addCases (motive := fun _ => Bool)
  (fun p => decide (∀ l ∈ L, ¬incident p l)) (fun l => decide (l ∈ L))

theorem exact (C : Circuit) (hm : Monotone2 C)
    (good : ∀ p l : I, incident p l → C.eval (List.ofFn (pairInput (p.castAdd 13) (Fin.natAdd 13 l)))=true)
    (bad : ∀ T : Finset I, T.card≤3 → C.eval (List.ofFn (upper T))=false ∧ C.eval (List.ofFn (lower T))=false) :
    ∀ x : V → Bool, C.eval (List.ofFn x)=true ↔ flag x := by
  intro x
  have pm (p : I) : p ∈ pts x ↔ x (p.castAdd 13) = true := by simp [pts]
  have lm (l : I) : l ∈ lines x ↔ x (Fin.natAdd 13 l) = true := by simp [lines]
  constructor
  · intro yes 
    by_contra absent
    have dis : ∀ p∈pts x, ∀ l∈lines x, ¬incident p l :=
      fun p hp l hl e => absent ⟨p,l,e,(pm p).mp hp,(lm l).mp hl⟩
    rcases PEqualNP.Outside.L_meta_3771 (pts x) (lines x) dis with small|small
    · have le : x ≤ upper (pts x) := by
        intro i
        induction i using Fin.addCases with
        | left p => apply Bool.le_iff_imp.mpr; intro hp; simpa [upper] using (pm p).mpr hp
        | right l =>
          apply Bool.le_iff_imp.mpr
          intro hl
          simpa [upper, Fin.addCases_right] using (fun p hp => dis p hp l ((lm l).mpr hl))
      have z := PEqualNP.Outside.L_meta_2880.cmono C hm 26 _ _ le yes
      rw [(bad _ small).1] at z
      contradiction
    · have le : x ≤ lower (lines x) := by
        intro i
        induction i using Fin.addCases with
        | left p =>
          apply Bool.le_iff_imp.mpr
          intro hp
          simpa [lower] using (fun l hl => dis p ((pm p).mpr hp) l hl)
        | right l => apply Bool.le_iff_imp.mpr; intro hl; simpa [lower,Fin.addCases_right] using (lm l).mpr hl
      have z := PEqualNP.Outside.L_meta_2880.cmono C hm 26 _ _ le yes
      rw [(bad _ small).2] at z
      contradiction
  · rintro ⟨p,l,hl,hp,hq⟩
    apply PEqualNP.Outside.L_meta_2880.cmono C hm 26 _ _ _ (good p l hl)
    intro i
    apply Bool.le_iff_imp.mpr
    intro hi
    rcases of_decide_eq_true hi with rfl|rfl
    · exact hp
    · exact hq

end Tests3774
namespace Pricing3774
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership
open Tests3774
theorem cost (C : Circuit) (mono : Monotone2 C) (ao : PEqualNP.TopForm.IsAO2 26 C)
    (read : PEqualNP.ReadK.IsReadK 26 C 1)
    (pos : ∀ p l, incident p l → C.eval (List.ofFn (pairInput (p.castAdd 13) (Fin.natAdd 13 l)))=true)
    (neg : ∀ T : Finset (Fin 13), T.card≤3 →
      C.eval (List.ofFn (upper T))=false ∧ C.eval (List.ofFn (lower T))=false) : 64≤C.size := by
  have rows := Tests3774.exact C mono pos neg
  have hL : ∀ l, (Finset.univ.filter (fun p => incident p l)).card = 3+1 := by decide +kernel
  have hU : ∀ p p', p≠p' → ∃! l, incident p l ∧ incident p' l := by decide +kernel
  have price := Plane2583.exact_read_one_lower incident PEqualNP.Outside.L_meta_2237
    (q:=3) (by decide) (by decide) hL hU C ao (fun x => Bool.eq_iff_iff.mpr
      (by simpa only [decide_eq_true_eq] using rows x)) read
  omega
end Pricing3774
