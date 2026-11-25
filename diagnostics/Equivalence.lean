import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_2237
import PEqualNP.Outside.L_meta_3243
import PEqualNP.Outside.L_meta_3245
import PEqualNP.Outside.L_meta_3756
import PEqualNP.Outside.L_meta_5242


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

namespace Plane2583
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.ReadK
open PEqualNP.Outside.L_meta_5242

theorem prime_of_pairs {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hF : circuitFun n C = graphFun G ∅)
    (pairs : ∀ u v, G.Adj u v → readsAtMost C n [u.val,v.val] 1=true) : IsReadK n C 1 := by
  intro S hp
  have ht := hp.1
  rw [hF] at ht
  simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,
    Bool.false_or,decide_eq_true_eq,setInput] at ht
  obtain ⟨u,v,uv,hu,hv⟩ := ht
  have hsub : ({u,v} : Finset (Fin n)) ⊆ S := by
    intro w hw
    rcases Finset.mem_insert.mp hw with h | h
    · simpa only [h] using hu
    · simpa only [Finset.mem_singleton.mp h] using hv
  have eq : ({u,v} : Finset (Fin n)) = S := by
    by_contra bad
    have negative := hp.2 {u,v} (Finset.mem_ssubsets.mpr (lt_of_le_of_ne hsub bad))
    rw [hF] at negative
    have positive : graphFun G ∅ (setInput {u,v})=true := by
      simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,
        Bool.false_or,decide_eq_true_eq,setInput]
      exact ⟨u,v,uv,by simp,by simp⟩
    rw [positive] at negative
    contradiction
  rw [← eq]
  rcases lt_or_gt_of_ne uv.ne with lt|gt
  · rw [PEqualNP.Outside.L_meta_2237.cor_setList_pair u v lt]
    exact pairs u v uv
  · rw [Finset.pair_comm,PEqualNP.Outside.L_meta_2237.cor_setList_pair v u gt]
    exact pairs v u uv.symm

theorem bank_read {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO : IsAO2 n C) (hF : circuitFun n C = graphFun G ∅)
    (B : Finset ℕ)
    (bank : ∀ w ∈ B, w<n ∨ ∃ j < C.gates.length, w=n+j ∧ (gateAt C j).op=GateOp.or ∧
      ∀ i ∈ (gateAt C j).inputs, i∈B)
    (pins : ∀ j<C.gates.length, (gateAt C j).op=GateOp.and → ∀ i∈(gateAt C j).inputs, i∈B) :
    IsReadK n C 1 := by
  apply prime_of_pairs G C hF
  intro u v uv
  have hout (x : Fin n → Bool) : Base.val C (List.ofFn x) C.output = graphFun G ∅ x := congrFun hF x
  obtain ⟨j,hj,notOr,path,on⟩ := Base.edge_trace G (graphFun G ∅)
    (fun a b => (Base.graphFun_pair G a b).mp) hout u v ((Base.graphFun_pair G u v).mpr uv)
  have hand := (hAO.1 _ (Base.gateAt_mem hj)).resolve_right notOr
  have reach := Base.reach_orReaches path j rfl hj
  have step {w z : ℕ} (e : Base.OrStep n C w z) (hw : w ∈ B) : z∈B := by
    obtain ⟨k,_,ew,_,hin,_⟩ := e
    rcases bank w hw with low|⟨t,_,et,_,prop⟩
    · omega
    · have kt : k=t := by omega
      exact prop z (kt ▸ hin)
  have closed {w z : ℕ} (r : Relation.ReflTransGen (Base.OrStep n C) w z) : w∈B → z∈B := by
    induction r with
    | refl => exact id
    | tail _ e ih => exact fun hw => step e (ih hw)
  have raw (b : Fin 2) : ∃ w : Fin n, (w=u ∨ w=v) ∧ w∈side C j b := by
    have val := (Structural.and_true_iff hAO hj hand (pairInput u v)).mp on b
    rcases Base.operand_trace (C := C) u v _ val with ⟨w,wv,r⟩|⟨k,_,no,r,_⟩
    · exact ⟨w,wv,Base.reach_mem_orIn w r⟩
    · have hB := closed r (pins j hj hand _ (Structural.opnd_mem hAO hj b))
      rcases bank _ hB with low|⟨t,_,et,op,_⟩
      · omega
      · have kt : k=t := by omega
        exact (no (kt ▸ op)).elim
  obtain ⟨w,hw,w0⟩ := raw 0
  obtain ⟨z,hz,z1⟩ := raw 1
  have wz : w ≠ z := by
    intro same
    have w1 : w∈side C j 1 := by simpa only [same] using z1
    have both : ∀ b : Fin 2, Base.val C (List.ofFn (pairInput w w)) (opnd C j b)=true :=
      Final.forall_two.mpr ⟨Final.raw_up _ w w0 (Base.pairInput_left w w),
        Final.raw_up _ w w1 (Base.pairInput_left w w)⟩
    have ho := Final.reach_up (pairInput w w) reach ((Structural.and_true_iff hAO hj hand _).mpr both)
    rw [hout] at ho
    exact G.irrefl ((Base.graphFun_pair G w w).mp ho)
  have hside : (u∈side C j 0 ∧ v∈side C j 1) ∨ (v∈side C j 0 ∧ u∈side C j 1) := by
    rcases hw with wu|wv <;> rcases hz with zu|zv
    · exact (wz (wu.trans zu.symm)).elim
    · exact Or.inl ⟨wu ▸ w0,zv ▸ z1⟩
    · exact Or.inr ⟨wv ▸ w0,zu ▸ z1⟩
    · exact (wz (wv.trans zv.symm)).elim
  have no := (PEqualNP.Outside.L_meta_3756.main n G C hAO hF u v uv).mpr ⟨j,hj,hand,reach,hside⟩
  have bound : n ≤ C.output := reach.1
  have hat : PEqualNP.Core.atGate n C (C.output-n) = C := by
    cases C with
    | mk gs o =>
      simp only [PEqualNP.Core.atGate]
      simp only at bound
      congr 1
      omega
  simpa only [PEqualNP.Core.ReadTwiceAt,hat,Bool.not_eq_false] using no

theorem star_upper {N q : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hL : ∀ l, (Finset.univ.filter (fun p => I p l)).card = q+1) :
    ∃ D : Circuit, IsAO2 (N+N) D ∧
      (∀ x, circuitFun (N+N) D x = decide (∃ p l, I p l ∧ x (Fin.castAdd N p)=true ∧ x (Fin.natAdd N l)=true)) ∧
      D.size = N*(q+2)-1 ∧ IsReadK (N+N) D 1 := by
  classical
  let pts (l : Fin N) := ((Finset.univ.filter (fun p => I p l)).toList.map Fin.val)
  let own := (List.finRange N).map (fun l => (N+l.val,pts l))
  have plen (l : Fin N) : (pts l).length=q+1 := by simp [pts,hL]
  have info (l : Fin N) (i : ℕ) : i∈pts l ↔ ∃ p, I p l ∧ p.val=i := by
    simp [pts]
  have legal : ∀ t∈own, t.2 ≠ [] ∧
      ((t.1<N ∧ ∀ x∈t.2, N≤x ∧ x<N+N) ∨ N≤t.1 ∧ t.1<N+N ∧ ∀ x∈t.2, x<N) := by
    intro t ht
    obtain ⟨l,_,rfl⟩ := List.mem_map.mp ht
    refine ⟨fun h => ?_, Or.inr ⟨by simp,by have := l.isLt; omega,?_⟩⟩
    · have hnil : pts l = [] := h
      have eq := plen l
      simp [hnil] at eq
    · intro x hx
      obtain ⟨p,_,rfl⟩ := (info _ _).mp hx
      exact p.isLt
  have edges (p l : Fin N) : I p l ↔ ∃ t ∈ own,
      (t.1=p.val ∧ N+l.val∈t.2) ∨ (t.1=N+l.val ∧ p.val∈t.2) := by
    constructor
    · intro h
      refine ⟨(N+l.val,pts l), List.mem_map.mpr ⟨l,by simp,rfl⟩,Or.inr ⟨rfl,?_⟩⟩
      exact (info _ _).mpr ⟨p,h,rfl⟩
    · rintro ⟨t,ht,h⟩
      obtain ⟨a,_,rfl⟩ := List.mem_map.mp ht
      rcases h with ⟨e,_⟩|⟨e,m⟩
      · change N+a.val=p.val at e
        have := p.isLt
        omega
      · change N+a.val=N+l.val at e
        obtain rfl : a=l := Fin.ext (by omega)
        obtain ⟨p',hi,ev⟩ := (info _ _).mp m
        exact (Fin.ext ev : p'=p) ▸ hi
  let D := coverCircuitB (N+N) own
  obtain ⟨ds,fn⟩ := PEqualNP.Outside.L_meta_3243 N N I own legal edges
  obtain ⟨P,L,ao,pp,ll,pins⟩ := PEqualNP.Outside.L_meta_3245 N N own legal
  have total : (own.map (fun t => t.2.length)).sum=N*(q+1) := by
    have lists : own.map (fun t => t.2.length) = (List.finRange N).map (fun _ => q+1) := by
      simp [own,List.map_map,Function.comp_def,plen]
    rw [lists]
    have uniform (xs : List (Fin N)) : (xs.map (fun _ => q+1)).sum = xs.length*(q+1) := by
      induction xs with
      | nil => simp
      | cons x xs ih => simp [ih,Nat.succ_mul,Nat.add_comm]
    simpa using uniform (List.finRange N)
  have len : own.length=N := by simp [own]
  refine ⟨D,ao,fn,?_,?_⟩
  · change (coverCircuitB (N+N) own).size=_
    rw [ds,total,len,show N*(q+2)=N*(q+1)+N by ring]
  · letI := Classical.decRel (planeGraph I).Adj
    have hF : circuitFun (N+N) D = graphFun (planeGraph I) ∅ := by
      funext x
      rw [fn]
      simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or]
      apply Bool.eq_iff_iff.mpr
      simpa only [decide_eq_true_eq] using (edge_function I x).symm
    apply bank_read (planeGraph I) D ao hF (P∪L)
    · intro w hw
      rcases Finset.mem_union.mp hw with hp|hl
      · rcases pp w hp with lo|⟨j,jr,e,ho,op⟩
        · exact Or.inl (by omega)
        · exact Or.inr ⟨j,jr,e,ho,fun i hi => Finset.mem_union_left _ (op i hi)⟩
      · rcases ll w hl with lo|⟨j,jr,e,ho,op⟩
        · exact Or.inl lo.2
        · exact Or.inr ⟨j,jr,e,ho,fun i hi => Finset.mem_union_right _ (op i hi)⟩
    · intro j hj ha i hi
      obtain ⟨a,b,eq,h⟩ := pins j hj ha
      rw [eq] at hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases h with ⟨ap,bl⟩|⟨al,bp⟩ <;> rcases hi with rfl|rfl
      · exact Finset.mem_union_left _ ap
      · exact Finset.mem_union_right _ bl
      · exact Finset.mem_union_right _ al
      · exact Finset.mem_union_left _ bp

/-- The original replacement conclusion whenever the input circuit reaches the star size. -/
theorem replacement_above {N q : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hL : ∀ l, (Finset.univ.filter (fun p => I p l)).card = q+1)
    (C : Circuit) (bound : N*(q+2) ≤ C.size+1) :
    ∃ D : Circuit, IsAO2 (N+N) D ∧
      (∀ x, circuitFun (N+N) D x = decide (∃ p l, I p l ∧ x (Fin.castAdd N p)=true ∧ x (Fin.natAdd N l)=true)) ∧
      D.size ≤ C.size ∧ IsReadK (N+N) D 1 := by
  obtain ⟨D,ao,fn,size,read⟩ := star_upper I hL
  exact ⟨D,ao,fn,by omega,read⟩

end Plane2583

namespace Plane2583
theorem equivalence :
    (∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (N + N) D ∧ (∀ y : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D y = decide (∃ p l : Fin N, I p l ∧ y (Fin.castAdd N p) = true ∧ y (Fin.natAdd N l) = true)) ∧ D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (N + N) D 1) ↔ (∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) → N*(q+2) ≤ C.size+1) := by
  constructor
  · intro norm q N I inst C hq hN hL hU ao f
    exact requested_implies_lower I norm PEqualNP.Outside.L_meta_2237 hq hN hL hU C ao f
  · intro size q N I inst C hq hN hL hU ao f
    exact replacement_above I hL C (size q N I C hq hN hL hU ao f)
end Plane2583
