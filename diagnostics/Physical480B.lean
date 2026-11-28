import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_8869.Geometry
open Finset
theorem mul_self_sub_self (n : ℕ) : n * n - n = n * (n - 1) := by
  by_cases hn : n = 0
  · subst hn
    rfl
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have h1 : (k + 1) * (k + 1) = (k + 1) * k + (k + 1) := by ring
    have h2 : k + 1 - 1 = k := by omega
    rw [h1, h2, Nat.add_sub_cancel]

theorem offDiag_card_eq {α : Type*} [DecidableEq α] (s : Finset α) :
    s.offDiag.card = s.card * (s.card - 1) := by
  rw [Finset.offDiag_card]
  exact mul_self_sub_self s.card

theorem sq_eq_add_mul_pred (n : ℕ) : n ^ 2 = n + n * (n - 1) := by
  by_cases hn : n = 0
  · subst hn
    rfl
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hk : k + 1 - 1 = k := by omega
    rw [hk]
    ring

theorem card_filter_product_eq_sum {A B : Type} [DecidableEq A] [DecidableEq B]
    (E : Finset (A × B)) (X : Finset A) (Y : Finset B) :
    ((X ×ˢ Y).filter (fun p => p ∈ E)).card =
      ∑ a ∈ X, (Y.filter (fun b => (a, b) ∈ E)).card := by
  have hS : (X ×ˢ Y).filter (fun p => p ∈ E) =
      X.biUnion (fun a => (Y.filter (fun b => (a, b) ∈ E)).image (fun b => (a, b))) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion, Finset.mem_image]
    constructor
    · rintro ⟨⟨ha, hb⟩, hab⟩
      exact ⟨a, ha, b, ⟨hb, hab⟩, rfl⟩
    · rintro ⟨a', ha', b', ⟨hb', hab'⟩, h⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact ⟨⟨ha', hb'⟩, hab'⟩
  have hdisj : (X : Set A).PairwiseDisjoint
      (fun a => (Y.filter (fun b => (a, b) ∈ E)).image (fun b => (a, b))) := by
    intro a₁ _ a₂ _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro p hp₁ hp₂
    simp only [Finset.mem_image, Finset.mem_filter] at hp₁ hp₂
    obtain ⟨b₁, _, h₁⟩ := hp₁
    obtain ⟨b₂, _, h₂⟩ := hp₂
    exact hne (Prod.mk.inj (h₁.trans h₂.symm)).1
  rw [hS, Finset.card_biUnion hdisj]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.card_image_of_injective]
  exact fun b₁ b₂ h => (Prod.mk.inj h).2

theorem sum_pairs_le_offDiag {A B : Type} [DecidableEq A] [DecidableEq B]
    (E : Finset (A × B))
    (hE : ∀ a a' : A, ∀ b b' : B, a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (X : Finset A) (Y : Finset B) :
    ∑ a ∈ X, (Y.filter (fun b => (a, b) ∈ E)).card *
        ((Y.filter (fun b => (a, b) ∈ E)).card - 1) ≤
      Y.card * (Y.card - 1) := by
  have hdisj : (X : Set A).PairwiseDisjoint
      (fun a => (Y.filter (fun b => (a, b) ∈ E)).offDiag) := by
    intro a₁ _ a₂ _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro q hq₁ hq₂
    simp only [Finset.mem_offDiag, Finset.mem_filter] at hq₁ hq₂
    have hqne : q.1 ≠ q.2 := by tauto
    have h11 : (a₁, q.1) ∈ E := by tauto
    have h12 : (a₁, q.2) ∈ E := by tauto
    have h21 : (a₂, q.1) ∈ E := by tauto
    have h22 : (a₂, q.2) ∈ E := by tauto
    exact hE a₁ a₂ q.1 q.2 hne hqne ⟨h11, h12, h21, h22⟩
  have hsub : X.biUnion (fun a => (Y.filter (fun b => (a, b) ∈ E)).offDiag) ⊆ Y.offDiag := by
    rw [Finset.biUnion_subset]
    intro a _ q hq
    simp only [Finset.mem_offDiag, Finset.mem_filter] at hq ⊢
    tauto
  calc
    ∑ a ∈ X, (Y.filter (fun b => (a, b) ∈ E)).card *
        ((Y.filter (fun b => (a, b) ∈ E)).card - 1) =
      ∑ a ∈ X, ((Y.filter (fun b => (a, b) ∈ E)).offDiag).card := by
        refine Finset.sum_congr rfl fun a _ => ?_
        exact (offDiag_card_eq (Y.filter (fun b => (a, b) ∈ E))).symm
    _ = (X.biUnion (fun a => (Y.filter (fun b => (a, b) ∈ E)).offDiag)).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ Y.offDiag.card := Finset.card_le_card hsub
    _ = Y.card * (Y.card - 1) := offDiag_card_eq Y

theorem tangent (k : Nat) : 30*k≤k*(k-1)+240 := by
  by_cases h : k≤15
  · interval_cases k <;> decide
  · obtain ⟨x,rfl⟩ : ∃ x,k=x+16 := ⟨k-16,by omega⟩
    have e : x+16-1=x+15 := by omega
    rw [e]
    nlinarith [Nat.zero_le (x*x)]

theorem sparse_side {A B : Type} [DecidableEq A] [DecidableEq B]
    (E : Finset (A × B)) (X : Finset A) (Y : Finset B) (sub : E ⊆ X ×ˢ Y)
    (four : ∀ a a' : A, ∀ b b' : B, a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (yp : 0<Y.card) (ys : Y.card≤240) : E.card+8≤8*(X.card+Y.card) := by
  classical
  let d (a : A) := (Y.filter (fun b => (a,b)∈E)).card
  have el : (X ×ˢ Y).filter (fun e => e ∈ E)=E := by ext e; simp only [mem_filter]; exact ⟨And.right,fun h => ⟨sub h,h⟩⟩
  have summ : E.card=∑ a ∈ X,d a := el ▸ card_filter_product_eq_sum E X Y
  have pairs := sum_pairs_le_offDiag E four X Y
  change ∑ a ∈ X,d a*(d a-1) ≤ Y.card*(Y.card-1) at pairs
  have budget := Finset.sum_le_sum (s:=X) (fun a _ => tangent (d a))
  rw [←Finset.mul_sum,←summ,Finset.sum_add_distrib] at budget
  simp only [Finset.sum_const,Nat.nsmul_eq_mul] at budget
  have last := Nat.mul_le_mul_right (Y.card-1) ys
  have diff : 240*(Y.card-1)+240=240*Y.card := by
    have := Nat.sub_add_cancel (show 1≤Y.card from yp)
    nlinarith
  omega

def SquareFree {A B : Type} (E : Finset (A × B)) : Prop :=
  ∀ a a' : A, ∀ b b' : B, a ≠ a' → b ≠ b' → ¬ ((a,b)∈E ∧ (a,b')∈E ∧ (a',b)∈E ∧ (a',b')∈E)

theorem sparse_either {A B : Type} [DecidableEq A] [DecidableEq B] (E : Finset (A × B))
    (four : SquareFree E) (non : E.Nonempty)
    (small : (E.image Prod.fst).card≤240 ∨ (E.image Prod.snd).card≤240) :
    E.card+8≤8*((E.image Prod.fst).card+(E.image Prod.snd).card) := by
  classical
  let X := E.image Prod.fst
  let Y := E.image Prod.snd
  have sub : E ⊆ X ×ˢ Y := fun e he => mem_product.mpr ⟨mem_image_of_mem _ he,mem_image_of_mem _ he⟩
  obtain ⟨e,he⟩ := non
  rcases small with left|right
  · let D := E.image Prod.swap
    have dm (a : A) (b : B) : (b,a)∈D ↔ (a,b)∈E := by
      simp only [D,mem_image,Prod.exists,Prod.swap_prod_mk,Prod.mk.injEq]
      aesop
    have ds : D ⊆ Y ×ˢ X := by
      rintro ⟨b,a⟩ h
      obtain ⟨u,v⟩ := mem_product.mp (sub ((dm a b).mp h))
      exact mem_product.mpr ⟨v,u⟩
    have df : SquareFree D := by
      rintro b b' a a' ne ne' ⟨one,two,three,last⟩
      exact four a a' b b' ne' ne ⟨(dm _ _).mp one,(dm _ _).mp three,(dm _ _).mp two,(dm _ _).mp last⟩
    have upper := sparse_side D Y X ds df (card_pos.mpr ⟨e.1,(mem_product.mp (sub he)).1⟩) left
    have eq : D.card=E.card := card_image_of_injective _ (fun x y h => by simpa using congrArg Prod.swap h)
    change E.card+8≤8*(X.card+Y.card)
    omega
  · exact sparse_side E X Y sub four (card_pos.mpr ⟨e.2,(mem_product.mp (sub he)).2⟩) right
end PEqualNP.Outside.L_meta_8869.Geometry

namespace PEqualNP.Outside.L_meta_8869
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge Finset

abbrev pair {n : Nat} (e : Fin n × Fin n) (r : Fin (n+n)) := decide (r=Fin.castAdd n e.1 ∨ r=Fin.natAdd n e.2)
abbrev quiet {n : Nat} (q : Nat) (R : Fin n → Fin n → Prop) (C : Circuit) := ∀ x : Fin (n+n) → Bool,
  Fintype.card {l : Fin n // x (Fin.natAdd n l)=true} ≤ q →
    (¬∃ p l,R p l ∧ x (Fin.castAdd n p)=true ∧ x (Fin.natAdd n l)=true) → wireVal (n+n) C C.output x=false

theorem single_off {n q : Nat} {R : Fin n → Fin n → Prop} {C : Circuit} (hq : 1≤q) (sound : quiet q R C)
    (v : Fin (n+n)) : wireVal (n+n) C C.output (fun r => decide (r=v))=false := by
  apply sound
  · apply le_trans _ hq
    apply Fintype.card_le_one_iff_subsingleton.mpr
    constructor
    intro a b
    apply Subtype.ext
    exact Fin.natAdd_injective _ _ ((of_decide_eq_true a.property).trans (of_decide_eq_true b.property).symm)
  · rintro ⟨p,l,_,hv,hw⟩
    have eq := (of_decide_eq_true hv).trans (of_decide_eq_true hw).symm
    have h : p.val=n+l.val := congrArg Fin.val eq
    have := p.isLt
    omega


open PEqualNP.MetaComplexity
private def evalFrom {α : Type} (d : α) (op : GateOp → List α → α) (gates : List Gate) (xs : List α) :
    List α :=
  gates.foldl (fun u g => u ++ [op g.op (g.inputs.map fun i => u.getD i d)]) xs

private lemma evalFrom_cons {α : Type} (d : α) (op : GateOp → List α → α) (g : Gate) (gs : List Gate)
    (xs : List α) :
    evalFrom d op (g :: gs) xs = evalFrom d op gs
      (xs ++ [op g.op (g.inputs.map fun i => xs.getD i d)]) := rfl

private lemma evalFrom_length {α : Type} (d : α) (op : GateOp → List α → α) (gs : List Gate)
    (xs : List α) : (evalFrom d op gs xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp [evalFrom]
  | cons g gs ih => rw [evalFrom_cons, ih]; simp; omega

private def run (gs : List Gate) (xs : List Bool) : List Bool :=
  evalFrom false GateOp.eval gs xs

private lemma run_snoc (gs : List Gate) (g : Gate) (xs : List Bool) :
    run (gs ++ [g]) xs = run gs xs ++ [g.op.eval (g.inputs.map fun i => (run gs xs).getD i false)] := by
  simp [run, evalFrom, List.foldl_append]

private lemma run_length (gs : List Gate) (xs : List Bool) :
    (run gs xs).length = xs.length + gs.length :=
  evalFrom_length false GateOp.eval gs xs

private lemma supports (n : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (F : Finset ℕ) :
    ∃ S : Finset ℕ, S.card ≤ F.card + gs.length ∧
      ∀ (x y : List Bool), x.length = n → y.length = n →
        (∀ i ∈ S, x.getD i false = y.getD i false) →
        ∀ i ∈ F, (run gs x).getD i false = (run gs y).getD i false := by
  induction gs using List.reverseRecOn generalizing F with
  | nil => exact ⟨F, by simp, fun _ _ _ _ ha => ha⟩
  | append_singleton gs g ih =>
    let j := n + gs.length
    let B := if j ∈ F then F.erase j ∪ g.inputs.toFinset else F
    have hb : B.card ≤ F.card + 1 := by
      by_cases hj : j ∈ F
      · have hu := Finset.card_union_le (F.erase j) g.inputs.toFinset
        have he := Finset.card_erase_add_one hj
        have hd := (List.toFinset_card_le g.inputs).trans (hg g (by simp))
        simp only [B, ite_eq_left hj]
        omega
      · simp [B, hj]
    obtain ⟨S, hS, hs⟩ := ih (fun a ha => hg a (List.mem_append_left _ ha)) B
    refine ⟨S, by simp only [List.length_append, List.length_singleton]; omega, ?_⟩
    intro x y hx hy ha i hi
    have ex : (run gs x).length = j := by simp [run_length, hx, j]
    have ey : (run gs y).length = j := by simp [run_length, hy, j]
    rw [run_snoc, run_snoc]
    rcases lt_trichotomy i j with hij | rfl | hij
    · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      apply hs x y hx hy ha i
      by_cases hj : j ∈ F
      · simpa [B, hj] using Finset.mem_union_left g.inputs.toFinset (Finset.mem_erase.mpr ⟨hij.ne, hi⟩)
      · simpa [B, hj] using hi
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
      simp only [ex, ey, Nat.sub_self, List.getD_cons_zero]
      congr 1
      apply List.map_congr_left
      intro k hk
      apply hs x y hx hy ha k
      simpa [B, hi] using Finset.mem_union_right (F.erase j) (List.mem_toFinset.mpr hk)
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem essential_bits {n : Nat} (C : Circuit) (ao : IsAO2 n C) (I : Finset (Fin n))
    (sens : ∀ i∈I,∃ x y : Fin n → Bool,(∀ j,j≠i → x j=y j) ∧ wireVal n C C.output x≠wireVal n C C.output y) :
    I.card≤C.size+1 := by
  obtain ⟨S,hS,hs⟩ := supports n C.gates (fun g hg => (ao.2.2 g hg).le) {C.output}
  have sub : I.image Fin.val ⊆ S := by
    rintro _ hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
    by_contra miss
    obtain ⟨x,y,agree,ne⟩ := sens i hi
    apply ne
    apply hs (List.ofFn x) (List.ofFn y) (by simp) (by simp) _ C.output (by simp)
    intro j hj
    by_cases bound : j<n
    · rw [List.getD_eq_getElem _ _ (by simpa using bound),List.getD_eq_getElem _ _ (by simpa using bound)]
      simp only [List.getElem_ofFn]
      apply agree
      intro eq
      have e : j=i.val := congrArg Fin.val eq
      exact miss (e ▸ hj)
    · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt bound),
          List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt bound)]
  have card := Finset.card_le_card sub
  rw [Finset.card_image_of_injective _ Fin.val_injective] at card
  simpa only [Finset.card_singleton, Nat.add_comm 1,Circuit.size] using card.trans hS

theorem shores {n q : Nat} (R : Fin n → Fin n → Prop) (C : Circuit) (E : Finset (Fin n × Fin n))
    (hq : 1≤q) (ao : IsAO2 (n+n) C) (sound : quiet q R C)
    (on : ∀ e∈E,wireVal (n+n) C C.output (pair e)=true) :
    (E.image Prod.fst).card + (E.image Prod.snd).card ≤ C.size+1 := by
  classical
  let P := (E.image Prod.fst).image (Fin.castAdd n)
  let L := (E.image Prod.snd).image (Fin.natAdd n)
  have dis : Disjoint P L := by
    rw [Finset.disjoint_left]
    intro u hp hl
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨l,_,bad⟩ := Finset.mem_image.mp hl
    have eq := congrArg Fin.val bad
    change n+l.val=p.val at eq
    omega
  have all := essential_bits C ao (P ∪ L) (by
    intro i hi
    rcases Finset.mem_union.mp hi with pin|lin
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp pin
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hp
      refine ⟨pair e,fun r => decide (r=Fin.natAdd n e.2),?_,?_⟩
      · intro j ne
        simp only [pair,ne,false_or,or_false]
      · rw [on e he,single_off hq sound]
        decide
    · obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp lin
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hl
      refine ⟨pair e,fun r => decide (r=Fin.castAdd n e.1),?_,?_⟩
      · intro j ne
        simp only [pair,ne,false_or,or_false]
      · rw [on e he,single_off hq sound]
        decide)
  rw [Finset.card_union_of_disjoint dis] at all
  have pc : P.card=(E.image Prod.fst).card := card_image_of_injective _ (Fin.castAdd_injective n n)
  have lc : L.card=(E.image Prod.snd).card := card_image_of_injective _ (Fin.natAdd_injective n n)
  simpa only [pc,lc] using all

theorem shore_upper {n q : Nat} (R : Fin n → Fin n → Prop) (C : Circuit) (E : Finset (Fin n × Fin n))
    (hq : 1≤q) (joinp : ∀ p t,p≠t → ∃! l,R p l ∧ R t l) (ao : IsAO2 (n+n) C) (sound : quiet q R C)
    (on : ∀ e∈E,R e.1 e.2 ∧ wireVal (n+n) C C.output (pair e)=true)
    (small : (E.image Prod.fst).card≤240 ∨ (E.image Prod.snd).card≤240) :
    E.card≤8*C.size := by
  classical
  by_cases non : E.Nonempty
  · have four : Geometry.SquareFree E := by
      rintro a a' b b' an bn ⟨ab,ab',a'b,a'b'⟩
      obtain ⟨l,_,only⟩ := joinp a a' an
      exact bn ((only b ⟨(on _ ab).1,(on _ a'b).1⟩).trans (only b' ⟨(on _ ab').1,(on _ a'b').1⟩).symm)
    have geom := Geometry.sparse_either E four non small
    have supp := shores R C E hq ao sound (fun e he => (on e he).2)
    omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp non]

theorem gate480 {n q : Nat} (R : Fin n → Fin n → Prop) (C : Circuit) (E : Finset (Fin n × Fin n))
    (hq : 1≤q) (joinp : ∀ p t,p≠t → ∃! l,R p l ∧ R t l) (ao : IsAO2 (n+n) C) (sound : quiet q R C)
    (on : ∀ e∈E,R e.1 e.2 ∧ wireVal (n+n) C C.output (pair e)=true) (bounded : C.size≤480) :
    E.card≤8*C.size := by
  have bounds := shores R C E hq ao sound (fun e he => (on e he).2)
  exact shore_upper R C E hq joinp ao sound on (by omega)
end PEqualNP.Outside.L_meta_8869
