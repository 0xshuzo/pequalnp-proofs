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

namespace PEqualNP.Outside.L_meta_8869.Donor

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

-- Circuit evaluation and OR reachability follow L_meta_1490 and L_meta_4901.
def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false
lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj
lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

end PEqualNP.Outside.L_meta_8869.Donor
namespace PEqualNP.Outside.L_meta_8869
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

def push (n : Nat) (C : Circuit) (g : Gate) : Circuit := ⟨C.gates++[g],n+C.size⟩

theorem push_size (n : Nat) (C : Circuit) (g : Gate) : (push n C g).size=C.size+1 := by
  simp [push,Circuit.size]
theorem push_gate_old (n : Nat) (C : Circuit) (g : Gate) (i : Nat) (hi : i<C.size) :
    gateAt (push n C g) i=gateAt C i := by
  change i<C.gates.length at hi
  simp [push,gateAt,List.getD_eq_getElem?_getD,List.getElem?_append_left hi]

theorem push_gate_new (n : Nat) (C : Circuit) (g : Gate) : gateAt (push n C g) C.size=g := by
  simp [push,gateAt,Circuit.size,List.getD_eq_getElem?_getD]

theorem push_model {n : Nat} {C : Circuit} {g : Gate} (h : IsAO2 n C)
    (op : g.op=GateOp.and ∨ g.op=GateOp.or) (len : g.inputs.length=2)
    (earlier : ∀ w∈g.inputs,w<n+C.size) : IsAO2 n (push n C g) := by
  refine ⟨?_,?_,?_⟩
  · intro p hp
    change p∈C.gates++[g] at hp
    rcases List.mem_append.mp hp with old|new
    · exact h.1 p old
    · obtain rfl : p=g := List.mem_singleton.mp new
      exact op
  · intro j hj w hw
    change j<(push n C g).size at hj
    rw [push_size] at hj
    by_cases old : j<C.size
    · rw [push_gate_old _ _ _ _ old] at hw
      exact h.2.1 _ old _ hw
    · obtain rfl : j=C.size := by omega
      rw [push_gate_new] at hw
      exact earlier _ hw
  · intro p hp
    change p∈C.gates++[g] at hp
    rcases List.mem_append.mp hp with old|new
    · exact h.2.2 p old
    · obtain rfl : p=g := List.mem_singleton.mp new
      exact len

theorem push_keep {n : Nat} (C : Circuit) (g : Gate) (x : Fin n → Bool) (w : Nat)
    (hw : w<n+C.size) : wireVal n (push n C g) w x = wireVal n C w x := by
  change Donor.val (push n C g) (List.ofFn x) w = Donor.val C (List.ofFn x) w
  unfold Donor.val
  rw [Donor.wires_eq_foldl,Donor.wires_eq_foldl]
  change ((C.gates++[g]).foldl Donor.stepWire (List.ofFn x)).getD w false=_
  rw [List.foldl_append]
  apply Donor.foldl_getD_lt
  rw [Donor.foldl_length]
  simpa only [List.length_ofFn,Circuit.size] using hw

theorem push_value {n : Nat} (C : Circuit) (g : Gate) (x : Fin n → Bool)
    (earlier : ∀ w∈g.inputs,w<n+C.size) :
    wireVal n (push n C g) (n+C.size) x = g.op.eval (g.inputs.map (fun w => wireVal n C w x)) := by
  change Donor.val (push n C g) (List.ofFn x) (n+C.size)=_
  rw [Donor.val_gate (n:=n) (by simp) (by change C.size<(push n C g).size; rw [push_size]; omega),
    push_gate_new]
  congr 1
  apply List.map_congr_left
  intro w hw
  rw [if_pos (earlier w hw)]
  exact push_keep _ _ _ _ (earlier w hw)

def dup (w : Nat) : Gate := ⟨GateOp.and,[w,w]⟩
def join (u v : Nat) : Gate := ⟨GateOp.or,[u,v]⟩
def first (n : Nat) (C : Circuit) := push n C (dup C.output)
def second (n : Nat) (C : Circuit) := push n (first n C) (dup C.output)
def pad (n : Nat) (C : Circuit) := push n (second n C) (join (n+C.size) (n+(C.size+1)))

@[simp] theorem size_first (n : Nat) (C : Circuit) : (first n C).size=C.size+1 := push_size .. 
@[simp] theorem size_second (n : Nat) (C : Circuit) : (second n C).size=C.size+2 := by simp [second,push_size]
@[simp] theorem size_pad (n : Nat) (C : Circuit) : (pad n C).size=C.size+3 := by simp [pad,push_size]

theorem pad_model {n : Nat} {C : Circuit} (model : IsAO2 n C) (out : C.output<n+C.size) :
    IsAO2 n (pad n C) := by
  have a : IsAO2 n (first n C) := push_model model (Or.inl rfl) rfl (by simp [dup,out])
  have b : IsAO2 n (second n C) := push_model a (Or.inl rfl) rfl (by simp [dup]; omega)
  exact push_model b (Or.inr rfl) rfl (by simp [join] <;> omega)

end PEqualNP.Outside.L_meta_8869
namespace PEqualNP.Outside.L_meta_8869
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

theorem iter_gate (n : Nat) (C : Circuit) :
    gateAt (pad n C) C.size=dup C.output ∧ gateAt (pad n C) (C.size+1)=dup C.output ∧
    gateAt (pad n C) (C.size+2)=join (n+C.size) (n+(C.size+1)) := by
  constructor
  · unfold pad
    rw [push_gate_old _ _ _ _ (by simp)]
    unfold second
    rw [push_gate_old _ _ _ _ (by simp)]
    exact push_gate_new ..
  constructor
  · unfold pad
    rw [push_gate_old _ _ _ _ (by simp)]
    rw [←size_first n C]
    exact push_gate_new ..
  · rw [←size_second n C]
    exact push_gate_new ..

theorem iter_values {n : Nat} (C : Circuit) (out : C.output<n+C.size) (x : Fin n → Bool) :
    wireVal n (pad n C) C.output x=wireVal n C C.output x ∧
    wireVal n (pad n C) (n+C.size) x=wireVal n C C.output x ∧
    wireVal n (pad n C) (n+(C.size+1)) x=wireVal n C C.output x ∧
    wireVal n (pad n C) (pad n C).output x=wireVal n C C.output x := by
  let A := first n C
  let B := second n C
  have asize : A.size=C.size+1 := size_first ..
  have bsize : B.size=C.size+2 := size_second ..
  have aold : wireVal n A C.output x=wireVal n C C.output x := push_keep C _ x _ out
  have bold : wireVal n B C.output x=wireVal n A C.output x := push_keep A _ x _ (by omega)
  have pold : wireVal n (pad n C) C.output x=wireVal n B C.output x := push_keep B _ x _ (by omega)
  have firstVal : wireVal n A (n+C.size) x=wireVal n C C.output x := by
    rw [show A=push n C (dup C.output) from rfl,push_value _ _ _ (by simp [dup,out])]
    cases h : wireVal n C C.output x <;> simp [dup, GateOp.eval,h]
  have secondVal : wireVal n B (n+(C.size+1)) x=wireVal n A C.output x := by
    rw [←asize,show B=push n A (dup C.output) from rfl,push_value _ _ _ (by simp [dup]; omega)]
    cases h : wireVal n A C.output x <;> simp [dup,GateOp.eval,h]
  have bfirst : wireVal n B (n+C.size) x=wireVal n A (n+C.size) x := push_keep A _ x _ (by omega)
  have pfirst : wireVal n (pad n C) (n+C.size) x=wireVal n B (n+C.size) x := push_keep B _ x _ (by omega)
  have psecond : wireVal n (pad n C) (n+(C.size+1)) x=wireVal n B (n+(C.size+1)) x :=
    push_keep B _ x _ (by omega)
  refine ⟨pold.trans (bold.trans aold),pfirst.trans (bfirst.trans firstVal),psecond.trans (secondVal.trans aold),?_⟩
  change wireVal n (push n B (join (n+C.size) (n+(C.size+1)))) (n+B.size) x=_
  rw [push_value _ _ _ (by simp [join] <;> omega)]
  simp only [join,List.map_cons,List.map_nil,bfirst,firstVal,secondVal,aold]
  cases h : wireVal n C C.output x <;> rfl

theorem strict_cone (n : Nat) (C : Circuit) (i : Nat) : ∀ j, InCone n C i j → i<j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    obtain ⟨_,k,lt,_,rfl|pre⟩ := (Donor.inCone_iff n C i j).mp h
    · exact lt
    · exact lt_trans (ih k lt pre) lt

theorem separate {n : Nat} (C : Circuit) (out : C.output<n+C.size) :
    ¬InCone n (pad n C) C.size (C.size+1) ∧ ¬InCone n (pad n C) (C.size+1) C.size := by
  constructor
  · intro h
    obtain ⟨_,k,lt,inp,eq|pre⟩ := (Donor.inCone_iff ..).mp h
    · rw [(iter_gate n C).2.1] at inp
      simp [dup] at inp
      omega
    · have l := strict_cone _ _ _ _ pre
      omega
  · intro h
    have l := strict_cone _ _ _ _ h
    omega

abbrev step {n : Nat} (C : Circuit) (x : Fin n → Bool) (w w' : Nat) : Prop :=
  ∃ k<C.size,w'=n+k ∧ w∈(gateAt C k).inputs ∧ wireVal n C w x=true ∧ wireVal n C w' x=true

abbrev mark {n : Nat} (C : Circuit) (x : Fin n → Bool) (v : Fin n) (j : Nat) : Prop :=
  j<C.size ∧ (gateAt C j).op=GateOp.and ∧ Relation.ReflTransGen (step C x) (n+j) C.output ∧
  ∀ b : Fin 2,wireVal n C (opnd C j b) (fun r => decide (r=v))=false

theorem mark_both {n : Nat} (C : Circuit) (out : C.output<n+C.size) (x : Fin n → Bool)
    (on : wireVal n C C.output x=true) (v w : Fin n)
    (voff : wireVal n C C.output (fun r => decide (r=v))=false)
    (woff : wireVal n C C.output (fun r => decide (r=w))=false) :
    mark (pad n C) x v C.size ∧ mark (pad n C) x w (C.size+1) := by
  obtain ⟨g0,g1,g2⟩ := iter_gate n C
  obtain ⟨_,p0,p1,po⟩ := iter_values C out x
  have outIndex : (pad n C).output=n+(C.size+2) := by change n+(second n C).size=_; rw [size_second]
  have trace (j : Nat) (mem : n+j∈(gateAt (pad n C) (C.size+2)).inputs)
      (vj : wireVal n (pad n C) (n+j) x=true) :
      Relation.ReflTransGen (step (pad n C) x) (n+j) (pad n C).output := by
    exact Relation.ReflTransGen.single ⟨C.size+2,by rw [size_pad]; omega,outIndex,mem,vj,po.trans on⟩
  have operands (j : Nat) (gj : gateAt (pad n C) j=dup C.output) (b : Fin 2) :
      opnd (pad n C) j b=C.output := by fin_cases b <;> simp [opnd,gj,dup]
  constructor
  · refine ⟨by rw [size_pad]; omega,by rw [g0]; rfl,trace _ (by rw [g2]; simp [join]) (p0.trans on),?_⟩
    intro b
    rw [operands _ g0 b,(iter_values C out _).1,voff]
  · refine ⟨by rw [size_pad]; omega,by rw [g1]; rfl,trace _ (by rw [g2]; simp [join]) (p1.trans on),?_⟩
    intro b
    rw [operands _ g1 b,(iter_values C out _).1,woff]

end PEqualNP.Outside.L_meta_8869

namespace PEqualNP.Outside.L_meta_8869
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge Finset

abbrev Posted : Prop := ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Finset (Fin x2 × Fin x2)),   (87 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) →         (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) →           PEqualNP.TopForm.IsAO2 (x2 + x2) x5 →             have x12 : ℕ → (Fin (x2 + x2) → Bool) → Bool := PEqualNP.CleanedNonEdge.wireVal (x2 + x2) x5;             have x13 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (x2 + x2) x5;             have x14 : Fin x2 × Fin x2 → Fin (x2 + x2) → Bool := fun (x14 : Fin x2 × Fin x2) (x15 : Fin (x2 + x2)) => Decidable.decide (x15 = Fin.castAdd x2 x14.1 ∨ x15 = Fin.natAdd x2 x14.2);             have x15 : Fin x2 × Fin x2 → Fin (x2 + x2) → ℕ → Prop := fun (x15 : Fin x2 × Fin x2) (x16 : Fin (x2 + x2)) (x17 : ℕ) => x17 < x5.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x17).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ Relation.ReflTransGen (fun (x18 x19 : ℕ) => ∃ x20 < x5.size, x19 = x2 + x2 + x20 ∧ x18 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x20).inputs ∧ x12 x18 (x14 x15) = Bool.true ∧ x12 x19 (x14 x15) = Bool.true) (x2 + x2 + x17) x5.output ∧ ∀ (x18 : Fin (2 : ℕ)), (x12 (PEqualNP.TopForm.opnd x5 x17 x18) fun (x19 : Fin (x2 + x2)) => Decidable.decide (x19 = x16)) = Bool.false;             (∀ (x16 : Fin (x2 + x2) → Bool), Fintype.card { x17 : Fin x2 // x16 (Fin.natAdd x2 x17) = Bool.true } ≤ x1 → (¬∃ (x18 : Fin x2) (x19 : Fin x2), x3 x18 x19 ∧ x16 (Fin.castAdd x2 x18) = Bool.true ∧ x16 (Fin.natAdd x2 x19) = Bool.true) → x12 x5.output x16 = Bool.false) → (∀ x17 ∈ x6, x3 x17.1 x17.2 ∧ x12 x5.output (x14 x17) = Bool.true ∧ ∃ (x19 : ℕ) (x20 : ℕ), x19 ≠ x20 ∧ ¬x13 x19 x20 ∧ ¬x13 x20 x19 ∧ x15 x17 (Fin.castAdd x2 x17.1) x19 ∧ x15 x17 (Fin.natAdd x2 x17.2) x20) → x6.card ≤ (8 : ℕ) * x5.size

abbrev Unrestricted (overhead : Nat) : Prop :=
  ∀ (q n : Nat) (R : Fin n → Fin n → Prop) [DecidableRel R] (C : Circuit) (E : Finset (Fin n × Fin n)),
    87≤q → n=q^2+q+1 → (∀ l,Fintype.card {p : Fin n // R p l}=q+1) →
    (∀ p t,p≠t → ∃! l,R p l ∧ R t l) → IsAO2 (n+n) C → quiet q R C →
    (∀ e∈E,R e.1 e.2 ∧ wireVal (n+n) C C.output (pair e)=true) →
    E.card≤8*(C.size+overhead)

theorem lower_implication (h : Posted) : Unrestricted 3 := by
  intro q n R _ C E hq hn line joinp model sound acc
  classical
  by_cases he : E.Nonempty
  · obtain ⟨e,ee⟩ := he
    have o : C.output<n+n+C.size := by
      by_contra! bad
      have z := Donor.val_ge (C:=C) (by simp : (List.ofFn (pair e)).length=n+n) bad
      have yes := (acc e ee).2
      change Donor.val C (List.ofFn (pair e)) C.output=true at yes
      rw [z] at yes
      cases yes
    have sn := single_off (by omega : 1≤q) sound
    have b := h q n R (pad (n+n) C) E hq hn line joinp (pad_model model o) (by
      intro x few nohit
      exact ((iter_values C o x).2.2.2).trans (sound x few nohit)) (by
      intro e mem
      obtain ⟨inc,on⟩ := acc e mem
      obtain ⟨one,two⟩ := mark_both C o (pair e) on (Fin.castAdd n e.1) (Fin.natAdd n e.2) (sn _) (sn _)
      exact ⟨inc,((iter_values C o (pair e)).2.2.2).trans on,C.size,C.size+1,by omega,
        (separate C o).1,(separate C o).2,one,two⟩)
    simpa only [size_pad] using b
  · simp [Finset.not_nonempty_iff_eq_empty.mp he]

theorem upper_implication (h : Unrestricted 0) : Posted := by
  intro q n R _ C E hq hn line joinp model
  dsimp only
  intro sound acc
  have b := h q n R C E hq hn line joinp model sound (fun e he => ⟨(acc e he).1,(acc e he).2.1⟩)
  simpa using b
end PEqualNP.Outside.L_meta_8869

namespace PEqualNP.Outside.L_meta_8869
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.CleanedNonEdge Finset

theorem normalized_claim (h : Posted) {q n : Nat} (R : Fin n → Fin n → Prop) [DecidableRel R]
    (C : Circuit) (E : Finset (Fin n × Fin n)) (hq : 87≤q) (order : n=q^2+q+1)
    (deg : ∀ l,Fintype.card {p : Fin n // R p l}=q+1) (line : ∀ u v,u≠v → ∃! l,R u l ∧ R v l)
    (ao : IsAO2 (n+n) C) (sound : quiet q R C)
    (on : ∀ e∈E,R e.1 e.2 ∧ wireVal (n+n) C C.output (pair e)=true) :
    481*E.card≤3872*C.size := by
  by_cases low : C.size≤480
  · have exactB := gate480 R C E (by omega) line ao sound on low
    omega
  · have cap := lower_implication h q n R C E hq order deg line ao sound on
    omega

abbrev OriginalParent : Prop := ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (87 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.TopForm.IsAO2 (x2 + x2) x5 → (∀ (x11 : Fin (x2 + x2) → Bool), Fintype.card { x12 : Fin x2 // x11 (Fin.natAdd x2 x12) = Bool.true } ≤ x1 → (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x11 (Fin.castAdd x2 x13) = Bool.true ∧ x11 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x11 = Bool.false) → Fintype.card { x12 : Fin x2 × Fin x2 // x3 x12.1 x12.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x13 : Fin (x2 + x2)) => Decidable.decide (x13 = Fin.castAdd x2 x12.1 ∨ x13 = Fin.natAdd x2 x12.2)) = Bool.true ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x13 : ℕ) => Decidable.decide (x2 ≤ x13)) (↑x12.1) (x2 + ↑x12.2) = Bool.false ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x13 : ℕ) => Decidable.decide (x13 < x2)) (↑x12.1) (x2 + ↑x12.2) = Bool.false } ≤ (24 : ℕ) * x5.size
theorem gives_parent (h : Posted) : OriginalParent := by
  intro q n R _ C hq order deg line ao sound
  classical
  let F := univ.filter (fun e : Fin n × Fin n =>
    R e.1 e.2 ∧ PEqualNP.MetaComplexity.circuitFun (n+n) C (pair e)=true ∧
    PEqualNP.ReadK.lineSingle C (n+n) (fun i => decide (n≤i)) e.1.val (n+e.2.val)=false ∧
    PEqualNP.ReadK.lineSingle C (n+n) (fun i => decide (i<n)) e.1.val (n+e.2.val)=false)
  have cap := normalized_claim h R C F hq order deg line ao sound (fun e he =>
    ⟨(mem_filter.mp he).2.1,(mem_filter.mp he).2.2.1⟩)
  rw [Fintype.card_subtype]
  change F.card≤24*C.size
  omega
end PEqualNP.Outside.L_meta_8869
