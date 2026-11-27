import PEqualNP.Defs
namespace L1018

abbrev Edge (n : ℕ) := Fin n × Fin n
abbrev Row (n : ℕ) := Finset (Edge n) × Bool

def ends {n} (e : Edge n) := ({e.1,e.2} : Finset (Fin n))
def choices {n} (E : Finset (Edge n)) (k : ℕ) := E.powerset.filter fun Q => Q.card=k ∧
  ∀ e∈Q, ∀ f∈Q, e≠f → Disjoint (ends e) (ends f)
def signed {n} (Q : Finset (Edge n)) (rows : List (Row n)) : ℤ :=
  ((rows.filter (fun t => t.2 && decide (Q ⊆ t.1))).length : ℤ) -
  ((rows.filter (fun t => !t.2 && decide (Q ⊆ t.1))).length : ℤ)
def weight {n} (Q : Finset (Edge n)) : ℕ :=
  let V := Q.biUnion ends
  V.prod fun i => (V.filter (fun j => i<j)).prod fun j => (j.val-i.val)^2
def total {n} (k : ℕ) (E : Finset (Edge n)) (rows : List (Row n)) :=
  (choices E k).sum fun Q => weight Q * (signed Q rows).natAbs^2

theorem weight_pos {n} (Q : Finset (Edge n)) : 0<weight Q := by
  apply Finset.prod_pos
  intro i _
  apply Finset.prod_pos
  intro j hj
  exact pow_pos (Nat.sub_pos_of_lt (Finset.mem_filter.mp hj).2) _

theorem detected {n} (k : ℕ) (E : Finset (Edge n)) (rows : List (Row n)) :
    0<total k E rows ↔ ∃ Q∈choices E k, signed Q rows ≠ 0 := by
  classical
  constructor
  · intro h
    by_contra no
    push_neg at no
    have nul : total k E rows=0 := Finset.sum_eq_zero (fun Q hQ => by simp [no Q hQ])
    omega
  · rintro ⟨Q,hQ,sgn⟩
    have t := Finset.single_le_sum (f:=fun S => weight S * (signed S rows).natAbs^2)
      (fun i _ => Nat.zero_le _) hQ
    have pos : 0 < (signed Q rows).natAbs := Int.natAbs_pos.mpr sgn
    exact (Nat.mul_pos (weight_pos Q) (pow_pos pos 2)).trans_le t

def term {n} (Q : Finset (Edge n)) (r : Row n) : ℤ :=
  if Q⊆r.1 then if r.2 then 1 else -1 else 0

theorem signed_sum {n} (Q : Finset (Edge n)) (rows : List (Row n)) :
    signed Q rows=(rows.map (term Q)).sum := by
  induction rows with
  | nil => simp [signed]
  | cons r rs ih =>
    rcases r with ⟨A,b⟩
    unfold signed at ih ⊢
    cases b <;> by_cases h : Q⊆A <;>
      simp [List.filter_cons,term,h] at ih ⊢ <;> omega

theorem total_cast {n} (k : ℕ) (E : Finset (Edge n)) (rows : List (Row n)) :
    (total k E rows : ℤ) = ∑ Q∈choices E k, (weight Q : ℤ)*(signed Q rows)^2 := by
  simp only [total,Nat.cast_sum,Nat.cast_mul,Nat.cast_pow,Int.natCast_natAbs,sq_abs]

theorem list_mul_sum (a : ℤ) (l : List ℤ) : a*l.sum=(l.map fun z=>a*z).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [mul_add,ih]

theorem pair_expand (l : List ℤ) : l.sum^2=(l.map (fun x => (l.map (fun y=>x*y)).sum)).sum := by
  rw [pow_two,list_mul_sum]
  congr 1
  apply List.map_congr_left
  intro x _
  rw [mul_comm,list_mul_sum]

theorem total_pair_rows {n} (k : ℕ) (E : Finset (Edge n)) (rows : List (Row n)) :
    (total k E rows : ℤ) =
      ∑ Q∈choices E k, (weight Q : ℤ)*
        (rows.map (fun r => (rows.map (fun s => term Q r * term Q s)).sum)).sum := by
  rw [total_cast]
  apply Finset.sum_congr rfl
  intro Q _
  rw [signed_sum,pair_expand]
  simp only [List.map_map,Function.comp_def]

def quadFactor {n} (a b : Fin n) : ℤ := ((a.val:ℤ) - b.val)^2
def above {n} (a b : Fin n) : ℤ := if a<b then quadFactor a b else 1
def vweight {n} (V : Finset (Fin n)) : ℤ := ∏ i∈V, ∏ j∈V, above i j
def hitFactor {n} (V : Finset (Fin n)) (x : ℤ) : ℤ := ∏ i∈V, (x-i.val)^2

theorem factor_symm {n} (a b : Fin n) : quadFactor a b=quadFactor b a := by
  unfold quadFactor
  ring
theorem vandermonde_nat {n} (Q : Finset (Edge n)) :
    (weight Q : ℤ)=vweight (Q.biUnion ends) := by
  classical
  simp only [weight,vweight,Nat.cast_prod,Nat.cast_pow,Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro j hj
  by_cases lt : i<j
  · simp only [above,lt,if_true,quadFactor]
    change (((j.val-i.val)^2 : ℕ) : ℤ) = ((i.val : ℤ)-j.val)^2
    rw [Nat.cast_pow,Nat.cast_sub (Fin.le_iff_val_le_val.mp lt.le)]
    ring
  · simp [above,lt]

theorem insert_weight {n} (V : Finset (Fin n)) (a : Fin n) (fresh : a∉V) :
    vweight (insert a V)=vweight V*hitFactor V a.val := by
  classical
  unfold vweight hitFactor
  simp only [Finset.prod_insert fresh,Finset.prod_mul_distrib]
  have aa : above a a=1 := if_neg (lt_irrefl _)
  rw [aa,one_mul]
  have single : (∏ i∈V,above a i)*(∏ i∈V,above i a)=∏ i∈V,((a.val:ℤ)-i.val)^2 := by
    rw [←Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    have ne : a≠i := fun e => fresh (e.symm ▸ hi)
    rcases lt_or_gt_of_ne ne with lt|gt
    · simp [above,lt,not_lt.mpr lt.le,quadFactor]
    · simp only [above,gt,if_true,not_lt.mpr gt.le,if_false,one_mul]
      exact factor_symm i a
  rw [←single]
  ring

theorem edge_extension {n} (V : Finset (Fin n)) (a b : Fin n) (ab : a≠b) :
    (if a∈V ∨ b∈V then (0:ℤ) else vweight (insert a (insert b V))) =
      vweight V * quadFactor a b * hitFactor V a.val * hitFactor V b.val := by
  classical
  have van (j : Fin n) (hj : j∈V) : hitFactor V j.val=0 := by
    apply Finset.prod_eq_zero hj
    simp
  by_cases ha : a∈V
  · simp [ha,van a ha]
  by_cases hb : b∈V
  · simp [hb,van b hb]
  have none : a∉insert b V := by simp [ab,ha]
  rw [if_neg (not_or_intro ha hb),insert_weight _ _ none,insert_weight _ _ hb]
  simp only [hitFactor,Finset.prod_insert hb,quadFactor]
  ring

def sign {n} (r : Row n) : ℤ := if r.2 then 1 else -1
def kernel {n} (k : ℕ) (F : Finset (Edge n)) : ℤ := ∑ Q∈choices F k, (weight Q : ℤ)

theorem term_product {n} (Q : Finset (Edge n)) (r s : Row n) :
    term Q r * term Q s=(if Q⊆r.1 ∧ Q⊆s.1 then sign r * sign s else 0) := by
  by_cases hr : Q⊆r.1 <;> by_cases hs : Q⊆s.1 <;> simp [term,sign,hr,hs]

theorem choices_meet {n} (k : ℕ) (E X Y : Finset (Edge n)) :
    choices (E∩X∩Y) k = (choices E k).filter (fun Q => Q⊆X ∧ Q⊆Y) := by
  classical
  ext Q
  simp only [choices,Finset.mem_filter,Finset.mem_powerset,Finset.subset_inter_iff]
  tauto

theorem swap_sum {α β : Type} (S : Finset α) (r : List β) (f : α→β→ℤ) :
    (∑ a∈S, (r.map (f a)).sum)=(r.map (fun v => ∑ a∈S, f a v)).sum := by
  induction r with
  | nil => simp
  | cons a r ih => simp [Finset.sum_add_distrib,ih]

theorem fixed_pair {n} (k : ℕ) (E : Finset (Edge n)) (r s : Row n) :
    (∑ Q∈choices E k, (weight Q : ℤ)*(term Q r*term Q s)) =
      sign r * sign s * kernel k (E∩r.1∩s.1) := by
  classical
  rw [kernel,choices_meet,Finset.sum_filter,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro Q hQ
  rw [term_product]
  split <;> ring

theorem expanded_kernel {n} (k : ℕ) (E : Finset (Edge n)) (rows : List (Row n)) :
    (total k E rows : ℤ) =
      (rows.map fun r => (rows.map fun s => sign r * sign s * kernel k (E∩r.1∩s.1)).sum).sum := by
  rw [total_pair_rows]
  have push (Q : Finset (Edge n)) :
      (weight Q:ℤ)*(rows.map (fun r => (rows.map (fun s => term Q r * term Q s)).sum)).sum =
        (rows.map fun r => (rows.map fun s => (weight Q:ℤ)*(term Q r*term Q s)).sum).sum := by
    rw [list_mul_sum]
    simp only [List.map_map,Function.comp_def,list_mul_sum]
  simp_rw [push]
  rw [swap_sum]
  congr 1
  apply List.map_congr_left
  intro r _
  rw [swap_sum]
  congr 1
  apply List.map_congr_left
  intro s _
  exact fixed_pair k E r s


theorem mem_choices {n k} (E Q : Finset (Edge n)) :
    Q∈choices E k ↔ Q⊆E ∧ Q.card=k ∧ ∀ e∈Q, ∀ f∈Q,e≠f → Disjoint (ends e) (ends f) := by
  simp [choices]

def compatible {n} (e : Edge n) (Q : Finset (Edge n)) : Prop := ∀ f∈Q, Disjoint (ends e) (ends f)

instance {n} (e : Edge n) (Q : Finset (Edge n)) : Decidable (compatible e Q) :=
  inferInstanceAs (Decidable (∀ f∈Q, Disjoint (ends e) (ends f)))

theorem split_choices {n} (E : Finset (Edge n)) (e : Edge n) (fresh : e∉E) (t : ℕ) :
    choices (insert e E) (t+1) = choices E (t+1) ∪
      ((choices E t).filter (compatible e)).image (insert e) := by
  classical
  ext Q
  rw [mem_choices,Finset.mem_union,mem_choices,Finset.mem_image]
  constructor
  · rintro ⟨sub,sz,sep⟩
    by_cases h : e∈Q
    · right
      refine ⟨Q.erase e,Finset.mem_filter.mpr ⟨(mem_choices _ _).mpr ⟨?_,?_,?_⟩,?_⟩,
        Finset.insert_erase h⟩
      · intro f hf
        rcases Finset.mem_erase.mp hf with ⟨ne,mem⟩
        exact (Finset.mem_insert.mp (sub mem)).resolve_left ne
      · rw [Finset.card_erase_of_mem h,sz]
        omega
      · intro f hf g hg ne
        exact sep f (Finset.mem_of_mem_erase hf) g (Finset.mem_of_mem_erase hg) ne
      · intro f hf
        have p := Finset.mem_erase.mp hf
        exact sep e h f p.2 p.1.symm
    · left
      exact ⟨fun f hf => (Finset.mem_insert.mp (sub hf)).resolve_left
         (fun eq => h (eq ▸ hf)),sz,sep⟩
  · rintro (⟨sub,sz,sep⟩|⟨R,hR,rfl⟩)
    · exact ⟨sub.trans (Finset.subset_insert _ _),sz,sep⟩
    · obtain ⟨hr,ok⟩ := Finset.mem_filter.mp hR
      obtain ⟨sub,sz,sep⟩ := (mem_choices _ _).mp hr
      have no : e∉R := fun h => fresh (sub h)
      refine ⟨Finset.insert_subset_insert _ sub,by rw [Finset.card_insert_of_notMem no,sz],?_⟩
      intro f hf g hg ne
      rcases Finset.mem_insert.mp hf with rfl|hf
      · rcases Finset.mem_insert.mp hg with rfl|hg
        · exact (ne rfl).elim
        · exact ok g hg
      · rcases Finset.mem_insert.mp hg with rfl|hg
        · exact (ok f hf).symm
        · exact sep f hf g hg ne

theorem sum_choice_step {n} (E : Finset (Edge n)) (e : Edge n) (fresh : e∉E) (t : ℕ)
    (F : Finset (Edge n) → ℤ) :
    (∑ Q∈choices (insert e E) (t+1),F Q) =
     (∑ Q∈choices E (t+1),F Q) +
     ∑ Q∈choices E t, (if compatible e Q then F (insert e Q) else 0) := by
  classical
  have miss {j} {Q : Finset (Edge n)} (h : Q∈choices E j) : e∉Q :=
    fun he => fresh (((mem_choices E Q).mp h).1 he)
  rw [split_choices _ _ fresh,Finset.sum_union,Finset.sum_image,Finset.sum_filter]
  · intro Q hQ R hR eq
    have q := miss (Finset.mem_filter.mp hQ).1
    have r := miss (Finset.mem_filter.mp hR).1
    simpa [q,r] using congrArg (fun S : Finset (Edge n) => S.erase e) eq
  · apply Finset.disjoint_left.mpr
    intro Q hQ hR
    rcases Finset.mem_image.mp hR with ⟨R,_,rfl⟩
    exact miss hQ (Finset.mem_insert_self _ _)

end L1018

namespace Grid1018
abbrev Seq := ℕ → ℤ
def diff (f : Seq) (i : ℕ) := f (i+1)-f i
def order : ℕ → Seq → Prop
  | 0,f => ∀ x, f x=f 0
  | d+1,f => order d (diff f)

theorem add_order (d : ℕ) (f g : Seq) (hf : order d f) (hg : order d g) :
    order d (fun x => f x+g x) := by
  induction d generalizing f g with
  | zero => exact fun x => congrArg₂ (·+·) (hf x) (hg x)
  | succ d ih =>
    change order d (diff (fun x => f x+g x))
    rw [show diff (fun x => f x+g x)=(fun x => diff f x+diff g x) by funext x; simp [diff]; ring]
    exact ih _ _ hf hg

theorem shift_order (d : ℕ) (f : Seq) (hf : order d f) : order d (fun x => f (x+1)) := by
  induction d generalizing f with
  | zero => exact fun x => (hf (x+1)).trans (hf 1).symm
  | succ d ih => exact ih (diff f) hf

theorem mul_linear_order (d : ℕ) (f : Seq) (a : ℤ) (hf : order d f) :
    order (d+1) (fun x => ((x:ℤ)-a)*f x) := by
  have rule (g : Seq) : diff (fun x => ((x:ℤ)-a)*g x)=fun x => g (x+1)+((x:ℤ)-a)*diff g x := by
    funext i
    simp [diff]
    ring
  induction d generalizing f with
  | zero =>
    change ∀ x, diff (fun i => ((i:ℤ)-a)*f i) x=diff (fun i => ((i:ℤ)-a)*f i) 0
    rw [rule]
    intro x
    simp only [diff]
    rw [hf (x+1),hf x,hf (0+1)]
    ring
  | succ d ih =>
    change order (d+1) (diff (fun x => ((x:ℤ)-a)*f x))
    rw [rule]
    exact add_order (d+1) _ _ (shift_order (d+1) f hf) (ih _ hf)

theorem characteristic_order {n : ℕ} (V : Finset (Fin n)) :
    order (2*V.card) (fun x : ℕ => ∏ i∈V, ((x:ℤ)-i.val)^2) := by
  classical
  induction V using Finset.induction_on with
  | empty => simp [order]
  | @insert i V hi ih =>
    rw [Finset.card_insert_of_notMem hi,Nat.mul_succ]
    simp only [Finset.prod_insert hi]
    have one := mul_linear_order (2*V.card) _ (i.val:ℤ) ih
    have two := mul_linear_order (2*V.card+1) _ (i.val:ℤ) one
    convert two using 1 <;> first | rfl | (funext x; ring)

def recover : ℕ → Seq → Seq
  | 0,f,_ => f 0
  | d+1,f,x => f 0 + ∑ i∈Finset.range x, recover d (diff f) i

theorem telescopes (f : Seq) (n : ℕ) : f 0 + ∑ i∈Finset.range n, diff f i = f n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,←add_assoc,ih]
    simp [diff]

theorem reconstruction (d : ℕ) (f : Seq) (h : order d f) (x : ℕ) : recover d f x=f x := by
  induction d generalizing f x with
  | zero => exact (h x).symm
  | succ d ih =>
    simp only [recover]
    have eq : ∀ i, recover d (diff f) i=diff f i := fun i => ih _ h i
    simp only [eq,telescopes]

theorem on_grid (d : ℕ) (f g : Seq) (agree : ∀ i≤d, f i=g i) (x : ℕ) :
    recover d f x=recover d g x := by
  induction d generalizing f g x with
  | zero => exact agree 0 le_rfl
  | succ d ih =>
    simp only [recover,agree 0 (Nat.zero_le _)]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply ih
    intro j hj
    simp only [diff,agree (j+1) (by omega),agree j (by omega)]

theorem linear {α : Type*} (S : Finset α) (a : α → ℤ) (F : α → Seq) (d x : ℕ) :
    recover d (fun i => ∑ j∈S,a j*F j i) x = ∑ j∈S,a j*recover d (F j) x := by
  induction d generalizing F x with
  | zero => rfl
  | succ d ih =>
    have delta : diff (fun i => ∑ j∈S,a j*F j i)=(fun i => ∑ j∈S,a j*diff (F j) i) := by
      funext i
      simp [diff,Finset.sum_sub_distrib,mul_sub]
    simp only [recover,delta]
    simp_rw [ih]
    rw [Finset.sum_comm (s:=Finset.range x) (t:=S)]
    simp [Finset.mul_sum,mul_add,Finset.sum_add_distrib]

def coeff (d x j : ℕ) : ℤ := recover d (fun i => if i=j then 1 else 0) x

theorem interpolation (d : ℕ) (f : Seq) (h : order d f) (x : ℕ) :
    f x = ∑ j∈Finset.range (d+1), f j*coeff d x j := by
  classical
  simp only [coeff]
  rw [←reconstruction d f h x,←linear (Finset.range (d+1)) f (fun j i => if i=j then 1 else 0) d x]
  apply on_grid
  intro i hi
  have hmem : i∈Finset.range (d+1) := Finset.mem_range.mpr (by omega)
  simp [mul_ite,hmem]

end Grid1018

namespace L1018
def samples {n} (V : Finset (Fin n)) : List ℕ → ℤ
  | [] => 1
  | j::J => hitFactor V j * samples V J

def pairSamples (a b : ℕ) : List ℕ → ℤ
  | [] => 1
  | j::J => ((j:ℤ)-a)^2*((j:ℤ)-b)^2*pairSamples a b J

theorem sample_extend {n} (V : Finset (Fin n)) (a b : Fin n)
    (ha : a∉V) (hb : b∉V) (ab : a≠b) (J : List ℕ) :
    samples (insert a (insert b V)) J = pairSamples a.val b.val J * samples V J := by
  classical
  have missing : a∉insert b V := by simp [ab,ha]
  induction J with
  | nil => simp [samples,pairSamples]
  | cons j J ih =>
    simp only [samples,pairSamples,hitFactor,Finset.prod_insert missing,Finset.prod_insert hb] at ih ⊢
    rw [ih]
    ring

theorem accumulated_edge {n} (V : Finset (Fin n)) (a b : Fin n) (ab : a≠b) (J : List ℕ) :
    (if a∈V ∨ b∈V then 0 else vweight (insert a (insert b V))*samples (insert a (insert b V)) J) =
    quadFactor a b * pairSamples a.val b.val J * (vweight V * samples V (a.val::b.val::J)) := by
  have ext := edge_extension V a b ab
  by_cases coll : a∈V ∨ b∈V
  · rw [if_pos coll] at ext ⊢
    simp only [samples]
    calc
      (0:ℤ) = 0 * (pairSamples a.val b.val J * samples V J) := by ring
      _ = _ := by rw [ext]; ring
  · rw [if_neg coll] at ext ⊢
    rw [ext,sample_extend V a b (fun ha=>coll (Or.inl ha)) (fun hb=>coll (Or.inr hb)) ab]
    simp only [samples]
    ring

def moment {n} (E : Finset (Edge n)) (t : ℕ) (J : List ℕ) : ℤ :=
    ∑ Q∈choices E t,vweight (Q.biUnion ends)*samples (Q.biUnion ends) J

theorem compatible_iff {n} (Q : Finset (Edge n)) (e : Edge n) :
    compatible e Q ↔ ¬(e.1∈Q.biUnion ends ∨ e.2∈Q.biUnion ends) := by
  constructor
  · intro h bad
    rcases bad with b|b
    · obtain ⟨f,hf,hit⟩ := Finset.mem_biUnion.mp b
      exact (Finset.disjoint_left.mp (h f hf)) (by simp [ends]) hit
    · obtain ⟨f,hf,hit⟩ := Finset.mem_biUnion.mp b
      exact (Finset.disjoint_left.mp (h f hf)) (by simp [ends]) hit
  · intro no f hf
    apply Finset.disjoint_left.mpr
    intro v hv hit
    have b := Finset.mem_biUnion.mpr ⟨f,hf,hit⟩
    rcases (show v=e.1 ∨ v=e.2 by simpa [ends] using hv) with h|h
    · exact no (Or.inl (h ▸ b))
    · exact no (Or.inr (h ▸ b))

theorem endpoints_insert {n} (e : Edge n) (Q : Finset (Edge n)) :
    (insert e Q).biUnion ends = insert e.1 (insert e.2 (Q.biUnion ends)) := by
  classical
  ext i
  simp [Finset.biUnion_insert,ends,or_assoc]

theorem moment_insert {n} (E : Finset (Edge n)) (e : Edge n) (fresh : e∉E)
    (ab : e.1≠e.2) (t : ℕ) (J : List ℕ) :
    moment (insert e E) (t+1) J = moment E (t+1) J +
        quadFactor e.1 e.2 * pairSamples e.1.val e.2.val J * moment E t (e.1.val::e.2.val::J) := by
  classical
  unfold moment
  rw [sum_choice_step E e fresh t,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro Q hQ
  rw [compatible_iff,endpoints_insert]
  simpa only [ite_not] using accumulated_edge (Q.biUnion ends) e.1 e.2 ab J

theorem grid_double {n d} (V : Finset (Fin n)) (degree : 2*V.card=d)
    (a b : ℕ) (J : List ℕ) :
    samples V (a::b::J)=
    ∑ p∈Finset.range (d+1),∑ q∈Finset.range (d+1),
      Grid1018.coeff d a p * Grid1018.coeff d b q * samples V (p::q::J) := by
  have h : Grid1018.order d (fun x : ℕ => hitFactor V x) := by
    rw [←degree]
    exact Grid1018.characteristic_order V
  have ha := Grid1018.interpolation d (fun x : ℕ => hitFactor V x) h a
  have hb := Grid1018.interpolation d (fun x : ℕ => hitFactor V x) h b
  show hitFactor V a*(hitFactor V b*samples V J)=_
  calc
    _ = (∑ p∈Finset.range (d+1),hitFactor V p*Grid1018.coeff d a p) *
          ((∑ q∈Finset.range (d+1),hitFactor V q*Grid1018.coeff d b q)*samples V J) :=
          congrArg₂ (fun u v : ℤ => u*(v*samples V J)) ha hb
    _ = _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      simp only [samples]
      ring

theorem matching_ends_card {n} (Q : Finset (Edge n)) (strict : ∀ e∈Q,e.1<e.2)
    (sep : ∀ e∈Q,∀ f∈Q,e≠f → Disjoint (ends e) (ends f)) :
    (Q.biUnion ends).card=2*Q.card := by
  classical
  rw [Finset.card_biUnion (fun e he f hf neq => sep e he f hf neq)]
  have two (e : Edge n) (he : e∈Q) : (ends e).card=2 := by
    simp [ends,Finset.card_insert_of_notMem,ne_of_lt (strict e he)]
  calc
    _ = ∑ _∈Q, (2:ℕ) := Finset.sum_congr rfl two
    _ = _ := by simp [Nat.mul_comm]

theorem moment_grid {n} (E : Finset (Edge n)) (t a b : ℕ) (J : List ℕ)
    (strict : ∀ e∈E,e.1<e.2) :
    moment E t (a::b::J) =
    ∑ p∈Finset.range (4*t+1),∑ q∈Finset.range (4*t+1),
      Grid1018.coeff (4*t) a p * Grid1018.coeff (4*t) b q * moment E t (p::q::J) := by
  classical
  let S := Finset.range (4*t+1)
  let A := choices E t
  let F (Q : Finset (Edge n)) (p q : ℕ) := Grid1018.coeff (4*t) a p * Grid1018.coeff (4*t) b q *
          (vweight (Q.biUnion ends)*samples (Q.biUnion ends) (p::q::J))
  calc
    _ = ∑ Q∈A,∑ p∈S,∑ q∈S,F Q p q := by
      apply Finset.sum_congr rfl
      intro Q hQ
      obtain ⟨sub,sz,sep⟩ := (mem_choices E Q).mp hQ
      have szV := matching_ends_card Q (fun e he=>strict _ (sub he)) sep
      rw [grid_double (Q.biUnion ends) (d:=4*t) (by omega) a b J,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      unfold F
      ring
    _ = ∑ p∈S,∑ Q∈A,∑ q∈S,F Q p q := Finset.sum_comm
    _ = ∑ p∈S,∑ q∈S,∑ Q∈A,F Q p q := by
      apply Finset.sum_congr rfl
      intro p _
      exact Finset.sum_comm
    _ = _ := by simp only [moment,F,S,A,Finset.mul_sum]
end L1018

namespace L1018

def place (a : ℕ) : List ℕ → List ℕ
  | [] => [a]
  | b::J => if a≤b then a::b::J else b::place a J

theorem samples_place {n} (V : Finset (Fin n)) (a : ℕ) (J : List ℕ) :
    samples V (place a J)=samples V (a::J) := by
  induction J with
  | nil => rfl
  | cons b J ih =>
    simp only [place]
    split
    · rfl
    · simp only [samples] at ih ⊢
      rw [ih]
      ring

theorem moment_place {n} (E : Finset (Edge n)) (t a b : ℕ) (J : List ℕ) :
    moment E t (place a (place b J)) = moment E t (a::b::J) := by
  unfold moment
  apply Finset.sum_congr rfl
  intro Q _
  simp only [samples_place,samples]

theorem zero_rank {n} (E : Finset (Edge n)) : choices E 0={∅} := by
  ext Q
  rw [mem_choices,Finset.mem_singleton]
  constructor
  · exact fun h => Finset.card_eq_zero.mp h.2.1
  · rintro rfl
    simp

theorem samples_empty {n} (J : List ℕ) : samples (∅ : Finset (Fin n)) J=1 := by
  induction J with
  | nil => rfl
  | cons j J ih => simp [samples,hitFactor,ih]

theorem moment_zero {n} (E : Finset (Edge n)) (J : List ℕ) : moment E 0 J=1 := by
  simp [moment,zero_rank,samples_empty,vweight]

theorem no_edges {n} (t : ℕ) (J : List ℕ) : moment (∅ : Finset (Edge n)) (t+1) J=0 := by
  simp [moment,choices]

def gridEval {n} : List (Edge n) → ℕ → List ℕ → ℤ
  | [],t,_ => if t=0 then 1 else 0
  | _::_,0,_ => 1
  | e::tail,t+1,J =>
    gridEval tail (t+1) J + quadFactor e.1 e.2 * pairSamples e.1.val e.2.val J *
    ∑ p∈Finset.range (4*t+1),∑ q∈Finset.range (4*t+1),
      Grid1018.coeff (4*t) e.1.val p * Grid1018.coeff (4*t) e.2.val q *
        gridEval tail t (place p (place q J))

theorem gridEval_correct {n} (l : List (Edge n)) (nodup : l.Nodup) (strict : ∀ e∈l,e.1<e.2)
    (t : ℕ) (J : List ℕ) : gridEval l t J=moment l.toFinset t J := by
  induction l generalizing t J with
  | nil =>
    cases t with
    | zero => simp [gridEval,moment_zero]
    | succ t => simp [gridEval,no_edges]
  | cons e tail ih =>
    have hn := List.nodup_cons.mp nodup
    have st : ∀ f∈tail,f.1<f.2 := fun f hf => strict f (List.mem_cons_of_mem e hf)
    have st' : ∀ f∈tail.toFinset,f.1<f.2 := fun f hf => st f (List.mem_toFinset.mp hf)
    have fresh : e∉tail.toFinset := fun he => hn.1 (List.mem_toFinset.mp he)
    cases t with
    | zero => simp [gridEval,moment_zero]
    | succ t =>
      rw [List.toFinset_cons,moment_insert _ _ fresh (ne_of_lt (strict e (by simp))) t J,
          moment_grid _ _ _ _ _ st']
      simp only [gridEval,ih hn.2 st,moment_place]

theorem grid_kernel {n} (E : Finset (Edge n)) (strict : ∀ e∈E,e.1<e.2) (k : ℕ) :
    gridEval E.toList k []=kernel k E := by
  classical
  have st : ∀ e∈E.toList,e.1<e.2 := fun e he => strict e (Finset.mem_toList.mp he)
  rw [gridEval_correct _ (Finset.nodup_toList _) st]
  simp only [Finset.toList_toFinset,moment,kernel,samples,mul_one,vandermonde_nat]

theorem signed_grid_eval {n} (E : Finset (Edge n)) (strict : ∀ e∈E,e.1<e.2)
    (k : ℕ) (rows : List (Row n)) :
    (total k E rows : ℤ) = (rows.map fun r=> (rows.map fun s=>
      sign r*sign s*gridEval (E∩r.1∩s.1).toList k []).sum).sum := by
  rw [expanded_kernel]
  congr 1
  apply List.map_congr_left
  intro r _
  congr 1
  apply List.map_congr_left
  intro s _
  rw [grid_kernel _ (fun e h => strict e (Finset.mem_inter.mp (Finset.mem_inter.mp h).1).1)]
end L1018
