import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_393_aux

def mass : List Nat → Nat
  | [] => 0
  | x::xs => x + xs.sum + mass xs

def live : List Nat → Nat
  | [] => 0
  | x::xs => (if x = 0 then 0 else 1) + live xs

def quarter (xs : List Nat) := xs.map (· / 4)
def cost : Nat → List Nat → Nat
  | 0, _ => 0
  | f+1, xs => live xs + cost f (quarter xs)

lemma live_le_sum (xs : List Nat) : live xs ≤ xs.sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : x=0 <;> simp [live,h] <;> omega

lemma live_tri (xs : List Nat) : live xs * live xs + live xs ≤ 2*mass xs := by
  induction xs with
  | nil => decide
  | cons x xs ih =>
    have hh := live_le_sum xs
    by_cases eq : x=0
    · simp [mass,live,eq]; omega
    · have xpos : 1≤x := by omega
      simp [mass,live,eq]; nlinarith

lemma quarter_sum (xs : List Nat) : 4*(quarter xs).sum ≤ xs.sum := by
  induction xs with
  | nil => simp [quarter]
  | cons x xs ih =>
    change 4*(x/4+(quarter xs).sum) ≤ x+xs.sum
    omega

lemma quarter_mass (xs : List Nat) : 4*mass (quarter xs) ≤ mass xs := by
  induction xs with
  | nil => decide
  | cons x xs ih =>
    have hs := quarter_sum xs
    change 4*(x/4+(quarter xs).sum+mass (quarter xs)) ≤ x+xs.sum+mass xs
    omega

theorem cost_bound (fuel : Nat) (xs : List Nat) :
    cost fuel xs ≤ 2 * Nat.sqrt (2*mass xs) := by
  induction fuel generalizing xs with
  | zero => exact Nat.zero_le _
  | succ f ih =>
    have low : live xs ≤ Nat.sqrt (2*mass xs) :=
      Nat.le_sqrt.mpr (by have := live_tri xs; nlinarith)
    have small : 2 * Nat.sqrt (2 * mass (quarter xs)) ≤ Nat.sqrt (2 * mass xs) := by
      apply Nat.le_sqrt.mpr
      have hh := Nat.sqrt_le (2 * mass (quarter xs))
      have hq := quarter_mass xs
      nlinarith
    change live xs + cost f (quarter xs) ≤ _
    have := ih (quarter xs)
    omega

def writeCell : Nat → Nat → List (Fin 5)
  | 0, _ => [4]
  | f+1, x => if x=0 then [4] else ⟨x%4,by omega⟩ :: writeCell f (x/4)

def decode : List (Fin 5) → List Nat
  | [] => []
  | a::as => if a.val=4 then 0 :: decode as else
      match decode as with
      | [] => []
      | x::xs => (4*x+a.val) :: xs

lemma decode_cell (f x : Nat) (h : x≤f) (tail : List (Fin 5)) :
    decode (writeCell f x ++ tail) = x :: decode tail := by
  induction f generalizing x with
  | zero => have eq : x=0 := by omega
            simp [eq,writeCell,decode]
  | succ f ih =>
    by_cases eq : x=0
    · simp [eq,writeCell,decode]
    · simp only [writeCell,if_neg eq,List.cons_append,decode]
      rw [if_neg (show x%4 ≠ 4 by omega),ih (x/4) (by omega)]
      change (4*(x/4)+x%4) :: decode tail = x :: decode tail
      rw [show 4*(x/4)+x%4=x by omega]

def encode (f : Nat) (xs : List Nat) := xs.flatMap (writeCell f)

lemma decode_many (f : Nat) (xs : List Nat) (h : ∀ x∈xs,x≤f) (tail : List (Fin 5)) :
    decode (encode f xs ++ tail) = xs ++ decode tail := by
  induction xs with
  | nil => simp [encode]
  | cons x xs ih =>
    change decode ((writeCell f x ++ encode f xs) ++ tail) = _
    rw [List.append_assoc,decode_cell f x (h _ (by simp)),ih (fun k hk => h _ (by simp [hk]))]
    rfl

lemma write_zero (f : Nat) : writeCell f 0 = [4] := by cases f <;> simp [writeCell]

lemma cost_cons (f x : Nat) (xs : List Nat) :
    cost f (x::xs) + 1 = (writeCell f x).length + cost f xs := by
  induction f generalizing x xs with
  | zero => simp [writeCell,cost]
  | succ f ih =>
    have hh := ih (x/4) (quarter xs)
    by_cases eq : x=0
    · subst x
      simp only [Nat.zero_div,write_zero,List.length_cons,List.length_nil] at hh
      simp [writeCell,cost,live,quarter] at hh ⊢
      omega
    · change ((if x=0 then 0 else 1) + live xs + cost f ((x/4)::quarter xs)) + 1 =
        (writeCell (f+1) x).length + (live xs + cost f (quarter xs))
      simp only [eq,if_false,writeCell,List.length_cons]
      omega

lemma encode_length (f : Nat) (xs : List Nat) :
    (encode f xs).length = xs.length + cost f xs := by
  induction xs with
  | nil =>
    have zero (k : Nat) : cost k []=0 := by induction k <;> simp_all [cost,live,quarter]
    simp [encode,zero]
  | cons x xs ih =>
    change (writeCell f x ++ encode f xs).length = _
    rw [List.length_append,ih,List.length_cons]
    have := cost_cons f x xs
    omega

theorem inventory_code_bound (N : Nat) (xs : List Nat)
    (size : xs.length ≤ Nat.sqrt (2*N)) (wt : mass xs ≤ N) :
    (encode N xs).length ≤ 3 * Nat.sqrt (2*N) := by
  rw [encode_length]
  have a := cost_bound N xs
  have b : Nat.sqrt (2*mass xs) ≤ Nat.sqrt (2*N) := Nat.sqrt_le_sqrt (by omega)
  omega

def compact : Nat → List Nat → List (Nat × Nat)
  | _, [] => []
  | b, x::xs => if x=0 then compact (b+1) xs else (b+1,x)::compact 0 xs

def unpack : List (Nat × Nat) → List Nat
  | [] => []
  | (g,c)::xs => List.replicate (g-1) 0 ++ [c] ++ unpack xs

def area : Nat → List (Nat × Nat) → Nat
  | _, [] => 0
  | b, (g,c)::xs => (b+g)*c + area (b+g) xs

lemma area_compact (b skip : Nat) (xs : List Nat) :
    area b (compact skip xs) = (b+skip)*xs.sum + mass xs := by
  induction xs generalizing b skip with
  | nil => simp [area,compact,mass]
  | cons x xs ih =>
    by_cases h : x=0
    · simp [compact,h,mass,ih]; ring
    · simp [compact,h,area,mass,ih]; ring

lemma positive_compact (skip : Nat) (xs : List Nat) :
    ∀ t∈compact skip xs, 0<t.1 ∧ 0<t.2 := by
  induction xs generalizing skip with
  | nil => simp [compact]
  | cons x xs ih =>
    by_cases h : x=0
    · simpa [compact,h] using ih (skip+1)
    · simp only [compact,if_neg h,List.mem_cons]
      rintro t (rfl|ht)
      · exact ⟨by omega,by omega⟩
      · exact ih 0 t ht

lemma unpack_compact (skip : Nat) (xs : List Nat) :
    ∃ z, List.replicate skip 0 ++ xs = unpack (compact skip xs) ++ List.replicate z 0 := by
  induction xs generalizing skip with
  | nil => exact ⟨skip,by simp [unpack,compact]⟩
  | cons x xs ih =>
    by_cases h : x=0
    · obtain ⟨z,hz⟩ := ih (skip+1)
      refine ⟨z,?_⟩
      simpa [compact,h,List.replicate_succ',List.append_assoc] using hz
    · obtain ⟨z,hz⟩ := ih 0
      simp only [List.replicate_zero,List.nil_append] at hz
      refine ⟨z,?_⟩
      calc
        _ = List.replicate skip 0 ++ x :: (unpack (compact 0 xs) ++ List.replicate z 0) := congrArg (fun t => List.replicate skip 0 ++ x :: t) hz
        _ = _ := by simp [compact,h,unpack,List.append_assoc]

lemma mass_append (xs ys : List Nat) :
    mass (xs ++ ys) = mass xs + xs.length*ys.sum + mass ys := by
  induction xs with
  | nil => simp [mass]
  | cons x xs ih => simp [mass,ih,List.sum_append]; ring

lemma area_mult (xs : List (Nat×Nat)) (b : Nat)
    (pos : ∀ t∈xs, 0<t.1 ∧ 0<t.2) :
    b*(xs.map Prod.snd).sum + mass (xs.map Prod.snd) ≤ area b xs := by
  induction xs generalizing b with
  | nil => simp [mass,area]
  | cons t xs ih =>
    rcases t with ⟨g,c⟩
    have gp := (pos (g,c) (by simp)).1
    change 0<g at gp
    have h := ih (b+g) (fun t ht => pos _ (.tail _ ht))
    simp only [List.map_cons, List.sum_cons,Prod.snd,mass,area]
    nlinarith [Nat.mul_le_mul_right c (show 1≤g by omega),
      Nat.mul_le_mul_right ((xs.map Prod.snd).sum) (show 1≤g by omega)]

lemma area_gap (xs : List (Nat×Nat)) (b : Nat)
    (pos : ∀ t∈xs, 0<t.1 ∧ 0<t.2) :
    b*xs.length + mass (xs.map Prod.fst).reverse ≤ area b xs := by
  induction xs generalizing b with
  | nil => simp [mass,area]
  | cons t xs ih =>
    rcases t with ⟨g,c⟩
    have cp := (pos (g,c) (by simp)).2
    change 0<c at cp
    have h := ih (b+g) (fun t ht => pos _ (.tail _ ht))
    simp [List.reverse_cons,mass_append,mass,area]
    nlinarith [Nat.mul_le_mul_left (b+g) (show 1≤c by omega)]

lemma live_pos (xs : List Nat) (h : ∀ x∈xs, 0<x) : live xs = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx : x≠0 := Nat.ne_of_gt (h _ (by simp))
    simp [live,hx,ih (fun y hy => h y (.tail _ hy)),Nat.add_comm]

lemma entry_le_mass (xs : List Nat) (x : Nat) (mem : x∈xs) : x≤mass xs := by
  induction xs with
  | nil => cases mem
  | cons y ys ih =>
    rcases List.mem_cons.mp mem with rfl|h
    · simp [mass]; omega
    · have := ih h; simp [mass]; omega

def profileCode (N : Nat) (xs : List Nat) : List (Fin 5) × List (Fin 5) :=
  let ts := compact 0 xs
  (encode N (ts.map Prod.fst).reverse, encode N (ts.map Prod.snd))

lemma profile_bounds (N : Nat) (xs : List Nat) (bound : mass xs ≤ N) :
    let st := compact 0 xs
    mass (st.map Prod.fst).reverse ≤ N ∧ mass (st.map Prod.snd) ≤ N ∧
      st.length ≤ Nat.sqrt (2*N) := by
  let ts := compact 0 xs
  have ht := positive_compact 0 xs
  have ar : area 0 ts≤N := by simpa [ts,area_compact] using bound
  have h1 := area_gap ts 0 ht
  have h2 := area_mult ts 0 ht
  simp only [Nat.zero_mul,Nat.zero_add] at h1 h2
  have eq : live (ts.map Prod.snd) = ts.length := by
    rw [live_pos,List.length_map]
    intro k hk
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hk
    exact (ht v hv).2
  have h3 := live_tri (ts.map Prod.snd)
  rw [eq] at h3
  exact ⟨h1.trans ar,h2.trans ar,Nat.le_sqrt.mpr (by nlinarith)⟩

theorem profile_short (N : Nat) (xs : List Nat) (bound : mass xs ≤ N) :
    (profileCode N xs).1.length ≤ 3*Nat.sqrt (2*N) ∧
    (profileCode N xs).2.length ≤ 3*Nat.sqrt (2*N) := by
  obtain ⟨a,b,c⟩ := profile_bounds N xs bound
  constructor
  · exact inventory_code_bound N _ (by simpa using c) a
  · exact inventory_code_bound N _ (by simpa using c) b

lemma recover_encode (N : Nat) (xs : List Nat) (bound : mass xs≤N) :
    decode (encode N xs)=xs := by
  simpa [decode] using decode_many N xs (fun x hx => (entry_le_mass xs x hx).trans bound) []

lemma pair_lists {α β : Type} {a b : List (α×β)} (x : a.map Prod.fst=b.map Prod.fst)
    (y : a.map Prod.snd=b.map Prod.snd) : a=b := by
  induction a generalizing b with
  | nil => cases b <;> simp_all
  | cons h t ih =>
    cases b with
    | nil => simp at x
    | cons g r =>
      simp only [List.map_cons,List.cons.injEq] at x y
      rw [Prod.ext x.1 y.1,ih x.2 y.2]

theorem profile_faithful (N : Nat) (xs ys : List Nat) (hx : mass xs≤N) (hy : mass ys≤N)
    (len : xs.length=ys.length) (same : profileCode N xs=profileCode N ys) : xs=ys := by
  obtain ⟨a,b,_⟩ := profile_bounds N xs hx
  obtain ⟨c,d,_⟩ := profile_bounds N ys hy
  have ea := congrArg (fun q : List (Fin 5) × List (Fin 5) => decode q.1) same
  have eb := congrArg (fun q : List (Fin 5) × List (Fin 5) => decode q.2) same
  simp only [profileCode,recover_encode N _ a,recover_encode N _ c] at ea
  simp only [profileCode,recover_encode N _ b,recover_encode N _ d] at eb
  have ec : compact 0 xs=compact 0 ys := pair_lists (by simpa using congrArg List.reverse ea) eb
  obtain ⟨u,hu⟩ := unpack_compact 0 xs
  obtain ⟨v,hv⟩ := unpack_compact 0 ys
  simp only [List.replicate_zero,List.nil_append] at hu hv
  rw [ec] at hu
  have il := congrArg List.length hu
  have ir := congrArg List.length hv
  simp only [List.length_append,List.length_replicate] at il ir
  have uv : u=v := by omega
  exact hu.trans (uv ▸ hv.symm)


def pad (L : Nat) (s : List (Fin 5)) (i : Fin L) : Fin 6 :=
  if h : i.val<s.length then s[i.val].castSucc else 5

lemma pad_inj (L : Nat) (s t : List (Fin 5)) (hs : s.length≤L) (ht : t.length≤L)
    (eq : pad L s=pad L t) : s=t := by
  have notLess (u v : List (Fin 5)) (hv : v.length≤L) (same : pad L u=pad L v) :
      ¬u.length<v.length := by
    intro less
    let i : Fin L := ⟨u.length,by omega⟩
    have atI := congrFun same i
    simp only [pad,show ¬i.val<u.length by simp [i],dif_neg,show i.val<v.length from less,dif_pos] at atI
    have ev := congrArg Fin.val atI
    change 5=(v[u.length]).val at ev
    have := (v[u.length]).isLt
    omega
  have len := Nat.le_antisymm (Nat.le_of_not_gt (notLess t s hs eq.symm))
    (Nat.le_of_not_gt (notLess s t ht eq))
  apply List.ext_getElem len
  intro i hi _
  have k := congrFun eq (⟨i,by omega⟩ : Fin L)
  simp only [pad,dif_pos hi,dif_pos (show i<t.length by omega)] at k
  exact Fin.castSucc_inj.mp k

abbrev Profile (N : Nat) := {f : Fin N → Fin (N+1) // mass (List.ofFn (fun i => (f i).val)) ≤ N}

def codeMap (N : Nat) (p : Profile N) : (Fin (3*Nat.sqrt (2*N))→Fin 6) ×
    (Fin (3*Nat.sqrt (2*N))→Fin 6) :=
  let a := profileCode N (List.ofFn fun i => (p.val i).val)
  (pad _ a.1, pad _ a.2)

lemma codeMap_inj (N : Nat) : Function.Injective (codeMap N) := by
  intro x y eq
  let xs := List.ofFn (fun i => (x.val i).val)
  let ys := List.ofFn (fun i => (y.val i).val)
  have xle := profile_short N xs x.property
  have yle := profile_short N ys y.property
  have left := pad_inj _ _ _ xle.1 yle.1 (congrArg Prod.fst eq)
  have right := pad_inj _ _ _ xle.2 yle.2 (congrArg Prod.snd eq)
  have lists := profile_faithful N xs ys x.property y.property (by simp [xs,ys]) (Prod.ext left right)
  apply Subtype.ext
  funext i
  apply Fin.ext
  have h := congrArg (fun x : List Nat => x.getD i.val 0) lists
  simpa [xs,ys] using h

theorem profile_card (N : Nat) :
    Fintype.card (Profile N) ≤ 2^(18*Nat.sqrt (2*N)) := by
  classical
  let L := 3*Nat.sqrt (2*N)
  have h := Fintype.card_le_of_injective (codeMap N) (codeMap_inj N)
  simp only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin] at h
  have shift : 6^L ≤ 2^(3*L) := by
    calc 6^L ≤ (2^3)^L := Nat.pow_le_pow_left (by decide) _
         _ = 2^(3*L) := (pow_mul 2 3 L).symm
  have both := Nat.mul_le_mul shift shift
  change 6^L*6^L ≤ 2^(3*L)*2^(3*L) at both
  rw [←pow_add 2] at both
  have ex : 3*L+3*L=18*Nat.sqrt (2*N) := by dsimp [L]; omega
  rw [ex] at both
  exact h.trans both

theorem four_color_card (n : Nat) :
    Fintype.card (Fin 4→Profile (2*n)) ≤ 2^(144*(Nat.sqrt n+1)) := by
  have root : Nat.sqrt (2*(2*n)) ≤ 2*(Nat.sqrt n+1) := by
    have a := Nat.sqrt_le (2*(2*n))
    have b := Nat.lt_succ_sqrt n
    nlinarith
  rw [Fintype.card_fun,Fintype.card_fin]
  have h := Nat.pow_le_pow_left (profile_card (2*n)) 4
  rw [←pow_mul] at h
  exact h.trans (Nat.pow_le_pow_right (by decide) (by omega))

end PEqualNP.Outside.L_pcx_393_aux
