import PEqualNP.Defs

set_option maxRecDepth 6000 in
set_option maxHeartbeats 2600000 in
theorem PEqualNP.Outside.R_meta_4919_417
    (mono : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C →
      let enc (x : Fin 42 → Bool) :=
        let y (j : Fin 7) (d : ℕ) := x (Fin.ofNat 42 (21+(3*j.val+d)%21))
        (List.ofFn x ++ List.ofFn (fun j : Fin 7 => y j 5 || y j 17)) ++
          List.ofFn (fun j : Fin 7 => y j 5 || y j 17 || y j 20)
      ∀ x y, (∀ i, x i=true → y i=true) → C.eval (enc x)=true → C.eval (enc y)=true)
    (checkRows : ∀ F : Finset (Fin 21) → Finset (Fin 21) → Bool,
      let I (p l : Fin 21) := (l.val+42-p.val)%21 ∈ ([0,5,7,17,20] : List ℕ)
      (∀ P Q L M, P⊆Q → L⊆M → F P L=true → F Q M=true) →
      (∀ p l, I p l → F {p} {l} = true) →
      (∀ P L, (∀ p, p∈P ↔ ∀ l∈L, ¬I p l) → (∀ l, l∈L ↔ ∀ p∈P, ¬I p l) →
        (P.card≤5 ∨ L.card≤5 ∨ P.card=6 ∧ L.card=6) → F P L = false) →
      ∀ P L, F P L = true ↔ ∃ p∈P, ∃ l∈L, I p l)
    (search : let I (p l : Fin 21) := (l.val+42-p.val)%21 ∈ ([0,5,7,17,20] : List ℕ)
      let enc (x : Fin 42 → Bool) :=
        let y (j : Fin 7) (d : ℕ) := x (Fin.ofNat 42 (21+(3*j.val+d)%21))
        (List.ofFn x ++ List.ofFn (fun j : Fin 7 => y j 5 || y j 17)) ++
          List.ofFn (fun j : Fin 7 => y j 5 || y j 17 || y j 20)
      ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size≤110 ∧
        let F (P L : Finset (Fin 21)) := C.eval (enc (fun i =>
          if i.val<21 then decide (Fin.ofNat 21 i.val∈P) else decide (Fin.ofNat 21 (i.val-21)∈L)))
        (∀ p l, I p l → F {p} {l} = true) ∧
        (∀ P L, (∀ p, p∈P ↔ ∀ l∈L, ¬I p l) → (∀ l, l∈L ↔ ∀ p∈P, ¬I p l) →
          (P.card≤5 ∨ L.card≤5 ∨ P.card=6 ∧ L.card=6) → F P L = false)) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     x1.size ≤ (110 : ℕ) ∧       ∀ (x2 : Fin (42 : ℕ) → Bool),         x1.eval               (have x3 : Fin (7 : ℕ) → ℕ → Bool := fun (x3 : Fin (7 : ℕ)) (x4 : ℕ) => x2 (Fin.ofNat (42 : ℕ) ((21 : ℕ) + ((3 : ℕ) * ↑x3 + x4) % (21 : ℕ)));               (List.ofFn x2 ++ List.ofFn fun (x4 : Fin (7 : ℕ)) => x3 x4 (5 : ℕ) || x3 x4 (17 : ℕ)) ++ List.ofFn fun (x4 : Fin (7 : ℕ)) => x3 x4 (5 : ℕ) || x3 x4 (17 : ℕ) || x3 x4 (20 : ℕ)) =             Bool.true ↔           ∃ (x3 : Fin (42 : ℕ)) (x4 : Fin (42 : ℕ)), (↑x3 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x4 ∧ (↑x4 + (21 : ℕ) - ↑x3) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true := by
  obtain ⟨C,ao,size,h⟩ := search
  refine ⟨C,ao,size,?_⟩
  let enc (x : Fin 42 → Bool) :=
    let y (j : Fin 7) (d : ℕ) := x (Fin.ofNat 42 (21+(3*j.val+d)%21))
    (List.ofFn x ++ List.ofFn (fun j : Fin 7 => y j 5 || y j 17)) ++
      List.ofFn (fun j : Fin 7 => y j 5 || y j 17 || y j 20)
  let asg (P L : Finset (Fin 21)) : Fin 42 → Bool :=
    fun i => if i.val<21 then decide (Fin.ofNat 21 i.val∈P) else decide (Fin.ofNat 21 (i.val-21)∈L)
  let F (P L : Finset (Fin 21)) := C.eval (enc (asg P L))
  let I (p l : Fin 21) := (l.val+42-p.val)%21 ∈ ([0,5,7,17,20] : List ℕ)
  have up : ∀ P Q L M, P⊆Q → L⊆M → F P L=true → F Q M=true := by
    intro P Q L M pq lm hp
    apply mono C ao (asg P L) (asg Q M) _ hp
    intro i
    by_cases hi : i.val < 21
    · simpa only [asg,if_pos hi,decide_eq_true_eq] using @pq (Fin.ofNat 21 i.val)
    · simpa only [asg,if_neg hi,decide_eq_true_eq] using @lm (Fin.ofNat 21 (i.val-21))
  have table : ∀ P L, F P L = true ↔ ∃ p∈P, ∃ l∈L, I p l :=
    checkRows F up h.1 h.2
  intro x
  let P := Finset.univ.filter fun p : Fin 21 => x (Fin.castAdd 21 p)=true
  let L := Finset.univ.filter fun l : Fin 21 => x (Fin.natAdd 21 l)=true
  have eq : x=asg P L := by
    funext i
    by_cases hi : i.val<21
    · have ext : Fin.castAdd 21 (Fin.ofNat 21 i.val)=i := by
        apply Fin.ext
        change i.val % 21=i.val
        exact Nat.mod_eq_of_lt hi
      simp only [asg,if_pos hi,P,Finset.mem_filter,Finset.mem_univ,true_and,ext]
      cases x i <;> decide
    · have lt : i.val-21<21 := by have := i.isLt; omega
      have ext : Fin.natAdd 21 (Fin.ofNat 21 (i.val-21))=i := by
        apply Fin.ext
        change 21+(i.val-21)%21=i.val
        rw [Nat.mod_eq_of_lt lt]
        omega
      simp only [asg,if_neg hi,L,Finset.mem_filter,Finset.mem_univ,true_and,ext]
      cases x i <;> decide
  change C.eval (enc x) = true ↔ _
  calc
    C.eval (enc x)=true ↔ F P L=true := by exact Iff.of_eq (congrArg (fun z => C.eval (enc z)=true) eq)
    _ ↔ ∃ p∈P, ∃ l∈L, I p l := table P L
    _ ↔ _ := by
      constructor
      · rintro ⟨p,hp,l,hl,hit⟩
        refine ⟨Fin.castAdd 21 p,Fin.natAdd 21 l,⟨p.isLt,by change 21≤21+l.val; omega,?_⟩,
          (Finset.mem_filter.mp hp).2,(Finset.mem_filter.mp hl).2⟩
        change (21+l.val+21-p.val)%21 ∈ _
        simpa only [show 21+l.val+21=l.val+42 by omega] using hit
      · rintro ⟨u,v,⟨hu,hv,hit⟩,xu,xv⟩
        let p : Fin 21 := ⟨u.val,hu⟩
        let l : Fin 21 := ⟨v.val-21,by have := v.isLt; omega⟩
        have eu : Fin.castAdd 21 p=u := Fin.ext rfl
        have ev : Fin.natAdd 21 l=v := by apply Fin.ext; change 21+(v.val-21)=v.val; omega
        refine ⟨p,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [eu] using xu⟩,
          l,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [ev] using xv⟩,?_⟩
        change (v.val-21+42-u.val)%21 ∈ _
        simpa only [show v.val-21+42=v.val+21 by omega] using hit
