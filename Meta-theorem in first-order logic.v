(* ******************************** *)
(* 本文件参考余俊伟教授的《数理逻辑》一书 *)
(* ******************************** *)

Require Import Coq.Sets.Ensembles.
Require Import Coq.Logic.Epsilon.
Require Import Coq.Logic.Classical.

Notation "a ∈ A" := (In _ A a) (at level 10).
Notation "B ∪ C" := (Union _ B C) (at level 65, left associativity).
Notation "[ a ]" := (Singleton _ a)
                    (at level 0, right associativity).
Notation "A ⊆ B" := (Included _ A B) (at level 70).
Notation "A ~ B" := (Setminus _ A B)
                    (at level 0, right associativity).

(* 集合性质 *)
Corollary UnionI : forall {U} (a: U) B C, 
  a ∈ (B ∪ C) <-> a ∈ B \/ a ∈ C.
Proof. 
  split; intros; destruct H; eauto with sets. 
Qed.

Corollary Single : forall {U} (a x: U), a ∈ [ x ] <-> a = x.
Proof. split; intros. destruct H; auto. rewrite H. split. Qed.

Global Hint Resolve UnionI Single: sets.

(* 一阶语言符号 *)
(*个体变元*)
Inductive Var : Set :=
  | X : nat -> Var.

(*个体常元*)
Inductive Con : Set :=
  | C : nat -> Con.

(*运算符*)
(* Inductive Fun : Set :=
  | F : nat -> Fun. *)
  
Inductive Fun : Set :=
  | F : nat -> nat -> Fun.

(*谓词*)
(* Inductive Rel : Set :=
  | R : nat -> Rel. *)

Inductive Rel : Set :=
  | R : nat -> nat -> Rel.

(* 元数（arity）函数 *)
Definition arity_f (f : Fun) : nat :=
  match f with
  | F a b => a
  end.

Definition arity_r (r : Rel) : nat :=
  match r with
  | R a b => a
  end.

Definition arity_F f := S (arity_f f).
Definition arity_R r := S (arity_r r).

(* P74 项 *)
Inductive vector (A: Type) : nat -> Type :=
  |vector0 : vector A 0
  |vectorcons : forall (h:A) (n:nat), vector A n -> vector A (S n).

Inductive term : Set :=
  | Tvar : Var -> term
  | Tcon : Con -> term
  | Tfun : forall f: Fun, vector term (arity_F f) -> term.


(* 变元相关性质 *)
Fixpoint eqb (n m: nat) : bool :=
  match n with
  | 0 => match m with
         | 0 => true
         | S _ => false
         end
  | S n' => match m with
            | 0 => false
            | S m' => eqb n' m'
            end
  end.

Definition eqbv (n m: Var) : bool :=
  match n, m with
  | X p, X q => eqb p q
  end.

Corollary eq_n : forall n, eqb n n = true.
Proof.
  intros. induction n.
  - auto.
  - simpl. auto.
Qed.

Corollary eqbv_n : forall n, eqbv n n = true.
Proof.
  intros. induction n. simpl. apply eq_n.
Qed.

Corollary eqb_true : forall (m n: nat), eqb m n = true <-> m = n.
Proof.
  intros. split; intros. 
  - generalize dependent n. induction m; intros.
    + inversion H. destruct n; auto. discriminate H1.
    + inversion H. destruct n; auto. discriminate H.
  - rewrite H. apply eq_n.
Qed.

Corollary eqb_false : forall (m n: nat), eqb m n = false <-> m <> n.
Proof.
  intros. split; intros; generalize dependent n; induction m.
  - intros; inversion H; destruct n; auto.
    + discriminate H1.
  - intros. destruct n; intro; rewrite H0 in H;
    rewrite eq_n in H; inversion H.
  - intros. destruct n. assert(0 = 0). auto. apply H in H0. 
    inversion H0. simpl. auto.
  - intros. destruct n. 
    + simpl. auto.
    + simpl. apply IHm. intro. rewrite H0 in H. apply H. auto.
Qed.

Corollary eqbv_true : forall (m n: Var), eqbv m n = true <-> m = n.
Proof.
  intros. split; intros; destruct m; destruct n. 
  - simpl in H. f_equal. apply eqb_true. auto.
  - inversion H. simpl. apply eq_n.
Qed.

Corollary eqbv_fasle : forall (m n: Var), 
  eqbv m n = false <-> m <> n.
Proof.
  intros. split; intros; destruct m; destruct n.
  - simpl in H. intro. inversion H0.
    rewrite H2 in H.  rewrite eq_n in H. inversion H.
  - simpl. apply eqb_false. intro. apply H. congruence. 
Qed.


(* P75 公式 *)
Section Formula.

Inductive Formula :=
  | equality : term -> term -> Formula
  | atomic : forall (r: Rel), vector (term) (arity_R r) -> Formula
  | Not : Formula -> Formula
  | Contain : Formula -> Formula -> Formula 
  | Forall : Var -> Formula -> Formula.

(* 其他符号 *)
Definition Inequality t1 t2 := Not (equality t1 t2). 
(* ∨ *)
Definition Disjunction p q := Contain (Not p) q.
(* ∧ *)
Definition Conjunction p q := Not (Contain p (Not q)).
(* ↔ *)
Definition Equivalent p q := Conjunction (Contain p q) (Contain q p).

Definition Exists x p := Not (Forall x (Not p)).

End Formula.


Notation "¬ q" := (Not q)(at level 5,right associativity).

Notation "p → q" := (Contain p q)
                    (at level 11,right associativity).

Notation "∀ x , p" := (Forall x p) 
                       (at level 7, right associativity).

Notation " p ∨ q " := (Disjunction p q)
                      (at level 11, right associativity).
 
Notation " p ∧ q " := (Conjunction p q)
                      (at level 9, right associativity).

Notation " p ↔ q " := (Equivalent p q)
                      (at level 12, right associativity).

Notation "∃ x , p" := (Exists x p)
                      (at level 8, right associativity).

Theorem excluded : forall p, {p} + {~p}.
Proof.
  intros. assert { x:bool | if x then p else ~p }.
  { apply constructive_indefinite_description.
    destruct (classic p).
    - exists true. auto.
    - exists false. auto. }
  destruct H,x; auto.
Qed.

Definition Φ := @Empty_set Var.

Fixpoint term_Ens (t: term) :=
  match t with
  | Tcon c => Φ
  | Tvar x => [x]
  | Tfun  _ q => let fix Vector_Ens (n: nat) (r: vector (term) n) :=
                   match r with 
                   | vector0 _ => Φ 
                   | vectorcons _ h _ q => (term_Ens h) ∪ 
                                           (Vector_Ens _ q)
                   end in Vector_Ens _ q
  end. 

Fixpoint Vector_Ens (n: nat) (r: vector (term) n) :=
  match r with 
  | vector0 _ => Φ 
  | vectorcons _ h _ q => (term_Ens h) ∪ (Vector_Ens _ q)
  end.

(* 公式的变元集 *)
Fixpoint Formula_Ens (p: Formula) :=
  match p with 
  | equality t1 t2 => (term_Ens t1) ∪ (term_Ens t2)
  | atomic _ q => Vector_Ens _ q
  | Not q => Formula_Ens q
  | Contain m n =>  (Formula_Ens m) ∪ (Formula_Ens n)
  | Forall x q => (Formula_Ens q) ∪ [x]
  end.

(* 公式的自由变元集 *)
Fixpoint Formula_free_Ens (p: Formula) :=
  match p with 
  | equality t1 t2 => (term_Ens t1) ∪ (term_Ens t2)
  | atomic _ q => Vector_Ens _ q
  | Not q => Formula_free_Ens q
  | Contain m n => (Formula_free_Ens m) ∪ (Formula_free_Ens n)
  | Forall x q => (Formula_free_Ens q) ~ [x]
  end.

(* 项t对p中x是自由的 *)
Fixpoint t_x_free (p: Formula) (t: term) (x: Var) :=
  match p with 
  | equality t1 t2 => true
  | atomic _ q => true 
  | Not q => t_x_free q t x
  | Contain m n => andb (t_x_free m t x) (t_x_free n t x)
  | Forall y q => match (excluded (x ∈ (Formula_free_Ens p))) with
                    | left _ => match 
                              (excluded (y ∈ (term_Ens t))) with
                              | left _ => false
                              | right _ => t_x_free q t x
                              end
                    | right _ => true
                  end
  end.
  
  Fixpoint substitute_t (t t': term) (x: Var) :=
  match t with
  | Tcon c => Tcon c
  | Tvar y => if (eqbv x y) then t' else Tvar y 
  | Tfun  _ q => let fix substitute_v (n: nat) (r: vector (term) n)
                   (t': term) (x: Var) :=
                   match r with 
                    | vector0 _ => vector0 _
                    | vectorcons _ h _ q => vectorcons _ 
                    (substitute_t h t' x) _ (substitute_v _ q t' x) 
                   end in (Tfun _ (substitute_v _ q t' x))
  end.

Fixpoint substitute_v (n: nat) (r: vector (term) n) 
  (t': term) (x: Var) :=
  match r with 
  | vector0 _ => vector0 _
  | vectorcons _ h _ q => vectorcons _ (substitute_t h t' x) _
                          (substitute_v _ q t' x)
  end.
(* t'对p中x的代入 *)
Fixpoint substitute_f (p: Formula) (t': term) (x: Var) :=
  match p with 
  | equality t1 t2 => equality (substitute_t t1 t' x) 
                      (substitute_t t2 t' x) 
  | atomic _ q => atomic _ (substitute_v _ q t' x) 
  | Not q => Not (substitute_f q t' x)
  | Contain m n => Contain (substitute_f m t' x)
                   (substitute_f n t' x)
  | Forall y q => if (eqbv x y) then Forall y q
                  else Forall y (substitute_f q t' x)
  end.
  Fixpoint equality_4 (r: Formula) (m n: nat) (v1: vector(term) m) 
  (v2: vector (term) n) :=
  match v1 with
  | vector0 _ => r
  | vectorcons _ h _ s => match v2 with
                          | vector0 _ => r
                          | vectorcons _ l _ t => (equality h l) 
                            → (equality_4 r _ _ s t)
                          end
  end. 

(* P116 3.4 公理系统 *) 
Section Propositional_calculus.

Variable Γ: Ensemble Formula.

Inductive Axiom_system : Formula -> Prop :=
  | P1 : forall p q , Axiom_system (p → (q → p))
  | P2 : forall p q r, Axiom_system 
         ((p → (q → r)) → ((p → q) → (p → r)))
  | P3 : forall p q, Axiom_system ((¬p → q)→ ((¬p → ¬q) → p))
  | S' : forall p x t, t_x_free p t x = true ->
         Axiom_system ((∀ x , p) → (substitute_f p t x))
  | D' : forall p x q, Axiom_system 
         ((∀ x , (p → q)) → (∀ x , p) → (∀ x , q)) 
  | E1 : forall t, Axiom_system (equality t t)
  | E2 : forall t1 t2, Axiom_system 
         ((equality t1 t2) → (equality t2 t1))
  | E3 : forall t1 t2 t3, Axiom_system 
         ((equality t1 t2) → (equality t2 t3)→ (equality t1 t3))
  | E4 : forall r v1 v2, Axiom_system 
         (equality_4 (( atomic r v1)→ ( atomic r v2)) _ _ v1 v2)
  | E5 : forall f v1 v2, Axiom_system 
         (equality_4 (equality (Tfun f v1) (Tfun f v2)) _ _ v1 v2)
  | C1 : forall x p, ~ (x ∈ (Formula_free_Ens p)) -> 
         Axiom_system (p → (∀ x , p))
  | C2 : forall x p, Axiom_system p -> Axiom_system (Forall x p).

(* P122 证明与演绎 *)
Inductive deduce_K (Γ: Ensemble Formula) : Formula -> Prop :=
| K0 : forall p, p ∈ Γ -> deduce_K Γ p
| K1 : forall p, Axiom_system p -> deduce_K Γ p
| MP : forall p q, deduce_K Γ (p → q) -> deduce_K Γ p ->
       deduce_K Γ q.

End Propositional_calculus.

Notation " ├ p " := (deduce_K (@Empty_set Formula) p)(at level 80).
(* 语法蕴涵 *)
Notation " Γ ├ p " := (deduce_K Γ p)(at level 80).

(*语法等价*) 
Definition syntactically_equivalent p q :=
 [p] ├ q /\  [q] ├ p.

Global Hint Constructors Axiom_system deduce_K : LD.

Fact Union_l : forall Γ p, Γ ├ p -> forall A, Γ ∪ A ├ p.
Proof. intros. induction H; eauto with LD sets. Qed.

Fact Union_r : forall Γ p, Γ ├ p -> forall A, A ∪ Γ ├ p.
Proof. intros. induction H; eauto with LD sets. Qed.

Fact Union_r_A : forall A p, A ├ p -> forall Γ, Γ ∪ A ├ p.
Proof. intros. induction H; eauto with LD sets. Qed.

Fact Union_l_A : forall A p, A ├ p -> forall Γ, A ∪ Γ ├ p.
Proof. intros. induction H; eauto with LD sets. Qed.

Ltac autoL :=
  match goal with
  | H: ?Γ ├ ?p |- ?Γ ∪ ?A ├ ?p => apply Union_l; auto
  | H: ?Γ ├ ?p |- ?A ∪ ?Γ ├ ?p => apply Union_r; auto
  | H: ?a ∈ Φ |- _ => destruct H
  | H: ?Γ ├ ?p ,
    H1: ?Γ ├ ?p → ?q
    |- ?Γ ├ ?q => apply MP with p; autoL
  | H: ?Γ ├ ?p
    |- ?Γ ├ ?q → ?p =>
      let H0 := fresh in
      assert (H0: Γ ├ p → (q → p)) by ( apply K1; apply P1;constructor); autoL
  | H1: ?Γ ├ ¬?p  → ¬?q,
    H2: ?Γ ├ ¬?p  → ?q
    |- ?Γ ├ ?p =>
     assert (H0:Γ ├ (¬p → q)→ ((¬  p → ¬q) → p)) by (apply 
     K1;apply P3;constructor);autoL
  | |- ?Γ ├ ?x => eauto with LD sets
  | |- forall a, ?Q => intros; autoL
  end.

Ltac ES := 
  match goal with
  | H: ?a ∈ Φ |- _ => destruct H
  | H: ?p0 ∈ [?p] |- _ => apply Single in H; rewrite H in *; ES
  | H: ?a ∈ (?B ∪ ?C) |- _ => apply UnionI in H; ES
  | |- ?a ∈ (?B ∪ ?C) => apply UnionI; ES
  | H: ?B \/ ?C |- _ => destruct H; ES
  | H: ?B /\ ?C |- _ => destruct H; ES
  | |- forall a, ?Q => intros; ES
  | |- ?P <-> ?Q => split; intros; ES
  | |- _ => eauto with sets
  end.

Ltac Single_Union :=
  match goal with 
  | |- ?Γ ∪ [?p] ├ ?q => assert(Γ ∪ [p] ├ p); autoL
  end.

Fact L_3_4_11 : forall Γ p q x, ~ x ∈ (Formula_free_Ens p) /\ 
  ~ x ∈ (Formula_free_Ens q) -> 
  Γ ├ (p → q) → (∀ x , p) → (∀ x , q).
Proof.
   intros. pose proof (K1 Γ _ (D' p x q)). pose proof(K1 Γ _ 
   (P1 ((∀ x, (p → q) → ∀ x, p → ∀ x, q)) (p → q))).
   assert(Γ ├ (p → q) → ∀ x, (p → q) → ∀ x, p → ∀ x, q) by 
   (apply MP with (p:= ∀ x, (p → q) → ∀ x, p → ∀ x, q); auto).
   pose proof (K1 Γ _  (P2 (p → q) (∀ x, (p → q)) 
   (∀ x, p → ∀ x, q))). assert(Γ ├ ((p → q) → ∀ x, (p → q)) → 
   ((p → q) → ∀ x, p → ∀ x, q)) by ( apply MP with (p:= 
   (p → q) →(∀ x, (p → q) → ∀ x, p → ∀ x, q)); auto).
   assert(~ x ∈ (Formula_free_Ens (p → q))). { 
   intro. inversion H5; destruct H; eauto. }
   pose proof (K1 Γ _ (C1 x (p → q) H5)). 
   apply MP with (p:= (p → q) → ∀ x, (p → q)); auto.
Qed.

(* P122 *)
(* 命题1 同一律 |- p→p *)
Theorem law_identity : forall Γ p, Γ ├ p → p.
Proof.
  intros. assert(Γ ├  p →( p → p) → p) by autoL. autoL.
Qed. 

Global Hint Resolve law_identity : LD. 

(* P124 演绎定理  *)
Theorem Deductive_Theorem' : forall Γ p q, Γ ∪[p] ├ q <-> Γ ├ p → q.
Proof.
  split; intros.
  - induction H. 
    + destruct H. pose proof ((K1 Γ (x → p → x)) (P1 x p)). 
      apply MP with (p:=x); auto. apply K0; auto.
      apply Single in H. rewrite H. apply law_identity.
    + apply K1 with (Γ:=Γ) in H. 
      pose proof ((K1 Γ (p0 → p → p0)) (P1 p0 p)). 
      apply MP with (p:=p0); auto.
    + pose proof (K1 Γ ((p → p0 → q) → (p → p0)→ (p → q)) (P2 p p0 q)).
      apply MP with (p:=(p → p0)); auto. 
      apply MP with(p:= p → p0 → q); auto.
  - apply MP with p. apply Union_l; auto. apply K0. right. 
    apply Single. auto.
Qed.
Theorem Deductive_Theorem : forall Γ p q, Γ ∪[p] ├ q <-> Γ ├ p → q.
Proof.
  split; intros.
  - induction H;repeat (autoL; ES).
  - apply MP with p; autoL.
Qed.

(*P125 3.4.25 反证律*)
Theorem rule_Indirect : forall Γ p q, Γ ∪ [¬p] ├ q -> 
  Γ ∪ [¬p] ├ ¬q -> Γ ├ p.
Proof.
  intros. apply Deductive_Theorem in H0,H. autoL.
Qed.

Global Hint Resolve rule_Indirect: LD.

(* 推论 双重否定律 *)
Corollary law_double_negation_aux : forall p, [¬¬p] ├ p.
Proof. 
  intros. pose proof (rule_Indirect [¬¬p] p ¬p).
  apply H; autoL.
Qed.

Global Hint Resolve law_double_negation_aux :LD.

Corollary law_double_negation : forall  Γ p, Γ ├ ¬¬p → p.
Proof.
  intros; apply Deductive_Theorem. apply Union_r_A.
  autoL.
Qed.

Global Hint Resolve law_double_negation : LD.

(* 推论 假设三段论 *)
Corollary Syllogism' : forall p q r, 
  [p → q] ∪ [q → r] ├ p → r.
Proof.
  intros. apply -> Deductive_Theorem. 
  assert (([p → q] ∪ [q → r]) ∪ [p] ├ p ) by autoL.
  assert (([p → q] ∪ [q → r]) ∪ [p] ├ q ) by autoL.
  autoL.
Qed.

Theorem syllogism : forall Γ p q r, 
  Γ ∪ [p] ├ q -> Γ ∪ [r] ├ p -> Γ ∪ [r] ├ q.
Proof.
  intros. apply Deductive_Theorem in H. 
  apply Deductive_Theorem in H0.
  assert (Γ ∪ [r] ├ r) by autoL.
  pose proof (Union_l Γ (p → q) H [r] ).
  pose proof (Union_l Γ (r → p) H0 [r]).    
  autoL.
Qed.

Theorem syllogism' : forall Γ p q r, Γ ├ p → q -> 
  Γ ├ r → p -> Γ ├ r → q.
Proof.
  intros. apply Deductive_Theorem in H,H0. apply Deductive_Theorem.
  eauto using syllogism.
Qed.

(* 3.4.27 归谬律 law of reduction to absurdity *)
Theorem rule_Reduction_absurdity : forall Γ p q,
  Γ ∪ [p] ├ q -> Γ ∪ [p] ├ ¬q -> Γ ├ ¬p.
Proof.
  intros. assert (Γ ∪ [¬¬p] ├ q).     
  { eapply syllogism; autoL. } 
  assert (Γ ∪ [¬¬p] ├ ¬q). { eapply syllogism; autoL. }
  apply (rule_Indirect Γ (¬p) q H1 H2); auto.
Qed.

Lemma double_neg : forall p Γ, Γ ├ p → ¬¬p.
Proof. 
  intros. apply Deductive_Theorem. pose proof 
  (rule_Reduction_absurdity (Γ ∪ [p]) (¬p) p).
  apply H; autoL.
Qed.

(* 推论3.4.26 假言易位 *)
(* 换位律 *)
Theorem Transposition_2 : forall Γ p q, Γ ├ (¬p → ¬q) → (q → p).
Proof.
  intros. apply Deductive_Theorem.
  apply Deductive_Theorem with (p:= q).
  pose proof(rule_Indirect (Γ ∪ [¬p → ¬q] ∪ [q]) p q).
  apply H; autoL. apply MP with (p:= ¬p); autoL.
Qed.

Theorem Transposition_1 : forall Γ p q, Γ ├ (p → q) → (¬q → ¬p).
Proof.
  intros. apply Deductive_Theorem.
  assert(Γ ∪ [p → q] ├ ¬¬p → p) by autoL.
  pose proof (double_neg q (Γ ∪ [p → q])). Single_Union.
  assert(Γ ∪ [p → q] ├ ¬¬p → q). { apply syllogism' with p; auto. }
  assert(Γ ∪ [p → q] ├ ¬¬p → ¬¬q). { apply syllogism' with q; 
  auto. } apply MP with (p:= ¬¬ p → ¬¬ q). apply Transposition_2.
  auto.
Qed.

Theorem Transposition_3 : forall p q Γ, Γ ├ (p → ¬q) → (q → ¬p).
Proof.
  intros; repeat (apply -> Deductive_Theorem).
  apply (@rule_Reduction_absurdity (Γ ∪ [p → ¬q] ∪ [q]) p q); 
  autoL. apply MP with p; autoL.
Qed.

Theorem Transposition_4 : forall p q Γ, Γ ├ (¬p → q) → (¬q → p).
Proof.
  intros; repeat (apply -> Deductive_Theorem).
  assert(Γ ∪ [¬p → q] ∪ [¬q] ∪ [¬p] ├ q). { 
  apply MP with (¬p); autoL. } 
  assert(Γ ∪ [¬p → q] ∪ [¬q] ∪ [¬p] ├ ¬q). autoL. 
  pose proof (@rule_Reduction_absurdity (Γ ∪ [¬p → q] ∪
  [¬q]) (¬p) q) H H0. apply MP with (¬¬p). autoL. apply H1.
Qed.

Global Hint Resolve Transposition_2: LD.

(* 否定前件律 *)
Theorem law_deny_antecedent : forall Γ p q, Γ ├ ¬q → (q → p).
Proof. 
  intros. apply MP with (p:= ¬q → ¬p → ¬q); autoL.
Qed.

(* 引理 否定肯定律 (¬p→p)→p *)
Lemma law_negetion_affirmation : forall Γ p, Γ ├ (¬p → p) → p.
Proof.
  intros. apply -> Deductive_Theorem.
  assert (Γ ∪ [¬p → p] ├ (¬p → p) → (¬p → ¬(¬p → p))).
  { apply MP with (p:= ¬p → p → ¬(¬p → p)).
  pose proof ( K1 (Γ ∪ [¬p → p]) _ (P2  (¬p) p ¬(¬p → p))).
  auto. apply law_deny_antecedent. }
  assert (Γ ∪ [¬p → p] ├ ¬p → ¬(¬p → p)). {
  apply MP with (p:= ¬p → p). auto. autoL. }
  apply MP with (p:= ¬p → p); autoL.
Qed.

Global Hint Resolve law_negetion_affirmation law_identity : LD.
