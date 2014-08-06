
Require Import Arith.
Require Import List. 
Require Import ListSet. 
Require Import SetUtil. 
Require Import Tactics. 

(** * The $\Lambda$ #Lambda# language 

This is the syntax of $\lambda$ #lambda# terms. 
*)

(** For simplicity, variables are identified with the natural numbers. *)

Definition var := nat.

Inductive term (A : Type) : Type :=
| Var : var -> term A
| Const : A -> term A 
| Abs : var -> term A -> term A 
| App : term A -> term A -> term A.

(** We declare the type arguments for constructors as implicits. *)

Arguments Var [A] _.
Arguments Const [A] _. 
Arguments Abs [A] _ _. 
Arguments App [A] _ _. 

(** Notations to help with building terms. The notations for abstraction and 
    application were inspired by Haskell syntax, with a little kludge for the 
    case when the type argument cannot be inferred automatically. *)

Notation "\ x --> M" := (Abs x M) (at level 60, right associativity). 
Notation "\ T \ x --> M" := (Abs (A := T) x M) (at level 60, right associativity).
Notation "M $ N" := (App M N) (at level 60, right associativity). 

Inductive natconst : Type := 
| NConst : nat -> natconst
| Succ : nat -> natconst
| Pred : nat -> natconst. 

Definition lambda_nat := term natconst. 

(** Some variables for use in terms: *)

Definition X := 0.
Definition Y := 1.
Definition Z := 2. 

(** Example terms in the natconst type: *)

Definition natconst_term_1 : lambda_nat := Const (NConst 0). 

(** Example terms in nat type: *)

Definition nat_term_1 := Const 0. 
Definition nat_term_2 := \X --> nat_term_1. 
Definition nat_term_3 := Var (A := nat) X. 
Definition nat_term_4 := \nat\X --> (Var X). 

Fixpoint freevars {A : Type} (t : term A) : set var := 
  match t with
    | Const _ => nil
    | Var v => v :: nil
    | Abs v body => set_remove eq_nat_dec v (freevars body)
    | App m n => set_union eq_nat_dec (freevars m) (freevars n)
  end.

Fixpoint boundvars {A : Type} (t : term A) : set var := 
  match t with
    | Const _ => nil
    | Var _ => nil
    | Abs v body => set_add eq_nat_dec v (boundvars body)
    | App m n => set_union eq_nat_dec (boundvars m) (boundvars n)
  end.

Fixpoint variables {A : Type} (t : term A) : set var := 
  match t with
    | Const _ => nil
    | Var v => v :: nil
    | Abs v body => set_add eq_nat_dec v (variables body)
    | App m n => set_union eq_nat_dec (variables m) (variables n)
  end.

Fixpoint max_var {A : Type} (t : term A) : var := 
  match t with
    | Const _ => 0
    | Var v => v
    | Abs v body => max (max_var body) v
    | App m n => max (max_var m) (max_var n)
  end. 

Fixpoint max_list_aux (l : list nat) (m : nat) : nat :=
  match l with
      nil => m
    | n :: l' => if leb n m then max_list_aux l' m else max_list_aux l' n
  end.

Definition max_list (l : list nat) := max_list_aux l 0. 

Definition fresh_variable {A : Type} (t : term A) : var := 
  S (max_list (boundvars t)). 

Definition fresh_variable2 {A : Type} (t1 t2 : term A) : var := 
  S (max (max_var t1) (max_var t2)).


(** ** Substitution and the Substitution Lemma *)

(** Convert term [t], considered the body of an abstraction bound,
 to use variable [v2] in place of [v1]. *)

Fixpoint alpha_convert {A : Type} (t : term A) (v1 v2 : var) : term A := 
  match t with
    | Const _ => t
    | Var x => if beq_nat x v1 then Var v2 else t
    | Abs x body => if beq_nat x v1 then t else Abs x (alpha_convert body v1 v2)
    | App m n => App (alpha_convert m v1 v2) (alpha_convert n v1 v2)
  end. 

Example alpha_convert1 : alpha_convert nat_term_3 X Y = (Var Y). 
Proof. reflexivity. Qed. 

(** Shift all bound variables by the same amount. *)

Fixpoint shift_bound {A : Type} (t : term A) (inc : nat) : term A := 
  match t with
    | Const _ => t
    | Var _ => t 
    | Abs x body => Abs (x + inc) (alpha_convert (shift_bound body inc) x (x+inc))
    | App m n => App (shift_bound m inc) (shift_bound n inc)
  end.

Example shift_bound_ex1 : shift_bound (A := nat) (Var 0) 10 = Var 0. 
Proof. reflexivity. Qed. 

Example shift_bound_ex2 : shift_bound (A := nat) (\0 --> Var 0) 10 = (\10 --> Var 10).
Proof. reflexivity. Qed. 

Example shift_bound_ex3 : 
  shift_bound (A := nat) ((\0 --> \1 --> Var 0 $ Var 1) $ Var 1) 10 = 
  (\10 --> \11 --> Var 10 $ Var 11) $ (Var 1). 
Proof. reflexivity. Qed. 

(** Substitute [t] for [v] in term [orig], assuming that the bound variables in 
 [orig] are disjunct from the free variables in [t]. *)

Fixpoint subst_aux {A : Type} (orig : term A) (v : var) (t : term A) : term A := 
  match orig with
    | Const _ => orig
    | Var x => if beq_nat x v then t else orig
    | Abs x body => if eq_nat_dec x v then orig else Abs x (subst_aux body v t) (* assumes no capture will happen *)
    | App m n => App (subst_aux m v t) (subst_aux n v t)
  end.

(** Substitute [t] for [v] in term [orig], alpha-converting bound variables to 
    a fresh variable not present in [t] or [orig]. *)

Fixpoint subst_fresh {A : Type} (orig : term A) (v : var) (t : term A) : term A := 
  match orig with
    | Const _ => orig
    | Var x => if beq_nat x v then t else orig
    | Abs x body => if eq_nat_dec x v then orig 
                    else let v' := fresh_variable2 orig t in 
                         Abs v' (alpha_convert body v v')
    | App m n => App (subst_fresh m v t) (subst_fresh n v t)
  end.


(** Makes all bound variables in [rator] different from every free variable in 
 [rand], using the fact that variables are represented as numbers: the idea is 
 to find the highest free variable in [rand], then shift all bound variables 
 in [rator] by one plus this amount. *)

Definition freshen_boundvars {A : Type} (rator rand : term A) : term A := 
  shift_bound rator (S (max_list (freevars rand))).

Definition subst {A : Type} (orig : term A) (v : var) (t : term A) : term A := 
  subst_aux (freshen_boundvars orig t) v t. 

Notation "M [ x := N ]" := (subst M x N) (at level 50, left associativity).

Example subst_ex_1 : (Var (A := nat) X)[X := Var Y][Y := Var Z] = Var Z. 
Proof. reflexivity. Qed. 

Example subst_ex_2 : 
  (\nat\Y --> Var X $ Var Y)[X := \Z --> Var Y] <> 
  (\Y --> (\Z --> Var Y) $ Var Y). 
Proof. discriminate 1. Qed. 

(** The substitution lemma for [subst_aux]. *)

Lemma subst_aux_diff_var : forall (A : Type) x y (M : term A),
                             x <> y -> subst_aux (Var x) y M = Var x. 
Proof. 
  intros A x y M H. 
  simpl. replace (beq_nat x y) with (false).
  reflexivity. apply eq_sym. rewrite -> beq_nat_false_iff. intuition.
Qed. 

Lemma subst_aux_same_var : forall (A : Type) x (M : term A),
                             subst_aux (Var x) x M = M. 
Proof. 
  intros A x M. simpl. rewrite <- beq_nat_refl. reflexivity. 
Qed. 

Lemma not_in_set_then_diff : forall (A : Type) x v (M : term A),
                               M = Var v -> ~(set_In x (freevars M)) ->
                               v <> x.
Proof. 
  intros A x v M Hm Hnotin. 
  rewrite -> Hm in Hnotin. simpl in Hnotin. intuition. 
Qed. 
  
Lemma not_free_abs_not_free : forall (A : Type) x v (M : term A),
                                x <> v -> 
                                ~(set_In x (freevars (\v --> M))) ->
                                ~(set_In x (freevars M)).
Proof.
  intros A x v M Hneq Hnin. simpl in Hnin. 
  apply not_in_remove_not_in_set with (y := v) (Aeq_dec := eq_nat_dec); assumption. 
Qed. 

Lemma subst_non_free : forall (A : Type) x (M N : term A),
                         ~(set_In x (freevars M)) -> 
                         subst_aux M x N = M. 
Proof. 
  intros A x M N H. induction M. 

  (* Case M = Var v *)
  apply not_in_set_then_diff with (v := v) in H. 
  apply subst_aux_diff_var. assumption. reflexivity. 

  (* Case M = Const _ *) reflexivity. 

  (* Case M = Abs v M *)
  simpl.
  destruct (eq_nat_dec v x). reflexivity. f_equal. apply IHM. 
  apply not_free_abs_not_free with (v := v). apply (not_eq_sym n). assumption. 

  (* Case M = App M1 M2 *)
  simpl in H. 
  simpl; f_equal; 
    [ apply IHM1 | apply IHM2 ]; intro Hcontra;  apply H; 
    [ apply set_union_intro1 | apply set_union_intro2 ]; apply Hcontra. 
Qed. 

(* TODO: Define the hygiene conditions and use them in the lemma *)
Definition hygienic2 (A : Type) (M N : term A) : Prop := 
  (boundvars M) >< (freevars N) /\ (freevars M) >< (boundvars N). 

Section hygiene. 
  Variable A : Type. 
  Local Set Implicit Arguments. 
  
  Inductive free_not_bound : term A -> list (term A) -> Prop := 
  | fnb_nil : forall (t : term A), free_not_bound t nil
  | fnb_cons : forall (t1 t2 : term A) (ts : list (term A)), 
                 (freevars t1) >< (boundvars t2) -> 
                 free_not_bound t1 ts -> 
                 free_not_bound t1 (t2 :: ts). 

  Lemma fnb_app : forall (t : term A) (ts1 ts2 : list (term A)),
                    free_not_bound t (ts1 ++ ts2) -> free_not_bound t ts2. 
  Proof. 
    intros t ts1 ts2 Hfnb. 
    induction ts1 as [ | t' ts1' ]. 
    (* Case ts1 = nil *)
    rewrite app_nil_l in Hfnb. assumption. 
    (* Case ts1 = t' :: ts1' *)
    apply IHts1'. inversion Hfnb. assumption. 
  Qed. 

  Lemma fnb_split : forall (t1 t2 : term A) (ts : list (term A)),
                      free_not_bound t1 ts -> In t2 ts -> 
                      exists ts' : list (term A), free_not_bound t1 (t2 :: ts'). 
  Proof. 
    intros t1 t2 ts Hfnb Hin. 
    apply in_split in Hin. 
    destruct Hin as [ ts1 [ ts2 ] ]. 
    rewrite H in Hfnb. apply fnb_app in Hfnb. 
    exists ts2. 
    assumption. 
  Qed. 

  Lemma disjunct_free_not_bound : forall (t1 t2 : term A) x,
                                    (freevars t1) >< (boundvars t2) -> 
                                    set_In x (freevars t1) -> 
                                    ~(set_In x (boundvars t2)). 
  Proof. 
    intros t1 t2 x Hdis Hin. 
    intro Hcontra. 
    Admitted. 

  Theorem free_in_term_not_bound : 
    forall (t1 : term A) x (ts : list (term A)),
      free_not_bound t1 ts -> set_In x (freevars t1) -> 
      (forall t2 : term A, In t2 ts -> ~(set_In x (boundvars t2))).
  Proof. 
    intros t1 x ts Hfnb Hin t2 Hin2. 
    apply fnb_split with (t2 := t2) in Hfnb. inversion Hfnb. 
    Admitted. 

End hygiene. 

(* 
Fixpoint and_all (lp : list Prop) : Prop := 
  match lp with
    | nil => True
    | p1 :: nil => p1
    | p1 :: lp' => p1 /\ (and_all lp')
  end.

Fixpoint hygienic {A : Type} (ts : list (term A)) : Prop := 
  match ts with
      nil => True
    | t :: nil => True
    | t :: ts' => (and_all (map (fun t2 => (boundvars t) >< (freevars t2)) ts')) /\
                  (and_all (map (fun t2 => (freevars t) >< (boundvars t2)) ts')) /\
                  hygienic ts'
  end.

Lemma in_split2_dec : forall (A : Type) x y (l l1 l2 l3 : list A),
                        In x l -> In y l -> 
                        {l = l1 ++ (x :: l2) ++ (y :: l3)} + {l = l1 ++ (y :: l2) ++ (x :: l3)}.
Proof. 
  intros A x y l l1 l2 l3 Hin1 Hin2. 

Lemma hygienic_free_bound : forall (A : Type) (ts : list (term A)) (t1 t2 : term A),
                              hygienic ts -> In t1 ts -> In t2 ts -> 
                              (freevars t1) >< (boundvars t2).
Proof. 
  intros A ts t1 t2 Hhyg Hin1 Hin2. 
  
Theorem hygienic_free_not_bound : 
  forall (A : Type) x (t1 t2 : term A) (ts : list (term A)),
    hygienic ts -> In t1 ts -> In t2 ts -> 
    set_In x (freevars t1) -> ~(set_In x (boundvars t2)).
Proof. 
  intros A x t1 t2 ts Hhyg Hin1 Hin2 Hx. 
  
Import ListNotations. 
*)

(* Substitution lemma for [subst_aux] *)
Lemma subst_aux_lemma : forall (A : Type) x y (M N L : term A), 
                             x <> y -> ~(set_In x (freevars L)) ->
                             set_inter eq_nat_dec (boundvars M) (freevars N) = empty_set nat ->
                             subst_aux (subst_aux M x N) y L = subst_aux (subst_aux M y L) x (subst_aux N y L).
Proof. 
  intros A x y M N L Hneq Hnfree Hdis. 
  induction M. 

  (* M = Var v *)
  destruct (eq_nat_dec v x). 
    (* Case v = x *)
    rewrite e. rewrite subst_aux_same_var. rewrite subst_aux_diff_var. 
    rewrite subst_aux_same_var. reflexivity. apply Hneq. 
    (* Case v <> x *)
    rewrite subst_aux_diff_var. destruct (eq_nat_dec v y). 
      (* Case v = y *)
      rewrite e. rewrite subst_aux_same_var. apply eq_sym. 
      apply subst_non_free. apply Hnfree. 
      (* Case v <> y *)
      repeat rewrite subst_aux_diff_var; try reflexivity; try apply n; try apply n0. 
      apply n. 
    
  (* M = Const a *) reflexivity. 

  (* M = Abs v M' *)
  simpl. 
  destruct (eq_nat_dec v x). 
    
    
  (* M = App M N *)
  Admitted. 
  

(** The substitution lemma. *)

Lemma substitution_lemma : forall (A : Type) x y (M N L : term A), 
                             x <> y -> ~(set_In x (freevars L)) ->
                             M[x := N][y := L] = M[y := L][x := N[y := L]].
Proof. 
  intros A x y M N L Hneq Hnfree. 
  induction M. 
  destruct (eq_nat_dec v x). rewrite e. 
  Admitted. 
