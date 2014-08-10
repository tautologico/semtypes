
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
Notation "\ x # T --> M" := (Abs (A := T) x M) (at level 60, right associativity).
Notation "M $ N" := (App M N) (at level 60, right associativity). 

(** printing \ %\ensuremath{\lambda}% *)
(** printing --> %\ensuremath{.}% *)
(** printing # %\ensuremath{:}% *)

Inductive natconst : Type := 
| Num : nat -> natconst
| Succ : natconst
| Pred : natconst. 

Definition lambda_nat := term natconst. 

(** Some variables for use in terms: *)

Definition X := 0.
Definition Y := 1.
Definition Z := 2. 

(** Example terms in the natconst type: *)

Definition natconst_term_1 : lambda_nat := Const (Num 0). 
Definition natconst_term_2 : lambda_nat := App (Const (Succ)) (Const (Num 3)). 

(** Example terms in nat type: *)

Definition nat_term_1 := Const 0. 
Definition nat_term_2 := \X --> nat_term_1. 
Definition nat_term_3 := Var (A := nat) X. 
Definition nat_term_4 := \X#nat --> (Var X). 

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

Lemma freevar_le_max : forall (A : Type) (t : term A) v,
                           set_In v (freevars t) -> v <= (max_var t).
Proof. 
  intros A t v Hin. 
  induction t. 
  (* Case t = Var v0 *)
  inversion Hin. rewrite H. reflexivity. inversion H. 
  (* Case t = Const a *)
  inversion Hin. 
  (* Case t = Abs v0 t *)
  simpl. assert (Hle: (max_var t) <= max (max_var t) v0). apply Max.le_max_l. 
  apply le_trans with (m := max_var t). apply IHt. simpl in Hin. 
  apply in_remove_in_orig in Hin. assumption. assumption. 
  (* Case t = App t1 t2 *)
  simpl. simpl in Hin. apply set_union_elim in Hin. inversion Hin. 
  assert (Hle: (max_var t1) <= max (max_var t1) (max_var t2)). apply Max.le_max_l. 
  apply le_trans with (m := max_var t1). apply IHt1. assumption. assumption. 
  assert (Hle: (max_var t2) <= max (max_var t1) (max_var t2)). apply Max.le_max_r. 
  apply le_trans with (m := max_var t2). apply IHt2. assumption. assumption. 
Qed. 

Lemma fresh2_gt_free_l : forall (A : Type) (t1 t2 : term A) v,
                             set_In v (freevars t1) -> v < (fresh_variable2 t1 t2). 
Proof. 
  intros A t1 t2 v Hin. 
  apply freevar_le_max in Hin. unfold fresh_variable2.
  assert (Hmax: (max_var t1) <= max (max_var t1) (max_var t2)). apply Max.le_max_l.
  assert (Hle: v <= max (max_var t1) (max_var t2)). 
  apply le_trans with (m := max_var t1); assumption. 
  apply le_lt_n_Sm. assumption. 
Qed. 

Lemma fresh2_gt_free_r : forall (A : Type) (t1 t2 : term A) v,
                             set_In v (freevars t2) -> v < (fresh_variable2 t1 t2). 
Proof. 
  intros A t1 t2 v Hin. 
  apply freevar_le_max in Hin. unfold fresh_variable2.
  assert (Hmax: (max_var t2) <= max (max_var t1) (max_var t2)). apply Max.le_max_r.
  assert (Hle: v <= max (max_var t1) (max_var t2)). 
  apply le_trans with (m := max_var t2); assumption. 
  apply le_lt_n_Sm. assumption. 
Qed. 

Theorem fresh2_free : forall (A : Type) (t1 t2 : term A),
                        ~(set_In (fresh_variable2 t1 t2) (freevars t1)) /\
                        ~(set_In (fresh_variable2 t1 t2) (freevars t2)). 
Proof. 
  intros A t1 t2. 
  split; intro Hcontra; 
    [ apply fresh2_gt_free_l with (t2 := t2) in Hcontra |
      apply fresh2_gt_free_r with (t1 := t1) in Hcontra ]; 
    apply lt_irrefl in Hcontra; assumption. 
Qed. 

Theorem fresh2_sym : forall (A : Type) (t1 t2 : term A),
                       fresh_variable2 t1 t2 = fresh_variable2 t2 t1. 
Proof. 
  intros. unfold fresh_variable2. f_equal. apply Max.max_comm. 
Qed. 

