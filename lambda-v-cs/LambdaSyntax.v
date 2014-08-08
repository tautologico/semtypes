
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

(** Equivalence up to alpha conversion. *)

Fixpoint assoc_var (l : list (var * var)) (v : var) : option var := 
  match l with
      nil => None
    | (v1, v2) :: rl => if beq_nat v v1 then Some v2 else assoc_var rl v
  end.

Import ListNotations. 

Example assoc_var_1 : assoc_var [(1, 5); (2, 7); (11, 8)] 3 = None. 
Proof. reflexivity. Qed. 

Example assoc_var_2 : assoc_var [(1, 5); (2, 7); (11, 8)] 2 = Some 7. 
Proof. reflexivity. Qed. 

Fixpoint sub_var (ls : list (var * var)) (v : var) : var := 
  match assoc_var ls v with
    | None => v
    | Some v' => v'
  end.

Definition next_var (v : var) : var := S v. 

Definition var_fresh {A : Type} (v : var) (t : term A) : Prop := 
  forall v' : var, set_In v' (variables t) -> v > v'. 

Definition var_fresh2 {A : Type} (v : var) (t1 t2 : term A) : Prop := 
  forall v' : var, 
    set_In v' (set_union eq_nat_dec (variables t1) (variables t2)) -> v > v'. 

(** A representation that's a variation of De Bruijn indices, avoiding the 
  shifting of free variables. Shifting is only used to preserve the identity 
  of free variables when under binders, but here we distinguish free and 
  bound variables in a term explicitly. *)

Module DeBruijnVar. 
  Local Set Implicit Arguments. 

  Inductive dbv_var : Set := 
  | Free : nat -> dbv_var
  | Bound : nat -> dbv_var. 

  Inductive dbv_term (A : Type) : Type := 
  | DBV_const : A -> dbv_term A
  | DBV_var : dbv_var -> dbv_term A
  | DBV_abs : dbv_term A -> dbv_term A
  | DBV_app : dbv_term A -> dbv_term A -> dbv_term A.

  Definition binders := list var.

  Fixpoint find_var_in_binders (bs : binders) (v : var) (i : nat) : option nat := 
    match bs with
      | nil => None
      | v' :: bs' => if beq_nat v v' then Some i 
                     else find_var_in_binders bs' v (S i)
    end.

  Definition var_to_dbv_var (v : var) (bs : binders) : dbv_var := 
    match find_var_in_binders bs v 0 with
      | None => Free v
      | Some i => Bound i
    end. 

  Fixpoint convert_to_dbv_aux {A : Type} (t : term A) (bs : binders) : dbv_term A := 
    match t with
      | Const a => DBV_const a
      | Var v => DBV_var A (var_to_dbv_var v bs)
      | Abs x body => DBV_abs (convert_to_dbv_aux body (x :: bs))
      | App m n => DBV_app (convert_to_dbv_aux m bs) (convert_to_dbv_aux n bs)
    end. 

  Definition convert_to_dbv {A : Type} (t : term A) : dbv_term A := 
    convert_to_dbv_aux t nil. 

  Example dbv_conv_ex1 : 
    convert_to_dbv (\nat\X --> Var X) = (DBV_abs (DBV_var nat (Bound 0))).
  Proof. reflexivity. Qed. 

  Example dbv_conv_ex2 : 
    convert_to_dbv (\nat\X --> (Var X) $ (Var Y)) = 
    (DBV_abs (DBV_app (DBV_var nat (Bound 0)) (DBV_var nat (Free 1)))).
  Proof. reflexivity. Qed. 

  Example dbv_conv_ex3 : 
    convert_to_dbv (\nat\Y --> Var Y) = (DBV_abs (DBV_var nat (Bound 0))).
  Proof. reflexivity. Qed. 

  Example dbv_conv_ex4 : 
    convert_to_dbv (\nat\Y --> (Var Y) $ (Var Z)) = 
    (DBV_abs (DBV_app (DBV_var nat (Bound 0)) (DBV_var nat (Free Z)))).
  Proof. reflexivity. Qed. 

End DeBruijnVar. 

Import DeBruijnVar. 

(** We define alpha equivalence (equivalence of terms up to names of bound variables) 
    by translating terms to our variation of De Bruijn representation and checking if 
    they're equal. *)

Definition alpha_equiv {A : Type} (t1 t2 : term A) : Prop := 
  convert_to_dbv t1 = convert_to_dbv t2. 

(** printing == %\ensuremath{\equiv}% *)

Notation "t1 == t2" := (alpha_equiv t1 t2) (at level 20, no associativity). 


Theorem alpha_equiv_refl : forall (A : Type) (t : term A), t == t. 
Proof. 
  reflexivity. 
Qed. 

Theorem alpha_equiv_sym : forall (A : Type) (t1 t2 : term A), 
                            t1 == t2 -> t2 == t1. 
Proof. 
  intros A t1 t2 H12; unfold alpha_equiv in H12; apply eq_sym in H12; assumption. 
Qed. 

Theorem alpha_equiv_trans : forall (A : Type) (t1 t2 t3 : term A),
                              t1 == t2 -> t2 == t3 -> t1 == t3. 
Proof. 
  intros A t1 t2 t3 H12 H23. 
  unfold alpha_equiv in H12. unfold alpha_equiv in H23. rewrite H23 in H12. assumption. 
Qed. 

Inductive aequiv {A : Type} : var -> term A -> term A -> Prop := 
| ae_const : forall v a b, a = b -> aequiv v (Const a) (Const b)
| ae_var : forall v x y, x = y -> aequiv v (Var x) (Var y)
| ae_app : forall v m1 m2 n1 n2, aequiv v m1 m2 -> aequiv v n1 n2 -> 
                                 aequiv v (App m1 n1) (App m2 n2)
| ae_abs_sv : forall v x b1 b2, aequiv v b1 b2 -> aequiv v (Abs x b1) (Abs x b2)
| ae_abs : forall v x1 x2 b1 b2, 
             var_fresh v b1 -> var_fresh v b2 -> 
             aequiv (next_var v) (alpha_convert b1 x1 v) (alpha_convert b2 x2 v) -> 
             aequiv v (Abs x1 b1) (Abs x2 b2).

Definition alpha_eq {A : Type} (t1 t2 : term A) : Prop := 
  aequiv (fresh_variable2 t1 t2) t1 t2. 

Theorem aequiv_refl : forall (A : Type) (v : var) (t : term A), aequiv v t t. 
Proof. 
  intros A v t. 
  induction t; constructor; try reflexivity; try assumption. 
Qed. 

Theorem alpha_eq_refl : forall (A : Type) (t : term A), alpha_eq t t. 
Proof. 
  intros; apply aequiv_refl. 
Qed. 

Theorem aequiv_sym : forall (A : Type) (v : var) (t1 t2 : term A), 
                       aequiv v t1 t2 -> aequiv v t2 t1. 
Proof. 
  intros A v t1 t2 H12. 
  induction H12; constructor; try apply eq_sym; assumption. 
Qed. 

Theorem alpha_eq_sym : forall (A : Type) (t1 t2 : term A),
                         alpha_eq t1 t2 -> alpha_eq t2 t1. 
Proof. 
  intros. apply aequiv_sym. rewrite fresh2_sym. assumption. 
Qed. 

Theorem aequiv_trans : forall (A : Type) (v : var) (t1 t2 t3 : term A),
                         aequiv v t1 t2 -> aequiv v t2 t3 -> aequiv v t1 t3. 
Proof. 
  intros A v t1 t2 t3 H12 H23. generalize dependent t3.  
  assert (H12' : aequiv v t1 t2). assumption. 
  induction H12. 
    intros; rewrite H; assumption.
    intros; rewrite H; assumption. 
    intros. inversion H23. 
      apply ae_app; [ apply IHaequiv1 | apply IHaequiv2 ]; assumption. 
    intros. inversion H23. 
      apply ae_abs_sv. apply IHaequiv; assumption. 
      apply ae_abs. admit. assumption. 
    

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
