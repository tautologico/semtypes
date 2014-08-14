
Require Import Arith. 
Require Import Omega. 
Require Import List.
Require Import LambdaSyntax.

(** Representation using DeBruijn indices. *)

Set Implicit Arguments. 

Inductive db_term (A : Type) : Type := 
| db_const : A -> db_term A
| db_var : var -> db_term A
| db_app : db_term A -> db_term A -> db_term A
| db_abs : db_term A -> db_term A.

Arguments db_var [A] _. 

Notation "\\ M" := (db_abs M) (at level 60, right associativity). 
Notation "M $$ N" := (db_app M N) (at level 60, right associativity). 
Notation "[ v ]" := (db_var v) (at level 40, no associativity). 
Notation "[ v # T ]" := (db_var (A := T) v) (at level 40, no associativity). 

Definition binders := list var.

Fixpoint find_var_in_binders (bs : binders) (v : var) (i : nat) : option nat := 
  match bs with
    | nil => None
    | v' :: bs' => if beq_nat v v' then Some i 
                   else find_var_in_binders bs' v (S i)
  end.

Definition map_var (v : var) (lv : nat) (bs : binders) : var := 
  match find_var_in_binders bs v 0 with
    | None => v + lv
    | Some i => i
  end. 

Fixpoint term_to_db_aux {A : Type} (t : term A) (bs : binders) (lv : nat) : db_term A := 
  match t with
    | Const a => db_const a 
    | Var v => db_var (map_var v lv bs)
    | App m n => db_app (term_to_db_aux m bs lv) (term_to_db_aux n bs lv)
    | Abs x body => db_abs (term_to_db_aux body (x::bs) (S lv))
  end.

Definition term_to_db {A : Type} (t : term A) : db_term A := 
  term_to_db_aux t nil 0.

Example term_to_db_ex1 : 
  term_to_db (\X # nat --> Var X) = (\\ (db_var 0)).
Proof. reflexivity. Qed. 

Example term_to_db_ex2 : 
  term_to_db (\X # nat --> (Var X) $ (Var Y)) = 
  \\ ((db_var 0) $$ (db_var 2)).
Proof. reflexivity. Qed. 

Example term_to_db_ex3 : 
  term_to_db (\Y # nat --> Var Y) = (\\ (db_var 0)).
Proof. reflexivity. Qed. 

Example term_to_db_ex4 : 
  term_to_db (\Y # nat --> (Var Y) $ (Var Z)) = 
  (\\ ((db_var 0) $$ (db_var (S Z)))).
Proof. reflexivity. Qed. 

Example term_to_db_ex5 : 
  term_to_db ((Var 4) $ ((Var 3) $ (Var 2))) =
  ((db_var 4) $$ ((db_var 3) $$ [2 # nat])).
Proof. reflexivity. Qed. 

Example term_to_db_ex6 : 
  term_to_db (\ 7 --> (Var 3) $ (Var 7)) = 
  (\\ [4 # nat] $$ [0]).
Proof. reflexivity. Qed. 

Example term_to_db_ex7 : 
  term_to_db (\ 7 --> (\ 8 --> (Var 4))) = 
  (\\ (\\ [6 # nat])). 
Proof. reflexivity. Qed. 

Definition db_var_to_var (n i v : var) : var := 
  if leb (S n) i then (v + i - n) else (n - i). 

Fixpoint db_to_term_aux {A : Type} (dt : db_term A) (i v : var) : term A := 
  match dt with
    | db_const a => Const a
    | db_var n => Var (db_var_to_var n i v)
    | db_app m n => App (db_to_term_aux m i v) (db_to_term_aux n i v)
    | db_abs body => Abs (v + (S i)) (db_to_term_aux body (S i) v)
  end. 

Fixpoint max_free_var {A : Type} (dt : db_term A) (lv : nat) : nat := 
  match dt with
    | db_const _ => 0
    | db_var v => (v - lv)
    | db_app m n => max (max_free_var m lv) (max_free_var n lv) 
    | db_abs body => max_free_var body (S lv)
  end. 

Definition db_to_term {A : Type} (dt : db_term A) : term A := 
  db_to_term_aux dt 0 (max_free_var dt 0).

Example dbv_to_term_1 : db_to_term (\\ [0 # nat]) = (Abs 1 (Var 1)).
Proof. reflexivity. Qed. 

Example dbv_to_term_2 : 
  db_to_term (\\ ([0 # nat] $$ [2])) = 
  (\2 --> (Var 2) $ (Var 1)). 
Proof. reflexivity. Qed. 

Lemma dbvar_to_var_zero : forall (n v : var), 
                            db_var_to_var n 0 v = n. 
Proof. 
  intros n v. 
  unfold db_var_to_var. 
  replace (leb (S n) 0) with (false). apply eq_sym. apply minus_n_O. 
  apply eq_sym. apply leb_correct_conv. apply lt_0_Sn. 
Qed. 

Lemma mapvar_nil : forall v lv, map_var v lv nil = v + lv. 
Proof. 
  intros v lv. unfold map_var. simpl. reflexivity. 
Qed. 

Lemma maxvar_app : forall (A : Type) v n (dt1 dt2 : db_term A),
                     v >= max_free_var (dt1 $$ dt2) n -> 
                     v >= max_free_var dt1 n /\ v >= max_free_var dt2 n. 
Proof. 
  intros A v n dt1 dt2 Hgeq. simpl in Hgeq. 
  apply NPeano.Nat.max_lub_iff in Hgeq. assumption. 
Qed. 
  
(* 
Lemma from_to_dbv_vars : 
  forall (A : Type) v (dt : db_term A),
    term_to_db_aux (db_to_term_aux dt 1 v) (v + 1 :: nil) 1 = 
    term_to_db_aux (db_to_term_aux dt 0 v) nil 0.
Proof. 
  intros A v dt. induction dt. 
  (* Case dt = db_const *) reflexivity. 

  (* Case dt = db_var *)
  simpl. rewrite dbvar_to_var_zero. 
*)

Fixpoint range_n_v (n : nat) (v : var) : list var := 
  match n with 
    | 0 => nil
    | S n' => (v + n) :: (range_n_v n' v)
  end.

Lemma n_gt_0_Sn : forall n, 
                    n > 0 -> (exists n', n = S n'). 
Proof. 
  intros n H. destruct n eqn:E. inversion H. 
  exists n0. reflexivity. 
Qed. 

Lemma n_gt_Sv_Sn : forall n v,
                     n > S v -> (exists n', n = S n').
Proof. 
  intros n v H. destruct n eqn:E. inversion H. exists n0. reflexivity. 
Qed. 

Lemma v_lt_n_0 : forall n v, v < n -> 0 < n - v. 
Proof. 
  intros; omega. 
Qed. 
  
Lemma range_struct : forall n n' v,
                       n = S n' -> 
                       range_n_v n v = (v + n) :: range_n_v n' v. 
Proof. 
  intros. rewrite H. reflexivity. 
Qed. 

Lemma find_in_range2 : forall v0 n v,
                        v < n -> 
                        find_var_in_binders (range_n_v n v0) (v0 + n - v) 0 = Some v.
Proof. 
  intros. destruct v. apply n_gt_0_Sn in H. inversion H. 
  apply range_struct with (v := v0) in H0. rewrite H0. simpl. 
  replace (beq_nat (v0 + n - 0) (v0 + n)) with (true). reflexivity. 
  rewrite <- minus_n_O. apply beq_nat_refl. 
  apply n_gt_Sv_Sn in H. inversion H. 
  apply range_struct with (v := v0) in H0. rewrite H0. simpl.
Admitted. 

Lemma find_in_range : forall v0 n v i,
                        v < n -> i <= v -> 
                        find_var_in_binders (range_n_v (n - i) v0) (v0 + n - v) i = Some v.
Proof. 
  intros. assert (Hlt: i < n). omega. apply v_lt_n_0 in Hlt. 
  apply n_gt_0_Sn in Hlt. inversion Hlt. 
  apply range_struct with (v := v0) (n := n - i) in H1. rewrite H1. 
  simpl. 

  (* Case v = 0 *)
  inversion H0. 
  apply n_gt_0_Sn in H. inversion H. rewrite <- minus_n_O. 
  apply range_struct with (v := v0) in H2. rewrite H2. simpl. 
  replace (beq_nat (v0 + n - 0) (v0 + n)) with (true). reflexivity. 
  rewrite <- minus_n_O. apply beq_nat_refl. 

  (* Case v = S v *)
  assert (Hlt: i < n). omega. 
  apply v_lt_n_0 in Hlt. 
  apply n_gt_0_Sn in Hlt. inversion Hlt. 
  apply range_struct with (v := v0) (n := n - i) in H1. rewrite H1. 
  simpl. replace (beq_nat (v0 + n - S v) (v0 + (n - S v))) with (true). reflexivity. 
  replace (v0 + (n - S v)) with (v0 + n - S v). apply beq_nat_refl. 
  omega.
Qed. 

Lemma mapvar_in_range : forall v0 n v, 
                          (S v) <= n ->  
                          map_var (v0 + n - v) n (range_n_v n v0) = v.
Proof. 
  intros. unfold map_var. rewrite find_in_range2. reflexivity. 
  omega. 
Qed. 

Lemma mapvar_out_of_range : forall v n v0, 
                              (v - n) <= v0 -> 
                              map_var (v - n) n (range_n_v n v0) = v. 
Proof. 
  intros. Admitted. 

Theorem from_to_dbv_aux : 
  forall (A : Type) (dt : db_term A) v n,
    v >= (max_free_var dt n) -> 
    term_to_db_aux (db_to_term_aux dt n v) (range_n_v n v) n = dt.
Proof. 
  intros A dt. 
  induction dt. 

  (* Case dt = db_const *) reflexivity. 

  (* Case dt = db_var *)
  intros. simpl in H. 
  simpl. unfold db_var_to_var. destruct (leb (S v) n) eqn:E. 
  apply leb_complete in E. rewrite mapvar_in_range. reflexivity. assumption.
  rewrite mapvar_out_of_range. reflexivity. auto. 

  (* Case dt = dt_app *)
  intros. simpl. apply maxvar_app in H. 
  rewrite IHdt1; try rewrite IHdt2; try reflexivity; tauto. 

  (* Case dt = db_abs *)
  intros. simpl. f_equal. apply IHdt. simpl in H. assumption. 
Qed. 
