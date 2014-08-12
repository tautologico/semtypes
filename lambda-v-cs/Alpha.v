Require Import List. 
Require Import LambdaSyntax.
Require Import DBVar. 

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

(** We define alpha equivalence (equivalence of terms up to names of bound variables) 
    by translating terms to our variation of De Bruijn representation and checking if 
    they're equal. *)

Definition alpha_equiv {A : Type} (t1 t2 : term A) : Prop := 
  term_to_dbv t1 = term_to_dbv t2. 

(** printing == %\ensuremath{\equiv}% *)

(** If [t1] and [t2] are terms, we note equivalence up to names of bound 
 variables as [t1 == t2]. This is an equivalence relation. *)

(* begin hide *)
Notation "t1 == t2" := (alpha_equiv t1 t2) (at level 20, no associativity). 
(* end hide *)

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

Theorem equal_alpha_eq : forall (A : Type) (t1 t2 : term A),
                                t1 = t2 -> t1 == t2. 
Proof. 
  intros A t1 t2 Heq. rewrite Heq. apply alpha_equiv_refl. 
Qed. 

(** Equivalence of terms converted to and from a DeBruijn variation. *)

Fixpoint well_formed_aux {A : Type} (dt : dbv_term A) (b : nat) : bool := 
  match dt with
    | DBV_const _ => true
    | DBV_var (Free _) => true
    | DBV_var (Bound n) => leb (S n) b
    | DBV_abs body => well_formed_aux body (S b)
    | DBV_app m n => andb (well_formed_aux m b) (well_formed_aux n b)
  end. 

Lemma well_formed_var : forall (A : Type) (v n : nat),
                          well_formed_aux (DBV_var A (Bound v)) n = true -> 
                          v < n.
Proof. 
  intros A v n H. 
  simpl in H. destruct n. inversion H. apply le_lt_n_Sm. apply leb_complete. assumption. 
Qed. 

Lemma well_formed_higher : forall (A : Type) (dt : dbv_term A) (n : nat),
                             well_formed_aux dt n = true -> well_formed_aux dt (S n) = true. 
Proof. 
  intros A dt. induction dt. 
  (* Case dt = DBV_const *) reflexivity. 

  (* Case dt = DBV_var *) 
  intros n H. simpl. destruct d. reflexivity. 
  apply well_formed_var in H. apply leb_correct. apply lt_le_weak; assumption. 

  (* Case dt = DBV_abs *)
  intros n H. 
  simpl. simpl in H. apply IHdt. assumption. 

  (* Case dt = DBV_app *)
  intros n H. simpl in H. simpl. apply andb_prop in H. 
  apply andb_true_intro. split; [ apply IHdt1 | apply IHdt2 ]; tauto. 
Qed. 
  
(* 
Lemma convert_well_formed_higher : 
  forall (A : Type) (t : term A) v ls n,
    well_formed_aux (convert_to_dbv_aux t ls) n = true -> 
    well_formed_aux (convert_to_dbv_aux t (v::ls)) (S n) = true. 
Proof. 
  intros A t v ls n H. 
  induction t. simpl. 


Lemma convert_well_formed : forall (A : Type) (t : term A),
                              well_formed_aux (convert_to_dbv t) 0 = true.
Proof. 
  intros A t. 
  induction t. 
  reflexivity. reflexivity. 
  simpl. apply well_formed_higher. 
*)

Lemma to_from_dbv_eq : forall (A : Type) (dt : dbv_term A),
                         well_formed_aux dt 0 = true -> 
                         convert_to_dbv (dbv_to_term dt) = dt.
Proof. 
  intros A dt H. unfold dbv_to_term. unfold convert_to_dbv. induction dt. 
  (* Case dt = DBV_const a *) reflexivity. 
  
  (* Case dt = DBV_var *) 
  simpl. destruct d. reflexivity. 
  assert (Hcontra: well_formed_aux ([| n # A |]) 0 = false). 
  reflexivity. congruence. 

  (* Case dt = DBV_abs dt *)
  simpl. f_equal.

  (* Case dt = dt1 $$ dt2 *)
  simpl. 

Theorem from_to_dbv_equiv : forall (A : Type) (t : term A),
                              dbv_to_term (convert_to_dbv t) == t.
Proof. 
  intros A t. induction t. 

  (* Case t = Var v *) reflexivity. 

  (* Case t = Const a *) reflexivity. 

  (* Case t = Abs v t *) unfold alpha_equiv. 
  unfold convert_to_dbv. simpl. 