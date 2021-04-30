Require Import Metalib.Metatheory.
Require Import Stlc.Definitions.
Require Import Stlc.Lemmas.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.ClassicalFacts.
From Coq Require Import Relations.
From Coq Require Import Init.Nat.
(* We have extended step semantics to deal with stepping within abstractions *)
Fixpoint open_exp_wrt_exp_rec_abs (n:nat) (k:nat) (e_5:exp) (e__6:exp) {struct e__6}: exp :=
  match e__6 with
  | (var_b nat) => 
      match lt_eq_lt_dec nat k with
        | inleft (left _) => var_b nat
        | inleft (right _) => e_5
        | inright _ =>
      match compare nat n with
        | Gt => var_b (nat - 1)
        |  _ => var_b (nat)
end
      end
  | (var_f x) => var_f x
  | (abs e) => abs (open_exp_wrt_exp_rec_abs n (S k) e_5 e)
  | (app e1 e2) => app (open_exp_wrt_exp_rec_abs n k e_5 e1) (open_exp_wrt_exp_rec_abs n k e_5 e2)
end.

Definition open_exp_wrt_exp_abs n e_5 e__6 := open_exp_wrt_exp_rec_abs n 0  e__6 e_5.


Inductive abs_step : nat -> exp -> exp -> Prop :=    (* defn step *)
 | abs_step_beta : forall n (e1 e2:exp),
     abs_step n (app  ( (abs e1) )  e2)  (open_exp_wrt_exp_abs n  e1 e2 ) 
 | abs_step_app : forall n (e1 e2 e1':exp),
     abs_step n e1 e1' ->
     abs_step n (app e1 e2) (app e1' e2)
| abs_step_app_2 : forall n  (e1 e2 e2' :exp),
     abs_step n e2 e2' ->
     abs_step n (app e1 e2) (app e1 e2')
  | abs_step_abs : forall n (e1 e1':exp), abs_step (S n) e1 e1' -> abs_step n (abs e1) (abs e1').

Inductive step : exp -> exp -> Prop :=    (* defn step *)
 | step_beta : forall (e1 e2:exp),
     step (app  ( (abs e1) )  e2)  (open_exp_wrt_exp  e1 e2 ) 
 | step_app : forall (e1 e2 e1':exp),
     step e1 e1' ->
     step (app e1 e2) (app e1' e2)
| step_app_2 : forall (e1 e2 e2' :exp),
     step e2 e2' ->
     step (app e1 e2) (app e1 e2')
  | step_abs : forall (e1 e1':exp), abs_step 0 e1 e1' -> step (abs e1) (abs e1').

Definition relation (X : Type) := X -> X -> Prop.
Inductive star {A : Type} (R : A -> A -> Prop) : nat -> A -> A -> Prop :=
| Zero : forall x, star R 0 x x
| Step : forall x y, R x y -> forall n z, star R n y z -> star R (S n) x z.
Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.
Inductive step_count :  nat -> exp -> exp  -> Prop :=
  | sc_base : forall (e:exp),
    step_count 0 e e 
  | sc_ind : forall (e1 e2 e3:exp) (n:nat),
    step e1 e2 ->
    step_count n e2 e3 ->
    step_count (S n) e1 e3 .

Hint Constructors multi : core .
Hint Constructors step_count : core .

(** (In the [Rel] chapter of _Logical Foundations_ and
    the Coq standard library, this relation is called
    [clos_refl_trans_1n].  We give it a shorter name here for the sake
    of readability.) *)

(** The effect of this definition is that [multi R] relates two
    elements [x] and [y] if

      - [x = y], or
      - [R x y], or
      - there is some nonempty sequence [z1], [z2], ..., [zn] such that

          R x z1
          R z1 z2
          ...
          R zn y.

    Thus, if [R] describes a single-step of computation, then [z1] ... [zn]
    is the sequence of intermediate steps of computation between [x] and
    [y]. *)

(** We write [-->*] for the [multi step] relation on terms. *)
Notation " t '--->' t' " := ((abs_step 0)  t t') (at level 60).
Notation " t '--->*' t' " := (multi (abs_step 0) t t') (at level 60).
Notation " t '-->*' t' " := (multi step t t') (at level 40).
Theorem multi_R : forall (X : Type) (R : relation X) (x y : X),
    R x y -> (multi R) x y.
Proof.
  intros X R x y H.
  apply multi_step with y.
- auto.
  -  apply multi_refl.
Qed.

Theorem multi_other_step : forall (X : Type) (R : relation X) (x y z : X),
multi R x y -> R y z -> multi R x z.
Proof.
intros. 
induction H. 
  - apply multi_R. auto. 
  - apply IHmulti in H0. econstructor. eauto. auto.   
Qed.

(** Third, [multi R] is _transitive_. *)

Theorem multi_trans :
  forall (X : Type) (R : relation X) (x y z : X),
      multi R x y  ->
      multi R y z ->
      multi R x z.
Proof.
  intros X R x y z G H.
  induction H.
    - (* multi_refl *) assumption.
    - (* multi_step *)
       apply IHmulti. apply multi_other_step with x0.  assumption.
      assumption.
Qed.

(* define church numeral *)

Fixpoint remove_abs (e : exp) : exp :=
match e with
  | (abs (abs e1)) => e1
  | _ => (var_b 0)
end.



Fixpoint church_number (n : nat) : exp :=
match n with 
  | 0 =>  (abs (abs (var_b 0)))
  | S n' => (abs (abs (app (var_b 1) (remove_abs (church_number n')))))
end.

Definition c_one := (abs (abs (app (var_b 1) (var_b 0)))).

Definition c_two :=  (abs (abs (app (var_b 1) (app (var_b 1) (var_b 0))))).

Definition c_three :=  (abs (abs (app (var_b 1) (app (var_b 1) (app (var_b 1) (var_b 0)))))).

Definition c_four :=  (abs (abs (app (var_b 1) (app (var_b 1) (app (var_b 1) (app (var_b 1) (var_b 0))))))).
Lemma c_two_eqiv : church_number 2 = c_two.
Proof.
  unfold church_number. simpl. unfold c_two. auto. 
Qed.

Fixpoint c_to_nat_helper (e : exp) : nat :=
match e with 
    | (var_b 0) => 0
    | (app (var_b 1) e') => S (c_to_nat_helper e')
    | _ => 0
end.

Definition c_to_nat (e : exp) : nat := c_to_nat_helper (remove_abs e). 

Theorem church_reverse_1 : forall (n : nat), (c_to_nat  (church_number n)) = n.
Proof.
intros. induction n. 
  - auto. 
  - simpl. unfold c_to_nat. simpl. unfold c_to_nat in IHn.   rewrite IHn. auto.  
Qed.



(* defines successor functions *)
Definition c_S (e : exp) : exp :=
  let c := remove_abs e in 
    (abs (abs (app (var_b 1) c))).

Inductive is_church : exp -> Prop :=
  | c_def : is_church (abs (abs (var_b 0)))
  | c_trans : forall (e' : exp), is_church (abs (abs e')) -> is_church (abs (abs (app (var_b 1) e'))).
Hint Constructors is_church : core .

Theorem church_reverse_2 : forall (e : exp), is_church e -> (church_number  (c_to_nat e)) = e.
Proof.
intros. induction H. 
  - auto. 
  - simpl. unfold c_to_nat in IHis_church. simpl in *.
    rewrite IHis_church. auto.  
Qed.
Theorem church_inter : forall (e : exp) (n : nat), is_church e -> c_to_nat e = n <-> church_number n = e.
Proof.
intros. split; intros.
- subst. apply church_reverse_2. auto.
- subst. apply church_reverse_1.   
Qed. 

Lemma church_abs : forall (n : nat), exists c, (abs (abs c)) =  church_number n.
Proof.
intros. induction n. 
  -  eexists. unfold church_number. eauto.
  - simpl. destruct IHn. rewrite <- H. eexists. eauto.  
Qed.
Theorem church_valid : forall (e : exp), is_church e <-> exists n, church_number n = e.
Proof.
intros. split; intros. 
- exists (c_to_nat e). apply church_reverse_2. auto. 
- destruct H. generalize dependent e. induction x; intros. 
  -- simpl in H. subst. auto. 
  -- simpl in H. subst. eapply c_trans.  apply IHx. 
    assert (A: exists c, (abs (abs c)) = church_number x). apply church_abs. destruct A. 
    rewrite <- H. auto.
Qed.

Theorem S_valid : forall n, c_S (church_number n) = church_number (S n). 
Proof.
intros. 
induction n. 
- simpl. auto. 
- simpl in *. unfold c_S. simpl. reflexivity.  
Qed.



Fixpoint c_add_helper (e1 e2 : exp) : exp :=
match e1 with 
    | (var_b 0) => e2
    | (app (var_b 1) e') => (app (var_b 1) (c_add_helper e' e2))
    | _ => var_b 0
end.

Definition c_add (e1 e2 : exp) : exp := (abs (abs (c_add_helper (remove_abs e1) (remove_abs e2)))).

Theorem add_valid : forall n m, c_add (church_number n) (church_number m) = church_number (m + n). 
Proof.
intros. induction n. 
  - simpl. unfold c_add. simpl. rewrite <- plus_n_O.    
    assert (A: exists c, (abs (abs c)) = church_number m). apply church_abs. destruct A. 
    rewrite <- H. auto.
  - induction m. 
    --  simpl. unfold c_add. simpl in *. unfold c_add in IHn. simpl in IHn.  
    assert (A: exists c, (abs (abs c)) = church_number n). apply church_abs. destruct A. rewrite <- H in IHn.
    inversion IHn; subst. simpl.  
    rewrite <- H. simpl. rewrite -> H1.  auto.
    -- simpl. unfold c_add. simpl in *. unfold c_add in IHn. simpl in IHn.  
    assert (A: exists c, (abs (abs c)) = church_number n). apply church_abs. destruct A. rewrite <- H in IHn.
    inversion IHn; subst. simpl.  
    rewrite <- H. simpl. rewrite -> H1. rewrite <- plus_n_Sm. 
    simpl. auto.
Qed.

  
Definition comm (R : exp -> exp -> exp) : Prop := forall n m, is_church n -> is_church m -> R n m = R m n.

Theorem add_comm : comm c_add. 
Proof.
unfold comm. intros. apply church_valid in H. apply church_valid in H0. destruct H. destruct H0.
  subst. rewrite add_valid. rewrite add_valid. f_equal.  apply plus_comm. 
Qed.  

Definition assoc (R : exp -> exp -> exp) : Prop := forall n m o, is_church n -> is_church m -> is_church o ->  
R (R n m) o = R  n (R m o).

Theorem add_assoc : assoc c_add.
Proof.
unfold assoc. intros. apply church_valid in H. apply church_valid in H0. apply church_valid in H1. 
destruct H1. destruct H. destruct H0. subst. repeat rewrite add_valid. f_equal. apply plus_assoc. 
Qed.
Definition S_lam_helper : exp := (abs (abs (app (var_b 1) (app (app (var_b 2)  (var_b 1)) (var_b 0))))).
Definition S_lam : exp := (abs S_lam_helper). 


Hint Constructors lc_exp : core .
Lemma S_lam_exp : lc_exp S_lam.
Proof.
unfold S_lam. unfold S_lam_helper. apply lc_abs. intros. unfold StlcNotations.open.
unfold open_exp_wrt_exp_rec. simpl.   apply lc_abs. intros. unfold StlcNotations.open.
unfold open_exp_wrt_exp_rec. simpl.  apply lc_abs. intros. unfold StlcNotations.open.
unfold open_exp_wrt_exp_rec. simpl. auto. 
Qed.  

Ltac unfold_open :=
 unfold open_exp_wrt_exp_abs; unfold open_exp_wrt_exp_rec_abs; simpl; fold open_exp_wrt_exp_rec_abs.

Ltac check_lc :=
  repeat (apply lc_abs; intros; unfold StlcNotations.open;
unfold open_exp_wrt_exp_rec; simpl); try auto.
Lemma S_lam_test : (app S_lam c_two) --->* c_three.
Proof.
unfold S_lam. unfold c_two. eapply multi_step. 
  - apply abs_step_beta. 
  - unfold StlcNotations.open.
unfold open_exp_wrt_exp_rec_abs. simpl. eapply multi_step.
  --  eapply abs_step_abs. eapply abs_step_abs. eapply abs_step_app_2. eapply abs_step_app. apply abs_step_beta.
 --  unfold StlcNotations.open.
unfold open_exp_wrt_exp_rec_abs. simpl. eapply multi_step.
  --- eapply abs_step_abs. eapply abs_step_abs. eapply abs_step_app_2. apply abs_step_beta. 
  --- unfold StlcNotations.open.
unfold open_exp_wrt_exp_rec_abs. simpl. unfold open_exp_wrt_exp_abs. unfold open_exp_wrt_exp_rec_abs. simpl.
  unfold c_three. econstructor. 
Qed.

Lemma open_identity_2 : forall (n : nat), (open_exp_wrt_exp_rec_abs 2 0 (var_b 0) (open_exp_wrt_exp_rec_abs 2 1 (var_b 1) (remove_abs (church_number n))))
= (remove_abs (church_number n)).
Proof.
intros. induction n. unfold_open. auto. 
unfold_open. rewrite -> IHn. auto.   
Qed.

Lemma church_def: forall (n : nat),  abs (abs (app (var_b 1) (app (app (church_number (n)) (var_b 1)) (var_b 0)))) --->*
abs (abs (app (var_b 1) (remove_abs (church_number n)))).
Proof.
intros. induction n. 
- eapply multi_step. 
{ eapply abs_step_abs. eapply abs_step_abs. eapply abs_step_app_2. eapply abs_step_app. apply abs_step_beta. }
simpl. unfold_open.
eapply multi_step.
 eapply abs_step_abs. eapply abs_step_abs. eapply abs_step_app_2. eapply abs_step_beta. unfold_open. econstructor. 
- simpl. eapply multi_step. 
{ eapply abs_step_abs. eapply abs_step_abs. eapply abs_step_app_2. eapply abs_step_app. apply abs_step_beta. }
unfold_open. eapply multi_step. 
{  eapply abs_step_abs. eapply abs_step_abs. eapply abs_step_app_2. apply abs_step_beta. }
unfold_open. rewrite -> open_identity_2. econstructor.
Qed.

Lemma chruch_def_2 : forall (n : nat), abs (abs (app (app (church_number n) (var_b 1)) (var_b 0))) --->* church_number n.
Proof.
intros. induction n. 
- eapply multi_step. 
{ eapply abs_step_abs. eapply abs_step_abs.  eapply abs_step_app. apply abs_step_beta. }
simpl. unfold_open.
eapply multi_step.
 eapply abs_step_abs. eapply abs_step_abs. eapply abs_step_beta. unfold_open. econstructor. 
- simpl. eapply multi_step. 
{ eapply abs_step_abs. eapply abs_step_abs. eapply abs_step_app. apply abs_step_beta. }
unfold_open. eapply multi_step. 
{  eapply abs_step_abs. eapply abs_step_abs.  apply abs_step_beta. }
unfold_open. rewrite -> open_identity_2. econstructor.
Qed.


Theorem S_lam_correct : forall (n : nat), (app S_lam (church_number n)) --->* church_number (S n).
Proof.
intros. induction n. 
- unfold S_lam. eapply multi_step. 
{ apply abs_step_beta. }
simpl. unfold_open.
eapply multi_step. eapply abs_step_abs. eapply abs_step_abs. eapply abs_step_app_2. eapply abs_step_app.
eapply abs_step_beta. unfold_open. eapply multi_step. eapply abs_step_abs. eapply abs_step_abs.
eapply abs_step_app_2. eapply abs_step_beta. unfold_open. econstructor. 
- simpl. unfold S_lam. eapply multi_step. 
{ apply abs_step_beta. }
unfold_open. assert (A: c_S (church_number n) = church_number (S n)). apply S_valid.
unfold c_S in A. rewrite -> A. eapply multi_trans. apply church_def with (n := (S n)). 
simpl. auto.
Qed. 

Definition add_lam_helper : exp := (abs (abs (abs (app (app (var_b 3) (var_b 1)) (app (app (var_b 2)  (var_b 1)) (var_b 0)))))).
Definition add_lam : exp := (abs add_lam_helper).

Lemma add_lam_test : app (app add_lam c_one) c_two --->* c_three.
Proof.
unfold add_lam.  eapply multi_step. 
  - eapply abs_step_app. apply abs_step_beta. 
  - unfold_open. eapply multi_step.
  --  apply abs_step_beta.
 --  unfold_open.
eapply multi_step.
  --- eapply abs_step_abs. eapply abs_step_abs. eapply abs_step_app_2.  eapply abs_step_app. apply abs_step_beta. 
  --- unfold_open.
eapply multi_step.
  ---- eapply abs_step_abs. eapply abs_step_abs. eapply abs_step_app_2.  apply abs_step_beta.
  ---- unfold_open. eapply multi_step.
  ----- eapply abs_step_abs. eapply abs_step_abs. eapply abs_step_app. apply abs_step_beta.
  ----- unfold_open. eapply multi_step.
  ------ eapply abs_step_abs. eapply abs_step_abs. apply abs_step_beta.
  ------ unfold_open. unfold c_three. econstructor. 
Qed.
 
Lemma remove_abs_note : forall (n m : nat), (open_exp_wrt_exp_rec_abs 0 (S (S m)) (abs (abs (var_b 0))) (remove_abs (church_number n))) = 
(remove_abs ((open_exp_wrt_exp_rec_abs 0 (S (S m)) (abs (abs (var_b 0)))  (church_number n)))).
Proof.
intros. induction n. unfold_open. auto.
unfold_open. f_equal. 
assert (A: forall a, open_exp_wrt_exp_rec_abs 0 (S (S m)) (abs (abs (var_b 0))) (remove_abs (church_number a)) =
open_exp_wrt_exp_rec_abs 0 (S (S (S (S m)))) (abs (abs (var_b 0))) (remove_abs (church_number a))).
{
intros. induction a. auto. unfold_open. f_equal. auto.  

}auto.
Qed.

Definition multi_lam_helper : exp := (abs (abs (abs (app (app (var_b 3) (app (var_b 2) (var_b 1))) (var_b 0) )))).
Definition multi_lam : exp := (abs multi_lam_helper).
Lemma add_lam_open_m : forall (n m : nat), (m > 1) -> (open_exp_wrt_exp_rec_abs 0 m (abs (abs (var_b 0))) (church_number n)) = (church_number n).
Proof.
intros n. induction n; intros. auto.
unfold_open. assert (A: (S (S m)) > 1). auto. apply IHn in A. 
rewrite -> remove_abs_note. f_equal. f_equal. f_equal.  rewrite -> A.  auto. 
Qed.
Theorem add_lam_correct_0 : forall (n : nat), (app (app add_lam (church_number n)) (church_number 0 )) --->* church_number (n).
Proof.
intros. 
unfold add_lam.  eapply multi_step. 
  - eapply abs_step_app. apply abs_step_beta. 
  - unfold_open. eapply multi_step.
  --  apply abs_step_beta.
 --  unfold_open. rewrite -> add_lam_open_m; auto. 
eapply multi_step.
  --- eapply abs_step_abs. eapply abs_step_abs. eapply abs_step_app_2.  eapply abs_step_app. apply abs_step_beta. 
  --- unfold_open.
eapply multi_step.
  ---- eapply abs_step_abs. eapply abs_step_abs. eapply abs_step_app_2.  apply abs_step_beta.
  ---- unfold_open. apply chruch_def_2.
Qed.

Theorem add_lam_open_1 : forall (n m : nat), (m > 1) -> (open_exp_wrt_exp_rec_abs m 1 (var_b 1) (remove_abs (church_number n)) = (remove_abs (church_number n))).
Proof. intros n. induction n; intros; auto.
simpl. apply IHn in H. f_equal. auto. 
Qed. 

Theorem add_lam_open_0 : forall (n : nat), (open_exp_wrt_exp_rec_abs 2 0 (var_b 0) (remove_abs (church_number n)) = (remove_abs (church_number n))).
Proof. intros n. induction n; intros; auto. 
simpl. unfold_open. f_equal. auto.
 
Qed. 

Theorem add_lam_open_S_0 : forall (n m : nat), (open_exp_wrt_exp_rec_abs 0 4 (abs (abs (app (var_b 1) (remove_abs (church_number m)))))
                       (remove_abs (church_number n))) = (remove_abs (church_number n)). 
Proof.
intros. induction n. 
- simpl. auto. 
- simpl. f_equal. auto. 
Qed.

Theorem add_lam_open_S_step : forall (n m : nat), (open_exp_wrt_exp_rec_abs 2 0 (app (var_b 1) (remove_abs (church_number m))) (remove_abs (church_number n)))
= (app (var_b 1) (remove_abs (church_number (n + m)))).
Proof.
intros. induction n; intros; auto.  
simpl. rewrite -> IHn.  auto.
Qed. 

Theorem add_lam_S_step : forall (n m : nat), abs (abs (app (abs (app (var_b 1) (remove_abs (church_number n)))) (app (var_b 1) (remove_abs (church_number m))))) --->*
abs (abs (app (var_b 1) (app (var_b 1) (remove_abs (church_number (n + m)))))).
Proof.
intros n. induction n; intros; auto. 
simpl. 
- eapply multi_step.
   eapply abs_step_abs. eapply abs_step_abs.  apply abs_step_beta.
unfold_open. constructor. 
- simpl. eapply multi_step.
   eapply abs_step_abs. eapply abs_step_abs.  apply abs_step_beta.
unfold_open. rewrite -> add_lam_open_S_step. auto.
Qed.

Theorem add_lam_correct_S : forall (n m : nat),  
(app (app add_lam (church_number n)) (church_number (S m ))) --->* church_number (S (n + m)).
Proof.
unfold add_lam. intros n. induction n; intros; auto.
- simpl. eapply multi_step. 
  -- eapply abs_step_app. apply abs_step_beta. 
  -- unfold_open. eapply multi_step.
  ---  apply abs_step_beta.

  --- unfold_open.
eapply multi_step.
  ---- eapply abs_step_abs. eapply abs_step_abs. eapply abs_step_app_2. eapply abs_step_app. apply abs_step_beta.
  ---- unfold_open. eapply multi_step.
  ----- eapply abs_step_abs. eapply abs_step_abs. eapply abs_step_app. apply abs_step_beta.
  ----- unfold_open. rewrite -> add_lam_open_1; auto. eapply multi_step.
  ------ eapply abs_step_abs. eapply abs_step_abs. apply abs_step_beta.
  ------ unfold_open. eapply multi_step.
  ------- eapply abs_step_abs. eapply abs_step_abs. apply abs_step_beta.
  -------  unfold_open. rewrite -> add_lam_open_0. constructor.
- simpl. eapply multi_step. 
  -- eapply abs_step_app. apply abs_step_beta. 
  -- unfold_open. eapply multi_step.
  ---  apply abs_step_beta.
  --- unfold_open. rewrite -> add_lam_open_S_0. 
eapply multi_step.
eapply abs_step_abs. eapply abs_step_abs. eapply abs_step_app. apply abs_step_beta.
unfold_open. rewrite -> add_lam_open_1; auto. 
eapply multi_step. 
eapply abs_step_abs. eapply abs_step_abs. eapply abs_step_app_2. eapply abs_step_app. apply abs_step_beta.
unfold_open. rewrite -> add_lam_open_1; auto. 
eapply multi_step. 
eapply abs_step_abs. eapply abs_step_abs. eapply abs_step_app_2.  apply abs_step_beta.
unfold_open. rewrite -> add_lam_open_0. eapply multi_trans. apply add_lam_S_step.  auto. 
Qed. 
Theorem add_lam_correct : forall (n m : nat), (app (app add_lam (church_number n)) (church_number m )) --->* church_number (n + m).
Proof. destruct m. 
- rewrite <- plus_n_O. apply add_lam_correct_0. 
- rewrite <- plus_n_Sm. apply add_lam_correct_S.
Qed.

Definition comm_step (R : exp) : Prop := forall n m, is_church n -> is_church m -> exists e, (app (app R n) m) --->* e /\ app (app R m) n --->* e.

Theorem multi_app: forall (e1 e1' e2 e2' : exp) (n : nat), multi (abs_step n) e1 e1' -> multi (abs_step n) e2 e2' -> 
multi (abs_step n) (app e1 e2) (app e1' e2').
Proof.
intros. 
induction H. induction H0. constructor.
  -  eapply abs_step_app_2 in H. eapply multi_step. apply H. apply IHmulti.
  - induction H0.
  --  eapply abs_step_app in H. eapply multi_step. apply H. apply IHmulti.
  --  eapply abs_step_app in H. eapply multi_step. apply H. apply IHmulti.
Qed.

Definition assoc_step (R : exp) : Prop := forall n m o,
is_church o -> is_church n -> is_church m -> exists e, (app (app R (app (app R n) m)) o) --->* e /\ (app (app R n) (app (app R m) o)) --->* e.

Theorem add_step_comm : comm_step add_lam. 
Proof.
unfold comm_step. intros. 
  apply church_valid in H. apply church_valid in H0. destruct H. destruct H0.
  subst. exists (church_number (x + x0)). split. apply add_lam_correct.
  rewrite plus_comm.  apply add_lam_correct.
Qed.

Theorem add_step_assoc : assoc_step add_lam. 
Proof.
unfold assoc_step. intros. 
  apply church_valid in H. apply church_valid in H0. apply church_valid in H1. 
destruct H1. destruct H. destruct H0.
  subst. exists (church_number (x1 + (x + x0))). split. eapply multi_trans. eapply multi_app. eapply multi_app.
constructor. apply add_lam_correct. constructor. eapply multi_trans. apply add_lam_correct.
rewrite -> plus_assoc. constructor.  
eapply multi_trans. eapply multi_app. constructor. 
 apply add_lam_correct. eapply multi_trans. apply add_lam_correct.
rewrite -> plus_assoc. constructor.
Qed.

Lemma multi_lam_test : app (app multi_lam c_two) c_two --->* c_four.
Proof.
unfold multi_lam.  eapply multi_step. 
  - eapply abs_step_app. apply abs_step_beta. 
  - unfold_open. eapply multi_step.
  --  apply abs_step_beta.
 --  unfold_open.
eapply multi_step.
  --- eapply abs_step_abs. eapply abs_step_abs. eapply abs_step_app. apply abs_step_beta. 
  --- unfold_open.
eapply multi_step.
  ---- eapply abs_step_abs. eapply abs_step_abs.  apply abs_step_beta.
  ---- unfold_open. eapply multi_step.
  ----- eapply abs_step_abs. eapply abs_step_abs.  eapply abs_step_app. apply abs_step_beta.
  ----- unfold_open. eapply multi_step.
  ------ eapply abs_step_abs. eapply abs_step_abs. apply abs_step_beta.
  ------ unfold_open. eapply multi_step.
  ------- eapply abs_step_abs. eapply abs_step_abs. eapply abs_step_app_2. eapply abs_step_app_2.
eapply abs_step_app. apply abs_step_beta.
  ------- unfold_open. eapply multi_step.
  -------- eapply abs_step_abs. eapply abs_step_abs. eapply abs_step_app_2. eapply abs_step_app_2. apply abs_step_beta.
  -------- unfold_open. econstructor. 
Qed.
Fixpoint stack_abs (n : nat) : exp :=
match n with
  |0 =>  (var_b 0)
  | S n' => (app (abs (var_b 0)) (stack_abs n'))
end.

Theorem open_to_stack : forall n m, (open_exp_wrt_exp_rec_abs  (S m) 1 (abs (var_b 0)) (remove_abs (church_number n))) = stack_abs n. 
Proof.
intros. induction n. 
simpl. auto.
simpl.  f_equal. auto.
Qed.

Theorem stack_simpl : forall n m, (multi (abs_step m) (stack_abs n)  (var_b 0)). 
Proof.
intros. induction n. 
constructor. 
simpl. eapply multi_step. apply abs_step_beta. unfold_open. auto.
Qed. 

Theorem abs_step_multi : forall (e1 e1': exp) n, multi (abs_step (S n)) e1 e1'-> multi (abs_step n) (abs e1) (abs e1'). 
Proof.
intros. induction H. 
  - constructor. 
  - apply abs_step_abs in H. apply multi_step with (y0 := (abs y)). apply H. auto. 
Qed.

Theorem multi_lam_helper_0 : forall (n m: nat), multi (abs_step m) (abs (app (app (church_number n) (abs (var_b 0))) (var_b 0)))   (abs (var_b 0)).
Proof.
intros. 
induction n. simpl.
eapply multi_step.  eapply abs_step_abs. eapply abs_step_app. apply abs_step_beta. 
unfold_open. eapply multi_step.  eapply abs_step_abs. apply abs_step_beta. unfold_open.  constructor. 
simpl.  
eapply multi_step.  eapply abs_step_abs. eapply abs_step_app. apply abs_step_beta. 
unfold_open. rewrite -> open_to_stack. eapply multi_trans. eapply abs_step_multi. eapply multi_app. 
 eapply abs_step_multi. eapply multi_app. constructor. apply stack_simpl. constructor.    
eapply multi_step.  eapply abs_step_abs. eapply abs_step_app. eapply abs_step_abs.  eapply abs_step_beta.
unfold_open.  
eapply multi_step.  eapply abs_step_abs.   eapply abs_step_beta.
constructor. 
Qed.
Theorem multi_lam_correct_0 : forall (n : nat), (app (app multi_lam (church_number n)) (church_number 0 )) --->* church_number (0).
Proof.
intros. 
unfold add_lam.  eapply multi_step. 
  - eapply abs_step_app. apply abs_step_beta. 
  - unfold_open. eapply multi_step.
  --  apply abs_step_beta.
 --  unfold_open. rewrite -> add_lam_open_m; auto. 
eapply multi_step.
  --- eapply abs_step_abs. eapply abs_step_abs. eapply abs_step_app.  eapply abs_step_app_2. apply abs_step_beta. 
  --- unfold_open.
eapply multi_trans. eapply abs_step_multi. apply  multi_lam_helper_0. constructor.
Qed.
Lemma church_step_one_helper : forall (n : nat), open_exp_wrt_exp_abs 2 (abs (app (var_b 1) (remove_abs (church_number n)))) 
(var_b 1) =  (abs (app (var_b 1) (remove_abs (church_number n)))).
Proof.
intros. induction n. 
auto. 
unfold_open. f_equal. f_equal. f_equal. apply add_lam_open_1. auto.

Qed.
Theorem church_step_one : forall (n : nat), abs_step 2 (app (church_number n) (var_b 1)) (abs (remove_abs (church_number n))).
Proof.
intros. induction n. 
simpl. apply abs_step_beta. 
simpl.
assert (A: abs_step 2 (app (abs (abs (app (var_b 1) (remove_abs (church_number n))))) (var_b 1))
  (open_exp_wrt_exp_abs 2 (abs (app (var_b 1) (remove_abs (church_number n)))) (var_b 1))).
apply abs_step_beta.  rewrite -> church_step_one_helper in A. auto. 

Qed.

Theorem multi_lam_open_S_0 : forall (n m : nat), (open_exp_wrt_exp_rec_abs 0 4 (church_number m)
                       (remove_abs (church_number n))) = (remove_abs (church_number n)). 
Proof.
intros. induction n. auto. 
simpl. f_equal. auto.
Qed.
Fixpoint stack_mult (n m: nat) : exp :=
match n with
  |0 =>  (var_b 0)
  | S n' => (app (abs (remove_abs (church_number m))) (stack_mult n' m))
end.

Fixpoint add_b_1 (n : nat) (e : exp) : exp :=
match n with 
  |0 => e
  | S n' => (app (var_b 1) (add_b_1 n' e))
end.

Theorem  lol : forall (n m o : nat), (open_exp_wrt_exp_abs o (abs (remove_abs (church_number n))) (abs (remove_abs (church_number m)))) = 
  (abs (stack_mult n m)).
Proof.
intros. induction n. simpl. induction m. 
auto. 
simpl.  unfold_open. auto. 
unfold_open. f_equal. f_equal. unfold open_exp_wrt_exp_abs in IHn. unfold open_exp_wrt_exp_rec_abs in IHn. simpl.
fold open_exp_wrt_exp_rec_abs in IHn. injection IHn; auto. 
Qed.
Theorem stack_mult_equ : forall n m o,  (abs_step o) (app (church_number n) (abs (remove_abs (church_number m)))) (abs (stack_mult n m)). 
Proof.
intros. 
assert (A: (abs_step o) (app (church_number n) (abs (remove_abs (church_number m))))
 ((open_exp_wrt_exp_abs o (abs (remove_abs (church_number n))) (abs (remove_abs (church_number m)))))).
{
assert (C : exists c,  abs (abs c) = church_number n).
apply  church_abs. destruct C. rewrite <- H. simpl.  
apply abs_step_beta.
}
rewrite -> lol in A. auto.
Qed.  

Theorem stack_mult_simpl_h : forall n m o, (open_exp_wrt_exp_rec_abs 3 0 (stack_mult n o) (remove_abs (church_number m))) = 
(add_b_1 m (stack_mult n o)).
Proof.
intros.  induction m. auto.
simpl. f_equal. unfold_open. f_equal. auto.
Qed.   

Theorem stack_mult_simpl_equiv : forall n m o, add_b_1 m (remove_abs (church_number (n * o))) = (remove_abs (church_number (m + n * o))).
intros.
induction m. simpl. auto.
simpl. f_equal. auto.
Qed.   
Theorem stack_step : forall m e e' o, multi (abs_step o) e e' -> multi (abs_step o) (add_b_1 m e) (add_b_1 m e'). 
Proof. 
intros. 
induction m. simpl. auto.
simpl. apply multi_app. auto. auto. 
Qed.

Theorem stack_mult_simpl : forall n m , (multi (abs_step 3) (stack_mult n m) (remove_abs (church_number (n * m)))). 
Proof.
intros. induction n.
simpl.
constructor. 
simpl. eapply multi_step. apply abs_step_beta. unfold_open. auto. rewrite -> stack_mult_simpl_h. rewrite <- stack_mult_simpl_equiv. 
eapply stack_step. auto. 

Qed.  


Theorem multi_wh : forall (n m: nat), open_exp_wrt_exp_rec_abs 0 4 (church_number m) (remove_abs (church_number n)) = remove_abs (church_number n).
Proof.
intros. induction n. auto. 
simpl. f_equal. auto.
Qed.
Theorem multi_open_open : forall (n m : nat), open_exp_wrt_exp_rec_abs 0 2 (church_number m) (church_number n) = church_number n.
intros. induction n. auto. simpl. f_equal. f_equal. f_equal. apply multi_wh.
Qed.  
Theorem multi_lam_correct : forall (n m : nat),  
(app (app multi_lam (church_number (n))) (church_number m)) --->* church_number ( n* m).
Proof.
intros. simpl. 
 eapply multi_step. 
eapply abs_step_app. apply abs_step_beta.
unfold_open.  
 eapply multi_step. apply abs_step_beta.
unfold_open. rewrite multi_open_open.    
 eapply multi_step. eapply abs_step_abs. eapply abs_step_abs.
eapply abs_step_app. eapply abs_step_app_2. eapply church_step_one.
 eapply multi_step. eapply abs_step_abs. eapply abs_step_abs. eapply abs_step_app.
 apply stack_mult_equ.
unfold_open. eapply multi_trans. eapply abs_step_multi. eapply abs_step_multi. eapply multi_app.  
eapply abs_step_multi. apply stack_mult_simpl. constructor. 
eapply multi_step.  eapply abs_step_abs. eapply abs_step_abs. eapply abs_step_beta. 
unfold_open. rewrite -> add_lam_open_0. 
assert  (C : exists c,  abs (abs c) = church_number (n*m)). eapply church_abs. 
destruct C. rewrite <- H. simpl.    constructor.
Qed.  


Theorem multi_step_comm : comm_step multi_lam. 
Proof.
unfold comm_step. intros. 
  apply church_valid in H. apply church_valid in H0. destruct H. destruct H0.
  subst. exists (church_number (x * x0)). split. apply multi_lam_correct.
  rewrite mult_comm.  apply multi_lam_correct.
Qed.

Theorem multi_step_assoc : assoc_step multi_lam. 
Proof.
unfold assoc_step. intros. 
  apply church_valid in H. apply church_valid in H0. apply church_valid in H1. 
destruct H1. destruct H. destruct H0.
  subst. exists (church_number (x1 * (x * x0))). split. eapply multi_trans. eapply multi_app. eapply multi_app.
constructor. apply multi_lam_correct. constructor. eapply multi_trans. apply multi_lam_correct.
rewrite -> mult_assoc. constructor.  
eapply multi_trans. eapply multi_app. constructor. 
 apply multi_lam_correct. eapply multi_trans. apply multi_lam_correct.
rewrite -> mult_assoc. constructor.
Qed.


Theorem multi_lam_correct_S : forall (n m : nat),  
(app (app multi_lam (church_number (S n))) (church_number m)) --->* church_number (m + n * m).

intros. simpl. 
 eapply multi_step. 
eapply abs_step_app. apply abs_step_beta.
unfold_open.  
 eapply multi_step. apply abs_step_beta.
unfold_open. rewrite -> multi_lam_open_S_0.   
 eapply multi_step. eapply abs_step_abs. eapply abs_step_abs.
eapply abs_step_app. eapply abs_step_app_2. eapply church_step_one.
 eapply multi_step. eapply abs_step_abs. eapply abs_step_abs. eapply abs_step_app.
 apply abs_step_beta.
unfold_open. 
 abs_step_beta. unfold_open. constructor.  
Qed.