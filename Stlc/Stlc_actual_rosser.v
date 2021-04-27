Require Import Metalib.Metatheory.
Require Import Stlc.Definitions.
Require Import Stlc.Lemmas.
Require Import Coq.Program.Equality.
From Coq Require Import Relations.

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
Notation " t '--->' t' " := (step t t') (at level 60).
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
       apply IHmulti. apply multi_step with x0.  assumption.
      assumption.
Qed.

Theorem count_to_multi : forall e1 e2 n, step_count  n e1 e2  -> e1 -->* e2.
Proof.
intros. dependent induction H; try constructor.  econstructor; eauto.  
Qed. 

Theorem deterministic_step : forall e1 e2 e3, e1 ---> e2 -> e1 ---> e3 -> e2 = e3.
Proof.
intros. generalize dependent e3. dependent induction H; intros; subst.
  - inversion H1; subst. auto. inversion H6. 
  - inversion H0; subst.
  -- inversion H1; subst. assert (A: (StlcNotations.open e0 e4) = e1'). auto. subst. auto.
  -- inversion H1; subst. assert (A: (app e1'0 e4) = e1'). auto. subst. auto.   
Qed.

Theorem deterministic_step_2 : forall e1 e2 e3 e4 e5, e1 ---> e2 -> e1 ---> e3 -> e2 ---> e4 -> e3 ---> e5 -> e4 = e5 /\ e2 = e3.
Proof.
intros. assert (A : e2 = e3). eapply deterministic_step; eauto. subst.
  assert (B: e4 = e5). eapply deterministic_step; eauto. subst. split; auto.
Qed.

Theorem deterministic_step_count : forall n e1 e2 e3, step_count n e1 e2 -> step_count n e1 e3 -> e2 = e3.
Proof.
  intros. generalize dependent e3. dependent induction H; intros. inversion H0. auto.
  inversion H1; subst. apply IHstep_count in H4; subst. eapply deterministic_step; eauto.  
Qed.

Theorem test : forall e1 e2 e3, e1 ---> e2 -> e1 -->* e3 -> e1 <> e3 -> e2 -->* e3. 
Proof.
intros. generalize dependent e2.  induction H0; intros. 
  - destruct H1. auto. 
  - eapply IHmulti in H1.   
Qed.

Theorem deterministic_multi_step : forall e1 m n, multi step e1 m -> multi step e1 n -> multi step m n \/ multi step n m.
Proof.
intros. generalize dependent n. dependent induction H; intros.
  - left. auto.
  -  apply IHmulti in H1. destruct H1. 
    -- right. econstructor; eauto.   


Definition confluence (R : relation exp) : Prop := forall (e1 m n : exp),
lc_exp e1 -> multi R e1 m -> multi R e1 n -> (exists f, multi R m f /\ multi R n f).

Definition semi_confluence (R : relation exp) : Prop := forall (e1 m n : exp),
lc_exp e1 -> R e1 m -> multi R e1 n -> (exists f, multi R m f /\ multi R n f).

Definition diamond (R : relation exp) : Prop := forall (e1 m n: exp),
lc_exp e1 -> R e1 m -> R e1 n -> exists f, R n f /\ R m f.

Definition diamond_multi (R1 R2 : relation exp) : Prop := forall (e1 m n: exp),
lc_exp e1 -> R1 e1 m -> R2 e1 n -> exists f, R2 n f /\ R1 m f.

Definition lc_preserve (R : relation exp) : Prop := forall e1 e2, lc_exp e1 -> multi R e1 e2 -> lc_exp e2. 
Lemma clos_refl_star : forall {A} R x y, clos_refl_trans_1n A R x y <-> exists n, star R n x y.
Proof.
intros. split. 
  - intros. dependent induction H; subst.  
    -- exists 0. constructor.
    -- destruct IHclos_refl_trans_1n. exists (S x0). econstructor. apply H. auto.
  - intros. destruct H; dependent induction H; subst.
    --  constructor.
    --  econstructor. eauto. eauto.      
Qed.
Theorem step_lc_preserve_one : forall e1 e2, lc_exp e1 -> e1 ---> e2 -> lc_exp e2.

Proof.
intros. induction H0. 
  - inversion H; subst. apply lc_body_exp_wrt_exp. 
  -- unfold body_exp_wrt_exp. intros. inversion H0; subst. auto. 
  -- auto. 
  - constructor. inversion H; subst.  apply IHstep in H4. auto. inversion H; subst.  auto.
Qed.
Theorem step_lc_preserve : lc_preserve step. 
Proof.
  unfold lc_preserve. intros. induction H0. auto. apply IHmulti in H. eapply step_lc_preserve_one in H; auto. apply H. auto.    
Qed.

Theorem diamond_step : diamond step. 
Proof.
unfold diamond. intros. assert (A: ). eapply deterministic_step_2; eauto.
subst. exists o. split. auto. auto.
Qed.

Theorem diamond_to_multi : forall R, diamond R -> diamond_multi R R. 
Proof.
intros. unfold diamond in H. unfold diamond_multi. intros.  eapply H in H0; eauto.
Qed.

Lemma diamond_symmetric : forall (R1 R2 : relation exp),
  diamond_multi R1 R2 -> diamond_multi R2 R1.
Proof.
intros. unfold diamond_multi in H. unfold diamond_multi. intros. 
assert (A : lc_exp e1). auto. 
eapply H with   (m := n) (n := m) (o := p) in A . destruct A. destruct H5. exists x. split; auto. 
auto. auto. auto. eauto.  
Qed.
Lemma on_the_left :
  forall R1 R2,
  diamond_multi R1 R2 -> forall n, diamond_multi (star R1 n) R2.
Proof.
  intros. unfold diamond_multi in *. intros. dependent induction H1. 
  - inversion H4; subst. eapply H with ( in H0


Lemma on_the_right :                     
  forall {A : Type} (R1 R2 : A -> A -> Prop),
  diamond_property R1 R2 -> forall n, diamond_property R1 (star R2 n).

Lemma diamond_property_implies_mn_confluence :
  forall {A : Type} (R : A -> A -> Prop),
  diamond_property R R -> forall m n, diamond_property (star R m) (star R n).

Theorem diamond_to_semi_conf : forall (R : relation exp), lc_preserve R -> diamond R -> semi_confluence R. 
 Proof.
intros R L H. unfold diamond in H. unfold semi_confluence. intros. 
induction H2.
  - exists m. split. auto. constructor. apply multi_R. auto.  
  - unfold lc_preserve in L. 
    assert (A: lc_exp y). eapply L. apply H0. auto. 

 apply IHmulti in H0; auto. destruct H0.  destruct H0. apply H  with (n := x0) (m := z) in A; auto.
    -- destruct A. destruct H5. exists x1. split; auto. eapply multi_trans. apply H4. auto. 
Theorem semi_conf_to_conf : forall (R : relation exp), lc_preserve R -> semi_confluence R -> confluence R. 
Proof.
intros R L H. unfold semi_confluence in H. unfold confluence. intros. 
induction H1.
  - exists n. split. auto. constructor. 
  - unfold lc_preserve in L. 
    assert (A: lc_exp y). eapply L. apply H0. auto. 

 apply IHmulti in H0; auto. destruct H0.  destruct H0. apply H  with (n := x0) (m := z) in A; auto.
    -- destruct A. destruct H5. exists x1. split; auto. eapply multi_trans. apply H4. auto. 
Qed.

Theorem semi_conf_step : semi_confluence step. 
Proof.
unfold semi_confluence. intros. dependent induction H1. 
  - exists m. split.
    -- constructor. 
    -- apply multi_R. auto. 
  - 
Qed. 
