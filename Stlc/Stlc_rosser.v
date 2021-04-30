Require Import Metalib.Metatheory.
Require Import Stlc.Definitions.
Require Import Stlc.Lemmas.
(* defns JEval *)
Inductive step : exp -> exp -> Prop :=    (* defn step *)
 | step_beta : forall (e1 e2:exp),
     step (app  ( (abs e1) )  e2)  (open_exp_wrt_exp  e1 e2 ) 
 | step_app : forall (e1 e2 e1':exp),
     step e1 e1' -> step (app e1 e2) (app e1' e2)
 | step_app_2 : forall (e1 e2 e2':exp),
     step e2 e2' -> step (app e1 e2) (app e1 e2')
 | step_abs : forall (e1 e1':exp),
      step e1 e1' -> step (abs e1) (abs e1').


(** infrastructure *)
Hint Constructors typing step lc_exp : core.

Notation "[ z ~> u ] e" := (subst_exp u z e) (at level 0) : exp_scope.
Notation open e1 e2 := (open_exp_wrt_exp e1 e2). 
Theorem subst :forall e1 e2 e3 x2 x1,
  x2 `notin` fv_exp e2 ->
  x2 <> x1 ->
  [ x1~>e2 ] ([x2 ~> e3] e1) = [x2 ~> ([x1 ~> e2] e3)] ([x1 ~> e2] e1).
Proof.
apply subst_exp_subst_exp.
Qed.



(* Inductive step_count : exp -> exp -> nat -> Prop :=
  | sc_base : forall (e:exp),
    step_count e e 0
  | sc_ind : forall (e1 e2 e3:exp) (n:nat),
    step e1 e2 ->
    step_count e2 e3 n ->
    step_count e1 e3 (S n).

Inductive bounded_reduction : exp -> nat -> Prop :=
  | bound : forall (e1:exp) (v:nat),
    (forall (e2:exp) (n:nat), step_count e1 e2 n -> n < v) ->
    bounded_reduction e1 v.

Inductive strong_norm : exp -> Prop :=
  | sn_bound : forall (e:exp) (v:nat),
    bounded_reduction e v ->
    strong_norm e.

(* Theorem sn_arrow : forall (G:ctx) (e:exp) (U V:typ),
  typing G e (typ_arrow U V) ->
  (forall (u:exp),
    typing G u U -> strong_norm u ->
    typing G (app e u) V ->
    strong_norm (app e u)) ->
  strong_norm e.
Proof.
  intros G e U V Ht Hu.
  assert (Hsn: strong_norm (app e (var_b 5))).
  {
    apply Hu.

  } *)
  *)
  


Definition norm (e : exp) : Prop :=
  (~ exists e2, step e e2).

Theorem test : forall (x y : var), norm (app (var_f x) (var_f y)).
Proof.
unfold norm. unfold not. intros. destruct H.
  inversion H; subst. inversion H3. inversion H3.
Qed.

(*Inductive norm: exp -> Prop :=
  | norm_b : forall (n : nat), norm (var_b n)
  | norm_f : forall (x : var), norm (var_f x)
  | norm_fabs : forall (x : var), norm (var_f x)
  | norm_f : forall (x : var), norm (var_f x) 
Girard defines norm as not containing any (abs (app e1) e2) but the above definition is simpler. Decide later what to use*)

Inductive step_count : exp -> nat -> Prop := (*count!*)
  | count_b : forall (e:exp), norm e -> step_count e 0
  | count_step : forall (e e2:exp) (n:nat), step e e2 -> step_count e2 (n - 1) -> step_count e n.


Lemma norm_v : forall (x:var), norm (var_f x).
Proof.
intros. unfold norm. unfold not. intros. destruct H. inversion H. Qed. 

Theorem test_step_count : forall (x : var), step_count (app (abs (var_f x)) (var_f x)) 1.
Proof.
intros. eapply count_step. apply step_beta.
intros.
  - simpl. unfold open_exp_wrt_exp. unfold open_exp_wrt_exp_rec. constructor. apply norm_v.
Qed.
Definition strong_norm  (e : exp) : Prop :=
exists n, step_count e n.
Fixpoint reducible (T : typ) (e : exp) : Prop :=
  match T with
  | typ_base => strong_norm e
  | typ_arrow T1 T2 => (forall (e2: exp) , reducible T1 e2 -> reducible T2  (app e e2))
end.

Definition relation (X : Type) := X -> X -> Prop.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R y z ->
                    multi R x y ->
                    multi R x z.

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
  apply multi_step with x.
 - auto.
  - apply multi_refl.
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
      apply multi_step with y. assumption.
      apply IHmulti. assumption.
Qed.
Definition lc_preserve (R : relation exp) : Prop := forall e1 e2, lc_exp e1 -> multi R e1 e2 -> lc_exp e2. 
(*

Definition confluence (R : relation exp) : Prop := forall (e1 m n : exp),
lc_exp e1 -> multi R e1 m -> multi R e1 n -> (exists f, multi R m f /\ multi R n f).

Definition semi_confluence (R : relation exp) : Prop := forall (e1 m n : exp),
lc_exp e1 -> R e1 m -> multi R e1 n -> (exists f, multi R m f /\ multi R n f).

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


Definition map (X : Type) := X -> X.

Definition monotonic (R : relation exp) (m : map exp) : Prop := forall (a b : exp), lc_exp a -> multi R a b -> multi R (m a) (m b). 



Definition Z_prop (R : relation exp) : Prop :=  exists (m : map exp), forall (a b : exp), R a b -> lc_exp a -> multi R b (m a) /\ multi R (m a) (m b).

Definition Z_prop_m (R : relation exp) (m : map exp) := forall (a b : exp), R a b -> lc_exp a -> multi R b (m a) /\ multi R (m a) (m b).




Lemma Z_prop_to_m : forall (R : relation exp),  Z_prop R -> exists m, Z_prop_m R m.
Proof.
intros.
unfold Z_prop in H. destruct H as [m H0]. exists m. unfold Z_prop_m. auto.
Qed.

(*Theorem Z_monotonic_helper : forall (R : relation exp) (a b : exp) (m : map exp), Z_prop R -> (R a b -> multi R b (m a) /\ multi R (m a) (m b))
 -> exists (m : map exp), multi R a b -> multi R (m a) (m b).
Proof.
intros. exists m. intros.
induction H1.
  - apply multi_refl.
  - unfold Z_prop in H. assert (H2 :  exists m : map exp, R x y -> multi R y (m x) /\ multi R (m x) (m y)).
    {
apply H with (a := x) (b := y).
}
  apply H2 in H0. destruct H0.
  eapply multi_trans. 
  -- apply H3.
 apply H in  
*)
Theorem Z_monotonic : forall (R : relation exp), lc_preserve R -> Z_prop R -> exists (m : map exp), monotonic R m. 
Proof.
intros R L H. unfold Z_prop in H. destruct H as [m H]. eexists. unfold monotonic. 
intros.
induction H1.
  - apply multi_refl.
  - assert (M : lc_exp y). 
  { unfold lc_preserve in L. eapply L. apply H0. apply H2. }  
assert (H3 : R y z -> multi R z (m y) /\ multi R (m y) (m z)).
    { auto. 
}
assert (H4: R y z). auto. 
  apply H3 in H1. destruct H1.
  eapply multi_trans. 
  -- apply IHmulti. auto. 
  -- apply H3. auto. 
Qed.
Theorem Z_monotonic_m : forall (R : relation exp) (m : map exp), lc_preserve R -> Z_prop_m R m -> monotonic R m. 
Proof.
intros. unfold Z_prop_m in H. unfold monotonic. 
intros.
induction H2.
  - apply multi_refl.
  - assert (M : lc_exp y). 
  { unfold lc_preserve in H. eapply H. apply H1. apply H3. }  
assert (H4 : R y z -> multi R z (m y) /\ multi R (m y) (m z)).
    { auto. 
}
assert (H5: R y z). auto. 
  apply H4 in H2. destruct H2.
  eapply multi_trans. 
  -- apply IHmulti. auto. 
  -- apply H6. 
Qed.

Theorem semi_con_Z_prop : forall (R : relation exp), lc_preserve R -> Z_prop R -> semi_confluence R.
Proof.
intros R L H. apply Z_prop_to_m in H. destruct H as [map H].
assert (Z: Z_prop_m R map). auto.
apply Z_monotonic_m in Z.
unfold Z_prop_m in H. unfold monotonic in Z.
 unfold semi_confluence. intros.
induction H2.
  - exists m. split; auto. constructor. apply multi_R. assumption.
  -  assert (B: lc_exp y). unfold lc_preserve in L. eapply L. apply H0. auto. 
eapply H with (b:=z) in B; (try apply multi_R; auto). destruct B. assert (M: multi R m (map x)).
{
  apply H with (b:=m) in H0. destruct H0. auto. auto.
}
apply H in H1. destruct H1.
assert (N : multi R m (map y)).
{
eapply multi_trans. eauto. eauto.
}
exists (map y). split. auto. auto. auto.
-  auto.
Qed.

*)


Definition confluence (R : relation exp) : Prop := forall (e1 m n : exp),
multi R e1 m -> multi R e1 n -> (exists f, multi R m f /\ multi R n f).

Definition semi_confluence (R : relation exp) : Prop := forall (e1 m n : exp),
R e1 m -> multi R e1 n -> (exists f, multi R m f /\ multi R n f).

Theorem semi_conf_to_conf : forall (R : relation exp), semi_confluence R -> confluence R. 
Proof.
intros. unfold semi_confluence in H. unfold confluence. intros. 
induction H0.
  - exists n. split. auto. constructor. 
  - apply IHmulti in H1. destruct H1.  destruct H1. apply H  with (n := x0) in H0.
    -- destruct H0. destruct H0. exists x1. split; auto. eapply multi_trans. apply H3. auto. 
    -- auto.    
Qed.

Definition map (X : Type) := X -> X.

Definition monotonic (R : relation exp) (m : map exp) : Prop := forall (a b : exp), multi R a b -> multi R (m a) (m b). 



Definition Z_prop (R : relation exp) : Prop :=  exists (m : map exp), forall (a b : exp), R a b -> multi R b (m a) /\ multi R (m a) (m b).

Definition Z_prop_m (R : relation exp) (m : map exp) := forall (a b : exp), R a b -> multi R b (m a) /\ multi R (m a) (m b).

Lemma Z_prop_to_m : forall (R : relation exp),  Z_prop R -> exists m, Z_prop_m R m.
Proof.
intros.
unfold Z_prop in H. destruct H as [m H0]. exists m. unfold Z_prop_m. auto.
Qed.

(*Theorem Z_monotonic_helper : forall (R : relation exp) (a b : exp) (m : map exp), Z_prop R -> (R a b -> multi R b (m a) /\ multi R (m a) (m b))
 -> exists (m : map exp), multi R a b -> multi R (m a) (m b).
Proof.
intros. exists m. intros.
induction H1.
  - apply multi_refl.
  - unfold Z_prop in H. assert (H2 :  exists m : map exp, R x y -> multi R y (m x) /\ multi R (m x) (m y)).
    {
apply H with (a := x) (b := y).
}
  apply H2 in H0. destruct H0.
  eapply multi_trans. 
  -- apply H3.
 apply H in  
*)
Theorem Z_monotonic : forall (R : relation exp), Z_prop R -> exists (m : map exp), monotonic R m. 
Proof.
intros. unfold Z_prop in H. destruct H as [m H]. eexists. unfold monotonic. 
intros.
induction H0.
  - apply multi_refl.
  - assert (H2 : R y z -> multi R z (m y) /\ multi R (m y) (m z)).
    {
apply H with (a := y) (b := z).
}
  apply H2 in H0. destruct H0.
  eapply multi_trans. 
  -- apply IHmulti.
  -- apply H3.
Qed.
Theorem Z_monotonic_m : forall (R : relation exp) (m : map exp), Z_prop_m R m -> monotonic R m. 
Proof.
intros. unfold Z_prop_m in H. unfold monotonic. 
intros.
induction H0.
  - apply multi_refl.
  - assert (H2 : R y z -> multi R z (m y) /\ multi R (m y) (m z)).
    {
apply H with (a := y) (b := z).
}
  apply H2 in H0. destruct H0.
  eapply multi_trans. 
  -- apply IHmulti.
  -- apply H3.
Qed.

Theorem semi_con_Z_prop : forall (R : relation exp), Z_prop R -> semi_confluence R.
Proof.
intros. apply Z_prop_to_m in H. destruct H as [map H].
assert (Z: Z_prop_m R map). auto.
apply Z_monotonic_m in Z.
unfold Z_prop_m in H. unfold monotonic in Z.
 unfold semi_confluence. intros.
induction H1.
  - exists m. split; auto. constructor. apply multi_R. assumption.
  -  apply Z in H2. assert (M: multi R m (map x)).
{
  apply H in H0. destruct H0. auto.
}
apply H in H1. destruct H1.
assert (N : multi R m (map y)).
{
eapply multi_trans. eauto. eauto.
}
exists (map y). split. auto. auto.
Qed.
Theorem step_lc_preserve_one : forall e1 e2, lc_exp e1 -> e1 ---> e2 -> lc_exp e2.
Proof.
intros. induction H0. 
  - inversion H; subst. apply lc_body_exp_wrt_exp. 
  -- unfold body_exp_wrt_exp. intros. inversion H2; subst. auto. 
  -- auto. 
  - constructor. inversion H; subst.  apply IHstep in H3. auto. inversion H; subst.  auto.
  - inversion H; subst. constructor. apply IHstep in H4. auto. auto. 
  -  inversion H; subst. Admitted.
Theorem step_lc_preserve : lc_preserve step. 
Proof.
  unfold lc_preserve. intros. induction H0. auto. apply IHmulti in H. eapply step_lc_preserve_one in H; auto. apply H. auto.    
Qed.

Theorem app_lc : forall e1 e2, lc_exp (app e1 e2) -> lc_exp e2 /\ lc_exp e1.
Proof.
intros. inversion H. auto.
Qed.




Theorem open_first_step :
  forall (e1 e1' e2 : exp), e1 ---> e1' -> (open_exp_wrt_exp e1 e2) ---> (open_exp_wrt_exp e1' e2). 
Proof.
  intros. generalize dependent e2. generalize dependent e1'. induction e1; intros e1' H e2 . 
  - unfold open_exp_wrt_exp. unfold open_exp_wrt_exp_rec. destruct n; simpl. inversion H. inversion H. 
  - inversion H. 
  - inversion H; subst.   unfold open_exp_wrt_exp. unfold open_exp_wrt_exp in IHe1. 
    simpl. apply step_abs. Admitted. 
Theorem open_second_step :
  forall (e1 e2' e2 : exp), e2 ---> e2' -> (open_exp_wrt_exp e1 e2) ---> (open_exp_wrt_exp e1 e2'). 
Proof.
intros. generalize dependent e1. generalize dependent e2'. induction e2; intros e2' H e1.
- inversion H.  
- inversion H.
- inversion H; subst. unfold open_exp_wrt_exp. Admitted.


(*app with built in beta reduce*)
Fixpoint app_beta (e1 e2 : exp) : exp :=
  match e1 with
  | (abs e) => (open_exp_wrt_exp e e2)
  | _ => (app e1 e2)
end.

Theorem app_beta_resolve : forall (e1 e2: exp), app e1 e2 -->* app_beta e1 e2.
Proof.
intros. induction e1; unfold app_beta; try constructor.
apply multi_R. constructor.  
Qed.

Theorem app_beta_one : forall (e1 e2 e1': exp), e1 ---> e1' -> app_beta e1 e2 -->* app_beta e1' e2. 
Proof.
intros. generalize dependent e2. 
induction e1.
- inversion H.  
- inversion H.
- intros. inversion H; subst. unfold app_beta. apply multi_R. apply open_first_step. auto.
- intros. unfold app_beta. fold app_beta.
  inversion H. 
  -- assert (A : (app (app (abs e1) e1_2) e2 ) -->* app (open e1 e1_2) e2).
   apply multi_R. constructor. constructor.
    assert (B : app (open e1 e1_2) e2 -->*  app_beta (open e1 e1_2) e2). apply app_beta_resolve. 
     eapply multi_trans. apply A. apply B. 
  -- unfold app_beta. apply multi_R. constructor. constructor. auto. 
  -- unfold app_beta. apply multi_R. constructor. constructor. auto.
Qed.

Theorem app_beta_one_multi : forall (e1 e2 e1': exp), e1 -->* e1' -> app_beta e1 e2 -->* app_beta e1' e2.
Proof.
intros. induction H. constructor. apply app_beta_one  with (e2 := e2) in H. eapply multi_trans. apply IHmulti. auto.   
Qed. 

Theorem app_beta_two : forall (e1 e2 e2': exp), e2 ---> e2' -> app_beta e1 e2 ---> app_beta e1 e2'. 
Proof.
intros. induction e2.
- inversion H.  
- inversion H.
- inversion H; subst. unfold app_beta. destruct e1. 
  -- apply step_app_2. apply step_abs. auto.
  -- apply step_app_2. apply step_abs. auto.
  -- apply open_second_step. apply step_abs. auto.
  -- apply step_app_2. apply step_abs. auto.
- inversion H; subst. unfold app_beta. destruct e1; try (apply step_app_2; apply step_beta). 
  apply open_second_step. apply step_beta.
         unfold app_beta. destruct e1; try (apply step_app_2; apply step_app; auto). 
  apply  open_second_step. apply step_app. auto.
    unfold app_beta. destruct e1; try (apply step_app_2; apply step_app_2; auto). 
   apply  open_second_step. apply step_app_2. auto.
Qed.

Theorem app_beta_cong : forall (e1 e1' e2 e2' : exp), e1 -->* e1' -> e2 -->* e2' -> app_beta e1 e2 -->* app_beta e1' e2'. 
Proof.
  intros e1  e1' e2 e2' G H.
  assert (A : app_beta e1 e2 -->* app_beta e1' e2). apply app_beta_one_multi. auto.
  eapply multi_trans. apply A.  
  induction H. 
  - constructor. 

  - apply app_beta_two  with (e1 := e1') in H. eapply multi_trans. apply IHmulti. auto. apply multi_R. auto.
Qed.

(*the mapping function that satisfies Z-property*)
Fixpoint Z_map (e : exp) : exp :=
match e with
  | var_b n => var_b n
  | var_f e1 => var_f e1
  | abs e1 => abs (Z_map e1)
  | app e1 e2 => app_beta (Z_map e1) (Z_map e2)
end.


Theorem test_beta_eq : forall (e1 e2 : exp), 
     multi step (app (Z_map e1) (Z_map e2)) (Z_map (app e1 e2)).
Proof.
intros. simpl. destruct (Z_map e1).
  - constructor.
  - constructor.
  - simpl. apply multi_step with (y :=  app (abs e) (Z_map e2)). constructor; auto. constructor.
  - simpl. constructor.
Qed.


(*Theorem lc_step : forall (e1 e2 : exp), e1 ---> e2 -> lc_exp e1 -> lc_exp e2.
intros.
induction H; simpl.
- apply lc_abs in H. *)

Theorem multi_app: forall (e1 e1' e2 e2' : exp), e1 -->* e1' -> e2 -->* e2' -> app e1 e2 -->* app e1' e2'.
Proof.
intros. 
induction H. induction H0. constructor.
  -  eapply step_app_2 in H. eapply multi_step. apply H. apply IHmulti.
  - induction H0.
  --  eapply step_app in H. eapply multi_step. apply H. apply IHmulti.
  --  eapply step_app in H. eapply multi_step. apply H. apply IHmulti.
Qed.
Theorem multi_abs : forall (e1 e2 : exp), e1 -->* e2 -> abs e1 -->* abs e2.
Proof.
intros. 
induction H. constructor. 
apply step_abs in H. eapply multi_step. apply H. apply IHmulti.

Qed.
Theorem step_Z_map : forall (e : exp), e -->* (Z_map e).
Proof. intros. induction e; simpl; try constructor.
  - apply multi_abs. auto.
  - destruct (Z_map e1). 
    -- unfold app_beta. apply multi_app; auto.
    -- unfold app_beta. apply multi_app; auto.
    -- unfold app_beta. 
     assert (H2: (app e1 e2) -->* (app (abs e) (Z_map e2))). 
{
  apply multi_app; auto.
}
    apply multi_step with (y:= (app (abs e) (Z_map e2))). 
  --- apply step_beta. 
  --- auto.
  -- unfold app_beta. apply multi_app; auto. 
Qed.

(*Theorem lol : forall (e1 e2 e3: exp) x,  x `notin` fv_exp e1 `union` fv_exp e2 -> (open_exp_wrt_exp e1 e2) = (open_exp_wrt_exp e1 e3) <-> 
  exists e, [x~>e2]e = [x~>e3]e.
Proof.
intros. unfold open_exp_wrt_exp. 
  assert(A : open_exp_wrt_exp e1 e2
Qed.
*)
Theorem abs_step : forall (e1 e1': exp), e1 -->* e1' -> abs e1 -->* abs e1'. 
Proof.
intros. induction H. 
  - constructor. 
  - apply step_abs in H. eapply multi_step. apply H. auto. 
Qed.


Theorem open_Z_map : forall x e1, (open (Z_map e1) (var_f x)) = Z_map (open e1 (var_f x)).
Proof.
intros. induction e1. 
- simpl. unfold open. unfold open_exp_wrt_exp_rec. destruct n. auto. auto. 
- simpl. auto. 
- simpl. unfold open. unfold open_exp_wrt_exp_rec.  fold open_exp_wrt_exp_rec. f_equal.
  unfold open in IHe1. Admitted.

Theorem abs_exists : forall e1 e1', abs e1 ---> e1' -> exists x, e1' = abs x /\ e1 -->* x.
Proof.
intros. inversion H. subst. exists e1'0. split; auto. apply multi_R. auto.  
Qed.
Require Import Coq.Program.Equality.

Theorem abs_exists_multi : forall e1 e1',  abs e1 -->* e1' -> exists x, e1' = abs x /\ e1 -->* x.
Proof.
intros. dependent induction H. 
- exists e1. split. auto. constructor.
- assert (H1: exists x : exp, y = abs x /\ e1 -->* x) . apply IHmulti. auto. 
  destruct H1. destruct H1. subst. apply abs_exists in H. destruct H. exists x0. destruct H. split. auto.
  eapply multi_trans. apply H2. auto.       
Qed.

Theorem kms: forall a  e x u, a <> x -> [x ~> u](open e (var_f a)) = (open [x ~>u] e (var_f a)).
Proof.
intros.
  dependent induction e.
  -  
Qed. 

Theorem subst_lift : forall a e' e x u, [x ~> u]e -->* e' -> [x ~> u](open e (var_f a)) -->* open e' (var_f a).
Proof.
  intros. 
  dependent induction H. 
  -  
Admitted. 


Theorem subst_step_one : forall x u u' e, u ---> u' -> [x ~> u]e -->* [x ~> u']e.
Proof.
intros. induction e. 
  - simpl. constructor. 
  - simpl. destruct (x0 == x). 
    -- apply multi_R. auto. 
    -- constructor. 
  - simpl. apply multi_abs. auto. 
  - simpl. apply multi_app; auto. 
Qed.  

Theorem subst_step_one_multi : forall x u u' e, u -->* u' ->  [x ~> u]e -->* [x ~> u']e.
Proof.
intros. induction H. constructor. apply subst_step_one with (x := x) (e := e) in H. eapply multi_trans. apply IHmulti. auto. 
Qed.   
Theorem subst_step_two : forall e x u e' ,lc_exp u -> e ---> e' -> [x ~> u]e -->* [x ~> u]e'.
Proof.
intros e. induction e; intros.
  - inversion H0. 
  - inversion H0.
  - inversion H0; subst. apply multi_abs. apply IHe. auto. auto. 
  - inversion H0; subst.
    --  simpl. 
assert (A: app (abs [x ~> u] (e0)) [x ~> u] (e2) -->* open ([x~>u] e0) ([x~>u] e2)). apply multi_R. constructor. 
eapply multi_trans. apply A. simpl.  
 assert (B: open [x ~> u] (e0) [x ~> u] (e2) = [x ~> u] (open e0 e2)).
 symmetry. apply subst_exp_open_exp_wrt_exp. auto. rewrite -> B. constructor. 
  -- simpl. apply multi_app. auto. constructor.  
  -- simpl. apply multi_app. constructor. auto. 
Qed.  
Theorem subst_step_two_multi : forall e x u e' ,lc_exp u -> e -->* e' -> [x ~> u]e -->* [x ~> u]e'.
Proof.
intros. induction H0. constructor. eapply subst_step_two in H; try apply H0. eapply multi_trans. apply IHmulti. apply H. 
Qed.   
(* Theorem subst_step : forall x u u' e e', lc_exp u -> u -->* u' -> e -->* e' -> [x ~> u]e -->* [x ~> u']e'. 
Proof.
intros. 
assert (B: [x ~> u] (e) -->* [x ~> u] e'). apply subst_step_two_multi. auto. auto. 
assert (A: [x ~> u] (e') -->* [x ~> u'] e'). apply subst_step_one_multi. auto. 
eapply multi_trans. apply B. apply A. Qed. *)


Theorem subst_step : forall x u u' e e', u -->* u' -> e -->* e' -> [x ~> u]e -->* [x ~> u']e'. Proof. Admitted.
Theorem subst_Z_map : forall x (e1 e2 : exp),  [x ~> (Z_map e1)] (Z_map e2) -->* Z_map ([x ~> e1] e2).
Proof.
intros x e1 e2.
induction e2; intros. 
  - simpl. constructor. 
  - simpl. destruct (x0 == x). constructor. unfold Z_map. constructor. 
  - simpl. apply multi_abs. auto. 
  - simpl.

 
 destruct (Z_map e2_1). 
    -- unfold app_beta. fold app_beta. unfold subst_exp. fold subst_exp. unfold subst_exp in IHe2_1. fold subst_exp in IHe2_1.
       assert (H : app (var_b n) [x ~> Z_map e1] (Z_map e2_2) -->* app (Z_map [x ~> e1] (e2_1)) (Z_map [x ~> e1] (e2_2))).
{
  apply multi_app; auto. 
}
  assert (G : multi step (app (Z_map [x ~> e1] (e2_1)) (Z_map [x ~> e1] (e2_2))) (Z_map (app [x ~> e1] (e2_1)  [x ~> e1] (e2_2)))).
{
  apply test_beta_eq.
}
  simpl in G. eapply multi_trans. apply H. apply G. 
   --  unfold app_beta. fold app_beta. unfold subst_exp. fold subst_exp. unfold subst_exp in IHe2_1. fold subst_exp in IHe2_1.
       assert (H : app (if x0 == x then Z_map e1 else var_f x0) [x ~> Z_map e1] (Z_map e2_2) -->* app (Z_map [x ~> e1] (e2_1)) (Z_map [x ~> e1] (e2_2))).
{
  apply multi_app; auto. 
}
  assert (G : multi step (app (Z_map [x ~> e1] (e2_1)) (Z_map [x ~> e1] (e2_2))) (Z_map (app [x ~> e1] (e2_1)  [x ~> e1] (e2_2)))).
{
  apply test_beta_eq.
}
  simpl in G. eapply multi_trans. apply H. apply G. 
  -- simpl. 
    assert (E : exists v, Z_map [x~>e1] (e2_1) = (abs v) /\ [x ~> Z_map e1] e -->* v).
    {
  apply abs_exists_multi. simpl in IHe2_1. auto.  
} 
destruct E. destruct H. 
pick fresh a for (union (fv_exp x0) (union ({{x}}) (union (fv_exp (Z_map e1)) (fv_exp e)))). 
  assert(A: open e (Z_map e2_2) = [a ~> Z_map e2_2] (open e (var_f a))). { apply subst_exp_intro. auto. }
  rewrite -> A. rewrite -> subst_exp_subst_exp; try fsetdec. 
  assert (H1: ([x ~> Z_map e1] (open e (var_f a))) -->* open x0 (var_f a)). apply subst_lift. auto.
    rewrite -> H. simpl.  
  assert(B: open x0 (Z_map [x ~> e1] (e2_2)) = [a ~> (Z_map [x ~> e1] (e2_2))] (open x0 (var_f a))). { apply subst_exp_intro. auto. }
  rewrite -> B. apply subst_step.  auto. auto. 
 -- unfold app_beta. fold app_beta. unfold subst_exp. fold subst_exp. unfold subst_exp in IHe2_1. fold subst_exp in IHe2_1.
       assert (H : app (app [x ~> Z_map e1] (e2) [x ~> Z_map e1] (e3))[x ~> Z_map e1] (Z_map e2_2) -->* app (Z_map [x ~> e1] (e2_1)) (Z_map [x ~> e1] (e2_2))).
{
  apply multi_app; auto. 
}
  assert (G : multi step (app (Z_map [x ~> e1] (e2_1)) (Z_map [x ~> e1] (e2_2))) (Z_map (app [x ~> e1] (e2_1)  [x ~> e1] (e2_2)))).
{
  apply test_beta_eq.
}
  simpl in G. eapply multi_trans. apply H. apply G.
Qed. 


Theorem open_Z_map_step : forall (e1 e2 : exp), (open_exp_wrt_exp (Z_map e1) (Z_map e2)) -->* Z_map (open_exp_wrt_exp e1 e2). 
Proof.
intros e1 e2.
pick fresh a for (union (fv_exp e1) (fv_exp (Z_map e1))). 
assert (A : open (Z_map e1) (Z_map e2) = [a ~> Z_map e2] (open (Z_map e1) (var_f a))). apply subst_exp_intro. fsetdec. 
assert (B : open e1 e2 = [a ~> e2] (open e1 (var_f a))). apply subst_exp_intro. fsetdec.
rewrite -> open_Z_map in A. rewrite -> A. rewrite -> B. apply subst_Z_map. 
Qed.  


Theorem open_step :
  forall (e1 e2 e1' e2' : exp),
      e1 -->* e1' -> e2 -->* e2' -> (open_exp_wrt_exp e1 e2) -->* (open_exp_wrt_exp e1' e2'). 
Proof.
  intros e1 e2 e1' e2' G H.
  induction G. 
  - induction H. 
    -- constructor. 
    -- eapply open_second_step in H. eapply multi_step.  apply H. auto. 
  - induction H.
    -- eapply open_first_step in H0. eapply multi_step.  apply H0. auto.
    -- eapply open_first_step in H0. eapply multi_step.  apply H0. auto. 
Qed.


(*Theorem beta_Z_property : Z_prop step.
Proof.
unfold Z_prop. exists Z_map. intros a b H. 
assert (LL: lc_preserve step). apply step_lc_preserve.  
induction H.
assert (H: (app (abs e1) e2) ---> (open_exp_wrt_exp e1 e2)). constructor.  
     assert (L: (Z_map (app (abs e1) e2)) = (open_exp_wrt_exp (Z_map e1) (Z_map e2))).
{
  unfold Z_map. unfold app_beta. reflexivity. 
}
- split. 
  -- assert (M:  e1 -->* (Z_map e1)). apply step_Z_map.
    assert (N: e2 -->* (Z_map e2)). apply step_Z_map.
    assert (O: open_exp_wrt_exp e1 e2 -->* open_exp_wrt_exp (Z_map e1) (Z_map e2)). apply open_step; auto.
    rewrite <- L in O. auto. 
  -- assert (M:   open_exp_wrt_exp (Z_map e1) (Z_map e2) -->* (Z_map (open_exp_wrt_exp e1 e2))). apply open_Z_map_step. 
    rewrite <- L in M. auto. 
- split. 
  -- assert (L1: lc_exp e1). inversion H0; subst. auto. destruct IHstep; auto. assert (M:  e2 -->* Z_map e2). apply step_Z_map.
     assert (N: app e1' e2 -->* app (Z_map e1) (Z_map e2)). apply multi_app; auto. 
     eapply multi_trans. apply N. apply test_beta_eq. 
  -- assert (L1: lc_exp e1). inversion H0; subst. auto. destruct IHstep; auto. unfold Z_map. fold Z_map. simpl. apply app_beta_cong; auto. constructor.
- split.
  --   assert (L1: lc_exp e2). inversion H0; subst. auto.  destruct IHstep; auto. assert (M:  e1 -->* Z_map e1). apply step_Z_map.
     assert (N: app e1 e2' -->* app (Z_map e1) (Z_map e2)). apply multi_app; auto. 
     eapply multi_trans. apply N. apply test_beta_eq. 
  --  assert (L1: lc_exp e2). inversion H0; subst. auto.  destruct IHstep; auto.  unfold Z_map. fold Z_map. simpl. apply app_beta_cong; auto. constructor.
- destruct IHstep. split. 
  -- assert (M:  e1 -->* Z_map e1). apply step_Z_map. unfold Z_map. fold Z_map. apply abs_step. auto.
  -- unfold Z_map. fold Z_map. apply abs_step. auto. 
 
Qed.
*)
Theorem beta_Z_property : Z_prop step.
Proof.
unfold Z_prop. exists Z_map. intros a b H. 
induction H.
assert (H: (app (abs e1) e2) ---> (open_exp_wrt_exp e1 e2)). constructor.  
     assert (L: (Z_map (app (abs e1) e2)) = (open_exp_wrt_exp (Z_map e1) (Z_map e2))).
{
  unfold Z_map. unfold app_beta. reflexivity. 
}
- split. 
  -- assert (M:  e1 -->* (Z_map e1)). apply step_Z_map.
    assert (N: e2 -->* (Z_map e2)). apply step_Z_map.
    assert (O: open_exp_wrt_exp e1 e2 -->* open_exp_wrt_exp (Z_map e1) (Z_map e2)). apply open_step; auto.
    rewrite <- L in O. auto. 
  -- assert (M:   open_exp_wrt_exp (Z_map e1) (Z_map e2) -->* (Z_map (open_exp_wrt_exp e1 e2))). apply open_Z_map_step. 
    rewrite <- L in M. auto. 
- split. 
  -- destruct IHstep. assert (M:  e2 -->* Z_map e2). apply step_Z_map.
     assert (N: app e1' e2 -->* app (Z_map e1) (Z_map e2)). apply multi_app; auto. 
     eapply multi_trans. apply N. apply test_beta_eq. 
  -- destruct IHstep. unfold Z_map. fold Z_map. simpl. apply app_beta_cong; auto. constructor.
- destruct IHstep. split.
  --  assert (M:  e1 -->* Z_map e1). apply step_Z_map.
     assert (N: app e1 e2' -->* app (Z_map e1) (Z_map e2)). apply multi_app; auto. 
     eapply multi_trans. apply N. apply test_beta_eq. 
  --  unfold Z_map. fold Z_map. simpl. apply app_beta_cong; auto. constructor.
- destruct IHstep. split. 
  -- assert (M:  e1 -->* Z_map e1). apply step_Z_map. unfold Z_map. fold Z_map. apply abs_step. auto.
  -- unfold Z_map. fold Z_map. apply abs_step. auto. 
 
Qed.

Theorem church_rosser : confluence step.
Proof.
apply semi_conf_to_conf. apply semi_con_Z_prop. apply beta_Z_property.
Qed.

Inductive reducible : typ -> exp -> Prop :=
  | red_arrow : forall (G:ctx) (e:exp) (U V:typ),
    typing G e (typ_arrow U V) ->
    (forall (u:exp), 
      strong_norm u -> reducible V (app e u)) ->
    reducible (typ_arrow U V) e
  | red_atom : forall (G:ctx) (e:exp),
    typing G e typ_base ->
    strong_norm e ->
    reducible typ_base e.

Theorem all_types_inhabited : forall (T:typ),
  exists (G:ctx) (e:exp),
  typing G e T.
Proof.
  intros.
  exists [(fresh nil, T)].
  exists (var_f (fresh nil)).
  auto. Qed.

Theorem sn_red: forall (G:ctx) (T:typ) (e:exp),
  typing G e T ->
  reducible T e ->
  strong_norm e.
Proof.
  induction T.
  - intros e Ht Hr.
    inversion Hr; subst; auto. 
  - intros t Htt Hrt.
    inversion Hrt; subst.
    