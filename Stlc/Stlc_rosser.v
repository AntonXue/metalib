Require Import Metalib.Metatheory.
(** syntax *)
Definition index : Set := nat.

Inductive typ : Set :=  (*r types *)
 | typ_base : typ (*r base type *)
 | typ_arrow (T1:typ) (T2:typ) (*r function types *).

Inductive exp : Set :=  (*r expressions *)
 | var_b (_:nat) (*r variables *)
 | var_f (x:var) (*r variables *)
 | abs (e:exp) (*r abstractions *)
 | app (e1:exp) (e2:exp) (*r applications *).

Definition ctx : Set := list ( atom * typ ).

(* EXPERIMENTAL *)
(** auxiliary functions on the new list types *)
(** library functions *)
(** subrules *)
(** arities *)
(** opening up abstractions *)
Fixpoint open_exp_wrt_exp_rec (k:nat) (e_5:exp) (e__6:exp) {struct e__6}: exp :=
  match e__6 with
  | (var_b nat) => 
      match lt_eq_lt_dec nat k with
        | inleft (left _) => var_b nat
        | inleft (right _) => e_5
        | inright _ => var_b (nat - 1)
      end
  | (var_f x) => var_f x
  | (abs e) => abs (open_exp_wrt_exp_rec (S k) e_5 e)
  | (app e1 e2) => app (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
end.

Definition open_exp_wrt_exp e_5 e__6 := open_exp_wrt_exp_rec 0 e__6 e_5.

(** terms are locally-closed pre-terms *)
(** definitions *)

(* defns LC_exp *)
Inductive lc_exp : exp -> Prop :=    (* defn lc_exp *)
 | lc_var_f : forall (x:var),
     (lc_exp (var_f x))
 | lc_abs : forall (e:exp),
      ( forall x , lc_exp  ( open_exp_wrt_exp e (var_f x) )  )  ->
     (lc_exp (abs e))
 | lc_app : forall (e1 e2:exp),
     (lc_exp e1) ->
     (lc_exp e2) ->
     (lc_exp (app e1 e2)).
(** free variables *)
Fixpoint fv_exp (e_5:exp) : vars :=
  match e_5 with
  | (var_b nat) => {}
  | (var_f x) => {{x}}
  | (abs e) => (fv_exp e)
  | (app e1 e2) => (fv_exp e1) \u (fv_exp e2)
end.

(** substitutions *)
Fixpoint subst_exp (e_5:exp) (x5:var) (e__6:exp) {struct e__6} : exp :=
  match e__6 with
  | (var_b nat) => var_b nat
  | (var_f x) => (if eq_var x x5 then e_5 else (var_f x))
  | (abs e) => abs (subst_exp e_5 x5 e)
  | (app e1 e2) => app (subst_exp e_5 x5 e1) (subst_exp e_5 x5 e2)
end.


Definition is_value (e : exp) : Prop :=
  match e with
  | abs _   => True
  | _       => False
  end.

Module StlcNotations.
Notation "[ z ~> u ] e" := (subst_exp u z e) (at level 0).
Notation open e1 e2     := (open_exp_wrt_exp e1 e2).
End StlcNotations.


(** definitions *)

(* defns JTyping *)
Inductive typing : ctx -> exp -> typ -> Prop :=    (* defn typing *)
 | typing_var : forall (G:ctx) (x:var) (T:typ),
      uniq  G  ->
      binds  x T G  ->
     typing G (var_f x) T
 | typing_abs : forall (L:vars) (G:ctx) (e:exp) (T1 T2:typ),
      ( forall x , x \notin  L  -> typing  (( x ~ T1 )++ G )   ( open_exp_wrt_exp e (var_f x) )  T2 )  ->
     typing G (abs e) (typ_arrow T1 T2)
 | typing_app : forall (G:ctx) (e1 e2:exp) (T2 T1:typ),
     typing G e1 (typ_arrow T1 T2) ->
     typing G e2 T1 ->
     typing G (app e1 e2) T2.

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
Theorem open_first_step :
  forall (e1 e1' e2 : exp), e1 ---> e1' -> (open_exp_wrt_exp e1 e2) ---> (open_exp_wrt_exp e1' e2). 
Proof.
  intros. generalize dependent e2. generalize dependent e1'. induction e1; intros e1' H e2 . 
  - unfold open_exp_wrt_exp. unfold open_exp_wrt_exp_rec. destruct n; simpl. inversion H. inversion H. 
  - inversion H. 
  - inversion H; subst.   unfold open_exp_wrt_exp. unfold open_exp_wrt_exp in IHe1. 
    simpl. apply step_abs. unfold open_exp_wrt_exp_rec.

Theorem open_second_step :
  forall (e1 e1' e2 : exp), e2 ---> e1' -> (open_exp_wrt_exp e1 e2) ---> (open_exp_wrt_exp e1 e1'). 
Proof.
  Admitted.
(*app with built in beta reduce*)
Fixpoint app_beta (e1 e2 : exp) : exp :=
  match e1 with
  | (abs e) => (open_exp_wrt_exp e e2)
  | _ => (app e1 e2)
end.
Theorem app_beta_one : forall (e1 e2 e1': exp), e1 ---> e1' -> app_beta e1 e2 ---> app_beta e1' e2. 
Proof.
intros. generalize dependent e2. 
induction e1.
- inversion H.  
- inversion H.
- intros. inversion H; subst. unfold app_beta. apply open_first_step. auto.
- intros. unfold app_beta. fold app_beta. Admitted.

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
  intros e1 e2 e1' e2' G H.
  induction G. 
  - induction H. 
    -- constructor. 
    -- eapply app_beta_two in H. eapply multi_step.  apply H. auto. 
  - induction H.
    -- eapply app_beta_one in H0. eapply multi_step.  apply H0. auto.
    -- eapply app_beta_one in H0. eapply multi_step.  apply H0. auto.  
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


Theorem abs_step : forall (e1 e1': exp), e1 -->* e1' -> abs e1 -->* abs e1'. 
Proof.
intros. induction H. 
  - constructor. 
  - apply step_abs in H. eapply multi_step. apply H. auto. 
Qed.
Theorem subst_Z_map : forall (e1 e2 : exp), (open_exp_wrt_exp (Z_map e1) (Z_map e2)) -->* Z_map (open_exp_wrt_exp e1 e2). 
Proof.
intros e1 e2.
induction e1. 
  - simpl. unfold open_exp_wrt_exp. destruct n. unfold open_exp_wrt_exp_rec; simpl. constructor.
    unfold open_exp_wrt_exp_rec. simpl. constructor.
  - simpl. unfold open_exp_wrt_exp. simpl. constructor.
  - simpl. unfold open_exp_wrt_exp. simpl. unfold open_exp_wrt_exp in IHe1. apply abs_step.
    

    inversion L1; subst. constructor

Theorem whatever : forall (e1 e1' e2 e2' : exp), e1 -->* e1' -> e2 -->* e2' -> open_exp_wrt_exp_rec 0 e2' e1' -->* (open_exp_wrt_exp_rec 0 e2 e1) ->
open_exp_wrt_exp_rec 1 e2' e1' -->* (open_exp_wrt_exp_rec 1 e2 e1).
Proof.
intros.
induction e1'. 
  - destruct n. unfold open_exp_wrt_exp_rec in H1; simpl in H1. fold open_exp_wrt_exp_rec in H1.
    unfold open_exp_wrt_exp_rec; simpl. fold open_exp_wrt_exp_rec. inversion H.  constructor.
    unfold open_exp_wrt_exp_rec. simpl. constructor.
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
  -- assert (M:   open_exp_wrt_exp (Z_map e1) (Z_map e2) -->* (Z_map (open_exp_wrt_exp e1 e2))). apply subst_Z_map. 
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
    