(* Require Import Lemmas. *)
Require Import Metalib.Metatheory.
Require Import Metalib.MetatheoryAtom.
Require Import Stlc.Stlc.

Require Import Coq.FSets.FSetInterface.
Require Import Metalib.CoqListFacts.
Require Import Metalib.CoqFSetInterface.
Require Import Metalib.FSetExtra.
Require Import Metalib.FSetWeakNotin.
Require Import Metalib.LibTactics.

Definition norm (e : exp) : Prop :=
      (~ exists e2, step e e2).
(* 
Inductive wn (G:ctx) : ctx -> typ -> exp -> Prop :=
  | wn_ne : forall (T:typ) (e:exp) (x:var),  
    neutral G T e -> wn G T e
  | wn_lam : forall (A B:typ) (e:exp) (x:var),
    wn ((x ~ A) ++ G) B e ->
    wn G (typ_arrow A B) (abs a)   *)



Fixpoint degree_typ (T:typ) : nat :=
  match T with
  | typ_base => 1
  | (typ_arrow t1 t2) => S (max (degree_typ t1) (degree_typ t2))
  end.

Inductive degree_redex : ctx -> typ -> exp -> nat -> Prop :=
  | deg_app_abs : forall (G:ctx) (e1 e2:exp) (U V:typ),
    typing G (abs e1) (typ_arrow U V) ->
    degree_redex G (typ_arrow U V)
      (app (abs e1) e2) (degree_typ (typ_arrow U V)).
  (* | deg_otherwise : forall (G:ctx) (e:exp),
    ~(exists (e1 e2:exp), e = (app (abs e1) e2)) ->
    degree_redex e 0. *)

Lemma degree_redex_unique : forall (e:exp) 
    (G:ctx) (T:typ) (n m:nat),
  degree_redex G T e n ->
  degree_redex G T e m ->
  n = m.
Proof.
  intros e G T n m Hn Hm.
  inversion Hn; inversion Hm; subst.
  inversion H6; subst. reflexivity.
Qed.

Definition tm_deg_type (t:typ) (e:exp) : typ :=
  match e with
  | (app e1 e2) => match t with
    | (typ_arrow U V) => U
    | (typ_base) => typ_base (*this should never happen if e is well-typed*)
    end
  | _ => t
  end.

  
Definition atom_fresh_for_set (L:atoms) :=
  match (atom_fresh L) with
  | (exist _ x _ ) => x
  end.


Inductive degree_term : ctx -> typ -> exp -> nat -> Prop :=
  | deg_app_redex : forall (e1 e2:exp) (G:ctx) (U V:typ) (n m r:nat),
    degree_term G (tm_deg_type (typ_arrow U V) e1) e1 n ->
    degree_term G (tm_deg_type U e2) e2 m ->
    degree_redex G (typ_arrow U V) (app e1 e2) r ->
    degree_term G (typ_arrow U V) (app e1 e2) (max (max n m) r)
  | deg_app_no_redex : forall (e1 e2: exp) (G:ctx) (U V:typ) (n m:nat),
    degree_term G (tm_deg_type (typ_arrow U V) e1) e1 n ->
    degree_term G (tm_deg_type U e2) e2 m ->
    ~(exists (r:nat), degree_redex G (typ_arrow U V) (app e1 e2) r) ->
    degree_term G (typ_arrow U V) (app e1 e2) (max n m)
  | deg_abs : forall (e:exp) (G:ctx) (U V:typ) (L:vars)
      (n m:nat),
    degree_term (((atom_fresh_for_set L) ~ U )++ G ) (tm_deg_type V e)
      (open_exp_wrt_exp e (var_f (atom_fresh_for_set L))) n ->
    degree_term G (typ_arrow U V) (abs e) n
  | deg_var_f : forall (G:ctx) (T:typ) (x:var),
    typing G (var_f x) T ->
    degree_term G T (var_f x) 0
  | deg_var_b : forall (G:ctx) (T:typ) (n:nat),
    typing G (var_b n) T ->
    degree_term G T (var_b n) 0.

Hint Constructors degree_redex degree_term : core.


Lemma degree_unique : forall (G:ctx) (T:typ) (e:exp) (n m:nat),
  degree_term G T e n ->
  degree_term G T e m ->
  n = m.
Proof.
  intros G T e n m Hn.
  generalize dependent m.
  induction Hn.
  - intros deg Hdeg; inversion Hdeg; subst.
    + assert (Hr:r0 = r). {
        eapply degree_redex_unique.
        apply H8. apply H.
      }
      subst.
      apply IHHn1 in H5; subst.
      apply IHHn2 in H7; subst. auto.
    + exfalso. apply H8. exists r. apply H.
  - intros deg Hdeg; inversion Hdeg; subst; auto.
    exfalso. apply H. exists r. apply H8.
  - intros deg Hdeg; inversion Hdeg; subst.
    apply IHHn in H4. assumption.
  - intros deg Hdeg; inversion Hdeg; auto.
  - intros deg Hdeg; inversion Hdeg; auto.
Qed.

Lemma degree_total : forall (e:exp) (G:ctx) (T:typ),
  typing G e T ->
  exists (n:nat), degree_term G T e n.
Proof.
  intros e G T H.
  induction H.
  - exists 0. auto.
  - assert (Hi: (atom_fresh_for_set (fv_exp e)) \notin (L) )
  - intros G T Ht.
    inversion Ht; subst.
    


(* Lemma redex_le_term : forall (e:exp) (n m:nat),
  degree_redex e n ->
  degree_term e m ->
  n <= m.
Proof.
  intros e n m Hred Hexp.
  inversion Hred; subst.
  inversion Hexp; subst. *)



Lemma degree_subst : forall (G:ctx) (t u:exp) (x:var) (U V:typ) 
                            (dt du dU dc:nat),
  degree_term G U t dt ->
  degree_term G U u du ->
  degree_typ U dU ->
  typing G (abs t)  ->
  degree_term (open_exp_wrt_exp t u x).

(* Fixpoint degree (e:exp) : nat :=
  match e with
  | (abs e') => S (degree e')
  | (app e1 e2) => (degree e1) + (degree e2)
  | _ => 0
  end.  *)


(* Inductive degree : exp -> nat -> Prop :=
  | deg_abs : forall (e:exp) (n:nat),
    degree e n ->
    degree (abs e) (S n)
  | deg_app : forall (e1 e2:exp) (n m:nat),
    degree e1 n ->
    degree e2 m ->
    degree (app e1 e2) (max n m)
  | deg_var_f : forall (v:var),
    degree (var_f v) 0
  | deg_var_b : forall (n:nat),
    degree (var_b n) 0.

Hint Constructors degree : core.

Lemma degree_total : forall (e:exp),
  exists (n:nat),
  degree e n.
Proof.
  induction e.
  (* var_b *)
  - exists 0. auto.
  (* var_f *)
  - exists 0. auto.
  (* abs *)
  - destruct IHe as [n IHn].
    exists (S n). auto.
  - destruct IHe1 as [n IHn].
    destruct IHe2 as [m IHm].
    exists (max n m). auto.
Qed.

Lemma degree_unique : forall (e:exp) (n m:nat),
  degree e n ->
  degree e m ->
  n = m.
Proof.
  intros e n m Hn.
  generalize dependent m.
  induction Hn; try intros m Hm.
  - inversion Hm; subst.
    apply IHHn in H0; subst. reflexivity.
  - intros k Hk. inversion Hk; subst.
    apply IHHn1 in H1; subst.
    apply IHHn2 in H3; subst.
    reflexivity.
  - inversion Hm. reflexivity.
  - inversion Hm. reflexivity.
Qed.   *)

(* Lemma open_preserves_deg : forall (t u:exp),
  lc_exp (abs t) ->
  lc_exp u ->
  degree (open_exp_wrt_exp t u) = degree t. *)

Lemma step_dec_deg : forall (e e':exp),
  e ---> e' ->
  degree e = S (degree e').
Proof.
  intros e e' H.
  induction H.
  - simpl. destruct (degree e2).
    + 

Theorem weak_norm :
  forall (G:ctx) (e:exp) (T:typ),
  typing G e T ->
  exists (e':exp),
  e -->* e' /\ norm e'.
Proof.
  intros G e T Ht.
  assert (Hd: exists (n:nat), degree e n).
  { apply degree_total. }
  destruct Hd as [n Hd].
  

  (* - exists (var_b n). split. apply multi_refl. 
    unfold norm. intro H.
    destruct H as [e He]. inversion He.
  - exists (var_f x). split. apply multi_refl.
    unfold norm. intro H. destruct H as [e He].
    inversion He.
  -  *)

    

(* 
Inductive step_count : exp -> exp -> nat -> Prop :=
  | sc_base : forall (e:exp),
    step_count e e 0
  | sc_ind : forall (e1 e2 e3:exp) (n:nat),
    step e1 e2 ->
    step_count e2 e3 n ->
    step_count e1 e3 (S n). *)

(*Inductive bounded_reduction : exp -> nat -> Prop :=
  | bound : forall (e1:exp) (v:nat),
    (forall (e2:exp) (n:nat), step_count e1 e2 n -> n <= v) ->
    bounded_reduction e1 v.

Inductive strong_norm : exp -> Prop :=
  | sn_bound : forall (e:exp),
    (exists (v:nat), bounded_reduction e v) ->
    strong_norm e. *)



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
  
  
  Theorem test : norm (app (var_b 1) (var_b 2)).
  Proof.
  unfold norm. unfold not. intros. destruct H.
    inversion H. inversion H4.
  Qed.
  
  (*Inductive norm: exp -> Prop :=
    | norm_b : forall (n : nat), norm (var_b n)
    | norm_f : forall (x : var), norm (var_f x)
    | norm_fabs : forall (x : var), norm (var_f x)
    | norm_f : forall (x : var), norm (var_f x) 
  Girard defines norm as not containing any (abs (app e1) e2) but the above definition is simpler. Decide later what to use*)
  
  (*
  Inductive step_count : exp -> nat -> Prop := (*count!*)
    | count_b : forall (e:exp), norm e -> step_count e 0
    | count_step : forall (e e2:exp) (n:nat), 
      step e e2 -> 
      step_count e2 (n - 1) -> 
      step_count e n.*)
  
  Lemma norm_b : forall (x:nat), norm (var_b x).
  Proof.
  intros. unfold norm. unfold not. intros. destruct H. 
  inversion H. Qed. 
  
  Lemma norm_v : forall (x:var), norm (var_f x).
  Proof.
  intros. unfold norm. unfold not. intros. destruct H. 
  inversion H. Qed. 
  
  (* Theorem test_step_count : forall (x : var), 
    step_count (app (abs (var_f x)) (var_f x)) 1.
  Proof.
  intros. eapply count_step. apply step_beta.
  apply lc_abs. intros.
    - simpl. unfold open_exp_wrt_exp. unfold open_exp_wrt_exp_rec. 
      auto.
    - auto.
    - simpl.  unfold open_exp_wrt_exp. unfold open_exp_wrt_exp_rec. 
      apply count_b.  apply norm_v.
  Qed. *)
  
  
  (* Definition strong_norm  (e : exp) : Prop :=
  exists n, step_count e n. *)
  Fixpoint reducible (T : typ) (e : exp) : Prop :=
    match T with
    | typ_base => strong_norm e
    | typ_arrow T1 T2 => (forall (e2: exp), 
      reducible T1 e2 -> 
      reducible T2  (app e e2))
  end.
  
  (* Inductive reduc : typ -> exp -> Prop :=
    | red_arrow : forall (G:ctx) (e:exp) (U V:typ),
      typing G e (typ_arrow U V) ->
      (forall (u:exp), 
        reduc U u -> reduc V (app e u)) ->
        reduc (typ_arrow U V) e*)
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
  (*app with built in beta reduce*)
  Fixpoint app_beta (e1 e2 : exp) : exp :=
    match e1 with
    | (abs e) => (open_exp_wrt_exp e e2)
    | _ => (app e1 e2)
  end.
  
  (*the mapping function that satisfies Z-property*)
  Fixpoint Z_map (e : exp) : exp :=
  match e with
    | var_b e1 => var_b e1
    | var_f e1 => var_f e1
    | abs e1 => abs (Z_map e1)
    | app e1 e2 => app_beta (Z_map e1) (Z_map e2)
  end.
  
  
  Theorem test_beta_eq : forall (e1 e2 : exp), lc_exp (Z_map e1) ->
       lc_exp (Z_map e2) -> multi step (app (Z_map e1) (Z_map e2)) (Z_map (app e1 e2)).
  Proof.
  intros. simpl. destruct (Z_map e1).
    - constructor.
    - simpl.  constructor.
    - simpl. apply multi_step with (y :=  app (abs e) (Z_map e2)). constructor; auto. constructor.
    - simpl. constructor.
  Qed.
  Proof.
  Theorem lc_step : forall (e1 e2 : exp), e1 ---> e2 -> lc_exp e1 -> lc_exp e2.
  intros.
  induction H; simpl.
  - apply lc_abs in H. 
  Qed.
  Theorem multi_abs : forall (e1 e2 : exp), lc_exp e1 -> lc_exp e2 -> e1 -->* e2 -> abs e1 -->* abs e2.
  Proof.
  intros. 
  induction H1. constructor. apply step_abs in H1.
  
  Qed.
  Theorem step_Z_map : forall (e : exp), e -->* (Z_map e).
  Proof. intros. induction e; simpl; try constructor.
    - apply step_abs.
  
  (* 
  Theorem church_rosser : confluence step.
  Proof.
  unfold confluence. *)
  
  (*
  Inductive reducible : typ -> exp -> Prop :=
    | red_arrow : forall (G:ctx) (e:exp) (U V:typ),
      typing G e (typ_arrow U V) ->
      (forall (u:exp), 
        strong_norm u -> reducible V (app e u)) ->
      reducible (typ_arrow U V) e
    | red_atom : forall (G:ctx) (e:exp),
      typing G e typ_base ->
      strong_norm e ->
      reducible typ_base e.*)
  
  
  Theorem all_types_inhabited: forall (G:ctx) (T:typ),
    exists (v:exp), typing G v T.
  Admitted.
  
  Inductive neutral : exp -> Prop :=
    | neutral_varf : forall (v:var),
      neutral (var_f v)
    | neutral_varb : forall (n:nat),
      neutral (var_b n)
    | neutral_app : forall (e1 e2:exp),
      neutral (app e1 e2).
  
  (* Fixpoint multistep : exp -> exp -> Prop :=
  | ms_base : forall (e:exp),
    multistep e e
  | ms_ind : forall (e1 e2 e3:exp),
    step e1 e2 ->
    multistep e2 e3 ->
    multistep e1 e3. *)
  
  Inductive multistep : exp -> exp -> Prop :=
    | ms_count : forall (t1 t2:exp),
      (exists (n:nat), step_count t1 t2 n) ->
      multistep t1 t2.
  
  Lemma step_count_sum : forall (n1 n2:nat) (e1 e2 e3:exp),
    step_count e1 e2 n1 ->
    step_count e2 e3 n2 ->
    step_count e1 e3 (n1 + n2).
  Proof.
    induction n1 as [|n1' IHn1]; intros.
    - inversion H; subst. auto.
    - inversion H; subst.
      assert (H43: step_count e4 e3 (n1' + n2)).
      { apply IHn1 with e2; auto. }
      apply sc_ind with e4; auto.
  Qed.
  
  Lemma plus_n_le : forall (n m k:nat),
    n + m <= k ->
    m <= k.
  Proof.
    intros. induction n; auto.
    apply IHn. simpl in H.
    apply le_trans with (S (n + m)); auto.
  Qed. 
      
  
  Theorem sn_red: forall (G:ctx) (T:typ) (e e':exp),
    (typing G e T ->
    reducible T e ->
    strong_norm e) /\
    (reducible T e' ->
    multistep e' e ->
    reducible T e) /\
    (neutral e -> 
    (forall (e2:exp),
      step e e2 -> reducible T e2) ->
    reducible T e).
  Proof.
    induction T.
    - split.
      intros Ht Hr. inversion Hr; subst; auto.
      split.
      + intros Hrb Hms. simpl in Hrb. simpl.
        inversion Hms; subst.
        destruct H as [n Hstep].
        inversion Hrb; subst.
        destruct H as [v' Hbre].
        apply sn_bound.
        exists v'.
        apply bound. 
        intros e2 n2 He2.
        inversion Hbre; subst.
        assert (He'2:step_count e' e2 (n + n2)).
        { apply step_count_sum with e; auto. }
        apply H in He'2.
        apply plus_n_le with n. auto.
      + intros Hn Hred.
        simpl. simpl in Hred.
        destruct e; inversion Hn; subst; auto.
        * apply sn_bound. exists 0.
          apply bound. intros e2 n2 H.
          induction n2; auto.
          inversion H.
          inversion H1.
        * apply sn_bound. exists 0.
          apply bound. intros. induction n; auto.
          inversion H. inversion H1.
        * induction e1.
            (* var_b *)
            apply sn_bound. exists 0. apply bound.
            intros. induction n0; auto.
            inversion H. inversion H1. inversion H9.
            (* var_f *)
            apply sn_bound. exists 0. apply bound.
            intros. induction n; auto.
            inversion H. inversion H1. inversion H9.
            (* abs *)
            assert (Hstep: step (app (abs e1) e2) (open_exp_wrt_exp  e1 e2 )).
            {
             apply step_beta. apply lc_abs.
             admit. 
            }
  Admitted.
           
  
  
  
          
    (*-  
      simpl in Hrt.
      apply sn_bound.
      assert (Hu:exists (u:exp), typing G u T1). 
      {
        apply all_types_inhabited.
      }
      destruct Hu as [u Hu].
      apply IHT1 in Hu.*)
  
  
  
      
  