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
     lc_exp (abs e1) ->
     lc_exp e2 ->
     step (app  ( (abs e1) )  e2)  (open_exp_wrt_exp  e1 e2 ) 
 | step_app : forall (e1 e2 e1':exp),
     lc_exp e2 ->
     step e1 e1' ->
     step (app e1 e2) (app e1' e2).


(** infrastructure *)
Hint Constructors typing step lc_exp : core.

Inductive step_count : exp -> exp -> nat -> Prop :=
  | sc_base : forall (e:exp),
    step_count e e 0
  | sc_ind : forall (e1 e2 e3:exp) (n:nat),
    step e1 e2 ->
    step_count e2 e3 n ->
    step_count e1 e3 (S n).

Inductive bounded_reduction : exp -> nat -> Prop :=
  | bound : forall (e1:exp) (v:nat),
    (forall (e2:exp) (n:nat), step_count e1 e2 n -> n <= v) ->
    bounded_reduction e1 v.

Inductive strong_norm : exp -> Prop :=
  | sn_bound : forall (e:exp),
    (exists (v:nat), bounded_reduction e v) ->
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
  
  
Definition norm (e : exp) : Prop :=
  (~ exists e2, step e e2).

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

(* have we guaranteed that there is only one possible step? *)
(* Inductive step_count : exp -> nat -> Prop := (*count!*)
  | count_b : forall (e:exp), norm e -> step_count e 0
  | count_step : forall (e e2:exp) (n:nat), 
    step e e2 -> 
    step_count e2 (n - 1) -> 
    step_count e n. *)

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
      reduc (typ_arrow U V) e
  | red_atom : forall (G:ctx) (e:exp),
    typing G e typ_base ->
    strong_norm e ->
    reduc typ_base e. *)

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
            
          }
         



        
  - intros t Htt Hrt.
    simpl in Hrt.
    apply sn_bound.
    assert (Hu:exists (u:exp), typing G u T1). 
    {
      apply all_types_inhabited.
    }
    destruct Hu as [u Hu].
    apply IHT1 in Hu.



    