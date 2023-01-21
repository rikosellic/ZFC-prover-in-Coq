Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Strings.String.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Lists.List.
Import ListNotations.


Module Type NAME_SYSTEM.

Parameter t: Type.
Parameter eq_dec: forall v1 v2: t, {v1 = v2} + {v1 <> v2}.
Parameter max: t -> t -> t.
Parameter next_name: t -> t.
Parameter le: t -> t -> Prop.
Parameter le_trans: Transitive le.
Parameter default: t.

Axiom next_name_new: forall v v_max, le v v_max -> v <> next_name v_max.
Axiom le_max_r: forall v1 v2, le v1 (max v1 v2).
Axiom le_max_l: forall v1 v2, le v2 (max v1 v2).
Axiom max_sym: forall v1 v2, max v1 v2 = max v2 v1.
Axiom max_comm: forall v1 v2 v3, max v1 (max v2 v3) = max (max v1 v2) v3.

End NAME_SYSTEM.

Module NAME_SYSTEM_EXT (Name:NAME_SYSTEM).
Include Name.

(** Max name of a list **)
Fixpoint list_max (xs:list t):=
  match xs with
  | nil => default
  | (x::xs') => max x (list_max xs')
  end.  

(** Find a new name for a list **)
Definition list_new_name (xs:list t):= next_name (list_max xs).

Lemma list_max_correct: forall s xs,
  In s xs -> le s (list_max xs).
Proof.
  intros. induction xs. inversion H. simpl.  destruct H.
  + subst a. apply le_max_r.
  + assert (le (list_max xs) (max a (list_max xs))) by apply le_max_l. apply IHxs in H.
     pose proof le_trans. transitivity (list_max xs); tauto.
Qed.

Lemma list_new_name_new: forall s xs,
  In s xs -> s <> list_new_name xs.
Proof.
  intros. apply list_max_correct in H. apply next_name_new. tauto.
Qed.

Lemma list_max_Permuatation: forall l1 l2, 
  Permutation l1 l2 -> list_max l1 = list_max l2.
Proof.
  intros. induction H.
  + reflexivity.
  + simpl. congruence.
  + simpl. assert (max x (list_max l)=max (list_max l) x) by apply max_sym.
      rewrite H. rewrite max_comm. apply max_sym.
  + congruence.
Qed.

Corollary list_new_name_Permutation: forall l1 l2,
  Permutation l1 l2  -> list_new_name l1 = list_new_name l2.
Proof.
  intros. apply list_max_Permuatation in H. unfold list_new_name. congruence.
Qed.

Definition eqb (x y:t) :bool:=
  if eq_dec x y then true else false.
  
Lemma eqb_eq: forall v1 v2,
  eqb v1 v2 = true <-> v1=v2.
Proof. unfold eqb; split; intros; destruct (eq_dec v1 v2); easy. Qed.

Lemma eqb_neq: forall v1 v2,
  eqb v1 v2 = false <-> v1 <> v2.
Proof. unfold eqb; split; intros; destruct (eq_dec v1 v2); easy. Qed.

(** Key-value pairs**)
Fixpoint look_up {A: Type} (x: t) (KV: list (t * A)): option A :=
  match KV with
  | nil => None
  | (x0, v0) :: KV0 =>
      if eqb x0 x then Some v0 else look_up x KV0
  end.

Fixpoint remove {A: Type} (x: t) (KV: list (t * A)): list (t * A) :=
  match KV with
  | nil => nil
  | (x0, v0) :: KV0 =>
      if eqb x0 x
      then remove x KV0
      else (x0, v0) :: remove x KV0
  end.

End NAME_SYSTEM_EXT.



(** Instantiate NAME_SYSTEM with string **)
Module StringSystem <: NAME_SYSTEM.

Definition t := string.

Definition eq_dec: forall v1 v2: t, {v1 = v2} + {v1 <> v2} :=
  string_dec.

Definition max (v1 v2: t): t :=
  match String_as_OT.cmp v1 v2 with
  | Lt => v2
  | _ => v1
  end.

(** New name: add a suffix ' at the end **)
Definition next_name (v: t): t :=
  append v (String (Ascii.Ascii true true true false false true false false) EmptyString).

Definition le := fun t1 t2 => String_as_OT.lt t1 t2 \/ t1 = t2.

Instance le_trans: Transitive le.
Proof.  
  unfold Transitive. intros.
  destruct H; destruct H0; unfold le.
  + left. apply String_as_OT.lt_trans with y; tauto.
  + left. congruence.
  + left. congruence.
  + right. congruence.
Qed.

Lemma next_name_new: forall v v_max,
  le v v_max ->
  v <> next_name v_max.
Proof.
  unfold le, next_name.
  intros. 
  assert (String_as_OT.lt v_max  (append v_max (String (Ascii.Ascii true true true false false true false false) EmptyString))).
  { clear v H. apply String_as_OT.cmp_lt. induction v_max. 
     + reflexivity.
     + simpl. assert (a=a) by reflexivity. apply Ascii_as_OT.cmp_eq in H. rewrite H. tauto. }
  remember  (append v_max (String (Ascii.Ascii true true true false false true false false) EmptyString)) as z. destruct H.
  + assert (String_as_OT.lt v z). eapply String_as_OT.lt_trans. apply H. tauto.
      destruct (eq_dec v z);[|tauto]. apply String_as_OT.cmp_lt in H1. apply String_as_OT.cmp_eq in e. congruence. 
  + subst v_max.  destruct (eq_dec v z);[|tauto].  apply String_as_OT.cmp_lt in H0. apply String_as_OT.cmp_eq in e. congruence.
Qed. 

Local Lemma compare_helper_gt {a b : string} (G : String_as_OT.cmp a b = Gt):
   String_as_OT.lt b a.
Proof.
  rewrite String_as_OT.cmp_antisym in G.
  rewrite CompOpp_iff in G.
  now apply String_as_OT.cmp_lt.
Qed.

Local Lemma compare_helper_lt_gt {a b: string} (H:String_as_OT.cmp a b = Lt):
  String_as_OT.cmp b a = Gt.
Proof.
  rewrite String_as_OT.cmp_antisym in H.
  rewrite CompOpp_iff in H. tauto.
Qed.

Local Lemma compare_helper_gt_lt {a b: string} (H:String_as_OT.cmp a b = Gt):
  String_as_OT.cmp b a = Lt.
Proof.
  rewrite String_as_OT.cmp_antisym in H.
  rewrite CompOpp_iff in H. tauto.
Qed.

Lemma le_max_r: forall (v1 v2:t), le v1 (max v1 v2).
Proof.
  unfold le, max; intros. destruct (String_as_OT.cmp v1 v2) eqn:E;try tauto.
  left. apply String_as_OT.cmp_lt. tauto. 
Qed.

Lemma le_max_l: forall (v1 v2:t), le v2 (max v1 v2).
Proof.
  unfold le, max; intros. destruct (String_as_OT.cmp v1 v2) eqn:E.
  + right. apply String_as_OT.cmp_eq in E. congruence.
  + tauto.
  + apply compare_helper_gt in E. tauto.
Qed.

Lemma max_sym: forall v1 v2, max v1 v2 = max v2 v1.
Proof.
  intros. unfold max. destruct (String_as_OT.cmp v1 v2) eqn: E1; destruct (String_as_OT.cmp v2 v1) eqn: E2; try tauto .
  + apply String_as_OT.cmp_eq in E1. apply String_as_OT.cmp_eq in E2. congruence.
  + apply String_as_OT.cmp_eq. tauto.
  + apply compare_helper_lt_gt in E2. congruence.
  + apply String_as_OT.cmp_eq in E2. congruence.
  + apply compare_helper_gt_lt in E2. congruence.
Qed.

Lemma max_comm:  forall v1 v2 v3, max v1 (max v2 v3) = max (max v1 v2) v3.
Proof.
  intros. unfold max. destruct (String_as_OT.cmp v1 v2) eqn:E1; destruct (String_as_OT.cmp v2 v3) eqn:E2.
  + rewrite E1. rewrite String_as_OT.cmp_eq in E1. rewrite String_as_OT.cmp_eq in E2.
      subst v2. apply String_as_OT.cmp_eq in E2. rewrite E2. reflexivity.
  + rewrite String_as_OT.cmp_eq in E1. subst v2. rewrite E2. reflexivity.
  + rewrite String_as_OT.cmp_eq in E1. assert (E3:=E1). apply String_as_OT.cmp_eq in E3.
      rewrite E3. subst v2. rewrite E2. reflexivity.
  + rewrite E1. reflexivity.
  + rewrite String_as_OT.cmp_lt in E1. rewrite String_as_OT.cmp_lt in E2. 
      assert (String_as_OT.cmp v1 v3=Lt). apply String_as_OT.cmp_lt. eapply String_as_OT.lt_trans.
      apply E1. tauto. rewrite H. reflexivity.
  + rewrite E1. reflexivity.
  + rewrite String_as_OT.cmp_eq in E2. subst v3. rewrite E1. reflexivity.
  + reflexivity.
  + rewrite E1. assert (String_as_OT.cmp v1 v3=Gt). apply compare_helper_lt_gt. apply String_as_OT.cmp_lt.
      apply compare_helper_gt in E1. apply compare_helper_gt in E2. eapply String_as_OT.lt_trans. 
      apply E2. tauto. rewrite H. reflexivity.
Qed.
  
Definition default: t := "x"%string.

End StringSystem.

Module StringName:= NAME_SYSTEM_EXT StringSystem.