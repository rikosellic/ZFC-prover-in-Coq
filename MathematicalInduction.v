Require Import FV.ZFLib.
Require Export FV.Tutorial.

(** Your tasks **)

(** Your target is to prove mathematical induction. Please write your own
    proof. **)

Lemma Nat_inductive_base_step:
  [[ ZF;;
    is_natural_number N;;
    ∅ ∈ X;;
    ∀ n, n ∈ N -> n ∈ X -> n ∪ {n} ∈ X
  |--
    ∅ ∈ X ∩ N ]].
Proof.
  pose proof Intersection_iff.
  universal instantiation H X N empty_set.
  The conclusion is already proved.
Qed.

Lemma Nat_inductive_inductive_step_X:
 [[ ZF;;
    is_natural_number N;;
    ∅ ∈ X;;
    ∀ n, n ∈ N -> n ∈ X ->n ∪ {n} ∈ X;;
    y  ∈  X ∩ N 
  |--
    y ∪ {y} ∈ X]].
Proof.
  pose proof Intersection_iff.
  universal instantiation H X N y.
  assert [[ ZF;; ∀ n, n ∈ N -> n∈X -> n ∪ {n} ∈ X
    |-- ∀ n, n ∈ N -> n ∈ X ->  n ∪ {n} ∈ X]] by Tauto.
  universal instantiation H1 y.
  The conclusion is already proved.
Qed.

Lemma Nat_inductive_inductive_step_N:
  [[ZF;;
    is_natural_number N;;
    ∅ ∈ X;;
    ∀ n, n ∈ N -> n∈ X -> n ∪ {n}∈ X;;
    y  ∈ X ∩ N 
  |--
    y ∪ {y} ∈ N]].
Proof.
  pose proof Intersection_iff.
  universal instantiation H X N y.
  assert [[ZF;; is_natural_number N |-- ∀ y, y ∈ N -> y ∪ {y} ∈ N]] by Tauto.
  universal instantiation H1 y.
  The conclusion is already proved.
Qed.

Lemma Nat_inductive_inductive_step:
  [[ZF;;
    is_natural_number N;;
    ∅ ∈ X;;
    ∀ n, n ∈ N -> n ∈ X ->n ∪ {n} ∈ X
     |-- y ∈ X ∩ N ->
   y ∪ {y}∈ X ∩ N]].
Proof.
  pose proof Intersection_iff.
  universal instantiation H X N [[y ∪ {y}]].
  pose proof Nat_inductive_inductive_step_X.
  pose proof Nat_inductive_inductive_step_N.
  The conclusion is already proved.
Qed.

Lemma Nat_intersection_inductive:
    [[ZF;;
    is_natural_number N;;
    ∅ ∈ X;;
    ∀ n, n ∈ N -> n ∈ X -> n ∪ {n}∈ X
  |-- is_inductive (X ∩ N)]].     
Proof.
  pose proof Nat_inductive_base_step.
  pose proof Nat_inductive_inductive_step.
  universal generalization H0 y.
  The conclusion is already proved.
Qed.

Theorem mathematical_induction:
  [[ZF;;
    is_natural_number N;;
    ∅ ∈ X;;
    ∀ n, n ∈ N -> n ∈ X -> n ∪ {n}∈ X
  |-- ∀ n, n ∈ N -> n ∈ X]].
Proof.
  pose proof Nat_intersection_inductive.
  
  assert ([[ZF;; is_natural_number N 
     |-- ∀ w, is_inductive w -> N ⊆ w]]) by Tauto.
     
  universal instantiation H0 [[X∩N]].
  
  assert ([[ZF;; is_natural_number N;; is_inductive X ∩ N 
    |-- N ⊆ X ∩ N]]) by Tauto.
    
  universal instantiation H2 n.
  
  pose proof Intersection_iff.
  
  universal instantiation H4 X N n.
  
  assert ([[ZF;; is_natural_number N;; ∅ ∈ X;; 
        ∀ n, n ∈ N -> n ∈ X -> n ∪ {n} ∈ X 
        |-- n ∈ N -> n ∈ X ]]) by Tauto.
  
  universal generalization H6 n.
  
  The conclusion is already proved.
Qed.

Lemma induction_intersect:
  [[ ZF |-- ∀ x, ∀ y, is_inductive(x) -> is_inductive(y) -> is_inductive(x ∩ y)]].
Proof.
  assert [[ ZF;; is_inductive(x) |-- ∅ ∈ x ]] by Tauto.
  assert [[ ZF;; is_inductive(y) |-- ∅ ∈ y ]] by Tauto.
  pose proof Intersection_iff.
  universal instantiation H1 x y [[∅]].
  assert [[ ZF;; is_inductive(x);; is_inductive(y) |-- ∅ ∈ x ∩ y ]] by Tauto.
  assert [[ ZF;; is_inductive(x) |-- ∀ n, n ∈ x -> n ∪ {n} ∈ x ]] by Tauto.
  assert [[ ZF;; is_inductive(y) |-- ∀ n, n ∈ y -> n ∪ {n} ∈ y ]] by Tauto.
  universal instantiation H4 n.
  universal instantiation H5 n.
  universal instantiation H1 x y n.
  universal instantiation H1 x y [[ n ∪ {n} ]].
  assert [[ ZF;; is_inductive(x);; is_inductive(y) |-- n ∈ x ∩ y -> n ∪ {n} ∈ x ∩ y ]] by Tauto.
  universal generalization H10 n.
  assert [[ ZF |-- is_inductive(x) -> is_inductive(y) -> is_inductive (x ∩ y) ]] by Tauto.
  universal generalization H12 x y.
  The conclusion is already proved.
Qed.