Require Import FV.ZFLib.
Require Import FV.MathematicalInduction.
Require Import FV.Peano.
Require Import FV.Peano_plus.

Lemma mult_unique:
  [[ZF;;is_natural_number N;;is_plus e N|--∀x,∀y,is_mult x e N/\is_mult y e N->x=y]].
Proof.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult x e N|--∀y,is_legal_mult y e N -> x⊆y]]by Tauto.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult y e N|--∀x,is_legal_mult x e N -> y⊆x]]by Tauto.
universal instantiation H y.
universal instantiation H0 x.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult x e N;;is_mult y e N|-- x ⊆ y /\ y ⊆ x ]] by Tauto.
pose proof subset_subset_equal.
universal instantiation H4 x y.
assert [[ZF;;is_natural_number N;;is_plus e N|--is_mult x e N/\is_mult y e N->x=y]] by Tauto.
universal generalization H6 x y.
The conclusion is already proved.
Qed.

Lemma in_mult_exists_zero:
  [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--∀x,x∈N->∃z,z∈N/\in_rel3 x ∅ z f]].
Proof.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--∀x,x∈N->in_rel3 x ∅ ∅ f]]by Tauto.
universal instantiation H x. clear H.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;x∈N|--∅∈N/\in_rel3 x ∅ ∅ f]]by Tauto.
pose proof equal_rev.
universal instantiation H1 z [[∅]]. clear H1.
apply PEq_sub [[∅]] z [[z∈N/\in_rel3 x ∅ z f]].
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;x∈N;;z=∅|--z∈N/\in_rel3 x ∅ z f]]by Tauto.
existential generalization H3 [[∃z,z∈N/\in_rel3 x ∅ z f]]. clear H3.
existential instantiation H4 [[∃x,x=∅]]. clear H4.
pose proof equal_zero_exists.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--x∈N->∃z,z∈N/\in_rel3 x ∅ z f]]by Tauto.
universal generalization H5 x. clear H0 H H2 H1 H3 H4 H5.
The conclusion is already proved.
Qed.

Lemma in_mult_exists_induction:
  [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--∀y,y∈N/\(∀x,x∈N->∃z,z∈N/\in_rel3 x y z f)->y∪{y}∈N/\(∀x,x∈N->∃z,z∈N/\in_rel3 x y∪{y} z f)]].
Proof.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--∀x,∀y,∀z,∀a,x∈N/\y∈N/\z∈N/\a∈N->in_rel3 x y z f->in_rel3 z x a e->in_rel3 x y∪{y} a f]]by Tauto.
universal instantiation H x y z a. clear H.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;x∈N/\y∈N/\z∈N/\in_rel3 x y z f;;a∈N/\in_rel3 z x a e|--a∈N/\in_rel3 x y∪{y} a f]]by Tauto. clear H0.
existential generalization H [[∃z,z∈N/\in_rel3 x y∪{y} z f]]. clear H.
pose proof in_plus_exists.
universal instantiation H z x. clear H.
existential instantiation H0 [[∃a,a∈N/\in_rel3 z x a e]]. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;x∈N/\y∈N;;z∈N/\in_rel3 x y z f|--∃z,z∈N/\in_rel3 x y∪{y} z f]]by Tauto. clear H1 H.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀x,x∈N->(∃z,z∈N/\in_rel3 x y z f)|--∀x,x∈N->∃z,z∈N/\in_rel3 x y z f]]by Tauto.
universal instantiation H x. clear H.
existential instantiation H0 [[∃z,z∈N/\in_rel3 x y z f]]. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀x,x∈N->(∃z,z∈N/\in_rel3 x y z f);;y∈N|--x∈N->(∃z,z∈N/\in_rel3 x y∪{y} z f)]]by Tauto. clear H1 H.
universal generalization H0 x. clear H0.
assert [[ZF;;is_natural_number N|--∀x,x∈N->x∪{x}∈N]]by Tauto.
universal instantiation H0 y. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--y∈N/\(∀x,x∈N->∃z,z∈N/\in_rel3 x y z f)->y∪{y}∈N/\(∀x,x∈N->∃z,z∈N/\in_rel3 x y∪{y} z f)]]by Tauto. clear H H1.
universal generalization H0 y.
The conclusion is already proved.
Qed.

Lemma in_mult_exists:
  [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--∀x,∀y,x∈N/\y∈N->∃z,z∈N/\in_rel3 x y z f]].
Proof.
pose proof mathematical_induction.
assert [[ZF;;is_natural_number N;; is_plus e N;;is_mult f e N;;∀y,y∈X<->y∈N/\(∀x,x∈N->∃z,z∈N/\in_rel3 x y z f)|--∀y,y∈X<->y∈N/\(∀x,x∈N->∃z,z∈N/\in_rel3 x y z f)]] by Tauto.
universal instantiation H0 [[∅]].
pose proof in_mult_exists_zero.
assert [[ZF;;is_natural_number N;; is_plus e N;;is_mult f e N;;∀y,y∈X<->y∈N/\(∀x,x∈N->∃z,z∈N/\in_rel3 x y z f)|--∅ ∈ X]] by Tauto. clear H1 H2.

pose proof in_mult_exists_induction.
universal instantiation H1 n. clear H1.
universal instantiation H0 n.
universal instantiation H0 y.
universal instantiation H0 [[n∪{n}]]. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀y,y∈X<->y∈N/\(∀x,x∈N->∃z,z∈N/\in_rel3 x y z f)|--
 n∈N -> n∈X->n∪{n}∈X]]by Tauto. clear H2 H1 H5.
universal generalization H0 n. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀y,y∈X<->y∈N/\(∀x,x∈N->∃z,z∈N/\in_rel3 x y z f)|--∀n,n∈N->n∈X]]by Tauto.
universal instantiation H0 y. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀y,y∈X<->y∈N/\(∀x,x∈N->∃z,z∈N/\in_rel3 x y z f)|--y∈N->(∀x,x∈N->∃z,z∈N/\in_rel3 x y z f)]]by Tauto.
existential instantiation H0 [[∃X,∀y,y∈ X <-> y∈N/\(∀x,x∈N->∃z,z∈N/\in_rel3 x y z f)]].
apply separation [[∃X,∀y,y∈X <-> y∈N/\(∀x,x∈N->∃z,z∈N/\in_rel3 x y z f)]].
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--y∈N->(∀x,x∈N->∃z,z∈N/\in_rel3 x y z f)]]by Tauto.
universal generalization H7 y. clear H H3 H4 H1 H2 H0 H5 H6 H7.

universal instantiation H8 y.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;y∈N|--∀x,x∈N->∃z,z∈N/\in_rel3 x y z f]]by Tauto.
universal instantiation H0 x.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--x∈N/\y∈N->∃z,z∈N/\in_rel3 x y z f]]by Tauto.
universal generalization H2 x y.
The conclusion is already proved.
Qed.

Lemma is_mult_inversion:
  [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--∀x,∀y,∀z,x∈N/\y∈N/\z∈N/\in_rel3 x y z f -> (y=∅/\z=∅)\/(∃u,∃v,∃w,u∈N/\v∈N/\w∈N/\in_rel3 u v w f/\x=u/\y=v∪{v}/\in_rel3 w u z e)]].
Proof.
apply separation [[∃h,∀x,x∈h<->x∈f/\¬x=d]].
assert [[ZF;;∀x,x∈h <-> x∈f /\ ¬x=d|--∀x,x∈h <-> x∈f /\ ¬x=d]]by Tauto.
universal instantiation H0 g.

assert [[ZF;;x∈N;;is_triple g x ∅ ∅;;is_natural_number N;;is_plus e N;;is_mult f e N|--∀ x,x∈N->in_rel3 x ∅ ∅ f]]by Tauto.
universal instantiation H2 x. clear H2.
assert [[ZF;;x∈N;;is_triple g x ∅ ∅;;is_natural_number N;;is_plus e N;;is_mult f e N|--∃u,is_triple u x ∅ ∅/\u∈f]]by Tauto. clear H3.
pose proof triple_injection.
universal instantiation H3 x [[∅]] [[∅]] u g. clear H3.
apply PEq_sub u g [[g∈f]].
assert [[ZF;;x∈N;;is_triple g x ∅ ∅;;is_natural_number N;;is_plus e N;;is_mult f e N;;is_triple u x ∅ ∅/\u∈f|--g∈f]]by Tauto. clear H4 H3.
existential instantiation H5 [[∃u,is_triple u x ∅ ∅/\u∈f]]. clear H5.
assert [[ZF;;x∈N;;is_triple g x ∅ ∅;;is_natural_number N;;is_plus e N;;is_mult f e N|--g∈f]]by Tauto. clear H2 H3.
apply PEq_sub g d [[is_triple d x ∅ ∅]].
pose proof triple_inversion.
universal instantiation H3 a b c x [[∅]] [[∅]] d. clear H3.
apply PEq_sub x c [[b=c]].
pose proof equal_rev.
universal instantiation H6 c x. clear H6.
assert [[ZF;;g=d;;is_triple g x ∅ ∅;;is_triple d a b c|--b=∅/\c=∅]] by Tauto. clear H2 H5 H3 H7.
assert [[ZF;;is_triple g x ∅ ∅;;is_triple d a b c;;¬(b=∅/\c=∅)|--¬g=d]]by Tauto. clear H6.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;a∈N/\b∈N/\c∈N;;is_triple d a b c/\d∈f;;¬(b=∅/\c=∅)/\¬(∃u,∃v,∃w,u∈N/\v∈N/\w∈N/\in_rel3 u v w f/\a=u/\b=v∪{v}/\in_rel3 w u c e);;∀x,x∈h <-> x∈f /\ ¬x=d;;x∈N;;is_triple g x ∅ ∅|--is_triple g x ∅ ∅ /\ g∈h]]by Tauto. clear H4 H2.
existential generalization H3 [[∃ g,is_triple g x ∅ ∅/\g∈h]]. clear H3.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;a∈N/\b∈N/\c∈N;;is_triple d a b c/\d∈f;;¬(b=∅/\c=∅)/\¬(∃u,∃v,∃w,u∈N/\v∈N/\w∈N/\in_rel3 u v w f/\a=u/\b=v∪{v}/\in_rel3 w u c e);;∀x,x∈h <-> x∈f /\ ¬x=d;;x∈N;;is_triple g x ∅ ∅|--in_rel3 x ∅ ∅ h]]by Tauto. clear H2.
existential instantiation H3 [[∃u, is_triple u x ∅ ∅]]. clear H3.
pose proof triple_exists.
universal instantiation H3 x [[∅]] [[∅]]. clear H3.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;a∈N/\b∈N/\c∈N;;is_triple d a b c/\d∈f;;¬(b=∅/\c=∅)/\¬(∃u,∃v,∃w,u∈N/\v∈N/\w∈N/\in_rel3 u v w f/\a=u/\b=v∪{v}/\in_rel3 w u c e);;∀x,x∈h <-> x∈f /\ ¬x=d|--x∈N->in_rel3 x ∅ ∅ h]]by Tauto. clear H2 H4.
universal generalization H3 x. clear H3.

assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀x,x∈h<->x∈f/\¬x=d;;u∈N/\v∈N/\w∈N;;in_rel3 u v w h|--∃g, is_triple g u v w /\ g ∈ h]]by Tauto.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀x,x∈h<->x∈f/\¬x=d;;u∈N/\v∈N/\w∈N;;is_triple g u v w /\ g ∈ h|--is_triple g u v w/\g∈f]]by Tauto.
existential generalization H4 [[∃g,is_triple g u v w/\g∈f]].
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀x,x∈h<->x∈f/\¬x=d;;u∈N/\v∈N/\w∈N;;is_triple g u v w /\ g ∈ h|--in_rel3 u v w f]]by Tauto. clear H4 H5.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--∀u,∀v,∀w,∀a,u∈N/\v∈N/\w∈N/\a∈N->(in_rel3 u v w f ->in_rel3 w u a e->in_rel3 u v∪{v} a f)]]by Tauto.
universal instantiation H4 u v w m. clear H4.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀x,x∈h<->x∈f/\¬x=d;;u∈N/\v∈N/\w∈N;;is_triple g u v w /\ g ∈ h|--m∈N/\in_rel3 w u m e -> in_rel3 u v∪{v} m f]]by Tauto. clear H6 H5.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀x,x∈h<->x∈f/\¬x=d;;u∈N/\v∈N/\w∈N;;is_triple g u v w /\ g ∈ h;;m∈N/\in_rel3 w u m e|--∃X, is_triple X u v∪{v} m /\ X∈f]]by Tauto. clear H4.
apply PEq_sub X d [[is_triple d u v∪{v} m]].
pose proof triple_inversion.
universal instantiation H6 a b c u [[v∪{v}]] m d. clear H6.
assert [[ZF;;X=d;;is_triple X u v∪{v} m;;is_triple d a b c|--a=u/\b=v∪{v}/\c=m]]by Tauto. clear H4 H7.
assert [[ZF;;∀x,x∈h<->x∈f/\¬x=d;;is_triple g u v w /\ g ∈ h|--is_triple g u v w/\g∈f]]by Tauto.
existential generalization H4 [[∃g,is_triple g u v w/\g∈f]]. clear H4.
assert [[ZF;;∀x,x∈h<->x∈f/\¬x=d;;is_triple g u v w /\ g ∈ h|--in_rel3 u v w f]]by Tauto. clear H7.
pose proof equal_rev.
universal instantiation H7 c m. clear H7.
apply PEq_sub m c [[in_rel3 w u c e]].
assert [[ZF;;X=d;;is_triple X u v∪{v} m;;is_triple d a b c;;in_rel3 w u m e|--a=u/\b=v∪{v}/\in_rel3 w u c e]]by Tauto. clear H6 H8 H7.
assert [[ZF;;∀x,x∈h<->x∈f/\¬x=d;;is_triple g u v w/\g∈h;;X=d;;is_triple X u v∪{v} m;;u∈N/\v∈N/\w∈N;;m∈N/\in_rel3 w u m e;;is_triple d a b c|--u∈N/\v∈N/\w∈N/\in_rel3 u v w f/\a=u/\b=v∪{v}/\in_rel3 w u c e]]by Tauto. clear H4 H9.
existential generalization H6 [[∃u,∃v,∃w,u∈N/\v∈N/\w∈N/\in_rel3 u v w f/\a=u/\b=v∪{v}/\in_rel3 w u c e]]. clear H6.
assert [[ZF;;∀x,x∈h<->x∈f/\¬x=d;;is_triple g u v w/\g∈h;;is_triple X u v∪{v} m;;u∈N/\v∈N/\w∈N;;m∈N/\in_rel3 w u m e;;is_triple d a b c;;¬(∃u,∃v,∃w,u∈N/\v∈N/\w∈N/\in_rel3 u v w f/\a=u/\b=v∪{v}/\in_rel3 w u c e)|--¬X=d]]by Tauto. clear H4.
universal instantiation H0 X.
assert [[ZF;;∀x,x∈h<->x∈f/\¬x=d;;is_triple g u v w/\g∈h;;is_triple X u v∪{v} m/\X∈f;;u∈N/\v∈N/\w∈N;;m∈N/\in_rel3 w u m e;;is_triple d a b c;;¬(∃u,∃v,∃w,u∈N/\v∈N/\w∈N/\in_rel3 u v w f/\a=u/\b=v∪{v}/\in_rel3 w u c e)|--is_triple X u v∪{v} m/\X∈h]]by Tauto. clear H6 H4.
existential generalization H7 [[∃X,is_triple X u v∪{v} m/\X∈h]]. clear H7.
assert [[ZF;;∀x,x∈h<->x∈f/\¬x=d;;is_triple g u v w/\g∈h;;is_triple X u v∪{v} m/\X∈f;;u∈N/\v∈N/\w∈N;;m∈N/\in_rel3 w u m e;;is_triple d a b c;;¬(∃u,∃v,∃w,u∈N/\v∈N/\w∈N/\in_rel3 u v w f/\a=u/\b=v∪{v}/\in_rel3 w u c e)|--in_rel3 u v∪{v} m h]]by Tauto. clear H4.
existential instantiation H6 [[∃X,is_triple X u v∪{v} m/\X∈f]]. clear H6.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀x,x∈h<->x∈f/\¬x=d;;u∈N/\v∈N/\w∈N;;m∈N/\in_rel3 w u m e;;is_triple g u v w/\g∈h;;is_triple d a b c;;¬(∃u,∃v,∃w,u∈N/\v∈N/\w∈N/\in_rel3 u v w f/\a=u/\b=v∪{v}/\in_rel3 w u c e)|--in_rel3 u v∪{v} m h]]by Tauto. clear H5 H4.
existential instantiation H6 [[∃g,is_triple g u v w/\g∈h]]. clear H6.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀x,x∈h<->x∈f/\¬x=d;;u∈N/\v∈N/\w∈N;;m∈N/\in_rel3 w u m e;;in_rel3 u v w h;;is_triple d a b c;;¬(∃u,∃v,∃w,u∈N/\v∈N/\w∈N/\in_rel3 u v w f/\a=u/\b=v∪{v}/\in_rel3 w u c e)|--in_rel3 u v∪{v} m h]]by Tauto. clear H3 H4.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀x,x∈h<->x∈f/\¬x=d;;is_triple d a b c;;¬(∃u,∃v,∃w,u∈N/\v∈N/\w∈N/\in_rel3 u v w f/\a=u/\b=v∪{v}/\in_rel3 w u c e)|--u∈N/\v∈N/\w∈N/\m∈N->in_rel3 u v w h->in_rel3 w u m e->in_rel3 u v∪{v} m h]]by Tauto. clear H5.
universal generalization H3 u v w m. clear H3.

assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;a∈N/\b∈N/\c∈N;;is_triple d a b c/\d∈f;;¬(b=∅/\c=∅)/\¬(∃u,∃v,∃w,u∈N/\v∈N/\w∈N/\in_rel3 u v w f/\a=u/\b=v∪{v}/\in_rel3 w u c e);;∀x,x∈h<->x∈f/\¬x=d|--is_legal_mult h e N]]by Tauto. clear H1 H2 H4.

assert [[ZF;;is_plus e N;;is_mult f e N|--∀x,is_legal_mult x e N -> f⊆x]]by Tauto.
universal instantiation H1 h. clear H1.
assert [[ZF;;is_plus e N;;is_mult f e N;;is_legal_mult h e N|--∀z,z∈f->z∈h]]by Tauto. clear H2.
universal instantiation H1 d. clear H1.
universal instantiation H0 d.
apply PEq_refl d.
assert [[ZF;;∀x,x∈h<->x∈f/\¬x=d|--¬d∈h]]by Tauto. clear H1 H4.
assert [[ZF;;is_plus e N;;is_mult f e N;;is_legal_mult h e N;;∀x,x∈h<->x∈f/\¬x=d|--¬d∈f]]by Tauto. clear H2 H5.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;a∈N/\b∈N/\c∈N;;is_triple d a b c/\d∈f;;∀x,x∈h<->x∈f/\¬x=d|--(b=∅/\c=∅)\/(∃u,∃v,∃w,u∈N/\v∈N/\w∈N/\in_rel3 u v w f/\a=u/\b=v∪{v}/\in_rel3 w u c e)]]by Tauto. clear H0 H3 H1.
existential instantiation H2 [[∃h,∀ x, x ∈ h <-> x ∈ f /\ ¬ x = d]].
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;a∈N/\b∈N/\c∈N;;is_triple d a b c/\d∈f|--(b=∅/\c=∅)\/(∃u,∃v,∃w,u∈N/\v∈N/\w∈N/\in_rel3 u v w f/\a=u/\b=v∪{v}/\in_rel3 w u c e)]]by Tauto. clear H H2 H0.
existential instantiation H1 [[∃u,is_triple u a b c /\ u ∈ f]].
assert [[ZF;;in_rel3 a b c f|--∃u,is_triple u a b c /\ u ∈ f]]by Tauto.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--a∈N/\b∈N/\c∈N/\in_rel3 a b c f->(b=∅/\c=∅)\/(∃u,∃v,∃w,u∈N/\v∈N/\w∈N/\in_rel3 u v w f/\a=u/\b=v∪{v}/\in_rel3 w u c e)]]by Tauto.
universal generalization H2 a b c.
The conclusion is already proved.
Qed.

Lemma mult_func_zero:
  [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--∀x,∀z,x∈N/\z∈N/\in_rel3 x ∅ z f->z=∅]].
Proof.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀m,m∈h<->m∈f/\(∀x,∀z,x∈N/\z∈N/\is_triple m x ∅ z->z=∅)|--∀m,m∈h<->m∈f/\(∀x,∀z,x∈N/\z∈N/\is_triple m x ∅ z->z=∅)]] by Tauto.
universal instantiation H m. clear H.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--∀n,n∈N->in_rel3 n ∅ ∅ f]] by Tauto.
universal instantiation H n. clear H.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;n∈N|--∃u, is_triple u n ∅ ∅ /\ u ∈ f]] by Tauto.
clear H1.
pose proof triple_injection.
universal instantiation H1 n [[∅]] [[∅]] u m. clear H1.
apply PEq_sub u m [[m ∈ f]].
assert [[ZF;;is_triple u n ∅ ∅ /\ u ∈ f;;is_triple m n ∅ ∅|--m∈f]]by Tauto. clear H2 H1.
existential instantiation H3 [[∃ u, is_triple u n ∅ ∅ /\ u ∈ f]]. clear H3.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--n∈N/\is_triple m n ∅ ∅->m∈f]] by Tauto. clear H H1.

pose proof triple_inversion.
universal instantiation H x [[∅]] z n [[∅]] [[∅]] m. clear H.
assert [[ZF;;is_triple m n ∅ ∅|--x∈N/\z∈N/\is_triple m x ∅ z -> z = ∅]] by Tauto.
universal generalization H x z. clear H1 H.

assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀m,m∈h<->m∈f/\(∀x,∀z,x∈N/\z∈N/\is_triple m x ∅ z->z=∅);;n∈N;;is_triple m n ∅ ∅|--is_triple m n ∅ ∅/\m∈h]] by Tauto.
existential generalization H [[∃ m, is_triple m n ∅ ∅ /\ m ∈ h]]. clear H.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀m,m∈h<->m∈f/\(∀x,∀z,x∈N/\z∈N/\is_triple m x ∅ z->z=∅);;n∈N;;is_triple m n ∅ ∅|--in_rel3 n ∅ ∅ h]] by Tauto.
existential instantiation H [[∃ u, is_triple u n ∅ ∅]]. clear H.
pose proof triple_exists.
universal instantiation H n [[∅]] [[∅]]. clear H.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀m,m∈h<->m∈f/\(∀x,∀z,x∈N/\z∈N/\is_triple m x ∅ z->z=∅)|--n∈N -> in_rel3 n ∅ ∅ h]] by Tauto.
universal generalization H n. clear H2 H3 H1 H4 H5 H.

assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--∀a,∀b,∀c,∀d,a∈N/\b∈N/\c∈N/\d∈N->in_rel3 a b c f -> in_rel3 c a d e->in_rel3 a b∪{b} d f]] by Tauto.
universal instantiation H a b c d. clear H.
assert [[ZF;;is_triple m a b c/\m∈h;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀m,m∈h<->m∈f/\(∀x,∀z,x∈N/\z∈N/\is_triple m x ∅ z->z=∅)|--is_triple m a b c/\m∈f]] by Tauto.
existential generalization H [[∃v, is_triple v a b c/\v∈f]]. clear H.
assert [[ZF;;is_triple m a b c/\m∈h;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀m,m∈h<->m∈f/\(∀x,∀z,x∈N/\z∈N/\is_triple m x ∅ z->z=∅);;a∈N/\b∈N/\c∈N;;d∈N/\in_rel3 c a d e|--∃v, is_triple v a b∪{b} d /\ v ∈ f]]by Tauto. clear H1 H2.

assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀m,m∈h<->m∈f/\(∀x,∀z,x∈N/\z∈N/\is_triple m x ∅ z->z=∅)|--∀m,m∈h<->m∈f/\(∀x,∀z,x∈N/\z∈N/\is_triple m x ∅ z->z=∅)]] by Tauto.
universal instantiation H1 v. clear H1.
pose proof not_empty.
universal instantiation H1 b. clear H1.
pose proof triple_inversion.
universal instantiation H1 a [[b∪{b}]] d x [[∅]] z v. clear H1.
assert [[ZF;;is_triple v a b∪{b} d|--x∈N/\z∈N/\is_triple v x ∅ z -> z=∅]]by Tauto. clear H3 H4.
universal generalization H1 x z. clear H1.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀m,m∈h<->m∈f/\(∀x,∀z,x∈N/\z∈N/\is_triple m x ∅ z->z=∅);;is_triple v a b∪{b} d/\v∈f|--is_triple v a b∪{b} d/\v∈h]]by Tauto. clear H3.
existential generalization H1 [[∃v, is_triple v a b∪{b} d/\v∈h]]. clear H1.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀m,m∈h<->m∈f/\(∀x,∀z,x∈N/\z∈N/\is_triple m x ∅ z->z=∅);;is_triple v a b∪{b} d/\v∈f|--in_rel3 a b∪{b} d h]]by Tauto. clear H2 H3.
existential instantiation H1 [[∃v, is_triple v a b∪{b} d/\v∈f]]. clear H1.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀m,m∈h<->m∈f/\(∀x,∀z,x∈N/\z∈N/\is_triple m x ∅ z->z=∅);;is_triple m a b c/\m∈h|--a∈N/\b∈N/\c∈N/\d∈N->in_rel3 c a d e->in_rel3 a b∪{b} d h]]by Tauto. clear H H2.
existential instantiation H1 [[∃m, is_triple m a b c/\m∈h]]. clear H1.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀m,m∈h<->m∈f/\(∀x,∀z,x∈N/\z∈N/\is_triple m x ∅ z->z=∅)|--a∈N/\b∈N/\c∈N/\d∈N->in_rel3 a b c h->in_rel3 c a d e->in_rel3 a b∪{b} d h]]by Tauto. clear H.
universal generalization H1 a b c d. clear H1.

assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀m,m∈h<->m∈f/\(∀x,∀z,x∈N/\z∈N/\is_triple m x ∅ z->z=∅)|--is_legal_mult h e N]]by Tauto. clear H0 H6 H.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--∀y,is_legal_mult y e N->f⊆y]]by Tauto.
universal instantiation H h. clear H.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀m,m∈h<->m∈f/\(∀x,∀z,x∈N/\z∈N/\is_triple m x ∅ z->z=∅)|--f⊆h]] by Tauto. clear H1 H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀m,m∈h<->m∈f/\(∀x,∀z,x∈N/\z∈N/\is_triple m x ∅ z->z=∅)|--∀m,m∈h<->m∈f/\(∀x,∀z,x∈N/\z∈N/\is_triple m x ∅ z->z=∅)]]by Tauto.
universal instantiation H0 m. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀m,m∈h<->m∈f/\(∀x,∀z,x∈N/\z∈N/\is_triple m x ∅ z->z=∅)|--∀m,m∈f->m∈h]]by Tauto.
universal instantiation H0 m. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀m,m∈h<->m∈f/\(∀x,∀z,x∈N/\z∈N/\is_triple m x ∅ z->z=∅);;m∈f|--(∀x,∀z,x∈N/\z∈N/\is_triple m x ∅ z->z=∅)]]by Tauto. clear H H1 H2.
universal instantiation H0 x z. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀m,m∈h<->m∈f/\(∀x,∀z,x∈N/\z∈N/\is_triple m x ∅ z->z=∅);;x∈N/\z∈N;;is_triple m x ∅ z/\m∈f|--z=∅]]by Tauto. clear H.
existential instantiation H0 [[∃m,is_triple m x ∅ z/\m∈f]]. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀m,m∈h<->m∈f/\(∀x,∀z,x∈N/\z∈N/\is_triple m x ∅ z->z=∅)|--x∈N/\z∈N/\in_rel3 x ∅ z f->z=∅]]by Tauto. clear H.
universal generalization H0 x z. clear H0.
existential instantiation H [[∃h,∀m,m∈h<->m∈f/\(∀x,∀z,x∈N/\z∈N/\is_triple m x ∅ z->z=∅)]]. clear H.
apply separation [[∃h,∀m,m∈h<->m∈f/\(∀x,∀z,x∈N/\z∈N/\is_triple m x ∅ z->z=∅)]].
The conclusion is already proved. 
Qed.

Lemma mult_func_zero_alter:
  [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--∅∈N/\(∀x,∀z,∀a,x∈N/\z∈N/\a∈N/\in_rel3 x ∅ z f/\in_rel3 x ∅ a f->z=a)]].
Proof.
pose proof mult_func_zero.
universal instantiation H x z.
universal instantiation H x a. clear H.
pose proof equal_rev.
universal instantiation H a [[∅]]. clear H.
apply PEq_sub [[∅]] a [[z=a]].
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--x∈N/\z∈N/\a∈N/\in_rel3 x ∅ z f/\in_rel3 x ∅ a f->z=a]]by Tauto.
universal generalization H3 x z a.
The conclusion is already proved. 
Qed.

Lemma mult_func_induction:
  [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--∀y,y∈N/\(∀x,∀z,∀a,x∈N/\z∈N/\a∈N/\in_rel3 x y z f/\in_rel3 x y a f->z=a)->y∪{y}∈N/\(∀x,∀z,∀a,x∈N/\z∈N/\a∈N/\in_rel3 x y∪{y} z f/\in_rel3 x y∪{y} a f->z=a)]].
Proof.
pose proof is_mult_inversion.
universal instantiation H x [[y∪{y}]] z.
universal instantiation H x [[y∪{y}]] a.
assert [[ZF;;is_natural_number N|--∀x,x∈N->x∪{x}∈N]]by Tauto.
universal instantiation H2 y. clear H2.
pose proof not_empty.
universal instantiation H2 y. clear H2.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;x∈N/\y∈N/\z∈N/\a∈N;;in_rel3 x y∪{y} z f;;in_rel3 x y∪{y} a f|--(∃ u, ∃ v, ∃ w, u∈N/\v∈N/\w∈N/\in_rel3 u v w f /\ x = u /\ y∪{y} = v∪{v} /\ in_rel3 w u z e)/\(∃ u, ∃ v, ∃ w, u∈N/\v∈N/\w∈N/\in_rel3 u v w f /\ x = u /\ y∪{y} = v∪{v} /\ in_rel3 w u a e)]]by Tauto. clear H H0 H1 H4.

pose proof Sn_inversion.
universal instantiation H y v. clear H.
pose proof equal_rev.
universal instantiation H x u.
universal instantiation H y v. clear H.
apply PEq_sub v y [[in_rel3 u y w f]].
apply PEq_sub u x [[in_rel3 x y w f]].
apply PEq_sub u x [[in_rel3 w x z e]].
assert [[ZF;;in_rel3 u v w f /\ x = u /\ y∪{y} = v∪{v} /\ in_rel3 w u z e|--in_rel3 x y w f/\in_rel3 w x z e]]by Tauto. clear H0 H1 H4 H H5 H6.

pose proof Sn_inversion.
universal instantiation H y c. clear H.
pose proof equal_rev.
universal instantiation H x b.
universal instantiation H y c. clear H.
apply PEq_sub c y [[in_rel3 b y d f]].
apply PEq_sub b x [[in_rel3 x y d f]].
apply PEq_sub b x [[in_rel3 d x a e]].
assert [[ZF;;in_rel3 b c d f /\ x = b /\ y∪{y} = c∪{c} /\ in_rel3 d b a e|--in_rel3 x y d f/\in_rel3 d x a e]]by Tauto. clear H0 H1 H4 H H5 H6.

assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀ x,∀ z,∀ a, x ∈ N /\ z ∈ N /\ a ∈ N /\ in_rel3 x y z f /\ in_rel3 x y a f -> z = a|--∀ x,∀ z,∀ a, x ∈ N /\ z ∈ N /\ a ∈ N /\ in_rel3 x y z f /\ in_rel3 x y a f -> z = a]]by Tauto.
universal instantiation H x w d. clear H.

apply PEq_sub w d [[in_rel3 d x z e]].
pose proof plus_func.
universal instantiation H1 d x z a. clear H1.

assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀x,∀z,∀a,x∈N/\z∈N/\a∈N/\in_rel3 x y z f/\in_rel3 x y a f->z=a;;x∈N/\y∈N/\z∈N/\a∈N;;u∈N/\v∈N/\w∈N/\in_rel3 u v w f/\x=u/\y∪{y}=v∪{v}/\in_rel3 w u z e;;b∈N/\c∈N/\d∈N/\in_rel3 b c d f/\x=b/\y∪{y}=c∪{c}/\in_rel3 d b a e|--z=a]]by Tauto. clear H7 H8 H0 H H4.
existential instantiation H1 [[∃u,∃v,∃w,u∈N/\v∈N/\w∈N/\in_rel3 u v w f/\x=u/\y∪{y}=v∪{v}/\in_rel3 w u a e]]. clear H1.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀x,∀z,∀a,x∈N/\z∈N/\a∈N/\in_rel3 x y z f/\in_rel3 x y a f->z=a;;x∈N/\y∈N/\z∈N/\a∈N;;u∈N/\v∈N/\w∈N/\in_rel3 u v w f/\x=u/\y∪{y}=v∪{v}/\in_rel3 w u z e|--(∃u,∃v,∃w,u∈N/\v∈N/\w∈N/\in_rel3 u v w f/\x=u/\y∪{y}=v∪{v}/\in_rel3 w u a e)->z=a]]by Tauto. clear H.
existential instantiation H0 [[∃u,∃v,∃w,u∈N/\v∈N/\w∈N/\in_rel3 u v w f/\x=u/\y∪{y}=v∪{v}/\in_rel3 w u z e]]. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀x,∀z,∀a,x∈N/\z∈N/\a∈N/\in_rel3 x y z f/\in_rel3 x y a f->z=a;;y∈N|--x∈N/\z∈N/\a∈N/\in_rel3 x y∪{y} z f/\in_rel3 x y∪{y} a f->z=a]]by Tauto. clear H2 H.
universal generalization H0 x z a. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--y∈N/\(∀x,∀z,∀a,x∈N/\z∈N/\a∈N/\in_rel3 x y z f/\in_rel3 x y a f->z=a)->y∪{y}∈N/\(∀x,∀z,∀a,x∈N/\z∈N/\a∈N/\in_rel3 x y∪{y} z f/\in_rel3 x y∪{y} a f->z=a)]]by Tauto.
universal generalization H0 y.
The conclusion is already proved.
Qed.

Lemma mult_func:
  [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--∀x,∀y,∀z,∀a,x∈N/\y∈N/\z∈N/\a∈N/\in_rel3 x y z f/\in_rel3 x y a f->z=a]].
Proof.
pose proof mathematical_induction.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀y,y∈X<->y∈N/\(∀x,∀z,∀a,x∈N/\z∈N/\a∈N/\in_rel3 x y z f/\in_rel3 x y a f->z=a)|--∀y,y∈X<->y∈N/\(∀x,∀z,∀a,x∈N/\z∈N/\a∈N/\in_rel3 x y z f/\in_rel3 x y a f->z=a)]] by Tauto.
universal instantiation H0 [[∅]].
pose proof mult_func_zero_alter.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀y,y∈X<->y∈N/\(∀x,∀z,∀a,x∈N/\z∈N/\a∈N/\in_rel3 x y z f/\in_rel3 x y a f->z=a)|--∅∈X]] by Tauto. clear H1 H2.

pose proof mult_func_induction.
universal instantiation H1 n. clear H1.
universal instantiation H0 n.
universal instantiation H0 y.
universal instantiation H0 [[n∪{n}]]. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀y,y∈X<->y∈N/\(∀x,∀z,∀a,x∈N/\z∈N/\a∈N/\in_rel3 x y z f/\in_rel3 x y a f->z=a)|-- n∈ N -> n∈X->n∪{n}∈X]] by Tauto. clear H2 H1 H5.
universal generalization H0 n. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀y,y∈X<->y∈N/\(∀x,∀z,∀a,x∈N/\z∈N/\a∈N/\in_rel3 x y z f/\in_rel3 x y a f->z=a)|--∀n,n∈N->n∈X]]by Tauto.
universal instantiation H0 y. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀y,y∈X<->y∈N/\(∀x,∀z,∀a,x∈N/\z∈N/\a∈N/\in_rel3 x y z f/\in_rel3 x y a f->z=a)|--y∈N->(∀x,∀z,∀a,x∈N/\z∈N/\a∈N/\in_rel3 x y z f/\in_rel3 x y a f->z=a)]]by Tauto.
existential instantiation H0 [[∃X,∀y,y∈X<->y∈N/\(∀x,∀z,∀a,x∈N/\z∈N/\a∈N/\in_rel3 x y z f/\in_rel3 x y a f->z=a)]].
apply separation [[∃X,∀y,y∈X<->y∈N/\(∀x,∀z,∀a,x∈N/\z∈N/\a∈N/\in_rel3 x y z f/\in_rel3 x y a f->z=a)]].
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--y∈N->(∀x,∀z,∀a,x∈N/\z∈N/\a∈N/\in_rel3 x y z f/\in_rel3 x y a f->z=a)]]by Tauto.
universal generalization H7 y. clear H H3 H4 H1 H2 H0 H5 H6 H7.

universal instantiation H8 y.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;y∈N|--∀x,∀z,∀a,x∈N/\z∈N/\a∈N/\in_rel3 x y z f/\in_rel3 x y a f->z=a]]by Tauto.
universal instantiation H0 x z a.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--x∈N/\y∈N/\z∈N/\a∈N/\in_rel3 x y z f/\in_rel3 x y a f->z=a]]by Tauto.
universal generalization H2 x y z a.
The conclusion is already proved.
Qed.

Lemma mult_dist_zero:
  [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--∀x,∀z,∀a,∀b,∀c,∀d,x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 ∅ z d e/\in_rel3 x ∅ a f/\in_rel3 x z b f/\in_rel3 x d c f->in_rel3 a b c e]].
Proof.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--∀x,x∈N->in_rel3 x ∅ ∅ f]]by Tauto.
universal instantiation H x. clear H.
pose proof mult_func.
universal instantiation H x [[∅]] [[∅]] a. clear H.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--x∈N/\a∈N/\in_rel3 x ∅ a f->∅=a]]by Tauto. clear H0 H1.
pose proof plus_func_zero.
universal instantiation H0 z d. clear H0.
pose proof mult_func.
universal instantiation H0 x d b c. clear H0.
apply PEq_sub z d [[in_rel3 x d b f]].
assert [[ZF;;is_natural_number N;;is_plus e N|--∀x,x∈N->in_rel3 ∅ x x e]]by Tauto.
universal instantiation H3 b. clear H3.
apply PEq_sub b c [[in_rel3 ∅ b c e]].
apply PEq_sub [[∅]] a [[in_rel3 a b c e]].
assert [[ZF;;is_natural_number N;;is_plus e N;;in_rel3 x d b f;;b∈N;;b=c;;∅=a|--in_rel3 a b c e]]by Tauto. clear H4 H3 H5.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 ∅ z d e/\in_rel3 x ∅ a f/\in_rel3 x z b f/\in_rel3 x d c f->in_rel3 a b c e]]by Tauto.
universal generalization H3 x z a b c d.
The conclusion is already proved.
Qed.

Lemma mult_dist_induction:
  [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--∀y,y∈N/\(∀x,∀z,∀a,∀b,∀c,∀d,x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 y z d e/\in_rel3 x y a f/\in_rel3 x z b f/\in_rel3 x d c f->in_rel3 a b c e)->y∪{y}∈N/\(∀x,∀z,∀a,∀b,∀c,∀d,x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 y∪{y} z d e/\in_rel3 x y∪{y} a f/\in_rel3 x z b f/\in_rel3 x d c f->in_rel3 a b c e)]].
Proof.
assert [[ZF;;∀x,∀z,∀a,∀b,∀c,∀d,x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 y z d e/\in_rel3 x y a f/\in_rel3 x z b f/\in_rel3 x d c f->in_rel3 a b c e|--∀x,∀z,∀a,∀b,∀c,∀d,x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 y z d e/\in_rel3 x y a f/\in_rel3 x z b f/\in_rel3 x d c f->in_rel3 a b c e]]by Tauto.
universal instantiation H x z q b n w. clear H.
pose proof plus_same.
universal instantiation H q b n x a c.
assert [[ZF;;is_natural_number N;;is_plus e N;;∀x,∀z,∀a,∀b,∀c,∀d,x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 y z d e/\in_rel3 x y a f/\in_rel3 x z b f/\in_rel3 x d c f->in_rel3 a b c e|--x∈N/\z∈N/\q∈N/\a∈N/\b∈N/\c∈N/\n∈N/\w∈N/\in_rel3 y z w e/\in_rel3 x y q f/\in_rel3 x z b f/\in_rel3 x w n f/\in_rel3 q x a e/\in_rel3 n x c e->in_rel3 a b c e]]by Tauto. clear H H0 H1.
assert [[ZF;;is_natural_number N|--∀x,x∈N->x∪{x}∈N]]by Tauto.
universal instantiation H y. clear H.
pose proof not_empty.
universal instantiation H y.
universal instantiation H w. clear H.
pose proof Sn_inversion.
universal instantiation H y u.
universal instantiation H y p.
universal instantiation H m w. clear H.
pose proof equal_rev.
universal instantiation H y u.
universal instantiation H z v.
universal instantiation H d [[w∪{w}]].
universal instantiation H x g.
universal instantiation H d [[m∪{m}]].
universal instantiation H x h.
universal instantiation H y p. clear H.
assert [[ZF;;y∪{y}=u∪{u}|--u=y]]by Tauto.
assert [[ZF;;y∪{y}=p∪{p}|--p=y]]by Tauto. clear H4 H5 H7 H13.
apply PEq_sub u y [[in_rel3 y v w e]].
apply PEq_sub v z [[in_rel3 y z w e]].
assert [[ZF;;in_rel3 u v w e/\y∪{y}=u∪{u}/\z=v|--in_rel3 y z w e]]by Tauto. clear H8 H H4 H5.
apply PEq_sub g x [[in_rel3 x m n f]].
apply PEq_sub g x [[in_rel3 n x c e]].
assert [[ZF;;in_rel3 g m n f/\x=g/\in_rel3 n g c e|--in_rel3 x m n f/\in_rel3 n x c e]]by Tauto. clear H10 H H4.
apply PEq_sub h x [[in_rel3 x p q f]].
apply PEq_sub p y [[in_rel3 x y q f]].
apply PEq_sub h x [[in_rel3 q x a e]].
assert [[ZF;;in_rel3 h p q f/\x=h/\y∪{y}=p∪{p}/\in_rel3 q h a e|--in_rel3 x y q f/\in_rel3 q x a e]]by Tauto. clear H12 H14 H H4 H8.
apply PEq_sub d [[w∪{w}]] [[m∪{m}=w∪{w}]].
apply PEq_sub m w [[in_rel3 x w n f]].
assert [[ZF;;d=w∪{w};;d=m∪{m};;in_rel3 x m n f|--in_rel3 x w n f]]by Tauto. clear H6 H9 H11 H H4.
assert [[ZF;;is_natural_number N;;is_plus e N;;∀x,∀z,∀a,∀b,∀c,∀d,x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 y z d e/\in_rel3 x y a f/\in_rel3 x z b f/\in_rel3 x d c f->in_rel3 a b c e;;x∈N/\z∈N/\q∈N/\a∈N/\b∈N/\c∈N/\n∈N/\w∈N;;in_rel3 u v w e/\y∪{y}=u∪{u}/\z=v;;in_rel3 h p q f/\x=h/\y∪{y}=p∪{p}/\in_rel3 q h a e;;in_rel3 x z b f;;in_rel3 g m n f/\x=g/\in_rel3 n g c e;;d=w∪{w};;d=m∪{m}|--in_rel3 a b c e]]by Tauto. clear H7 H5 H10 H8.
assert [[ZF;;is_natural_number N;;is_plus e N;;∀x,∀z,∀a,∀b,∀c,∀d,x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 y z d e/\in_rel3 x y a f/\in_rel3 x z b f/\in_rel3 x d c f->in_rel3 a b c e;;x∈N/\z∈N/\a∈N/\b∈N/\c∈N;;in_rel3 x z b f;;u∈N/\v∈N/\w∈N/\in_rel3 u v w e/\y∪{y}=u∪{u}/\z=v/\d=w∪{w};;h∈N/\p∈N/\q∈N/\in_rel3 h p q f/\x=h/\y∪{y}=p∪{p}/\in_rel3 q h a e;;g∈N/\m∈N/\n∈N/\in_rel3 g m n f/\x=g/\d=m∪{m}/\in_rel3 n g c e|--in_rel3 a b c e]]by Tauto. clear H.
pose proof equal_rev.
universal instantiation H d [[w∪{w}]]. clear H.
apply PEq_sub [[w∪{w}]] d [[¬d=∅]].
assert [[ZF;;d=w∪{w}|--¬d=∅]]by Tauto. clear H3 H5 H.
pose proof is_mult_inversion.
universal instantiation H x d c.
existential instantiation H4 [[∃u,∃v,∃w,u∈N/\v∈N/\w∈N/\in_rel3 u v w f/\x=u/\d=v∪{v}/\in_rel3 w u c e]]. clear H2 H4.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀x,∀z,∀a,∀b,∀c,∀d,x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 y z d e/\in_rel3 x y a f/\in_rel3 x z b f/\in_rel3 x d c f->in_rel3 a b c e;;x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N;;in_rel3 x z b f/\in_rel3 x d c f;;u∈N/\v∈N/\w∈N/\in_rel3 u v w e/\y∪{y}=u∪{u}/\z=v/\d=w∪{w};;h∈N/\p∈N/\q∈N/\in_rel3 h p q f/\x=h/\y∪{y}=p∪{p}/\in_rel3 q h a e|--in_rel3 a b c e]]by Tauto. clear H6 H3 H5.
universal instantiation H x [[y∪{y}]] a. clear H.
existential instantiation H2 [[∃u,∃v,∃w,u∈N/\v∈N/\w∈N/\in_rel3 u v w f/\x=u/\y∪{y}=v∪{v}/\in_rel3 w u a e]]. clear H2.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀x,∀z,∀a,∀b,∀c,∀d,x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 y z d e/\in_rel3 x y a f/\in_rel3 x z b f/\in_rel3 x d c f->in_rel3 a b c e;;x∈N/\y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N;;in_rel3 x y ∪ {y} a f/\in_rel3 x z b f/\in_rel3 x d c f;;u∈N/\v∈N/\w∈N/\in_rel3 u v w e/\y∪{y}=u∪{u}/\z=v/\d=w∪{w}|--in_rel3 a b c e]]by Tauto. clear H3 H.
pose proof is_plus_inversion.
universal instantiation H [[y∪{y}]] z d. clear H.
existential instantiation H2 [[∃u,∃v,∃w,u∈N/\v∈N/\w∈N/\in_rel3 u v w e/\y∪{y}=u∪{u}/\z=v/\d=w∪{w}]]. clear H2.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀x,∀z,∀a,∀b,∀c,∀d,x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 y z d e/\in_rel3 x y a f/\in_rel3 x z b f/\in_rel3 x d c f->in_rel3 a b c e;;x∈N/\y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N;;in_rel3 y∪{y} z d e/\in_rel3 x y∪{y} a f/\in_rel3 x z b f/\in_rel3 x d c f|--in_rel3 a b c e]]by Tauto. clear H1 H3 H.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀x,∀z,∀a,∀b,∀c,∀d,x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 y z d e/\in_rel3 x y a f/\in_rel3 x z b f/\in_rel3 x d c f->in_rel3 a b c e;;y∈N|--x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 y∪{y} z d e/\in_rel3 x y∪{y} a f/\in_rel3 x z b f/\in_rel3 x d c f->in_rel3 a b c e]]by Tauto.
universal generalization H x z a b c d. clear H.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--y∈N/\(∀x,∀z,∀a,∀b,∀c,∀d,x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 y z d e/\in_rel3 x y a f/\in_rel3 x z b f/\in_rel3 x d c f->in_rel3 a b c e)->y∪{y}∈N/\(∀x,∀z,∀a,∀b,∀c,∀d,x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 y∪{y} z d e/\in_rel3 x y∪{y} a f/\in_rel3 x z b f/\in_rel3 x d c f->in_rel3 a b c e)]]by Tauto.
universal generalization H y.
The conclusion is already proved.
Qed.

Lemma mult_dist:
  [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--∀x,∀y,∀z,∀a,∀b,∀c,∀d,x∈N/\y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 y z d e/\in_rel3 x y a f/\in_rel3 x z b f/\in_rel3 x d c f->in_rel3 a b c e]].
Proof.
pose proof mathematical_induction.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀y,y∈X<->y∈N/\(∀x,∀z,∀a,∀b,∀c,∀d,x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 y z d e/\in_rel3 x y a f/\in_rel3 x z b f/\in_rel3 x d c f->in_rel3 a b c e)|--∀y,y∈X<->y∈N/\(∀x,∀z,∀a,∀b,∀c,∀d,x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 y z d e/\in_rel3 x y a f/\in_rel3 x z b f/\in_rel3 x d c f->in_rel3 a b c e)]] by Tauto.
universal instantiation H0 [[∅]].
pose proof mult_dist_zero.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀y,y∈X<->y∈N/\(∀x,∀z,∀a,∀b,∀c,∀d,x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 y z d e/\in_rel3 x y a f/\in_rel3 x z b f/\in_rel3 x d c f->in_rel3 a b c e)|--∅∈X]] by Tauto. clear H1 H2.

pose proof mult_dist_induction.
universal instantiation H1 n. clear H1.
universal instantiation H0 n.
universal instantiation H0 y.
universal instantiation H0 [[n∪{n}]]. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀y,y∈X<->y∈N/\(∀x,∀z,∀a,∀b,∀c,∀d,x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 y z d e/\in_rel3 x y a f/\in_rel3 x z b f/\in_rel3 x d c f->in_rel3 a b c e)|-- n∈N -> n∈X->n∪{n}∈X]] by Tauto. clear H2 H1 H5.
universal generalization H0 n. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀y,y∈X<->y∈N/\(∀x,∀z,∀a,∀b,∀c,∀d,x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 y z d e/\in_rel3 x y a f/\in_rel3 x z b f/\in_rel3 x d c f->in_rel3 a b c e)|--∀n,n∈N->n∈X]]by Tauto.
universal instantiation H0 y. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀y,y∈X<->y∈N/\(∀x,∀z,∀a,∀b,∀c,∀d,x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 y z d e/\in_rel3 x y a f/\in_rel3 x z b f/\in_rel3 x d c f->in_rel3 a b c e)|--y∈N->(∀x,∀z,∀a,∀b,∀c,∀d,x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 y z d e/\in_rel3 x y a f/\in_rel3 x z b f/\in_rel3 x d c f->in_rel3 a b c e)]]by Tauto.
existential instantiation H0 [[∃X,∀y,y∈X<->y∈N/\(∀x,∀z,∀a,∀b,∀c,∀d,x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 y z d e/\in_rel3 x y a f/\in_rel3 x z b f/\in_rel3 x d c f->in_rel3 a b c e)]].
apply separation [[∃X,∀y,y∈X<->y∈N/\(∀x,∀z,∀a,∀b,∀c,∀d,x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 y z d e/\in_rel3 x y a f/\in_rel3 x z b f/\in_rel3 x d c f->in_rel3 a b c e)]].
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--y∈N->(∀x,∀z,∀a,∀b,∀c,∀d,x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 y z d e/\in_rel3 x y a f/\in_rel3 x z b f/\in_rel3 x d c f->in_rel3 a b c e)]]by Tauto.
universal generalization H7 y. clear H H3 H4 H1 H2 H0 H5 H6 H7.

universal instantiation H8 y.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;y∈N|--∀x,∀z,∀a,∀b,∀c,∀d,x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 y z d e/\in_rel3 x y a f/\in_rel3 x z b f/\in_rel3 x d c f->in_rel3 a b c e]]by Tauto.
universal instantiation H0 x z a b c d.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--x∈N/\y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 y z d e/\in_rel3 x y a f/\in_rel3 x z b f/\in_rel3 x d c f->in_rel3 a b c e]]by Tauto.
universal generalization H2 y z a b c d.
universal generalization H3 x.
The conclusion is already proved.
Qed.

Lemma mult_dist_PtoM_zero:
  [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--∀x,∀z,∀a,∀b,∀c,∀d,x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 ∅ z d e/\in_rel3 x ∅ a f/\in_rel3 x z b f/\in_rel3 a b c e->in_rel3 x d c f]].
Proof.
pose proof plus_func_zero.
universal instantiation H z d. clear H.
pose proof mult_func_zero.
universal instantiation H x a. clear H.
apply PEq_sub a [[∅]] [[in_rel3 ∅ b c e]].
assert [[ZF;;is_natural_number N;;is_plus e N|--∀x,x∈N->in_rel3 ∅ x x e]] by Tauto.
universal instantiation H2 b. clear H2.
pose proof plus_func.
universal instantiation H2 [[∅]] b b c. clear H2.
apply PEq_sub z d [[in_rel3 x d b f]].
apply PEq_sub b c [[in_rel3 x d c f]].
assert [[ZF;;is_natural_number N;;is_plus e N|--b∈N/\c∈N/\in_rel3 ∅ b c e/\in_rel3 x d b f->in_rel3 x d c f]]by Tauto. clear H3 H4 H5.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 ∅ z d e/\in_rel3 x ∅ a f/\in_rel3 x z b f/\in_rel3 a b c e->in_rel3 x d c f]]by Tauto.
universal generalization H3 x z a b c d.
The conclusion is already proved.
Qed.

Lemma mult_dist_PtoM_induction:
  [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--∀y,y∈N/\(∀x,∀z,∀a,∀b,∀c,∀d,x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 y z d e/\in_rel3 x y a f/\in_rel3 x z b f/\in_rel3 a b c e->in_rel3 x d c f)->y∪{y}∈N/\(∀x,∀z,∀a,∀b,∀c,∀d,x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 y∪{y} z d e/\in_rel3 x y∪{y} a f/\in_rel3 x z b f/\in_rel3 a b c e->in_rel3 x d c f)]].
Proof.
pose proof Sn_inversion.
universal instantiation H y u.
universal instantiation H y m. clear H.
pose proof equal_rev.
universal instantiation H y u.
universal instantiation H z v.
universal instantiation H x g.
universal instantiation H y m. clear H.
assert [[ZF|--y∪{y}=u∪{u}->u=y]]by Tauto.
assert [[ZF|--y∪{y}=m∪{m}->m=y]]by Tauto. clear H0 H1 H2 H5.
apply PEq_sub u y [[in_rel3 y v w e]].
apply PEq_sub v z [[in_rel3 y z w e]].
assert [[ZF|--y∪{y}=u∪{u}/\z=v/\in_rel3 u v w e->in_rel3 y z w e]]by Tauto. clear H3 H H0 H1.
apply PEq_sub g x [[in_rel3 x m n f]].
apply PEq_sub m y [[in_rel3 x y n f]].
assert [[ZF|--x=g/\y∪{y}=m∪{m}/\in_rel3 g m n f->in_rel3 x y n f]]by Tauto. clear H4 H6 H H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀x,∀z,∀a,∀b,∀c,∀d,x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 y z d e/\in_rel3 x y a f/\in_rel3 x z b f/\in_rel3 a b c e->in_rel3 x d c f|--∀x,∀z,∀a,∀b,∀c,∀d,x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 y z d e/\in_rel3 x y a f/\in_rel3 x z b f/\in_rel3 a b c e->in_rel3 x d c f]]by Tauto.
universal instantiation H x z n b h w. clear H.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--∀ x,∀ y,∀ z,∀ a,x ∈ N /\ y ∈ N /\ z ∈ N /\ a ∈ N ->in_rel3 x y z f -> in_rel3 z x a e -> in_rel3 x y ∪ {y} a f]]by Tauto.
universal instantiation H x w h p. clear H.
pose proof equal_rev.
universal instantiation H d [[w∪{w}]]. clear H.
apply PEq_sub [[w∪{w}]] d [[in_rel3 x d p f]].
assert [[ZF;;d=w∪{w};;in_rel3 x w∪{w} p f|--in_rel3 x d p f]]by Tauto. clear H4.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;x∈N/\w∈N/\h∈N/\p∈N/\in_rel3 x w h f/\in_rel3 h x p e;;d=w∪{w}|--in_rel3 x d p f]]by Tauto. clear H3 H H5.
pose proof plus_same.
universal instantiation H n b h x a p. clear H.
pose proof plus_func.
universal instantiation H a b p c. clear H.
apply PEq_sub p c [[in_rel3 x d c f]].
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;x∈N/\a∈N/\b∈N/\c∈N;;w∈N/\d=w∪{w};;h∈N/\in_rel3 x w h f;;n∈N/\in_rel3 n b h e/\in_rel3 n x a e;;in_rel3 a b c e;;p∈N/\in_rel3 h x p e|--in_rel3 x d c f]]by Tauto. clear H4 H3 H5 H.
pose proof in_plus_exists.
universal instantiation H h x. clear H.
existential instantiation H6 [[∃z,z∈N/\in_rel3 h x z e]]. clear H6.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;x∈N/\a∈N/\b∈N/\c∈N;;w∈N/\d=w∪{w};;h∈N/\in_rel3 x w h f;;n∈N/\in_rel3 n b h e/\in_rel3 n x a e;;in_rel3 a b c e|--in_rel3 x d c f]]by Tauto. clear H3 H.
pose proof equal_rev.
universal instantiation H x g. clear H.
apply PEq_sub g x [[in_rel3 n x a e]].
assert [[ZF;;x=g;;in_rel3 n g a e|--in_rel3 n x a e]]by Tauto. clear H3 H.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀x,∀z,∀a,∀b,∀c,∀d,x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 y z d e/\in_rel3 x y a f/\in_rel3 x z b f/\in_rel3 a b c e->in_rel3 x d c f;;x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N;;in_rel3 x z b f/\in_rel3 a b c e;;u∈N/\v∈N/\w∈N/\in_rel3 u v w e/\y∪{y}=u∪{u}/\z=v/\d=w∪{w};;g∈N/\m∈N/\n∈N/\in_rel3 g m n f/\x=g/\y∪{y}=m∪{m}/\in_rel3 n g a e;;h∈N/\in_rel3 n b h e|--in_rel3 x d c f]]by Tauto. clear H2 H1 H0 H4 H5.
existential instantiation H [[∃z,z∈N/\in_rel3 n b z e]]. clear H.
pose proof in_plus_exists.
universal instantiation H n b. clear H.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀x,∀z,∀a,∀b,∀c,∀d,x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 y z d e/\in_rel3 x y a f/\in_rel3 x z b f/\in_rel3 a b c e->in_rel3 x d c f;;x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N;;in_rel3 x z b f/\in_rel3 a b c e;;u∈N/\v∈N/\w∈N/\in_rel3 u v w e/\y∪{y}=u∪{u}/\z=v/\d=w∪{w};;g∈N/\m∈N/\n∈N/\in_rel3 g m n f/\x=g/\y∪{y}=m∪{m}/\in_rel3 n g a e|--in_rel3 x d c f]]by Tauto. clear H0 H1.
pose proof is_mult_inversion.
universal instantiation H0 x [[y∪{y}]] a. clear H0.
pose proof not_empty.
universal instantiation H0 y. clear H0.
existential instantiation H [[∃u,∃v,∃w,u∈N/\v∈N/\w∈N/\in_rel3 u v w f/\x=u/\y∪{y}=v∪{v}/\in_rel3 w u a e]]. clear H.
assert [[ZF;;is_natural_number N|--∀x,x∈N->x∪{x}∈N]]by Tauto.
universal instantiation H y. clear H.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀x,∀z,∀a,∀b,∀c,∀d,x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 y z d e/\in_rel3 x y a f/\in_rel3 x z b f/\in_rel3 a b c e->in_rel3 x d c f;;y∈N;;x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N;;in_rel3 x y∪{y} a f/\in_rel3 x z b f/\in_rel3 a b c e;;u∈N/\v∈N/\w∈N/\in_rel3 u v w e/\y∪{y}=u∪{u}/\z=v/\d=w∪{w}|--in_rel3 x d c f]]by Tauto. clear H1 H0.
pose proof is_plus_inversion.
universal instantiation H0 [[y∪{y}]] z d. clear H0.
existential instantiation H [[∃u,∃v,∃w,u∈N/\v∈N/\w∈N/\in_rel3 u v w e/\y∪{y}=u∪{u}/\z=v/\d=w∪{w}]]. clear H.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀x,∀z,∀a,∀b,∀c,∀d,x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 y z d e/\in_rel3 x y a f/\in_rel3 x z b f/\in_rel3 a b c e->in_rel3 x d c f;;y∈N;;x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N;;in_rel3 y∪{y} z d e/\in_rel3 x y∪{y} a f/\in_rel3 x z b f/\in_rel3 a b c e|--in_rel3 x d c f]]by Tauto. clear H2 H1 H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀x,∀z,∀a,∀b,∀c,∀d,x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 y z d e/\in_rel3 x y a f/\in_rel3 x z b f/\in_rel3 a b c e->in_rel3 x d c f;;y∈N|--x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 y∪{y} z d e/\in_rel3 x y∪{y} a f/\in_rel3 x z b f/\in_rel3 a b c e->in_rel3 x d c f]]by Tauto. clear H.
universal generalization H0 x z a b c d. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--y∈N/\(∀x,∀z,∀a,∀b,∀c,∀d,x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 y z d e/\in_rel3 x y a f/\in_rel3 x z b f/\in_rel3 a b c e->in_rel3 x d c f)->y∪{y}∈N/\(∀x,∀z,∀a,∀b,∀c,∀d,x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 y∪{y} z d e/\in_rel3 x y∪{y} a f/\in_rel3 x z b f/\in_rel3 a b c e->in_rel3 x d c f)]]by Tauto.
universal generalization H0 y. clear H3 H H0.
The conclusion is already proved.
Qed.

Lemma mult_dist_PtoM:
  [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--∀x,∀y,∀z,∀a,∀b,∀c,∀d,x∈N/\y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 y z d e/\in_rel3 x y a f/\in_rel3 x z b f/\in_rel3 a b c e->in_rel3 x d c f]].
Proof.
pose proof mathematical_induction.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀y,y∈X<->y∈N/\(∀x,∀z,∀a,∀b,∀c,∀d,x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 y z d e/\in_rel3 x y a f/\in_rel3 x z b f/\in_rel3 a b c e->in_rel3 x d c f)|--∀y,y∈X<->y∈N/\(∀x,∀z,∀a,∀b,∀c,∀d,x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 y z d e/\in_rel3 x y a f/\in_rel3 x z b f/\in_rel3 a b c e->in_rel3 x d c f)]] by Tauto.
universal instantiation H0 [[∅]].
pose proof mult_dist_PtoM_zero.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀y,y∈X<->y∈N/\(∀x,∀z,∀a,∀b,∀c,∀d,x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 y z d e/\in_rel3 x y a f/\in_rel3 x z b f/\in_rel3 a b c e->in_rel3 x d c f)|--∅∈X]] by Tauto. clear H1 H2.

pose proof mult_dist_PtoM_induction.
universal instantiation H1 n. clear H1.
universal instantiation H0 n.
universal instantiation H0 y.
universal instantiation H0 [[n∪{n}]]. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀y,y∈X<->y∈N/\(∀x,∀z,∀a,∀b,∀c,∀d,x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 y z d e/\in_rel3 x y a f/\in_rel3 x z b f/\in_rel3 a b c e->in_rel3 x d c f)|-- n∈ N -> n∈X->n∪{n}∈X]] by Tauto. clear H2 H1 H5.
universal generalization H0 n. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀y,y∈X<->y∈N/\(∀x,∀z,∀a,∀b,∀c,∀d,x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 y z d e/\in_rel3 x y a f/\in_rel3 x z b f/\in_rel3 a b c e->in_rel3 x d c f)|--∀n,n∈N->n∈X]]by Tauto.
universal instantiation H0 y. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀y,y∈X<->y∈N/\(∀x,∀z,∀a,∀b,∀c,∀d,x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 y z d e/\in_rel3 x y a f/\in_rel3 x z b f/\in_rel3 a b c e->in_rel3 x d c f)|--y∈N->(∀x,∀z,∀a,∀b,∀c,∀d,x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 y z d e/\in_rel3 x y a f/\in_rel3 x z b f/\in_rel3 a b c e->in_rel3 x d c f)]]by Tauto.
existential instantiation H0 [[∃X,∀y,y∈X<->y∈N/\(∀x,∀z,∀a,∀b,∀c,∀d,x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 y z d e/\in_rel3 x y a f/\in_rel3 x z b f/\in_rel3 a b c e->in_rel3 x d c f)]].
apply separation [[∃X,∀y,y∈X<->y∈N/\(∀x,∀z,∀a,∀b,∀c,∀d,x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 y z d e/\in_rel3 x y a f/\in_rel3 x z b f/\in_rel3 a b c e->in_rel3 x d c f)]].
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--y∈N->(∀x,∀z,∀a,∀b,∀c,∀d,x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 y z d e/\in_rel3 x y a f/\in_rel3 x z b f/\in_rel3 a b c e->in_rel3 x d c f)]]by Tauto.
universal generalization H7 y. clear H H3 H4 H1 H2 H0 H5 H6 H7.

universal instantiation H8 y.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;y∈N|--∀x,∀z,∀a,∀b,∀c,∀d,x∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 y z d e/\in_rel3 x y a f/\in_rel3 x z b f/\in_rel3 a b c e->in_rel3 x d c f]]by Tauto.
universal instantiation H0 x z a b c d.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--x∈N/\y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\d∈N/\in_rel3 y z d e/\in_rel3 x y a f/\in_rel3 x z b f/\in_rel3 a b c e->in_rel3 x d c f]]by Tauto.
universal generalization H2 y z a b c d.
universal generalization H3 x.
The conclusion is already proved.
Qed.

Lemma mult_assoc_zero:
  [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--∀x,∀y,∀a,∀b,∀c,x∈N/\y∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a f/\in_rel3 y ∅ b f/\in_rel3 a ∅ c f->in_rel3 x b c f]].
Proof.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--∀n,n∈N->in_rel3 n ∅ ∅ f]] by Tauto.
universal instantiation H x. clear H.
pose proof mult_func_zero.
universal instantiation H y b.
universal instantiation H a c. clear H.
pose proof equal_rev.
universal instantiation H b [[∅]].
universal instantiation H c [[∅]]. clear H.
apply PEq_sub [[∅]] b [[in_rel3 x b ∅ f]].
apply PEq_sub [[∅]] c [[in_rel3 x b c f]].
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--x∈N/\y∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a f/\in_rel3 y ∅ b f/\in_rel3 a ∅ c f->in_rel3 x b c f]] by Tauto.
universal generalization H6 x y a b c.
The conclusion is already proved.
Qed.

Lemma mult_assoc_induction:
  [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--∀z,z∈N/\(∀x,∀y,∀a,∀b,∀c,x∈N/\y∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a f/\in_rel3 y z b f/\in_rel3 a z c f->in_rel3 x b c f)->z∪{z}∈N/\(∀x,∀y,∀a,∀b,∀c,x∈N/\y∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a f/\in_rel3 y z∪{z} b f/\in_rel3 a z∪{z} c f->in_rel3 x b c f)]].
Proof.
pose proof equal_rev.
universal instantiation H y u.
universal instantiation H z v. clear H.
apply PEq_sub u y [[in_rel3 y v w f]].
apply PEq_sub v z [[in_rel3 y z w f]].
apply PEq_sub u y [[in_rel3 w y b e]].
assert [[ZF;;in_rel3 u v w f/\y=u/\z=v/\in_rel3 w u b e|--in_rel3 y z w f/\in_rel3 w y b e]]by Tauto. clear H0 H1 H H2 H3.
pose proof equal_rev.
universal instantiation H a g.
universal instantiation H z m. clear H.
apply PEq_sub g a [[in_rel3 a m n f]].
apply PEq_sub m z [[in_rel3 a z n f]].
apply PEq_sub g a [[in_rel3 n a c e]].
assert [[ZF;;in_rel3 g m n f/\a=g/\z=m/\in_rel3 n g c e|--in_rel3 a z n f/\in_rel3 n a c e]]by Tauto. clear H0 H1 H H2 H3.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;z∈N/\(∀x,∀y,∀a,∀b,∀c,x∈N/\y∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a f/\in_rel3 y z b f/\in_rel3 a z c f->in_rel3 x b c f)|--∀x,∀y,∀a,∀b,∀c,x∈N/\y∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a f/\in_rel3 y z b f/\in_rel3 a z c f->in_rel3 x b c f]]by Tauto.
universal instantiation H x y a w n. clear H.
pose proof mult_dist_PtoM.
universal instantiation H x w y n a c b. clear H.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;z∈N/\(∀x,∀y,∀a,∀b,∀c,x∈N/\y∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a f/\in_rel3 y z b f/\in_rel3 a z c f->in_rel3 x b c f);;x∈N/\y∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a f;;u∈N/\v∈N/\w∈N/\in_rel3 u v w f/\y=u/\z=v/\in_rel3 w u b e;;g∈N/\m∈N/\n∈N/\in_rel3 g m n f/\a=g/\z=m/\in_rel3 n g c e|--in_rel3 x b c f]]by Tauto. clear H4 H5 H0 H1.
pose proof Sn_inversion.
universal instantiation H0 z v.
universal instantiation H0 z m. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;z∈N/\(∀x,∀y,∀a,∀b,∀c,x∈N/\y∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a f/\in_rel3 y z b f/\in_rel3 a z c f->in_rel3 x b c f);;x∈N/\y∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a f;;u∈N/\v∈N/\w∈N/\in_rel3 u v w f/\y=u/\z∪{z}=v∪{v}/\in_rel3 w u b e;;g∈N/\m∈N/\n∈N/\in_rel3 g m n f/\a=g/\z∪{z}=m∪{m}/\in_rel3 n g c e|--in_rel3 x b c f]]by Tauto. clear H H1 H2.
existential instantiation H0 [[∃u,∃v,∃w,u∈N/\v∈N/\w∈N/\in_rel3 u v w f/\a=u/\z∪{z}=v∪{v}/\in_rel3 w u c e]]. clear H0.
pose proof is_mult_inversion.
universal instantiation H0 a [[z∪{z}]] c. clear H0.
assert [[ZF;;is_natural_number N|--∀x,x∈N->x∪{x}∈N]]by Tauto.
universal instantiation H0 z. clear H0.
pose proof not_empty.
universal instantiation H0 z. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;z∈N/\(∀x,∀y,∀a,∀b,∀c,x∈N/\y∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a f/\in_rel3 y z b f/\in_rel3 a z c f->in_rel3 x b c f);;x∈N/\y∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a f/\in_rel3 a z∪{z} c f;;u∈N/\v∈N/\w∈N/\in_rel3 u v w f/\y=u/\z∪{z}=v∪{v}/\in_rel3 w u b e|--in_rel3 x b c f]]by Tauto. clear H H1.
existential instantiation H0 [[∃u,∃v,∃w,u∈N/\v∈N/\w∈N/\in_rel3 u v w f/\y=u/\z∪{z}=v∪{v}/\in_rel3 w u b e]]. clear H0.
pose proof is_mult_inversion.
universal instantiation H0 y [[z∪{z}]] b. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;z∈N/\(∀x,∀y,∀a,∀b,∀c,x∈N/\y∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a f/\in_rel3 y z b f/\in_rel3 a z c f->in_rel3 x b c f)|--x∈N/\y∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a f/\in_rel3 y z∪{z} b f/\in_rel3 a z∪{z} c f->in_rel3 x b c f]]by Tauto. clear H3 H H1.
universal generalization H0 x y a b c. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--z∈N/\(∀x,∀y,∀a,∀b,∀c,x∈N/\y∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a f/\in_rel3 y z b f/\in_rel3 a z c f->in_rel3 x b c f)->z∪{z}∈N/\(∀x,∀y,∀a,∀b,∀c,x∈N/\y∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a f/\in_rel3 y z∪{z} b f/\in_rel3 a z∪{z} c f->in_rel3 x b c f)]]by Tauto.
universal generalization H0 z. clear H0.
The conclusion is already proved.
Qed.

Lemma mult_assoc_half:
  [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--∀x,∀y,∀z,∀a,∀b,∀c,x∈N/\y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a f/\in_rel3 y z b f/\in_rel3 a z c f->in_rel3 x b c f]].
Proof.
pose proof mathematical_induction.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀z,z∈X<->z∈N/\(∀x,∀y,∀a,∀b,∀c,x∈N/\y∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a f/\in_rel3 y z b f/\in_rel3 a z c f->in_rel3 x b c f)|--∀z,z∈X<->z∈N/\(∀x,∀y,∀a,∀b,∀c,x∈N/\y∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a f/\in_rel3 y z b f/\in_rel3 a z c f->in_rel3 x b c f)]] by Tauto.
universal instantiation H0 [[∅]].
pose proof mult_assoc_zero.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀z,z∈X<->z∈N/\(∀x,∀y,∀a,∀b,∀c,x∈N/\y∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a f/\in_rel3 y z b f/\in_rel3 a z c f->in_rel3 x b c f)|--∅∈X]] by Tauto. clear H1 H2.

pose proof mult_assoc_induction.
universal instantiation H1 n. clear H1.
universal instantiation H0 n.
universal instantiation H0 z.
universal instantiation H0 [[n∪{n}]]. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀z,z∈X<->z∈N/\(∀x,∀y,∀a,∀b,∀c,x∈N/\y∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a f/\in_rel3 y z b f/\in_rel3 a z c f->in_rel3 x b c f)|-- n∈ N -> n∈X->n∪{n}∈X]] by Tauto. clear H2 H1 H5.
universal generalization H0 n. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀z,z∈X<->z∈N/\(∀x,∀y,∀a,∀b,∀c,x∈N/\y∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a f/\in_rel3 y z b f/\in_rel3 a z c f->in_rel3 x b c f)|--∀n,n∈N->n∈X]]by Tauto.
universal instantiation H0 z. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀z,z∈X<->z∈N/\(∀x,∀y,∀a,∀b,∀c,x∈N/\y∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a f/\in_rel3 y z b f/\in_rel3 a z c f->in_rel3 x b c f)|--z∈N->(∀x,∀y,∀a,∀b,∀c,x∈N/\y∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a f/\in_rel3 y z b f/\in_rel3 a z c f->in_rel3 x b c f)]]by Tauto.
existential instantiation H0 [[∃X,∀z,z∈X<->z∈N/\(∀x,∀y,∀a,∀b,∀c,x∈N/\y∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a f/\in_rel3 y z b f/\in_rel3 a z c f->in_rel3 x b c f)]].
apply separation [[∃X,∀z,z∈X<->z∈N/\(∀x,∀y,∀a,∀b,∀c,x∈N/\y∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a f/\in_rel3 y z b f/\in_rel3 a z c f->in_rel3 x b c f)]].
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--z∈N->(∀x,∀y,∀a,∀b,∀c,x∈N/\y∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a f/\in_rel3 y z b f/\in_rel3 a z c f->in_rel3 x b c f)]]by Tauto.
universal generalization H7 z. clear H H3 H4 H1 H2 H0 H5 H6 H7.

universal instantiation H8 z.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;z∈N|--∀x,∀y,∀a,∀b,∀c,x∈N/\y∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a f/\in_rel3 y z b f/\in_rel3 a z c f->in_rel3 x b c f]]by Tauto.
universal instantiation H0 x y a b c.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--x∈N/\y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a f/\in_rel3 y z b f/\in_rel3 a z c f->in_rel3 x b c f]]by Tauto.
universal generalization H2 x y z a b c.
The conclusion is already proved.
Qed.

Lemma zero_mult_n_is_zero_base:
  [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--in_rel3 ∅ ∅ ∅ f]].
Proof.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--∀x,x∈N->in_rel3 x ∅ ∅ f]]by Tauto.
universal instantiation H [[∅]].
The conclusion is already proved.
Qed.

Lemma zero_mult_n_is_zero_induction:
  [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--∀n,n∈N/\in_rel3 ∅ n ∅ f->n∪{n}∈N/\in_rel3 ∅ n∪{n} ∅ f]].
Proof.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--∀x,∀y,∀z,∀a,x∈N/\y∈N/\z∈N/\a∈N->in_rel3 x y z f->in_rel3 z x a e->in_rel3 x y∪{y} a f]]by Tauto.
universal instantiation H [[∅]] n [[∅]] [[∅]]. clear H.
assert [[ZF;;is_natural_number N;;is_plus e N|--∀x,x∈N->in_rel3 ∅ x x e]]by Tauto.
universal instantiation H [[∅]]. clear H.
assert [[ZF;;is_natural_number N|--∀x,x∈N->x∪{x}∈N]]by Tauto.
universal instantiation H [[∅]].
universal instantiation H n. clear H.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--n∈N/\in_rel3 ∅ n ∅ f->n∪{n}∈N/\in_rel3 ∅ n∪{n} ∅ f]]by Tauto.
universal generalization H n.
The conclusion is already proved.
Qed.

Lemma zero_mult_n_is_zero:
  [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--∀n,n∈N->in_rel3 ∅ n ∅ f]].
Proof.
pose proof mathematical_induction.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀n,n∈X<->n∈N/\in_rel3 ∅ n ∅ f|--∀n,n∈X<->n∈N/\in_rel3 ∅ n ∅ f]] by Tauto.
universal instantiation H0 [[∅]].
pose proof zero_mult_n_is_zero_base.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀n,n∈X<->n∈N/\in_rel3 ∅ n ∅ f|--∅∈X]] by Tauto. clear H1 H2.

pose proof zero_mult_n_is_zero_induction.
universal instantiation H1 n. clear H1.
universal instantiation H0 n.
universal instantiation H0 [[n∪{n}]]. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀n,n∈X<->n∈N/\in_rel3 ∅ n ∅ f|-- n∈ N -> n∈X->n∪{n}∈X]] by Tauto. clear H2 H4.
universal generalization H0 n. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀n,n∈X<->n∈N/\in_rel3 ∅ n ∅ f|--∀n,n∈N->n∈X]]by Tauto. clear H2.
universal instantiation H0 n. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀n,n∈X<->n∈N/\in_rel3 ∅ n ∅ f|--n∈N->in_rel3 ∅ n ∅ f]]by Tauto.
existential instantiation H0 [[∃X,∀n,n∈X<->n∈N/\in_rel3 ∅ n ∅ f]].
apply separation [[∃X,∀n,n∈X<->n∈N/\in_rel3 ∅ n ∅ f]].
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--n∈N->in_rel3 ∅ n ∅ f]]by Tauto.
universal generalization H6 n. clear H H3 H1 H2 H0 H4 H5 H6.
The conclusion is already proved.
Qed.

Lemma m_mult_n_plus_n_is_Sm_mult_n_zero:
  [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--∀m,∀x,∀y,m∈N/\x∈N/\y∈N/\in_rel3 m ∅ x f/\in_rel3 x ∅ y e->in_rel3 m∪{m} ∅ y f]].
Proof.
pose proof mult_func_zero.
universal instantiation H m x. clear H.
assert [[ZF;;is_natural_number N|--∀x,x∈N->x∪{x}∈N]]by Tauto.
universal instantiation H m. clear H.
pose proof plus_func_zero.
universal instantiation H [[∅]] y. clear H.
apply PEq_sub using condition x [[∅]] [[in_rel3 x ∅ y e]].
apply PEq_sub [[∅]] y [[in_rel3 m∪{m} ∅ y f]].
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--∀x,x∈N->in_rel3 x ∅ ∅ f]]by Tauto.
universal instantiation H4 [[m∪{m}]]. clear H4.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--m∈N/\x∈N/\y∈N/\in_rel3 m ∅ x f/\in_rel3 x ∅ y e->in_rel3 m∪{m} ∅ y f]]by Tauto. clear H0 H1 H2 H H3 H5.
universal generalization H4 m x y.
The conclusion is already proved.
Qed.

Lemma m_mult_n_plus_n_is_Sm_mult_n_induction:
  [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--∀n,n∈N/\(∀m,∀x,∀y,m∈N/\x∈N/\y∈N/\in_rel3 m n x f/\in_rel3 x n y e->in_rel3 m∪{m} n y f)->n∪{n}∈N/\(∀m,∀x,∀y,m∈N/\x∈N/\y∈N/\in_rel3 m n∪{n} x f/\in_rel3 x n∪{n} y e->in_rel3 m∪{m} n∪{n} y f)]].
Proof.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀m,∀x,∀y,m∈N/\x∈N/\y∈N/\in_rel3 m n x f/\in_rel3 x n y e->in_rel3 m∪{m} n y f;;n∈N|--∀m,∀x,∀y,m∈N/\x∈N/\y∈N/\in_rel3 m n x f/\in_rel3 x n y e->in_rel3 m∪{m} n y f]]by Tauto.
universal instantiation H m w z. clear H.
pose proof plus_same.
universal instantiation H w n z m x g. clear H.
pose proof plus_comm.
universal instantiation H x n g. clear H.
assert [[ZF;;is_natural_number N;;is_plus e N|--∀x,∀y,∀z,x∈N/\y∈N/\z∈N->in_rel3 x y z e->in_rel3 x∪{x} y z∪{z} e]]by Tauto.
universal instantiation H n x g. clear H.
pose proof plus_comm.
universal instantiation H [[n∪{n}]] x [[g∪{g}]]. clear H.
assert [[ZF;;is_natural_number N;;is_plus e N;;w∈N/\n∈N/\n∪{n}∈N/\z∈N/\m∈N/\x∈N/\g∈N/\g∪{g}∈N/\in_rel3 w n z e/\in_rel3 w m x e/\in_rel3 z m g e|--in_rel3 x n∪{n} g∪{g} e]]by Tauto. clear H1 H2 H3 H4.
pose proof plus_func.
universal instantiation H1 x [[n∪{n}]] [[g∪{g}]] y. clear H1.
assert [[ZF;;is_natural_number N;;is_plus e N;;w∈N/\n∈N/\n∪{n}∈N/\z∈N/\m∈N/\x∈N/\y∈N/\g∈N/\g∪{g}∈N/\in_rel3 w n z e/\in_rel3 w m x e/\in_rel3 z m g e/\in_rel3 x n∪{n} y e|--g∪{g}=y]]by Tauto. clear H H2.
pose proof plus_comm.
universal instantiation H z m g. clear H.
assert [[ZF;;is_natural_number N;;is_plus e N|--∀x,∀y,∀z,x∈N/\y∈N/\z∈N->in_rel3 x y z e->in_rel3 x∪{x} y z∪{z} e]]by Tauto.
universal instantiation H m z g. clear H.
pose proof plus_comm.
universal instantiation H [[m∪{m}]] z [[g∪{g}]]. clear H.
assert [[ZF;;is_natural_number N;;is_plus e N;;z∈N/\m∈N/\m∪{m}∈N/\g∈N/\g∪{g}∈N/\in_rel3 z m g e|--in_rel3 z m∪{m} g∪{g} e]]by Tauto. clear H2 H3 H4.
apply PEq_sub [[g∪{g}]] y [[in_rel3 z m∪{m} y e]].
assert [[ZF;;is_natural_number N;;is_plus e N;;w∈N/\n∈N/\n∪{n}∈N/\m∈N/\m∪{m}∈N/\x∈N/\y∈N/\z∈N/\g∈N/\g∪{g}∈N/\in_rel3 w n z e/\in_rel3 w m x e/\in_rel3 z m g e/\in_rel3 x n∪{n} y e|--in_rel3 z m∪{m} y e]]by Tauto. clear H1 H H2.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--∀x,∀y,∀z,∀a,x∈N/\y∈N/\z∈N/\a∈N->in_rel3 x y z f->in_rel3 z x a e->in_rel3 x y∪{y} a f]]by Tauto.
universal instantiation H [[m∪{m}]] n z y. clear H.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀m,∀x,∀y,m∈N/\x∈N/\y∈N/\in_rel3 m n x f/\in_rel3 x n y e->in_rel3 m∪{m} n y f;;n∈N/\n∪{n}∈N/\m∈N/\m∪{m}∈N/\x∈N/\y∈N/\in_rel3 x n∪{n} y e;;w∈N/\in_rel3 m n w f/\in_rel3 w m x e;;z∈N/\in_rel3 w n z e;;g∈N/\g∪{g}∈N/\in_rel3 z m g e|--in_rel3 m∪{m} n∪{n} y f]]by Tauto. clear H0 H3 H1.
assert [[ZF;;is_natural_number N|--∀x,x∈N->x∪{x}∈N]]by Tauto.
universal instantiation H0 g.
universal instantiation H0 m.
universal instantiation H0 n. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀m,∀x,∀y,m∈N/\x∈N/\y∈N/\in_rel3 m n x f/\in_rel3 x n y e->in_rel3 m∪{m} n y f;;n∈N/\m∈N/\x∈N/\y∈N/\in_rel3 x n∪{n} y e;;w∈N/\in_rel3 m n w f/\in_rel3 w m x e;;z∈N/\in_rel3 w n z e;;g∈N/\in_rel3 z m g e|--in_rel3 m∪{m} n∪{n} y f]]by Tauto. clear H H1.
existential instantiation H0 [[∃g,g∈N/\in_rel3 z m g e]]. clear H0.
pose proof in_plus_exists.
universal instantiation H0 z m. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀m,∀x,∀y,m∈N/\x∈N/\y∈N/\in_rel3 m n x f/\in_rel3 x n y e->in_rel3 m∪{m} n y f;;n∈N/\m∈N/\x∈N/\y∈N/\in_rel3 x n∪{n} y e;;w∈N/\in_rel3 m n w f/\in_rel3 w m x e;;z∈N/\in_rel3 w n z e|--in_rel3 m∪{m} n∪{n} y f]]by Tauto. clear H H1.
existential instantiation H0 [[∃z,z∈N/\in_rel3 w n z e]]. clear H0.
pose proof in_plus_exists.
universal instantiation H0 w n. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀m,∀x,∀y,m∈N/\x∈N/\y∈N/\in_rel3 m n x f/\in_rel3 x n y e->in_rel3 m∪{m} n y f;;n∈N/\m∈N/\x∈N/\y∈N/\in_rel3 x n∪{n} y e;;w∈N/\in_rel3 m n w f/\in_rel3 w m x e|--in_rel3 m∪{m} n∪{n} y f]]by Tauto. clear H H1.
pose proof equal_rev.
universal instantiation H m u.
universal instantiation H n v. clear H.
pose proof Sn_inversion.
universal instantiation H n v. clear H.
apply PEq_sub u m [[in_rel3 m v w f]].
apply PEq_sub v n [[in_rel3 m n w f]].
apply PEq_sub u m [[in_rel3 w m x e]].
assert [[ZF;;in_rel3 u v w f/\m=u/\n∪{n}=v∪{v}/\in_rel3 w u x e|--in_rel3 m n w f/\in_rel3 w m x e]]by Tauto. clear H1 H4 H5 H H6 H7.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀m,∀x,∀y,m∈N/\x∈N/\y∈N/\in_rel3 m n x f/\in_rel3 x n y e->in_rel3 m∪{m} n y f;;n∈N/\m∈N/\x∈N/\y∈N/\in_rel3 x n∪{n} y e;;u∈N/\v∈N/\w∈N/\in_rel3 u v w f/\m=u/\n∪{n}=v∪{v}/\in_rel3 w u x e|--in_rel3 m∪{m} n∪{n} y f]]by Tauto. clear H0 H8.
existential instantiation H [[∃u,∃v,∃w,u∈N/\v∈N/\w∈N/\in_rel3 u v w f/\m=u/\n∪{n}=v∪{v}/\in_rel3 w u x e]]. clear H.
pose proof is_mult_inversion.
universal instantiation H m [[n∪{n}]] x. clear H.
pose proof not_empty.
universal instantiation H n. clear H.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀m,∀x,∀y,m∈N/\x∈N/\y∈N/\in_rel3 m n x f/\in_rel3 x n y e->in_rel3 m∪{m} n y f;;n∈N|--m∈N/\x∈N/\y∈N/\in_rel3 m n∪{n} x f/\in_rel3 x n∪{n} y e->in_rel3 m∪{m} n∪{n} y f]]by Tauto. clear H2 H0 H1 H4.
universal generalization H m x y. clear H.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--n∈N/\(∀m,∀x,∀y,m∈N/\x∈N/\y∈N/\in_rel3 m n x f/\in_rel3 x n y e->in_rel3 m∪{m} n y f)->n∪{n}∈N/\(∀m,∀x,∀y,m∈N/\x∈N/\y∈N/\in_rel3 m n∪{n} x f/\in_rel3 x n∪{n} y e->in_rel3 m∪{m} n∪{n} y f)]]by Tauto.
universal generalization H n. clear H.
The conclusion is already proved.
Qed.

Lemma m_mult_n_plus_n_is_Sm_mult_n:
  [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--∀m,∀n,∀x,∀y,m∈N/\n∈N/\x∈N/\y∈N/\in_rel3 m n x f/\in_rel3 x n y e->in_rel3 m∪{m} n y f]].
Proof.
pose proof mathematical_induction.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀n,n∈X<->n∈N/\(∀m,∀x,∀y,m∈N/\x∈N/\y∈N/\in_rel3 m n x f/\in_rel3 x n y e->in_rel3 m∪{m} n y f)|--∀n,n∈X<->n∈N/\(∀m,∀x,∀y,m∈N/\x∈N/\y∈N/\in_rel3 m n x f/\in_rel3 x n y e->in_rel3 m∪{m} n y f)]] by Tauto.
universal instantiation H0 [[∅]].
pose proof m_mult_n_plus_n_is_Sm_mult_n_zero.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀n,n∈X<->n∈N/\(∀m,∀x,∀y,m∈N/\x∈N/\y∈N/\in_rel3 m n x f/\in_rel3 x n y e->in_rel3 m∪{m} n y f)|--∅∈X]] by Tauto. clear H1 H2.

pose proof m_mult_n_plus_n_is_Sm_mult_n_induction.
universal instantiation H1 n. clear H1.
universal instantiation H0 n.
universal instantiation H0 [[n∪{n}]]. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀n,n∈X<->n∈N/\(∀m,∀x,∀y,m∈N/\x∈N/\y∈N/\in_rel3 m n x f/\in_rel3 x n y e->in_rel3 m∪{m} n y f)|-- n∈ N -> n∈X->n∪{n}∈X]] by Tauto. clear H2 H4.
universal generalization H0 n. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀n,n∈X<->n∈N/\(∀m,∀x,∀y,m∈N/\x∈N/\y∈N/\in_rel3 m n x f/\in_rel3 x n y e->in_rel3 m∪{m} n y f)|--∀n,n∈N->n∈X]]by Tauto. clear H2.
universal instantiation H0 n. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀n,n∈X<->n∈N/\(∀m,∀x,∀y,m∈N/\x∈N/\y∈N/\in_rel3 m n x f/\in_rel3 x n y e->in_rel3 m∪{m} n y f)|--n∈N->(∀m,∀x,∀y,m∈N/\x∈N/\y∈N/\in_rel3 m n x f/\in_rel3 x n y e->in_rel3 m∪{m} n y f)]]by Tauto.
existential instantiation H0 [[∃X,∀n,n∈X<->n∈N/\(∀m,∀x,∀y,m∈N/\x∈N/\y∈N/\in_rel3 m n x f/\in_rel3 x n y e->in_rel3 m∪{m} n y f)]].
apply separation [[∃X,∀n,n∈X<->n∈N/\(∀m,∀x,∀y,m∈N/\x∈N/\y∈N/\in_rel3 m n x f/\in_rel3 x n y e->in_rel3 m∪{m} n y f)]].
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--n∈N->(∀m,∀x,∀y,m∈N/\x∈N/\y∈N/\in_rel3 m n x f/\in_rel3 x n y e->in_rel3 m∪{m} n y f)]]by Tauto.
universal generalization H6 n. clear H H3 H1 H2 H0 H4 H5 H6.

universal instantiation H7 n.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;n∈N|--∀m,∀x,∀y,m∈N/\x∈N/\y∈N/\in_rel3 m n x f/\in_rel3 x n y e->in_rel3 m∪{m} n y f]]by Tauto.
universal instantiation H0 m x y.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--m∈N/\n∈N/\x∈N/\y∈N/\in_rel3 m n x f/\in_rel3 x n y e->in_rel3 m∪{m} n y f]]by Tauto.
universal generalization H2 m n x y.
The conclusion is already proved.
Qed.

Lemma mult_comm_zero:
  [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--∀x,∀z,x∈N/\z∈N/\in_rel3 x ∅ z f->in_rel3 ∅ x z f]].
Proof.
pose proof mult_func_zero.
universal instantiation H x z. clear H.
pose proof zero_mult_n_is_zero.
universal instantiation H x. clear H.
pose proof equal_rev.
universal instantiation H z [[∅]]. clear H.
apply PEq_sub [[∅]] z [[in_rel3 ∅ x z f]].
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--x∈N/\z∈N/\in_rel3 x ∅ z f->in_rel3 ∅ x z f]]by Tauto.
universal generalization H3 x z.
The conclusion is already proved.
Qed.

Lemma mult_comm_induction:
  [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--∀y,y∈N/\(∀x,∀z,x∈N/\z∈N/\in_rel3 x y z f->in_rel3 y x z f)->y∪{y}∈N/\(∀x,∀z,x∈N/\z∈N/\in_rel3 x y∪{y} z f->in_rel3 y∪{y} x z f)]].
Proof.
pose proof m_mult_n_plus_n_is_Sm_mult_n.
universal instantiation H y x w z. clear H.
pose proof equal_rev.
universal instantiation H x u.
universal instantiation H y v. clear H.
pose proof Sn_inversion.
universal instantiation H y v. clear H.
apply PEq_sub u x [[in_rel3 x v w f]].
apply PEq_sub v y [[in_rel3 x y w f]].
apply PEq_sub u x [[in_rel3 w x z e]].
assert [[ZF;;in_rel3 u v w f/\x=u/\y∪{y}=v∪{v}/\in_rel3 w u z e|--in_rel3 x y w f/\in_rel3 w x z e]]by Tauto. clear H1 H2 H3 H H4 H5.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀x,∀z,x∈N/\z∈N/\in_rel3 x y z f->in_rel3 y x z f|--∀x,∀z,x∈N/\z∈N/\in_rel3 x y z f->in_rel3 y x z f]]by Tauto.
universal instantiation H x w. clear H.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀x,∀z,x∈N/\z∈N/\in_rel3 x y z f->in_rel3 y x z f;;y∈N;;x∈N/\z∈N;;u∈N/\v∈N/\w∈N/\in_rel3 u v w f/\x=u/\y∪{y}=v∪{v}/\in_rel3 w u z e|--in_rel3 y∪{y} x z f]]by Tauto. clear H0 H6 H1.
existential instantiation H [[∃u,∃v,∃w,u∈N/\v∈N/\w∈N/\in_rel3 u v w f/\x=u/\y∪{y}=v∪{v}/\in_rel3 w u z e]]. clear H.
pose proof is_mult_inversion.
universal instantiation H x [[y∪{y}]] z. clear H.
pose proof not_empty.
universal instantiation H y. clear H.
assert [[ZF;;is_natural_number N|--∀x,x∈N->x∪{x}∈N]]by Tauto.
universal instantiation H y. clear H.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀x,∀z,x∈N/\z∈N/\in_rel3 x y z f->in_rel3 y x z f;;y∈N|--x∈N/\z∈N/\in_rel3 x y∪{y} z f->in_rel3 y∪{y} x z f]]by Tauto. clear H0 H1 H2.
universal generalization H x z. clear H.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--y∈N/\(∀x,∀z,x∈N/\z∈N/\in_rel3 x y z f->in_rel3 y x z f)->y∪{y}∈N/\(∀x,∀z,x∈N/\z∈N/\in_rel3 x y∪{y} z f->in_rel3 y∪{y} x z f)]]by Tauto.
universal generalization H y.
The conclusion is already proved.
Qed.

Lemma mult_comm:
  [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--∀x,∀y,∀z,x∈N/\y∈N/\z∈N/\in_rel3 x y z f->in_rel3 y x z f]].
Proof.
pose proof mathematical_induction.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀y,y∈X<->y∈N/\(∀x,∀z,x∈N/\z∈N/\in_rel3 x y z f->in_rel3 y x z f)|--∀y,y∈X<->y∈N/\(∀x,∀z,x∈N/\z∈N/\in_rel3 x y z f->in_rel3 y x z f)]] by Tauto.
universal instantiation H0 [[∅]].
pose proof mult_comm_zero.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀y,y∈X<->y∈N/\(∀x,∀z,x∈N/\z∈N/\in_rel3 x y z f->in_rel3 y x z f)|--∅∈X]] by Tauto. clear H1 H2.

pose proof mult_comm_induction.
universal instantiation H1 n. clear H1.
universal instantiation H0 n.
universal instantiation H0 y.
universal instantiation H0 [[n∪{n}]]. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀y,y∈X<->y∈N/\(∀x,∀z,x∈N/\z∈N/\in_rel3 x y z f->in_rel3 y x z f)|-- n∈ N -> n∈X->n∪{n}∈X]] by Tauto. clear H2 H1 H5.
universal generalization H0 n. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀y,y∈X<->y∈N/\(∀x,∀z,x∈N/\z∈N/\in_rel3 x y z f->in_rel3 y x z f)|--∀n,n∈N->n∈X]]by Tauto.
universal instantiation H0 y. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;∀y,y∈X<->y∈N/\(∀x,∀z,x∈N/\z∈N/\in_rel3 x y z f->in_rel3 y x z f)|--y∈N->(∀x,∀z,x∈N/\z∈N/\in_rel3 x y z f->in_rel3 y x z f)]]by Tauto.
existential instantiation H0 [[∃X,∀y,y∈X<->y∈N/\(∀x,∀z,x∈N/\z∈N/\in_rel3 x y z f->in_rel3 y x z f)]].
apply separation [[∃X,∀y,y∈X<->y∈N/\(∀x,∀z,x∈N/\z∈N/\in_rel3 x y z f->in_rel3 y x z f)]].
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--y∈N->(∀x,∀z,x∈N/\z∈N/\in_rel3 x y z f->in_rel3 y x z f)]]by Tauto.
universal generalization H7 y. clear H H3 H4 H1 H2 H0 H5 H6 H7.

universal instantiation H8 y.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;y∈N|--∀x,∀z,x∈N/\z∈N/\in_rel3 x y z f->in_rel3 y x z f]]by Tauto.
universal instantiation H0 x z.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--x∈N/\y∈N/\z∈N/\in_rel3 x y z f->in_rel3 y x z f]]by Tauto.
universal generalization H2 x y z.
The conclusion is already proved.
Qed.

Lemma mult_assoc:
  [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--∀x,∀y,∀z,∀a,∀b,∀c,x∈N/\y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a f/\in_rel3 y z b f->(in_rel3 a z c f<->in_rel3 x b c f)]].
Proof.
pose proof mult_assoc_half.
universal instantiation H x y z a b c.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;x∈N/\y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a f/\in_rel3 y z b f|--in_rel3 a z c f -> in_rel3 x b c f]]by Tauto. clear H0.
pose proof mult_comm.
universal instantiation H0 x b c.
universal instantiation H0 y z b.
universal instantiation H0 x y a.
universal instantiation H0 z a c.
universal instantiation H z y x b a c. clear H.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N;;x∈N/\y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a f/\in_rel3 y z b f|--in_rel3 x b c f -> in_rel3 a z c f]]by Tauto. clear H0 H2 H3 H4 H5 H6.
assert [[ZF;;is_natural_number N;;is_plus e N;;is_mult f e N|--x∈N/\y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a f/\in_rel3 y z b f->(in_rel3 a z c f<->in_rel3 x b c f)]]by Tauto.
universal generalization H0 x y z a b c.
The conclusion is already proved.
Qed.