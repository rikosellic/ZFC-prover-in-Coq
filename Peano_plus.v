Require Import FV.ZFLib.
Require Import FV.MathmeticalInduction.
Require Import FV.Peano.
   
Lemma plus_unique:
  [[ZF;;is_natural_number N|--∀x,∀y,is_plus x N/\is_plus y N->x=y]].
Proof.
assert [[ZF;;is_natural_number N;;is_plus x N|--∀y,is_legal_plus y N -> x⊆y]]by FOL_tauto.
assert [[ZF;;is_natural_number N;;is_plus y N|--∀x,is_legal_plus x N -> y⊆x]]by FOL_tauto.
universal instantiation H y.
universal instantiation H0 x.
assert [[ZF;;is_natural_number N;;is_plus x N;;is_plus y N|-- x ⊆ y /\ y ⊆ x ]] by FOL_tauto.
pose proof subset_subset_equal.
universal instantiation H4 x y.
assert [[ZF;;is_natural_number N|--is_plus x N/\is_plus y N->x=y]] by FOL_tauto.
universal generalization H6 x y.
The conclusion is already proved.
Qed.

Lemma in_plus_exists_zero:
  [[ZF;;is_natural_number N;;is_plus e N|--∀y,y∈N->∃z,z∈N/\in_rel3 ∅ y z e]].
Proof.
assert [[ZF;;is_natural_number N;;is_plus e N|--∀x,x∈N->in_rel3 ∅ x x e]]by FOL_tauto.
universal instantiation H y.
assert [[ZF;;is_natural_number N;;is_plus e N;;y∈N|--y∈N/\in_rel3 ∅ y y e]]by FOL_tauto.
existential generalization H1 [[∃z,z∈N/\in_rel3 ∅ y z e]]. clear H1.
assert [[ZF;;is_natural_number N;;is_plus e N|--y∈N->∃z,z∈N/\in_rel3 ∅ y z e]]by FOL_tauto.
universal generalization H1 y. clear H1.
The conclusion is already proved.
Qed.

Lemma in_plus_exists_induction:
  [[ZF;;is_natural_number N;;is_plus e N|--∀x,x∈N/\(∀y,y∈N->∃z,z∈N/\in_rel3 x y z e)->x∪{x}∈N/\(∀y,y∈N->∃z,z∈N/\in_rel3 x∪{x} y z e)]].
Proof.
assert [[ZF;;is_natural_number N;;is_plus e N|--∀x,∀y,∀z,x∈N/\y∈N/\z∈N->in_rel3 x y z e->in_rel3 x∪{x} y z∪{z} e]]by FOL_tauto.
universal instantiation H x y z. clear H.
assert [[ZF;;is_natural_number N;;is_plus e N;;∀y,y∈N->(∃z,z∈N/\in_rel3 x y z e)|--∀y,y∈N->(∃z,z∈N/\in_rel3 x y z e)]]by FOL_tauto.
universal instantiation H y. clear H.
assert [[ZF;;is_natural_number N;;is_plus e N;;x∈N/\y∈N;;z∈N/\z∪{z}∈N/\in_rel3 x y z e|--z∪{z}∈N/\in_rel3 x∪{x} y z∪{z} e]]by FOL_tauto.
existential generalization H [[∃z,z∈N/\in_rel3 x∪{x} y z e]]. clear H0 H.
assert [[ZF;;is_natural_number N|--∀x,x∈N->x∪{x}∈N]]by FOL_tauto.
universal instantiation H z.
assert [[ZF;;is_natural_number N;;is_plus e N;;x∈N/\y∈N;;z∈N/\in_rel3 x y z e|--∃z,z∈N/\in_rel3 x∪{x} y z e]]by FOL_tauto. clear H2 H0.
existential instantiation H3 [[∃z,z∈N/\in_rel3 x y z e]]. clear H3.
assert [[ZF;;is_natural_number N;;is_plus e N;;∀y,y∈N->(∃z,z∈N/\in_rel3 x y z e);;x∈N|--y∈N->(∃z,z∈N/\in_rel3 x∪{x} y z e)]]by FOL_tauto. clear H1 H0.
universal generalization H2 y. clear H2.
universal instantiation H x. clear H.
assert [[ZF;;is_natural_number N;;is_plus e N|--x∈N/\(∀y,y∈N->∃z,z∈N/\in_rel3 x y z e)->x∪{x}∈N/\(∀y,y∈N->∃z,z∈N/\in_rel3 x∪{x} y z e)]]by FOL_tauto.
universal generalization H x. clear H.
The conclusion is already proved.
Qed.

Lemma in_plus_exists:
  [[ZF;;is_natural_number N;;is_plus e N|--∀x,∀y,x∈N/\y∈N->∃z,z∈N/\in_rel3 x y z e]].
Proof.
pose proof mathemetical_induction_2.
assert [[ZF;;is_natural_number N;; is_plus e N;;∀ x, x ∈ X <-> x∈N/\(∀y,y∈N->∃z,z∈N/\in_rel3 x y z e)|--∀ x, x ∈ X <-> x∈N/\(∀y,y∈N->∃z,z∈N/\in_rel3 x y z e)]] by FOL_tauto.
universal instantiation H0 [[∅]].
pose proof in_plus_exists_zero.
assert [[ZF;;is_natural_number N;; is_plus e N;;∀ x, x ∈ X <-> x∈N/\(∀y,y∈N->∃z,z∈N/\in_rel3 x y z e)|--∅ ∈ X]] by FOL_tauto. clear H1 H2.

pose proof in_plus_exists_induction.
universal instantiation H1 n. clear H1.
universal instantiation H0 n.
universal instantiation H0 x.
universal instantiation H0 [[n∪{n}]]. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;∀ x, x ∈ X <-> x∈N/\(∀y,y∈N->∃z,z∈N/\in_rel3 x y z e)|--n∈X->n∪{n}∈X]]by FOL_tauto. clear H2 H1 H5.
universal generalization H0 n. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;∀ x, x ∈ X <-> x∈N/\(∀y,y∈N->∃z,z∈N/\in_rel3 x y z e)|--∀n,n∈N->n∈X]]by FOL_tauto.
universal instantiation H0 x. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;∀ x, x ∈ X <-> x∈N/\(∀y,y∈N->∃z,z∈N/\in_rel3 x y z e)|--x∈N->(∀y,y∈N->∃z,z∈N/\in_rel3 x y z e)]]by FOL_tauto.
existential instantiation H0 [[∃X,∀ x, x ∈ X <-> x∈N/\(∀y,y∈N->∃z,z∈N/\in_rel3 x y z e)]].
apply separation [[∃X,∀ x, x ∈ X <-> x∈N/\(∀y,y∈N->∃z,z∈N/\in_rel3 x y z e)]].
assert [[ZF;;is_natural_number N;;is_plus e N|--x∈N->(∀y,y∈N->∃z,z∈N/\in_rel3 x y z e)]]by FOL_tauto.
universal generalization H7 x. clear H H3 H4 H1 H2 H0 H5 H6 H7.

universal instantiation H8 x.
assert [[ZF;;is_natural_number N;;is_plus e N;;x∈N|--∀y,y∈N->∃z,z∈N/\in_rel3 x y z e]]by FOL_tauto.
universal instantiation H0 y.
assert [[ZF;;is_natural_number N;;is_plus e N|--x∈N/\y∈N->∃z,z∈N/\in_rel3 x y z e]]by FOL_tauto.
universal generalization H2 x y.
The conclusion is already proved.
Qed.

Lemma is_plus_inversion: 
[[ZF;; is_natural_number N;; is_plus e N |-- ∀x, ∀y, ∀z, x∈N /\ y∈N /\ z∈N /\ in_rel3 x y z e ->
 x= ∅ /\ y = z \/ ∃u, ∃v, ∃ w, u∈N/\v∈N/\w∈N/\in_rel3 u v w e /\ x = u ∪ {u} /\ y = v /\ z = w ∪ {w}]].
Proof.
apply separation [[∃f,∀x,x∈f <-> x∈e /\ ¬x=d]].
assert [[ZF;;∀x,x∈f <-> x∈e /\ ¬x=d|--∀x,x∈f <-> x∈e /\ ¬x=d]]by FOL_tauto.
universal instantiation H0 g.

assert [[ZF;;x∈N;;is_triple g ∅ x x;;is_natural_number N;;is_plus e N|--∀ x,x∈N->in_rel3 ∅ x x e]]by FOL_tauto.
universal instantiation H2 x.
assert [[ZF;;x∈N;;is_triple g ∅ x x;;is_natural_number N;;is_plus e N|--∃u,is_triple u ∅ x x/\u∈e]]by FOL_tauto. clear H3 H2.
pose proof triple_injection.
universal instantiation H2 [[∅]] x x u g. clear H2.
apply PEq_sub u g [[g∈e]].
assert [[ZF;;x∈N;;is_triple g ∅ x x;;is_natural_number N;;is_plus e N;;is_triple u ∅ x x/\u∈e|--g∈e]]by FOL_tauto. clear H2 H3.
existential instantiation H5 [[∃u,is_triple u ∅ x x/\u∈e]].
assert [[ZF;;x∈N;;is_triple g ∅ x x;;is_natural_number N;;is_plus e N|--g∈e]]by FOL_tauto. clear H4 H5 H2.
apply PEq_sub g d [[is_triple d ∅ x x]].
pose proof triple_inversion.
universal instantiation H4 a b c [[∅]] x x d. clear H4.
apply PEq_sub x c [[b=c]].
pose proof equal_rev.
universal instantiation H6 c x.
assert [[ZF;;g=d;;is_triple g ∅ x x;;is_triple d a b c|--a=∅/\b=c]] by FOL_tauto. clear H2 H5 H4 H6 H7.
assert [[ZF;;is_triple g ∅ x x;;is_triple d a b c;;¬(a=∅/\b=c)|--¬g=d]]by FOL_tauto. clear H8.
assert [[ZF;;is_natural_number N;;is_plus e N;;a∈N/\b∈N/\c∈N;;is_triple d a b c/\d∈e;;¬(a=∅/\b=c)/\¬(∃u,∃v,∃w, u∈N/\v∈N/\w∈N/\in_rel3 u v w e /\ a=u∪{u}/\b=v/\c=w∪{w});;∀x,x∈f <-> x∈e /\ ¬x=d;;x∈N;;is_triple g ∅ x x|--is_triple g ∅ x x /\ g∈f]]by FOL_tauto. clear H3 H2.
existential generalization H4 [[∃ g,is_triple g ∅ x x/\g∈f]].
assert [[ZF;;is_natural_number N;;is_plus e N;;a∈N/\b∈N/\c∈N;;is_triple d a b c/\d∈e;;¬(a=∅/\b=c)/\¬(∃u,∃v,∃w, u∈N/\v∈N/\w∈N/\in_rel3 u v w e /\ a=u∪{u}/\b=v/\c=w∪{w});;∀x,x∈f <-> x∈e /\ ¬x=d;;x∈N;;is_triple g ∅ x x|--in_rel3 ∅ x x f]]by FOL_tauto. clear H2.
existential instantiation H3 [[∃u, is_triple u ∅ x x]].
pose proof triple_exists.
universal instantiation H5 [[∅]] x x.
assert [[ZF;;is_natural_number N;;is_plus e N;;a∈N/\b∈N/\c∈N;;is_triple d a b c/\d∈e;;¬(a=∅/\b=c)/\¬(∃u,∃v,∃w, u∈N/\v∈N/\w∈N/\in_rel3 u v w e /\ a=u∪{u}/\b=v/\c=w∪{w});;∀x,x∈f <-> x∈e /\ ¬x=d|--x∈N->in_rel3 ∅ x x f]]by FOL_tauto. clear H4 H3 H2 H5 H6.
universal generalization H7 x. clear H7.

assert [[ZF;;is_natural_number N;;is_plus e N;;∀x,x∈f <-> x∈e /\ ¬x=d;;u∈N/\v∈N/\w∈N;;in_rel3 u v w f|--∃g, is_triple g u v w /\ g ∈ f]]by FOL_tauto.
assert [[ZF;;is_natural_number N;;is_plus e N;;∀x,x∈f <-> x∈e /\ ¬x=d;;u∈N/\v∈N/\w∈N;;is_triple g u v w /\ g ∈ f|--is_triple g u v w/\g∈e]]by FOL_tauto.
existential generalization H4 [[∃g,is_triple g u v w/\g∈e]].
assert [[ZF;;is_natural_number N;;is_plus e N;;∀x,x∈f <-> x∈e /\ ¬x=d;;u∈N/\v∈N/\w∈N;;is_triple g u v w /\ g ∈ f|--in_rel3 u v w e]]by FOL_tauto. clear H4 H5.
assert [[ZF;;is_natural_number N;;is_plus e N|--∀ u,∀ v,∀ w, u ∈ N /\ v ∈ N /\ w ∈ N ->( in_rel3 u v w e -> in_rel3 u∪{u} v w∪{w} e)]]by FOL_tauto.
universal instantiation H4 u v w. clear H4.
assert [[ZF;;is_natural_number N;;is_plus e N;;∀x,x∈f <-> x∈e /\ ¬x=d;;u∈N/\v∈N/\w∈N;;is_triple g u v w /\ g ∈ f|--in_rel3 u∪{u} v w∪{w} e]]by FOL_tauto. clear H6 H5.
assert [[ZF;;is_natural_number N;;is_plus e N;;∀x,x∈f <-> x∈e /\ ¬x=d;;u∈N/\v∈N/\w∈N;;is_triple g u v w /\ g ∈ f|--∃X, is_triple X u∪{u} v w∪{w} /\ X∈e]]by FOL_tauto. clear H4.
apply PEq_sub X d [[is_triple d u∪{u} v w∪{w}]].
pose proof triple_inversion.
universal instantiation H6 a b c [[u∪{u}]] v [[w∪{w}]] d. clear H6.
assert [[ZF;;X=d;;is_triple X u∪{u} v w∪{w};;is_triple d a b c|--a=u∪{u}/\b=v/\c=w∪{w}]]by FOL_tauto.
assert [[ZF;;∀ x, x ∈ f <-> x ∈ e /\ ¬ x = d;;is_triple g u v w /\ g ∈ f|--is_triple g u v w/\g∈e]]by FOL_tauto.
existential generalization H8 [[∃g,is_triple g u v w/\g∈e]].
assert [[ZF;;∀ x, x ∈ f <-> x ∈ e /\ ¬ x = d;;is_triple g u v w /\ g ∈ f|--in_rel3 u v w e]]by FOL_tauto. clear H8 H9.
assert [[ZF;;∀ x, x ∈ f <-> x ∈ e /\ ¬ x = d;;is_triple g u v w /\ g ∈ f;;X=d;;is_triple X u∪{u} v w∪{w};;u∈N/\v∈N/\w∈N;;is_triple d a b c|--u∈N/\v∈N/\w∈N/\in_rel3 u v w e/\a=u∪{u}/\b=v/\c=w∪{w}]]by FOL_tauto. clear H4 H7 H6 H10.
existential generalization H8 [[∃u,∃v,∃w,u∈N/\v∈N/\w∈N/\in_rel3 u v w e/\a=u∪{u}/\b=v/\c=w∪{w}]]. clear H8.
assert [[ZF;;∀ x, x ∈ f <-> x ∈ e /\ ¬ x = d;;is_triple g u v w /\ g ∈ f;;is_triple X u∪{u} v w∪{w};;u∈N/\v∈N/\w∈N;;is_triple d a b c;;¬(∃u,∃v,∃w,u∈N/\v∈N/\w∈N/\in_rel3 u v w e/\a=u∪{u}/\b=v/\c=w∪{w})|--¬X=d]]by FOL_tauto. clear H4.
universal instantiation H0 X.
assert [[ZF;;∀ x, x ∈ f <-> x ∈ e /\ ¬ x = d;;is_triple g u v w /\ g ∈ f;;is_triple X u∪{u} v w∪{w}/\X∈e;;u∈N/\v∈N/\w∈N;;is_triple d a b c;;¬(∃u,∃v,∃w,u∈N/\v∈N/\w∈N/\in_rel3 u v w e/\a=u∪{u}/\b=v/\c=w∪{w})|--is_triple X u∪{u} v w∪{w}/\X∈f]]by FOL_tauto. clear H6 H4.
existential generalization H7 [[∃X,is_triple X u∪{u} v w∪{w}/\X∈f]].
assert [[ZF;;∀ x, x ∈ f <-> x ∈ e /\ ¬ x = d;;is_triple g u v w /\ g ∈ f;;is_triple X u∪{u} v w∪{w}/\X∈e;;u∈N/\v∈N/\w∈N;;is_triple d a b c;;¬(∃u,∃v,∃w,u∈N/\v∈N/\w∈N/\in_rel3 u v w e/\a=u∪{u}/\b=v/\c=w∪{w})|--in_rel3 u∪{u} v w∪{w} f]]by FOL_tauto. clear H7 H4.
existential instantiation H6 [[∃X,is_triple X u ∪ {u} v w ∪ {w} /\ X ∈ e]]. clear H6.
assert [[ZF;;is_natural_number N;; is_plus e N;; ∀ x, x ∈ f <-> x ∈ e /\ ¬ x = d;;u ∈ N /\ v ∈ N /\ w ∈ N;; is_triple g u v w /\ g ∈ f;;is_triple d a b c;;¬ (∃ u, ∃ v, ∃ w, u∈N/\v∈N/\w∈N/\in_rel3 u v w e /\ a = u ∪ {u} /\ b = v /\ c = w ∪ {w})|--in_rel3 u∪{u} v w∪{w} f]]by FOL_tauto. clear H5 H4.
existential instantiation H6 [[∃g,is_triple g u v w /\ g ∈ f]]. clear H6.
assert [[ZF;;is_natural_number N;;is_plus e N;;∀ x, x ∈ f <-> x ∈ e /\ ¬ x = d;;u ∈ N /\ v ∈ N /\ w ∈ N;;in_rel3 u v w f;;is_triple d a b c;; ¬ (∃ u, ∃ v, ∃ w, u∈N/\v∈N/\w∈N/\in_rel3 u v w e /\ a = u ∪ {u} /\ b = v /\ c = w ∪ {w})|--in_rel3 u∪{u} v w∪{w} f ]]by FOL_tauto. clear H3 H4.
assert [[ZF;;is_natural_number N;;is_plus e N;;∀ x, x ∈ f <-> x ∈ e /\ ¬ x = d;;is_triple d a b c;; ¬ (∃ u, ∃ v, ∃ w, u∈N/\v∈N/\w∈N/\in_rel3 u v w e /\ a = u ∪ {u} /\ b = v /\ c = w ∪ {w})|--u ∈ N /\ v ∈ N /\ w ∈ N->in_rel3 u v w f->in_rel3 u∪{u} v w∪{w} f]]by FOL_tauto. clear H5.
universal generalization H3 u v w. clear H3.

assert [[ZF;;is_natural_number N;;is_plus e N;;a∈N/\b∈N/\c∈N;;is_triple d a b c/\d∈e;;¬(a=∅/\b=c)/\¬(∃u,∃v,∃w,u∈N/\v∈N/\w∈N/\in_rel3 u v w e/\a=u∪{u}/\b=v/\c=w∪{w});;∀ x, x ∈ f <-> x ∈ e /\ ¬ x = d|--(∀ x, x ∈ N -> in_rel3 ∅ x x f)/\(∀ u,∀ v, ∀ w, u ∈ N /\ v ∈ N /\ w ∈ N -> in_rel3 u v w f -> in_rel3 u ∪ {u} v w ∪ {w} f)]]by FOL_tauto.
assert [[ZF;;is_natural_number N;;is_plus e N;;a∈N/\b∈N/\c∈N;;is_triple d a b c/\d∈e;;¬(a=∅/\b=c)/\¬(∃u,∃v,∃w,u∈N/\v∈N/\w∈N/\in_rel3 u v w e/\a=u∪{u}/\b=v/\c=w∪{w});;∀ x, x ∈ f <-> x ∈ e /\ ¬ x = d|--is_legal_plus f N]]by FOL_tauto. clear H1 H2 H4 H3.

assert [[ZF;;is_plus e N|--∀x,is_legal_plus x N -> e⊆x]]by FOL_tauto.
universal instantiation H1 f. clear H1.
assert [[ZF;;is_plus e N;;is_legal_plus f N|--∀z,z∈e->z∈f]]by FOL_tauto. clear H2.
universal instantiation H1 d. clear H1.
universal instantiation H0 d.
apply PEq_refl d.
assert [[ZF;;∀ x, x ∈ f <-> x ∈ e /\ ¬ x = d|--¬d∈f]]by FOL_tauto. clear H1 H3.
assert [[ZF;;is_plus e N;; is_legal_plus f N;;∀ x, x ∈ f <-> x ∈ e /\ ¬ x = d|--¬d∈e]]by FOL_tauto. clear H2 H4.
assert [[ZF;;is_natural_number N;;is_plus e N;;a∈N/\b∈N/\c∈N;;is_triple d a b c/\d∈e;;∀ x, x ∈ f <-> x ∈ e /\ ¬ x = d|--(a=∅/\b=c)\/(∃u,∃v,∃w,u∈N/\v∈N/\w∈N/\in_rel3 u v w e/\a=u∪{u}/\b=v/\c=w∪{w})]]by FOL_tauto. clear H0 H5 H1.
existential instantiation H2 [[∃f,∀ x, x ∈ f <-> x ∈ e /\ ¬ x = d]].
assert [[ZF;;is_natural_number N;;is_plus e N;;a∈N/\b∈N/\c∈N;;is_triple d a b c/\d∈e|--(a=∅/\b=c)\/(∃u,∃v,∃w,u∈N/\v∈N/\w∈N/\in_rel3 u v w e/\a=u∪{u}/\b=v/\c=w∪{w})]]by FOL_tauto. clear H H2 H0.
existential instantiation H1 [[∃u,is_triple u a b c /\ u ∈ e]].
assert [[ZF;;in_rel3 a b c e|--∃u,is_triple u a b c /\ u ∈ e]]by FOL_tauto.
assert [[ZF;;is_natural_number N;;is_plus e N|--a∈N/\b∈N/\c∈N/\in_rel3 a b c e->(a=∅/\b=c)\/(∃u,∃v,∃w,u∈N/\v∈N/\w∈N/\in_rel3 u v w e/\a=u∪{u}/\b=v/\c=w∪{w})]]by FOL_tauto.
universal generalization H2 a b c.
The conclusion is already proved.
Qed.

Lemma zero_plus_zero_is_zero:
  [[ZF;;is_natural_number N;;is_plus e N|--in_rel3 ∅ ∅ ∅ e]].
Proof.
assert[[ZF;;is_natural_number N;;is_plus e N|--∀ n, n ∈ N -> in_rel3 ∅ n n e]] by FOL_tauto.
universal instantiation H [[∅]].
assert[[ZF;;is_natural_number N|--∅ ∈ N]] by FOL_tauto.
assert[[ZF;;is_natural_number N;;is_plus e N|--in_rel3 ∅ ∅ ∅ e]] by FOL_tauto.
The conclusion is already proved.
Qed.

Lemma one_plus_one_is_two:
  [[ZF;;is_natural_number N;;is_plus e N|--in_rel3 ∅∪{∅} ∅∪{∅} ∅∪{∅}∪{∅∪{∅}} e]].
Proof.
assert[[ZF;;is_natural_number N;;is_plus e N|--∀ n, n ∈ N -> in_rel3 ∅ n n e]] by FOL_tauto.
universal instantiation H [[∅∪{∅}]] .
assert[[ZF;;is_natural_number N;;is_plus e N|--(∀ a,∀ b,∀ c, a ∈ N /\ b ∈ N /\ c ∈ N ->( in_rel3 a b c e -> in_rel3 a∪{a} b c∪{c} e))]] by FOL_tauto.
universal instantiation H1 [[∅]] [[∅∪{∅}]] [[∅∪{∅}]].
pose proof one_in_nat.
assert [[ZF;;is_natural_number N;;is_plus e N|--in_rel3 ∅∪{∅} ∅∪{∅} ∅∪{∅}∪{∅∪{∅}} e]] by FOL_tauto. 
The conclusion is already proved.
Qed.

Lemma one_plus_zero_is_one:
  [[ZF;;is_natural_number N;;is_plus e N|--in_rel3 ∅∪{∅} ∅ ∅∪{∅} e]].
Proof.
pose proof zero_plus_zero_is_zero.
assert [[ZF;;is_natural_number N;;is_plus e N|--(∀ a,∀ b,∀ c, a ∈ N /\ b ∈ N /\ c ∈ N ->( in_rel3 a b c e -> in_rel3 a∪{a} b c∪{c} e))]] by FOL_tauto.
universal instantiation H0 [[∅]] [[∅]] [[∅]].
assert [[ZF;;is_natural_number N;;is_plus e N|--∅ ∈ N]] by FOL_tauto.
assert [[ZF;;is_natural_number N;;is_plus e N|--in_rel3 ∅∪{∅} ∅ ∅∪{∅} e]] by FOL_tauto.
The conclusion is already proved.
Qed.

Lemma zero_plus_one_is_one:
  [[ZF;;is_natural_number N;;is_plus e N|--in_rel3 ∅ ∅∪{∅} ∅∪{∅} e]].
Proof.
assert[[ZF;;is_natural_number N;;is_plus e N|--∀ n, n ∈ N -> in_rel3 ∅ n n e]] by FOL_tauto.
universal instantiation H [[∅∪{∅}]].
pose proof one_in_nat.
assert[[ZF;;is_natural_number N;;is_plus e N|--in_rel3 ∅ ∅∪{∅} ∅∪{∅} e]] by FOL_tauto.
The conclusion is already proved.
Qed.

Lemma one_plus_a_is_a':
  [[ZF;;is_natural_number N;;is_plus e N|--∀a, a∈N -> in_rel3 ∅∪{∅} a a∪{a} e]].
Proof.
assert[[ZF;;is_natural_number N;;is_plus e N|--∀ n, n ∈ N -> in_rel3 ∅ n n e]] by FOL_tauto.
universal instantiation H a.
assert [[ZF;;is_natural_number N;;is_plus e N|--(∀ a,∀ b,∀ c, a ∈ N /\ b ∈ N /\ c ∈ N ->( in_rel3 a b c e -> in_rel3 a∪{a} b c∪{c} e))]] by FOL_tauto.
universal instantiation H1 [[∅]] a a.
assert [[ZF;;is_natural_number N;;is_plus e N|--∅ ∈ N]] by FOL_tauto.
assert [[ZF;; is_natural_number N;; is_plus e N |--a ∈ N -> in_rel3 ∅ ∪ {∅} a a ∪ {a} e]] by FOL_tauto.
universal generalization H4 a.
The conclusion is already proved.
Qed.

Lemma a_plus_one_is_a'_induction0:
  [[ZF;;is_natural_number N;;is_plus e N|--∀b, b∈N /\ in_rel3 b ∅∪{∅} b∪{b} e -> in_rel3 b∪{b} ∅∪{∅} b∪{b}∪{b∪{b}} e]].
Proof.
assert [[ZF;;is_natural_number N;;is_plus e N|--(∀ a,∀ b,∀ c, a ∈ N /\ b ∈ N /\ c ∈ N ->( in_rel3 a b c e -> in_rel3 a∪{a} b c∪{c} e))]] by FOL_tauto.
universal instantiation H b [[∅∪{∅}]] [[b∪{b}]].
pose proof one_in_nat.
assert [[ZF;;is_natural_number N|--∀x, x∈N->x∪{x}∈ N]] by FOL_tauto.
universal instantiation H2 b.
assert [[ZF;; is_natural_number N;; is_plus e N |--b ∈ N ->in_rel3 b ∅ ∪ {∅} b ∪ {b} e -> in_rel3 b ∪ {b} ∅ ∪ {∅} b ∪ {b} ∪ {b ∪ {b}} e]] by FOL_tauto.
assert [[ZF;; is_natural_number N;; is_plus e N |--b ∈ N /\in_rel3 b ∅ ∪ {∅} b ∪ {b} e -> in_rel3 b ∪ {b} ∅ ∪ {∅} b ∪ {b} ∪ {b ∪ {b}} e]] by FOL_tauto.
universal generalization H5 b.
The conclusion is already proved.
Qed.

Lemma a_plus_one_is_a'_induction1:
  [[ZF;;is_natural_number N;;is_plus e N;;∀ x, x ∈ w <-> x ∈ N /\ (in_rel3 x ∅∪{∅} x∪{x} e)|--∅ ∈ w]].
Proof.
assert [[ZF;;∀ x, x ∈ w <-> x ∈ N /\ (in_rel3 x ∅∪{∅} x∪{x} e)|--∀ x, x ∈ w <-> x ∈ N /\ (in_rel3 x ∅∪{∅} x∪{x} e)]] by FOL_tauto.
universal instantiation H [[∅]].
assert [[ZF;;∀ x, x ∈ w <-> x ∈ N /\ (in_rel3 x ∅∪{∅} x∪{x} e)|--∅ ∈ N /\ (in_rel3 ∅ ∅∪{∅} ∅∪{∅} e) -> ∅∈ w]] by FOL_tauto.
pose proof zero_plus_one_is_one.
assert [[ZF;;is_natural_number N;;is_plus e N;;∀ x, x ∈ w <-> x ∈ N /\ (in_rel3 x ∅∪{∅} x∪{x} e)|--∅∈ w]] by FOL_tauto.
The conclusion is already proved.
Qed.

Lemma a_plus_one_is_a'_induction2:
  [[ZF;;is_natural_number N;;is_plus e N;;∀ x, x ∈ w <-> x ∈ N /\ (in_rel3 x ∅∪{∅} x∪{x} e)|--∀b,b∈w->b∪{b}∈w]].
Proof.
assert [[ZF;;∀ x, x ∈ w <-> x ∈ N /\ (in_rel3 x ∅∪{∅} x∪{x} e)|--∀ x, x ∈ w <-> x ∈ N /\ (in_rel3 x ∅∪{∅} x∪{x} e)]] by FOL_tauto.
universal instantiation H b.
assert [[ZF;;is_natural_number N;;is_plus e N;;∀ x, x ∈ w <-> x ∈ N /\ (in_rel3 x ∅∪{∅} x∪{x} e)|--b∈ w -> b ∈ N /\ (in_rel3 b ∅∪{∅} b∪{b} e)]] by FOL_tauto.
universal instantiation H [[b∪{b}]].
assert [[ZF;;is_natural_number N;;is_plus e N;;∀ x, x ∈ w <-> x ∈ N /\ (in_rel3 x ∅∪{∅} x∪{x} e)|--b∪{b} ∈ N /\ (in_rel3 b∪{b} ∅∪{∅} b∪{b}∪{b∪{b}} e) -> b∪{b}∈ w]] by FOL_tauto.
pose proof a_plus_one_is_a'_induction0.
universal instantiation H4 b.
assert [[ZF;;is_natural_number N;; is_plus e N;;∀ x, x ∈ w <-> x ∈ N /\ (in_rel3 x ∅∪{∅} x∪{x} e)|--b∈ w -> b ∈ N /\ (in_rel3 b ∅∪{∅} b∪{b} e)]] by FOL_tauto.
assert [[ZF;;is_natural_number N|--∀ x, x∈ N -> x∪{x} ∈ N]] by FOL_tauto.
universal instantiation H7 b.
assert [[ZF;;is_natural_number N;; is_plus e N |-- b ∈ N /\ in_rel3 b ∅ ∪ {∅} b ∪ {b} e ->b∪{b}∈N /\ in_rel3 b ∪ {b} ∅ ∪ {∅} b ∪ {b} ∪ {b ∪ {b}} e]] by FOL_tauto.
assert [[ZF;;is_natural_number N;; is_plus e N;;∀ x, x ∈ w <-> x ∈ N /\ (in_rel3 x ∅∪{∅} x∪{x} e)|--b∈ w -> b∪{b}∈ w]] by FOL_tauto.
universal generalization H10 b.
The conclusion is already proved.
Qed.

Lemma a_plus_one_is_a':
  [[ZF;;is_natural_number N;;is_plus e N|--∀a, a∈N -> in_rel3 a ∅∪{∅} a∪{a} e]].
Proof.
pose proof mathemetical_induction_2.
assert [[ZF;;is_natural_number N|--∅∈X/\(∀ n, n ∈ X -> n ∪ {n} ∈ X)->∀ n, n ∈ N -> n ∈ X]] by FOL_tauto.
universal generalization H0 X.
universal instantiation H1 w.
pose proof a_plus_one_is_a'_induction2.
universal instantiation H3 n.
universal generalization H4 n. clear H H0 H1 H3 H4.
pose proof a_plus_one_is_a'_induction1.
assert [[ZF;;is_natural_number N;; is_plus e N;;∀ x, x ∈ w <-> x ∈ N /\ in_rel3 x ∅ ∪ {∅} x ∪ {x} e|--∀ n, n ∈ N -> n ∈ w]] by FOL_tauto.
assert [[ZF;;is_natural_number N;; is_plus e N;;∀ x, x ∈ w <-> x ∈ N /\ in_rel3 x ∅ ∪ {∅} x ∪ {x} e|--∀ x, x ∈ w <-> x ∈ N /\ in_rel3 x ∅ ∪ {∅} x ∪ {x} e]]by FOL_tauto.
universal instantiation H1 n.
assert [[ZF;;is_natural_number N;; is_plus e N;;∀ x, x ∈ w <-> x ∈ N /\ in_rel3 x ∅ ∪ {∅} x ∪ {x} e|--n∈w->in_rel3 n ∅ ∪ {∅} n ∪ {n} e]]by FOL_tauto.
universal instantiation H0 n.
assert [[ZF;;is_natural_number N;; is_plus e N;;∀ x, x ∈ w <-> x ∈ N /\ in_rel3 x ∅ ∪ {∅} x ∪ {x} e|--n∈N->in_rel3 n ∅ ∪ {∅} n ∪ {n} e]]by FOL_tauto.
universal generalization H7 n.
existential instantiation H8 [[∃w, ∀ x, x ∈ w <-> x ∈ N /\ in_rel3 x ∅ ∪ {∅} x ∪ {x} e]].
apply separation [[∃ w, ∀ x, x ∈ w <-> x ∈ N /\ (in_rel3 x ∅∪{∅} x∪{x} e)]].
assert [[ZF;;is_natural_number N;;is_plus e N|--∀n, n∈N -> in_rel3 n ∅∪{∅} n∪{n} e]]by FOL_tauto.
universal instantiation H11 a.
universal generalization H12 a.
The conclusion is already proved.
Qed.

Lemma a_plus_zero_is_a_induction0:
  [[ZF;;is_natural_number N;;is_plus e N|--∀b, b∈N /\ in_rel3 b ∅ b e -> in_rel3 b∪{b} ∅ b∪{b} e]].
Proof.
assert [[ZF;;is_natural_number N;;is_plus e N|--(∀ a,∀ b,∀ c, a ∈ N /\ b ∈ N /\ c ∈ N ->( in_rel3 a b c e -> in_rel3 a∪{a} b c∪{c} e))]] by FOL_tauto.
universal instantiation H b [[∅]] b.
assert [[ZF;;is_natural_number N|--∅∈N]] by FOL_tauto.
assert [[ZF;;is_natural_number N|--∀x, x∈N->x∪{x}∈ N]] by FOL_tauto.
universal instantiation H2 b.
assert [[ZF;; is_natural_number N;; is_plus e N |--b ∈ N ->in_rel3 b ∅ b e -> in_rel3 b ∪ {b} ∅  b ∪ {b} e]] by FOL_tauto.
assert [[ZF;; is_natural_number N;; is_plus e N |--b ∈ N /\in_rel3 b ∅ b e -> in_rel3 b ∪ {b} ∅  b ∪ {b} e]] by FOL_tauto.
universal generalization H5 b.
The conclusion is already proved.
Qed.

Lemma a_plus_zero_is_a_induction1:
  [[ZF;;is_natural_number N;;is_plus e N;;∀ x, x ∈ X <-> x ∈ N /\ (in_rel3 x ∅ x e)|--∅ ∈ X]].
Proof.
assert [[ZF;;is_natural_number N;;is_plus e N;;∀ x, x ∈ X <-> x ∈ N /\ (in_rel3 x ∅ x e)|--∀ x, x ∈ X <-> x ∈ N /\ (in_rel3 x ∅ x e)]]by FOL_tauto.
universal instantiation H [[∅]].
assert [[ZF;;is_natural_number N;;is_plus e N;;∀ x, x ∈ X <-> x ∈ N /\ (in_rel3 x ∅ x e)|-- ∅ ∈ N /\ (in_rel3 ∅ ∅ ∅ e) -> ∅ ∈ X]]by FOL_tauto.
pose proof zero_plus_zero_is_zero.
assert [[ZF;;is_natural_number N;;is_plus e N;;∀ x, x ∈ X <-> x ∈ N /\ (in_rel3 x ∅ x e)|-- ∅ ∈ X]]by FOL_tauto.
The conclusion is already proved.
Qed.

Lemma a_plus_zero_is_a_induction2:
  [[ZF;;is_natural_number N;;is_plus e N;;∀ x, x ∈ X <-> x ∈ N /\ (in_rel3 x ∅ x e)|--∀ b, b ∈ X -> b ∪ {b} ∈ X]].
Proof.
assert [[ZF;;∀ x, x ∈ X <-> x ∈ N /\ (in_rel3 x ∅ x e)|--∀ x, x ∈ X <-> x ∈ N /\ (in_rel3 x ∅ x e)]] by FOL_tauto.
universal instantiation H b.
assert [[ZF;;is_natural_number N;;is_plus e N;;∀ x, x ∈ X <-> x ∈ N /\ (in_rel3 x ∅ x e)|--b∈ X -> b ∈ N /\ (in_rel3 b ∅ b e)]] by FOL_tauto.
universal instantiation H [[b∪{b}]].
assert [[ZF;;is_natural_number N;;is_plus e N;;∀ x, x ∈ X <-> x ∈ N /\ (in_rel3 x ∅ x e)|--b∪{b} ∈ N /\ (in_rel3 b∪{b} ∅ b∪{b} e) -> b∪{b}∈ X]] by FOL_tauto.
pose proof a_plus_zero_is_a_induction0.
universal instantiation H4 b.
assert [[ZF;;is_natural_number N;; is_plus e N;;∀ x, x ∈ X <-> x ∈ N /\ (in_rel3 x ∅ x e)|--b∈ X -> b ∈ N /\ (in_rel3 b ∅ b e)]] by FOL_tauto.
assert [[ZF;;is_natural_number N|--∀ x, x∈ N -> x∪{x} ∈ N]] by FOL_tauto.
universal instantiation H7 b.
assert [[ZF;;is_natural_number N;; is_plus e N |-- b ∈ N /\ in_rel3 b ∅ b e ->b∪{b}∈N /\ in_rel3 b ∪ {b} ∅ b ∪ {b} e]] by FOL_tauto.
assert [[ZF;;is_natural_number N;; is_plus e N;;∀ x, x ∈ X <-> x ∈ N /\ (in_rel3 x ∅ x e)|--b∈ X -> b∪{b}∈ X]] by FOL_tauto.
universal generalization H10 b.
The conclusion is already proved.
Qed.

Lemma a_plus_zero_is_a:
  [[ZF;;is_natural_number N;;is_plus e N|--∀a, a∈N -> in_rel3 a ∅ a e]].
Proof.
pose proof mathemetical_induction_2.
pose proof a_plus_zero_is_a_induction2.
universal instantiation H0 n.
universal generalization H1 n.
pose proof a_plus_zero_is_a_induction1.
assert [[ZF;;is_natural_number N;; is_plus e N;;∀ x, x ∈ X <-> x ∈ N /\ in_rel3 x ∅ x e|--∀ n, n ∈ N -> n ∈ X]] by FOL_tauto.
assert [[ZF;;is_natural_number N;; is_plus e N;;∀ x, x ∈ X <-> x ∈ N /\ in_rel3 x ∅ x e|--∀ x, x ∈ X <-> x ∈ N /\ in_rel3 x ∅ x e]]by FOL_tauto.
universal instantiation H5 n.
assert [[ZF;;is_natural_number N;; is_plus e N;;∀ x, x ∈ X <-> x ∈ N /\ in_rel3 x ∅ x e|--n∈X->in_rel3 n ∅  n  e]]by FOL_tauto.
universal instantiation H4 n.
assert [[ZF;;is_natural_number N;; is_plus e N;;∀ x, x ∈ X <-> x ∈ N /\ in_rel3 x ∅ x e|--n∈N->in_rel3 n ∅ n e]]by FOL_tauto.
universal generalization H9 n.
existential instantiation H10 [[∃X, ∀ x, x ∈ X <-> x ∈ N /\ in_rel3 x ∅ x e]].
apply separation [[∃ X, ∀ x, x ∈ X <-> x ∈ N /\ (in_rel3 x ∅ x e)]].
assert [[ZF;;is_natural_number N;;is_plus e N|--∀n, n∈N -> in_rel3 n ∅ n e]]by FOL_tauto.
universal instantiation H13 a.
universal generalization H14 a.
The conclusion is already proved.
Qed.

Lemma plus_func_zero_try0:
  [[ZF;;is_natural_number N;;is_plus e N;;∀z,z∈u <-> z∈e/\(∀x,∀y,x∈ N /\ y∈ N /\ is_triple z ∅ x y -> x = y) |-- ∀ n, n ∈ N -> in_rel3 ∅ n n u]].
Proof.
assert [[ZF;;is_natural_number N;;is_plus e N;;∀z,z∈u <-> z∈e/\(∀x,∀y,x∈ N /\ y∈ N /\ is_triple z ∅ x y -> x = y) |-- ∀z,z∈u <-> z∈e/\(∀x,∀y,x∈ N /\ y∈ N /\ is_triple z ∅ x y -> x = y) ]] by FOL_tauto.
universal instantiation H z.
assert [[ZF;;is_natural_number N;;is_plus e N;;∀z,z∈u <-> z∈e/\(∀x,∀y,x∈ N /\ y∈ N /\ is_triple z ∅ x y -> x = y)|--z ∈ e /\ (∀ x, ∀ y, x ∈ N /\ y ∈ N /\ is_triple z ∅ x y -> x = y)-> z∈u ]] by FOL_tauto.
clear H H0.

assert [[ZF;;is_natural_number N;;is_plus e N|--∀n,n∈N->in_rel3 ∅ n n e]] by FOL_tauto.
universal instantiation H n.
assert [[ZF;;is_natural_number N;;is_plus e N;;n∈N|--∃u, is_triple u ∅ n n /\ u ∈ e]] by FOL_tauto.
clear H H0.

pose proof triple_injection.
universal instantiation H [[∅]] n n u z.
apply PEq_sub u z [[z ∈ e]].
assert [[ZF;;is_triple u ∅ n n /\ u ∈ e;;is_triple z ∅ n n|--z∈e]]by FOL_tauto.
existential instantiation H4 [[∃ u, is_triple u ∅ n n /\ u ∈ e]].
assert [[ZF;;is_natural_number N;;is_plus e N|--n∈N/\is_triple z ∅ n n->z∈e]] by FOL_tauto.

pose proof triple_inversion.
universal instantiation H7 [[∅]] n n.
universal instantiation H8 [[∅]] x y z.
clear H7 H8.
apply PEq_sub n x [[x=y]].
assert [[ZF|--is_triple z ∅ n n /\ is_triple z ∅ x y -> x = y]] by FOL_tauto.
assert [[ZF;;is_triple z ∅ n n|--x∈N/\y∈N/\is_triple z ∅ x y -> x = y]] by FOL_tauto.
universal generalization H10 x y.

assert [[ZF;;is_natural_number N;;is_plus e N;;∀z,z∈u <-> z∈e/\(∀x,∀y,x∈ N /\ y∈ N /\ is_triple z ∅ x y -> x = y);;n∈N;;is_triple z ∅ n n|--is_triple z ∅ n n /\ z ∈ u]] by FOL_tauto.
existential generalization H12 [[∃ z, is_triple z ∅ n n /\ z ∈ u]].
assert [[ZF;;is_natural_number N;;is_plus e N;;∀z,z∈u <-> z∈e/\(∀x,∀y,x∈ N /\ y∈ N /\ is_triple z ∅ x y -> x = y);;n∈N;;is_triple z ∅ n n|--in_rel3 ∅ n n u]] by FOL_tauto.
existential instantiation H14 [[∃ u, is_triple u ∅ n n]].
pose proof triple_exists.
universal instantiation H16 [[∅]] n n. clear H11 H12 H13 H14 H16.
assert [[ZF;;is_natural_number N;;is_plus e N;;∀z,z∈u <-> z∈e/\(∀x,∀y,x∈ N /\ y∈ N /\ is_triple z ∅ x y -> x = y)|--n∈N -> in_rel3 ∅ n n u]] by FOL_tauto.
universal generalization H11 n.
The conclusion is already proved.
Qed.

Lemma plus_func_zero_try1:
  [[ZF;;is_natural_number N;;is_plus e N;;∀z,z∈u <-> z∈e/\(∀x,∀y,x∈ N /\ y∈ N /\ is_triple z ∅ x y -> x = y) |-- ∀ n,∀ d,∀ f, n ∈ N /\ d ∈ N /\ f ∈ N ->( in_rel3 n d f u -> in_rel3 n∪{n} d f∪{f} u) ]].
Proof.
assert [[ZF;;is_natural_number N;;is_plus e N;;∀z,z∈u <-> z∈e/\(∀x,∀y,x∈ N /\ y∈ N /\ is_triple z ∅ x y -> x = y) |-- ∀z,z∈u <-> z∈e/\(∀x,∀y,x∈ N /\ y∈ N /\ is_triple z ∅ x y -> x = y) ]] by FOL_tauto.
universal instantiation H z.
assert [[ZF;;is_natural_number N;;is_plus e N;;∀z,z∈u <-> z∈e/\(∀x,∀y,x∈ N /\ y∈ N /\ is_triple z ∅ x y -> x = y)|--z ∈ e /\ (∀ x, ∀ y, x ∈ N /\ y ∈ N /\ is_triple z ∅ x y -> x = y)-> z∈u ]] by FOL_tauto.
assert [[ZF;;is_natural_number N;;is_plus e N;;∀z,z∈u <-> z∈e/\(∀x,∀y,x∈ N /\ y∈ N /\ is_triple z ∅ x y -> x = y)|--z∈u -> z ∈ e /\ (∀ x, ∀ y, x ∈ N /\ y ∈ N /\ is_triple z ∅ x y -> x = y)]] by FOL_tauto.
clear H H0.

assert [[ZF;;in_rel3 n d f u |-- ∃ z, is_triple z n d f /\ z ∈ u ]] by FOL_tauto.
assert [[ZF;;is_natural_number N;;is_plus e N|--∀ n,∀ d,∀ f, n ∈ N /\ d ∈ N /\ f ∈ N ->( in_rel3 n d f e -> in_rel3 n∪{n} d f∪{f} e)]] by FOL_tauto.
universal instantiation H0 n d f.

pose proof triple_exists.
universal instantiation H4 n d f.
universal instantiation H4 [[n∪{n}]] d [[f∪{f}]].

assert [[ZF;;is_natural_number N;;is_plus e N;;∀z,z∈u <-> z∈e/\(∀x,∀y,x∈ N /\ y∈ N /\ is_triple z ∅ x y -> x = y)|--z∈u -> z∈e]] by FOL_tauto.
assert [[ZF;;is_triple z n d f/\z∈u;;is_natural_number N;;is_plus e N;;∀z,z∈u <-> z∈e/\(∀x,∀y,x∈ N /\ y∈ N /\ is_triple z ∅ x y -> x = y)|--is_triple z n d f/\z∈e]] by FOL_tauto.
existential generalization H8 [[∃v, is_triple v n d f/\v∈e]].
assert [[ZF;;is_triple z n d f/\z∈u;;is_natural_number N;;is_plus e N;;∀z,z∈u <-> z∈e/\(∀x,∀y,x∈ N /\ y∈ N /\ is_triple z ∅ x y -> x = y)|--in_rel3 n d f e]]by FOL_tauto.

assert [[ZF;;is_triple z n d f/\z∈u;;is_natural_number N;;is_plus e N;;∀z,z∈u <-> z∈e/\(∀x,∀y,x∈ N /\ y∈ N /\ is_triple z ∅ x y -> x = y);;n ∈ N /\ d ∈ N /\ f ∈ N|--in_rel3 n ∪ {n} d f ∪ {f} e]]by FOL_tauto.
assert [[ZF;;is_triple z n d f/\z∈u;;is_natural_number N;;is_plus e N;;∀z,z∈u <-> z∈e/\(∀x,∀y,x∈ N /\ y∈ N /\ is_triple z ∅ x y -> x = y);;n ∈ N /\ d ∈ N /\ f ∈ N|--∃v, is_triple v n∪{n} d f∪{f} /\ v ∈ e]]by FOL_tauto.
clear H8 H9 H10 H11.

assert [[ZF;;is_natural_number N;;is_plus e N;;∀z,z∈u <-> z∈e/\(∀x,∀y,x∈ N /\ y∈ N /\ is_triple z ∅ x y -> x = y) |-- ∀z,z∈u <-> z∈e/\(∀x,∀y,x∈ N /\ y∈ N /\ is_triple z ∅ x y -> x = y) ]] by FOL_tauto.
universal instantiation H8 v.
assert [[ZF;;is_natural_number N;;is_plus e N;;∀z,z∈u <-> z∈e/\(∀x,∀y,x∈ N /\ y∈ N /\ is_triple z ∅ x y -> x = y);;is_triple v n∪{n} d f∪{f} /\ v∈e|--v∈e/\(∀x,∀y,x∈ N /\ y∈ N /\ is_triple v ∅ x y -> x = y)->v∈u]]by FOL_tauto.
clear H8 H9.

pose proof not_empty.
universal instantiation H8 n. clear H8.

pose proof triple_inversion.
universal instantiation H8 [[n∪{n}]] d [[f∪{f}]].
universal instantiation H11 [[∅]] x y v.
assert [[ZF;;is_triple v n ∪ {n} d f ∪ {f}|--is_triple v ∅ x y -> n ∪ {n} = ∅]] by FOL_tauto.
clear H8 H11 H13.

assert [[ZF;;is_triple v n ∪ {n} d f ∪ {f}|--¬n ∪ {n} = ∅ -> ¬ is_triple v ∅ x y]] by FOL_tauto.
assert [[ZF;;is_triple v n ∪ {n} d f ∪ {f}|--¬ is_triple v ∅ x y]] by FOL_tauto.
clear H9 H14 H8.
assert [[ZF;;¬ is_triple v ∅ x y|--is_triple v ∅ x y -> x=y]]by FOL_tauto.
assert [[ZF;; is_triple v n ∪ {n} d f ∪ {f} |--is_triple v ∅ x y -> x=y]]by FOL_tauto.
assert [[ZF;; is_triple v n ∪ {n} d f ∪ {f} |--x ∈ N /\ y ∈ N/\is_triple v ∅ x y -> x=y]]by FOL_tauto.
universal generalization H13 x y.
clear H11 H8 H9 H13.

assert [[ZF;;is_natural_number N;;is_plus e N;;∀z,z∈u <-> z∈e/\(∀x,∀y,x∈ N /\ y∈ N /\ is_triple z ∅ x y -> x = y);;is_triple v n ∪ {n} d f ∪ {f}/\v∈e|--v∈u]]by FOL_tauto.
assert [[ZF;;is_natural_number N;;is_plus e N;;∀z,z∈u <-> z∈e/\(∀x,∀y,x∈ N /\ y∈ N /\ is_triple z ∅ x y -> x = y);;is_triple v n ∪ {n} d f ∪ {f}/\v∈e|--is_triple v n ∪ {n} d f ∪ {f} /\ v∈u]]by FOL_tauto.
existential generalization H9 [[∃v, is_triple v n ∪ {n} d f ∪ {f} /\ v∈u]].
assert [[ZF;;is_natural_number N;;is_plus e N;;∀z,z∈u <-> z∈e/\(∀x,∀y,x∈ N /\ y∈ N /\ is_triple z ∅ x y -> x = y);;is_triple v n ∪ {n} d f ∪ {f}/\v∈e|--in_rel3 n ∪ {n} d f ∪ {f} u]]by FOL_tauto.
clear H8 H9 H11.
existential instantiation H13 [[∃v, is_triple v n ∪ {n} d f ∪ {f} /\ v ∈ e]].
clear H14 H13.

assert [[ZF;; is_triple z n d f /\ z ∈ u;; is_natural_number N;; is_plus e N;;
        ∀ z, z ∈ u <-> z ∈ e /\ (∀ x, ∀ y, x ∈ N /\ y ∈ N /\ is_triple z ∅ x y -> x = y);;
        n ∈ N /\ d ∈ N /\ f ∈ N|--in_rel3 n ∪ {n} d f ∪ {f} u]]by FOL_tauto.
clear H10 H8.

assert [[ZF;; is_triple z n d f /\ z ∈ u;; is_natural_number N;; is_plus e N;;
        ∀ z, z ∈ u <-> z ∈ e /\ (∀ x, ∀ y, x ∈ N /\ y ∈ N /\ is_triple z ∅ x y -> x = y);;
        n ∈ N /\ d ∈ N /\ f ∈ N|--in_rel3 n d f u -> in_rel3 n∪{n} d f∪{f} u]]by FOL_tauto.

assert [[ZF;; is_triple z n d f /\ z ∈ u;; is_natural_number N;; is_plus e N;;
        ∀ z, z ∈ u <-> z ∈ e /\ (∀ x, ∀ y, x ∈ N /\ y ∈ N /\ is_triple z ∅ x y -> x = y)|--
        n ∈ N /\ d ∈ N /\ f ∈ N->(in_rel3 n d f u -> in_rel3 n∪{n} d f∪{f} u)]]by FOL_tauto.

existential instantiation H10 [[∃z,is_triple z n d f /\ z ∈ u]].

assert [[ZF;;in_rel3 n d f u|--∃ z, is_triple z n d f /\ z ∈ u]]by FOL_tauto.

assert [[ZF;; is_natural_number N;; is_plus e N;;
        ∀ z, z ∈ u <-> z ∈ e /\ (∀ x, ∀ y, x ∈ N /\ y ∈ N /\ is_triple z ∅ x y -> x = y);; n ∈ N /\ d ∈ N /\ f ∈ N|--
       (in_rel3 n d f u -> in_rel3 n∪{n} d f∪{f} u)]]by FOL_tauto.
clear H10 H11 H13.
assert [[ZF;; is_natural_number N;; is_plus e N;;
        ∀ z, z ∈ u <-> z ∈ e /\ (∀ x, ∀ y, x ∈ N /\ y ∈ N /\ is_triple z ∅ x y -> x = y)|-- n ∈ N /\ d ∈ N /\ f ∈ N->
       (in_rel3 n d f u -> in_rel3 n∪{n} d f∪{f} u)]]by FOL_tauto.
universal generalization H10 n d f.

The conclusion is already proved.
Qed.

Lemma plus_func_zero_try2:
  [[ZF;;is_natural_number N;;is_plus e N;;∀z,z∈u <-> z∈e/\(∀x,∀y,x∈ N /\ y∈ N /\ is_triple z ∅ x y -> x = y) |-- is_legal_plus u N ]].
Proof.
pose proof plus_func_zero_try0.
pose proof plus_func_zero_try1.
assert [[ZF;;is_natural_number N;;is_plus e N;;∀z,z∈u <-> z∈e/\(∀x,∀y,x∈ N /\ y∈ N /\ is_triple z ∅ x y -> x = y) |-- is_legal_plus u N ]] by FOL_tauto.
The conclusion is already proved.
Qed.

Lemma plus_func_zero:
    [[ZF;;is_natural_number N;;is_plus e N|-- ∀x, ∀y,  x ∈ N /\ y ∈ N /\ in_rel3 ∅ x y e -> x = y]].
Proof.
assert [[ZF;;is_natural_number N;;is_plus e N;;∀z,z∈u <-> z∈e/\(∀x,∀y,x∈ N /\ y∈ N /\ is_triple z ∅ x y -> x = y) |--∀ y, is_legal_plus y N -> e ⊆ y ]]by FOL_tauto.
universal instantiation H u.
pose proof plus_func_zero_try2.
assert [[ZF;;is_natural_number N;;is_plus e N;;∀z,z∈u <-> z∈e/\(∀x,∀y,x∈ N /\ y∈ N /\ is_triple z ∅ x y -> x = y) |-- e ⊆ u ]] by FOL_tauto.
assert [[ZF;;is_natural_number N;;is_plus e N;;∀z,z∈u <-> z∈e/\(∀x,∀y,x∈ N /\ y∈ N /\ is_triple z ∅ x y -> x = y) |-- ∀ z, z∈e -> z∈u ]] by FOL_tauto.
universal instantiation H3 z.
assert [[ZF;;is_natural_number N;;is_plus e N;;∀z,z∈u <-> z∈e/\(∀x,∀y,x∈ N /\ y∈ N /\ is_triple z ∅ x y -> x = y)|--(∀ z, z ∈ u <-> z ∈ e /\ (∀ x, ∀ y, x∈N/\y∈N /\ is_triple z ∅ x y -> x = y))]]by FOL_tauto.
universal instantiation H5 z.
assert [[ZF;;is_natural_number N;;is_plus e N;;∀z,z∈u <-> z∈e/\(∀x,∀y,x∈ N /\ y∈ N /\ is_triple z ∅ x y -> x = y)|--z ∈ u -> z ∈ e /\ (∀ x, ∀ y,x∈ N /\ y∈ N /\ is_triple z ∅ x y -> x = y)]]by FOL_tauto.
assert [[ZF;;is_natural_number N;;is_plus e N;;∀z,z∈u <-> z∈e/\(∀x,∀y,x∈ N /\ y∈ N /\ is_triple z ∅ x y -> x = y)|--z ∈ e -> z ∈ e /\ (∀ x, ∀ y,x∈ N /\ y∈ N /\ is_triple z ∅ x y -> x = y)]]by FOL_tauto.
assert [[ZF;;is_natural_number N;;is_plus e N;;∀z,z∈u <-> z∈e/\(∀x,∀y,x∈ N /\ y∈ N /\ is_triple z ∅ x y -> x = y);;z ∈ e|--(∀ x, ∀ y,x∈ N /\ y∈ N /\ is_triple z ∅ x y -> x = y)]]by FOL_tauto.
universal instantiation H9 x y.
assert [[ZF;;is_natural_number N;;is_plus e N;;∀z,z∈u <-> z∈e/\(∀x,∀y,x∈ N /\ y∈ N /\ is_triple z ∅ x y -> x = y)|--z ∈ e /\ x∈ N /\ y∈ N /\ is_triple z ∅ x y -> x = y ]]by FOL_tauto.
assert [[ZF;;is_natural_number N;;is_plus e N;;∀z,z∈u <-> z∈e/\(∀x,∀y,x∈ N /\ y∈ N /\ is_triple z ∅ x y -> x = y);;is_triple z ∅ x y /\ z ∈ e|-- x∈ N /\ y∈ N -> x = y ]]by FOL_tauto.
existential instantiation H12 [[∃u, is_triple u ∅ x y /\ u ∈ e]]. clear H1 H2 H3 H4 H5.
assert [[ZF;;is_natural_number N;;is_plus e N;;∀z,z∈u <-> z∈e/\(∀x,∀y,x∈ N /\ y∈ N /\ is_triple z ∅ x y -> x = y)|--(∃ u, is_triple u ∅ x y /\ u ∈ e) -> x∈ N /\ y∈ N -> x = y ]]by FOL_tauto.
assert [[ZF;;is_natural_number N;;is_plus e N;;∀z,z∈u <-> z∈e/\(∀x,∀y,x∈ N /\ y∈ N /\ is_triple z ∅ x y -> x = y)|--in_rel3 ∅ x y e -> x∈ N /\ y∈ N -> x = y ]]by FOL_tauto.
assert [[ZF;;is_natural_number N;;is_plus e N;;∀z,z∈u <-> z∈e/\(∀x,∀y,x∈ N /\ y∈ N /\ is_triple z ∅ x y -> x = y)|--x∈ N /\ y∈ N /\in_rel3 ∅ x y e -> x = y ]]by FOL_tauto.
universal generalization H3 x y.
existential instantiation H4 [[∃u, ∀z,z∈u <-> z∈e/\(∀x,∀y,x∈ N /\ y∈ N /\ is_triple z ∅ x y -> x = y)]].
apply separation [[∃u,∀z,z∈u <-> z∈e/\(∀x,∀y,x∈ N /\ y∈ N /\ is_triple z ∅ x y -> x = y)]].
assert [[ZF;;is_natural_number N;;is_plus e N|--∀ x, ∀ y, x∈ N /\ y∈ N /\ in_rel3 ∅ x y e -> x = y ]] by FOL_tauto.
The conclusion is already proved.
Qed.

Lemma plus_func_induction:
  [[ZF;;is_natural_number N;;is_plus e N|-- ∀x, x∈ N/\(∀y, ∀z, ∀a, y ∈ N /\ z ∈ N /\ a ∈ N/\in_rel3 x y z e /\ in_rel3 x y a e -> z = a) -> x∪{x}∈N/\(∀y, ∀z, ∀a,  y ∈ N /\ z ∈ N /\ a ∈ N/\in_rel3 x∪{x} y z e /\ in_rel3 x∪{x} y a e -> z = a)]].
Proof.
pose proof is_plus_inversion.
universal instantiation H [[x∪{x}]] y z.
universal instantiation H [[x∪{x}]] y a.
assert [[ZF;;is_natural_number N|--∀x,x∈N->x∪{x}∈N]]by FOL_tauto.
universal instantiation H2 x. clear H2.
pose proof not_empty.
universal instantiation H2 x. clear H2.
assert [[ZF;;is_natural_number N;;is_plus e N;;x∈N/\y∈N/\z∈N/\a∈N;;in_rel3 x∪{x} y z e;;in_rel3 x∪{x} y a e|--(∃ u, ∃ v, ∃ w, u∈N/\v∈N/\w∈N/\in_rel3 u v w e /\ x ∪ {x} = u ∪ {u} /\ y = v /\ z = w ∪ {w})/\(∃ u, ∃ v, ∃ w, u∈N/\v∈N/\w∈N/\in_rel3 u v w e /\ x ∪ {x} = u ∪ {u} /\ y = v /\ a = w ∪ {w})]]by FOL_tauto. clear H H0 H1 H3 H4.

pose proof Sn_inversion.
universal instantiation H x u. clear H.
pose proof equal_rev.
universal instantiation H x u.
universal instantiation H y v. clear H.
apply PEq_sub v y [[in_rel3 u y w e]].
apply PEq_sub u x [[in_rel3 x y w e]].
assert [[ZF;;in_rel3 u v w e /\ x ∪ {x} = u ∪ {u} /\ y = v /\ z = w ∪ {w}|--in_rel3 x y w e]]by FOL_tauto. clear H0 H1 H3 H4 H.

pose proof Sn_inversion.
universal instantiation H x b. clear H.
pose proof equal_rev.
universal instantiation H x b.
universal instantiation H y c. clear H.
apply PEq_sub c y [[in_rel3 b y d e]].
apply PEq_sub b x [[in_rel3 x y d e]].
assert [[ZF;;in_rel3 b c d e /\ x ∪ {x} = b ∪ {b} /\ y = c /\ a = d ∪ {d}|--in_rel3 x y d e]]by FOL_tauto. clear H0 H1 H3 H4 H.

assert [[ZF;;is_natural_number N;;is_plus e N;;∀ y,∀ z,∀ a, y ∈ N /\ z ∈ N /\ a ∈ N /\ in_rel3 x y z e /\ in_rel3 x y a e -> z = a|--∀ y,∀ z,∀ a, y ∈ N /\ z ∈ N /\ a ∈ N /\ in_rel3 x y z e /\ in_rel3 x y a e -> z = a]]by FOL_tauto.
universal instantiation H y w d. clear H.

apply PEq_sub w d [[z=d∪{d}]].
pose proof equal_rev.
universal instantiation H1 a [[d∪{d}]]. clear H1.
apply PEq_sub [[d∪{d}]] a [[z=a]].
assert [[ZF;;z=w∪{w};;a=d∪{d};;w=d|--z=a]]by FOL_tauto. clear H H3 H1.

assert [[ZF;;is_natural_number N;;is_plus e N;;y∈N;;∀y,∀z,∀a,y∈N/\z∈N/\a∈N/\in_rel3 x y z e/\in_rel3 x y a e->z=a;;u∈N/\v∈N/\w∈N/\in_rel3 u v w e/\x∪{x}=u∪{u}/\y=v/\z=w∪{w};;b∈N/\c∈N/\d∈N/\in_rel3 b c d e/\x∪{x}=b∪{b}/\y=c/\a=d∪{d}|--z=a]]by FOL_tauto. clear H5 H6 H0 H4.
existential instantiation H [[∃u,∃v,∃w,u∈N/\v∈N/\w∈N/\in_rel3 u v w e/\x∪{x}=u∪{u}/\y=v/\a=w∪{w}]].
assert [[ZF;;is_natural_number N;;is_plus e N;;y∈N;;∀y,∀z,∀a,y∈N/\z∈N/\a∈N/\in_rel3 x y z e/\in_rel3 x y a e->z=a;;u∈N/\v∈N/\w∈N/\in_rel3 u v w e/\x∪{x}=u∪{u}/\y=v/\z=w∪{w}|--(∃u,∃v,∃w,u∈N/\v∈N/\w∈N/\in_rel3 u v w e/\x∪{x}=u∪{u}/\y=v/\a=w∪{w})->z=a]]by FOL_tauto.
existential instantiation H1 [[∃u,∃v,∃w,u∈N/\v∈N/\w∈N/\in_rel3 u v w e/\x∪{x}=u∪{u}/\y=v/\z=w∪{w}]].
assert [[ZF;;is_natural_number N;;is_plus e N;;x∈N/\y∈N/\z∈N/\a∈N;;in_rel3 x∪{x} y z e;;in_rel3 x∪{x} y a e;;∀y,∀z,∀a,y∈N/\z∈N/\a∈N/\in_rel3 x y z e/\in_rel3 x y a e->z=a|--z=a]]by FOL_tauto. clear H2 H H0 H1 H3.
assert [[ZF;;is_natural_number N;;is_plus e N;;x∈N;;∀y,∀z,∀a,y∈N/\z∈N/\a∈N/\in_rel3 x y z e/\in_rel3 x y a e->z=a|--y∈N/\z∈N/\a∈N/\in_rel3 x∪{x} y z e/\in_rel3 x∪{x} y a e->z=a]]by FOL_tauto.
universal generalization H y z a.
assert [[ZF;;is_natural_number N|--∀x,x∈N->x∪{x}∈N]]by FOL_tauto.
universal instantiation H1 x. clear H1.
assert [[ZF;;is_natural_number N;;is_plus e N|--x∈N/\(∀y,∀z,∀a,y∈N/\z∈N/\a∈N/\in_rel3 x y z e/\in_rel3 x y a e->z=a)->x∪{x}∈N/\(∀y,∀z,∀a,y∈N/\z∈N/\a∈N/\in_rel3 x∪{x} y z e/\in_rel3 x∪{x} y a e->z=a)]]by FOL_tauto.
universal generalization H1 x.
The conclusion is already proved.
Qed.

Lemma plus_func_zero_alter:
  [[ZF;;is_natural_number N;;is_plus e N|--∀y, ∀z, ∀a, y ∈ N /\ z ∈ N /\ a ∈ N/\in_rel3 ∅ y z e /\ in_rel3 ∅ y a e -> z = a]].
Proof.
pose proof plus_func_zero.
universal instantiation H y z.
universal instantiation H y a. clear H.
apply PEq_sub y z [[z=a]].
assert [[ZF;;is_natural_number N;;is_plus e N|--y∈N/\z∈N/\a∈N/\in_rel3 ∅ y z e/\in_rel3 ∅ y a e->z=a]]by FOL_tauto.
universal generalization H2 y z a.
The conclusion is already proved.
Qed.

Lemma plus_func:
  [[ZF;;is_natural_number N;;is_plus e N|-- ∀x, ∀y, ∀z, ∀a, x ∈ N /\ y ∈ N /\ z ∈ N /\ a ∈ N/\in_rel3 x y z e /\ in_rel3 x y a e -> z = a ]].
Proof.
pose proof mathemetical_induction_2.
assert [[ZF;;is_natural_number N;; is_plus e N;;∀ x, x ∈ X <-> x∈N/\(∀y, ∀z, ∀a, y ∈ N /\ z ∈ N /\ a ∈ N/\in_rel3 x y z e /\ in_rel3 x y a e -> z = a)|--∀ x, x ∈ X <-> x∈N/\(∀y, ∀z, ∀a, y ∈ N /\ z ∈ N /\ a ∈ N/\in_rel3 x y z e /\ in_rel3 x y a e -> z = a)]] by FOL_tauto.
universal instantiation H0 [[∅]].
pose proof plus_func_zero_alter.
assert [[ZF;;is_natural_number N;; is_plus e N;;∀ x, x ∈ X <-> x∈N/\(∀y, ∀z, ∀a,  y ∈ N /\ z ∈ N /\ a ∈ N/\in_rel3 x y z e /\ in_rel3 x y a e -> z = a)|--∅ ∈ X]] by FOL_tauto. clear H1 H2.

pose proof plus_func_induction.
universal instantiation H1 n. clear H1.
universal instantiation H0 n.
universal instantiation H0 x.
universal instantiation H0 [[n∪{n}]]. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;∀ x, x ∈ X <-> x∈N/\(∀y, ∀z, ∀a, y ∈ N /\ z ∈ N /\ a ∈ N/\in_rel3 x y z e /\ in_rel3 x y a e -> z = a)|--n∈X->n∪{n}∈X]]by FOL_tauto. clear H2 H1 H5.
universal generalization H0 n. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;∀ x, x ∈ X <-> x∈N/\(∀y, ∀z, ∀a, y ∈ N /\ z ∈ N /\ a ∈ N/\in_rel3 x y z e /\ in_rel3 x y a e -> z = a)|--∀n,n∈N->n∈X]]by FOL_tauto.
universal instantiation H0 x. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;∀ x, x ∈ X <-> x∈N/\(∀y, ∀z, ∀a, y ∈ N /\ z ∈ N /\ a ∈ N/\in_rel3 x y z e /\ in_rel3 x y a e -> z = a)|--x∈N->(∀y, ∀z, ∀a, y ∈ N /\ z ∈ N /\ a ∈ N/\in_rel3 x y z e /\ in_rel3 x y a e -> z = a)]]by FOL_tauto.
existential instantiation H0 [[∃X,∀ x, x ∈ X <-> x∈N/\(∀y, ∀z, ∀a, y ∈ N /\ z ∈ N /\ a ∈ N/\in_rel3 x y z e /\ in_rel3 x y a e -> z = a)]].
apply separation [[∃X,∀ x, x ∈ X <-> x∈N/\(∀y, ∀z, ∀a, y ∈ N /\ z ∈ N /\ a ∈ N/\in_rel3 x y z e /\ in_rel3 x y a e -> z = a)]].
assert [[ZF;;is_natural_number N;;is_plus e N|--x∈N->(∀y, ∀z, ∀a, y ∈ N /\ z ∈ N /\ a ∈ N/\in_rel3 x y z e /\ in_rel3 x y a e -> z = a)]]by FOL_tauto.
universal generalization H7 x. clear H H3 H4 H1 H2 H0 H5 H6 H7.

universal instantiation H8 x.
assert [[ZF;;is_natural_number N;;is_plus e N;;x∈N|--∀y,∀z,∀a,y ∈ N /\ z ∈ N /\ a ∈ N /\ in_rel3 x y z e /\ in_rel3 x y a e -> z = a]]by FOL_tauto.
universal instantiation H0 y z a.
assert [[ZF;;is_natural_number N;;is_plus e N|--x∈N/\y ∈ N /\ z ∈ N /\ a ∈ N /\ in_rel3 x y z e /\ in_rel3 x y a e -> z = a]]by FOL_tauto.
universal generalization H2 x y z a.
The conclusion is already proved.
Qed.

Lemma plus_assoc_zero:
  [[ZF;;is_natural_number N;;is_plus e N|-- ∀y, ∀z, ∀a, ∀b, ∀c,y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\ in_rel3 ∅ y a e /\ in_rel3 a z c e /\ in_rel3 y z b e -> in_rel3 ∅ b c e]].
Proof.
assert [[ZF;;is_natural_number N;;is_plus e N|--∀n, n∈N-> in_rel3 ∅ n n e]] by FOL_tauto.
pose proof plus_func_zero.
universal instantiation H0 y a.
assert [[ZF;; is_natural_number N;; is_plus e N;;y ∈ N /\ a ∈ N /\ in_rel3 ∅ y a e|--y=a]]by FOL_tauto.
assert [[ZF;; is_natural_number N;; is_plus e N;;y ∈ N /\ a ∈ N /\ in_rel3 ∅ y a e/\in_rel3 a z c e|--y=a]]by FOL_tauto.
pose proof equal_rev.
universal instantiation H4 y a.
assert [[ZF;; is_natural_number N;; is_plus e N;;y ∈ N /\ a ∈ N /\ in_rel3 ∅ y a e/\in_rel3 a z c e|--a=y]] by FOL_tauto.
apply PEq_sub a y [[in_rel3 y z c e]].
assert [[ZF;; is_natural_number N;; is_plus e N;;y ∈ N /\ a ∈ N /\ in_rel3 ∅ y a e/\in_rel3 a z c e|--in_rel3 y z c e]]by FOL_tauto.
pose proof plus_func.
universal instantiation H9 y z c b.
clear H0 H1 H2 H3 H4 H5 H6 H7.
assert [[ZF;; is_natural_number N;; is_plus e N;;y ∈ N /\ a ∈ N /\ z ∈ N /\ c ∈ N /\ b ∈ N /\ in_rel3 ∅ y a e/\in_rel3 a z c e/\in_rel3 y z c e/\in_rel3 y z b e|--c = b]]by FOL_tauto.
universal instantiation H c.
apply PEq_sub c b [[in_rel3 ∅ b c e]].
assert [[ZF;;is_natural_number N;;is_plus e N|--y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\ in_rel3 ∅ y a e /\ in_rel3 a z c e /\ in_rel3 y z b e -> in_rel3 ∅ b c e]] by FOL_tauto.
universal generalization H3 y z a b c.
The conclusion is already proved.
Qed.

Lemma plus_assoc_induction:
  [[ZF;;is_natural_number N;;is_plus e N|-- ∀x, x ∈ N /\ (∀y, ∀z, ∀a, ∀b, ∀c, y ∈ N /\ z ∈ N /\ a ∈ N /\ b ∈ N /\ c ∈ N /\ in_rel3 x y a e /\ in_rel3 a z c e /\ in_rel3 y z b e -> in_rel3 x b c e)
 -> x∪{x}∈N/\(∀y, ∀z, ∀a, ∀b, ∀c, y ∈ N /\ z ∈ N /\ a ∈ N /\ b ∈ N /\ c ∈ N /\ in_rel3 x∪{x} y a e /\ in_rel3 a z c e /\ in_rel3 y z b e -> in_rel3 x∪{x} b c e)]].
Proof.
pose proof is_plus_inversion.
universal instantiation H [[x∪{x}]] y a.
pose proof not_empty.
universal instantiation H1 x. clear H1.
assert [[ZF;;is_natural_number N;;is_plus e N;;x∪{x}∈N/\y∈N/\a∈N/\in_rel3 x∪{x} y a e|--∃u,∃v,∃w,u∈N/\v∈N/\w∈N/\in_rel3 u v w e/\x∪{x}=u∪{u}/\y=v/\a=w∪{w}]]by FOL_tauto. clear H0 H2.

universal instantiation H a z c.
pose proof not_empty.
universal instantiation H2 w. clear H2.
pose proof equal_rev.
universal instantiation H2 a [[w∪{w}]]. clear H2.
apply PEq_sub [[w∪{w}]] a [[¬a=∅]].
assert [[ZF;;is_natural_number N;;is_plus e N;;a=w∪{w};;a∈N/\z∈N/\c∈N/\in_rel3 a z c e|--∃u,∃v,∃w,u∈N/\v∈N/\w∈N/\in_rel3 u v w e/\a=u∪{u}/\z=v/\c=w∪{w}]]by FOL_tauto. clear H0 H3 H4 H2.

pose proof Sn_inversion.
universal instantiation H0 x u. clear H0.
pose proof equal_rev.
universal instantiation H0 x u. clear H0.
apply PEq_sub u x [[in_rel3 x v w e]].
pose proof equal_rev.
universal instantiation H4 y v. clear H4.
apply PEq_sub v y [[in_rel3 x y w e]].
assert [[ZF;;is_natural_number N;;is_plus e N;;u∈N/\v∈N/\w∈N/\in_rel3 u v w e/\x∪{x}=u∪{u}/\y=v/\a=w∪{w}|--in_rel3 x y w e]]by FOL_tauto. clear H2 H3 H0 H6 H4.

pose proof Sn_inversion.
universal instantiation H0 w d. clear H0.
apply PEq_sub a [[w∪{w}]] [[w∪{w}=d∪{d}]].
pose proof equal_rev.
universal instantiation H3 w d. clear H3.
apply PEq_sub d w [[in_rel3 w f g e]].
pose proof equal_rev.
universal instantiation H6 z f. clear H6.
apply PEq_sub f z [[in_rel3 w z g e]].
assert [[ZF;;is_natural_number N;;is_plus e N;;d∈N/\f∈N/\g∈N/\in_rel3 d f g e/\a=d∪{d}/\z=f/\c=g∪{g};;a=w∪{w}|--in_rel3 w z g e]]by FOL_tauto. clear H2 H0 H4 H3 H8 H6.

assert [[ZF;;is_natural_number N;;is_plus e N;;x∈N;;∀y,∀z,∀a,∀b,∀c,y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a e/\in_rel3 a z c e/\in_rel3 y z b e->in_rel3 x b c e|--∀y,∀z,∀a,∀b,∀c,y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a e/\in_rel3 a z c e/\in_rel3 y z b e->in_rel3 x b c e]]by FOL_tauto.
universal instantiation H0 y z w b g. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;x∈N;;y∈N/\z∈N/\b∈N;;u∈N/\v∈N/\w∈N/\in_rel3 u v w e/\x∪{x}=u∪{u}/\y=v/\a=w∪{w};;d∈N/\f∈N/\g∈N/\in_rel3 d f g e/\a=d∪{d}/\z=f/\c=g∪{g};;in_rel3 y z b e;;∀y,∀z,∀a,∀b,∀c,y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a e/\in_rel3 a z c e/\in_rel3 y z b e->in_rel3 x b c e|--in_rel3 x b g e]]by FOL_tauto. clear H H7 H9 H2.
assert [[ZF;;is_natural_number N;;is_plus e N|--∀x,∀y,∀z,x∈N/\y∈N/\z∈N -> in_rel3 x y z e -> in_rel3 x∪{x} y z∪{z} e]]by FOL_tauto.
universal instantiation H x b g. clear H.
assert [[ZF;;is_natural_number N;;is_plus e N;;x∈N;;y∈N/\z∈N/\b∈N;;u∈N/\v∈N/\w∈N/\in_rel3 u v w e/\x∪{x}=u∪{u}/\y=v/\a=w∪{w};;d∈N/\f∈N/\g∈N/\in_rel3 d f g e/\a=d∪{d}/\z=f/\c=g∪{g};;in_rel3 y z b e;;∀y,∀z,∀a,∀b,∀c,y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a e/\in_rel3 a z c e/\in_rel3 y z b e->in_rel3 x b c e|--in_rel3 x∪{x} b g∪{g} e]]by FOL_tauto. clear H0 H2.
pose proof equal_rev.
universal instantiation H0 c [[g∪{g}]]. clear H0.
apply PEq_sub [[g∪{g}]] c [[in_rel3 x∪{x} b c e]].
assert [[ZF;;is_natural_number N;;is_plus e N;;x∈N;;y∈N/\z∈N/\b∈N;;u∈N/\v∈N/\w∈N/\in_rel3 u v w e/\x∪{x}=u∪{u}/\y=v/\a=w∪{w};;d∈N/\f∈N/\g∈N/\in_rel3 d f g e/\a=d∪{d}/\z=f/\c=g∪{g};;in_rel3 y z b e;;∀y,∀z,∀a,∀b,∀c,y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a e/\in_rel3 a z c e/\in_rel3 y z b e->in_rel3 x b c e|--in_rel3 x∪{x} b c e]]by FOL_tauto. clear H H2 H0.
existential instantiation H3 [[∃u,∃v,∃w,u∈N/\v∈N/\w∈N/\in_rel3 u v w e/\a=u∪{u}/\z=v/\c=w∪{w}]]. clear H3.
assert [[ZF;;is_natural_number N;;is_plus e N;;x∈N;;y∈N/\z∈N/\a∈N/\b∈N/\c∈N;;u∈N/\v∈N/\w∈N/\in_rel3 u v w e/\x∪{x}=u∪{u}/\y=v/\a=w∪{w};;in_rel3 y z b e/\in_rel3 a z c e;;∀y,∀z,∀a,∀b,∀c,y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a e/\in_rel3 a z c e/\in_rel3 y z b e->in_rel3 x b c e|--in_rel3 x∪{x} b c e]]by FOL_tauto. clear H5 H.
existential instantiation H0 [[∃u,∃v,∃w,u∈N/\v∈N/\w∈N/\in_rel3 u v w e/\x∪{x}=u∪{u}/\y=v/\a=w∪{w}]]. clear H0.
assert [[ZF;;is_natural_number N|--∀x,x∈N->x∪{x}∈N]]by FOL_tauto.
universal instantiation H0 x. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;x∈N;;y∈N/\z∈N/\a∈N/\b∈N/\c∈N;;in_rel3 x∪{x} y a e/\in_rel3 y z b e/\in_rel3 a z c e;;∀y,∀z,∀a,∀b,∀c,y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a e/\in_rel3 a z c e/\in_rel3 y z b e->in_rel3 x b c e|--in_rel3 x∪{x} b c e]]by FOL_tauto. clear H1 H.
assert [[ZF;;is_natural_number N;;is_plus e N;;x∈N;;∀y,∀z,∀a,∀b,∀c,y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a e/\in_rel3 a z c e/\in_rel3 y z b e->in_rel3 x b c e|--y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x∪{x} y a e/\in_rel3 a z c e/\in_rel3 y z b e->in_rel3 x∪{x} b c e]]by FOL_tauto. clear H0.
universal generalization H y z a b c. clear H.
assert [[ZF;;is_natural_number N;;is_plus e N|--x∈N/\(∀y,∀z,∀a,∀b,∀c,y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a e/\in_rel3 a z c e/\in_rel3 y z b e->in_rel3 x b c e)->x∪{x}∈N/\(∀y,∀z,∀a,∀b,∀c,y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x∪{x} y a e/\in_rel3 a z c e/\in_rel3 y z b e->in_rel3 x∪{x} b c e)]]by FOL_tauto.
universal generalization H x.
The conclusion is already proved.
Qed.

Lemma plus_assoc_half: 
  [[ZF;;is_natural_number N;;is_plus e N|-- ∀x, ∀y, ∀z, ∀a, ∀b, ∀c, x ∈ N /\ y ∈ N /\ z ∈ N /\ a ∈ N /\ b ∈ N /\ c ∈ N /\ in_rel3 x y a e /\ in_rel3 a z c e /\ in_rel3 y z b e -> in_rel3 x b c e]].
Proof.
pose proof mathemetical_induction_2.
assert [[ZF;;is_natural_number N;; is_plus e N;;∀ x, x ∈ X <-> x∈N/\(∀y,∀z,∀a,∀b,∀c,y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a e/\in_rel3 a z c e/\in_rel3 y z b e->in_rel3 x b c e)|--∀ x, x ∈ X <-> x∈N/\(∀y,∀z,∀a,∀b,∀c,y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a e/\in_rel3 a z c e/\in_rel3 y z b e->in_rel3 x b c e)]] by FOL_tauto.
universal instantiation H0 [[∅]].
pose proof plus_assoc_zero.
assert [[ZF;;is_natural_number N;; is_plus e N;;∀ x, x ∈ X <-> x∈N/\(∀y,∀z,∀a,∀b,∀c,y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a e/\in_rel3 a z c e/\in_rel3 y z b e->in_rel3 x b c e)|--∅ ∈ X]] by FOL_tauto. clear H1 H2.

pose proof plus_assoc_induction.
universal instantiation H1 n. clear H1.
universal instantiation H0 n.
universal instantiation H0 x.
universal instantiation H0 [[n∪{n}]]. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;∀ x, x ∈ X <-> x∈N/\(∀y,∀z,∀a,∀b,∀c,y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a e/\in_rel3 a z c e/\in_rel3 y z b e->in_rel3 x b c e)|--n∈X->n∪{n}∈X]]by FOL_tauto. clear H2 H1 H5.
universal generalization H0 n. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;∀ x, x ∈ X <-> x∈N/\(∀y,∀z,∀a,∀b,∀c,y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a e/\in_rel3 a z c e/\in_rel3 y z b e->in_rel3 x b c e)|--∀n,n∈N->n∈X]]by FOL_tauto.
universal instantiation H0 x. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;∀ x, x ∈ X <-> x∈N/\(∀y,∀z,∀a,∀b,∀c,y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a e/\in_rel3 a z c e/\in_rel3 y z b e->in_rel3 x b c e)|--x∈N->(∀y,∀z,∀a,∀b,∀c,y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a e/\in_rel3 a z c e/\in_rel3 y z b e->in_rel3 x b c e)]]by FOL_tauto.
existential instantiation H0 [[∃X,∀ x, x ∈ X <-> x∈N/\(∀y,∀z,∀a,∀b,∀c,y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a e/\in_rel3 a z c e/\in_rel3 y z b e->in_rel3 x b c e)]].
apply separation [[∃X,∀ x, x ∈ X <-> x∈N/\(∀y,∀z,∀a,∀b,∀c,y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a e/\in_rel3 a z c e/\in_rel3 y z b e->in_rel3 x b c e)]].
assert [[ZF;;is_natural_number N;;is_plus e N|--x∈N->(∀y,∀z,∀a,∀b,∀c,y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a e/\in_rel3 a z c e/\in_rel3 y z b e->in_rel3 x b c e)]]by FOL_tauto.
universal generalization H7 x. clear H H3 H4 H1 H2 H0 H5 H6 H7.

universal instantiation H8 x.
assert [[ZF;;is_natural_number N;;is_plus e N;;x∈N|--∀y,∀z,∀a,∀b,∀c,y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a e/\in_rel3 a z c e/\in_rel3 y z b e->in_rel3 x b c e]]by FOL_tauto.
universal instantiation H0 y z a b c.
assert [[ZF;;is_natural_number N;;is_plus e N|--x∈N/\y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a e/\in_rel3 a z c e/\in_rel3 y z b e->in_rel3 x b c e]]by FOL_tauto.
universal generalization H2 x y z a b c.
The conclusion is already proved.
Qed.

Lemma Sa_plus_b_is_a_plus_Sb:
  [[ZF;;is_natural_number N;;is_plus e N|--∀a,∀b,∀c,a∈N/\b∈N/\c∈N/\in_rel3 a∪{a} b c e -> in_rel3 a b∪{b} c e]].
Proof.
pose proof plus_assoc_half.
universal instantiation H a [[∅∪{∅}]] b [[a∪{a}]] [[b∪{b}]] c. clear H.
pose proof a_plus_one_is_a'.
universal instantiation H a. clear H.
pose proof one_plus_a_is_a'.
universal instantiation H b. clear H.
assert [[ZF;;is_natural_number N|--∀x,x∈N->x∪{x}∈N]]by FOL_tauto.
universal instantiation H [[∅]].
universal instantiation H a.
universal instantiation H b. clear H.
assert [[ZF;;is_natural_number N;;is_plus e N|--a∈N/\b∈N/\c∈N/\in_rel3 a∪{a} b c e->in_rel3 a b∪{b} c e]]by FOL_tauto. clear H0 H1 H2 H3 H4 H5.
universal generalization H a b c.
The conclusion is already proved.
Qed.

Lemma plus_comm_zero:
  [[ZF;;is_natural_number N;;is_plus e N|-- ∀y, ∀z, y∈N /\ z∈N /\ in_rel3 ∅ y z e -> in_rel3 y ∅ z e]].
Proof.
pose proof plus_func_zero.
universal instantiation H y z. clear H.
pose proof a_plus_zero_is_a.
universal instantiation H y. clear H.
apply PEq_sub y z [[in_rel3 y ∅ z e]].
assert [[ZF;;is_natural_number N;;is_plus e N|--y∈N/\z∈N/\in_rel3 ∅ y z e->in_rel3 y ∅ z e]] by FOL_tauto.
universal generalization H2 y z.
The conclusion is already proved.
Qed.

Lemma plus_comm_induction:
  [[ZF;;is_natural_number N;;is_plus e N|-- ∀x, x∈N /\ (∀y, ∀z, y∈N /\ z∈N /\ in_rel3 x y z e -> in_rel3 y x z e) -> x∪{x}∈N /\ (∀y, ∀z, y∈N /\ z∈N /\ in_rel3 x∪{x} y z e -> in_rel3 y x∪{x} z e)]].
Proof.
pose proof is_plus_inversion.
universal instantiation H [[x∪{x}]] y z. clear H.
pose proof not_empty.
universal instantiation H x. clear H.
assert [[ZF;;is_natural_number N;;is_plus e N;;x∪{x}∈N/\y∈N/\z∈N/\in_rel3 x∪{x} y z e|--∃u,∃v,∃w,u∈N/\v∈N/\w∈N/\in_rel3 u v w e/\x∪{x}=u∪{u}/\y=v/\z=w∪{w}]]by FOL_tauto. clear H0 H1.
pose proof Sn_inversion.
universal instantiation H0 x u. clear H0.
pose proof equal_rev.
universal instantiation H0 x u.
universal instantiation H0 y v. clear H0.
apply PEq_sub u x [[in_rel3 x v w e]].
apply PEq_sub v y [[in_rel3 x y w e]].
assert [[ZF;;is_natural_number N;;is_plus e N;;u∈N/\v∈N/\w∈N/\in_rel3 u v w e/\x∪{x}=u∪{u}/\y=v/\z=w∪{w}|--in_rel3 x y w e]]by FOL_tauto. clear H1 H2 H3 H0 H4.
assert [[ZF;;is_natural_number N;;is_plus e N;;x∈N;;∀y,∀z,y∈N/\z∈N/\in_rel3 x y z e->in_rel3 y x z e|--∀y,∀z,y∈N/\z∈N/\in_rel3 x y z e->in_rel3 y x z e]]by FOL_tauto.
universal instantiation H0 y w. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N|--∀x,∀y,∀z,x∈N/\y∈N/\z∈N->in_rel3 x y z e->in_rel3 x∪{x} y z∪{z} e]]by FOL_tauto.
universal instantiation H0 y x w. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;x∈N;;y∈N;;u∈N/\v∈N/\w∈N/\in_rel3 u v w e/\x∪{x}=u∪{u}/\y=v/\z=w∪{w};;∀y,∀z,y∈N/\z∈N/\in_rel3 x y z e->in_rel3 y x z e|--in_rel3 y∪{y} x w∪{w} e]]by FOL_tauto. clear H5 H1 H2.
pose proof equal_rev.
universal instantiation H1 z [[w∪{w}]]. clear H1.
apply PEq_sub [[w∪{w}]] z [[in_rel3 y∪{y} x z e]].
assert [[ZF;;is_natural_number N;;is_plus e N;;x∈N;;y∈N;;u∈N/\v∈N/\w∈N/\in_rel3 u v w e/\x∪{x}=u∪{u}/\y=v/\z=w∪{w};;∀y,∀z,y∈N/\z∈N/\in_rel3 x y z e->in_rel3 y x z e|--in_rel3 y∪{y} x z e]]by FOL_tauto. clear H0 H2 H1.

pose proof Sa_plus_b_is_a_plus_Sb.
universal instantiation H0 y x z. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;x∈N;;y∈N/\z∈N;;u∈N/\v∈N/\w∈N/\in_rel3 u v w e/\x∪{x}=u∪{u}/\y=v/\z=w∪{w};;∀y,∀z,y∈N/\z∈N/\in_rel3 x y z e->in_rel3 y x z e|--in_rel3 y x∪{x} z e]]by FOL_tauto.
existential instantiation H0 [[∃u,∃v,∃w,u∈N/\v∈N/\w∈N/\in_rel3 u v w e/\x∪{x}=u∪{u}/\y=v/\z=w∪{w}]]. clear H3 H1 H0.
assert [[ZF;;is_natural_number N|--∀x,x∈N->x∪{x}∈N]]by FOL_tauto.
universal instantiation H0 x. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;x∈N;;y∈N/\z∈N/\in_rel3 x∪{x} y z e;;∀y,∀z,y∈N/\z∈N/\in_rel3 x y z e->in_rel3 y x z e|--in_rel3 y x∪{x} z e]]by FOL_tauto. clear H H2.
assert [[ZF;;is_natural_number N;;is_plus e N;;x∈N;;∀y,∀z,y∈N/\z∈N/\in_rel3 x y z e->in_rel3 y x z e|--y∈N/\z∈N/\in_rel3 x∪{x} y z e->in_rel3 y x∪{x} z e]]by FOL_tauto.
universal generalization H y z. clear H.
assert [[ZF;;is_natural_number N;;is_plus e N|--x∈N/\(∀y,∀z,y∈N/\z∈N/\in_rel3 x y z e->in_rel3 y x z e)->x∪{x}∈N/\(∀y,∀z,y∈N/\z∈N/\in_rel3 x∪{x} y z e->in_rel3 y x∪{x} z e)]]by FOL_tauto.
universal generalization H x.
The conclusion is already proved.
Qed.

Lemma plus_comm: 
  [[ZF;;is_natural_number N;;is_plus e N|-- ∀x, ∀y, ∀z, x∈N /\ y∈N /\ z∈N /\ in_rel3 x y z e -> in_rel3 y x z e]].
Proof.
pose proof mathemetical_induction_2.
assert [[ZF;;is_natural_number N;; is_plus e N;;∀ x, x ∈ X <-> x∈N/\(∀y,∀z,y∈N/\z∈N/\in_rel3 x y z e->in_rel3 y x z e)|--∀ x, x ∈ X <-> x∈N/\(∀y,∀z,y∈N/\z∈N/\in_rel3 x y z e->in_rel3 y x z e)]] by FOL_tauto.
universal instantiation H0 [[∅]].
pose proof plus_comm_zero.
assert [[ZF;;is_natural_number N;; is_plus e N;;∀ x, x ∈ X <-> x∈N/\(∀y,∀z,y∈N/\z∈N/\in_rel3 x y z e->in_rel3 y x z e)|--∅ ∈ X]] by FOL_tauto. clear H1 H2.

pose proof plus_comm_induction.
universal instantiation H1 n. clear H1.
universal instantiation H0 n.
universal instantiation H0 x.
universal instantiation H0 [[n∪{n}]]. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;∀ x, x ∈ X <-> x∈N/\(∀y,∀z,y∈N/\z∈N/\in_rel3 x y z e->in_rel3 y x z e)|--n∈X->n∪{n}∈X]]by FOL_tauto. clear H2 H1 H5.
universal generalization H0 n. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;∀ x, x ∈ X <-> x∈N/\(∀y,∀z,y∈N/\z∈N/\in_rel3 x y z e->in_rel3 y x z e)|--∀n,n∈N->n∈X]]by FOL_tauto.
universal instantiation H0 x. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;∀ x, x ∈ X <-> x∈N/\(∀y,∀z,y∈N/\z∈N/\in_rel3 x y z e->in_rel3 y x z e)|--x∈N->(∀y,∀z,y∈N/\z∈N/\in_rel3 x y z e->in_rel3 y x z e)]]by FOL_tauto.
existential instantiation H0 [[∃X,∀ x, x ∈ X <-> x∈N/\(∀y,∀z,y∈N/\z∈N/\in_rel3 x y z e->in_rel3 y x z e)]].
apply separation [[∃X,∀ x, x ∈ X <-> x∈N/\(∀y,∀z,y∈N/\z∈N/\in_rel3 x y z e->in_rel3 y x z e)]].
assert [[ZF;;is_natural_number N;;is_plus e N|--x∈N->(∀y,∀z,y∈N/\z∈N/\in_rel3 x y z e->in_rel3 y x z e)]]by FOL_tauto.
universal generalization H7 x. clear H H3 H4 H1 H2 H0 H5 H6 H7.

universal instantiation H8 x.
assert [[ZF;;is_natural_number N;;is_plus e N;;x∈N|--∀y,∀z,y∈N/\z∈N/\in_rel3 x y z e->in_rel3 y x z e]]by FOL_tauto.
universal instantiation H0 y z.
assert [[ZF;;is_natural_number N;;is_plus e N|--x∈N/\y∈N/\z∈N/\in_rel3 x y z e->in_rel3 y x z e]]by FOL_tauto.
universal generalization H2 x y z.
The conclusion is already proved.
Qed.

Lemma plus_assoc: 
  [[ZF;;is_natural_number N;;is_plus e N|-- ∀x, ∀y, ∀z, ∀a, ∀b, ∀c, x ∈ N /\ y ∈ N /\ z ∈ N /\ a ∈ N /\ b ∈ N /\ c ∈ N /\ in_rel3 x y a e /\ in_rel3 y z b e -> (in_rel3 a z c e <-> in_rel3 x b c e)]].
Proof.
pose proof plus_assoc_half.
universal instantiation H x y z a b c.
assert [[ZF;;is_natural_number N;;is_plus e N;;x∈N/\y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a e/\in_rel3 y z b e|--in_rel3 a z c e -> in_rel3 x b c e]]by FOL_tauto. clear H0.
pose proof plus_comm.
universal instantiation H0 x b c.
universal instantiation H0 y z b.
universal instantiation H0 x y a.
universal instantiation H0 z a c.
universal instantiation H z y x b a c. clear H.
assert [[ZF;;is_natural_number N;;is_plus e N;;x∈N/\y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a e/\in_rel3 y z b e|--in_rel3 x b c e -> in_rel3 a z c e]]by FOL_tauto. clear H0 H2 H3 H4 H5 H6.
assert [[ZF;;is_natural_number N;;is_plus e N|--x∈N/\y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y a e/\in_rel3 y z b e->(in_rel3 a z c e<->in_rel3 x b c e)]]by FOL_tauto.
universal generalization H0 x y z a b c.
The conclusion is already proved.
Qed.

Lemma plus_same_zero:
  [[ZF;;is_natural_number N;;is_plus e N|--∀y,∀z,∀a,∀b,∀c,y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 ∅ y z e/\in_rel3 ∅ a b e/\in_rel3 z a c e->in_rel3 b y c e]].
Proof.
pose proof plus_func_zero.
universal instantiation H y z.
universal instantiation H a b. clear H.
pose proof equal_rev.
universal instantiation H y z. clear H.
apply PEq_sub z y [[in_rel3 y a c e]].
apply PEq_sub a b [[in_rel3 y b c e]].
pose proof plus_comm.
universal instantiation H4 y b c. clear H4.
assert [[ZF;;is_natural_number N;;is_plus e N|--y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 ∅ y z e/\in_rel3 ∅ a b e/\in_rel3 z a c e->in_rel3 b y c e]]by FOL_tauto.
universal generalization H4 y z a b c.
The conclusion is already proved.
Qed.

Lemma plus_same_induction:
  [[ZF;;is_natural_number N;;is_plus e N|--∀x,x∈N/\(∀y,∀z,∀a,∀b,∀c,y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y z e/\in_rel3 x a b e/\in_rel3 z a c e->in_rel3 b y c e)->x∪{x}∈N/\(∀y,∀z,∀a,∀b,∀c,y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x∪{x} y z e/\in_rel3 x∪{x} a b e/\in_rel3 z a c e->in_rel3 b y c e)]].
Proof.
pose proof is_plus_inversion.
universal instantiation H [[x∪{x}]] y z.
universal instantiation H [[x∪{x}]] a b.
universal instantiation H z a c. clear H.
pose proof not_empty.
universal instantiation H x. clear H.
assert [[ZF;;is_natural_number N|--∀x,x∈N->x∪{x}∈N]]by FOL_tauto.
universal instantiation H x. clear H.
assert [[ZF;;is_natural_number N;;is_plus e N;;x∈N/\y∈N/\z∈N/\a∈N/\b∈N/\in_rel3 x∪{x} y z e/\in_rel3 x∪{x} a b e|--(∃u,∃v,∃w,u∈N/\v∈N/\w∈N/\in_rel3 u v w e/\x∪{x}=u∪{u}/\y=v/\z=w∪{w})/\(∃u,∃v,∃w,u∈N/\v∈N/\w∈N/\in_rel3 u v w e/\x∪{x}=u∪{u}/\a=v/\b=w∪{w})]]by FOL_tauto. clear H0 H1 H3.

pose proof Sn_inversion.
universal instantiation H0 x u.
universal instantiation H0 x d. clear H0.
pose proof equal_rev.
universal instantiation H0 x u.
universal instantiation H0 x d.
universal instantiation H0 y v.
universal instantiation H0 a f.
universal instantiation H0 a m. clear H0.
apply PEq_sub u x [[in_rel3 x v w e]].
apply PEq_sub v y [[in_rel3 x y w e]].
assert [[ZF;;in_rel3 u v w e/\x∪{x}=u∪{u}/\y=v|--in_rel3 x y w e]]by FOL_tauto. clear H1 H5 H7 H0 H10.
apply PEq_sub d x [[in_rel3 x f g e]].
apply PEq_sub f a [[in_rel3 x a g e]].
assert [[ZF;;in_rel3 d f g e/\x∪{x}=d∪{d}/\a=f|--in_rel3 x a g e]]by FOL_tauto. clear H3 H6 H8 H0 H1.
apply PEq_sub z [[w∪{w}]] [[w∪{w}=h∪{h}]].
pose proof Sn_inversion.
universal instantiation H1 w h. clear H1.
pose proof equal_rev.
universal instantiation H1 w h. clear H1.
apply PEq_sub h w [[in_rel3 w m n e]].
apply PEq_sub m a [[in_rel3 w a n e]].
assert [[ZF;;in_rel3 h m n e/\z=w∪{w}/\z=h∪{h}/\a=m|--in_rel3 w a n e]]by FOL_tauto. clear H9 H0 H3 H6 H1 H7.
assert [[ZF;;is_natural_number N;;is_plus e N;;x∈N/\(∀y,∀z,∀a,∀b,∀c,y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y z e/\in_rel3 x a b e/\in_rel3 z a c e->in_rel3 b y c e)|--(∀y,∀z,∀a,∀b,∀c,y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y z e/\in_rel3 x a b e/\in_rel3 z a c e->in_rel3 b y c e)]]by FOL_tauto.
universal instantiation H0 y w a g n. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N|--∀x,∀y,∀z,x∈N/\y∈N/\z∈N->in_rel3 x y z e->in_rel3 x∪{x} y z∪{z} e]]by FOL_tauto.
universal instantiation H0 g y n. clear H0.
pose proof equal_rev.
universal instantiation H0 b [[g∪{g}]].
universal instantiation H0 c [[n∪{n}]]. clear H0.
apply PEq_sub [[g∪{g}]] b [[in_rel3 b y n∪{n} e]].
apply PEq_sub [[n∪{n}]] c [[in_rel3 b y c e]].
assert [[ZF;;is_natural_number N;;is_plus e N;;b=g∪{g}/\c=n∪{n};;in_rel3 g∪{g} y n∪{n} e|--in_rel3 b y c e]]by FOL_tauto. clear H6 H7 H0 H9.
assert [[ZF;;is_natural_number N;;is_plus e N;;x∈N/\(∀y,∀z,∀a,∀b,∀c,y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y z e/\in_rel3 x a b e/\in_rel3 z a c e->in_rel3 b y c e);;y∈N/\w∈N/\a∈N/\g∈N/\n∈N/\in_rel3 x y w e/\in_rel3 x a g e/\in_rel3 w a n e;;b=g∪{g}/\c=n∪{n}|--in_rel3 b y c e]]by FOL_tauto. clear H1 H3 H10.
assert [[ZF;;is_natural_number N;;is_plus e N;;x∈N/\(∀y,∀z,∀a,∀b,∀c,y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y z e/\in_rel3 x a b e/\in_rel3 z a c e->in_rel3 b y c e);;x∈N/\y∈N/\z∈N/\a∈N/\b∈N/\c∈N;;u∈N/\v∈N/\w∈N/\in_rel3 u v w e/\x∪{x}=u∪{u}/\y=v/\z=w∪{w};;d∈N/\f∈N/\g∈N/\in_rel3 d f g e/\x∪{x}=d∪{d}/\a=f/\b=g∪{g};;h∈N/\m∈N/\n∈N/\in_rel3 h m n e/\z=h∪{h}/\a=m/\c=n∪{n}|--in_rel3 b y c e]]by FOL_tauto. clear H11 H5 H8 H0.
pose proof not_empty.
universal instantiation H0 w. clear H0.
pose proof equal_rev.
universal instantiation H0 z [[w∪{w}]]. clear H0.
apply PEq_sub [[w∪{w}]] z [[¬z=∅]].
assert [[ZF;;z=w∪{w}|--¬z=∅]]by FOL_tauto. clear H3 H5 H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;z=w∪{w};;z∈N/\a∈N/\c∈N/\in_rel3 z a c e|--∃u,∃v,∃w,u∈N/\v∈N/\w∈N/\in_rel3 u v w e/\z=u∪{u}/\a=v/\c=w∪{w}]]by FOL_tauto. clear H2 H6.
existential instantiation H1 [[∃u,∃v,∃w,u∈N/\v∈N/\w∈N/\in_rel3 u v w e/\z=u∪{u}/\a=v/\c=w∪{w}]]. clear H1.
assert [[ZF;;is_natural_number N;;is_plus e N;;x∈N/\(∀y,∀z,∀a,∀b,∀c,y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y z e/\in_rel3 x a b e/\in_rel3 z a c e->in_rel3 b y c e);;x∈N/\y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 z a c e;;u∈N/\v∈N/\w∈N/\in_rel3 u v w e/\x∪{x}=u∪{u}/\y=v/\z=w∪{w};;d∈N/\f∈N/\g∈N/\in_rel3 d f g e/\x∪{x}=d∪{d}/\a=f/\b=g∪{g}|--in_rel3 b y c e]]by FOL_tauto. clear H0 H2.
existential instantiation H1 [[∃u,∃v,∃w,u∈N/\v∈N/\w∈N/\in_rel3 u v w e/\x∪{x}=u∪{u}/\a=v/\b=w∪{w}]]. clear H1.
assert [[ZF;;is_natural_number N;;is_plus e N;;x∈N/\(∀y,∀z,∀a,∀b,∀c,y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y z e/\in_rel3 x a b e/\in_rel3 z a c e->in_rel3 b y c e);;x∈N/\y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x∪{x} y z e/\in_rel3 x∪{x} a b e/\in_rel3 z a c e;;u∈N/\v∈N/\w∈N/\in_rel3 u v w e/\x∪{x}=u∪{u}/\y=v/\z=w∪{w}|--in_rel3 b y c e]]by FOL_tauto. clear H0.
existential instantiation H1 [[∃u,∃v,∃w,u∈N/\v∈N/\w∈N/\in_rel3 u v w e/\x∪{x}=u∪{u}/\y=v/\z=w∪{w}]]. clear H1.
assert [[ZF;;is_natural_number N;;is_plus e N;;x∈N/\(∀y,∀z,∀a,∀b,∀c,y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y z e/\in_rel3 x a b e/\in_rel3 z a c e->in_rel3 b y c e)|--y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x∪{x} y z e/\in_rel3 x∪{x} a b e/\in_rel3 z a c e->in_rel3 b y c e]]by FOL_tauto. clear H H0.
universal generalization H1 y z a b c. clear H1.
assert [[ZF;;is_natural_number N;;is_plus e N|--x∈N/\(∀y,∀z,∀a,∀b,∀c,y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y z e/\in_rel3 x a b e/\in_rel3 z a c e->in_rel3 b y c e)->x∪{x}∈N/\(∀y,∀z,∀a,∀b,∀c,y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x∪{x} y z e/\in_rel3 x∪{x} a b e/\in_rel3 z a c e->in_rel3 b y c e)]]by FOL_tauto.
universal generalization H0 x.
The conclusion is already proved.
Qed.

Lemma plus_same:
  [[ZF;;is_natural_number N;;is_plus e N|--∀x,∀y,∀z,∀a,∀b,∀c,x∈N/\y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y z e/\in_rel3 x a b e/\in_rel3 z a c e->in_rel3 b y c e]].
Proof.
pose proof mathemetical_induction_2.
assert [[ZF;;is_natural_number N;; is_plus e N;;∀ x, x ∈ X <-> x∈N/\(∀y,∀z,∀a,∀b,∀c,y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y z e/\in_rel3 x a b e/\in_rel3 z a c e->in_rel3 b y c e)|--∀ x, x ∈ X <-> x∈N/\(∀y,∀z,∀a,∀b,∀c,y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y z e/\in_rel3 x a b e/\in_rel3 z a c e->in_rel3 b y c e)]] by FOL_tauto.
universal instantiation H0 [[∅]].
pose proof plus_same_zero.
assert [[ZF;;is_natural_number N;; is_plus e N;;∀ x, x ∈ X <-> x∈N/\(∀y,∀z,∀a,∀b,∀c,y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y z e/\in_rel3 x a b e/\in_rel3 z a c e->in_rel3 b y c e)|--∅ ∈ X]] by FOL_tauto. clear H1 H2.

pose proof plus_same_induction.
universal instantiation H1 n. clear H1.
universal instantiation H0 n.
universal instantiation H0 x.
universal instantiation H0 [[n∪{n}]]. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;∀ x, x ∈ X <-> x∈N/\(∀y,∀z,∀a,∀b,∀c,y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y z e/\in_rel3 x a b e/\in_rel3 z a c e->in_rel3 b y c e)|--n∈X->n∪{n}∈X]]by FOL_tauto. clear H2 H1 H5.
universal generalization H0 n. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;∀ x, x ∈ X <-> x∈N/\(∀y,∀z,∀a,∀b,∀c,y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y z e/\in_rel3 x a b e/\in_rel3 z a c e->in_rel3 b y c e)|--∀n,n∈N->n∈X]]by FOL_tauto.
universal instantiation H0 x. clear H0.
assert [[ZF;;is_natural_number N;;is_plus e N;;∀ x, x ∈ X <-> x∈N/\(∀y,∀z,∀a,∀b,∀c,y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y z e/\in_rel3 x a b e/\in_rel3 z a c e->in_rel3 b y c e)|--x∈N->(∀y,∀z,∀a,∀b,∀c,y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y z e/\in_rel3 x a b e/\in_rel3 z a c e->in_rel3 b y c e)]]by FOL_tauto.
existential instantiation H0 [[∃X,∀ x, x ∈ X <-> x∈N/\(∀y,∀z,∀a,∀b,∀c,y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y z e/\in_rel3 x a b e/\in_rel3 z a c e->in_rel3 b y c e)]].
apply separation [[∃X,∀ x, x ∈ X <-> x∈N/\(∀y,∀z,∀a,∀b,∀c,y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y z e/\in_rel3 x a b e/\in_rel3 z a c e->in_rel3 b y c e)]].
assert [[ZF;;is_natural_number N;;is_plus e N|--x∈N->(∀y,∀z,∀a,∀b,∀c,y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y z e/\in_rel3 x a b e/\in_rel3 z a c e->in_rel3 b y c e)]]by FOL_tauto.
universal generalization H7 x. clear H H3 H4 H1 H2 H0 H5 H6 H7.

universal instantiation H8 x.
assert [[ZF;;is_natural_number N;;is_plus e N;;x∈N|--∀y,∀z,∀a,∀b,∀c,y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y z e/\in_rel3 x a b e/\in_rel3 z a c e->in_rel3 b y c e]]by FOL_tauto.
universal instantiation H0 y z a b c.
assert [[ZF;;is_natural_number N;;is_plus e N|--x∈N/\y∈N/\z∈N/\a∈N/\b∈N/\c∈N/\in_rel3 x y z e/\in_rel3 x a b e/\in_rel3 z a c e->in_rel3 b y c e]]by FOL_tauto.
universal generalization H2 x y z a b c.
The conclusion is already proved.
Qed.