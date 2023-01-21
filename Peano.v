Require Import FV.ZFLib.
Require Import FV.MathmeticalInduction.

Lemma equal_rev:
  [[ZF|--∀ x, ∀ y , x = y -> y = x]].
Proof.
pose proof Extensionality.
universal instantiation H x y.
assert [[ZF;;x=y|--∀ z, z ∈ x <-> z ∈ y]] by FOL_tauto.
universal instantiation H1 z.
assert [[ZF;;x=y|--z ∈ y <-> z ∈ x]] by FOL_tauto.
universal generalization H3 z.
universal instantiation H y x.
assert [[ZF|--x=y->y=x]] by FOL_tauto.
universal generalization H6 x y.
The conclusion is already proved.
Qed.

Lemma subset_subset_equal:
  [[ ZF |-- ∀ x, ∀ y, x ⊆ y -> y ⊆ x -> x = y ]].
Proof.
  pose proof Extensionality.
  universal instantiation H x y.
  assert [[ ZF;; x ⊆ y ;; y ⊆ x |-- ∀ z, z ∈ x -> z ∈ y ]] by FOL_tauto.
  assert [[ ZF;; x ⊆ y ;; y ⊆ x |-- ∀ z, z ∈ y -> z ∈ x ]] by FOL_tauto.
  universal instantiation H1 z.
  universal instantiation H2 z.
  assert [[ ZF;; x ⊆ y ;; y ⊆ x |-- z ∈ x <-> z ∈ y ]] by FOL_tauto.
  universal generalization H5 z.
  assert [[ ZF |-- x ⊆ y -> y ⊆ x -> x = y ]] by FOL_tauto.
  universal generalization H7 x y.
  The conclusion is already proved.
Qed.

Lemma is_singleton_exists: 
[[ZF|-- ∀x, ∃y, is_singleton y x ]].
Proof.
  pose proof Pairing.
  universal instantiation H x x. clear H.
  assert [[ZF;; ∀ u, u ∈ z <-> u = x \/ u = x |-- ∀ u, u ∈ z <-> u = x \/ u = x]] by Tauto.
  universal instantiation H u. clear H.
  assert [[ZF |-- u∈x \/ u ∈x<-> u∈x]] by Tauto.
  assert [[ZF;; ∀ u, u ∈ z <-> u = x \/ u = x |-- u ∈ z <-> u = x ]] by Tauto. clear H H1.
  universal generalization H2 u. clear H2.
  existential generalization H [[∃z, ∀u, u∈ z <-> u = x]]. clear H.
  existential instantiation H1 [[∃ z, ∀ u, u ∈ z <-> u = x \/ u = x]]. clear H1.
  assert [[ZF|-- ∃z, is_singleton z x]] by Tauto. clear H H0.
  universal generalization H1 x. clear H1.
  The conclusion is already proved.
Qed.

Lemma singleton_equivalent:
  [[ZF|--∀ x, ∀ y, is_singleton y x <-> y = {x} ]].
Proof.
assert [[ZF|--is_singleton y x <-> (∀ z, z∈y <-> z = x)]] by FOL_tauto.
pose proof Singleton.
pose proof Extensionality.
universal instantiation H0 x.
universal instantiation H1 [[{x}]] y.
assert [[ZF;;z ∈ y<->z = x;;z ∈ {x}<->z = x|--z∈y<->z∈{x}]] by FOL_tauto.
assert [[ZF;;is_singleton y x |-- ∀ z, z ∈ y <-> z = x]] by FOL_tauto.
universal instantiation H5 z.
universal instantiation H2 z.
assert [[ZF;;is_singleton y x |--z∈y <-> z∈{x} ]] by FOL_tauto.
universal generalization H8 z.
universal instantiation H1 y [[{x}]].
assert [[ZF;;is_singleton y x|--y={x}]] by FOL_tauto.
clear H5 H6 H8 H9.
assert [[ZF;;y={x}|--∀ z, z ∈ y <-> z ∈ {x}]]by FOL_tauto.
universal instantiation H5 z.
assert [[ZF;;y={x}|--z∈y<->z=x]]by FOL_tauto.
universal generalization H8 z.
assert [[ZF;;y={x}|--is_singleton y x]] by FOL_tauto.
assert [[ZF|--is_singleton y x <-> y={x}]] by FOL_tauto.
universal generalization H13 x y.
The conclusion is already proved.
Qed.

Lemma is_singleton_injection:
[[ZF |-- ∀x,∀y,∀z, is_singleton x z -> is_singleton y z -> x = y ]].
Proof.
  assert [[ZF;;is_singleton x z |-- ∀ a, a ∈ x <-> a = z]] by Tauto.
  universal instantiation H a. clear H.
  assert [[ZF;;is_singleton y z |-- ∀ a, a ∈ y <-> a = z]] by Tauto.
  universal instantiation H a. clear H.
  assert [[ZF;; is_singleton x z;; is_singleton y z |-- a ∈ x <-> a ∈ y]] by Tauto.
  universal generalization H a. clear H0 H1 H.
  pose proof Extensionality.
  universal instantiation H x y. clear H.
  assert [[ZF  |-- is_singleton x z -> is_singleton y z -> x = y ]] by Tauto.
  universal generalization H x y z.
  The conclusion is already proved.
Qed.  
  
Lemma is_singleton_inversion: 
[[ZF |-- ∀ x, ∀y, ∀z, is_singleton x y -> is_singleton x z -> y = z]].
Proof.
  assert [[ZF;;is_singleton x y |-- ∀ a, a ∈ x <-> a = y]] by Tauto.
  universal instantiation H a. clear H.
  assert [[ZF;;is_singleton x z |-- ∀ a, a ∈ x <-> a = z]] by Tauto.
  universal instantiation H a. clear H.
  assert [[ZF;;is_singleton x y;; is_singleton x z |--  a = y <-> a=z]] by Tauto.
  universal generalization H a. clear H H0 H1.
  universal instantiation H2 y.
  apply PEq_refl y.
  assert [[ZF|-- is_singleton x y ->  is_singleton x z -> y=z]] by Tauto.
  universal generalization H1 x y z.
  The conclusion is already proved.
Qed.

Lemma has_two_ele_exists: 
[[ZF |-- ∀x, ∀y, ∃ z, has_two_ele z x y]].
Proof.
  pose proof Pairing.
  The conclusion is already proved.
Qed.

Lemma has_two_ele_injection: 
[[ZF |-- ∀ x, ∀ y, ∀ u, ∀ v, has_two_ele x u v -> has_two_ele y u v -> x = y ]].
Proof.
  assert [[ ZF;; has_two_ele x u v |--  ∀ a, a ∈ x <-> a = u \/ a = v]] by Tauto.
  universal instantiation H a. clear H.
  assert [[ ZF;; has_two_ele y u v |--  ∀ a, a ∈ y <-> a = u \/ a = v]] by Tauto.
  universal instantiation H a. clear H.
  assert [[ ZF;; has_two_ele x u v;; has_two_ele y u v |-- a ∈ x <-> a ∈ y ]] by Tauto.
  universal generalization H a. clear H H0 H1.
  pose proof Extensionality.
  universal instantiation H x y. clear H.
  assert [[ ZF |-- has_two_ele x u v -> has_two_ele y u v -> x = y ]] by Tauto. clear H0 H2.
  universal generalization H x y u v.
  The conclusion is already proved.
Qed.  

Lemma has_two_ele_inversion:
 [[ZF |-- ∀x, ∀y, ∀z, ∀u, ∀ v, has_two_ele x y z -> has_two_ele x u v -> y = u /\ z = v \/ y=v /\ z=u ]].
Proof.  
  assert [[ZF;; has_two_ele x y z |-- ∀ a, a ∈ x <-> a= y \/ a= z]] by Tauto.
  universal instantiation H a. clear H.
  assert [[ZF;; has_two_ele x u v |-- ∀ a, a ∈ x <-> a= u \/ a= v]] by Tauto.
  universal instantiation H a. clear H.
  assert [[ZF;; has_two_ele x y z;; has_two_ele x u v |-- a= y \/ a=z <-> a= u \/ a = v]] by Tauto.
  universal generalization H a. clear H H0 H1.
  universal instantiation H2 y.
  apply PEq_refl y.
  assert [[ZF;; has_two_ele x y z;; has_two_ele x u v |-- y = u \/ y = v]] by Tauto.
  clear H H0.
  universal instantiation H2 z.
  apply PEq_refl z.
  assert [[ZF;; has_two_ele x y z;; has_two_ele x u v |-- z = u \/ z = v]] by Tauto.
  clear H H0.
  universal instantiation H2 u.
  apply PEq_refl u.
  assert [[ZF;; has_two_ele x y z;; has_two_ele x u v |-- u = y \/ u = z]] by Tauto.
  clear H H0.
  universal instantiation H2 v.
  apply PEq_refl v.
  assert [[ZF;; has_two_ele x y z;; has_two_ele x u v |-- v = y \/ v = z]] by Tauto.
  clear H H0.
  pose proof equal_rev.
  universal instantiation H v y.
  universal instantiation H v z.
  universal instantiation H u y.
  universal instantiation H u z.
  assert [[ZF |--  has_two_ele x y z -> has_two_ele x u v -> y = u /\ z = v \/ y=v /\ z=u  ]] by Tauto.
  universal generalization H9 x y z u v.
  The conclusion is already proved.
Qed.

Lemma is_pair_exists:
[[ZF |-- ∀x, ∀y, ∃z, is_pair z x y]].
Proof.  
  pose proof is_singleton_exists.
  universal instantiation H y. clear H.
  pose proof has_two_ele_exists. 
  universal instantiation H y z. 
  universal instantiation H y0 z0. clear H.
  assert [[ZF;; is_singleton y0 y;; has_two_ele z0 y z;; has_two_ele g y0 z0 |--  is_singleton y0 y/\ has_two_ele z0 y z/\ has_two_ele g y0 z0 ]] by Tauto.
  existential generalization H [[∃g ,∃ u, ∃ v, is_singleton u y /\ has_two_ele v y z /\ has_two_ele g u v]]. clear H.
  existential instantiation H3 [[∃g, has_two_ele g y0 z0]]. clear H3.
  assert [[ZF;;  is_singleton y0 y;; has_two_ele z0 y z |-- ∃ g, is_pair g y z]] by Tauto. clear H.
  existential instantiation H3 [[∃z0, has_two_ele z0 y z]]. clear H3.
  assert [[ZF;;is_singleton y0 y |-- ∃ g, is_pair g y z]] by Tauto. clear H. 
  existential instantiation H3 [[∃y0, is_singleton y0 y]]. clear H3.
  assert [[ZF |-- ∃ g, is_pair g y z]] by Tauto. clear H H0 H1 H2.
  universal generalization H3 y z.
  The conclusion is already proved.
Qed.

Lemma is_pair_injection: 
[[ZF |-- ∀x, ∀ y, ∀ u, ∀ v, is_pair x u v -> is_pair y u v -> x = y]].
Proof.
  Print is_pair_def.
  assert [[ZF;; is_pair x u v |-- ∃ a, ∃ b, is_singleton a u /\ has_two_ele b u v /\ has_two_ele x a b]] by Tauto.
  assert [[ZF;; is_pair y u v |-- ∃ c, ∃ d, is_singleton c u /\ has_two_ele d u v /\ has_two_ele y c d]] by Tauto.
  pose proof is_singleton_injection.
  universal instantiation H1 a c u.
  pose proof has_two_ele_injection.
  universal instantiation H3 b d u v.
  apply PEq_sub c a [[has_two_ele y a d]].
  apply PEq_sub d b [[has_two_ele y a b]].
  pose proof equal_rev.
  universal instantiation H7 a c. 
  universal instantiation H7 b d.
  clear H7.
  universal instantiation H3 x y a b.
  clear H1 H3.
  assert [[ZF;; is_singleton a u /\ has_two_ele b u v /\ has_two_ele x a b;;
  is_singleton c u /\ has_two_ele d u v /\ has_two_ele y c d |-- x = y]] by Tauto.
  clear H2 H4 H5 H6 H8 H9 H7.
  existential instantiation  H1 [[ ∃ c, ∃ d, is_singleton c u /\ has_two_ele d u v /\ has_two_ele y c d]].
  assert [[ZF;; is_pair y u v;;  is_singleton a u /\ has_two_ele b u v /\ has_two_ele x a b |-- x = y ]] by Tauto.
  existential instantiation  H3 [[ ∃ a, ∃ b, is_singleton a u /\ has_two_ele b u v /\ has_two_ele x a b]].
  assert [[ZF |-- is_pair x u v -> is_pair y u v -> x = y ]] by Tauto.
  universal generalization H5 x y u v.
  The conclusion is already proved.
Qed.
   
Lemma is_singleton_has_two_ele_inversion: 
[[ZF |-- ∀x, ∀y,∀u,∀v, is_singleton x y -> has_two_ele x u v -> y = u /\ y = v]].
Proof.
  assert [[ZF;; is_singleton x y |-- ∀a, a∈x <-> a = y]] by Tauto.
  universal instantiation H a.
  assert [[ZF;; has_two_ele x u v |-- ∀a, a∈x <-> a = u \/ a=v ]] by Tauto.
  universal instantiation H1 a.
  assert [[ZF;; is_singleton x y;; has_two_ele x u v |-- a=y <-> a = u \/ a=v]] by Tauto.
  universal generalization H3 a. clear H H0 H1 H2 H3.
  universal instantiation H4 u.
  apply PEq_refl u.
  assert [[ZF;; is_singleton x y;; has_two_ele x u v |-- u = y]] by Tauto.
  universal instantiation H4 v.
  apply PEq_refl v.
  assert [[ZF;; is_singleton x y;; has_two_ele x u v |-- v = y]] by Tauto.
  pose proof equal_rev.
  universal instantiation H6 v y.
  universal instantiation H6 u y.
  assert [[ZF |-- is_singleton x y -> has_two_ele x u v -> y = u /\ y = v]] by Tauto.
  universal generalization H9 x y u v.
  The conclusion is already proved.
Qed.
   
Lemma is_pair_inversion:
[[ZF|-- ∀x,∀ y, ∀ z, ∀ u,  ∀v, is_pair x y z -> is_pair x u v -> y = u /\ z = v]].
Proof.
  assert [[ZF;; is_pair x y z |--   ∃ a, ∃ b, is_singleton a y /\ has_two_ele b y z /\ has_two_ele x a b ]] by Tauto.
  assert [[ZF;; is_pair x u v |--   ∃ c, ∃ d, is_singleton c u /\ has_two_ele d u v /\ has_two_ele x c d ]] by Tauto.
  pose proof has_two_ele_inversion.
  pose proof is_singleton_inversion. 
  universal instantiation H1 x a b c d. 
  apply PEq_sub c a [[is_singleton a u]].
  pose proof equal_rev.
  universal instantiation H5 a c.
  universal instantiation H2 a y u.
  assert [[ ZF;;is_singleton a y;; is_singleton c u;; a = c |-- y = u]] by Tauto.
  clear H4 H6 H7.
  apply PEq_sub d b [[has_two_ele b u v]].
  universal instantiation H1 b y z u v.
  apply PEq_sub u v [[z=v]].
  apply PEq_sub y u [[u = v]].
  assert [[ ZF;;y = v /\ z = u;; y = u |-- z = v]] by Tauto. clear H7 H9.
  universal instantiation H5 b d.
  assert [[ZF;; is_singleton a y;; is_singleton c u;; a=c /\ b=d;; has_two_ele b y z;; has_two_ele d u v |-- y = u /\ z = v]] by Tauto.
  clear H1 H2 H8 H4 H6 H10 H7.
  apply PEq_sub d a [[has_two_ele a u v]].
  universal instantiation H5 a d.
  pose proof is_singleton_has_two_ele_inversion.
  universal instantiation H4 a y u v.
  apply PEq_sub c b [[is_singleton b u]].
  universal instantiation H5 b c.
  universal instantiation H4 b u y z.
  apply PEq_sub u v [[z=v]].
  apply PEq_sub y u [[u=v]].
  universal instantiation H5 u z.
  assert [[ ZF;; y=u ;; u=z;; y = v |-- z=v ]] by Tauto.
  clear H4 H11 H12 H13.
  assert [[ZF;; is_singleton a y;; is_singleton c u;; a=d /\ b=c;; has_two_ele b y z;; has_two_ele d u v |-- y = u /\ z = v]] by Tauto.
  clear H1 H2 H5 H6 H7 H8 H10 H14.
  assert [[ZF;;  is_singleton a y /\ has_two_ele b y z /\ has_two_ele x a b;; 
   is_singleton c u /\ has_two_ele d u v /\ has_two_ele x c d |-- y = u /\ z = v]] by Tauto.
   clear H3 H4 H9.
   existential instantiation H1 [[∃ c, ∃ d, is_singleton c u /\ has_two_ele d u v /\ has_two_ele x c d]]. clear H1.
   assert [[ZF;;  is_pair x u v;; is_singleton a y /\ has_two_ele b y z /\ has_two_ele x a b |-- y = u /\ z = v]] by Tauto.
   existential instantiation H1 [[∃ a, ∃ b, is_singleton a y /\ has_two_ele b y z /\ has_two_ele x a b]]. clear H0 H1 H2.
   assert [[ZF |-- is_pair x y z -> is_pair x u v -> y = u /\ z = v]] by Tauto.
  universal generalization H0 x y z u v.
  The conclusion is already proved.
Qed.
  

Lemma triple_exists:
[[ZF |-- ∀x, ∀y,∀z, ∃u, is_triple u x y z]].
Proof.
  pose proof is_pair_exists.
  universal instantiation H x y.
  assert [[ZF|-- ∃a, is_pair a x y]] by Tauto. clear H0.
  universal instantiation H a z. clear H.
  assert [[ZF|-- ∃b, is_pair b a z]] by Tauto. clear H0.
  assert [[ZF;; is_pair a x y;; is_pair b a z |-- is_pair a x y /\ is_pair b a z ]] by Tauto.
  existential generalization H0 [[∃b, ∃a, is_pair a x y /\ is_pair b a z]]. clear H0.
  existential instantiation H2 [[∃b, is_pair b a z]]. clear H2.
  assert [[ZF;; is_pair a x y |-- ∃b, is_triple b x y z]] by Tauto. clear H0.
  existential instantiation H2 [[∃a, is_pair a x y]]. 
  assert [[ZF|-- ∃b, is_triple b x y z]] by Tauto. clear H H0 H1 H2.
  universal generalization H3 x y z.
  The conclusion is already proved.
Qed.  

Lemma triple_injection:
  [[ZF|--∀ x, ∀ y, ∀ z, ∀ a, ∀ b, is_triple a x y z /\ is_triple b x y z -> a = b ]].
Proof.
assert [[ZF;;is_triple a x y z |-- ∃ u , is_pair u x y /\ is_pair a u z]] by FOL_tauto.
assert [[ZF;;is_triple b x y z |-- ∃ v , is_pair v x y /\ is_pair b v z]] by FOL_tauto.
pose proof is_pair_injection.
universal instantiation H1 u v x y.
apply PEq_sub u v [[is_pair a v z]].
universal instantiation H1 a b v z.
assert [[ZF;;is_pair u x y /\ is_pair a u z;;is_pair v x y /\ is_pair b v z|--a=b]]by FOL_tauto.
existential instantiation H5 [[∃ v, is_pair v x y /\ is_pair b v z]].
assert [[ZF;;∃ v,is_pair v x y /\ is_pair b v z;;is_pair u x y /\ is_pair a u z|--a=b]]by FOL_tauto.
existential instantiation H7 [[∃ u, is_pair u x y /\ is_pair a u z]].
assert [[ZF|--is_triple a x y z /\ is_triple b x y z -> a = b]]by FOL_tauto.
universal generalization H9 x y z a b.
The conclusion is already proved.
Qed.

Lemma triple_inversion:
  [[ZF|--∀ x, ∀ y, ∀ z, ∀ a, ∀ b, ∀ c, ∀ u, is_triple u x y z /\ is_triple u a b c -> x = a /\ y = b /\ z = c ]].
Proof.
pose proof is_pair_inversion.
assert [[ZF;;is_triple u x y z|--∃ X, is_pair X x y /\ is_pair u X z]] by FOL_tauto.
assert [[ZF;;is_triple u a b c|--∃ Y, is_pair Y a b /\ is_pair u Y c]] by FOL_tauto.
universal instantiation H u X z Y c.
apply PEq_sub Y X [[is_pair X a b]].
pose proof equal_rev.
universal instantiation H4 X Y.
universal instantiation H X x y a b.
assert [[ZF;;is_pair X x y /\ is_pair u X z;;is_pair Y a b /\ is_pair u Y c|--x = a /\ y = b /\ z = c]] by FOL_tauto.
existential instantiation H7 [[∃ Y, is_pair Y a b /\ is_pair u Y c]].
assert [[ZF;;is_pair X x y /\ is_pair u X z|--(∃ Y, is_pair Y a b /\ is_pair u Y c) -> x = a /\ y = b /\ z = c]] by FOL_tauto.
existential instantiation H9 [[∃ X, is_pair X x y /\ is_pair u X z]].
assert [[ZF|--is_triple u x y z /\ is_triple u a b c -> x = a /\ y = b /\ z = c]] by FOL_tauto.
universal generalization H11 a b c u.
universal generalization H12 x y z.
The conclusion is already proved.
Qed.

Lemma natural_number_inversion: 
[[ZF;; is_natural_number N |-- ∀ x, x ∈ N -> x= ∅ \/ ∃ y, y∈N /\ x= y ∪ {y}]].
Proof.
  apply separation  [[∃u, ∀x, x∈u <-> x∈N /\ (x=∅ \/ ∃y,  y∈N /\  x = y ∪ {y})]].
  apply PEq_refl empty_set.
  assert [[ZF |-- ∅=∅ \/ ∃y,  y∈N /\  ∅ = y ∪ {y}]] by Tauto. clear H0.
  assert [[ZF;; ∀ x, x ∈ u <-> x ∈ N /\ (x = ∅ \/ (∃ y, y ∈ N /\ x = y ∪ {y}))|--
  ∀ x, x ∈ u <-> x ∈ N /\ (x = ∅ \/ (∃ y, y ∈ N /\ x = y ∪ {y})) ]] by Tauto.
  universal instantiation H0 [[∅]]. 
  assert [[ZF;; ∀ x, x ∈ u <-> x ∈ N /\ (x = ∅ \/ (∃ y, y ∈ N /\ x = y ∪ {y}));; is_natural_number N|--
  ∅ ∈ u ]] by Tauto. clear H1 H2.
  
  universal instantiation H0 [[x∪{x}]]. 
  assert [[ZF;; is_natural_number N |-- ∀x, x∈ N -> x ∪ {x}∈ N]] by Tauto.
  universal instantiation H2 x. clear H2.
  apply PEq_refl [[x∪{x}]].
  assert [[ZF;; x∈N |-- x ∈ N /\ x ∪ {x} = x∪{x} ]] by Tauto. clear H2.
  existential generalization H5 [[∃ y, y ∈ N /\ x ∪ {x} = y ∪ {y}]]. clear H5.
  assert [[ZF;; is_natural_number N;; x∈ N;; ∀ x, x ∈ u <-> x ∈ N /\ (x = ∅ \/ (∃ y, y ∈ N /\ x = y ∪ {y})) 
   |--  x ∪ {x} ∈u]] by Tauto. clear H1 H2 H4.
   
  universal instantiation H0 x. 
  assert [[ZF;; ∀ x, x ∈ u <-> x ∈ N /\ (x = ∅ \/ (∃ y, y ∈ N /\ x = y ∪ {y}));; is_natural_number N
     |-- x∈u -> x∪{x}∈ u]] by Tauto. clear H1.
  universal generalization H2 x. clear H2.
  assert [[ZF;; ∀ x, x ∈ u <-> x ∈ N /\ (x = ∅ \/ (∃ y, y ∈ N /\ x = y ∪ {y}));; is_natural_number N |--
       is_inductive u]] by Tauto. clear H1 H3 H5.
       
  
  assert [[ZF;; is_natural_number N |-- ∀ x, is_inductive x -> N ⊆ x]] by Tauto.
  universal instantiation H1 u. clear H1.
  assert [[ZF;; ∀ x, x ∈ u <-> x ∈ N /\ (x = ∅ \/ (∃ y, y ∈ N /\ x = y ∪ {y}));; is_natural_number N |--
             N ⊆ u]] by Tauto. clear H2 H3.
             
  universal instantiation H0 x. clear H0.
  assert [[ZF;; N⊆ u|-- ∀ x, x∈ N -> x∈ u]] by Tauto.
  universal instantiation H0 x. clear H0.
  assert [[ZF;; N⊆u ;; ∀ x, x ∈ u <-> x ∈ N /\ (x = ∅ \/ (∃ y, y ∈ N /\ x = y ∪ {y}))  |--
  x∈ N ->  x = ∅ \/ (∃ y, y ∈ N /\ x = y ∪ {y})]] by Tauto. clear  H2 H3.
  universal generalization H0 x. clear H0.
  assert [[ZF;; ∀ x, x ∈ u <-> x ∈ N /\ (x = ∅ \/ (∃ y, y ∈ N /\ x = y ∪ {y}));; is_natural_number N |--
  ∀ x, x ∈ N -> x = ∅ \/ (∃ y, y ∈ N /\ x = y ∪ {y}) ]] by Tauto. clear H1 H2.
  existential instantiation H0  [[∃ u, ∀ x, x ∈ u <-> x ∈ N /\ (x = ∅ \/ (∃ y, y ∈ N /\ x = y ∪ {y}))]].  clear H0. 
  The conclusion is already proved.
Qed.

Lemma not_empty:
  [[ZF|--∀n, ¬n∪{n}=∅]].
Proof.
pose proof Singleton.
universal instantiation H n n.
apply PEq_refl n.
assert [[ZF|--n ∈ {n} ]] by FOL_tauto.
pose proof Empty.
assert [[ZF|--∀ x, ¬ x ∈ ∅ ]] by FOL_tauto.
universal instantiation H4 n.

pose proof Extensionality.
universal instantiation H6 [[n∪{n}]] [[∅]].
assert [[ZF;;n ∪ {n} = ∅|--∀z, z∈n∪{n} <-> z∈∅]]by FOL_tauto.
universal instantiation H8 n.
assert [[ZF|--n∪{n}=∅->n∈n∪{n}-> n∈∅]]by FOL_tauto.
assert [[ZF|--¬ n∪{n}=∅ \/ ¬n∈n∪{n} \/ n∈∅]]by FOL_tauto.
assert [[ZF|--¬ n∪{n}=∅ \/ ¬n∈n∪{n}]]by FOL_tauto.

pose proof Union.
universal instantiation H13 n [[{n}]] n.
clear H H0 H1 H3 H4 H6 H7 H8.
assert [[ZF|-- n∈n∪{n} ]]by FOL_tauto.

assert [[ZF|--¬ n∪{n}=∅]]by FOL_tauto.
universal generalization H0 n.
The conclusion is already proved.
Qed.

Lemma one_in_nat:
  [[ZF;;is_natural_number N|--∅∪{∅}∈N]].
Proof.
assert [[ZF;;is_natural_number N|--∀ x, x ∈ N -> x∪{x} ∈ N]] by FOL_tauto.
universal instantiation H [[∅]].
assert [[ZF;;is_natural_number N|--∅∈N]] by FOL_tauto.
The conclusion is already proved.
Qed.

Lemma two_in_nat:
  [[ZF;;is_natural_number N|--∅∪{∅}∪{∅∪{∅}}∈N]].
Proof.
assert [[ZF;;is_natural_number N|--∀ x, x ∈ N -> x∪{x} ∈ N]] by FOL_tauto.
universal instantiation H [[∅∪{∅}]].
pose proof one_in_nat.
The conclusion is already proved.
Qed.

Lemma equal_zero_exists:
  [[ZF|--∃x,x=∅]].
Proof.
apply PEq_refl [[∅]].
existential generalization H [[∃x,x=∅]].
The conclusion is already proved.
Qed.

Lemma singleton_not_empty:
  [[ZF|--∀x,¬is_empty {x}]].
Proof.
pose proof Singleton.
universal instantiation H x x.
apply PEq_refl x.
assert [[ZF|--x∈{x}]]by FOL_tauto.
assert [[ZF;;is_empty {x}|--∀z,¬z∈{x}]]by FOL_tauto.
universal instantiation H3 x.
assert [[ZF|--¬is_empty {x}]]by FOL_tauto.
universal generalization H5 x.
The conclusion is already proved.
Qed.

Lemma x_not_in_x:
  [[ZF|--∀x,¬x∈x]].
Proof.
pose proof singleton_not_empty.
universal instantiation H x. clear H.
pose proof Regularity.
universal instantiation H [[{x}]]. clear H.
pose proof Singleton.
universal instantiation H x y.
universal instantiation H x x. clear H.
assert [[ZF;;y∈{x};;∀z,z∈{x}->¬z∈y|--∀z,z∈{x}->¬z∈y]]by FOL_tauto.
universal instantiation H x. clear H.
apply PEq_refl x.
apply PEq_sub using condition y x [[¬x∈y]].
assert [[ZF;;y∈{x}/\(∀z,z∈{x}->¬z∈y)|--¬x∈x]]by FOL_tauto.
existential instantiation H6 [[∃y,y∈{x}/\(∀z,z∈{x}->¬z∈y)]].
assert [[ZF|--¬x∈x]]by FOL_tauto.
universal generalization H8 x.
The conclusion is already proved.
Qed.

Lemma no_mutual_belong:
  [[ZF|--∀x,∀y,¬(x∈y/\y∈x)]].
Proof.
pose proof Pairing.
universal instantiation H x y. clear H.
assert [[ZF;;∀u,u∈a<->u=x\/u=y|--∀u,u∈a<->u=x\/u=y]]by FOL_tauto.
universal instantiation H x.
universal instantiation H y.
apply PEq_refl x.
apply PEq_refl y.
assert [[ZF;;∀u,u∈a<->u=x\/u=y|--x∈a/\y∈a]]by FOL_tauto. clear H1 H2 H3 H4.
assert [[ZF;;is_empty a|--∀x,¬x∈a]]by FOL_tauto.
universal instantiation H1 x. clear H1.
assert [[ZF;;∀u,u∈a<->u=x\/u=y|--¬is_empty a /\ x∈a /\ y∈a]]by FOL_tauto. clear H5 H2.

pose proof Regularity.
universal instantiation H2 a. clear H2.
universal instantiation H c. clear H.
assert [[ZF;;∀u,u∈a<->u=x\/u=y;;c∈a/\(∀z,z∈a->¬z∈c)|--c=x\/c=y]]by FOL_tauto. clear H2.
assert [[ZF;;∀u,u∈a<->u=x\/u=y;;c∈a/\(∀z,z∈a->¬z∈c);;c=x|--∀z,z∈a->¬z∈c]]by FOL_tauto.
universal instantiation H2 y.
apply PEq_sub c x [[¬y∈x]].
assert [[ZF;;∀u,u∈a<->u=x\/u=y;;c∈a/\(∀z,z∈a->¬z∈c);;c=x|--¬y∈x]]by FOL_tauto. clear H2 H4 H5.
assert [[ZF;;∀u,u∈a<->u=x\/u=y;;c∈a/\(∀z,z∈a->¬z∈c);;c=y|--∀z,z∈a->¬z∈c]]by FOL_tauto.
universal instantiation H2 x.
apply PEq_sub c y [[¬x∈y]].
assert [[ZF;;∀u,u∈a<->u=x\/u=y;;c∈a/\(∀z,z∈a->¬z∈c);;c=y|--¬x∈y]]by FOL_tauto. clear H2 H4 H5.
assert [[ZF;;∀u,u∈a<->u=x\/u=y;;c∈a/\(∀z,z∈a->¬z∈c)|--¬x∈y\/¬y∈x]]by FOL_tauto. clear H H6 H7.
existential instantiation H2 [[∃y,y∈a/\(∀z,z∈a->¬z∈y)]].
assert [[ZF;;∀u,u∈a<->u=x\/u=y|--¬x∈y\/¬y∈x]]by FOL_tauto.
existential instantiation H4 [[∃z,∀u,u∈z<->u=x\/u=y]].
assert [[ZF|--¬(x∈y/\y∈x)]]by FOL_tauto.
universal generalization H6 x y.
The conclusion is already proved.
Qed.

Lemma Sn_inversion:
  [[ZF|--∀x,∀y, x∪{x}=y∪{y}->x=y]].
Proof.
pose proof Union.
universal instantiation H x [[{x}]] x.
universal instantiation H y [[{y}]] y. clear H.
pose proof Singleton.
universal instantiation H x x.
universal instantiation H y y. clear H.
apply PEq_refl x.
apply PEq_refl y.
assert [[ZF|--x∈x∪{x}/\y∈y∪{y}]]by FOL_tauto. clear H0 H1 H2 H3 H H4.
apply PEq_sub [[x∪{x}]] [[y∪{y}]] [[x∈y∪{y}]].
pose proof equal_rev.
universal instantiation H0 [[x∪{x}]] [[y∪{y}]]. clear H0.
apply PEq_sub [[y∪{y}]] [[x∪{x}]] [[y∈x∪{x}]].
assert [[ZF;;x∪{x}=y∪{y}|--y∈x∪{x}/\x∈y∪{y}]]by FOL_tauto. clear H5 H H1 H0.
pose proof Union.
universal instantiation H x [[{x}]] y.
universal instantiation H y [[{y}]] x. clear H.
assert [[ZF;;x∪{x}=y∪{y}|--(y∈x\/y∈{x})/\(x∈y\/x∈{y})]]by FOL_tauto. clear H2 H0 H1.
assert [[ZF;;x∪{x}=y∪{y}|--(y∈x/\x∈y)\/(y∈x/\x∈{y})\/(y∈{x}/\x∈y)\/(y∈{x}/\x∈{y})]]by FOL_tauto. clear H.

pose proof no_mutual_belong.
universal instantiation H y x. clear H.

pose proof Singleton.
universal instantiation H y x. clear H.

apply PEq_sub using condition y x [[y∈x]].
pose proof equal_rev.
universal instantiation H3 x y. clear H3.
pose proof x_not_in_x.
universal instantiation H3 x. clear H3.
assert [[ZF|--¬(y∈x/\x∈{y})]]by FOL_tauto. clear H2 H H4 H5.

pose proof Singleton.
universal instantiation H x y. clear H.
apply PEq_sub using condition x y [[x∈y]].
pose proof equal_rev.
universal instantiation H4 y x. clear H4.
pose proof x_not_in_x.
universal instantiation H4 y. clear H4.
assert [[ZF|--¬(x∈y/\y∈{x})]]by FOL_tauto. clear H2 H H5 H6.

pose proof Singleton.
universal instantiation H y x. clear H.

assert [[ZF|--x∪{x}=y∪{y}->x=y]]by FOL_tauto.
universal generalization H x y.
The conclusion is already proved.
Qed.

Lemma Sn_natural_number_inversion:
  [[ZF;;is_natural_number N|--∀x,x∪{x}∈N->x∈N]].
Proof.
pose proof natural_number_inversion.
universal instantiation H [[x∪{x}]]. clear H.
pose proof not_empty.
universal instantiation H x. clear H.
assert [[ZF;;is_natural_number N;;x∪{x}∈N|--(∃y,y∈N/\x∪{x}=y∪{y})]]by FOL_tauto. clear H0 H1.
pose proof Sn_inversion.
universal instantiation H0 x y. clear H0.
pose proof equal_rev.
universal instantiation H0 x y. clear H0.
apply PEq_sub y x [[x∈N]].
assert [[ZF;;y∈N/\x∪{x}=y∪{y}|--x∈N]]by FOL_tauto. clear H1 H2 H0.
existential instantiation H3 [[∃y,y∈N/\x∪{x}=y∪{y}]].
assert [[ZF;;is_natural_number N|--x ∪ {x} ∈ N->x∈N]]by FOL_tauto.
universal generalization H1 x.
The conclusion is already proved.
Qed.
