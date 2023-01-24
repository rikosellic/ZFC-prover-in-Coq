Require Import FV.ZFLib.

(*** How to type unicode symbols in Coq ***)

(** By default, you can only use the following variable names.
  - x; y; z; u; v; w; n; a; b; c; d; e; f; g; X; Y; Z; N

 In this assignment, you may frequently use the symbols below, which seems
    hard to be typed out using an ordinary keyboard.

    - ∈; ∪; ∩; ∀; ∃; ∅; ¬; ⊆  

    Since these symbols are not in ASC-II (can not be directly found on your
    keyboard), you need to use CoqIDE's unicode support.

    - First, type the latex-format string of the symbol.

    - Second, press shift+space at the end of it.

    - Then, the latex string will then be automatically converted to the
      coressponding symbol.

    For example, to type ∈, first type \in, and when the cursor is at the end
    of 'n', press shift+space, then \in will become ∈.

    Here is a table of unicode symbols that you may use, and their corresponding
    latex representations:

    - \in ∈;

    - \cup ∪;

    - \cap ∩;

    - \forall ∀;

    - \exists ∃;

    - \emptyset ∅;

    - \neg ¬;

    - \subseteq ⊆. **)

(*** How to describe a set theory statement in Coq ***)

(** In short, you can use all of the following symbols to represent set theory
    constants, operations and predicates:

    - "∅" represents the empty set and it is a constant symbol;

    - "x ∪ y" represents the union of x and y, and you can treat union as a
      binary function in the logic;

    - "x ∩ y" represents the intersection of x and y, and you can treat
      intersection as a binary function in the logic;

    - "{ x }" represents the singleton set that containing x, and you can treat
      singleton set construction as a unary function in the logic;

    - "x ∈ y" says x is an element of y, and you can treat it as a binray
      predicate in the logic;

    - "x = y" says x and y are the same set and you can treat equality as a
      binary predicate in the logic;

    - "x ⊆ y" says x is a subset of y, and it is defined as an abbreviation of
      "∀ z, z ∈ x -> z ∈ y".

    You can use Coq's "Check" command to test whether we have written down a
    grammarly correct proposition. Remember to put your your proposition inside
    double square brackets. The following line is an example. Please press
    "Ctrl" + "Down" and get Coq's response. *)

Check [[ ∅ ∈ {∅} ]].

(** You should see Coq's response on the right column in CoqIDE. It says:
    [[∅ ∈ {∅}]] : prop. That means, your proposition is grammarly correct. Here
    is another example. *)

Check [[ ∅ ⊆ {∅} ]].

(** Well, please remember that the "Check" command is only for grammar
    check. *)

Check [[ {∅} ∈ {∅} ]].
Check [[ ∅ = {∅} ]].

(** In these examples above, the proposition "{∅} ∈ {∅}" and "∅ = {∅}" are
    mathematically incorrect statement and they can pass Coq's grammar check. *)

(** Beside these set theory symbols, we will use the following abbreviations to
    describe important set theory concepts:

    - "is_empty t" is an abbreviation of

      [[ ∀ y, ¬ y ∈ t ]]

    - "is_inductive t" is an abbreviation of

      [[ ∅ ∈ t /\ (∀ y, y ∈ t -> y ∪ {y} ∈ t ]]

    - "is_natural_number t" is an abbreviation of

      [[ is_inductive t /\ (∀ w, is_inductive w -> t ⊆ w ]]. *)

(** You can also use quantifiers and logic connectives when writing set theory
    propositions. Specifically:

    - "¬ phi" represents "not phi";

    - "phi /\ psi" represents "phi and psi";

    - "phi \/ psi" represents "phi or psi";

    - "phi -> psi" represents "phi implies psi";

    - "phi <-> psi" represents "phi is equivalent to psi";

    - "∀ x, phi" and "∃ x, phi" are quantified propositions.
    
    - Of course you can use parentheses  "()" to determine priority.
    
    Here are some examples. *)

Check [[ ∀ x, ¬ x ∈ ∅ ]].

Check [[ ∀ x, ∀ y, x ∈ y \/ ¬ x ∈ y ]].

Check [[ ∀ x, ∀ y, x ∈ y \/ y ∈ x ]].

Check [[ ∃ x, ∃ y, ¬ x ∈ y /\ ¬ y ∈ x ]].

Check [[ (∀x, x=y) -> z=y]].

Check [[ x=(y ∪ z) ∩ w ]].

(** In the end, remember that whenever we prove something in ZF set theory, we
    do actually derive them from ZF axioms using a first order logic. Here is an
    example of logic derivation. Again, Coq only checks grammar. *)

Check [[ ZF;; x = y |-- ∀ z, z ∈ x <-> z ∈ y ]].

(** This time, Coq says: [[ZF;; x = y |-- ∀ z, z ∈ x <-> z ∈ y]] : Prop. Notice
    that Coq's "prop" is different from "Prop". The checking result "Prop" says
    this is a grammarly correct statement about a first order logic; in
    comparison, previous checking result "prop" says those expressions are
    grammarly correct propositions inside the first order logic. 

    Here are some additional examples. *)

Check [[ ZF |-- x = y -> y = z -> z = x ]].
Check [[ ZF;; x ∈ y  |-- y ∈ z ]].
Check [[ ZF  |-- ∃ x, ∀ y, x ∈ y ]].
Check [[ ZF  |-- ∃ x, ∀ y, x ⊆ y ]].

(*** How to prove a first order logic derivation in Coq ***)

(** Till now, we have only introduced how to write down a first order logic
    derivation. Nothing has been done about proofs. Here is a super simple
    example. *)

Theorem intersect_subset1:
  [[ ZF |-- ∀ u, ∀ v, u ∩ v ⊆ u ]].
Proof.
  pose proof Intersection_iff.
  universal instantiation H u v z.
  assert [[ ZF |-- z ∈ u ∩ v -> z ∈ u ]] by Tauto.
  universal generalization H1 u v z.
  The conclusion is already proved.
Qed.

(** In this proof above, we first use the key [Theorem] to indicate that we are
    now ready to state a first order logic derivation and to prove it. Then,
    "intersect_subset1" is the name of this conclusion --- you can name your own
    set theory conclusion later.

    After stating this theorem, we start our proof by "Proof" and end it by
    "Qed". Between "Proof" and "Qed", the proof script contains 5 lines. These 5
    lines shows exactly all 5 proof commands that you can use in this
    assignment.

    - The "pose proof" command allows you to apply a set theory axiom. Here is
      a short list:

      Empty:
        [[ ZF |-- is_empty ∅ ]]

      Union:
        [[ ZF |-- ∀ x, ∀ y, ∀ z, z ∈ x ∪ y <-> z ∈ x \/ z ∈ y ]]
 
      Intersection_iff:
        [[ ZF |-- ∀ x, ∀ y, ∀ z, z ∈ x ∩ y <-> z ∈ x /\ z ∈ y ]]

      Union_iff:
        [[ ZF |-- ∀ x, ∃ y, ∀ z, z ∈ y <-> ∃ u, z ∈ u /\ u ∈ x ]]

      Singleton:
        [[ ZF |-- ∀x,∀ z, z ∈ {x} <-> z = x ]] 

      Extensionality:
        [[ ZF |-- ∀ x, ∀ y, (∀ z, z ∈ x <-> z ∈ y) <-> x = y ]]

      Pairing:
        [[ ZF |-- ∀ x, ∀ y, ∃ z, ∀ u, u ∈ z <-> u = x \/ u = y ]]

      PowerSet:
        [[ ZF |-- ∀ x, ∃ y, ∀ z, z ∈ y <-> z ⊂ x ]]

      Infinity:
        [[ ZF |-- ∃ x, isinductive x ]]

      We omit Axiom of Separation, Axiom of Replacement, Axiom of Regularity
      and Axiom of Choice here. They are included in our definition of ZF in
      this Coq library but they would probably be useless in your proof. If
      you really want to use these axioms, contact your instructor.

      After executing this command (using "Ctrl" + "Down"), you will find an
      extra line on the right side window. It says:
        H : [[ZF |-- ∀ x, ∀ y, ∀ z, z ∈ x ∩ y <-> z ∈ x /\ z ∈ y]]
      That means, you get a new hypothesis to use in this proof. The name of
      this hypothesis is "H".

    - The "universal instantiation" command applies universal instantiation on
      an existing hypothesis. In the proof sample above, the command
        " universal instantiation H u v z "
      uses u, v and w to instantiate three universally quantified variables in
      H, which are x, y and z.

      After executing this command (using "Ctrl" + "Down"), you will find an
      extra hypothesis H0 stating the instantiation result.

    - The "assert ... by Tauto" command allows you to state a first order logic
      derivation but you are only allowed to do so if this derivation can be
      proved using all existing assumptions (you may use zero assumption, one
      assumption, or more than one assumptions) and propositional logic
      tautologies.

      In the example above, it is legal to claim
         [[ ZF |-- z ∈ u ∩ v -> z ∈ u ]]
      because we have already known
         [[ZF |-- z ∈ u ∩ v <-> z ∈ u /\ z ∈ v]].
      The propositional logic reasoning behind it is: if [Phi |-- P <-> Q /\ R]
      then [Phi |-- P -> Q].

    - The "universal generalization" command applies universal generalization on
      an existing hypothesis.

    - The "The conclusion is already proved" command is used to complete a
      proof. You can only use it if the conclusion can be proved using all
      existing assumptions and propositional logic tautologies.

      Remember, subset relation is not itself a binary predicate in the logic.
      It is an abbreviation. In other words, [[ u ∩ v ⊆ u ]] is just a concise
      way of writing [[ ∀ u, ∀ v, ∀ z, z ∈ u ∩ v -> z ∈ u ]]. *)

(*** More examples of proofs ***)

(** Congratulations! Now you have simple yet powerful tools to prove theroems
    about set theory. Here we show more examples. *)

Theorem empty_set_is_empty:
  [[ ZF |-- ∀ y, ¬ y ∈ ∅ ]].
Proof.
  pose proof Empty.
  The conclusion is already proved.
Qed.

(** In this example above, we successfully claim that the conclusion is already 
    proved because [[ is_empty ∅ ]] is an abbreviation of [[ ∀ y, ¬ y ∈ ∅ ]]. *)

Theorem empty_set_subset:
  [[ ZF |-- ∀ x, ∅ ⊆ x ]].
Proof.
  pose proof empty_set_is_empty.
  universal instantiation H y.
  assert [[ ZF |-- y ∈ ∅ -> y ∈ x ]] by Tauto.
  universal generalization H1 x y.
  The conclusion is already proved.
Qed. 

(** In this example above, we show that the "pose proof" command allows you to
    pose not only axioms but also the theorems that you have already proved. *)

Theorem unique_empty_set:
  [[ZF |-- ∀ x, is_empty x -> x = ∅ ]]. 
Proof.
  pose proof Extensionality.
  universal instantiation H x [[∅]].
  pose proof Empty.
  universal instantiation H1 z.
  assert [[ZF |-- z ∈ ∅ -> z ∈ x]] by Tauto.
  assert [[ZF;; is_empty x |-- ∀ y, ¬ y ∈ x]] by Tauto.
  universal instantiation H4 z.
  assert ([[ZF;; is_empty x |-- z ∈ x <-> z ∈ ∅]]) by Tauto.
  universal generalization H6 z.
  assert ([[ZF |-- is_empty x -> x = ∅]]) by Tauto.
  universal generalization H8 x.
  The conclusion is already proved.
Qed.

(** Now, you may try by yourself and prove a very simple set theory property:
    for any two sets x and y, if [[ x ⊆ y ]] and [[ y ⊆ x ]], then [[ x = y ]].
    Specifically, remove "Admitted.", complete the proof below and make sure
    Coq accepts your proofs. *)

Theorem subset_subset_equal:
  [[ ZF |-- ∀ x, ∀ y, x ⊆ y -> y ⊆ x -> x = y ]].
Proof.
(* FILL IN HERE *)
pose proof Extensionality.
universal instantiation H x y.
assert [[ZF |-- (∀ z, z ∈ x <-> z ∈ y)-> x = y]] by Tauto.
assert [[ZF;; x ⊆ y /\ y ⊆ x|-- ∀ z, z ∈ x -> z ∈ y]] by Tauto.
universal instantiation H2 z.
assert [[ZF;; x ⊆ y /\ y ⊆ x |-- ∀ z, z ∈ y -> z ∈ x]] by Tauto.
universal instantiation H4 z.
assert [[ZF;; x ⊆ y /\ y ⊆ x |-- z ∈ x <-> z ∈ y]] by Tauto.
universal generalization H6 z.
assert [[ZF;; x ⊆ y /\ y ⊆ x|--x=y]] by Tauto.
assert [[ZF |-- x ⊆ y -> y ⊆ x -> x=y]] by Tauto.
universal generalization H9 x y.
The conclusion is already proved.
Qed.