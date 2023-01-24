Require Export Coq.Strings.String.
Require Export Coq.ZArith.ZArith.
Require Export Coq.Sets.Ensembles.
Require Export Coq.Bool.Bool.
Require Export FV.ExplicitName.
Require Export Compare_dec.
Require Export Coq.Lists.List.
Export ListNotations.

(* ***************************************************************** *)
(*                                                                   *)
(*                                                                   *)
(*  Basic library for Coq                                            *)
(*                                                                   *)
(*                                                                   *)
(* ***************************************************************** *)
Module A:= StringName.
Module B:= StringName.

Lemma Union_spec: forall A (v: A) P Q, Union _ P Q v <-> P v \/ Q v.
Proof.
  intros.
  split; intros.
  + inversion H; auto.
  + destruct H; [apply Union_introl | apply Union_intror]; auto.
Qed.

Lemma Singleton_spec: forall U x y, (Singleton U x) y <-> x = y.
Proof.
  intros; split; intro.
  + inversion H; auto.
  + subst; constructor.
Qed.

(* ***************************************************************** *)
(*                                                                   *)
(*                                                                   *)
(*  Syntax                                                           *)
(*                                                                   *)
(*                                                                   *)
(* ***************************************************************** *)

Module V := StringName.

Inductive term := 
| var (v:V.t)
| empty_set
| singleton (x:term)
| union (x y: term) 
| intersection (x y:term).

Inductive prop: Type :=
| PEq (t1 t2: term): prop
| PRel (t1 t2: term): prop
| PFalse: prop
| PTrue: prop
| PNot(P: prop)
| PAnd (P Q: prop): prop
| POr(P Q: prop): prop
| PImpl (P Q: prop): prop
| PIff (P Q: prop): prop
| PForall (x: V.t) (P: prop): prop
| PExists (x: V.t)(P:prop): prop.

Declare Custom Entry set.

Coercion var: V.t >-> term.

Notation "[[ e ]]" := e (at level 0, e custom set at level 99).
Notation "( x )" := x (in custom set, x custom set at level 99).
Notation "x" := x (in custom set at level 0, x constr at level 0).
(* Notation "f x .. y" := (.. (f x) .. y)
                  (in custom set at level 0, only parsing,
                  f constr, x constr, y constr). *)
Notation "∅":= empty_set (in custom set at level 5, no associativity).
Notation "{ x }":= (singleton x) (in custom set at level 5, x at level 13, no associativity).
Notation "x ∩ y" := (intersection x y)(in custom set at level 11, left associativity). 
Notation "x ∪  y" := (union x y)(in custom set at level 12, left associativity).
(* Notation "f x" := (f x) (in custom set at level 20, f constr, x constr, left associativity). *)
Notation "x = y" := (PEq x y) (in custom set at level 20, no associativity).
Notation "x ∈ y" := (PRel x y) (in custom set at level 20, no associativity).
Notation "¬ P" := (PNot P) (in custom set at level 23, right associativity).
Notation "P1 /\ P2" := (PAnd P1 P2) (in custom set at level 24, left associativity).
Notation "P1 \/ P2" := (POr P1 P2) (in custom set at level 26, left associativity).
Notation "P1 -> P2" := (PImpl P1 P2) (in custom set at level 27, right associativity).
Notation "P1 <-> P2" := (PIff P1 P2) (in custom set at level 28, no associativity).
Notation "∃ x , P" := (PExists x P) (in custom set at level 29,  right associativity).
Notation "∀ x , P" := (PForall x P) (in custom set at level 29, right associativity).
Notation " 'var2tm' x":= (var x) (in custom set at level 5, only parsing, x constr).

(* ***************************************************************** *)
(*                                                                   *)
(*                                                                   *)
(*  Substitution                                                     *)
(*                                                                   *)
(*                                                                   *)
(* ***************************************************************** *)

Fixpoint term_occur (x: V.t) (t: term): nat :=
    match t with
    | [[∅]] => O
    | var x0 => if V.eq_dec x x0 then S O else O
    | [[{x0}]] => term_occur x x0
    | [[ x0 ∩ y0 ]]
    | [[ x0 ∪ y0 ]] => term_occur x x0 + term_occur x y0
    end.

Fixpoint prop_free_occur (x: V.t) (d: prop): nat :=
    match d with
    | [[ t1 = t2]]   => (term_occur x t1) + (term_occur x t2)
    | [[ t1 ∈ t2]]   => (term_occur x t1) + (term_occur x t2)
    | PFalse  
    | PTrue        => O
    | [[ ¬ P ]] => prop_free_occur x P
    | [[ P1 /\ P2 ]]
    | [[ P1 \/ P2 ]]
    | [[ P1 -> P2 ]]
    | [[ P1 <-> P2]]  => (prop_free_occur x P1) + (prop_free_occur x P2)
    | [[ ∀x',P]] 
    | [[ ∃x',P]] => if V.eq_dec x x'
                      then O
                      else prop_free_occur x P
    end.

Fixpoint term_max_var (t: term): V.t :=
    match t with
    | [[∅]] => V.default
    |  var x0 => x0
    |  [[ {x0} ]] => term_max_var x0
    |  [[ x0 ∩ y0 ]]
    | [[ x0 ∪ y0 ]]=> V.max (term_max_var x0) (term_max_var y0)
    end.

Fixpoint prop_max_var (d: prop): V.t :=
    match d with
    | [[ t1 = t2]] 
    | [[ t1 ∈ t2]]  => V.max (term_max_var t1) (term_max_var t2)
    | PTrue
    | PFalse       => V.default
    | [[ ¬ P ]]  => prop_max_var P
    | [[ P1 /\ P2 ]]
    | [[ P1 \/ P2 ]]
    | [[ P1 -> P2 ]]
    | [[ P1 <-> P2]]   => V.max (prop_max_var P1) (prop_max_var P2)
    | [[ ∀x',P]] 
    | [[ ∃x',P]]  => V.max x' (prop_max_var P)
    end.

Definition subst_task: Type := list (V.t * term).

Fixpoint subst_task_occur (x: V.t) (st: subst_task): nat :=
    match st with
    | nil => O
    | cons (x', t') st' => term_occur x x' + term_occur x t' + subst_task_occur x st'
    end.

Fixpoint subst_task_max_var (st: subst_task): V.t :=
    match st with
    | nil => V.default
    | cons (x', t') st' => V.max x' (V.max (term_max_var t') (subst_task_max_var st'))
    end.

Definition new_var (P: prop) (st: subst_task): V.t :=
  V.next_name (V.max (prop_max_var P) (subst_task_max_var st)).

Fixpoint var_sub (x: V.t) (st: subst_task): term :=
  match st with
  | nil => x
  | cons (x', t') st' =>
    if V.eq_dec x x' then t' else var_sub x st'
  end.

Fixpoint term_sub (st: subst_task) (t: term) :=
  match t with
  | [[∅]]=> [[∅]]
  | var x => var_sub x st
  | [[ {x} ]]=> singleton (term_sub st x)
  | [[ x ∪ y]] => union (term_sub st x) (term_sub st y)
  | [[ x ∩ y]] => intersection (term_sub st x) (term_sub st y)
  end.

Fixpoint prop_sub (st: subst_task) (d: prop): prop :=
    match d with
    | [[ t1 = t2]]  => PEq (term_sub st t1) (term_sub st t2)
    | [[ t1 ∈ t2]]   => PRel (term_sub st t1) (term_sub st t2)
    | PTrue      => PTrue
    | PFalse      => PFalse
    |  [[ ¬ P ]]  => PNot (prop_sub st P)
    |  [[ P1 /\ P2 ]]=> PAnd (prop_sub st P1) (prop_sub st P2)
    | [[ P1 \/ P2 ]] => POr (prop_sub st P1) (prop_sub st P2)
    | [[ P1 -> P2 ]] => PImpl (prop_sub st P1) (prop_sub st P2)
    | [[ P1 <-> P2]] => PIff (prop_sub st P1) (prop_sub st P2)
    | [[ ∀x,P]]  => match subst_task_occur x st with
                     | O => PForall x (prop_sub st P)
                     | _ => let x' := new_var P st in
                            PForall x' (prop_sub (cons (x, var x') st) P)
                     end
    | [[ ∃x,P]]  => match subst_task_occur x st with
                     | O => PExists x (prop_sub st P)
                     | _ => let x' := new_var P st in
                            PExists x' (prop_sub (cons (x, var x') st) P)
                     end
    end.

 Notation "x |-> t" := (x, t) (in custom set at level 17, no associativity). 
Notation "P [ xt ]" :=
  (prop_sub ( cons xt nil ) P) (in custom set at level 20, no associativity) .
Notation "P [ xt1 ; xt2 ; .. ; xtn ]" :=
  (prop_sub ( cons xt1  (cons xt2 .. (cons xtn nil) .. ) ) P) (in custom set at level 20,  no associativity).

(* ***************************************************************** *)
(*                                                                   *)
(*                                                                   *)
(*  Alpha equivalence                                                *)
(*                                                                   *)
(*                                                                   *)
(* ***************************************************************** *)

Definition binder_pair:Type:=V.t*V.t*bool.

Definition binder_list: Type:=list binder_pair.

Definition binder_update (x:V.t)(y:V.t)(bd:binder_pair):binder_pair:=
let '(x0,y0,b):= bd in
if zerop (term_occur x x0 + term_occur y y0) then bd else (x0,y0,false).

Definition update (x y:V.t)(st:binder_list):=
  map (fun bd => binder_update x y bd) st.

Fixpoint in_binder_list(x y:V.t)(l:binder_list):bool:=
  match l with
  | nil => false
  | (x0,y0,b)::ls => if V.eq_dec x x0 
                                  then if V.eq_dec y y0
                                      then if Sumbool.sumbool_of_bool b
                                                  then true
                                               else
                                                  in_binder_list x y ls
                                       else  in_binder_list x y ls else  in_binder_list x y ls 
end.

Fixpoint not_in_binder_list(x:V.t)(l:binder_list):bool:=
  match l with
  | nil => true
  | (x0,y0,b)::ls => if V.eq_dec x x0 then false else
                                      if V.eq_dec x y0 then false else not_in_binder_list x ls
  end.

Fixpoint term_alpha_eq(l:binder_list)(t1 t2:term):bool:=
  match t1,t2 with
  | empty_set, empty_set => true
  | var x, var y => if V.eq_dec x y then in_binder_list x y l || not_in_binder_list x l
                              else in_binder_list x y l
  | singleton x, singleton y => term_alpha_eq l x y
  | intersection x1 x2, intersection y1 y2
  | union x1 x2, union y1 y2 => term_alpha_eq l x1 y1 && term_alpha_eq l x2 y2
  | _ , _ => false
  end.

Fixpoint alpha_eq(l:binder_list)(P Q:prop):bool:=
  match P,Q with
  | [[t1 = t2]], [[t3=t4]]
  | [[t1 ∈ t2]], [[t3 ∈ t4]] => term_alpha_eq l t1 t3 && term_alpha_eq l t2 t4
  | PTrue, PTrue
  | PFalse, PFalse => true
  | [[¬ P1]], [[¬ Q1]] => alpha_eq l P1 Q1 
  | [[P1 /\ P2]], [[Q1 /\ Q2]]
  | [[P1 \/ P2]],  [[Q1 \/ Q2]]
  | [[P1 -> P2]],  [[Q1 -> Q2]]
  | [[P1 <-> P2]],  [[Q1 <-> Q2]] => alpha_eq l P1 Q1 && alpha_eq l P2 Q2 
  | [[∀x, P1]], [[∀y, Q1]]
  | [[∃x, P1]],  [[∃y, Q1]]=> alpha_eq ((x,y,true)::(update x y l)) P1 Q1
  | _, _ => false
  end.
  
Definition aeq(P Q:prop):bool:= alpha_eq nil P Q.

(* ***************************************************************** *)
(*                                                                   *)
(*                                                                   *)
(*  SAT solver                                                       *)
(*                                                                   *)
(*                                                                   *)
(* ***************************************************************** *)

Module prop_table.

Fixpoint term_eqb (s t: term): bool :=
  match s, t with
  | var x, var y => if V.eq_dec x y then true else false
  | empty_set, empty_set => true
  | singleton s1, singleton t1 => term_eqb s1 t1
  | union s1 s2, union t1 t2 => term_eqb s1 t1 && term_eqb s2 t2
  | intersection s1 s2, intersection t1 t2 => term_eqb s1 t1 && term_eqb s2 t2
  | _, _ => false
  end.

Fixpoint prop_eqb (P Q: prop) :=
  match P, Q with
  | PEq s1 s2, PEq t1 t2 => term_eqb s1 t1 && term_eqb s2 t2
  | PRel s1 s2, PRel t1 t2 => term_eqb s1 t1 && term_eqb s2 t2
  | PFalse, PFalse => true
  | PTrue, PTrue => true
  | PNot P1, PNot Q1 => prop_eqb P1 Q1
  | PAnd P1 P2, PAnd Q1 Q2 => prop_eqb P1 Q1 && prop_eqb P2 Q2
  | POr P1 P2, POr Q1 Q2 => prop_eqb P1 Q1 && prop_eqb P2 Q2
  | PImpl P1 P2, PImpl Q1 Q2 => prop_eqb P1 Q1 && prop_eqb P2 Q2
  | PIff P1 P2, PIff Q1 Q2 => prop_eqb P1 Q1 && prop_eqb P2 Q2
  | PForall x P1, PForall y Q1 => if V.eq_dec x y then prop_eqb P1 Q1 else false
  | PExists x P1, PExists y Q1 => if V.eq_dec x y then prop_eqb P1 Q1 else false
  | _, _ => false
  end.

Definition prop_table := list (prop * string).

Fixpoint prop_look_up {B: Type} (x: prop) (KV: list (prop * B)): option B :=
  match KV with
  | nil => None
  | cons (x0, v0) KV0 =>
      if aeq x0 x then Some v0 else prop_look_up x KV0
  end.

End prop_table.
                                 
Module ToyDPLL.

Module PV := StringName.

Definition ident := PV.t.

Definition clause := list (bool * ident).

Definition CNF := list clause.

Definition partial_asgn := list (ident * bool).

Inductive UP_result :=
| Conflict
| UP (x: ident) (b: bool)
| Nothing.

Fixpoint find_unit_pro_in_clause (c: clause) (J: partial_asgn) (cont: UP_result): UP_result :=
  match c with
  | nil => cont
  | (op, x) :: c' =>
      match PV.look_up x J with
      | None => match cont with
                | Conflict => find_unit_pro_in_clause c' J (UP x op)
                | UP _ _ => Nothing
                | _ => Nothing
                end
      | Some b => if eqb op b then Nothing else find_unit_pro_in_clause c' J cont
      end
  end.

Definition unit_pro' (P: CNF) (J: partial_asgn): list UP_result :=
  map (fun c => find_unit_pro_in_clause c J Conflict) P.

Definition fold_UP_result (rs: list UP_result): option partial_asgn :=
  fold_left (fun (o: option partial_asgn) (r: UP_result) =>
               match r, o with
               | _, None => None
               | Nothing, _ => o
               | Conflict, _ => None
               | UP x b, Some J => Some ((x, b) :: J)
               end) rs (Some nil).

Definition unit_pro (P: CNF) (J: partial_asgn): option partial_asgn :=
  fold_UP_result (unit_pro' P J).

Definition clause_filter (J: partial_asgn) (c: clause): clause :=
  filter (fun opx: bool * ident =>
            match opx with
            | (op, x) => match PV.look_up x J with
                         | None => true
                         | Some b => eqb b op
                         end
            end) c.
         
Definition clause_not_ex_true (J: partial_asgn) (c: clause): bool :=
  negb 
  (existsb
      (fun opx: bool * ident =>
            match opx with
            | (op, x) => match PV.look_up x J with
                         | None => false
                         | Some b => eqb b op
                         end
            end) c).

Definition pick (P: CNF): ident :=
  match P with
  | ((_, x) :: _) :: _ => x
  | _ => "impossible"%string
  end.

Definition CNF_filter (P: CNF) (J: partial_asgn): CNF :=
  map (clause_filter J) (filter (clause_not_ex_true J) P).

Fixpoint DPLL_UP (P: CNF) (J: partial_asgn) (n: nat): bool :=
  match n with | O => true | S n' =>
    match unit_pro P J with
    | None => false
    | Some kJ => match kJ with
                 | nil => DPLL_filter P J n'
                 | _ => DPLL_UP P (kJ ++ J) n'
                 end
    end
  end
with DPLL_filter (P: CNF) (J: partial_asgn) (n: nat): bool :=
  match n with | O => true | S n' =>
    DPLL_pick (CNF_filter P J) nil n'
  end
with DPLL_pick (P: CNF) (J: partial_asgn) (n: nat): bool :=
  match n with | O => true | S n' =>
    let x := pick P in
    DPLL_UP P ((x, true) :: J) n' || DPLL_UP P ((x, false) :: J) n'
  end.

Local Open Scope string.

Definition cnf1 :=
  ((true, "x") :: (true, "y") :: nil) :: ((true, "x") :: (false, "y") :: nil) :: nil. 

Eval compute in (DPLL_UP cnf1 nil 6).

Definition cnf2 :=
  ((true, "x") :: (true, "y") :: nil) :: ((true, "x") :: (false, "y") :: nil) :: ((false, "x") :: nil) :: nil.

Eval compute in (DPLL_UP cnf2 nil 6).

Definition cnf3 :=
  ((false, "x") :: (true, "y") :: nil) ::
  ((false, "y") :: (true, "z") :: nil) ::
  ((false, "z") :: (true, "w") :: nil) ::
  ((true, "x") :: nil) ::
  ((false, "w") :: nil) :: nil.

Eval compute in (DPLL_UP cnf3 nil 12).

Inductive sprop: Type :=
| SId (x: V.t)
| SFalse
| STrue
| SNot (P: sprop)
| SAnd (P Q: sprop)
| SOr (P Q: sprop)
| SImpl (P Q: sprop).

Fixpoint sprop_gen (P: prop) (t: prop_table.prop_table) (n: V.t): sprop * prop_table.prop_table * V.t :=
  match prop_table.prop_look_up P t with
  | Some x => (SId x, t, n)
  | None => match P with
            | PFalse => (SFalse, t, n)
            | PTrue => (STrue, t, n)
            | PNot P1 => match sprop_gen P1 t n with
                         | (res0, t0, n0) => (SNot res0, t0, n0)
                         end
            | PAnd P1 P2 => match sprop_gen P1 t n with
                            | (res0, t0, n0) =>
                                match sprop_gen P2 t0 n0 with
                                | (res1, t1, n1) => (SAnd res0 res1, t1, n1)
                                end
                            end
            | POr P1 P2  => match sprop_gen P1 t n with
                            | (res0, t0, n0) =>
                                match sprop_gen P2 t0 n0 with
                                | (res1, t1, n1) => (SOr res0 res1, t1, n1)
                                end
                            end
            | PImpl P1 P2=> match sprop_gen P1 t n with
                            | (res0, t0, n0) =>
                                match sprop_gen P2 t0 n0 with
                                | (res1, t1, n1) => (SImpl res0 res1, t1, n1)
                                end
                            end
            | PIff P1 P2=> match sprop_gen P1 t n with
                           | (res0, t0, n0) =>
                               match sprop_gen P2 t0 n0 with
                               | (res1, t1, n1) => (SAnd (SImpl res0 res1) (SImpl res1 res0), t1, n1)
                               end
                           end
            | _ => (SId n, (P, n) :: t, V.next_name n)
            end
  end.

Fixpoint clause_gen (P: sprop) (n: V.t) (cont': clause) (cont: CNF): clause * CNF * V.t :=
  match P with
  | SId x => ((true, x) :: cont', cont, n)
  | SFalse => (cont', cont, n)
  | STrue => (((true, "tauto"):: (false, "tauto"):: nil), cont, n)
  | SNot P1 => clause_neg_gen P1 n cont' cont
  | SAnd P1 P2 => match clause_gen P1 (V.next_name n) ((false, n) :: nil) cont with
                  | (cont'0, cont0, n0) =>
                      match clause_gen P2 n0 ((false, n) :: nil) (cont'0 :: cont0) with
                      | (cont'1, cont1, n1) =>
                        ((true, n) :: cont', cont'1 :: cont1, n1)
                      end
                  end
  | SOr P1 P2 => match clause_gen P1 n cont' cont with
                 | (cont'0, cont0, n0) =>
                     clause_gen P2 n0 cont'0 cont0
                 end
  | SImpl P1 P2 => match clause_neg_gen P1 n cont' cont with
                   | (cont'0, cont0, n0) =>
                       clause_gen P2 n0 cont'0 cont0
                   end
  end
with clause_neg_gen (P: sprop) (n: V.t) (cont': clause) (cont: CNF): clause * CNF * V.t :=
  match P with
  | SId x => ((false, x) :: cont', cont, n)
  | SFalse => (((true, "tauto"):: (false, "tauto"):: nil), cont, n)
  | STrue => (cont', cont, n)
  | SNot P1 => clause_gen P1 n cont' cont
  | SAnd P1 P2 => match clause_neg_gen P1 n cont' cont with
                  | (cont'0, cont0, n0) =>
                      clause_neg_gen P2 n0 cont'0 cont0
                  end
  | SOr P1 P2 => match clause_neg_gen P1 (V.next_name n) ((true, n) :: nil) cont with
                 | (cont'0, cont0, n0) =>
                     match clause_neg_gen P2 n0 ((true, n) :: nil) (cont'0 :: cont0) with
                     | (cont'1, cont1, n1) =>
                       ((false, n) :: cont', cont'1 :: cont1, n1)
                     end
                 end
  | SImpl P1 P2 => match clause_gen P1 (V.next_name n) ((true, n) :: nil) cont with
                   | (cont'0, cont0, n0) =>
                       match clause_neg_gen P2 n0 ((true, n) :: nil) (cont'0 :: cont0) with
                       | (cont'1, cont1, n1) =>
                         ((false, n) :: cont', cont'1 :: cont1, n1)
                       end
                   end
  end.

Fixpoint cnf_gen (P: sprop) (n: V.t) (cont: CNF): CNF * V.t :=
  match P with
  | SId x => (((true, x) :: nil) :: cont, n)
  | SFalse => (((true, "impossible"):: nil) :: ((false, "impossible"):: nil) :: nil, n)
  | STrue => (cont, n)
  | SNot P1 => match clause_neg_gen P1 (V.next_name n) ((true, n) :: nil) (((false, n) :: nil) :: cont) with
               | (cont'0, cont0, n0) => (cont'0 :: cont0, n0)
               end
  | SAnd P1 P2 => match cnf_gen P1 n cont with
                  | (cont0, n0) => cnf_gen P2 n0 cont0
                  end
  | SOr P1 P2 => match clause_gen P1 n nil cont with
                 | (cont'0, cont0, n0) =>
                     match clause_gen P2 n0 cont'0 cont0 with
                     | (cont'1, cont1, n1) => (cont'1 :: cont1, n1)
                     end
                 end
  | SImpl P1 P2 => match clause_neg_gen P1 n nil cont with
                   | (cont'0, cont0, n0) =>
                       match clause_gen P2 n0 cont'0 cont0 with
                       | (cont'1, cont1, n1) => (cont'1 :: cont1, n1)
                       end
                   end
  end.

Definition valid (P: prop): bool :=
  match sprop_gen (PNot P) nil "x" with
  | (P', _, n) =>
    match cnf_gen P' n nil with
    | (P'', _) => negb (DPLL_UP P'' nil 24)
    end
  end.

Definition der_judgement: Type := list prop * prop.

Definition proof_goal: Type := list der_judgement * der_judgement.

Definition der2prop (d: der_judgement): prop :=
  fold_right PImpl (snd d) (fst d).

Definition pg2prop (pg: proof_goal): prop :=
  fold_right (fun x y => PImpl (der2prop x) y) (der2prop (snd pg)) (fst pg).

End ToyDPLL.

Module ToyDPLL2.

Import ToyDPLL.

Inductive result :=
| SAT
| UNSAT
| UNKNOWN (J: partial_asgn) (P: CNF).

Fixpoint DPLL_UP (P: CNF) (J: partial_asgn) (n: nat): result :=
  match n with | O => UNKNOWN J P | S n' =>
    match unit_pro P J with
    | None => UNSAT
    | Some kJ => match kJ with
                 | nil => DPLL_filter P J n'
                 | _ => DPLL_UP P (kJ ++ J) n'
                 end
    end
  end
with DPLL_filter (P: CNF) (J: partial_asgn) (n: nat): result :=
  match n with | O => UNKNOWN J P | S n' =>
    DPLL_pick (CNF_filter P J) nil n'
  end
with DPLL_pick (P: CNF) (J: partial_asgn) (n: nat): result :=
  match n with | O => UNKNOWN J P | S n' =>
    let x := pick P in
    match DPLL_UP P ((x, true) :: J) n' with
    | SAT => SAT
    | UNSAT => DPLL_UP P ((x, false) :: J) n'
    | UNKNOWN J P => match DPLL_UP P ((x, false) :: J) n' with
                 | SAT => SAT
                 | _ => UNKNOWN J P
                 end
    end
  end.

End ToyDPLL2.

(* ***************************************************************** *)
(*                                                                   *)
(*                                                                   *)
(*  Variable name definitions                                        *)
(*                                                                   *)
(*                                                                   *)
(* ***************************************************************** *)

Notation "'EVAL' x" := (ltac:(let y := eval compute in x in exact y): V.t) (at level 0).

Module ShortNames.

Definition x := EVAL "x"%string.
Definition x0 := EVAL (V.next_name x).
Definition x1 := EVAL (V.next_name x0).
Definition x2 := EVAL (V.next_name x1).
Definition x3 := EVAL (V.next_name x2).
Definition y := EVAL "y"%string.
Definition y0 := EVAL (V.next_name y).
Definition y1 := EVAL (V.next_name y0).
Definition y2 := EVAL (V.next_name y1).
Definition y3 := EVAL (V.next_name y2).
Definition z := EVAL "z"%string.
Definition z0 := EVAL (V.next_name z).
Definition z1 := EVAL (V.next_name z0).
Definition z2 := EVAL (V.next_name z1).
Definition z3 := EVAL (V.next_name z2).
Definition u := EVAL "u"%string.
Definition u0 := EVAL (V.next_name u).
Definition u1 := EVAL (V.next_name u0).
Definition u2 := EVAL (V.next_name u1).
Definition u3 := EVAL (V.next_name u2).
Definition v := EVAL "v"%string.
Definition v0 := EVAL (V.next_name v).
Definition v1 := EVAL (V.next_name v0).
Definition v2 := EVAL (V.next_name v1).
Definition v3 := EVAL (V.next_name v2).
Definition w := EVAL "w"%string.
Definition w0 := EVAL (V.next_name w).
Definition w1 := EVAL (V.next_name w0).
Definition w2 := EVAL (V.next_name w1).
Definition w3 := EVAL (V.next_name w2).
Definition n := EVAL "n"%string.
Definition n0 := EVAL (V.next_name n).
Definition n1 := EVAL (V.next_name n0).
Definition n2 := EVAL (V.next_name n1).
Definition n3 := EVAL (V.next_name n2).
Definition m := EVAL "m"%string.
Definition m0 := EVAL (V.next_name m).
Definition m1 := EVAL (V.next_name m0).
Definition m2 := EVAL (V.next_name m1).
Definition m3 := EVAL (V.next_name m2).
Definition a := EVAL "a"%string.
Definition a0 := EVAL (V.next_name a).
Definition a1 := EVAL (V.next_name a0).
Definition a2 := EVAL (V.next_name a1).
Definition a3 := EVAL (V.next_name a2).
Definition b := EVAL "b"%string.
Definition b0 := EVAL (V.next_name b).
Definition b1 := EVAL (V.next_name b0).
Definition b2 := EVAL (V.next_name b1).
Definition b3 := EVAL (V.next_name b2).
Definition c := EVAL "c"%string.
Definition c0 := EVAL (V.next_name c).
Definition c1 := EVAL (V.next_name c0).
Definition c2 := EVAL (V.next_name c1).
Definition c3 := EVAL (V.next_name c2).
Definition d := EVAL "d"%string.
Definition d0 := EVAL (V.next_name d).
Definition d1 := EVAL (V.next_name d0).
Definition d2 := EVAL (V.next_name d1).
Definition d3 := EVAL (V.next_name d2).
Definition e := EVAL "e"%string.
Definition e0 := EVAL (V.next_name e).
Definition e1 := EVAL (V.next_name e0).
Definition e2 := EVAL (V.next_name e1).
Definition e3 := EVAL (V.next_name e2).
Definition f := EVAL "f"%string.
Definition f0 := EVAL (V.next_name f).
Definition f1 := EVAL (V.next_name f0).
Definition f2 := EVAL (V.next_name f1).
Definition f3 := EVAL (V.next_name f2).
Definition g := EVAL "g"%string.
Definition g0 := EVAL (V.next_name g).
Definition g1 := EVAL (V.next_name g0).
Definition g2 := EVAL (V.next_name g1).
Definition g3 := EVAL (V.next_name g2).
Definition h := EVAL "h"%string.
Definition h0 := EVAL (V.next_name h).
Definition h1 := EVAL (V.next_name h0).
Definition h2 := EVAL (V.next_name h1).
Definition h3 := EVAL (V.next_name h2).
Definition p := EVAL "p"%string.
Definition p0 := EVAL (V.next_name p).
Definition p1 := EVAL (V.next_name p0).
Definition p2 := EVAL (V.next_name p1).
Definition p3 := EVAL (V.next_name p2).
Definition q := EVAL "q"%string.
Definition q0 := EVAL (V.next_name q).
Definition q1 := EVAL (V.next_name q0).
Definition q2 := EVAL (V.next_name q1).
Definition q3 := EVAL (V.next_name q2).
Definition X := EVAL "X"%string.
Definition X0 := EVAL (V.next_name X).
Definition X1 := EVAL (V.next_name X0).
Definition X2 := EVAL (V.next_name X1).
Definition X3 := EVAL (V.next_name X2).
Definition Y := EVAL "Y"%string.
Definition Y0 := EVAL (V.next_name Y).
Definition Y1 := EVAL (V.next_name Y0).
Definition Y2 := EVAL (V.next_name Y1).
Definition Y3 := EVAL (V.next_name Y2).
Definition Z := EVAL "Z"%string.
Definition Z0 := EVAL (V.next_name Z).
Definition Z1 := EVAL (V.next_name Z0).
Definition Z2 := EVAL (V.next_name Z1).
Definition Z3 := EVAL (V.next_name Z2).
Definition N := EVAL "N"%string.

Ltac super_fold_in H :=
  repeat
    first
    [ progress fold x3 in H
    | progress fold x2 in H
    | progress fold x1 in H
    | progress fold x0 in H
    | progress fold x in H
    | progress fold y3 in H
    | progress fold y2 in H
    | progress fold y1 in H
    | progress fold y0 in H
    | progress fold y in H
    | progress fold z3 in H
    | progress fold z2 in H
    | progress fold z1 in H
    | progress fold z0 in H
    | progress fold z in H
    | progress fold u3 in H
    | progress fold u2 in H
    | progress fold u1 in H
    | progress fold u0 in H
    | progress fold u in H
    | progress fold v3 in H
    | progress fold v2 in H
    | progress fold v1 in H
    | progress fold v0 in H
    | progress fold v in H
    | progress fold w3 in H
    | progress fold w2 in H
    | progress fold w1 in H
    | progress fold w0 in H
    | progress fold w in H
    | progress fold n3 in H
    | progress fold n2 in H
    | progress fold n1 in H
    | progress fold n0 in H
    | progress fold n in H
    | progress fold m3 in H
    | progress fold m2 in H
    | progress fold m1 in H
    | progress fold m0 in H
    | progress fold m in H
    | progress fold a3 in H
    | progress fold a2 in H
    | progress fold a1 in H
    | progress fold a0 in H
    | progress fold a in H
    | progress fold b3 in H
    | progress fold b2 in H
    | progress fold b1 in H
    | progress fold b0 in H
    | progress fold b in H
    | progress fold c3 in H
    | progress fold c2 in H
    | progress fold c1 in H
    | progress fold c0 in H
    | progress fold c in H
    | progress fold d3 in H
    | progress fold d2 in H
    | progress fold d1 in H
    | progress fold d0 in H
    | progress fold d in H
    | progress fold e3 in H
    | progress fold e2 in H
    | progress fold e1 in H
    | progress fold e0 in H
    | progress fold e in H
    | progress fold f3 in H
    | progress fold f2 in H
    | progress fold f1 in H
    | progress fold f0 in H
    | progress fold f in H
    | progress fold g3 in H
    | progress fold g2 in H
    | progress fold g1 in H
    | progress fold g0 in H
    | progress fold g in H
    | progress fold h3 in H
    | progress fold h2 in H
    | progress fold h1 in H
    | progress fold h0 in H
    | progress fold h in H
    | progress fold p3 in H
    | progress fold p2 in H
    | progress fold p1 in H
    | progress fold p0 in H
    | progress fold p in H
    | progress fold q3 in H
    | progress fold q2 in H
    | progress fold q1 in H
    | progress fold q0 in H
    | progress fold q in H
    | progress fold X3 in H
    | progress fold X2 in H
    | progress fold X1 in H
    | progress fold X0 in H
    | progress fold X in H
    | progress fold Y3 in H
    | progress fold Y2 in H
    | progress fold Y1 in H
    | progress fold Y0 in H
    | progress fold Y in H
    | progress fold Z3 in H
    | progress fold Z2 in H
    | progress fold Z1 in H
    | progress fold Z0 in H
    | progress fold Z in H
    | progress fold N in H].

End ShortNames.

(* ***************************************************************** *)
(*                                                                   *)
(*                                                                   *)
(*  Abbreviations                                                    *)
(*                                                                   *)
(*                                                                   *)
(* ***************************************************************** *)

Module Rules.

Import ShortNames.

Definition subset (t1 t2: term): prop :=
  [[ ( ∀ z, z ∈ x -> z ∈ y )[ x |-> t1 ; y |-> t2 ] ]].

Notation "t1 '⊆' t2" := (subset t1 t2) (in custom set at level 20, no associativity) .

Definition is_empty_def (t: term): prop :=
  [[ (∀ y, ¬ y ∈ x) [ x |-> t ] ]].

Notation " 'is_empty'  t1":= (is_empty_def t1) (in custom set at level 20, t1 at level 15,no associativity).   

(* t1 = {t2} *)
Definition is_singleton_def (t1 t2: term): prop :=
 [[ (∀ z, z ∈ x <-> z = y) [ x |-> t1 ; y |-> t2 ] ]].
 
Notation " 'is_singleton'  t1 t2 ":= (is_singleton_def t1 t2) (in custom set at level 20, t1 at level 15, t1 at level 15, no associativity).

(* t1 = {t2, t3} *)
Definition has_two_ele_def (t1 t2 t3: term): prop :=
 [[ (∀ u, u ∈ x <-> u = y \/ u = z) [ x |-> t1 ; y |-> t2 ; z |-> t3 ] ]].

Notation " 'has_two_ele'  t1 t2 t3":= (has_two_ele_def t1 t2 t3) (in custom set at level 20, t1 at level 15, t2 at level 15, t3 at level 15, no associativity).

(* t1 = (t2, t3) := {{t2}, {t2, t3}} *)
Definition is_pair_def (t1 t2 t3: term): prop :=
  [[ (∃ u, ∃ v, is_singleton u y  /\  has_two_ele v y z/\ has_two_ele x u v) [ x |-> t1 ; y |-> t2 ; z |-> t3 ] ]].
  
 Notation " 'is_pair'  t1 t2 t3":= (is_pair_def t1 t2 t3) (in custom set at level 20, t1 at level 15, t2 at level 15, t3 at level 15, no associativity).
 
(* t1 = t2 U t3 *)
Definition is_union2_def (t1 t2 t3: term): prop :=
[[ (∀ u, u  ∈ x <-> u ∈ y \/ u ∈ z) [ x |-> t1 ; y |-> t2 ; z |-> t3 ] ]].

Notation " 'is_union2'  t1 t2 t3":= (is_union2_def t1 t2 t3) (in custom set at level 20, t1 at level 15, t2 at level 15, t3 at level 15, no associativity).

Definition is_prod_def (t1 t2 t3: term): prop :=
  [[(∀ u, u ∈ x <-> ∃ v, ∃ w, v ∈ y /\ w ∈ z /\  is_pair u v w )
  [ x |-> t1 ; y |-> t2 ; z |-> t3 ] ]].
  
Notation " 'is_prod'  t1 t2 t3":= (is_prod_def t1 t2 t3) (in custom set at level 20, t1 at level 15, t2 at level 15, t3 at level 15, no associativity).

Definition is_rel_def (t1 t2 t3: term): prop :=
 [[ (∀ u, u ∈ x -> ∃ v, ∃ w, v ∈ y /\ w ∈ z /\  is_pair u v w)
  [ x |-> t1 ; y |-> t2 ; z |-> t3 ] ]].
  
Notation " 'is_rel'  t1 t2 t3":= (is_rel_def t1 t2 t3) (in custom set at level 20, t1 at level 15, t2 at level 15, t3 at level 15, no associativity).

(* (t1, t2) in t3 *)
Definition in_rel_def (t1 t2 t3: term): prop :=
  [[ (∃ u,  is_pair u x y  /\ u ∈ z) [ x |-> t1 ; y |-> t2 ; z |-> t3 ] ]].
  
Notation " 'in_rel'  t1 t2 t3":= (in_rel_def t1 t2 t3) (in custom set at level 20, t1 at level 15, t2 at level 15, t3 at level 15, no associativity).

Definition is_func_def (t: term): prop :=
  [[ (∀ y, ∀ z, ∀ u,
    in_rel y z x  -> in_rel y u x  -> z = u) ]].
   
Notation " 'is_func'  t1":= (is_func_def t1) (in custom set at level 20, t1 at level 15, no associativity).
   
Definition is_inductive_def(t:term):=
  [[ (∅ ∈ x /\ ∀ y, (y ∈ x -> y ∪ {y} ∈ x) ) [ x |-> t] ]].
  
Notation " 'is_inductive'  t1":= (is_inductive_def t1) (in custom set at level 20, t1 at level 15, no associativity).  

Definition is_natural_number_def(t:term):=
  [[ (is_inductive x /\ ∀ w, (is_inductive w) -> x ⊆ w)[ x |-> t] ]].
  
Notation " 'is_natural_number'  t1":= (is_natural_number_def t1) (in custom set at level 20, t1 at level 15, no associativity).

Definition is_triple_def (t1 t2 t3 t4: term): prop :=
  [[ (∃ a, is_pair a x y /\ is_pair b a z ) [ b |-> t1 ; x |-> t2 ; y |-> t3 ; z |-> t4] ]].
  
Notation " 'is_triple'  t1 t2 t3 t4":= (is_triple_def t1 t2 t3 t4) (in custom set at level 20, t1 at level 15, t2 at level 15, t3 at level 15, t4 at level 15, no associativity).

Definition is_N2_def(t1 t2:term): prop :=
  [[( is_pair x N N )[x |-> t1; N |-> t2] ]].
  
Notation " 'is_N2'  t1 t2":= (is_N2_def t1 t2) (in custom set at level 20, t1 at level 15, t2 at level 15, no associativity).

Definition is_N3_def(t1 t2:term): prop :=
  [[(∃Y, is_N2 Y N /\ is_pair x Y N )[x|-> t1; N |-> t2] ]].
  
Notation " 'is_N3'  t1 t2":= (is_N3_def t1 t2) (in custom set at level 20, t1 at level 15, t2 at level 15, no associativity).

Definition in_rel3_def (t1 t2 t3 t4: term): prop :=
  [[ (∃ u, is_triple u x y z /\ u ∈ n) [ x |-> t1 ; y |-> t2 ; z |-> t3 ; n |-> t4 ] ]].
  
Notation " 'in_rel3'  t1 t2 t3 t4":= (in_rel3_def t1 t2 t3 t4) (in custom set at level 20, t1 at level 15, t2 at level 15, t3 at level 15, t4 at level 15, no associativity).

Definition is_legal_plus_def(t1 t2:term):prop:= 
  [[( (∀ n, n ∈ N -> in_rel3 ∅ n n x) /\ (∀ n,∀ d,∀ e, n ∈ N /\ d ∈ N /\ e ∈ N ->( in_rel3 n d e x -> in_rel3 n∪{n} d e∪{e} x))) [ x |-> t1 ; N |-> t2] ]].
  
Notation " 'is_legal_plus'  t1 t2":= (is_legal_plus_def t1 t2) (in custom set at level 20, t1 at level 15, t2 at level 15, no associativity).

Definition is_plus_def(t1 t2:term):=
  [[(is_legal_plus x N /\ (∀ y, is_legal_plus y N -> x ⊆ y))[x |-> t1 ; N |-> t2] ]].
  
Notation " 'is_plus'  t1 t2":= (is_plus_def t1 t2) (in custom set at level 20, t1 at level 15, t2 at level 15, no associativity).

Definition is_legal_mult_def(t1 t2 t3:term):prop:= 
  [[( (∀ n, n ∈ N -> in_rel3 n ∅ ∅ f) /\ (∀x, ∀y, ∀z, ∀a, x∈N/\y∈N/\z∈N/\a∈N -> in_rel3 x y z f -> (in_rel3 z x a e -> in_rel3 x y∪{y} a f ))) [ f |-> t1 ; e |-> t2 ; N |-> t3] ]].

Notation " 'is_legal_mult'  t1 t2 t3":= (is_legal_mult_def t1 t2 t3) (in custom set at level 20, t1 at level 15, t2 at level 15, t3 at level 15, no associativity).

Definition is_mult_def(t1 t2 t3:term):=
  [[(is_legal_mult x e N /\ (∀ y, is_legal_mult y e N -> x ⊆ y))[x |-> t1 ; e |-> t2 ; N |-> t3] ]].

Notation " 'is_mult'  t1 t2 t3":= (is_mult_def t1 t2 t3) (in custom set at level 20, t1 at level 15, t2 at level 15, t3 at level 15, no associativity).

(* ***************************************************************** *)
(*                                                                   *)
(*                                                                   *)
(*  Proof theory                                                     *)
(*                                                                   *)
(*                                                                   *)
(* ***************************************************************** *)

Definition context: Type := prop -> Prop.
Definition empty_context: context := fun _ => False.
Notation "Phi ;; x" := (Union _ Phi (Singleton _ x)) (in custom set at level 31, left associativity).

Inductive derivable: context -> prop -> Prop :=
| PForall_elim: forall Phi (vr: V.t) (t: term) P,
    derivable Phi [[∀ vr, P]] ->
    derivable Phi [[ P [ vr |-> t ] ]]
| PExists_intros: forall Phi (vr: V.t) (t: term) P,
    derivable Phi [[ P [ vr |-> t ] ]] ->
    derivable Phi [[ ∃ vr, P ]]
| PForall_intros: forall (Phi: context) (vr: V.t) P,
    (forall phi, Phi phi -> prop_free_occur vr phi = O) ->
    derivable Phi P ->
    derivable Phi [[ ∀ vr, P]]
| PExists_elim: forall (Phi: context) (vr: V.t) P Q,
    (forall phi, Phi phi -> prop_free_occur vr phi = O) ->
    prop_free_occur vr Q = O ->
    derivable [[Phi ;; P]] Q ->
    derivable [[Phi ;; (∃ vr, P)]] Q
| PAnd_intros: forall Phi P Q,
    derivable Phi P ->
    derivable Phi Q ->
    derivable Phi [[P /\ Q]]
| PAnd_elim1: forall Phi P Q,
    derivable Phi [[P /\ Q]] ->
    derivable Phi P
| PAnd_elim2: forall Phi P Q,
    derivable Phi [[P /\ Q]] ->
    derivable Phi Q
| POr_intros1: forall Phi P Q,
    derivable [[Phi;; P]] [[P \/ Q]]
| POr_intros2: forall Phi P Q,
    derivable [[Phi;; Q]] [[P \/ Q]]
| POr_elim: forall Phi P Q R,
    derivable [[Phi;; P]] R ->
    derivable [[Phi;; Q]] R ->
    derivable [[Phi;; P \/ Q]] R
| PNot_EM: forall Phi P Q,
    derivable [[Phi;; P]] Q ->
    derivable [[Phi;; ¬ P]] Q ->
    derivable Phi Q
| PNot_Contra: forall Phi P Q,
    derivable [[Phi;; ¬ P]] Q ->
    derivable [[Phi;; ¬ P]] [[¬ Q]] ->
    derivable Phi P
| Assu: forall Phi P,
    derivable [[Phi ;; P]] P
| Weaken: forall (Phi Phi': context) P,
    (forall phi, Phi phi -> Phi' phi) ->
    derivable Phi P ->
    derivable Phi' P
| Modus_Ponens: forall Phi P Q,
    derivable Phi P ->
    derivable Phi [[P -> Q]] ->
    derivable Phi Q
| PImply_intros: forall Phi P Q,
    derivable [[Phi ;; P]] Q ->
    derivable Phi [[P -> Q]]
| PIff_intros: forall Phi P Q,
    derivable Phi [[P -> Q]] ->
    derivable Phi [[Q -> P]] ->
    derivable Phi [[P <-> Q]]
| PIff_elim1: forall Phi P Q,
    derivable Phi [[P <-> Q]] ->
    derivable Phi [[P -> Q]]
| PIff_elim2: forall Phi P Q,
    derivable Phi [[P <-> Q]]->
    derivable Phi [[Q -> P]]
| PEq_refl: forall (t: term),
    derivable empty_context [[t = t]]
| PEq_sub: forall P (x: V.t) (t t': term),
    derivable empty_context [[t = t' -> P[x |-> t] -> P[x |-> t'] ]]

| Empty:
    derivable empty_context [[is_empty ∅]]

| Union:
    derivable empty_context [[∀ x, ∀ y, ∀ z, z ∈ x ∪ y <-> z ∈ x \/ z ∈ y ]]
 
| Intersection_iff:
    derivable empty_context [[∀ x, ∀ y, ∀ z, z ∈ x ∩ y <-> z ∈ x /\ z ∈ y ]]

| Singleton:
    derivable empty_context [[∀x, ∀ z, z ∈ {x} <-> z = x]] 

| Extensionality:
    derivable empty_context
      [[∀ x, ∀ y, (∀ z, z ∈ x <-> z ∈ y) <-> x = y]]
              
| Pairing:
    derivable empty_context
      [[∀ x, ∀ y, ∃ z, ∀ u, u ∈ z <-> u = x \/ u = y]]

| Separation: forall Phi P,
    prop_free_occur x P = O ->
    prop_free_occur y P = O ->
    derivable Phi [[∀ x, ∃ y, ∀ z, z ∈ y <-> z ∈ x /\ P]]
    
| Union_iff:
    derivable empty_context
      [[∀ x, ∃ y, ∀ z, z ∈ y <-> ∃ u, z ∈ u /\ u ∈ x]]
                
| PowerSet:
    derivable empty_context
      [[∀ x, ∃ y, ∀ z, z ∈ y <-> z ⊆ x]]

| Infinity:
    derivable empty_context [[∃ x, is_inductive x]]

(*| Infinity2: forall Phi,
    derivable Phi
              (\exists x,
                (\exists y, is_empty y AND y \in x) AND
                (\forall y, y \in x -> \exists z, \exists u,
                   is_singleton z y AND is_union2 u y z AND u \in x))  *)

| Replacement: forall Phi P,
    prop_free_occur z P = O ->
    prop_free_occur u P = O ->
    derivable Phi
      [[ (∀ x, ∀ y, ∀ z, P [ y |-> (var2tm z) ] -> P -> y = z) ->
       (∀ u, ∃ z, ∀ y, y ∈ z <-> ∃ x, P /\ x ∈ u)]] 

| Choice:
    derivable empty_context
      [[∀ x,
              (∀ y, y ∈ x -> ¬ is_empty y) ->
              ∃ y, is_func y /\
                         ∀ z, z ∈ x -> ∃ u, in_rel z u y /\ u ∈ z]]

| Regularity:
    derivable empty_context
              [[∀ x,
              ¬ is_empty x ->
                  ∃ y, y ∈ x /\ ∀ z, z ∈ x -> ¬ z ∈ y]]
                  
| Alpha_congruence: forall Phi P Q,
   aeq P Q = true ->
   derivable Phi P -> 
   derivable Phi Q
.

End Rules.

Export Rules.

Notation "Phi  |--  P" := (derivable Phi P) (in custom set at level 41, no associativity).

Axiom PImply_elim: forall Phi P Q,
  [[ Phi |-- P-> Q]] ->
  [[ Phi;;P |-- Q]].

Axiom PNot_Contra': forall Phi P Q,
  [[Phi;;P |-- Q]] ->
  [[Phi;;P |-- ¬ Q]] ->
  [[Phi |-- ¬ P]].

Axiom Exfalso: forall Phi P Q,
   [[ Phi |-- P ]]->
   [[ Phi |-- ¬P]] ->
   [[ Phi |-- Q]].

Axiom PNot_elim: forall Phi P Q,
    [[Phi |-- ¬P]] ->
    [[Phi ;; P |-- Q]].
    

(* ***************************************************************** *)
(*                                                                   *)
(*                                                                   *)
(* Tauto tactic                                                      *)
(*                                                                   *)
(*                                                                   *)
(* ***************************************************************** *)

Definition denote_der (d: ToyDPLL.der_judgement): Prop :=
  derivable (fold_left (fun Phi p => @Ensembles.Union _ Phi (@Ensembles.Singleton _ p)) (fst d) empty_context) (snd d).

Definition denote_pg (pg: ToyDPLL.proof_goal): Prop :=
  fold_right (fun d P => denote_der d -> P: Prop) (denote_der (snd pg)) (fst pg).

Axiom dpll_sound: forall pg,
  ToyDPLL.valid (ToyDPLL.pg2prop pg) = true -> denote_pg pg.

Ltac reify_assu Phi l :=
  match Phi with
  | empty_context => constr:(l)
  | [[?Phi' ;; ?P]] => reify_assu Phi' constr:(P :: l)
  end.

Ltac reify_der P :=
  match P with
  | derivable ?Phi ?Q => let l := reify_assu Phi (@nil prop) in
                         constr:((l, Q))
  end.

Ltac reify_pg :=
  match goal with
  | |- ?P => let d := reify_der P in
             change (denote_pg (@nil ToyDPLL.der_judgement, d))
  end;
  repeat
  match goal with
  | H: ?P |- denote_pg (?l, ?d) =>
             let d0 := reify_der P in
             revert H;
             change (denote_pg (d0 :: l, d))
  end.

Ltac FOL_tauto :=
 try assumption; first
  [ reify_pg; apply dpll_sound; reflexivity
  | fail 1 "This is not an obvious tautology" ].

Notation "'ZF'" := empty_context (in custom set at level 20).

(* ***************************************************************** *)
(*                                                                   *)
(*                                                                   *)
(*  Derived Rules                                                    *)
(*                                                                   *)
(*                                                                   *)
(* ***************************************************************** *)

Axiom aeq_subst: forall P Q st,
  aeq P Q = true ->
  aeq (prop_sub st P) (prop_sub st Q) = true.

Axiom aeq_refl: forall P, aeq P P = true.

Axiom subst_subst: forall P st x t,
  (forall u, prop_free_occur u P > 0 -> In u (map fst st)) ->
  aeq
    (prop_sub ((x, t) :: nil) (prop_sub st P))
    (prop_sub (map (fun xt => (fst xt, (term_sub ((x, t) :: nil)) (snd xt))) st) P) = true.

Lemma subset_subst: forall (t1 t2: term) (x: V.t) t,
  aeq
    (prop_sub ((x, t) :: nil) (subset t1 t2))
    (subset (term_sub ((x, t) :: nil) t1) (term_sub ((x, t) :: nil) t2)) = true.
Proof.
  intros.
  unfold subset.
  apply (subst_subst [[ ∀ ShortNames.z, ShortNames.z ∈ ShortNames.x -> ShortNames.z ∈ ShortNames.y ]]).
  intros.
  simpl in H.
  destruct (V.eq_dec u ShortNames.z); [inversion H |].
  destruct (V.eq_dec u ShortNames.x); [simpl; subst u; tauto |].
  destruct (V.eq_dec u ShortNames.y); [simpl; subst u; tauto |].
  inversion H.
Qed.

Axiom Separation_aux: forall Phi (x y z: V.t) P, 
    prop_free_occur x P = O ->
    prop_free_occur y P = O ->
    derivable Phi [[∀ x, ∃ y, ∀ z, z ∈ y <-> z ∈ x /\ P]].

Corollary Alpha_congruence_A: forall Phi P1 P2 Q,
  aeq P1 P2= true ->
  derivable [[Phi;; P1]] Q ->
  derivable [[Phi;; P2]] Q.
Proof.
  intros. apply PImply_elim.
  apply Alpha_congruence with [[P1->Q]].
  unfold aeq. simpl. unfold aeq in H. rewrite H. rewrite aeq_refl. reflexivity.
  apply PImply_intros, H0.
Qed.



(* ***************************************************************** *)
(*                                                                   *)
(*                                                                   *)
(*  Tactics                                                    *)
(*                                                                   *)
(*                                                                   *)
(* ***************************************************************** *)

Ltac get_new_var P x t x1 :=
  let b := eval compute in (V.eqb x x1) in
  match b with
  | true => let x2 := eval compute in (V.next_name x1) in
            get_new_var P x t x2
  | false =>
        let c := eval compute in (term_occur x1 t) in
        match c with
        | S _ => let x2 := eval compute in (V.next_name x1) in
                 get_new_var P x t x2
        | _ => let c' := eval compute in (prop_free_occur x1 P) in
               match c' with
               | S _ => let x2 := eval compute in (V.next_name x1) in
                        get_new_var P x t x2
               | _ => constr:(x1)
               end
        end
  end.

(***  More predicates notations needed ***)
Ltac special_tac P x t :=
 match P with
  | subset ?t1 ?t2 =>
      let t3 := eval compute in (term_sub ((x,t):: nil) t1) in
      let t4 := eval compute in (term_sub ((x,t):: nil) t2) in
      constr:(subset t3 t4)
  | [[ is_singleton ?t1 ?t2]] =>
      let t3 := eval compute in (term_sub ((x,t):: nil) t1) in
      let t4 := eval compute in (term_sub ((x,t):: nil) t2) in
      constr:([[ is_singleton t3 t4]] )
  | [[ has_two_ele ?t1 ?t2 ?t3 ]] =>
      let t5 := eval compute in (term_sub ((x,t):: nil) t1) in
      let t6 := eval compute in (term_sub ((x,t):: nil) t2) in
      let t7 := eval compute in (term_sub ((x,t):: nil) t3) in
      constr:([[ has_two_ele t5 t6 t7 ]])
  | [[ is_inductive ?t1 ]] =>
      let t3 := eval compute in (term_sub ((x,t):: nil) t1) in
      constr:([[is_inductive t3 ]])
  | [[ is_natural_number ?t1 ]] =>
      let t3 := eval compute in (term_sub ((x,t):: nil) t1) in
      constr:([[ is_natural_number t3 ]])
  | [[ is_empty ?t1 ]] =>
      let t3 := eval compute in (term_sub ((x,t):: nil) t1) in
      constr:([[ is_empty t3 ]])
  | [[ is_pair ?t1 ?t2 ?t3 ]] =>
      let t5 := eval compute in (term_sub ((x,t):: nil) t1) in
      let t6 := eval compute in (term_sub ((x,t):: nil) t2) in
      let t7 := eval compute in (term_sub ((x,t):: nil) t3) in
      constr:([[ is_pair t5 t6 t7 ]])
  | [[ in_rel ?t1 ?t2 ?t3 ]] =>
      let t5 := eval compute in (term_sub ((x,t):: nil) t1) in
      let t6 := eval compute in (term_sub ((x,t):: nil) t2) in
      let t7 := eval compute in (term_sub ((x,t):: nil) t3) in
      constr:([[ in_rel t5 t6 t7 ]])
  | [[ is_triple ?t1 ?t2 ?t3 ?t4 ]] =>
      let t5 := eval compute in (term_sub ((x,t):: nil) t1) in
      let t6 := eval compute in (term_sub ((x,t):: nil) t2) in
      let t7 := eval compute in (term_sub ((x,t):: nil) t3) in
      let t8 := eval compute in (term_sub ((x,t):: nil) t4) in
      constr:([[ is_triple t5 t6 t7 t8 ]])
  | [[ in_rel3 ?t1 ?t2 ?t3 ?t4 ]] =>
      let t5 := eval compute in (term_sub ((x,t):: nil) t1) in
      let t6 := eval compute in (term_sub ((x,t):: nil) t2) in
      let t7 := eval compute in (term_sub ((x,t):: nil) t3) in
      let t8 := eval compute in (term_sub ((x,t):: nil) t4) in
      constr:([[ in_rel3 t5 t6 t7 t8 ]])
  | [[ is_legal_plus ?t1 ?t2 ]] =>
      let t3 := eval compute in (term_sub ((x,t):: nil) t1) in
      let t4 := eval compute in (term_sub ((x,t):: nil) t2) in
      constr:([[ is_legal_plus t3 t4 ]])
  | [[ is_plus ?t1 ?t2 ]] =>
      let t3 := eval compute in (term_sub ((x,t):: nil) t1) in
      let t4 := eval compute in (term_sub ((x,t):: nil) t2) in
      constr:([[ is_plus t3 t4 ]])
  | [[ is_legal_mult ?t1 ?t2 ?t3 ]] =>
      let t5 := eval compute in (term_sub ((x,t):: nil) t1) in
      let t6 := eval compute in (term_sub ((x,t):: nil) t2) in
      let t7 := eval compute in (term_sub ((x,t):: nil) t3) in
      constr:([[ is_legal_mult t5 t6 t7 ]])
  | [[ is_mult ?t1 ?t2 ?t3 ]] =>
      let t5 := eval compute in (term_sub ((x,t):: nil) t1) in
      let t6 := eval compute in (term_sub ((x,t):: nil) t2) in
      let t7 := eval compute in (term_sub ((x,t):: nil) t3) in
      constr:([[ is_mult t5 t6 t7 ]])
  end.

Ltac subst_aeq_constr_tac P x t :=
  match P with
  | PEq ?t1 ?t2 =>
      let t3 := eval compute in (term_sub ((x,t):: nil) t1) in
      let t4 := eval compute in (term_sub ((x,t):: nil) t2) in
      constr:(PEq t3 t4)
  | PRel ?t1 ?t2 =>
      let t3 := eval compute in (term_sub ((x,t):: nil) t1) in
      let t4 := eval compute in (term_sub ((x,t):: nil) t2) in
      constr:(PRel t3 t4)
  | PFalse => constr:(PFalse)
  | PTrue => constr:(PTrue)
  | PNot ?P1 =>
      let Q1 := subst_aeq_constr_tac P1 x t in
      constr:(PNot Q1)
  | PAnd ?P1 ?P2 =>
      let Q1 := subst_aeq_constr_tac P1 x t in
      let Q2 := subst_aeq_constr_tac P2 x t in
      constr:(PAnd Q1 Q2)
  | POr ?P1 ?P2 =>
      let Q1 := subst_aeq_constr_tac P1 x t in
      let Q2 := subst_aeq_constr_tac P2 x t in
      constr:(POr Q1 Q2)
  | PImpl ?P1 ?P2 =>
      let Q1 := subst_aeq_constr_tac P1 x t in
      let Q2 := subst_aeq_constr_tac P2 x t in
      constr:(PImpl Q1 Q2)
  | PIff ?P1 ?P2 =>
      let Q1 := subst_aeq_constr_tac P1 x t in
      let Q2 := subst_aeq_constr_tac P2 x t in
      constr:(PIff Q1 Q2)
  | PForall ?x1 ?P1 =>
      let b := eval compute in (V.eqb x x1) in
      match b with
      | true => constr:(PForall x1 P1)
      | false =>
          let c := eval compute in (term_occur x1 t) in
          match c with
          | O => let Q1 := subst_aeq_constr_tac P1 x t in
                 constr:(PForall x1 Q1)
          | _ => let x2 := get_new_var P x t constr:(V.next_name x1) in
                 let Q1 := subst_aeq_constr_tac P1 x1 constr:(var x2) in
                 let Q2 := subst_aeq_constr_tac Q1 x t in
                 constr:(PForall x2 Q2)
          end
      end
  | PExists ?x1 ?P1 =>
      let b := eval compute in (V.eqb x x1) in
      match b with
      | true => constr:(PExists x1 P1)
      | false =>
          let c := eval compute in (term_occur x1 t) in
          match c with
          | O => let Q1 := subst_aeq_constr_tac P1 x t in
                 constr:(PExists x1 Q1)
          | _ => let x2 := get_new_var P x t constr:(V.next_name x1) in
                 let Q1 := subst_aeq_constr_tac P1 x1 constr:(var x2) in
                 let Q2 := subst_aeq_constr_tac Q1 x t in
                 constr:(PExists x2 Q2)
          end
      end
  | _ => special_tac P x t
  end.



Ltac custom_hnf P :=
  match P with
  | subset ?t1 ?t2 =>
      let P1 := eval hnf in P in
      let P2 := eval simpl in P1 in
          constr:(P2)
  | [[is_inductive ?t1]] =>
      let P1 := eval hnf in P in
      let P2 := eval simpl in P1 in
          constr:(P2)
  | [[is_natural_number ?t1]] =>
      let P1 := eval hnf in P in
      let P2 := eval simpl in P1 in
          constr:(P2)
  | [[is_empty ?t1]] =>
      let P1 := eval hnf in P in
      let P2 := eval simpl in P1 in
          constr:(P2)
  | _ => constr:(P)
  end.

Ltac aeq_constr_tac P ts :=
  match ts with
  | nil => constr:(P)
  | cons ?t ?ts0 =>
      let P' := custom_hnf  P in
      match P' with
      | PForall ?x ?Q => let Q0 := subst_aeq_constr_tac Q x t in
                         aeq_constr_tac Q0 ts0
      end
  end.

Fixpoint compute_forall_inst (P: prop) (ts: list term): prop :=
  match ts with
  | nil => P
  | t :: ts0 =>
    match P with
    | [[∀ x, P0]] => compute_forall_inst (prop_sub ((x, t):: nil) P0) ts0
    | _ => P
    end
  end.

Fixpoint compute_forall_check (P: prop) (ts: list term): bool :=
  match ts with
  | nil => true
  | t :: ts0 =>
    match P with
    |[[∀ x, P0]]  => compute_forall_check (prop_sub ((x, t):: nil) P0) ts0
    | _ => false
    end
  end.

Lemma universal_instantiation_tac_aux: forall {Phi P} (H: [[Phi |-- P]]) (ts: list term),
  derivable  Phi  (compute_forall_inst P ts).
Proof.
  intros.
  revert P H; induction ts; simpl; intros.
  + auto.
  + destruct P; auto.
    apply IHts.
    apply PForall_elim, H.
Qed.

Ltac universal_instantiation_tac H ts :=
  first
  [ let H0 := fresh "H" in
    match type of H with
    | [[_ |-- ?P]] => unify (compute_forall_check P ts) true;
    let Q := aeq_constr_tac P ts in
    pose proof Alpha_congruence _ _ _ (@eq_refl _ true: (aeq (compute_forall_inst P ts) Q = true)) (universal_instantiation_tac_aux H ts) as H0
    end;
    repeat
    match type of H0 with
    | context [new_var ?P ?st] =>
        let x := eval compute in (new_var P st) in
        change (new_var P st) with x in H0
    end; 
    ShortNames.super_fold_in H0
  | fail 1 "Universal instantiation fails"].

Tactic Notation "universal" "instantiation" constr(H) constr(t0) :=
  universal_instantiation_tac H (@cons term (t0: term) nil).

Tactic Notation "universal" "instantiation" constr(H) constr(t0) constr(t1) :=
  universal_instantiation_tac H (@cons term (t0: term) (cons (t1: term) nil)).

Tactic Notation "universal" "instantiation" constr(H) constr(t0) constr(t1) constr(t2) :=
  universal_instantiation_tac H (@cons term (t0: term) (cons (t1: term) (cons (t2: term) nil))).

Tactic Notation "universal" "instantiation" constr(H) constr(t0) constr(t1) constr(t2) constr(t3) :=
  universal_instantiation_tac H (@cons term (t0: term) (cons (t1: term) (cons (t2: term) (cons (t3: term) nil)))).

Tactic Notation "universal" "instantiation" constr(H) constr(t0) constr(t1) constr(t2) constr(t3) constr(t4) :=
  universal_instantiation_tac H (@cons term (t0: term) (cons (t1: term) (cons (t2: term) (cons (t3: term) (cons (t4: term) nil))))).

Tactic Notation "universal" "instantiation" constr(H) constr(t0) constr(t1) constr(t2) constr(t3) constr(t4) constr(t5) :=
  universal_instantiation_tac H (@cons term (t0: term) (cons (t1: term) (cons (t2: term) (cons (t3: term) (cons (t4: term) (cons (t5: term) nil)))))).

Tactic Notation "universal" "instantiation" constr(H) constr(t0) constr(t1) constr(t2) constr(t3) constr(t4) constr(t5) constr(t6) :=
  universal_instantiation_tac H (@cons term (t0: term) (cons (t1: term) (cons (t2: term) (cons (t3: term) (cons (t4: term) (cons (t5: term) (cons (t6: term) nil))))))).

Ltac check_free_occurrence :=
  first
  [ let H := fresh "H" in
    let phi := fresh "phi" in
    intros phi H; simpl in H;
    repeat (rewrite Union_spec, Singleton_spec in H; destruct H as [H | H]);
    [inversion H | subst phi; reflexivity ..]
  | fail 1 "Free occurrence check fails"].

Ltac universal_generalization_constr H xs :=
  match xs with
  | nil => constr:(H)
  | ?x :: ?xs0 =>
      match type of H with
      | [[?Phi |-- ?P]] =>
          let H0 := constr:(PForall_intros Phi x P ltac:(check_free_occurrence) H) in
          universal_generalization_constr H0 xs0
      end
  end.

Ltac universal_generalization H xs :=
  first
  [ let H0 := universal_generalization_constr H xs in
    pose proof H0
  | fail 1 "Universal generalization fails"].

Tactic Notation "universal" "generalization" constr(H) constr(X0) :=
  universal_generalization H (@cons V.t X0 nil).

Tactic Notation "universal" "generalization" constr(H) constr(X0) constr(X1) :=
  universal_generalization H (@cons V.t X1 (@cons V.t X0 nil)).

Tactic Notation "universal" "generalization" constr(H) constr(X0) constr(X1) constr(X2) :=
  universal_generalization H (@cons V.t X2 (@cons V.t X1 (@cons V.t X0 nil))).

Tactic Notation "universal" "generalization" constr(H) constr(X0) constr(X1) constr(X2) constr(X3) :=
  universal_generalization H (@cons V.t X3 (@cons V.t X2 (@cons V.t X1 (@cons V.t X0 nil)))).

Tactic Notation "universal" "generalization" constr(H) constr(X0) constr(X1) constr(X2) constr(X3) constr(X4) :=
  universal_generalization H (@cons V.t X4 (@cons V.t X3 (@cons V.t X2 (@cons V.t X1 (@cons V.t X0 nil))))).

Tactic Notation "universal" "generalization" constr(H) constr(X0) constr(X1) constr(X2) constr(X3) constr(X4) constr(X5) :=
  universal_generalization H (@cons V.t X5 (@cons V.t X4 (@cons V.t X3 (@cons V.t X2 (@cons V.t X1 (@cons V.t X0 nil)))))).
  
Fixpoint term_eqb (t1 t2:term):bool:=
  match t1, t2 with
  | empty_set, empty_set => true
  | var a, var b => if V.eq_dec a b then true else false
  | union a b, union x y 
  | intersection a b, union x y => term_eqb a x && term_eqb b y
  | singleton a, singleton b => term_eqb a b
  | _ , _ => false
  end.
  
Ltac check_result_tac ts:=
  match ts with
  | nil => constr:(@None term)
  | ?ot::nil => constr:(ot)
  | ?ot1::?ot2:: ?ots => match ot1 with
                                 | None =>  check_result_tac (ot2::ots)
                                 | Some ?t1 => match ot2 with
                                                      | None=>  check_result_tac (ot1::ots)
                                                      | Some ?t2 => let b:= eval compute in (term_eqb t1 t2) in
                                                        match b with
                                                        | true =>  check_result_tac (ot2::ots)
                                                        end end end
  end.

Ltac compare_term_tac vr t1 t2:=
  match t1 with
  | var ?v => let b:= eval compute in (V.eqb v vr) in
        match b with
        | true => constr:(Some t2)
        | false => constr:(@None term)
        end
  | empty_set => match t2 with | empty_set => constr:(@None term) end
  | union ?a ?b => match t2 with | union ?x ?y => 
        let ot1:= compare_term_tac vr a x in
        let ot2:= compare_term_tac vr b y in
        check_result_tac (ot1::ot2::(@nil (option term)))
        end
  | intersection ?a ?b => match t2 with | intersection ?x ?y => 
        let ot1:= compare_term_tac vr a x in
        let ot2:= compare_term_tac vr b y in
        check_result_tac (ot1::ot2::(@nil (option term)))
        end
  | singleton ?a => match t2 with | singleton ?b => compare_term_tac vr a b end
  end.

Ltac compare_prop_special_tac vr p1 p2:= 
  match p1 with
  | subset ?t1 ?t2 => match p2 with |  subset ?t3 ?t4 =>
          let ot1:= compare_term_tac vr t1 t3 in
          let ot2:= compare_term_tac vr t2 t4 in
          check_result_tac (ot1::ot2::(@nil (option term)))  end    
  | [[is_singleton ?t1 ?t2]] => match p2 with | [[is_singleton ?t3 ?t4]] =>
          let ot1:= compare_term_tac vr t1 t3 in
          let ot2:= compare_term_tac vr t2 t4 in
          check_result_tac (ot1::ot2::(@nil (option term)))  end    
  | [[has_two_ele ?t1 ?t2 ?t3]] => match p2 with | [[has_two_ele ?t5 ?t6 ?t7]] =>
          let ot1:= compare_term_tac vr t1 t5 in
          let ot2:= compare_term_tac vr t2 t6 in
          let ot3:= compare_term_tac vr t3 t7 in
          check_result_tac (ot1::ot2::ot3::(@nil (option term)))  end    
  | [[is_inductive ?t1]] => match p2 with | [[is_inductive ?t2]] =>
         compare_term_tac vr t1 t2 end
  | [[is_natural_number ?t1]] => match p2 with | [[is_natural_number ?t2]] =>
         compare_term_tac vr t1 t2 end
  | [[is_empty ?t1]] => match p2 with | [[is_empty ?t2]] =>
         compare_term_tac vr t1 t2 end
  | [[is_pair ?t1 ?t2 ?t3]] => match p2 with | [[is_pair ?t5 ?t6 ?t7]] =>
          let ot1:= compare_term_tac vr t1 t5 in
          let ot2:= compare_term_tac vr t2 t6 in
          let ot3:= compare_term_tac vr t3 t7 in
          check_result_tac (ot1::ot2::ot3::(@nil (option term)))  end  
  | [[in_rel ?t1 ?t2 ?t3]] => match p2 with | [[in_rel ?t5 ?t6 ?t7]] =>
          let ot1:= compare_term_tac vr t1 t5 in
          let ot2:= compare_term_tac vr t2 t6 in
          let ot3:= compare_term_tac vr t3 t7 in
          check_result_tac (ot1::ot2::ot3::(@nil (option term)))  end 
  | [[is_triple ?t1 ?t2 ?t3 ?t4]] => match p2 with | [[is_triple ?t5 ?t6 ?t7 ?t8]] =>
          let ot1:= compare_term_tac vr t1 t5 in
          let ot2:= compare_term_tac vr t2 t6 in
          let ot3:= compare_term_tac vr t3 t7 in
          let ot4:= compare_term_tac vr t4 t8 in
          check_result_tac (ot1::ot2::ot3::ot4::(@nil (option term)))  end   
  | [[in_rel3 ?t1 ?t2 ?t3 ?t4]] => match p2 with | [[in_rel3 ?t5 ?t6 ?t7 ?t8]] =>
          let ot1:= compare_term_tac vr t1 t5 in
          let ot2:= compare_term_tac vr t2 t6 in
          let ot3:= compare_term_tac vr t3 t7 in
          let ot4:= compare_term_tac vr t4 t8 in
          check_result_tac (ot1::ot2::ot3::ot4::(@nil (option term)))  end   
  | [[is_legal_plus ?t1 ?t2]] => match p2 with |  [[is_legal_plus ?t3 ?t4]] =>
          let ot1:= compare_term_tac vr t1 t3 in
          let ot2:= compare_term_tac vr t2 t4 in
          check_result_tac (ot1::ot2::(@nil (option term)))  end    
  | [[is_plus ?t1 ?t2]] => match p2 with |  [[is_plus ?t3 ?t4]] =>
          let ot1:= compare_term_tac vr t1 t3 in
          let ot2:= compare_term_tac vr t2 t4 in
          check_result_tac (ot1::ot2::(@nil (option term)))  end  
  | [[is_legal_mult ?t1 ?t2 ?t3]] => match p2 with | [[is_legal_mult ?t5 ?t6 ?t7]] =>
          let ot1:= compare_term_tac vr t1 t5 in
          let ot2:= compare_term_tac vr t2 t6 in
          let ot3:= compare_term_tac vr t3 t7 in
          check_result_tac (ot1::ot2::ot3::(@nil (option term)))  end 
  | [[is_mult ?t1 ?t2 ?t3]] => match p2 with | [[is_mult ?t5 ?t6 ?t7]] =>
          let ot1:= compare_term_tac vr t1 t5 in
          let ot2:= compare_term_tac vr t2 t6 in
          let ot3:= compare_term_tac vr t3 t7 in
          check_result_tac (ot1::ot2::ot3::(@nil (option term)))  end 
  end.
  

Ltac compare_prop_tac vr p1 p2:=
  match p1 with
  | PEq ?t1 ?t2 => match p2 with  | PEq ?t3 ?t4 => 
          let ot1:= compare_term_tac vr t1 t3 in
          let ot2:= compare_term_tac vr t2 t4 in
          check_result_tac (ot1::ot2::(@nil (option term)))  end                    
  | PRel ?t1 ?t2 => match p2 with   | PRel ?t3 ?t4 => 
          let ot1:= compare_term_tac vr t1 t3 in
          let ot2:= compare_term_tac vr t2 t4 in
          check_result_tac (ot1::ot2::(@nil (option term)))  end  
  | PFalse => match p2 with  | PFalse => constr:(@None term)  end
  | PTrue => match p2 with   | PTrue => constr:(@None term)  end
  | PNot ?P1 => match p2 with | PNot ?P2 => compare_prop_tac vr P1 P2 end
  | PAnd ?P1 ?P2 => match p2 with | PAnd ?P3 ?P4 =>
          let ot1:= compare_prop_tac vr P1 P3 in
          let ot2:= compare_prop_tac vr P2 P4 in
          check_result_tac (ot1::ot2::(@nil (option term)))  end
  | POr ?P1 ?P2 => match p2 with | POr ?P3 ?P4 =>
          let ot1:= compare_prop_tac vr P1 P3 in
          let ot2:= compare_prop_tac vr P2 P4 in
          check_result_tac (ot1::ot2::(@nil (option term)))  end   
  | PImpl ?P1 ?P2 => match p2 with | PImpl ?P3 ?P4 =>
          let ot1:= compare_prop_tac vr P1 P3 in
          let ot2:= compare_prop_tac vr P2 P4 in
          check_result_tac (ot1::ot2::(@nil (option term)))  end 
  | PIff ?P1 ?P2 => match p2 with | PIff ?P3 ?P4 =>
          let ot1:= compare_prop_tac vr P1 P3 in
          let ot2:= compare_prop_tac vr P2 P4 in
          check_result_tac (ot1::ot2::(@nil (option term)))  end 
  | PForall ?x ?P1 => let b:= eval compute in (V.eqb x vr) in
        match b with
        | true => constr:(@None term)
        | false => match p2 with | PForall ?y ?P2 => compare_prop_tac vr P1 P2 end
        end
   | PExists ?x ?P1 => let b:= eval compute in (V.eqb x vr) in
        match b with
        | true => constr:(@None term)
        | false => match p2 with | PExists ?y ?P2 => compare_prop_tac vr P1 P2 end
        end
   | _ => compare_prop_special_tac vr p1 p2
  end.

Ltac search_subst_term_tac xs P Q:=
 match xs with
 | nil => constr:(@nil term)
 | ?x::?xs0 => let ot:= compare_prop_tac x P Q in
                   match ot with
                   | Some ?t => let ots:= search_subst_term_tac xs0 P Q in
                     constr:(t::ots)
                   end
 end.
 
Ltac count_exists_tac P:=
  match P with
  | [[∃ ?x, ?Q]] => let n:= count_exists_tac Q in constr:(S n)
  | _ => constr:(O)
  end.
  
Ltac extract_exists_tac P n:=
  match n with
  | O => constr:(@nil V.t)
  | S ?m => match P with
                  |  [[∃ ?x, ?Q]]  => let xs:= extract_exists_tac Q m in
                      constr:(x::xs)
                  | _ => constr:(@nil V.t)
                  end
 end.
 
Ltac remove_exists_tac P n:=
 match n with
  | O => constr:(P)
  | S ?m => match P with
                  | [[∃ ?x, ?Q]] => remove_exists_tac Q m
                  | _ => constr:(P)
                  end 
 end.
 
 Ltac generate_exists_term_tac P Q:=
  let np:= count_exists_tac P in 
  let nq:= count_exists_tac Q in 
  let n:= eval compute in (np-nq) in
  let xs:= extract_exists_tac P n in
  let P':= remove_exists_tac P n in 
  search_subst_term_tac xs P' Q .

Fixpoint compute_exists_inst (P: prop) (ts: list term): prop :=
  match ts with
  | nil => P
  | t :: ts0 =>
    match P with
    | [[∃ x, P0]] => compute_exists_inst (prop_sub ((x, t):: nil) P0) ts0
    | _ => P
    end
  end.

Lemma existential_generalization_tac_aux: forall {Phi P} (ts: list term)(H: derivable  Phi  (compute_exists_inst P ts)) ,
  [[Phi |-- P]].
Proof.
  intros.
  revert P H; induction ts; simpl; intros.
  + auto. 
  + destruct P; auto. eapply PExists_intros.
      apply IHts, H.
Qed.

Ltac existential_generalization_tac H P :=
 first [  
    let H0:= fresh "H" in
    match type of H with
     | [[?Phi |-- ?Q]] => first [ let ts:= generate_exists_term_tac P Q in
                                   assert [[Phi |--  P]] as H0;[apply (existential_generalization_tac_aux ts); 
                                   apply Alpha_congruence with Q; cbv; easy|] | idtac "Cannot infer the terms to be quantified in" H ; fail]
    end;
    repeat
    match type of H0 with
    | context [new_var ?P ?st] =>
        let x := eval compute in (new_var P st) in
        change (new_var P st) with x in H0
    end;
    ShortNames.super_fold_in H0  |
    fail 1 "Existential generalization fails"].


Tactic Notation "existential" "generalization" constr(H) constr(P):=
   existential_generalization_tac H P.

Ltac use_separation_tac P:=
first [  
  let H0:= fresh "H" in
  let H1:= fresh "H" in
  match P with
  | PExists ?y (PForall ?z (PIff (PRel (var ?z) (var ?y)) (PAnd (PRel (var ?z) ?t) ?Q ))) =>
      let ny:= eval compute in (prop_free_occur y Q) in
      let x':= get_new_var P ShortNames.x [[∅]] ShortNames.x in (
      match ny with
      | O => idtac
      | S _ => idtac y "should not freely occur in" Q"."; fail
      end;
      pose proof (Separation_aux [[ZF]] x' y z Q eq_refl eq_refl ) as H1 ;
      universal instantiation H1 t; clear H1; ShortNames.super_fold_in H0) 
  | _ => idtac "Your proposition does not match the form of separation axiom"; fail
  end |
  fail 1 "Applying separation axiom fails"] .

Tactic Notation "apply" "separation" constr(P):= use_separation_tac P.
  
Ltac assu_length Phi :=
  match Phi with
  | empty_context  => constr:(O)
  | [[?Phi';;?P]] => let n:= assu_length Phi' in constr:(S n)
  end.   
 
Local Ltac nth_assu_aux Phi n :=
  match n with
  | O => match Phi with
              | empty_context => empty_context
              | [[?Phi';;?Q]] => Q
             end
  | S ?n' => match Phi with
                 | empty_context => empty_context
                 | [[?Phi';;?Q]] => nth_assu_aux Phi' n'
                end
  end.
  
Ltac nth_assu Phi n:=
  let m:= assu_length Phi in
  let r:= eval compute in (m - n) in
  nth_assu_aux Phi r.
  
Local Ltac remove_nth_assu_aux Phi n:=
  match n with
  | O => match Phi with
              | empty_context => empty_context
              | [[?Phi';; ?P]] => Phi'
              end
  | S ?n' => match Phi with
                  | empty_context => empty_context
                  | [[?Phi';; ?P]] => let Phi'':= remove_nth_assu_aux Phi'  n' in 
                                               constr:([[Phi'';;P]])
                  end
  end.
  
Ltac remove_nth_assu Phi n:=
  let m:= assu_length Phi in
  let r:= eval compute in (m-n) in
  remove_nth_assu_aux Phi r.
  
Local Ltac check_in_context_aux Phi P:=
 match Phi with
 | empty_context => idtac P "not in context"; fail
 | [[?Phi' ;; ?U]] => match U with
                              | P => right; constructor
                              | _ => left; check_in_context_aux Phi' P
                              end
end.
  
Ltac check_in_context:=
  match goal with
  | |- ?Phi ?P => check_in_context_aux Phi P
  end.  

Fixpoint add_existential_quantifier (P:prop) (vr:list V.t): prop:=
  match vr with
  | nil => P
  | v::vs => PExists v (add_existential_quantifier P vs)
  end.
  
Fixpoint extract_var_list (ts: list term): list V.t:=
  match ts with
  | nil => nil
  | t::ts0 => match t with
                   | var v => v::(extract_var_list ts0)
                   | _ => extract_var_list ts0
                   end
  end.


Lemma existential_instantiation_tac_aux: forall (Phi: context) P Q (vs: list V.t) ,
  (forall vr, In vr vs -> (forall phi : prop, Phi phi -> prop_free_occur vr phi = 0)) ->
  (forall vr, In vr vs -> prop_free_occur vr Q = 0) ->
  [[Phi;; P |-- Q]] ->
  derivable (Ensembles.Union prop Phi (Ensembles.Singleton prop (add_existential_quantifier P vs))) Q .
Proof.
  intros.
  revert P H H0 H1; induction vs;intros.
  + auto. 
  + simpl.  apply PExists_elim. 
      apply H. now left.
      apply H0. now left.
      apply IHvs; intros. 
      apply H. now right.
      easy. apply H0. now right. easy.
Qed.

Ltac aeq_constr_tac_exists P ts :=
  match ts with
  | nil => constr:(P)
  | cons ?t ?ts0 =>
      let P' := custom_hnf  P in
      match P' with
      | PExists ?x ?Q => let Q0 := subst_aeq_constr_tac Q x t in
                         aeq_constr_tac_exists Q0 ts0
      end
  end.

Ltac add_existential_quantifier_tac P vs:=
  match vs with
  | nil => constr:(P)
  | cons ?v ?vs0 => add_existential_quantifier_tac constr:(PExists v P) vs0
  end.

Ltac existential_instantiation_tac_from_conclusion n vrs:=
  first [  
  match goal with
  | |- [[?Phi |-- ?Q]] =>
      let H:= fresh "H" in
      let H0:= fresh "H" in
      let phi:= fresh "phi" in
      let v:= fresh "v" in
      let rvrs:= eval simpl rev in (rev vrs) in
      let l:= eval compute in (length vrs) in
      let vs := eval simpl  in (rev (map var vrs)) in
      let p:= nth_assu Phi n in
      let d:= aeq_constr_tac_exists p vs in 
      let q:= add_existential_quantifier_tac d vrs in 
      let Phi':= remove_nth_assu Phi n in 
        pose proof (Weaken [[Phi';;p]] Phi Q) as H; ShortNames.super_fold_in H; 
        apply H ; [intros phi H0;repeat (rewrite Union_spec, Singleton_spec in H0; destruct H0 as [H0 | H0]);
        [inversion H0| subst phi; check_in_context..]| ..]; clear H;
        pose proof (Alpha_congruence_A Phi' q p Q) as H; ShortNames.super_fold_in H;
        apply H; [reflexivity|clear H] ; 
        match goal with
        |- [[ ?Phi'' |-- _]] => 
          let n':= assu_length Phi'' in 
          let q':= nth_assu Phi'' n' in 
          let d':= remove_exists_tac q' l in
          apply (existential_instantiation_tac_aux Phi' d' Q rvrs);
          [intros v H; repeat (destruct H as [H|H]);[subst v; intros phi H0; 
          repeat (rewrite Union_spec, Singleton_spec in H0; destruct H0 as [H0 | H0]);
          [inversion H0| subst phi; first [reflexivity | idtac "Some variable freely occurs in other propositions"; fail].. ]..|inversion H ] 
          | intros v H; repeat (destruct H as [H|H]);[subst v; first [reflexivity | idtac "Some variable freely occurs in conclusion"; fail]..| inversion H ] | 
          ]  
        end
  end 
  |  fail 1 "existential instantiation fails"] .
 
Ltac existential_instantiation_search_assu Phi P n default:=
  match Phi with
  | empty_context => constr:(default)
  | [[?Phi';;?Q]] =>  let vs:= generate_exists_term_tac P Q in constr:((n,vs))
  | _ => match Phi with [[?Phi';;?Q]] => 
      let predn:= eval compute in (pred n) in  existential_instantiation_search_assu Phi' P predn default
 end end.

Ltac existential_instantiation_tac H' P:=
first [  match type of H' with
  | [[?Phi |-- ?Q]] => 
          let H:= fresh "H" in
          let H0:= fresh "H" in
          let H1:= fresh "H" in
          let phi:= fresh "phi" in
          let v:= fresh "v" in
          let len:= assu_length Phi in
          let os:= existential_instantiation_search_assu Phi P len (O, (@nil term)) in 
          let n:= eval simpl fst in (fst os) in
          let vrs0:= eval simpl snd in (snd os) in
          let p:= nth_assu Phi n in
          match n with
            | S _ =>  let vs0:= eval compute in (extract_var_list vrs0) in 
                                        let Phi':= remove_nth_assu Phi n in
                                        assert [[Phi';;p |-- Q]] as H ; [ FOL_tauto| ] ; 
                                        apply existential_instantiation_tac_aux with (vs:=vs0) in H;[ simpl in H; ShortNames.super_fold_in H
                                        | intros v H0; ShortNames.super_fold_in H0; repeat (destruct H0 as [H0 | H0]);
                                          [ subst v; intros phi H1;repeat (rewrite Union_spec, Singleton_spec in H1; destruct H1 as [H1 | H1]);
                                           [ inversion H1| subst phi; first [reflexivity | idtac "Some variable freely occurs in other propositions in" H'; fail] ..] .. | inversion H0] 
                                        | intros v H0; ShortNames.super_fold_in H0;repeat (destruct H0 as [H0 | H0]);
                                            [ subst v;  first [reflexivity | idtac "Some variable freely occurs in conclusion"; fail] ..|inversion H0]
                                        ] ; apply Alpha_congruence_A with (P2:=P) in H; [| reflexivity]
           end  
  end  | fail 1 "existential instantiation fails" ] .


Tactic Notation "existential" "instantiation"  constr(n) constr(X0) :=
  match type of n with
  | nat => existential_instantiation_tac_from_conclusion n (@cons V.t X0 nil)
  | derivable _ _ => existential_instantiation_tac n X0
  end.

Tactic Notation "existential" "instantiation" constr(n) constr(X0) constr(X1) :=
 existential_instantiation_tac_from_conclusion n (@cons V.t X1 (@cons V.t X0 nil)).
  
Tactic Notation "existential" "instantiation" constr(n) constr(X0) constr(X1) constr(X2) :=
  existential_instantiation_tac_from_conclusion n (@cons V.t X2 (@cons V.t X1 (@cons V.t X0 nil))).

Tactic Notation "existential" "instantiation" constr(n) constr(X0) constr(X1) constr(X2) constr(X3) :=
  existential_instantiation_tac_from_conclusion n (@cons V.t X3 (@cons V.t X2 (@cons V.t X1 (@cons V.t X0 nil)))).

Tactic Notation "existential" "instantiation" constr(n) constr(X0) constr(X1) constr(X2) constr(X3) constr(X4) :=
  existential_instantiation_tac_from_conclusion n (@cons V.t X4 (@cons V.t X3 (@cons V.t X2 (@cons V.t X1 (@cons V.t X0 nil))))).

Tactic Notation "existential" "instantiation" constr(n) constr(X0) constr(X1) constr(X2) constr(X3) constr(X4) constr(X5) :=
  existential_instantiation_tac_from_conclusion n (@cons V.t X5 (@cons V.t X4 (@cons V.t X3 (@cons V.t X2 (@cons V.t X1 (@cons V.t X0 nil)))))).

Tactic Notation "existential" "instantiation" constr(n) constr(X0) constr(X1) constr(X2) constr(X3) constr(X4) constr(X5) constr(X6) :=
  existential_instantiation_tac_from_conclusion n (@cons V.t X6 (@cons V.t X5 (@cons V.t X4 (@cons V.t X3 (@cons V.t X2 (@cons V.t X1 (@cons V.t X0 nil))))))).

Ltac replace_term_tac s t t':=
  let b:= eval compute in (term_eqb t t') in
  match b with
  | true => constr:(var s)
  | false => match t' with
                 | [[∅]] => constr:( [[∅]])
                 | var ?v => constr:(var v)
                 | singleton ?t0 => let t0':= replace_term_tac s t t0 in
                                       constr:(singleton t0')
                 | intersection ?t1 ?t2 => let t1':= replace_term_tac s t t1 in
                                          let t2':= replace_term_tac s t t2 in
                                          constr:( intersection t1' t2' )
                 | union ?t1 ?t2 => let t1':= replace_term_tac s t t1 in
                                          let t2':= replace_term_tac s t t2 in
                                          constr:( union t1' t2' )
                end
 end.
  
Ltac replace_special_tac x t P:=
 match P with
  | subset ?t1 ?t2 =>
      let t3:= replace_term_tac x t t1 in
      let t4:= replace_term_tac x t t2 in
      constr:(subset t3 t4)
  | [[ is_singleton ?t1 ?t2]] =>
      let t3:= replace_term_tac x t t1 in
      let t4:= replace_term_tac x t t2 in
      constr:([[ is_singleton t3 t4]] )
  | [[ has_two_ele ?t1 ?t2 ?t3 ]] =>
     let t5:= replace_term_tac x t t1 in
     let t6:= replace_term_tac x t t2 in
     let t7:= replace_term_tac x t t3 in
      constr:([[ has_two_ele t5 t6 t7 ]])
  | [[ is_inductive ?t1 ]] =>
      let t3:= replace_term_tac x t t1 in
      constr:([[is_inductive t3 ]])
  | [[ is_natural_number ?t1 ]] =>
      let t3:= replace_term_tac x t t1 in
      constr:([[ is_natural_number t3 ]])
  | [[ is_empty ?t1 ]] =>
      let t3:= replace_term_tac x t t1 in
      constr:([[ is_empty t3 ]])
  | [[ is_pair ?t1 ?t2 ?t3 ]] =>
     let t5:= replace_term_tac x t t1 in
     let t6:= replace_term_tac x t t2 in
     let t7:= replace_term_tac x t t3 in
      constr:([[ is_pair t5 t6 t7 ]])
  | [[ in_rel ?t1 ?t2 ?t3 ]] =>
     let t5:= replace_term_tac x t t1 in
     let t6:= replace_term_tac x t t2 in
     let t7:= replace_term_tac x t t3 in
      constr:([[ in_rel t5 t6 t7 ]])
  | [[ is_triple ?t1 ?t2 ?t3 ?t4 ]] =>
       let t5:= replace_term_tac x t t1 in
       let t6:= replace_term_tac x t t2 in
       let t7:= replace_term_tac x t t3 in
       let t8:= replace_term_tac x t t4 in
      constr:([[ is_triple t5 t6 t7 t8 ]])
  | [[ in_rel3 ?t1 ?t2 ?t3 ?t4 ]] =>
       let t5:= replace_term_tac x t t1 in
       let t6:= replace_term_tac x t t2 in
       let t7:= replace_term_tac x t t3 in
       let t8:= replace_term_tac x t t4 in
      constr:([[ in_rel3 t5 t6 t7 t8 ]])
  | [[ is_legal_plus ?t1 ?t2 ]] =>
      let t3:= replace_term_tac x t t1 in
      let t4:= replace_term_tac x t t2 in
      constr:([[ is_legal_plus t3 t4 ]])
  | [[ is_plus ?t1 ?t2 ]] =>
      let t3:= replace_term_tac x t t1 in
      let t4:= replace_term_tac x t t2 in
      constr:([[ is_legal_plus t3 t4 ]])
  | [[ is_legal_mult ?t1 ?t2 ?t3 ]] =>
     let t5:= replace_term_tac x t t1 in
     let t6:= replace_term_tac x t t2 in
     let t7:= replace_term_tac x t t3 in
      constr:([[ is_legal_mult t5 t6 t7 ]])
  | [[ is_mult ?t1 ?t2 ?t3 ]] =>
     let t5:= replace_term_tac x t t1 in
     let t6:= replace_term_tac x t t2 in
     let t7:= replace_term_tac x t t3 in
      constr:([[ is_mult t5 t6 t7 ]])
  end.    
  
Ltac replace_prop_tac x t P:=
   match P with
   | PEq ?t1 ?t2 => let t3:= replace_term_tac x t t1 in
                             let t4:= replace_term_tac x t t2 in
                            constr:(PEq t3 t4)
   | PRel ?t1 ?t2 => let t3:= replace_term_tac x t t1 in
                             let t4:= replace_term_tac x t t2 in
                            constr:(PRel t3 t4)
  | PFalse => constr:(PFalse)
  | PTrue => constr:(PTrue)
  | PNot ?P1 =>
      let Q1 := replace_prop_tac  x t P1 in
      constr:(PNot Q1)
  | PAnd ?P1 ?P2 =>
      let Q1 := replace_prop_tac x t P1 in
      let Q2 := replace_prop_tac x t P2 in
      constr:(PAnd Q1 Q2)
  | POr ?P1 ?P2 =>
      let Q1 := replace_prop_tac x t P1 in
      let Q2 := replace_prop_tac x t P2 in
      constr:(POr Q1 Q2)
  | PImpl ?P1 ?P2 =>
      let Q1 := replace_prop_tac x t P1 in
      let Q2 := replace_prop_tac x t P2 in
      constr:(PImpl Q1 Q2)
  | PIff ?P1 ?P2 =>
      let Q1 := replace_prop_tac x t P1 in
      let Q2 := replace_prop_tac x t P2 in
      constr:(PIff Q1 Q2)
  | PForall ?x1 ?P1 =>
      let Q1 := replace_prop_tac x t P1 in
           constr:(PForall x1 Q1)
  | PExists ?x1 ?P1 =>
      let Q1 := replace_prop_tac x t P1 in
           constr:(PExists x1 Q1)
    
  | _ => replace_special_tac x t P
end.  


Ltac peq_sub_tac t t' P:=
 first [  
  let H0:= fresh "H" in
  let H1:= fresh "H" in
  let v := get_new_var P ShortNames.x [[∅]] ShortNames.x in
  let Q := replace_prop_tac v t' P in 
  pose proof (PEq_sub Q v t t') as H1;  (* cbv in H1; ShortNames.super_fold_in H1 ; fold empty_context in H1 ; *)
  match type of t with
  | V.t => let Q':= subst_aeq_constr_tac Q v (var t) in assert [[ZF;; t=t' ;; Q' |-- P]] as H0 by FOL_tauto; clear H1;ShortNames.super_fold_in H0
  | _ =>  let Q':= subst_aeq_constr_tac Q v t in assert [[ZF;; t=t' ;; Q' |-- P]] as H0 by FOL_tauto; clear H1; ShortNames.super_fold_in H0
  end
  | fail 1 "Apply PEq_sub fails"]. 
  
Tactic Notation "apply" "PEq_sub" constr(t) constr(t') constr(P) := peq_sub_tac t t' P.

Ltac peq_sub_cond_tac t t' P:=
(*   first [   *)
  let H0:= fresh "H" in
  let H1:= fresh "H" in
  let v := get_new_var P ShortNames.x [[∅]] ShortNames.x in
  let Q:= replace_prop_tac v t P in
  pose proof (PEq_sub Q v t t') as H1;
  match type of t' with
  | V.t => let Q':= subst_aeq_constr_tac Q v (var t') in assert [[ZF;; t=t' ;; P |-- Q']] as H0 by FOL_tauto; clear H1;ShortNames.super_fold_in H0
  | _ =>  let Q':= subst_aeq_constr_tac Q v t' in assert [[ZF;; t=t' ;; P |-- Q']] as H0 by FOL_tauto; clear H1; ShortNames.super_fold_in H0
  end
 (*  | fail 1 "Apply PEq_sub using condition fails"] *). 

Tactic Notation "apply" "PEq_sub" "using" "condition" constr(t) constr(t') constr(P) := peq_sub_cond_tac t t' P.
  
Ltac peq_refl_tac t:=
  pose proof PEq_refl t.
  
Tactic Notation "apply" "PEq_refl" constr(t) := peq_refl_tac t.
  
Module Test.
Import ShortNames. 

Lemma test4: [[ZF;; x ∪ y ∈ z;; x = y |-- y ∪ y∈z]].
Proof.
  apply PEq_sub using condition  x y [[x∪y∈z]].
  FOL_tauto.
Qed.

Lemma test3: [[ZF;; a=b ;; ∀x,  is_inductive x -> a ⊆ x |--  x=x /\ ∀y,  is_inductive y -> b ⊆ y]] . 
Proof.
    apply PEq_refl x.
    apply PEq_sub a b [[∀y,  is_inductive y -> b ⊆ y]].
    FOL_tauto.
Qed.

Lemma test: [[ZF;; ∃w,∃v, is_inductive w /\ ¬ w=v;; y∈z|-- ∃x, ∅∈x]] .
Proof.
  assert [[ZF;; is_inductive a /\ ¬a=b;; y∈z |-- ∅∈a]] by FOL_tauto.
  existential generalization H [[∃x, ∅∈x]]. 
  existential instantiation H0  [[∃w,∃v, is_inductive w /\ ¬ w = v ]].
  FOL_tauto.
Qed.

Lemma test2: [[ZF;; ∃w,∃v, is_inductive w /\ ¬ w=v;; y∈z|-- ∃x, ∅∈x]] . 
Proof.  existential instantiation 1 a b.
             assert [[ZF;; is_inductive a |-- ∅∈a]] by FOL_tauto.
             existential generalization H [[∃x, ∅∈x]].
             FOL_tauto.
Qed.


End Test.

Tactic Notation "The" "conclusion" "is" "already" "proved" :=
  FOL_tauto.
(*
  first
  [ repeat
    match goal with
    | H: derivable ?Phi ?P |- derivable ?Phi ?Q =>
      first [ exact (Alpha_congruence Phi P Q eq_refl H) | clear H]
    end
  | fail 1 "The conclusion is not yet proved"]. *)

Export ShortNames.

Ltac Tauto := FOL_tauto.  
  
Module ToyDPLL_Debug.

Lemma DebugLmm00: forall P J n', ToyDPLL.DPLL_UP P J (S n') =
     (match ToyDPLL.unit_pro P J with
      | Some [] => ToyDPLL.DPLL_filter P J n'
      | Some ((_ :: _) as kJ) => ToyDPLL.DPLL_UP P (kJ ++ J) n'
      | None => false
      end).
Proof.
  reflexivity.
Qed.

(* Lemma DebugLmm01: forall P J n', ToyDPLL.DPLL_filter P J (S n') =
    ToyDPLL.DPLL_pick (ToyDPLL.CNF_filter P J) J n'.
Proof.
  reflexivity.
Qed. *)

Lemma DebugLmm01: forall P J n', ToyDPLL.DPLL_filter P J (S n') =
    ToyDPLL.DPLL_pick (ToyDPLL.CNF_filter P J) nil n'.
Proof.
  reflexivity.
Qed.

Ltac debug_Tauto_step1 := 
  reify_pg;
  apply dpll_sound;
  unfold ToyDPLL.pg2prop;
  simpl fold_right;
  unfold ToyDPLL.der2prop;
  simpl fold_right;
  unfold ToyDPLL.valid;
  simpl ToyDPLL.sprop_gen;
  unfold V.next_name.

Ltac debug_Tauto_step2 :=
  simpl ToyDPLL.cnf_gen;
  unfold V.next_name.

Ltac idtacs L :=
  match L with
  | cons ?X ?L0 => idtac X; idtacs L0
  | nil => idtac
  end.

Ltac idtac_CNF :=
  match goal with
  | |- context [ToyDPLL.DPLL_UP ?L _ _] => idtacs L
  end.

Ltac simpl_one_step_UP :=
  match goal with
  | |- context [ToyDPLL.DPLL_UP ?P ?J (S ?n')] =>
         rewrite (DebugLmm00 P J n')
  end;
  unfold ToyDPLL.unit_pro;
  simpl ToyDPLL.fold_UP_result;
  unfold ToyDPLL.fold_UP_result;
  unfold fold_left;
  unfold app.

Ltac simpl_one_step_filter :=
  match goal with
  | |- context [ToyDPLL.DPLL_filter ?P ?J (S ?n')] =>
         rewrite (DebugLmm01 P J n')
  end;
  unfold ToyDPLL.CNF_filter;
  simpl map.

Ltac fold_Xs :=
  set (X17 := "''''''''''''''''x"%string) in *;
  set (X16 := "'''''''''''''''x"%string) in *;
  set (X15 := "''''''''''''''x"%string) in *;
  set (X14 := "'''''''''''''x"%string) in *;
  set (X13 := "''''''''''''x"%string) in *;
  set (X12 := "'''''''''''x"%string) in *;
  set (X11 := "''''''''''x"%string) in *;
  set (X10 := "'''''''''x"%string) in *;
  set (X9 := "''''''''x"%string) in *;
  set (X8 := "'''''''x"%string) in *;
  set (X7 := "''''''x"%string) in *;
  set (X6 := "'''''x"%string) in *;
  set (X5 := "''''x"%string) in *;
  set (X4 := "'''x"%string) in *;
  set (X3 := "''x"%string) in *;
  set (X2 := "'x"%string) in *;
  set (X1 := "x"%string) in *.

End ToyDPLL_Debug.