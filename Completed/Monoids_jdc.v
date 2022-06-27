From HoTT Require Import Basics Types Spaces.Nat Classes.implementations.peano_naturals.

(** * Monoids *)

(** This defines the type of monoids as a record, which is equvialent to a nested sigma-type but has the convenience of 'named projections' (explained below). *)

Record Monoid := {
    monoid_type : Type;
    monoid_ishset : IsHSet monoid_type;
    monoid_unit : monoid_type;
    monoid_op : monoid_type -> monoid_type -> monoid_type;
    monoid_op_assoc : forall x y z,
      monoid_op x (monoid_op y z) = monoid_op (monoid_op x y) z;
    monoid_left_identity : forall x, monoid_op monoid_unit x = x;
    monoid_right_identity : forall x, monoid_op x monoid_unit = x;
  }.

(** [monoid_type], [monoid_op], etc... are "named projections" or "accessors". Given [M : Monoid], the underlying type is [monoid_type M]. Simlarly, [monoid_op M] is the binary operation. *)
Check monoid_type.

(** If we have [M : Monoid], then to pick an element of [M] we have to write [x : monoid_type M]. This line lets us simply write [x : M] by making [monoid_type] a coercion. *)
Coercion monoid_type : Monoid >-> Sortclass.

(** We make the monoid an implicit argument to some of the accessors, as Coq can usually figure it out. *)
Arguments monoid_unit {_}.
Arguments monoid_op {_} _ _.
Arguments monoid_left_identity {_} _.
Arguments monoid_right_identity {_} _.

(** This adds the fact that monoids are sets to Coq's "typeclass database," which lets us apply results about sets to monoids without having to repeatedly prove to Coq that monoids are sets. *)
Local Existing Instance monoid_ishset.

(** Standard notation. *)
Local Notation "1" := monoid_unit : monoid_scope.
Local Notation "x * y" := (monoid_op x y) : monoid_scope.

Delimit Scope monoid_scope with monoid.

Open Scope monoid_scope.

Record MonoidHom (M N : Monoid) := {
    monoidhom_fun : M -> N;
    monoidhom_unit : monoidhom_fun 1 = 1;
    monoidhom_op : forall x y : M,
      monoidhom_fun (x * y) = monoidhom_fun x * monoidhom_fun y;
  }.

Coercion monoidhom_fun : MonoidHom >-> Funclass.


(** ** Basics *)

Lemma unique_left_unit (M : Monoid) (u : M)
  : (forall x : M, u * x = x) -> (u = 1).
Proof.
  intro is_left_unit_u.
  pose (u1 := is_left_unit_u 1).
  refine (_ @ u1). (* the symbol [@] is for path concatenation *)
  exact (monoid_right_identity u)^. (* the hat [^] inverts a path *)
Defined.

Lemma unique_right_unit (M : Monoid) (u : M)
  : (forall x : M, x * u = x) -> (u = 1).
Proof.
  intro is_right_unit_u.
  (* This can be inlined, but you need to clarify which "1" you mean.  I think the [@] notation makes Coq think we are in path_scope. *)
  exact ((monoid_left_identity u)^ @ is_right_unit_u 1%monoid).
Defined.

(** Next, state and prove the following:  for [x] in a monoid, if [y] is a left-inverse to [x] and [z] is a right-inverse to [x], then [y = z]. *)
(** It follows that two two-sided inverses are equal.  Do you think it is true that two left-inverses are necessarily equal? *)

Lemma inverses_coincide (M : Monoid) (x y z : M) : (y * x = 1) * (x * z = 1) -> (y = z).
Proof.
  intros [p q].
  (* Most of the time (but not always), it's best not to "pose" things into the context. *)
  (* Instead, we can build up a composite of paths, one step at a time, like this: *)
  refine ((monoid_right_identity y)^ @ _).
  (* [refine] lets me partially solve a goal, with underscores creating new goals (unless Coq can guess how to fill them in). *)
  refine ((ap _ q)^ @ _).  (* Coq guesses the function. *)
  refine (monoid_op_assoc _ _ _ _ @ _).
  refine (ap (fun m => m*z) p @ _).  (* Here Coq needs help. *)
  apply monoid_left_identity.
  (* Advantages of the iterative approach:
     - Coq can guess arguments, since the terms are being defined with a specific goal in mind.
       This saves you work.
     - Coq tells you what the next goal is, so you don't have to do scratch work figuring out
       the final answer all at once.
     - The reader can follow along and see how the proof progresses. *)
Defined.


(** ** The two monoid structures on [Bool] *)

(** Look at the definition of [Bool] in Types/Bool. There are two monoid structures on [Bool], one using [andb] and one using [orb]. *)

Definition monoid_bool_orb : Monoid.
Proof.
  (* Coq automatically gives us a function [Build_Monoid] which lets us construct monoids. *)
  (* [srapply] is a custom tactic in the HoTT library which figures out how many arguments need to be supplied to a function and leaves those as goals for you to figure out. *)
  srapply (Build_Monoid Bool).
  - exact false.
  - exact orb.
  - induction x; induction y; reflexivity.
  - simpl. reflexivity.
  - induction x; reflexivity.
    (* [simpl]'s that don't change anything should be removed. *)
Defined.

Definition monoid_bool_andb : Monoid.
Proof.
  srapply (Build_Monoid Bool).
  - exact true.
  - exact andb.
  - induction x; induction y; reflexivity.
  - simpl. reflexivity.
  - induction x; reflexivity.
Defined.

(** The negation function [negb] defines a homomorphism between these monoid structures. *)

Definition monoid_negb : MonoidHom monoid_bool_andb monoid_bool_orb.
  srapply Build_MonoidHom.
  - exact negb.
  - simpl. reflexivity.
  - simpl. induction x; reflexivity.
Defined.


(** ** The monoid structure on [nat] *)

(** Next show that set of natural numbers is a monoid. The natural numbers are defined in Basics/Overture (search for "Natural numbers"), and there are useful functions in Spaces/Nat. You can also use Coq's search functionality to find things, by giving the signature of the term that you want: *)
Search (nat -> nat -> nat).
  
Definition monoid_nat : Monoid.
Proof.
srapply (Build_Monoid nat).
- exact O.
- exact add.
- apply add_assoc. (* Your proofs were great! It can be hard to find existing things in the library. *)
- reflexivity.
- apply add_0_r.
Defined.

(* Need to prove that everything in the image of the proposed homomorphism below commutes, so I define it as a
   function of its underlying types first and check the identifications in the next Lemma. *)


(* Essentially exponentiation on x by natural numbers *)
(* { } indicates implicit arguments. *)
Definition monoid_exp {M : Monoid} (x : M) : monoid_nat -> M.
Proof.
  - intro n. induction n.
    + exact 1.
    + exact (IHn * x).
Defined.

(* Is there a way to coerce Coq into understanding a different encoding for a function? Writing
   ptd_mon_function M x for each application is a bit cumbersome and obfuscates the code, but I wanted a 
   descriptive name. *)
(* I chose a shorter descriptive name, and made the [M] argument implicit. You could also make a notation, if you want, e.g. [x ** n]. *)
Lemma xy_paths_commute (M : Monoid) (x : M) : forall n, (monoid_exp x n) * x = x * (monoid_exp x n).
Proof.
  intro y. induction y.
  + cbn.
    exact (monoid_left_identity _ @ (monoid_right_identity _)^).
  + simpl. (* [cbn] and [simpl] use different heuristics, and sometimes [simpl] is better. *)
    refine (ap (fun m => m*x) IHy @ _).
    symmetry.  (* reverse LHS and RHS *)
    apply monoid_op_assoc. (* Coq can guess the arguments. *)
Defined.

(** Next state and prove that if [M] is any monoid with a chosen element [x], there is a monoid homomorphism from [nat] to [M] sending [1] to [x]. *)

(* Jarl and I did a similar path concatenation on the board; is there a more concise way of making this proof go through? *)

Lemma monoid_hom_exp {M : Monoid} (x : M) : MonoidHom monoid_nat M.
Proof.
srapply Build_MonoidHom.
- exact (monoid_exp x).
- cbn. reflexivity.
- intros m n. induction m.
  + simpl. symmetry. apply monoid_left_identity.
  + simpl.
    (* I won't clean this up, since I give a better approach below. *)
    pose (ap_IH := ap (fun y => y*x) IHm).
    pose (assoc := monoid_op_assoc M (monoid_exp x m) (monoid_exp x n) x).
    pose (IH_assoc := ap_IH @ assoc^).
    pose (ap_comm_paths := ap (monoid_op (monoid_exp x m)) (xy_paths_commute M x n)).
    pose (IH_assoc_comm := IH_assoc @ ap_comm_paths).
    pose (assoc' := monoid_op_assoc M (monoid_exp x m) x (monoid_exp x n)).
    exact (IH_assoc_comm @ assoc').
Defined.

(* Essentially exponentiation on x by natural numbers *)
(* Since the successor of [n] is [1 + n], let's define [monoid_exp' (S n)] to be [x * monoid_exp n]. *)
Definition monoid_exp' {M : Monoid} (x : M) : monoid_nat -> M.
Proof.
  - intro n. induction n.
    + exact 1.
    + exact (x * IHn).
Defined.

(* Now we don't need the lemma about commutation, and the proof below is much shorter.
   This is a good lesson:  choose your definitions carefully, and if they seem to lead
   to complication, look at how you might be able to change them to make later things easier. *)

(** Next state and prove that if [M] is any monoid with a chosen element [x], there is a monoid homomorphism from [nat] to [M] sending [1] to [x]. *)
Lemma monoid_hom_exp' {M : Monoid} (x : M) : MonoidHom monoid_nat M.
Proof.
  srapply Build_MonoidHom.
  - exact (monoid_exp' x).
  - cbn. reflexivity.
  - intros m n. induction m.
    + simpl. symmetry. apply monoid_left_identity.
    + simpl.
      refine (ap _ IHm @ _). (* Coq can guess the function. *)
      apply monoid_op_assoc.
Defined.
