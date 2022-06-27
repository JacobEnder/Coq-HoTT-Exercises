From HoTT Require Import Basics Types Spaces.Nat.

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
Local Notation "1" := monoid_unit.
Local Notation "x * y" := (monoid_op x y).


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
  pose (u' := is_right_unit_u 1).
  exact ((monoid_left_identity u)^ @ u').
Defined.

(** Next, state and prove the following:  for [x] in a monoid, if [y] is a left-inverse to [x] and [z] is a right-inverse to [x], then [y = z]. *)
(** It follows that two two-sided inverses are equal.  Do you think it is true that two left-inverses are necessarily equal? *)

Lemma inverses_coincide (M : Monoid) (x y z : M) : (y * x = 1) * (x * z = 1) -> (y = z).
Proof.
  intro pq; destruct pq as (p,q).
  pose (y_unit := (monoid_right_identity y)^).
  pose (z_unit := monoid_left_identity z).
  pose (y_path := y_unit @ (ap (monoid_op(y)) q)^ @ (monoid_op_assoc _ y x z)).
  exact (y_path @ (ap (fun m => m*z)) p @ z_unit).
Defined.


(** ** The two monoid structures on [Bool] *)

(** Look at the definition of [Bool] in Types/Bool. There are two monoid structures on [Bool], one using [andb] and one using [orb]. *)

Definition monoid_bool_orb : Monoid.
Proof.
  (* Coq automatically gives us a function [Build_Monoid] which lets us construct monoids. *)
  (* [srapply] is a custom tactic in the HoTT library which figures out how many arguments need to be supplied to a function and leaves those as goals for you to figure out. *)
  srapply (Build_Monoid Bool).
  - exact false.
  - intros b1 b2. exact (orb b1 b2).
  - simpl.
    induction x; induction y; reflexivity.
  - simpl. reflexivity.
  - simpl. induction x; reflexivity.
Defined.

Definition monoid_bool_andb : Monoid.
Proof.
  srapply (Build_Monoid Bool).
  - exact true.
  - intros b1 b2. exact (andb b1 b2).
  - induction x; induction y; reflexivity.
  - simpl. reflexivity.
  - simpl. induction x; reflexivity.
Defined.

(** The negation function [negb] defines a homomorphism between these monoid structures. *)

Definition monoid_negb : MonoidHom monoid_bool_andb monoid_bool_orb.
  srapply Build_MonoidHom.
  - intro b. induction b.
    + exact false.
    + exact true.
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
- intros x y z. induction x.
  + reflexivity.
  + exact (ap (add 1) IHx).
- reflexivity.
- induction x.
  + reflexivity.
  + exact (ap (add 1) IHx).
Defined.

(* Need to prove that everything in the image of the proposed homomorphism below commutes, so I define it as a
   function of its underlying types first and check the identifications in the next Lemma. *)


(* Essentially exponentiation on x by natural numbers *)
Definition ptd_mon_function (M : Monoid) (x : M) : monoid_nat -> M.
Proof.
  - intro n. induction n.
    + exact 1.
    + exact (IHn * x).
Defined.

(* Is there a way to coerce Coq into understanding a different encoding for a function? Writing
   ptd_mon_function M x for each application is a bit cumbersome and obfuscates the code, but I wanted a 
   descriptive name. *)
Lemma xy_paths_commute (M : Monoid) (x : M) : forall y, (ptd_mon_function _ x y)*x = x*(ptd_mon_function _ x y).
Proof.
  intro y. induction y.
  + cbn.
    pose (u1 := monoid_left_identity x).
    pose (u2 := (monoid_right_identity x)^).
    exact (u1 @ u2).
  + cbn. 
    pose (ap_IH := ap (fun m => m*x) IHy).
    pose (assoc := monoid_op_assoc M x (ptd_mon_function M x y) x).
    exact (ap_IH @ assoc^).
Defined.

(** Next state and prove that if [M] is any monoid with a chosen element [x], there is a monoid homomorphism from [nat] to [M] sending [1] to [x]. *)

(* Jarl and I did a similar path concatenation on the board; is there a more concise way of making this proof go through? *)

Lemma pointed_monoid_from_nat (M : Monoid) (x : M) : MonoidHom monoid_nat M.
Proof.
srapply Build_MonoidHom.
- exact (ptd_mon_function M x).
- cbn. reflexivity.
- intros x0. cbn. induction x0.
  + intro y. cbn. symmetry. apply monoid_left_identity.
  + intro y. cbn.
    pose (ap_IH := ap (fun m => m*x) (IHx0 y)).
    pose (assoc := monoid_op_assoc M (ptd_mon_function M x x0) (ptd_mon_function M x y) x).
    pose (IH_assoc := ap_IH @ assoc^).
    pose (ap_comm_paths := ap (monoid_op (ptd_mon_function M x x0)) (xy_paths_commute M x y)).
    pose (IH_assoc_comm := IH_assoc @ ap_comm_paths).
    pose (assoc' := monoid_op_assoc M (ptd_mon_function M x x0) x (ptd_mon_function M x y)).
    exact (IH_assoc_comm @ assoc').
Defined.
