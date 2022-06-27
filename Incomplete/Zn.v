From HoTT Require Import Basics Types HSet Spaces.Int Spaces.Finite Spaces.Pos 
  Algebra.Groups Algebra.AbGroups.

Local Open Scope positive_scope.
Local Open Scope int_scope.
Local Open Scope mc_mult_scope.


(** * Finite cyclic groups *)

(** Define an abelian group structure on [Fin n]. Look at Spaces.Finite.Fin for how to work with [Fin n]. *)
Definition abgroup_fin (n : nat) : AbGroup.
Proof.
  snrapply Build_AbGroup.
  - snrapply Build_Group.
    (* Use [+] for the next level of bullets.  You can use things like [unfold SgOp] to see more details about what you need to provide. *)
Admitted.

(** Define the group homomorphism [abgroup_Z -> abgroup_fin_n] which computes the modulus. *)
Definition modulo (n : nat) : GroupHomomorphism abgroup_Z (abgroup_fin n).
Admitted.

(** The inclusion of the naturals into the integers. Note that [pos_of_nat] sends [0] to [1], since [Pos] only encodes strictly positive naturals. (I can't believe that this isn't already in the library!) *)
Definition toZ : nat -> Int.
Proof.
  intro n; induction n.
  - exact 0.
  - exact (pos (pos_of_nat n.+1)).
Defined.

Compute toZ 0.
Compute toZ 1.
Compute toZ 2.

(** Show that [n : abgroup_Z] is sent to zero. *)
Lemma modulo_n_n (n : nat) : modulo n (toZ n) = mon_unit.
Admitted.

(** ** Subgroups of [abgroup_Z] *)

(** Subgroups are defined in Algebra.Groups.Subgroup, and they are represented as predicates (i.e. families of propositions) which are appropriately closed (go look at the definition of [IsSubgroup]). *)

(** Define the subgroup [nZ] of [abgroup_Z]. (If you want to multiply by [toZ] on the left, you can write [sg_op (A:=abgroup_Z (toZ) a]. For multiplication on the right, Coq understands [a * (toZ n)] since it infers the group structure [abgroup_Z] from [a].) *)
(* I've filled some of the definition in to illustrate, but you might want to swap the order of multiplication, for example. Figure out what's best! *)
Definition subgroup_Z (n : nat) : Subgroup (abgroup_Z).
  snrapply Build_Subgroup'. (* This is a "smart constructor" for subgroups. *)
  - intro a. (* You can write Sigma-types as follows: *)
    exact { b : abgroup_Z & b * toZ n = a }.
  - exact _. (* Coq should already knows it's a proposition. *)
Admitted.


(** ** Quotients of [abgroup_Z] *)

(** Define the multiplication-by-n map using [int_mul] (from Spaces.Int.Core). You may find [int_mul_add_distr_l] from Spaces.Int.Spec useful. *)
Definition mul (n : Int) : GroupHomomorphism abgroup_Z abgroup_Z.
Admitted.

(** We can form quotients of subgroups using [QuotientAbGroup], and [grp_image] gives the image of a map. Coq already knows that subgroups of abelian groups are normal by [isnormal_ab_subgroup]. We currently lack cokernels of maps in the library (though they're easy to define by what I just explained). *)

(** Define the cokernel of a map. *)
Definition ab_cokernel {G : Group} {A : AbGroup} (f : GroupHomomorphism G A)
  : AbGroup.
Admitted.

(** The universal property of [ab_cokernel f] is given by [grp_quotient_rec] in Algebra.Groups.QuotientGroup. *)

(** Define the n-th cyclic group as the cokernel of [mul n]. *)
Definition cyclic (n : nat) : AbGroup.
Admitted.

(** Define the induced homomorphism [cyclic n -> abgroup_fin n]. *)
Definition cyclic_to_fin (n : nat) : GroupHomomorphism (cyclic n) (abgroup_fin n).
Admitted.

(** Give an alternative definition of [cyclic n] by taking the quotient by [nZ]. *)
Definition cyclic' (n : nat) : AbGroup.
Admitted.

(** Define the induced homomorphism [cyclic' n -> abgroup_fin n]. *)


(** ** Short exact sequences *)

(** Define the short exact sequence [nZ -> Z -> Z/n] using [abses_from_inclusion]. You might find [subgroup_incl] from Algebra.Groups.Subgroup useful. *)
