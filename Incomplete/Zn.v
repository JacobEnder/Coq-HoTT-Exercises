From HoTT Require Import Basics Types Pointed HSet Spaces.Int Spaces.Finite Spaces.Pos 
  Algebra.Groups Algebra.AbGroups Spaces.Nat Classes.implementations.peano_naturals
Spaces.Circle Homotopy.ClassifyingSpace Homotopy.Pi1S1 Homotopy.HomotopyGroup Homotopy.Bouquet.

Local Open Scope positive_scope.
Local Open Scope int_scope.
Local Open Scope mc_mult_scope.

Lemma mod_plus {n : nat} (m k : nat) : @fin_nat n (Nat.add m (fin_to_nat (@fin_nat n k)) ) = @fin_nat n (Nat.add m k).
Proof.
  induction k. 
  + apply ap, ap. exact path_nat_fin_zero.
Admitted.

Lemma cancellation {n : nat} (x y : Fin n.+1) : fin_to_nat (@fin_nat n (Nat.add (fin_to_nat x) (fin_to_nat y))) = Nat.add (fin_to_nat x) (fin_to_nat y).
Admitted.

Lemma inclusion_reduction {n : nat} (x : Fin n.+1) : fin_nat (fin_to_nat x) = x.
Admitted.

Axiom admit : forall {T}, T.


(** * Finite cyclic groups *)

(** Define an abelian group structure on [Fin n]. Look at Spaces.Finite.Fin for how to work with [Fin n]. *)
Definition abgroup_fin (n : nat) : AbGroup.
Proof.
  snrapply Build_AbGroup.
  - snrapply Build_Group.
    + exact (Fin n.+1).
    + intros k l. apply fin_nat. exact (Nat.add (fin_to_nat k) (fin_to_nat l)).
    + unfold MonUnit. exact fin_zero.
    + unfold Negate. intro x. apply fin_nat. exact (Nat.sub (n.+1) (fin_to_nat x)).
    + split; try split.
      * split.
        ** intros x y p. destruct p. intro y. cbn. exact _.
        ** unfold Associative. unfold HeteroAssociative. 
           intros x y z. unfold "*".
           refine ((mod_plus (fin_to_nat x) (fin_to_nat y + fin_to_nat z)) @ _).
           apply ap. refine ((add_assoc (fin_to_nat x) (fin_to_nat y) (fin_to_nat z)) @ _).
           exact ((ap (fun m => Nat.add m (fin_to_nat z)) (cancellation x y))^).
      * unfold LeftIdentity. intro y. unfold "*". unfold mon_unit. 
        refine (ap (fin_nat) (ap (fun m => Nat.add m (fin_to_nat y)) path_nat_fin_zero) @ _).
        cbn. apply inclusion_reduction.
      * unfold RightIdentity. intro y. unfold "*". unfold mon_unit.
        refine (ap (fin_nat) (ap (fun m => Nat.add (fin_to_nat y) m) path_nat_fin_zero) @ _).
        refine ((ap (fin_nat) (add_n_O (fin_to_nat y)))^ @ _). apply inclusion_reduction.
      * apply admit.
      * apply admit.
  - apply admit.
Defined.

(** The inclusion of the naturals into the integers. Note that [pos_of_nat] sends [0] to [1], since [Pos] only encodes strictly positive naturals. (I can't believe that this isn't already in the library!) *)
Definition toZ : nat -> Int.
Proof.
  intro n; induction n.
  - exact 0.
  - exact (pos (pos_of_nat n.+1)).
Defined.

Definition pos_to_nat : Core.Pos -> nat.
Proof.
  intro p. induction p.
  + exact (S O).
  + exact (Nat.add IHp IHp).
  + exact (S (Nat.add IHp IHp)).
Defined.


(* Special case of the free group on an n-bouquet *)
Definition unit_bouquet_is_free `{Univalence} : IsFreeGroupOn Unit (Pi 1 (Bouquet Unit)) (pi1bouquet_incl Unit).
Proof.
  apply isfreegroupon_pi1bouquet.
Defined.


(* I am defining Z to be the free group on one generator *)
Definition free_Z : Group := FreeGroup Unit.

(* Universal property of free_Z - my version *)
Definition free_Z_rec (G : Group) (g : G) : GroupHomomorphism free_Z G.
Proof.
  apply FreeGroup_rec.
  exact (fun tt => g).
Defined.

(** The universal property of the integers - Jarl's version, with the current definition of Z *)
Definition Z_rec `{Univalence} (G : Group) (g : G)
  : GroupHomomorphism abgroup_Z G.
Proof.
  refine (grp_homo_compose _ (grp_iso_inverse Pi1Circle)).
  apply (equiv_bg_pi1_adjoint _ _)^-1.
  srapply Build_pMap.
  1: exact (Circle_rec _ (point _) (bloop g)).
  reflexivity.
Defined.

(** Define the group homomorphism [abgroup_Z -> abgroup_fin_n] which computes the modulus. *)

(* Defined with my free group - previously the old Int was used *)
Definition modulo (n : nat) : GroupHomomorphism free_Z (abgroup_fin n).
Proof.
 exact (free_Z_rec (abgroup_fin n) (@fin_nat n (S O))).
Defined.

Compute toZ 0.
Compute toZ 1.
Compute toZ 2.

(** Show that [n : abgroup_Z] is sent to zero. *)

(* The inclusion toZ : Nat -> Int doesn't work anymore of course. *)
Lemma modulo_n_n (n : nat) : modulo n (toZ n) = mon_unit.
Admitted.


(** ** Subgroups of [abgroup_Z] *)

Lemma cancel_x (x : Int) : -x + x = 0.
Proof.

Admitted.

(** Subgroups are defined in Algebra.Groups.Subgroup, and they are represented as predicates (i.e. families of propositions) which are appropriately closed (go look at the definition of [IsSubgroup]). *)

(** Define the subgroup [nZ] of [abgroup_Z]. (If you want to multiply by [toZ] on the left, you can write [sg_op (A:=abgroup_Z (toZ) a]. For multiplication on the right, Coq understands [a * (toZ n)] since it infers the group structure [abgroup_Z] from [a].) *)
(* I've filled some of the definition in to illustrate, but you might want to swap the order of multiplication, for example. Figure out what's best! *)
Definition subgroup_Z (n : nat) : Subgroup (abgroup_Z).
  snrapply Build_Subgroup'. (* This is a "smart constructor" for subgroups. *)
  - intro a. (* You can write Sigma-types as follows: *)
    exact { b : abgroup_Z & b * toZ n = a }.
  - exact _. (* Coq should already knows it's a proposition. *)
  - cbn. exact (-(toZ n); cancel_x (toZ n)).
  - intros x y. cbn. intros s t.
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
