From HoTT Require Import Basics Types Pointed
  Algebra.Groups Algebra.AbGroups Spaces.Circle Homotopy.Pi1S1 Homotopy.ClassifyingSpace
          WildCat.

(** ** Working with the free group on one generator *)

Local Open Scope mc_add_scope.

(** Any homomorphism respects [grp_pow]. *)
Lemma grp_pow_homo {G H : Group} (f : GroupHomomorphism G H) (n : nat) (g : G)
  : f (grp_pow g n) = grp_pow (f g) n.
Proof.
  induction n.
  + cbn. apply grp_homo_unit.
  + cbn. refine ((grp_homo_op f g (grp_pow g n)) @ _).
    exact (ap (fun m => f g + m) IHn).
Defined.

(** Multiplication by [n : nat] defines an endomorphism of any abelian group [A]. *) 
Definition ab_mul_nat {A : AbGroup} (n : nat) : GroupHomomorphism A A.
Proof.
  snrapply Build_GroupHomomorphism.
  1: exact (fun a => grp_pow a n).
  intros a b.
  induction n; cbn.
  1: exact (grp_unit_l _)^.
  refine (_ @ associativity _ _ _).
  refine (_ @ ap _ (associativity _ _ _)^).
  rewrite (commutativity (grp_pow a n) b).
  refine (_ @ ap _ (associativity _ _ _)).
  refine (_ @ (associativity _ _ _)^).
  apply grp_cancelL.
  assumption.
Defined.

(** Alternative definition with worse computational properties. *)   
Definition ab_mul_nat' {A : AbGroup} (n : nat) : GroupHomomorphism A A.
Proof.
  induction n as [|n H].
  1: exact grp_homo_const.
  exact (ab_homo_add H grp_homo_id).
Defined.

(* jarl: Admitted for now. *)
Lemma FreeGroup_rec_beta {X : Type} {G : Group} (x : X) (s : X -> G)
  : FreeGroup_rec _ _ s (freegroup_in x) = s x.
Proof. Admitted.

(** We define [Z] as the free group with a single generator. *)
Definition Z := FreeGroup Unit.
Definition Z_gen : Z := freegroup_in tt. (* The generator *)

(** We simply define [nat_to_Z] using [grp_pow] applied to the generator. *)
Definition nat_to_Z : nat -> Z := fun n => grp_pow Z_gen n.

(** Using [Z_mul_nat] you can define the subgroup [nZ] using [grp_image]. *)
Definition Z_mul_nat (n : nat) : GroupHomomorphism Z Z.
Proof.
  apply FreeGroup_rec.
  apply Unit_rec.
  exact (nat_to_Z n).
Defined.

(** We can now say where [nat_to_Z n] is sent by maps out of [Z]. *)
Lemma Z_rec_nat_beta {A : AbGroup} (a : A) (n : nat)
  : FreeGroup_rec _ _  (fun _ => a) (nat_to_Z n) = ab_mul_nat n a.
Proof.
  induction n as [|n H].
  1: easy.
  refine (grp_pow_homo _ _ _ @ _); simpl.
  by rewrite grp_unit_r.
Defined.

(** From this it should be possible to show [moduluo_n_n] since the modulus map is a homomorphism. *)

Global Instance Z_commutative : Commutative (@group_sgop Z).
Admitted.
