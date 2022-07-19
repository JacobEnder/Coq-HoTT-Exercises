From HoTT Require Import Basics Types Pointed
  Algebra.Groups Algebra.AbGroups Spaces.Circle Homotopy.Pi1S1 Homotopy.ClassifyingSpace
          WildCat.
Require Import Centralizer FreeGroup2 Subgroup2.
Require Import AbProjective.

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

(* Put this somewhere else. *)
Definition commutative_iso_commutative {G H : Group} {C : Commutative (@group_sgop G)}
           (f : GroupIsomorphism G H)
  : Commutative (@group_sgop H).
Proof.
  unfold Commutative.
  rapply (equiv_ind f); intro g1.
  rapply (equiv_ind f); intro g2.
  refine ((preserves_sg_op _ _)^ @ _ @ (preserves_sg_op _ _)).
  refine (ap f _).
  apply C.
Defined.

(* The free group [Z] on one generator is isomorphic to the subgroup of [Z] generated by the generator.  And such cyclic subgroups are known to be commutative, by [commutative_cyclic_subgroup]. *)
Global Instance Z_commutative `{Funext} : Commutative (@group_sgop Z)
  := commutative_iso_commutative iso_subgroup_incl_freegroupon.
(* [Funext] is used in [isfreegroupon_freegroup], but there is a comment there saying that it can be removed.  If that is done, don't need it here either. A different proof of this result, directly using the construction of the free group, could probably also avoid [Funext]. *)

Lemma Z_rec {G : Group} (g : G) : Z $-> G.
Proof.
  apply FreeGroup_rec.
  exact (fun _ => g).
Defined.

Definition ab_Z `{Funext} : AbGroup
  := Build_AbGroup Z _.

Lemma Z_projective `{Funext} : IsAbProjective ab_Z.
Proof.
  apply iff_isabprojective_surjections_split.
  intros A p H1.
  unfold IsConnMap in H1.
  pose proof (c := @center _ (H1 Z_gen)).
  strip_truncations.
  apply tr.
  snrefine (_; _).
  + apply Z_rec. exact c.1.
  + cbn beta. apply ap10.
    change idmap with (grp_homo_map _ _ (@grp_homo_id ab_Z)).
    apply ap. (* of the coercion [grp_homo_map] *)
    apply path_homomorphism_from_free_group.
    simpl.
    intros [].
    refine (_ @ c.2).
    exact (ap p (grp_unit_r _)).
Defined.
