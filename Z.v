From HoTT Require Import Basics Types Pointed
  Algebra.Groups Algebra.AbGroups.

(** ** Working with the free group on one generator *)

Local Open Scope mc_add_scope.

(** We can multiply by [n : nat] in any abelian group. *)
Definition ab_mul_nat {A : AbGroup} (n : nat) : GroupHomomorphism A A.
Proof.
  induction n as [|n H].
  1: exact grp_homo_const.
  exact (ab_homo_add H grp_homo_id).
Defined.


(* jarl: Couldn't find this in the library. *)
Definition freegroup_in {X : Type} : X -> FreeGroup X.
Proof.
  exact (fun x => freegroup_eta (cons (inl x) nil)).
Defined.


(* jarl: Admitted for now. *)
Lemma FreeGroup_rec_beta {X : Type} {G : Group} (x : X) (s : X -> G)
  : FreeGroup_rec _ _ s (freegroup_in x) = s x.
Proof. Admitted.

(** We define [Z] as the free group with a single generator. *)
Definition Z := FreeGroup Unit.
Definition Z_gen : Z := freegroup_in tt. (* The generator *)

(* Jarl: I used Fixpoint here since that ended up computing better below. *)
Fixpoint nat_to_Z (n : nat) : Z
  := match n with
     | O => mon_unit
     | S n => nat_to_Z n + Z_gen
     end.

(** We don't yet know that [Z] is abelian, but we can multiply by [n : nat] directly. *)
Definition Z_mul_nat (n : nat) : GroupHomomorphism Z Z.
Proof.
  srapply FreeGroup_rec.
  apply Unit_rec.
  exact (nat_to_Z n). 
Defined.

Lemma Z_mul_nat_Sn_gen (n : nat) : Z_mul_nat (S n) Z_gen = Z_mul_nat n Z_gen + Z_gen.
Proof.
  refine (FreeGroup_rec_beta _ _ @ _); simpl.
  apply (grp_cancelR Z_gen).
  exact (grp_unit_r _)^.
Defined.

Lemma Z_mul_nat_gen (n : nat)
  : Z_mul_nat n Z_gen = nat_to_Z n.
Proof.
  induction n as [|n H].
  1: easy.
  refine (Z_mul_nat_Sn_gen _ @ _).
  unfold nat_to_Z.
  apply (grp_cancelR Z_gen).
  assumption.
Defined.

(** We can now say where [nat_to_Z n] is sent by maps out of [Z]. *)
Lemma Z_rec_nat_beta {A : AbGroup} (a : A) (n : nat)
  : FreeGroup_rec _ _  (fun _ => a) (nat_to_Z n) = ab_mul_nat n a.
Proof.
  induction n as [|n H].
  1: easy.
  unfold nat_to_Z.
  refine (grp_homo_op _ _ _ @ _).
  apply (ap011 (+) H); simpl.
  apply grp_unit_r.
Defined.

(** From this it should be possible to show [moduluo_n_n] since the modulus map is a homomorphism. *)


(** ** The Yoneda lemma for groups *)

Definition GTransformation (A B : Group)
  := forall G, GroupHomomorphism A G -> GroupHomomorphism B G.

Class IsGNatural {A B : Group} (t : GTransformation A B)
  := isnatural : forall G H, forall f : GroupHomomorphism G H,
    forall g : GroupHomomorphism A G, t H (grp_homo_compose f g) == f o t G g.

(** The notion of natural transformation between functors represented by groups. *)
Definition GNatTrans (A B : Group)
  := { t : GTransformation A B & IsGNatural t}.

Definition GNatIso (A B : Group)
  := { t : GNatTrans A B & forall G, IsEquiv (t.1 G) }.

(** Inversion of natural isomorphisms. *)
Definition gnatiso_inverse `{H0 : Funext} {A B : Group}
  : GNatIso A B -> GNatIso B A.
Proof.
  intros [[t nat_t] iso_t].
  srefine ((fun G => (t G)^-1; _); _); cbn.
  2: exact _.
  intros G H f.
  equiv_intro (t G) g.
  intro a.
  refine (ap (fun h => (t H)^-1 h a) _ (y:= t H (grp_homo_compose f g)) @ _).
  1: { apply equiv_path_grouphomomorphism; symmetry.
       apply nat_t. }
  by rewrite 2 eissect.
Defined.

(** The Yoneda lemma for groups *)
Definition group_yoneda `{Funext} {A B : Group}
  : GNatIso A B -> (GroupIsomorphism B A).
Proof.
  intros [[t nat_t] equiv_t].
  snrapply Build_GroupIsomorphism.
  1: exact (t A grp_homo_id).
  srapply isequiv_adjointify.
  1: exact ((t B)^-1 grp_homo_id).
  2: { intro a.
       refine ((nat_t _ _ _ _ a)^ @ _).
       refine (ap (fun f => t B f a) _ (y:=(((t; nat_t).1 B)^-1 grp_homo_id)) @ _).
       1: by apply equiv_path_grouphomomorphism.
       by rewrite eisretr. }
  intro a.
  pose (s := gnatiso_inverse ((t; nat_t); equiv_t)).
  refine ((s.1.2 B A (t A grp_homo_id) grp_homo_id a)^ @ _); cbn.
  refine (ap (fun f => (t A)^-1 f a) _ (y:=t A grp_homo_id) @ _).
  1: by apply equiv_path_grouphomomorphism.
  by rewrite eissect.
Defined.
