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


(* jarl: Couldn't find this in the library. *)
Definition freegroup_in {X : Type} : X -> FreeGroup X.
Proof.
  exact (fun x => freegroup_eta (cons (inl x) nil)).
Defined.


Lemma Z_mul_nat_Sn_gen (n : nat) : Z_mul_nat (S n) Z_gen = Z_mul_nat n Z_gen + Z_gen.
Proof.
  refine (FreeGroup_rec_beta _ _ @ _); simpl.
  apply (grp_cancelR Z_gen).
  (* exact (grp_unit_r _)^. *)
Admitted.

Lemma Z_mul_nat_gen (n : nat)
  : Z_mul_nat n Z_gen = nat_to_Z n.
Proof.
  induction n as [|n H].
  1: easy.
  refine (Z_mul_nat_Sn_gen _ @ _).
  unfold nat_to_Z.
  apply (grp_cancelR Z_gen).
  (* assumption. *)
Admitted.


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
