From HoTT Require Import Basics Types Pointed HSet Spaces.Int Spaces.Finite Spaces.Pos 
  Algebra.Groups Algebra.AbGroups Spaces.Nat Classes.implementations.peano_naturals
  Spaces.Circle Homotopy.ClassifyingSpace Homotopy.Pi1S1 Homotopy.HomotopyGroup Homotopy.Bouquet
  Homotopy.ExactSequence Modalities.ReflectiveSubuniverse.

Require Import Z.
Require Import BaerSumLaws.
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


(* Universal property of free_Z - my version *)
Definition free_Z_rec (G : Group) (g : G) : GroupHomomorphism Z G.
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
Definition modulo (n : nat) : GroupHomomorphism Z (abgroup_fin n).
Proof.
 exact (free_Z_rec (abgroup_fin n) (@fin_nat n (S O))).
Defined.

(*
Compute toZ 0.
Compute toZ 1.
Compute toZ 2.
*)

(** Show that [n : abgroup_Z] is sent to zero. *)

(* The inclusion toZ : Nat -> Int doesn't work anymore of course. *)

Lemma modulo_n_n (n : nat) : modulo n (nat_to_Z n) = mon_unit.
Proof.
  refine ((@Z_rec_nat_beta (abgroup_fin n) (@fin_nat n (S O)) n) @ _).
  induction n.
  + cbn. reflexivity.
  + 
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
    exact ( merely { b : abgroup_Z & grp_pow b n = a }).
  - exact _. (* Coq should already knows it's a proposition. *)
  - cbn. exact admit. (* exact (0 ; ). *)
  - cbn. intros x y. 
Admitted.

Definition ab_mul (n : Int) {A : AbGroup} : GroupHomomorphism A A.
Proof.
  induction n.
  - exact (grp_homo_compose ab_homo_negation (ab_mul_nat (pos_to_nat p))).
  - exact grp_homo_const.
  - exact (ab_mul_nat (pos_to_nat p)).  
Defined.

Lemma Z_hom_equiv `{Funext} (A : AbGroup) : GroupIsomorphism (ab_hom ab_Z A) A.
Proof.
  snrapply Build_GroupIsomorphism'.
  - refine (_ oE (equiv_freegroup_rec A Unit)).
    symmetry. exact (Build_Equiv _ _ (Unit_rec A) _).
  - intros f g. cbn. reflexivity.
Defined.

Lemma ab_mul_homo {A B : AbGroup} (n : Int) (f : GroupHomomorphism A B)
  : grp_homo_compose f (ab_mul n) ==  grp_homo_compose (ab_mul n) f.
Proof.
  intro x.
  induction n.
  - cbn.
    refine (grp_homo_inv _ _ @ _).
    refine (ap negate _).
    apply grp_pow_homo.
  - cbn. apply grp_homo_unit.
  - cbn.
    apply grp_pow_homo.
Defined.

Lemma ab_mul_precomp `{Funext} (A : AbGroup) (n : Int)
  : (Z_hom_equiv A) o (fun f : ab_hom ab_Z A => grp_homo_compose f (ab_mul n))
    == (ab_mul n) o (Z_hom_equiv A).
Proof.
  intro f.
  cbn.
  apply (ab_mul_homo n f _).
Defined.

Lemma isequiv_hset_bijection `{Funext} {A B : Type} `{IsHSet A, IsHSet B} (f : A -> B)
  `{S: IsSurjection f, E: IsEmbedding f}
  : IsEquiv f.
Proof.
  apply isequiv_contr_map.
  intro b.
  assert (z : ((Tr (-1)) (hfiber f b))).
  1: apply S.
  revert z.
  rapply Trunc_rec.
  intros z.
  exists z.
  apply E.
Defined.

Local Instance isequiv_cxfib_isembedding `{Funext} {A B C : pType} `{IsHSet A, IsHSet B, IsHSet C}
  (f : A ->* B) (g : B ->* C) (G : IsExact (Tr (-1)) f g) `{E : IsEmbedding f}
  : IsEquiv (cxfib cx_isexact).
Proof.
  nrapply isequiv_hset_bijection.
  1-3: exact _.
  rapply (cancelL_mapinO (Tr (-1))).
Defined.
                           
Lemma exactsequence_quotient_iso `{Funext}  (A B C : AbGroup) (f : ab_hom A B) (g : ab_hom B C) (H0 : IsEmbedding f) (H1 : IsSurjection g) (G : IsExact (Tr (-1)) f g)
  : GroupIsomorphism (QuotientAbGroup B (ab_image_embedding f)) C.
Proof.
  snrapply Build_GroupIsomorphism.
    - snrapply equiv_quotient_abgroup_ump.
      split with g.
      intros b x.
      destruct x as [x p].
      refine (ap g p^ @ _).
      rapply cx_isexact.
    - apply isequiv_hset_bijection.
      + rapply cancelR_conn_map.
      + rapply isembedding_isinj_hset.
        srapply Quotient_ind_hprop; intro x.
        srapply Quotient_ind_hprop; intro y.
        intro p.
        apply qglue.
        unfold in_cosetL.
        cbn.
        assert (q : g ((- x)%mc * y) = mon_unit).
        {  refine (grp_homo_op _ _ _ @ _).
          rewrite grp_homo_inv.
          apply grp_moveL_M1^-1.
          exact p^. }
        srefine (((cxfib cx_isexact)^-1 _ ; _)).
          * exact (_ ; q).
          * exact (ap pr1 (eisretr (cxfib cx_isexact) _)).
Defined.

Lemma trivial_surjection_kernel `{Univalence} {A : Group} (f : GroupHomomorphism A grp_trivial) 
  : grp_kernel f = maximal_subgroup :> Subgroup A.
Proof.
  rapply equiv_path_subgroup'.
  intro g. cbn.
  split.
    - exact (fun _ => tt).
    - intro x. symmetry; apply eta_unit. 
Defined.

(* To do: For a s.e.s. A -> B ->> 0, left map is an epi*)
Lemma exactsequence_leftmap_epi `{Funext} {A B : AbGroup}
  (f : ab_hom A B) (g : ab_hom B abgroup_trivial) (G : IsExact (Tr (-1)) f g)
    : IsSurjection f.
Proof.
  intro b.
  rapply contr_inhabited_hprop.
  rapply isexact_preimage.
  symmetry; apply eta_unit.
Defined.

(** ** Quotients of [abgroup_Z] *)

(** Define the multiplication-by-n map using [int_mul] (from Spaces.Int.Core). You may find [int_mul_add_distr_l] from Spaces.Int.Spec useful. *)
Definition mul (n : Int) : GroupHomomorphism Z Z.
  exact (ab_mul n).
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
