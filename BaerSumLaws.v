From HoTT Require Import Basics Types Pointed.
From HoTT Require Import Homotopy.ExactSequence WildCat.
From HoTT Require Import AbGroups.AbelianGroup AbSES.Core AbSES.Pullback AbSES.Pushout.
From HoTT Require Import BaerSum AbGroups.AbPushout.

Require Import AbProjective.

(* Jacob: The swap isomorphism of the direct product of two abelian groups. *)

Definition direct_sum_swap {A B : AbGroup} : (ab_biprod A B) $<~> (ab_biprod B A).
Proof.
  snrapply Build_GroupIsomorphism'.
  - apply equiv_prod_symm.
  - intro x.  reflexivity.
Defined.

(* Composing group homomorphisms with the identity has no effect. *)

(* Commented out for now, since unused:
Lemma grp_compose_id_r `{Funext} {A B : Group} (f : A $-> B) : grp_homo_compose f grp_homo_id = f.
Proof.
    apply equiv_path_grouphomomorphism. reflexivity.
Defined.

Lemma grp_compose_id_l `{Funext} {A B : Group} (f : A $-> B) : grp_homo_compose grp_homo_id f = f.
Proof.
    apply equiv_path_grouphomomorphism. reflexivity.
Defined.

Lemma abses_pushout_homotopic' `{Univalence} {A A' B : AbGroup} (f f' : A $-> A') (h : f == f')
  : abses_pushout0 (B:=B) f $=> abses_pushout0 f'.
Proof.
  induction (equiv_path_grouphomomorphism h).
  apply id_transformation.
Defined.

Definition abses_pushout_homotopic `{Univalence} {A A' B : AbGroup}
  (f f' : A $-> A') (h : f == f')
  : abses_pushout0 (B:=B) f == abses_pushout0 f'
  := equiv_path_data_homotopy _ _ (abses_pushout_homotopic' _ _ h).
*)

(* Given a morphism [f] of short exact sequences, the pushout of the domain along [f_1] equals the pullback of the codomain along [f_3]. *)
Lemma abses_pushout_is_pullback `{Univalence} {A A' B B' : AbGroup}
      {E : AbSES B A} {E' : AbSES B' A'} (f : AbSESMorphism E E')
  : abses_pushout0 (component1 f) E = abses_pullback0 (component3 f) E'.
Proof.
  (* The morphism [f : E -> E'] factors as [E -> f_1 E -> E'], where the first map is the map defining the pushout [f_1 E] and the second map is denoted [abses_pushout_morphism_rec f] below.  This second map is the identity on the first component, so it presents its domain as the pullback of [E'] along [f_3]. *)
  refine (abses_component1_trivial_pullback (abses_pushout_morphism_rec f) _); reflexivity.
Defined.

(* Given a short exact sequence [A -> E -> B] and maps [f : A -> A'], [g : B' -> B], we can change the order of pushing out along [f] and pulling back along [g]. *)
Lemma abses_reorder_pullback_pushout `{Univalence} {A A' B B' : AbGroup}
      (E : AbSES B A) (f : A $-> A') (g : B' $-> B)
  : abses_pushout0 f (abses_pullback0 g E) = abses_pullback0 g (abses_pushout0 f E).
Proof.
  (* There are morphisms [Eg -> E] and [E -> fE] by definition of the pullback and pushout. We define [F : Eg -> fE] to be the composite. Its first and third components are [f o id] and [id o g]. *)
  pose (F := absesmorphism_compose (abses_pushout_morphism E f) (abses_pullback_morphism E g)).
  (* We change [F] to a morphism that is the same except that the first and third components are [f] and [g]. Then [abses_pushout_is_pullback] shows that the pushout of [Eg] along [f] is equal to the pullback of [fE] along [g]. *)
  refine (abses_pushout_is_pullback (Build_AbSESMorphism f (component2 F) g _ _)); apply F.
Defined.

(* The following are a series of lemmas that we rely on for properties of the Baer sum. *)

(* This should replace the result of the same name in BaerSum.v in the library. The only difference is that F is allowed to involve different groups *)
(** The pointwise direct sum of two short exact sequences. *)
Definition abses_direct_sum `{Univalence} {B A B' A' : AbGroup} (E : AbSES B A) (F : AbSES B' A')
  : AbSES (ab_biprod B B') (ab_biprod A A')
  := Build_AbSES (ab_biprod E F)
                 (functor_ab_biprod (inclusion E) (inclusion F))
                 (functor_ab_biprod (projection E) (projection F))
                 (functor_ab_biprod_embedding _ _)
                 (functor_ab_biprod_sujection _ _)
                 (ab_biprod_exact _ _ _ _).

(* There is always a morphism [E + F -> F + E] of short exact sequences, for any two E, F : AbSES B A. *) 
Definition abses_swap_morphism `{Univalence} {A A' B B' : AbGroup}
           (E : AbSES B A) (F : AbSES B' A')
  : AbSESMorphism (abses_direct_sum E F) (abses_direct_sum F E).
Proof.
  snrapply Build_AbSESMorphism.
  1,2,3: exact direct_sum_swap.
  all: reflexivity.
Defined.

(* Precomposing the codiagonal with the swap map has no effect. *)
Lemma ab_codiagonal_swap `{Funext} {A : AbGroup} : (@ab_codiagonal A) $o direct_sum_swap = ab_codiagonal.
Proof.
  apply equiv_path_grouphomomorphism.
  intro a. cbn. apply abgroup_commutative.
Defined.

(* Post-composing the diagonal with the swap map has no effect. *)
Lemma ab_diagonal_swap {A : AbGroup} : (@ab_diagonal A) = direct_sum_swap $o (@ab_diagonal A).
Proof.
  reflexivity.
Defined.

(* Jacob: This is the isomorphism [A + (A + A) <~> (A + A) + A] that associativity relies on in Mac Lane. I get the sense that
   there is a much shorter way to do this - feel free to rewrite. *)

Lemma ab_biprod_assoc {A : AbGroup} : ab_biprod A (ab_biprod A A) $<~> ab_biprod (ab_biprod A A) A.
Proof.
  - snrapply Build_GroupIsomorphism.
    + snrapply Build_GroupHomomorphism.
      * intro x. destruct x as [f s]. destruct s as [s t]. exact ((f,s),t).
      * unfold IsSemiGroupPreserving. reflexivity.
    + srapply Build_IsEquiv.
      * intro x. destruct x as [f t]. destruct f as [f s]. exact (f, (s,t)).
      * intro x. destruct x as [f t]. destruct f as [f s]. reflexivity.
      * intro x. destruct x as [f s]. destruct s as [s t]. reflexivity.
      * cbn. reflexivity.
Defined.

(* We now get that [(ab_diagonal + id) o ab_diagonal = (id + ab_diagonal) o ab_diagonal] after passing into the right
   direct sum via the above isomorphism. *)
Lemma ab_commute_id_diagonal `{Funext} {A : AbGroup} :
  (functor_ab_biprod (@ab_diagonal A) grp_homo_id) $o ab_diagonal =
    ab_biprod_assoc $o (functor_ab_biprod grp_homo_id ab_diagonal) $o ab_diagonal.
Proof.
  apply equiv_path_grouphomomorphism.
  reflexivity.
Defined.

(* A similar result for the codiagonal. *)
Lemma ab_commute_id_codiagonal `{Funext} {A : AbGroup} :
  (@ab_codiagonal A) $o (functor_ab_biprod ab_codiagonal grp_homo_id) $o ab_biprod_assoc =
    ab_codiagonal $o (functor_ab_biprod grp_homo_id ab_codiagonal).
Proof.
  apply equiv_path_grouphomomorphism.
  intro a. cbn.
  exact (grp_assoc _ _ _)^.
Defined.


(* A proof of commutativity of the Baer sum.
   
   (The rewrite line will be switched out shortly.) *)
Lemma baer_sum_commutative `{Univalence} {A B : AbGroup} (E F : AbSES B A)
  : abses_baer_sum E F = abses_baer_sum F E.
Proof.
  unfold abses_baer_sum.
  refine (_ @ _).
  - refine (ap (abses_pullback ab_diagonal) _). 
    rewrite <- ab_codiagonal_swap. (* Use refine (_ @ _) and ap instead. *)
    refine (_ @ _).
    1: symmetry; rapply abses_pushout_compose.
    refine (_ @ _).
    1: exact (ap _ (abses_pushout_is_pullback (abses_swap_morphism E F))).
    unfold abses_swap_morphism, component3.
    exact (abses_reorder_pullback_pushout _ ab_codiagonal direct_sum_swap).
  - refine (abses_pullback_compose ab_diagonal direct_sum_swap _).
Defined.

