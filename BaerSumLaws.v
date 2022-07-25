From HoTT Require Import Basics Types Pointed.
From HoTT Require Import Homotopy.ExactSequence WildCat.
From HoTT Require Import AbGroups.AbelianGroup AbSES.Core AbSES.Pullback AbSES.Pushout.
From HoTT Require Import BaerSum.
Require Import AbProjective.

(* Jacob: The swap isomorphism of the direct product of two abelian groups. *)

Definition direct_sum_swap {A B : AbGroup} : (ab_biprod A B) $<~> (ab_biprod B A).
Proof.
  snrapply Build_GroupIsomorphism.
  + snrapply Build_GroupHomomorphism.
  - intro x. exact (snd x, fst x).
    - intro x. reflexivity.
  + snrapply Build_IsEquiv.
    1: intro x; exact (snd x, fst x).
    all: reflexivity.
Defined.

(* Jacob: A quick proof that the swap map is its own inverse. *)

Lemma swap_involution {A B : AbGroup} : @direct_sum_swap A B $o direct_sum_swap == idmap.
Proof.
   intro a. reflexivity.
Defined.

(* Composing group homomorphisms with the identity has no effect. *)

Lemma grp_compose_id_r `{Funext} {A B : Group} (f : A $-> B) : grp_homo_compose f grp_homo_id = f.
Proof.
    apply equiv_path_grouphomomorphism. reflexivity.
Defined.

Lemma grp_compose_id_l `{Funext} {A B : Group} (f : A $-> B) : grp_homo_compose grp_homo_id f = f.
Proof.
    apply equiv_path_grouphomomorphism. reflexivity.
Defined.

(* Given a short exact sequence [A -> E -> B] and maps [f : A -> A'], [g : B' -> B], we can change the order of
   pushing out along f and pulling back along g. *)

(* Jacob: This is the first version of the proof - will look into reasoning backwards to avoid posing. *)

Lemma abses_reorder_pullback_pushout `{Univalence} {A A' B B' : AbGroup} (E : AbSES B A) (f : A $-> A') (g : B' $-> B) :
    abses_pushout0 f (abses_pullback0 g E) = abses_pullback0 g (abses_pushout0 f E).
Proof.
  (* There are morphisms [Eg -> E] and [E -> fE] by definition of the pullback and pushout *)
  pose (F := absesmorphism_compose (abses_pushout_morphism E f) (abses_pullback_morphism E g)).

  (* This composite has a factorization [f(Eg) -> fE], which can be identified with the middle
   filler map defining (fE)g in the below way. *)
  pose (K := abses_component1_trivial_pullback (abses_pushout_morphism_rec F) (reflexive_pointwise_paths _ _ _)).
  simpl in K.
  rewrite (grp_compose_id_r f) in K. 
  rewrite (grp_compose_id_l g) in K.
  exact K.                                                              
Defined.
 

