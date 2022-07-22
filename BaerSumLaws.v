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

(* Jacob: Showing that for a short exact sequence [A -> E -> B] and maps f : A -> A' and g : B' -> B, we can commute the order of
   pulling back and pushing out. *)

Lemma abses_reorder_pullback_pushout `{Univalence} {A A' B B' : AbGroup} (E : AbSES B A) (f : A $-> A') (g : B' $-> B) :
    abses_pullback g (abses_pushout f E) = abses_pushout f (abses_pullback g E).
Proof.
  (* All I've done here is add the composite Eg -> fE into context, so that I know I have it - will try to find a way
     to do this without posing into context, once I figure out the rest of the proof. *)
  pose (F := absesmorphism_compose (abses_pushout_morphism E f) (abses_pullback_morphism E g)).

  (* We get a factorization Eg -> (fE)g. *)
  Check (abses_pullback_morphism_corec F).
Admitted.
 

