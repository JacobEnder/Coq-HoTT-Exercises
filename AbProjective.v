From HoTT Require Import Basics Types Pointed
  Algebra.Groups Algebra.AbGroups
  WildCat Limits.Pullback Homotopy.ExactSequence.

(** * Projective abelian groups *)

(** We define projective abelian groups and show that [P] is projective if and only if every epimorphism [A -> P] merely splits. From this it follows that [Ext P A] is trivial for all [A]. We also show that [Z] is projective. (And maybe we show that the free abelian group on a projective set is projective?) *)

(* jarl: Projective types have already been studied in Projectivity.v. Studying that file might be helpful. (You can disregard everything about modalities in that file. We're working with the "identity modality" here, so that [In O A] is a tautology). *)

(** An abelian group is [P] projective if for any map [P -> B] and epimorphism [A -> B], there merely exists a lift [P -> A] making the triangle commute. *)
(* jarl: maybe this should be a Class? *)
Definition IsAbProjective (P : AbGroup) : Type :=
  forall (A B : AbGroup), forall (f : P $-> B),
  forall (e : A $-> B), IsSurjection e -> merely (exists l : P $-> A, e $o l == f).


(** An abelian group is projective iff epis into it merely split. *)
(* jarl: The WildCat library gives us handy notation like [A $-> B] for group homomorphisms and [g $o f] for composition of group homomorphisms. You could also write them out (composition is [grp_homo_compose]).  *)
Proposition iff_isabprojective_surjections_split (P : AbGroup)
  : IsAbProjective P <->
      (forall A, forall p : A $-> P,
          IsSurjection p -> merely (exists s : P $-> A, p $o s == idmap)).
Proof.
  split.
  + intros H A p H1.
    exact (H A P (grp_homo_id) p H1).
  + intro H. unfold IsAbProjective. intros A B f e H1.
    pose proof (s := H (ab_pullback f e) (grp_pullback_pr1 f e) (conn_map_pullback _ f e)).
    strip_truncations.
    destruct s as [s h].
    apply tr. exists ((grp_pullback_pr2 f e) $o s).
    intro x. refine ((pullback_commsq f e _)^ @ _).
    exact (ap f (h x)).
Defined.

(** When [P] is projective, all extensions ending in [P] are split. *)
Proposition abext_projective_trivial `{Univalence} (P : AbGroup) {proj_P : IsAbProjective P}
  : forall A, forall E : AbSES P A, tr E = point (Ext P A).
Proof.
  intros A E. rapply iff_ab_ext_trivial_split.
  exact (fst (iff_isabprojective_surjections_split P) proj_P E
           (projection E) _).
Defined.

(** It follows that when [P] is projective, [Ext P A] is contractible. *)
Global Instance contr_abext_projective `{Univalence} (P : AbGroup) `{IsAbProjective P}
  {A : AbGroup}
  : Contr (Ext P A).
Proof.
  exists (point _).
  intro E.
  strip_truncations.
  symmetry.
  apply abext_projective_trivial; assumption.
Defined.

(* Fix [E], [P] and a surjection [E $-> P]. Then there is a short exact sequence [ker p $-> E $-> P]. *)
Lemma abses_from_surjection {E P : AbGroup} (p : E $-> P) `{IsSurjection p}
  : AbSES P (ab_kernel p).
Proof.
  srapply (Build_AbSES E _ p).
  + exact (subgroup_incl _).
  + exact _.
  + snrapply Build_IsExact.
    - snrapply Build_pHomotopy.
      -- intro e. cbn. unfold ispointed_group. exact e.2.
      -- apply path_ishprop.
    - cbn. exact _.
Defined.

(* Now we show the converse of [abext_projective_trivial]. *)
Proposition abext_trivial_projective `{Univalence} (P : AbGroup)
  : (forall A, forall E : AbSES P A, tr E = point (Ext P A)) -> IsAbProjective P.
Proof.
  intro H1. apply iff_isabprojective_surjections_split.
  intros A p H2.
  apply (iff_ab_ext_trivial_split (abses_from_surjection p))^-1.
  apply H1.
Defined.

(* jarl: Now import this file in [Z.v] and show that [Z] is projective. *)
