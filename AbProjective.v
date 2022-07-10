From HoTT Require Import Basics Types Pointed
  Algebra.Groups Algebra.AbGroups
  WildCat.

(** * Projective abelian groups *)

(** We define projective abelian groups and show that [P] is projective if and only if every epimorphism [A -> P] merely splits. From this it follows that [Ext P A] is trivial for all [A]. We also show that [Z] is projective. (And maybe we show that the free abelian group on a projective set is projective?) *)

(* jarl: Projective types have already been studied in Projectivity.v. Studying that file might be helpful. (You can disregard everything about modalities in that file. We're working with the "identity modality" here, so that [In O A] is a tautology). *)

(** An abelian group is [P] projective if for any map [P -> B] and epimorphism [A -> B], there merely exists a lift [P -> A] making the triangle commute. *)
(* jarl: maybe this should be a Class? *)
Definition IsAbProjective (P : AbGroup) : Type.
Admitted.

(** An abelian group is projective iff epis into it merely split. *)
(* jarl: The WildCat library gives us handy notation like [A $-> B] for group homomorphisms and [g $o f] for composition of group homomorphisms. You could also write them out (composition is [grp_homo_compose]).  *)
Proposition iff_isabprojective_surjections_split (P : AbGroup)
  : IsAbProjective P <->
      (forall A, forall p : A $-> P,
          IsSurjection p -> merely (exists s : P $-> A, p $o s == idmap)).
Admitted.

(** Using [iff_ab_ext_trivial_split], show that [AbSES B A] is trivial. *)
Proposition abext_projective_trivial `{Univalence} (P : AbGroup) {proj_P : IsAbProjective P}
  : forall A, forall E : AbSES P A, tr E = point (Ext P A).
Proof. Admitted.

(** Can you show the converse? That if [forall A, forall E, tr E = point (Ext P A)] then [P] is projective. *)

(* jarl: Now import this file in [Z.v] and show that [Z] is projective. *)
