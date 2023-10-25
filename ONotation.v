Require Import Program.Basics.
Require Import Coq.Init.Nat.
Require Import Lia.

Section Util.

  Definition monotonic (f : nat -> nat) : Prop :=
    forall x x', x <= x' -> f x <= f x'.

End Util.

Section Main.

  Notation "f ∘ g" := (compose f g).

  Inductive ParamCompl (X : Type) : Type :=
  | id__pc (f : X -> nat) : ParamCompl X
  | o__pc : ParamCompl X -> ParamCompl X
  | O__pc : ParamCompl X -> ParamCompl X
  | add__pc : ParamCompl X -> ParamCompl X -> ParamCompl X
  | mul__pc : ParamCompl X -> ParamCompl X -> ParamCompl X
  | exp__pc : ParamCompl X -> ParamCompl X -> ParamCompl X
  | Any__pc : ParamCompl X -> ParamCompl X.

  Notation "⟦ f ⟧" := (@id__pc _ f) (at level 30).
  Notation " 'o' ( f )" := (@o__pc _ f) (at level 50).
  Notation " 'O' ( f )" := (@O__pc _ f) (at level 50).
  Notation " f1 ⊕ f2 " := (@add__pc _ f1 f2) (at level 50).
  Notation " f1 ⊗ f2 " := (@mul__pc _ f1 f2) (at level 50).
  Notation " f1 ↑ f2 " := (@exp__pc _ f1 f2) (at level 50). (* Knuth's up-arrow notation *)
  Notation " 'Any' ( f )" := (@Any__pc _ f) (at level 50).

  Reserved Notation "f ∈p F" (at level 65).
  Fixpoint InParamCompl {X : Type} (f : X -> nat) (F : ParamCompl X) : Prop :=
    match F with
    | ⟦F⟧ => forall x, f x <= F x
    | O(F) => exists g, g ∈p F /\ exists a b,      forall x, f x <= a * g x + b
    | o(F) => exists g, g ∈p F /\ forall a b, exists δ, forall x, a * f x + b <= g x + δ
    | F1⊕F2 => exists g1 g2, g1 ∈p F1 /\ g2 ∈p F2 /\ forall x, f x <= g1 x + g2 x
    | F1⊗F2 => exists g1 g2, g1 ∈p F1 /\ g2 ∈p F2 /\ forall x, f x <= g1 x * g2 x
    | F1↑F2 => exists g1 g2, (forall x, 0 < g1 x) /\ g1 ∈p F1 /\ g2 ∈p F2 /\ forall x, f x <= g1 x ^ g2 x
    | Any(F) => exists G, monotonic G /\ exists g, g ∈p F /\ forall x, f x <= G (g x)
    end
  where "f ∈p F" := (InParamCompl f F).
  Notation "f ∉p F" := (~ InParamCompl f F) (at level 65).

  Definition compl_incl {X : Type} (F G : ParamCompl X) :=
    forall (f : X -> nat), f ∈p F -> f ∈p G.
  Notation "F ⊑ G" := (compl_incl F G) (at level 60).

  Section Lemmas.

    Section BasicInclusion.

      Context {X : Type}.

      Lemma comp_incl_refl:
        forall (F : ParamCompl X),
          F ⊑ F.
      Proof.
        now intros.
      Qed.

      Lemma comp_incl_trans:
        forall (F G H : ParamCompl X),
          F ⊑ G -> G ⊑ H -> F ⊑ H.
      Proof.
        now intros * IN1 IN2; firstorder.
      Qed.

      Lemma comp_incl_f_Of:
        forall (F : ParamCompl X),
          F ⊑ O(F).
      Proof.
        intros ? ? IN.
        exists f; split; auto.
        now exists 1, 0; intros ?; lia.
      Qed.

      Lemma comp_incl_base_ge:
        forall (f g : X -> nat),
          (forall x, f x = g x) ->
          ⟦f⟧ ⊑ ⟦g⟧.
      Proof.
        now intros * LE f IN x; rewrite <-LE.
      Qed.

      Lemma comp_incl_O:
        forall (F G : ParamCompl X),
          F ⊑ G -> O(F) ⊑ O(G).
      Proof.
        intros * SUB f IN.
        destruct IN as (fo & IN & a & b &LE).
        exists fo; split.
        + now apply SUB in IN.
        + now exists a, b.
      Qed.

      Lemma comp_incl_O_r:
        forall (F G : ParamCompl X),
          F ⊑ O(G) -> O(F) ⊑ O(G).
      Proof.
        intros * SUB f IN.
        destruct IN as (fo & IN & a & b & LE).
        apply SUB in IN.
        destruct IN as (foo & IN & α & β & LE2).
        exists foo; split.
        + now apply IN.
        + eexists (a * α); exists (a * β + b).
          intros.
          specialize (LE x); specialize (LE2 x).
          nia.
      Qed.

      Lemma coml_incl_O_idem:
        forall (F : ParamCompl X), O(O(F)) ⊑ O(F).
      Proof.
        intros ? ? IN.
        destruct IN as [f1 [IN1 [a1 [b1 LE1]]]].
        destruct IN1 as [f2 [IN2 [a2 [b2 LE2]]]].
        exists f2; split; auto.
        exists (a1 * a2), (a1 * b2 + b1).
        intros; specialize (LE1 x); specialize (LE2 x).
        nia.
      Qed.

      Lemma coml_incl_oO_K:
        forall (F : ParamCompl X), o(O(F)) ⊑ o(F).
      Proof.
        intros ? f IN.
        inversion_clear IN as [f1 [IN1 LE1]].
        inversion_clear IN1 as [f2 [IN2 [α [β LE]]]].
        assert(L : α = 0 \/ α > 0) by lia.
        destruct L as [Z|P]; subst.
        { exists f2; split; [easy | ].
          intros; specialize (LE1 a b); destruct LE1 as [δ LE3].
          exists (β + δ); intros; specialize (LE x); specialize (LE3 x).
          nia. }
        { exists f2; split;[easy | ].
          assert (LE2 : forall a b, exists δ, forall x, a * f x + b <= α * f2 x + (β + δ)).
          { intros a b; specialize (LE1 a b); destruct LE1 as [δ LE3].
            exists δ; intros; specialize (LE x); specialize (LE3 x); nia. }
          intros; specialize (LE2 (α * a) (α * b + β)); destruct LE2 as [δ LE3].
          exists δ; intros; specialize (LE3 x); nia. }
      Qed.

    End BasicInclusion.

    Section Arithmetic.

      Context {X : Type}.

      (* ------------------------------- Plus ------------------------------- *)

      Lemma comp_incl_max:
        forall (F : ParamCompl X) (f g : X -> nat),
          f ∈p F -> g ∈p F ->
          (fun x => max (f x) (g x)) ∈p F.
      Proof.
        induction F as [F | | | | | | ]; intros * IN1 IN2.
        - now intros ?; apply Max.max_lub.
        - destruct IN1 as [fo [IN3 LE1]], IN2 as [go [IN4 LE2]].
          specialize (IHF _ _ IN3 IN4).
          exists (fun x => max (fo x) (go x)); split.
          + exact IHF.
          + intros a b.
            specialize (LE1 a b); destruct LE1 as [δ1 LE3].
            specialize (LE2 a b); destruct LE2 as [δ2 LE4].
            exists (max δ1 δ2); intros.
            destruct (Max.max_dec (f x) (g x)) as [EQ|EQ].
            rewrite EQ; clear EQ; rewrite LE3; lia.
            rewrite EQ; clear EQ; rewrite LE4; lia.
        - destruct IN1 as [fo [IN3 LE1]], IN2 as [go [IN4 LE2]].
          specialize (IHF _ _ IN3 IN4).
          exists (fun x => max (fo x) (go x)); split.
          + exact IHF.
          + destruct LE1 as (a1 & b1 & LE1), LE2 as (a2 & b2 & LE2).
            exists (max a1 a2), (max b1 b2); intros.
            specialize (LE1 x); specialize (LE2 x).
            destruct (Max.max_dec (f x) (g x)) as [EQ|EQ].
            now rewrite EQ; clear EQ; rewrite LE1; nia.
            now rewrite EQ; clear EQ; rewrite LE2; nia.
        - destruct IN1 as [f1 [f2 [IN3 [IN4 LE1]]]], IN2 as [g1 [g2 [IN5 [IN6 LE2]]]].
          specialize (IHF1 _ _ IN3 IN5); specialize (IHF2 _ _ IN4 IN6).
          exists (fun x => max (f1 x) (g1 x)), (fun x => max (f2 x) (g2 x)); repeat split; try easy.
          now intros; specialize (LE1 x); specialize (LE2 x); lia.
        - destruct IN1 as [f1 [f2 [IN3 [IN4 LE1]]]], IN2 as [g1 [g2 [IN5 [IN6 LE2]]]].
          specialize (IHF1 _ _ IN3 IN5); specialize (IHF2 _ _ IN4 IN6).
          exists (fun x => max (f1 x) (g1 x)), (fun x => max (f2 x) (g2 x)); repeat split; try easy.
          now intros; specialize (LE1 x); specialize (LE2 x); nia.
        - destruct IN1 as (f1 & f2 & POS1 & IN3 & IN4 & LE1);
            destruct IN2 as (g1 & g2 & POS2 & IN5 & IN6 & LE2).
          specialize (IHF1 _ _ IN3 IN5); specialize (IHF2 _ _ IN4 IN6).
          exists (fun x => max (f1 x) (g1 x)), (fun x => max (f2 x) (g2 x)); repeat split; try easy.
          + now intros; specialize (POS1 x); specialize (POS2 x); nia.
          + intros; apply Max.max_lub.
            * rewrite LE1; apply PeanoNat.Nat.pow_le_mono.
              -- now apply PeanoNat.Nat.neq_0_lt_0, POS1.
              -- now apply PeanoNat.Nat.le_max_l.
              -- now apply PeanoNat.Nat.le_max_l.
            * rewrite LE2; apply PeanoNat.Nat.pow_le_mono.
              -- now apply PeanoNat.Nat.neq_0_lt_0, POS2.
              -- now apply PeanoNat.Nat.le_max_r.
              -- now apply PeanoNat.Nat.le_max_r.
        - destruct IN1 as (F1 & MON1 & f2 & IN3 & LE1);
            destruct IN2 as (G1 & MON2 & g2 & IN5 & LE2).
          specialize (IHF _ _ IN3 IN5).
          exists (fun x => max (F1 x) (G1 x)); split.
          + intros ? ? LE.
            apply Max.max_lub.
            * now apply PeanoNat.Nat.max_le_iff; left; apply MON1.
            * now apply PeanoNat.Nat.max_le_iff; right; apply MON2.
          + exists (fun x : X => max (f2 x) (g2 x)); repeat split; try easy.
            intros; destruct (Max.max_dec (f2 x) (g2 x)) as [EQ|EQ]; rewrite EQ.
            * apply Max.max_lub.
              -- now rewrite LE1; apply PeanoNat.Nat.max_le_iff; left; easy.
              -- rewrite LE2; apply PeanoNat.Nat.max_le_iff; right.
                 now apply MON2; rewrite <-EQ; apply PeanoNat.Nat.le_max_r.
            * apply Max.max_lub.
              -- rewrite LE1; apply PeanoNat.Nat.max_le_iff; left.
                 now apply MON1; rewrite <-EQ; apply PeanoNat.Nat.le_max_l.
              -- now rewrite LE2; apply PeanoNat.Nat.max_le_iff; right; easy.
      Qed.

      Lemma comp_incl_plus:
         forall (F : ParamCompl X) (f g : X -> nat),
           f ∈p F -> g ∈p F ->
           (fun x => f x + g x) ∈p O (F).
      Proof.
        intros * IN1 IN2.
        exists (fun x => max (f x) (g x)); repeat split.
        - now apply comp_incl_max.
        - exists 2, 0; intros.
          now destruct (Max.max_dec (f x) (g x)) as [EQ|EQ]; lia.
      Qed.

      Lemma comp_incl_plus_compat:
        forall (F1 F2 G1 G2 : ParamCompl X),
          F1 ⊑ F2 -> G1 ⊑ G2 -> F1 ⊕ G1 ⊑ F2 ⊕ G2.
      Proof.
        intros * IN1 IN2 f IN.
        inversion_clear IN as [g1 [g2 [IN3 [IN4 LE]]]].
        now exists g1, g2; eauto.
      Qed.

      Lemma comp_incl_plus_compat_l:
        forall (F G1 G2 : ParamCompl X),
          G1 ⊑ G2 -> F ⊕ G1 ⊑ F ⊕ G2.
      Proof. now intros * IN; apply comp_incl_plus_compat. Qed.

      Lemma comp_incl_plus_compat_r:
        forall (F1 F2 G : ParamCompl X),
          F1 ⊑ F2 -> F1 ⊕ G ⊑ F2 ⊕ G.
      Proof. now intros * IN; apply comp_incl_plus_compat. Qed.

      Lemma comp_incl_app :
        forall (F G H : ParamCompl X),
          F ⊑ H -> G ⊑ H -> (F ⊕ G) ⊑ O(H).
      Proof.
        intros * SUB1 SUB2 ? IN.
        destruct IN as [f1 [f2 [IN1 [IN2 LE]]]].
        specialize (SUB1 _ IN1); specialize (SUB2 _ IN2).
        apply coml_incl_O_idem.
        exists (fun x => f1 x + f2 x); split.
        - now apply comp_incl_plus.
        - now exists 1, 0; intros; specialize (LE x); nia. 
      Qed.

      (* ------------------------------- Mult ------------------------------- *)

      Lemma comp_incl_mult_compat:
        forall (F1 F2 G1 G2 : ParamCompl X),
          F1 ⊑ G1 -> F2 ⊑ G2 -> F1 ⊗ F2 ⊑ G1 ⊗ G2.
      Proof.
        intros * IN1 IN2 f IN.
        inversion_clear IN as [g1 [g2 [IN3 [IN4 LE]]]].
        now exists g1, g2; eauto.
      Qed.

      Lemma comp_incl_mult_compat_l:
        forall (F G1 G2 : ParamCompl X),
          G1 ⊑ G2 -> F ⊗ G1 ⊑ F ⊗ G2.
      Proof. now intros * IN; apply comp_incl_mult_compat. Qed.

      Lemma comp_incl_mult_compat_r:
        forall (F1 F2 G : ParamCompl X),
          F1 ⊑ F2 -> F1 ⊗ G ⊑ F2 ⊗ G.
      Proof. now intros * IN; apply comp_incl_mult_compat. Qed.

    End Arithmetic.

  End Lemmas.

End Main.
