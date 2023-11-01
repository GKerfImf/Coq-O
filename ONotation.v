Require Import Program.Basics.
Require Import Coq.Init.Nat.
Require Import Lia.

Require Import Coq.Setoids.Setoid Coq.Classes.Morphisms Coq.Arith.Arith.

Section SetoidRewrite.

  #[global] Instance setoid_le3_add : Proper (le ==> le ==> le) Nat.add.
  Proof. intros ? ? LE x' y' LE'; lia. Qed.

  #[global] Instance setoid_le3_mul : Proper (le ==> le ==> le) Nat.mul.
  Proof. intros ? ? LE x' y' LE'; nia. Qed.

End SetoidRewrite.

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

      Lemma comp_incl_base_le:
        forall (f g : X -> nat),
          (forall x, f x <= g x) ->
          ⟦f⟧ ⊑ ⟦g⟧.
      Proof.
        intros * LE h IN x.
        now rewrite IN.
      Qed.

      Lemma comp_incl_base_plus:
        forall (f g : X -> nat),
          ⟦f⟧ ⊕ ⟦g⟧ ⊑ ⟦fun x => f x + g x⟧.
      Proof.
        intros * h IN.
        destruct IN as (f1 & f2 & IN1 & IN2 & LE).
        intros ?; rewrite LE.
        now rewrite IN1, IN2.
      Qed.

      Lemma comp_incl_base_exp:
        forall (f g : X -> nat),
          ⟦f⟧ ↑ ⟦g⟧ ⊑ ⟦fun x => f x ^ g x⟧.
      Proof.
        intros * h IN.
        destruct IN as (f1 & f2 & POS & IN1 & IN2 & LE).
        intros ?; rewrite LE; clear LE.
        apply PeanoNat.Nat.pow_le_mono.
        - now apply PeanoNat.Nat.neq_0_lt_0, POS.
        - now apply IN1.
        - now apply IN2.
      Qed.

      Lemma comp_incl_o_exp:
        forall (a b : nat),
          a < b ->
          (fun n => n^a) ∈p o(⟦fun n => n^b⟧).
      Proof.
        intros ? ? LT.
        assert (EX: exists δ, δ > 0 /\ b = δ + a).
        { now exists (b - a); split; lia. }
        destruct EX as [δ [POS EQ]]; subst b; clear LT.
        exists (fun n => n ^ (δ + a)); split. easy.
        intros k c; exists (k * k ^ a + c).
        intros x.
        destruct (PeanoNat.Nat.eq_0_gt_0_cases x) as [Z|P]; subst.
        - destruct a, δ; simpl; lia.
        - rewrite PeanoNat.Nat.pow_add_r.
          eapply PeanoNat.Nat.le_trans; [
            | apply PeanoNat.Nat.add_le_mono_r,
              PeanoNat.Nat.mul_le_mono_r,
              PeanoNat.Nat.pow_le_mono_r,
              PeanoNat.Nat.neq_0_lt_0]; try lia.
          rewrite PeanoNat.Nat.pow_1_r.
          destruct (PeanoNat.Nat.le_ge_cases k x) as [NEQ|NEQ].
          + eapply PeanoNat.Nat.le_trans;
              [ | apply PeanoNat.Nat.add_le_mono_r, PeanoNat.Nat.mul_le_mono_r, NEQ]; lia.
          + eapply PeanoNat.Nat.le_trans; [
              | apply PeanoNat.Nat.add_le_mono_l,
                PeanoNat.Nat.add_le_mono_r,
                PeanoNat.Nat.mul_le_mono_l,
                PeanoNat.Nat.pow_le_mono_l,
                NEQ]; try lia.
      Qed.

      Lemma comp_incl_oO:
        forall (f g : X -> nat),
          f ∈p o(⟦g⟧) -> f ∈p O(⟦g⟧).
      Proof.
        intros ? g' IN.
        destruct IN as [g [IN LT]].
        exists g; split; auto; clear IN g'.
        specialize (LT 1 0).
        destruct LT as [δ LT].
        exists 1, δ.
        now intros x; specialize (LT x); lia.
      Qed.

      Lemma comp_incl_O:
        forall (F G : ParamCompl X),
          F ⊑ G -> O(F) ⊑ O(G).
      Proof.
        intros * SUB f IN.
        destruct IN as (fo & IN & a & b &LE).
        exists fo; split.
        - now apply SUB in IN.
        - now exists a, b.
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
          now intros; rewrite LE, LE2; nia.
      Qed.

      Lemma coml_incl_O_idem:
        forall (F : ParamCompl X), O(O(F)) ⊑ O(F).
      Proof.
        intros ? ? IN.
        destruct IN as [f1 [IN1 [a1 [b1 LE1]]]].
        destruct IN1 as [f2 [IN2 [a2 [b2 LE2]]]].
        exists f2; split; auto.
        exists (a1 * a2), (a1 * b2 + b1).
        now intros; rewrite LE1, LE2; nia.
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
          now exists (β + δ); intros; rewrite LE3, LE; nia. }
        { exists f2; split;[easy | ].
          assert (LE2 : forall a b, exists δ, forall x, a * f x + b <= α * f2 x + (β + δ)).
          { intros a b; specialize (LE1 a b); destruct LE1 as [δ LE3].
            now exists δ; intros; rewrite LE3, LE; nia. }
          intros; specialize (LE2 (α * a) (α * b + β)); destruct LE2 as [δ LE3].
          now exists δ; intros; specialize (LE3 x); nia. }
      Qed.

      Lemma coml_incl_Oo_K:
        forall (F : ParamCompl X), O(o(F)) ⊑ o(F).
      Proof.
        intros ? f IN.
        inversion_clear IN as [f1 [IN1 [α [β LE]]]].
        inversion_clear IN1 as [f2 [IN2 LE2]].
        assert(L : α = 0 \/ α > 0) by lia.
        destruct L as [Z|P]; subst.
        { exists f2; split; [easy | ].
          intros; specialize (LE2 a b); destruct LE2 as [δ LE3].
          now exists (a * β + b); intros; rewrite LE; nia. }
        { exists f2; split; [easy | ].
          intros *; specialize (LE2 (a * α) (a * β + b)).
          destruct LE2 as [δ LE2].
          now exists δ; intros; rewrite LE, Nat.mul_add_distr_l, <-Nat.add_assoc, Nat.mul_assoc, LE2. }
      Qed.

    End BasicInclusion.

    Section Arithmetic.

      Context {X : Type}.

      (* ------------------------------- Plus ------------------------------- *)

      Lemma comp_incl_le:
        forall (F : ParamCompl X) (f g : X -> nat),
          (forall x, f x <= g x) ->
          g ∈p F -> f ∈p F.
      Proof.
        destruct F as [F | | | | | | ]; intros * LE IN.
        - now eapply comp_incl_base_le.
        - destruct IN as (g0 & IN & LEg).
          exists g0; split; [easy | ].
          intros; specialize (LEg a b); destruct LEg as (δ & LEg).
          exists δ; intros; specialize (LE x); rewrite <-LEg; nia.
        - destruct IN as (g0 & IN & LEg).
          exists g0; split; [easy | ].
          destruct LEg as (a & b & LEg).
          exists a, b; intros.
          now rewrite LE.
        - destruct IN as (g0 & g1 & IN1 & IN2 & LEg).
          eexists; eexists; repeat split; eauto 2.
          intros; specialize (LE x); rewrite <-LEg; nia.
        - destruct IN as (g0 & g1 & IN1 & IN2 & LEg).
          eexists; eexists; repeat split; eauto 2.
          now intros; rewrite LE; apply LEg.
        - destruct IN as (g0 & g1 & IN1 & IN2 & LEg).
          eexists; eexists; repeat split; [eauto | eauto | apply LEg | ].
          now intros; rewrite LE; apply LEg.
        - destruct IN as (G & MON & g0 & IN & LEg).
          exists G; split; [easy | ].
          exists g0; split; [easy | ].
          now intros; rewrite LE, LEg.
      Qed.

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

    Section Const.

      Context {X : Type}.

      (** Constant parameter *)
      Definition _1 (x : X) := 1.

      Lemma in_const_impl_bounded_by_const:
        forall (c : X -> nat),
          c ∈p O(⟦_1⟧) ->
          exists b, forall x, c x <= b.
      Proof.
        intros ? IN.
        inversion_clear IN as [a [IN1 EQ]].
        destruct EQ as [c1 [c2 B2]].
        exists (c1 + c2); intros.
        rewrite B2; clear B2.
        apply PeanoNat.Nat.add_le_mono_r.
        rewrite <-PeanoNat.Nat.mul_1_r.
        now apply PeanoNat.Nat.mul_le_mono_l, IN1.
      Qed.

      Lemma bounded_by_const_impl_in_const:
        forall (c : X -> nat) (b : nat),
          (forall x, c x <= b) ->
          c ∈p O(⟦_1⟧).
      Proof.
        intros ? ? LE.
        exists _1; split.
        - now constructor.
        - exists b, 0. intros.
          now rewrite PeanoNat.Nat.add_0_r; unfold _1; rewrite PeanoNat.Nat.mul_1_r.
      Qed.

      Lemma compl_incl_Oc_in_O1:
        forall (c : X -> nat) (b : nat),
          (forall x, c x <= b) ->
          O(⟦c⟧) ⊑ O(⟦_1⟧).
      Proof.
        intros ? ? LE f IN.
        destruct IN as (f1 & IN1 & α & β & IN2).
        apply bounded_by_const_impl_in_const with (b := α * b + β).
        intros x; rewrite IN2.
        specialize (IN1 x); rewrite LE in IN1.
        nia.
      Qed.

    End Const.

    Section Poly.

      Variable X : Type.
      Variable size : X -> nat.
      Hypothesis H_pos_size : forall x, 0 < size x.

      (** Class of poly *)
      Definition poly (param : X -> nat) := O(⟦param⟧ ↑ O(⟦_1⟧)).

      Lemma in_poly_impl_bounded_by_monom :
        forall (f : X -> nat),
          f ∈p poly size ->
          exists a b c, forall x, f x <= a * (size x)^b + c.
      Proof.
        intros ? IN.
        inversion_clear IN as [g1 [IN1 [a [c B1]]]].
        inversion_clear IN1 as [g2 [b [POS [Base [IN3 B2]]]]].
        apply in_const_impl_bounded_by_const in IN3; destruct IN3 as [b' B3].
        exists a, b', (a + c); intros x.
        eapply PeanoNat.Nat.le_trans.
        - now apply B1.
        - rewrite B2; clear B2 B1.
          destruct (Nat.eq_0_gt_0_cases (g2 x)) as [Z|P].
          + rewrite Z; destruct (b x), b';
              now rewrite ?Nat.pow_succ_r', ?Nat.pow_0_r; nia.
          + apply Nat.add_le_mono; [ | lia].
            apply Nat.mul_le_mono_l.
            now apply Nat.pow_le_mono; auto; lia.
      Qed.

      Lemma bounded_by_monom_impl_in_poly :
        forall (f : X -> nat) (a b c : nat),
          (forall x, f x <= a * (size x)^b + c) ->
          f ∈p poly size.
      Proof.
        intros * LE.
        exists (fun x => size x ^ b); repeat split.
        - exists (size), (fun _ => b); repeat split; try easy.
          eexists; split.
          + intros ?; eapply le_n.
          + now exists 0, b.
        - now exists a, c.
      Qed.

      Lemma sum_of_poly_is_in_poly' :
        forall f g,
          f ∈p poly size ->
          g ∈p poly size ->
          (fun x => f x + g x) ∈p poly size.
      Proof.
        intros * IN1 IN2.
        apply in_poly_impl_bounded_by_monom in IN1;
          apply in_poly_impl_bounded_by_monom in IN2.
        destruct IN1 as [a__f [b__f [c__f LE__f]]], IN2 as [a__g [b__g [c__g LE__g]]].
        exists (fun x => size x ^ (max b__f b__g)); repeat split.
        - exists size, (fun _ => max b__f b__g); repeat split; try easy.
          exists _1; repeat split; [easy | ].
          now exists b__f, b__g; unfold _1; intros _; apply Nat.max_lub; lia.
        - exists (a__f + a__g), (a__f + a__g + c__f + c__g); intros.
          rewrite LE__f, LE__g; clear LE__f LE__g.
          destruct (Nat.eq_0_gt_0_cases (size x)) as [Z|P].
          + now rewrite Z; destruct b__f, b__g; simpl; lia.            
          + rewrite !Nat.add_assoc; apply plus_le_compat_r.
            rewrite Nat.add_comm; rewrite !Nat.add_assoc; apply plus_le_compat_r.
            apply Nat.le_trans with ((a__f + a__g) * size x ^ (max b__f b__g)); [ | lia].
            now rewrite Nat.mul_add_distr_r; rewrite Nat.add_comm;
              apply plus_le_compat; apply mult_le_compat_l, Nat.pow_le_mono_r; lia.
      Qed.

      Lemma sum_of_poly_is_in_poly :
        poly size ⊕ poly size ⊑ poly size.
      Proof.
        intros ? IN; inversion IN as [fl [fr [INl [INr LE]]]].
        now eapply comp_incl_le; [apply LE| ]; apply sum_of_poly_is_in_poly'.
      Qed.

      Lemma prod_of_poly_is_in_poly' :
        forall f g,
          f ∈p poly size ->
          g ∈p poly size ->
          (fun x => f x * g x) ∈p poly size.
      Proof.
        intros ? ? IN1 IN2.
        apply in_poly_impl_bounded_by_monom in IN1;
          apply in_poly_impl_bounded_by_monom in IN2.
        destruct IN1 as [a__f [b__f [c__f LE__f]]], IN2 as [a__g [b__g [c__g LE__g]]].
        exists (fun x => size x ^ (b__f + b__g)); repeat split.
        - exists size, (fun _ => b__f + b__g); repeat split; try easy.
          exists _1; repeat split; [easy| ].
          exists b__f, b__g; unfold _1; intros _; lia.
        - exists (a__f * a__g + a__f * c__g + a__g * c__f), (c__f * c__g + a__f * c__g + a__g * c__f); intros.
          rewrite LE__f, LE__g; clear LE__f LE__g.
          destruct (Nat.eq_0_gt_0_cases (size x)) as [Z|P].
          + now rewrite Z; destruct b__f, b__g; simpl; lia.
          + rewrite Nat.mul_add_distr_r, !Nat.mul_add_distr_l.
            rewrite Nat.add_assoc; apply plus_le_compat; [ | lia].
            rewrite !Nat.mul_add_distr_r. apply plus_le_compat. apply plus_le_compat.
            * rewrite <-!Nat.mul_assoc; apply mult_le_compat_l.
              rewrite Nat.mul_comm; rewrite <-!Nat.mul_assoc; apply mult_le_compat_l.
              now rewrite <-Nat.pow_add_r; apply Nat.pow_le_mono_r; lia.
            * rewrite <-!Nat.mul_assoc; apply mult_le_compat_l.
              rewrite Nat.mul_comm; apply mult_le_compat_l.
              now apply Nat.pow_le_mono_r; lia.
            * rewrite Nat.mul_assoc; apply mult_le_compat; [lia| ].
              now apply Nat.pow_le_mono_r; lia.
      Qed.

      Lemma prod_of_poly_is_in_poly :
        poly size ⊗ poly size ⊑ poly size.
      Proof.
        intros ? IN; inversion IN as [fl [fr [INl [INr LE]]]].
        now eapply comp_incl_le; [apply LE| ]; apply prod_of_poly_is_in_poly'.
      Qed.

    End Poly.

  End Lemmas.

End Main.
