Module shape_lemma Import terms occurrence alpha;

(* a crucial shape lemma *)

[tvars : Trm->VVs =
  Trec ([_:Trm]VVs)
       ([_:SS]NIL|VV)
       ([u:VV]unit u)
       ([_:PP]NIL|VV)
       ([u:VV][_,_:Trm][l,r:VVs]CONS u (append l r))
       ([u:VV][_,_:Trm][l,r:VVs]CONS u (append l r))
       ([_,_:Trm][l,r:VVs]append l r)];

[textual_voccur [v:VV][A:Trm] : BB = member VVeq v (tvars A)];

[p:PP];

Goal {M|Trm}{v|VV}(is_ff (textual_voccur v M)) -> 
      is_tt (Trm_eq (alpha p v (alpha' v p M)) M);
Refine Trec [M:Trm]{v|VV}{nocc:is_ff (textual_voccur v M)}
             is_tt (Trm_eq (alpha p v (alpha' v p M)) M);
(* sort *)
intros;Refine Trm_eq_refl;
(* var *)
intros;Equiv is_tt (Trm_eq (if ? ? ?) ?);
Qrepl Q_sym (ff_orr_unit (VVeq v n));Qrepl nocc;Refine Trm_eq_refl;
(* par *)
intros;Equiv is_tt (Trm_eq (alpha p v (if ? ? ?)) ?);Refine tt_or_ff (PPeq p n);
intros eqP;Qrepl eqP;Equiv is_tt (Trm_eq (if ? ? ?) ?);
           Qrepl VVrefl v;Qrepl PPdecide eqP;Refine Trm_eq_refl;
intros neqP;Qrepl neqP;Refine Trm_eq_refl;
(* pi *)
intros;Refine fst (deMorgan ? (member VVeq v (append (tvars A) (tvars B)))) nocc;
intros neqV noccAB;
Refine fst (deMorgan (member VVeq v (tvars A)) (member VVeq v (tvars B)));
Qrepl Q_sym (member_append_lem VVeq v (tvars A) (tvars B));Immed;
intros noccA noccB;
Equiv is_tt (Trm_eq (pi n (alpha p v (alpha' v p A))
              (if ? (alpha' v p B) (alpha p v (alpha' v p B)))) ?);
Qrepl Trm_eq_subst (ihA noccA);
Qrepl Trm_eq_subst (ihB noccB);
Qrepl neqV;Refine Trm_eq_refl;
(* lda *)
intros;Refine fst (deMorgan ? (member VVeq v (append (tvars A) (tvars B)))) nocc;
intros neqV noccAB;
Refine fst (deMorgan (member VVeq v (tvars A)) (member VVeq v (tvars B)));
Qrepl Q_sym (member_append_lem VVeq v (tvars A) (tvars B));Immed;
intros noccA noccB;
Equiv is_tt (Trm_eq (lda n (alpha p v (alpha' v p A))
               (if ? (alpha' v p B) (alpha p v (alpha' v p B)))) ?);
Qrepl Trm_eq_subst (ihA noccA);
Qrepl Trm_eq_subst (ihB noccB);
Qrepl neqV;Refine Trm_eq_refl;
(* app *)
intros;
Refine fst (deMorgan (member VVeq v (tvars A)) (member VVeq v (tvars B)));
Qrepl Q_sym (member_append_lem VVeq v (tvars A) (tvars B));Immed;
intros noccA noccB;
Equiv is_tt (Trm_eq (app (alpha p v (alpha' v p A))
                    (alpha p v (alpha' v p B))) ?);
Qrepl Trm_eq_subst (ihA noccA);
Qrepl Trm_eq_subst (ihB noccB);
Refine Trm_eq_refl;
Save fresh_var_subst_lem;

Discharge p;

%\VerbFileOpen shape_lemma
Goal shape_lemma:
     {p:PP}{M:Trm}Ex2 [v:VV][M':Trm] and (is_tt (Trm_eq M (alpha p v M')))
                                         (is_ff (poccur p M'));
%\VerbFileClos shape_lemma
intros; Refine VVinf (tvars M);
intros v vFresh; Refine Ex2In v (alpha' v p M); Refine pair;
Qrepl Trm_eq_subst (fresh_var_subst_lem p vFresh); Refine Trm_eq_refl;
Refine not_poccur_after_alpha';
Save;























