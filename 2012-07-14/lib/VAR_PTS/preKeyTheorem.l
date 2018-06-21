Module preKeyTheorem Import ots;

(*************** the Key Theorem --- preliminaries !!! ****************)

[LGB = PROD|VV|GB];
[Lgb [v:VV][p:PP][A:Trm] = Pr v (Gb p A) : LGB];
[VarOf = Fst|VV|GB : LGB->VV];
[NamOf [b:LGB] = namOf (Snd b) : PP];
[TypOf [b:LGB] = typOf (Snd b) : Trm];
[LGB_surj_pair [b:LGB] : Q b (Lgb (VarOf b) (NamOf b) (TypOf b))
 = Q_subst (GB_surj_pair (Snd b))
           ([gb:GB]Q b (Pr (VarOf b) gb))
           (PROD_surj_pair b)];

[BindingCxt = LL|LGB];
[nilBCxt = NIL|LGB];

[Vars = map VarOf : BindingCxt->VVs];
[Names = map NamOf : BindingCxt->PPs];
[Types = map TypOf : BindingCxt->Trms];

[Vars_append_lem : {BG,BH:BindingCxt}
                    Q (Vars (append BG BH)) (append (Vars BG) (Vars BH))
                 = map_append_lem VarOf];
[Names_append_lem : {BG,BH:BindingCxt}
                     Q (Names (append BG BH)) (append (Names BG) (Names BH))
                  = map_append_lem NamOf];
[Types_append_lem : {BG,BH:BindingCxt}
                     Q (Types (append BG BH)) (append (Types BG) (Types BH))
                  = map_append_lem TypOf];

[PiOf : BindingCxt->Trm->Trm
      = foldleft ([b:LGB][A:Trm]pi (VarOf b) (TypOf b) A)];

[PiOf_append_lem : {BG,BH:BindingCxt}{M:Trm}
                    Q (PiOf (append BG BH) M) (PiOf BH (PiOf BG M))
                 = foldleft_append_lem ([b:LGB][A:Trm]pi (VarOf b) (TypOf b) A)];

[LdaOf : BindingCxt->Trm->Trm
       = foldleft ([b:LGB][A:Trm]lda (VarOf b) (TypOf b) A)];

[LdaOf_append_lem : {BG,BH:BindingCxt}{M:Trm}
                     Q (LdaOf (append BG BH) M) (LdaOf BH (LdaOf BG M))
                  = foldleft_append_lem ([b:LGB][A:Trm]lda (VarOf b) (TypOf b) A)];

Goal {BG:BindingCxt}{b:LGB}{a:Trm}
      Ex3 [u:VV][A,B:Trm]is_tt (Trm_eq (PiOf (CONS b BG) a) (pi u A B));
Refine LLrec [BG|BindingCxt]{b:LGB}{a:Trm}
      Ex3 [u:VV][A,B:Trm]is_tt (Trm_eq (PiOf (CONS b BG) a) (pi u A B));
intros;Refine Ex3In (VarOf b) (TypOf b) a;Refine Trm_eq_refl;
intros;Refine LLih b (pi (VarOf b1) (TypOf b1) a);
Save PiOf_CONS_lem;

Goal {BG:BindingCxt}{b:LGB}{a:Trm}
      Ex3 [u:VV][A,B:Trm]is_tt (Trm_eq (LdaOf (CONS b BG) a) (lda u A B));
Refine LLrec [BG|BindingCxt]{b:LGB}{a:Trm}
      Ex3 [u:VV][A,B:Trm]is_tt (Trm_eq (LdaOf (CONS b BG) a) (lda u A B));
intros;Refine Ex3In (VarOf b) (TypOf b) a;Refine Trm_eq_refl;
intros;Refine LLih b (lda (VarOf b1) (TypOf b1) a);
Save LdaOf_CONS_lem;

Goal {BG|BindingCxt}{a|Trm}{s|SS}
     {eq:is_tt (Trm_eq (PiOf BG a) (sort s))}Q BG nilBCxt;
Refine LLrec [BG|BindingCxt]{a|Trm}{s|SS}
             {eq:is_tt (Trm_eq (PiOf BG a) (sort s))}Q BG nilBCxt;
intros;Refine Q_refl;
intros;Refine PiOf_CONS_lem prem b a;
intros;Refine tt_not_ff (Q_sym (?:is_tt (Trm_eq (pi t s1 u) (sort s))));
       Qrepl Q_sym (Trm_eq_subst H);Immed;
Save BCxt_sort_character;

Goal {BG|BindingCxt}{a|Trm}{p|PP}
     {eq:is_tt (Trm_eq (LdaOf BG a) (par p))}Q BG nilBCxt;
Refine LLrec [BG|BindingCxt]{a|Trm}{p|PP}
             {eq:is_tt (Trm_eq (LdaOf BG a) (par p))}Q BG nilBCxt;
intros;Refine Q_refl;
intros;Refine LdaOf_CONS_lem prem b a;
intros;Refine tt_not_ff (Q_sym (?:is_tt (Trm_eq (lda t s u) (par p))));
       Qrepl Q_sym (Trm_eq_subst H);Immed;
Save BCxt_par_character;

Goal {BG|BindingCxt}{X,A|Trm}{vcl:Vclosed X}{s|SS}
     {redX:par_bp_redn X (sort s)}
     {redBG:par_bp_redn X (PiOf BG A)}
      Q BG nilBCxt;
Refine LLrec [BG|BindingCxt]
     {X,A|Trm}{vcl:Vclosed X}{s|SS}
     {redX:par_bp_redn X (sort s)}
     {redBG:par_bp_redn X (PiOf BG A)}
      Q BG nilBCxt;
intros;Refine Q_refl;
intros;Refine PiOf_CONS_lem prem b A;
intros v A' B' eq;Refine par_bp_redn_DP vcl redX redBG;
Qrepl Trm_eq_subst eq;
intros S hypS;Refine par_bp_redn_pi_character (snd hypS);
intros w A'' B'' hypP;
Refine tt_not_ff (Q_sym (?:is_tt (Trm_eq (pi w A'' B'') (sort s))));
Qrepl Trm_eq_subst (and3_out3 hypP);
Refine par_bp_redn_sort_character (fst hypS);
Save BCxt_red_sort_character;

Goal {BG|BindingCxt}{X|Trm}{vcl:Vclosed X}{s|SS}{u|VV}{A,B|Trm}
     {redBG:par_bp_redn X (PiOf BG (sort s))}
     {redX:par_bp_redn X (pi u A B)}
      Ex2 [b:LGB][BH:BindingCxt]Q BG (append BH (unit b));
Refine LLrec [BG|BindingCxt]
     {X|Trm}{vcl:Vclosed X}{s|SS}{u|VV}{A,B|Trm}
     {redBG:par_bp_redn X (PiOf BG (sort s))}
     {redX:par_bp_redn X (pi u A B)}
      Ex2 [b:LGB][BH:BindingCxt]Q BG (append BH (unit b));
intros;Refine par_bp_redn_DP vcl redX redBG;
intros ss hypS;Refine par_bp_redn_pi_character (fst hypS);
intros v A' B' hypP;
Refine tt_not_ff (Q_sym (?:is_tt (Trm_eq (pi v A' B') (sort s))));
Qrepl Trm_eq_subst (and3_out3 hypP);
Refine par_bp_redn_sort_character (snd hypS);
intros;Refine non_nil_list_lem prem b;
Save BCxt_red_pi_character;

[IllFormed : BindingCxt->BB
           = LLrec ([_:BindingCxt]BB) ff
                   ([b:LGB][BG:BindingCxt][bb:BB]
                     orr (member VVeq (VarOf b) (Vars BG)) bb)];

[WellFormed [BG:BindingCxt] = is_ff (IllFormed BG)];

Goal {BG:BindingCxt}{puA,qvB:LGB}
      Q (member VVeq (VarOf puA) (Vars (append BG (unit qvB))))
        (orr (member VVeq (VarOf puA) (Vars BG)) (VVeq (VarOf qvB) (VarOf puA)));
intros;
Qrepl Vars_append_lem BG (unit qvB);
Qrepl member_append_lem VVeq (VarOf puA) (Vars BG) (Vars (unit qvB));
Equiv Q (orr ? (orr ? ff)) ?;Qrepl VVsym (VarOf puA) (VarOf qvB);
Qrepl ff_orr_unit (VVeq (VarOf qvB) (VarOf puA));Refine Q_refl;
Save member_Vars_lem;

Goal {BG:BindingCxt}{b:LGB}(WellFormed (append BG (unit b)))->
      and (WellFormed BG) (is_ff (member VVeq (VarOf b) (Vars BG)));
Refine LLrec [BG:BindingCxt]{b:LGB}{wf:WellFormed (append BG (unit b))}
              and (WellFormed BG) (is_ff (member VVeq (VarOf b) (Vars BG)));
intros;Refine fst (deMorgan ? ?) wf;
intros;
Refine fst (deMorgan (member VVeq (VarOf b) (Vars (append prem (unit b1))))
                     (IllFormed (append prem (unit b1)))) wf;
Qrepl member_Vars_lem prem b b1;
intros mem wf1;
Refine fst (deMorgan (member VVeq (VarOf b) (Vars prem))
                     (VVeq (VarOf b1) (VarOf b))) mem;
intros mem1 eqV;Refine LLih ? wf1;
intros wf2 mem2;Refine pair;
Refine snd (deMorgan ? ?) (pair mem1 wf2);
Refine snd (deMorgan ? ?) (pair eqV mem2);
Save WellFormed_split_lem;

Goal {BG:BindingCxt}{b:LGB}(WellFormed BG)->
     (is_ff (member VVeq (VarOf b) (Vars BG)))->
      WellFormed (append BG (unit b));
Refine LLrec [BG:BindingCxt]{b:LGB}{wf:WellFormed BG}
             {mem:is_ff (member VVeq (VarOf b) (Vars BG))}
              WellFormed (append BG (unit b));
intros;Refine snd (deMorgan ? ?) (pair mem (Q_refl ?));
intros;Refine fst (deMorgan ? (IllFormed ?)) wf;
intros mem1 wf1;Refine fst (deMorgan ? (member ? ? (Vars ?))) mem;
intros eqV mem1;Refine snd (deMorgan (member ? ? (Vars (append ? ?)))
                                     (IllFormed (append ? ?)));
Refine pair;Qrepl member_Vars_lem prem b b1;
Refine snd (deMorgan ? ?);Refine pair;Immed;
Refine LLih;Immed;
Save WellFormed_combine_lem;

[Bvsub [N:Trm][x:VV] : BindingCxt->BindingCxt
                     = map ([b:LGB]Lgb (VarOf b) (NamOf b) (vsub N x (TypOf b)))];

[Bvsub_append_lem [N:Trm][x:VV]
                 : {BG,BH:BindingCxt}
                    Q (Bvsub N x (append BG BH)) (append (Bvsub N x BG) (Bvsub N x BH))
                 = map_append_lem
                   ([b:LGB]Lgb (VarOf b) (NamOf b) (vsub N x (TypOf b)))];

[BindingSub : BindingCxt->Trm->Trm
            = foldleft ([b:LGB][A:Trm]alpha (NamOf b) (VarOf b) A)];

[BindingSub_append_lem : {BG,BH:BindingCxt}{M:Trm}
                          Q (BindingSub (append BG BH) M)
                            (BindingSub BH (BindingSub BG M))
                       = foldleft_append_lem
                         ([b:LGB][A:Trm]alpha (NamOf b) (VarOf b) A)];

Goal {N:Trm}{x:VV}{BG:BindingCxt}[BH = Bvsub N x BG]
      and3 ({M:Trm}Q (BindingSub BG M) (BindingSub BH M))
           (Q (Vars BG) (Vars BH))
           (Q (IllFormed BG) (IllFormed BH)); 
intros;Refine LLrec [BG|BindingCxt][BH = Bvsub N x BG]
      and3 ({M:Trm}Q (BindingSub BG M) (BindingSub BH M))
           (Q (Vars BG) (Vars BH))
           (Q (IllFormed BG) (IllFormed BH)); 
intros;Refine pair3;intros;Refine Q_refl;Refine Q_refl;Refine Q_refl;
intros;Refine LLih;
intros ih_BSub ih_Vars ih_IllFormed;Refine pair3;
[v = VarOf b][p = NamOf b][A = TypOf b];
[vsubA = vsub N x A][Bvsub_prem = Bvsub N x prem];

intros;
Qrepl BindingSub_append_lem (unit b) prem M;
Qrepl BindingSub_append_lem (unit (Lgb v p vsubA)) Bvsub_prem M;
Qrepl ih_BSub (alpha p v M);Refine Q_refl;

Equiv Q (CONS v (Vars prem)) (CONS v (Vars (Bvsub_prem)));
Qrepl ih_Vars;Refine Q_refl;

Equiv Q (orr (member VVeq v (Vars prem)) (IllFormed prem))
        (orr (member VVeq v (Vars (Bvsub_prem))) (IllFormed (Bvsub_prem)));
Qrepl ih_Vars;Qrepl ih_IllFormed;Refine Q_refl;
Save Bvsub_lemma;

Goal {N|Trm}{vclN:Vclosed N}{x|VV}{BG|BindingCxt}[BH = Bvsub N x BG]
     (is_ff (member VVeq x (Vars BG)))->
      and3 ({M:Trm}Q (vsub N x (BindingSub BG M)) (BindingSub BG (vsub N x M)))
           ({M:Trm}Q (vsub N x (PiOf BG M)) (PiOf BH (vsub N x M)))
           ({M:Trm}Q (vsub N x (LdaOf BG M)) (LdaOf BH (vsub N x M))); 
intros;
Refine LLrec [BG|BindingCxt][BH = Bvsub N x BG]{nocc:is_ff (member VVeq x (Vars BG))}
      and3 ({M:Trm}Q (vsub N x (BindingSub BG M)) (BindingSub BG (vsub N x M)))
           ({M:Trm}Q (vsub N x (PiOf BG M)) (PiOf BH (vsub N x M)))
           ({M:Trm}Q (vsub N x (LdaOf BG M)) (LdaOf BH (vsub N x M)));Immed;
intros;Refine pair3;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;

intros;Refine fst (deMorgan (VVeq ? ?) (member VVeq ? (Vars ?))) nocc;
intros neqV nocc_prem;Refine LLih nocc_prem;
intros ih_BSub ih_Pi ih_Lda;Refine pair3;
[v = VarOf b][p = NamOf b][A = TypOf b];
[vsubA = vsub N x A][Bvsub_prem = Bvsub N x prem];

intros;
Qrepl BindingSub_append_lem (unit b) prem M;
Qrepl BindingSub_append_lem (unit b) prem (vsub N x M);
Qrepl Q_sym (vsub_commutes_vsub neqV vclN (Vclosed_par p) M);
Qrepl ih_BSub (alpha p v M);Refine Q_refl;

intros;
Qrepl PiOf_append_lem (unit b) prem M;
Qrepl PiOf_append_lem (unit (Lgb v p vsubA)) Bvsub_prem (vsub N x M);
Qrepl ih_Pi (pi v A M);
Equiv Q (PiOf Bvsub_prem (pi v vsubA (if ? ? (vsub ? ? ?)))) ?;
Qrepl neqV;Refine Q_refl;

intros;
Qrepl LdaOf_append_lem (unit b) prem M;
Qrepl LdaOf_append_lem (unit (Lgb v p vsubA)) Bvsub_prem (vsub N x M);
Qrepl ih_Lda (lda v A M);
Equiv Q (LdaOf Bvsub_prem (lda v vsubA (if ? ? (vsub ? ? ?)))) ?;
Qrepl neqV;Refine Q_refl;

Save Bvsub_fresh_var_lemma;

[CxtOf [BG:BindingCxt][G:Cxt] : Cxt =
        LLrec ([_:BindingCxt]Cxt) G
              ([b:LGB][BG:BindingCxt][H:Cxt]
                CONS (Gb (NamOf b) (BindingSub BG (TypOf b))) H) BG];

Goal {G:Cxt}{b:LGB}[n = VarOf b]$[p = NamOf b]$[A = TypOf b]
     {BG|BindingCxt}(is_ff (member VVeq n (Vars BG)))->
      Q (CxtOf (append BG (unit b)) G)
        (CxtOf (Bvsub (par p) n BG) (CONS (Gb p A) G));
intros;Refine LLrec [BG:BindingCxt]{nocc:is_ff (member VVeq n (Vars BG))}
Q (CxtOf (append BG (unit b)) G) (CxtOf (Bvsub (par p) n BG) (CONS (Gb p A) G));
Immed;
intros;Refine Q_refl;
intros;
[n1 = VarOf b1][p1 = NamOf b1][A1 = TypOf b1];
Refine fst (deMorgan (VVeq n n1) (member VVeq n (Vars prem))) nocc;
intros neqV nocc_prem;
Equiv Q (CONS (Gb p1 (BindingSub (append prem (unit b)) A1))
              (CxtOf (append prem (unit b)) G)) ?;
Equiv Q ? (CONS (Gb p1 (BindingSub (Bvsub (par p) n prem) (alpha p n A1)))
                (CxtOf (Bvsub (par p) n prem) (CONS (Gb p A) G)));
Qrepl LLih nocc_prem;Qrepl BindingSub_append_lem prem (unit b) A1;
Qrepl and3_out1 (Bvsub_fresh_var_lemma (Vclosed_par p) nocc_prem) A1;
Qrepl and3_out1 (Bvsub_lemma (par p) n prem) (alpha p n A1);
Refine Q_refl;
Save CxtOf_alpha_lemma;

[BCxt_Trm_tvars [BG:BindingCxt][M:Trm] : VVs
 = foldright ([b:LGB][vs:VVs]append (CONS (VarOf b) (tvars (TypOf b))) vs)
              BG (tvars M)];

Goal {BG:BindingCxt}{N:Trm}{p:PP}
      Ex3 [x:VV][L:Trm][BH:BindingCxt]and5
          (is_ff (poccur p L)) (is_tt (Trm_eq N (alpha p x L)))
          (is_ff (member VVeq x (Vars BH))) (Q BG (Bvsub (par p) x BH))
          ({M|Trm}{noccM:is_ff (poccur p M)}and
            (is_ff (poccur p (PiOf BH M)))
            (is_ff (poccur p (LdaOf BH M)))
           );
intros;Refine VVinf (BCxt_Trm_tvars BG N);
intros x noccBGN;
[L = alpha' x p N];
[noccL : is_ff (poccur p L) = not_poccur_after_alpha' p x N];

Refine LLrec [BG:BindingCxt]{nocc:is_ff (member VVeq x (BCxt_Trm_tvars BG N))}
Ex [BH:BindingCxt]and4
          (is_tt (Trm_eq N (alpha p x L)))
          (is_ff (member VVeq x (Vars BH))) (Q BG (Bvsub (par p) x BH))
          ({M:Trm}{noccM:is_ff (poccur p M)}and
            (is_ff (poccur p (PiOf BH M)))
            (is_ff (poccur p (LdaOf BH M)))
           );
Immed;

intros;Refine ExIn nilBCxt;
Qrepl Trm_eq_sym N (alpha p x L);
Refine pair4 (fresh_var_subst_lem p nocc) (Q_refl ff) (Q_refl nilBCxt);
intros;Refine pair noccM noccM;

intros ___;
[v = VarOf b][q = NamOf b][A = TypOf b];
Qrepl member_append_lem VVeq x (CONS v (tvars A)) (BCxt_Trm_tvars prem N);
intros;Refine fst (deMorgan ? ?) nocc;
intros nocc_vA nocc_prem;Refine fst (deMorgan ? (textual_voccur ? ?)) nocc_vA;
intros neqV noccA;Refine LLih nocc_prem;
intros BH hypBH;Refine hypBH;
intros eqM noccBH eqBG noccBSubPiLda;
Refine ExIn (CONS (Lgb v q (alpha' x p A)) BH);Refine pair4;Immed;
Refine snd (deMorgan ? ?);Refine pair;Immed;
Qrepl LGB_surj_pair b;
Equiv Q ? (CONS (Lgb v q (alpha p x (alpha' x p A))) (Bvsub (par p) x BH));
Qrepl eqBG;Qrepl Trm_eq_subst (fresh_var_subst_lem p noccA);
Refine Q_refl;

intros;Refine pair;

Qrepl PiOf_append_lem (unit (Lgb v q (alpha' x p A))) BH M;
Refine fst (noccBSubPiLda (pi v (alpha' x p A) M) ?);
Refine pocc_split_lem2 ? noccM;Refine not_poccur_after_alpha';

Qrepl LdaOf_append_lem (unit (Lgb v q (alpha' x p A))) BH M;
Refine snd (noccBSubPiLda (lda v (alpha' x p A) M) ?);
Refine pocc_split_lem2 ? noccM;Refine not_poccur_after_alpha';

intros BH hyp;Refine hyp;
intros;Refine Ex3In x L BH;Refine pair5;Immed;
Save BCxt_Trm_shape_lemma;

Goal {G|Cxt}{lgb|LGB}[p = NamOf lgb][v = VarOf lgb][A = TypOf lgb]
     {BK|BindingCxt}[BH = append BK (unit lgb)]
     (Valid (CxtOf BH G))->(is_ff (member VVeq v (Vars BK)))->
     {L|Trm}{vcl:Vclosed L}[subGB = [b:GB]Gb(namOf b) (psub L p (typOf b))]
     {m|Trm}((is_ff (Poccur p G))->is_ff (poccur p (LdaOf BK m)))->
      and (is_ff (poccur p (BindingSub BK m)))
          (Ex [H:Cxt]and (Q (CxtOf BH G) (append H (CONS (Gb p A) G)))
                         (Q (CxtOf (Bvsub L v BK) G) (append (map subGB H) G)));

intros;
Refine LLrec [BK:BindingCxt][BH = append BK (unit lgb)]
       {val:Valid (CxtOf BH G)}[subGB = [b:GB]Gb(namOf b) (psub L p (typOf b))]
       {nocc:is_ff (member VVeq v (Vars BK))}
       {M|Trm}{noccLda:{noccG:is_ff (Poccur p G)}is_ff (poccur p (LdaOf BK M))}
        and3 (is_ff (poccur p M))
             ({N|Trm}{noccN:is_ff (poccur p N)}is_ff (poccur p (BindingSub BK N)))
             (Ex [K:Cxt]and (Q (CxtOf BH G) (append K (CONS (Gb p A) G)))
                            (Q (CxtOf (Bvsub L v BK) G) (append (map subGB K) G)));
Immed;

intros;Refine val;intros X Y jXY;Refine pair3;
Refine noccLda;Refine CxtCorrect0 jXY;
intros;Immed;
Refine ExIn nilCxt;Refine pair (Q_refl ?) (Q_refl ?);

intros;Refine fst (deMorgan (VVeq ? ?) (member ? ? (Vars ?))) nocc;
intros neqV nocc_prem;Refine LLih (tails_Valid val) nocc_prem noccLda;
intros nocc_lda noccBSub exK;Refine pocc_combine_lem nocc_lda;
intros noccB noccM;Refine exK;
intros K hypK;Refine hypK;
intros eqK eqKsub;Refine pair3 noccM;
[q = NamOf b][w = VarOf b][B = TypOf b];
[noccK : is_ff (Poccur q (append K (CONS (Gb p A) G)))
       = POCCUR_Poccur (wV_notPOCCURinTl (Valid_wValid
             (Q_subst (Q_resp (CONS ?) eqK) Valid val)))];

intros;Refine noccBSub;Refine not_pocc_vsub_lem noccN;Qrepl pocc_par_lem p q;
       Qrepl PPsym p q;Refine Poccur_compound_lem noccK;
       intros;Immed;

Refine ExIn (CONS (Gb q (alpha p v (BindingSub prem B))) K);

Refine pair (Q_resp_CONS ? eqK) (Q_resp_CONS ? eqKsub);
Equiv Q (Gb q (BindingSub (append ? ?) B)) ?;
Qrepl BindingSub_append_lem prem (unit lgb) B;Refine Q_refl;

Equiv Q (Gb q (BindingSub (Bvsub ? ? ?) (vsub L v B))) ?;
Qrepl Q_sym (and3_out1 (Bvsub_lemma L v prem) (vsub L v B));
Qrepl Q_sym (and3_out1 (Bvsub_fresh_var_lemma vcl nocc_prem) B);
Expand subGB1;
Qrepl Trm_eq_subst (vsub_is_psub_alpha L v (noccBSub noccB));
Refine Q_refl;

intros noccM noccBKM;Refine pair;Refine noccBKM;Immed;
Save Valid_BCxt_subst_lemma;
