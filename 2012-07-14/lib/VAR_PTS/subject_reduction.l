Module subject_reduction Import pre_subj_red no_red;


[cnv_no_red1_sym [A,A'|Trm][H:no_red1 A A'] : cnv A' A = 
               cnv_red1_sym (no_par_red1 H)];


(* We consider consider a context and a term together as the subject,
 * and define what "one step reduction" means on the subject.
 *)

(* red1 on contexts *)
Inductive [red1Cxt: Cxt->Cxt->Prop]  NoReductions Inversion
Constructors
 [red1CxtNIL: red1Cxt nilCxt nilCxt]
 [red1CxtCONS: {b,b'|GB}{G,G'|Cxt}{sc:and (Q (namOf b) (namOf b'))
                                          (no_red1 (typOf b) (typOf b'))}
               {premG:red1Cxt G G'}
               red1Cxt (CONS b G) (CONS b' G')];

[red1CxtRec = red1Cxt_elim
            : {C:{J,K|Cxt}(red1Cxt J K)->Prop}
   {nil:C red1CxtNIL}
   {cons:{b,b'|GB}{G,G'|Cxt}{sc:and (Q (namOf b) (namOf b'))
                                    (no_red1 (typOf b) (typOf b'))}
         {premG:red1Cxt G G'}{ih:C premG}C (red1CxtCONS sc premG)}
   {J,K|Cxt}{t:red1Cxt J K}C t];

Goal red1Cxt_refl:
     {G|Cxt}(VclCxt G)->red1Cxt G G;
Refine VclCxt_elim [G:Cxt][_:VclCxt G]red1Cxt G G;
intros; Refine red1CxtNIL;
intros; Refine red1CxtCONS; Refine pair (Q_refl ?) (no_red1_refl vclA);
Immed;
Save red1Cxt_refl;

Goal red1Cxt_VclCxt:
     {G,G'|Cxt}(red1Cxt G G')->and (VclCxt G) (VclCxt G');
Refine red1CxtRec [G,G':Cxt][_:red1Cxt G G']and (VclCxt G) (VclCxt G');
Refine pair VCnil VCnil;
intros; Refine no_red1_Vclosed (snd sc); Refine ih; intros;
Qrepl GB_surj_pair b; Qrepl GB_surj_pair b'; 
Refine pair (VCcons ???) (VCcons ???); Immed;
Save;

Goal {K|Cxt}(red1Cxt nilCxt K)->is_tt (Cxt_eq K nilCxt);
intros;
Refine red1CxtRec [G,G':Cxt][_:red1Cxt G G']
                  {eq:is_tt (Cxt_eq G nilCxt)}is_tt (Cxt_eq G' nilCxt);
Immed;
intros;Refine Cxt_eq_refl;
intros;Refine tt_not_ff (Q_sym eq);
Refine Cxt_eq_refl;
Save red1Cxt_nil_character;

Goal {p|PP}{A|Trm}{G,K|Cxt}(red1Cxt (CONS (Gb p A) G) K)->
      Ex2 [G':Cxt][A':Trm]and3 (is_tt (Cxt_eq K (CONS (Gb p A') G')))
                               (red1Cxt G G')
                               (no_red1 A A');
intros;
Refine red1CxtRec [H,K:Cxt][_:red1Cxt H K]
                  {eq:is_tt (Cxt_eq H (CONS (Gb p A) G))}
                  Ex2 [G':Cxt][A':Trm]
                  and3 (is_tt (Cxt_eq K (CONS (Gb p A') G')))
                              (red1Cxt G G')
                              (no_red1 A A');Immed;
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine new_eqCxtLem (Cxt_eq_subst
                       (Q_subst (GB_surj_pair b)
                                ([b:GB]is_tt (Cxt_eq (CONS b ?) ?)) eq));
intros eqP eqA eqG;
Qrepl Q_sym eqP;Qrepl Q_sym eqA;Qrepl Q_sym eqG;
Refine Ex2In G' (typOf b');Refine pair3;
Qrepl fst sc;Qrepl GB_surj_pair b';Refine Cxt_eq_refl;
Refine premG;
Refine snd sc;
Refine Cxt_eq_refl;
Save red1Cxt_cons_character;

Goal {G,K|Cxt}(red1Cxt G K)->Q (globalNames G) (globalNames K);
Refine red1CxtRec [G,K|Cxt][_:red1Cxt G K]Q (globalNames G) (globalNames K);
Refine Q_refl;
intros;
Equiv Q (CONS (namOf b) (globalNames G)) (CONS (namOf b') (globalNames G'));
Qrepl (fst sc);Qrepl ih;Refine Q_refl;
Save red1Cxt_globalNames;

Goal {G,K|Cxt}(red1Cxt G K)->{p:PP}Q (Poccur p G) (Poccur p K);
intros;Expand Poccur;Qrepl red1Cxt_globalNames H;Refine Q_refl;
Save red1Cxt_Poccur_lem;

Goal {G,K|Cxt}(red1Cxt G K)->{p|PP}(is_tt (POCCUR p K))->is_tt (POCCUR p G);
Refine red1CxtRec [G,K|Cxt][_:red1Cxt G K]
                  {p|PP}{occ:is_tt (POCCUR p K)}is_tt (POCCUR p G);
intros;Immed;
intros;
Refine snd (orr_character (PPeq p (namOf b))
                          (member PPeq p (append (params (typOf b))
                                                 (freeNames G))));
[lem : or (is_tt (PPeq p (namOf b')))
          (is_tt (member PPeq p (append (params (typOf b'))
                                        (freeNames G'))))
     = fst (orr_character (PPeq p (namOf b'))
                          (member PPeq p (append (params (typOf b'))
                                                 (freeNames G')))) occ];
Refine lem;
intros lem1;Refine inl;Qrepl (fst sc);Immed;
intros lem1;Refine inr;
Qrepl member_append_lem PPeq p (params (typOf b)) (freeNames G);
Refine snd (orr_character (poccur p (typOf b)) (POCCUR p G));
[lem2 : or (is_tt (poccur p (typOf b'))) (is_tt (POCCUR p G'))
      = fst (orr_character (poccur p (typOf b')) (POCCUR p G'))
        (Q_subst (member_append_lem PPeq p (params (typOf b')) (freeNames G'))
                  is_tt lem1)];
Refine lem2;
intros lem3;Refine inl;Refine no_red1_refl_pocc (snd sc) lem3;
intros lem3;Refine inr;Refine ih;Immed;
Save red1Cxt_POCCUR_lem;

Goal {G,K|Cxt}(red1Cxt G K)->{p|PP}(is_ff (POCCUR p G))->is_ff (POCCUR p K);
intros;Refine B_contrapos;Refine +1 red1Cxt_POCCUR_lem;Immed;
Save red1Cxt_not_POCCUR_lem;

Goal {G|Cxt}(wValid G)->{GG|Cxt}(red1Cxt G GG)->wValid GG;
Refine wValidRec [G:Cxt][_:wValid G]{GG|Cxt}{redC:red1Cxt G GG}wValid GG;
intros;Qrepl Cxt_eq_subst (red1Cxt_nil_character redC);Refine wVnil;
intros;
Refine red1CxtRec [GX,GG:Cxt][_:red1Cxt GX GG]
                  {eqC:is_tt (Cxt_eq (CONS (Gb p A) G) GX)}wValid GG;
Immed;
intros;Refine tt_not_ff (Q_sym eqC);
intros;
[lem : and (is_tt (GBeq (Gb p A) b)) (is_tt (Cxt_eq G G1))
     = fst (andd_character (GBeq (Gb p A) b) (Cxt_eq G G1)) eqC];
Qrepl GB_surj_pair b'; Qrepl Q_sym (fst sc);
Refine wVcons;
Refine snd (no_red1_Vclosed (snd sc));
Qrepl Q_sym (GBeq_subst (fst lem));
Qrepl Q_sym (red1Cxt_Poccur_lem premG p);
Qrepl Q_sym (Cxt_eq_subst (snd lem)); Refine sc_p;
intros;
Qrepl Q_sym (red1Cxt_Poccur_lem premG q);
Qrepl Q_sym (Cxt_eq_subst (snd lem));
Refine sc_A;
Qrepl snd (Q_resp_bnd_proj (GBeq_subst (fst lem)));
Refine no_red1_refl_pocc (snd sc) H;
Refine ih; Qrepl Cxt_eq_subst (snd lem); Immed;
Refine Cxt_eq_refl;
Save red1Cxt_preserves_wValid;

Goal {G,GG|Cxt}(red1Cxt G GG)->
     {p|PP}{A|Trm}(is_tt (GBoccur (Gb p A) G))->
     Ex [AA:Trm] and (is_tt (GBoccur (Gb p AA) GG)) (no_red1 A AA);
Refine red1CxtRec [G,GG:Cxt][_:red1Cxt G GG]
       {p|PP}{A|Trm}{occ:is_tt (GBoccur (Gb p A) G)}
       Ex [AA:Trm] and (is_tt (GBoccur (Gb p AA) GG)) (no_red1 A AA);
intros;Refine tt_not_ff (Q_sym occ); 
intros;
Qrepl GB_surj_pair b'; Qrepl Q_sym (fst sc);
Refine fst (orr_character (GBeq ? ?) (GBoccur ? G)) occ;
intros case_hd;
Refine ExIn (typOf b');
Qrepl fst (Q_resp_bnd_proj (GBeq_subst case_hd));
Qrepl snd (Q_resp_bnd_proj (GBeq_subst case_hd));
Refine pair;
Refine snd (orr_character ? (GBoccur ? G'));
Refine inl;Refine GBeq_refl;
Refine snd sc;
intros case_tl;Refine ih case_tl;
intros AA AAspec; Refine ExIn AA; Refine pair;
Refine snd (orr_character ? (GBoccur ? ?)); 
Refine inr; Refine fst AAspec;
Refine snd AAspec;
Save red1Cxt_GBoccur_lem;

(* red1 on subjects *)
Inductive [red1Subj: Cxt->Trm->Cxt->Trm->Prop] NoReductions  Constructors
 [red1SubjCT: {G,G'|Cxt}{premC:red1Cxt G G'}
              {A,A'|Trm}{premT:no_red1 A A'}
              red1Subj G A G' A'];

[red1SubjRec = red1Subj_elim
             : {C:{J|Cxt}{A|Trm}{J'|Cxt}{A'|Trm}(red1Subj J A J' A')->Prop}
   {ct:{G,G'|Cxt}{premC:red1Cxt G G'}
       {A,A'|Trm}{premT:no_red1 A A'}
        C (red1SubjCT premC premT)}
   {J|Cxt}{A|Trm}{J'|Cxt}{A'|Trm}{t:red1Subj J A J' A'}C t];


Goal {G|Cxt}{M|Trm}{G'|Cxt}{M'|Trm}(red1Subj G M G' M')->
      and (red1Cxt G G') (no_red1 M M');
Refine red1SubjRec [G|Cxt][M|Trm][G'|Cxt][M'|Trm][_:red1Subj G M G' M']
                    and (red1Cxt G G') (no_red1 M M');
intros;Refine pair;Immed;
Save red1SubjElim;

Goal subject_reduction_lem:
     {G|Cxt}{M,A|Trm}(gts G M A)->
     {G'|Cxt}{M'|Trm}(red1Subj G M G' M')->gts G' M' A;

intros;Refine red1SubjElim H1;
intros;
Refine gtsRec [Gamma:Cxt][M,A:Trm][_:gts Gamma M A]
              {Delta|Cxt}{R|Trm}
              {redC:red1Cxt Gamma Delta}
              {redT:no_red1 M R}
                gts Delta R A;Immed;
(* Ax *)
intros;
Qrepl Trm_eq_subst (no_red1_sort_character redT);
Qrepl Cxt_eq_subst (red1Cxt_nil_character redC);
Refine Ax;Immed;
(* Start *)
intros;
Qrepl Trm_eq_subst (no_red1_par_character redT);
Refine red1Cxt_cons_character redC;
intros Delta' A' hyp; Refine hyp; intros eqDelta redG redA;
[gts_DeltaA = ih redG redA : gts Delta' A' (sort s)];
Qrepl Cxt_eq_subst eqDelta;
Refine tCnv (cnv_no_red1_sym redA) (Start ? gts_DeltaA);
Refine +2 weakening (ih redG (no_red1_refl ?)) ?+1 gts_DeltaA;
Qrepl Q_sym (red1Cxt_Poccur_lem redG p);
Immed; Refine fst (no_red1_Vclosed redA);
(* vWeak *)
intros;
Qrepl Trm_eq_subst (no_red1_par_character redT);
Refine red1Cxt_cons_character redC;
intros Delta' A' hyp;
[eqDelta = and3_out1 hyp];
[redG = and3_out2 hyp];
[redA = and3_out3 hyp];
[gts_DeltaA = r_ih redG redA : gts Delta' A' (sort s)];
Qrepl Cxt_eq_subst eqDelta;
Refine vWeak ? (l_ih redG (no_red1_refl ?)) gts_DeltaA;
Qrepl Q_sym (red1Cxt_Poccur_lem redG p);Immed; Refine Vclosed_par;
(* sWeak *) 
intros;
Qrepl Trm_eq_subst (no_red1_sort_character redT);
Refine red1Cxt_cons_character redC;
intros Delta' A' hyp;
[eqDelta = and3_out1 hyp];
[redG = and3_out2 hyp];
[redA = and3_out3 hyp];
[gts_DeltaA = r_ih redG redA : gts Delta' A' (sort s)];
Qrepl Cxt_eq_subst eqDelta;
Refine sWeak ? (l_ih redG (no_red1_refl ?)) gts_DeltaA;
Qrepl Q_sym (red1Cxt_Poccur_lem redG p);Immed; Refine Vclosed_sort;
(* Pi *) 
intros;Refine no_red1_pi_character redT;
intros v A' B' hyp; Refine hyp; intros redA redB h3;
[noccB' = not_pocc_resp_no_red1_alpha redB noccB];
[gts_DeltaA : gts Delta A' (sort s1) = l_ih redC redA];
[gts_DeltaB : gts (CONS (Gb p A') Delta) (alpha p v B') (sort s2)
            = r_ih (red1CxtCONS|(Gb p A1)|(Gb p A')
                                (pair (Q_refl ?) redA) redC)
                   (redB ?)];
[eqR : Q R (pi v A' B') = Q_sym (Trm_eq_subst h3)];
Qrepl eqR;Refine Pi sc noccB' gts_DeltaA gts_DeltaB;
(* Lda *)
intros;Refine no_red1_lda_character redT;
intros v A' M' hyp; Refine hyp; intros redA redM h3;
[noccM': is_ff (poccur p M'1)
       = not_pocc_resp_no_red1_alpha redM noccM];
[redP : no_red1 (pi m A1 B) (pi m A' B)
      = no_red1_pi|?|?|m|m redA noccB noccB
                     (no_red1_refl (snd (gts_Vclosed_lem l_prem)))];
[gts_DeltaM : gts (CONS (Gb p A') Delta) (alpha p v M'1) (alpha p m B)
            = l_ih (red1CxtCONS|(Gb p A1)|(Gb p A')
                                (pair (Q_refl ?) redA) redC)
                   (redM ?)];
[gts_DeltaA : gts Delta (pi m A1 B) (sort s)
            = r_ih redC (no_red1_refl (fst (gts_Vclosed_lem r_prem)))];
[gts_DeltaA' : gts Delta (pi m A' B) (sort s)
             = r_ih redC redP];
[eqR : Q R (lda v A' M'1) = Q_sym (Trm_eq_subst h3)];
Qrepl eqR;
Refine tCnv (cnv_no_red1_sym redP) 
            (Lda noccM' noccB gts_DeltaM gts_DeltaA')
            gts_DeltaA;
(* App *)
intros;
[vclL : Vclosed L = fst (gts_Vclosed_lem r_prem)];
[gts_DeltaM : gts Delta M1 (pi n A1 B)
   = l_ih redC (no_red1_refl (fst (gts_Vclosed_lem l_prem)))];
[gts_DeltaL : gts Delta L A1 = r_ih redC (no_red1_refl vclL)];
[vclP : Vclosed (pi n A1 B) = snd (gts_Vclosed_lem l_prem)];
[vclB : {q:PP}Vclosed (alpha q n B) = snd (Vclosed_pi_lem vclP)];
Refine type_correctness_pi gts_DeltaM;
intros s gts_DeltaPi;Refine gts_gen_pi gts_DeltaPi;
intros s1 s2 s3 p gen_hyp;Refine gen_hyp;
intros r gts_DeltaA noccB gts_DeltaB c;
[gts_DeltaBsub : gts Delta (psub L p (vsub (par p) n B)) (sort s2)
               = cut_rule gts_DeltaL ? gts_DeltaB];
Refine no_red1_app_character redT;

(* case app-reduction *)
intros case; Refine case; intros M' L' red_hyp;
Refine red_hyp; intros redM redL eq;
[vclL' : Vclosed L' = snd (no_red1_Vclosed redL)];
[eqR  : Q R (app M'1 L') = Q_sym (Trm_eq_subst eq)];
Qrepl eqR;
Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha L n noccB));
Refine tCnv ? (App (l_ih redC redM) (r_ih redC redL)) gts_DeltaBsub;
Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha L' n noccB));
Refine cnv_red1_sym; Refine par_red1_refl_psub_lem; Refine no_par_red1;
Immed;

(* case beta-reduction *)
intros case; Refine case; intros v A' b red_hyp;
Refine red_hyp; intros eqM eq;
[redM : no_red1 M1 (lda v A' b)
      = Q_subst (Q_sym (Trm_eq_subst eqM))
                (no_red1 M1) (no_red1_refl (fst (gts_Vclosed_lem l_prem)))];
[eqR : Q R (vsub L v b) = Q_sym (Trm_eq_subst eq)];
[noccDelta : is_ff (Poccur p Delta)
           = POCCUR_Poccur (notPOCCURinTl gts_DeltaB)];
[noccb : is_ff (poccur p b)
        = snd (pocc_combine_lem
             (fst (free_params_lem1 (l_ih redC redM) noccDelta)))];
Refine apts_gen_lda (l_ih redC redM);
intros s' B' w gen_hyp'; Refine gen_hyp';
intros gtsDeltaPi' gts_Deltab c';
[vclP' : Vclosed (pi w A' B') = fst (gts_Vclosed_lem gtsDeltaPi')];
[vclb : {q:PP}Vclosed (alpha q w B') = snd (Vclosed_pi_lem vclP')];
Refine cnvCR_pi c';
intros cnvA cnvB; Refine apts_gen_pi gtsDeltaPi';
intros s1' s2' s3' gen_hyp'';Refine gen_hyp'';
intros r' gts_DeltaA' gts_DeltaB' c'';
[gts_DeltaL' : gts Delta L A' = tCnv cnvA gts_DeltaL gts_DeltaA'];
[cnvLB : cnv (psub L p (alpha p w B')) (psub L p (alpha p n B))
       = psub_resp_cnv vclL (cnvB p) p];
Qrepl eqR;
Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha L n noccB));
Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha L v noccb));
Refine tCnv cnvLB  ? gts_DeltaBsub;
Refine cut_rule gts_DeltaL' ? (gts_Deltab noccDelta);

(* tCnv *) 
intros;
Refine tCnv sc (l_ih redC redT)
               (r_ih redC (no_red1_refl (fst (gts_Vclosed_lem r_prem))));
Save;


Goal gtsSR: {G|Cxt}{M,A|Trm}(gts G M A)->{M'|Trm}(par_redn M M')->gts G M' A;
intros;
[redG : red1Cxt G G = red1Cxt_refl (wValid_VclCxt (gts_wValid_lem H))];
Refine no_rednRec [M,M'|Trm]{j:gts G M A}gts G M' A;
intros;Refine subject_reduction_lem j (red1SubjCT redG r);
intros;Refine rt_ih;Refine lt_ih;Immed;
Refine +1 par_no_redn;Immed;
Save;

Goal gtsPR: {G|Cxt}{M,A|Trm}(gts G M A)->{A'|Trm}(par_redn A A')->gts G M A';
intros;Refine type_correctness H;
intros s cases;Refine cases;
intros case_sort;
Qrepl Trm_eq_subst
       (par_redn_sort_character
        (Q_subst (Trm_eq_subst case_sort) ([M:Trm]par_redn M A') H1));
Qrepl Q_sym (Trm_eq_subst case_sort);Immed;
intros case_type; Refine tCnv (cnv_redn H1) ? (gtsSR case_type H1);
Immed;
Save;

(* note use of _conv_ *)
Goal predicate_conv: 
     {G|Cxt}{M,A|Trm}(gts G M A)->{s|SS}(conv A (sort s))->gts G M (sort s);
intros; Refine gtsPR; Refine +2 conv_sort_character (conv_sym ?); Immed;
Save;

(* redn on contexts *)
Inductive [rednCxt : Cxt->Cxt->Prop] NoReductions Inversion
Constructors
[rednCxt_red1 : {G,G'|Cxt}{premG:red1Cxt G G'}rednCxt G G']
[rednCxt_trans : {G,J,K|Cxt}(rednCxt G J)->(rednCxt J K)->rednCxt G K];

[rednCxtRec = rednCxt_elim
            : {C:{J,K|Cxt}(rednCxt J K)->Prop}
   {RED1:{G,G'|Cxt}{premG:red1Cxt G G'}C (rednCxt_red1 premG)}
   {TRANS:{G,J,K|Cxt}
          {lt_prem:rednCxt G J}{rt_prem:rednCxt J K}
          {lt_ih:C lt_prem}{rt_ih:C rt_prem}
           C (rednCxt_trans lt_prem rt_prem)}
   {J,K|Cxt}{t:rednCxt J K}C t];

Goal rednCxt_VclCxt:
     {G,K|Cxt}(rednCxt G K)->and (VclCxt G) (VclCxt K);
Refine rednCxtRec [G,K:Cxt][_:rednCxt G K]and (VclCxt G) (VclCxt K);
intros; Refine red1Cxt_VclCxt premG;
intros; Refine lt_ih; Refine rt_ih; intros; Refine pair; Immed;
Save;

Goal {G|Cxt}(VclCxt G)->rednCxt G G;
intros;Refine rednCxt_red1;Refine red1Cxt_refl;Immed;
Save rednCxt_refl;

Goal rednCxt nilCxt nilCxt;
intros;Refine rednCxt_red1;Refine red1CxtNIL;
Save rednCxtNIL;


Goal rednCxtCONS_T:
     {b,b'|GB}{sc:and (Q (namOf b) (namOf b'))
                      (par_redn (typOf b) (typOf b'))}
     {G|Cxt}(VclCxt G)->rednCxt (CONS b G) (CONS b' G);
intros;
Refine no_rednRec [A,A'|Trm]
                  {b,b'|GB}{eqP:Q (namOf b) (namOf b')}
                  {eqA:is_tt (Trm_eq A (typOf b))}
                  {eqA':is_tt (Trm_eq A' (typOf b'))}
                   rednCxt (CONS b G) (CONS b' G);
intros;Refine rednCxt_red1;
Refine red1CxtCONS (pair eqP ?) (red1Cxt_refl H);
Qrepl Q_sym (Trm_eq_subst eqA);
Qrepl Q_sym (Trm_eq_subst eqA');
Immed;
intros;Refine rednCxt_trans;
Refine +1 lt_ih;Refine +4 rt_ih;Refine Gb (namOf b1) D;Immed;
Refine Q_refl;Refine Trm_eq_refl;Refine Trm_eq_refl;
Refine +2 par_no_redn (snd sc);Refine fst sc;
Refine Trm_eq_refl;Refine Trm_eq_refl;
Save;

Goal rednCxtCONS_C:
     {G,G'|Cxt}{premG:rednCxt G G'}
     {b|GB}{Vclb:Vclosed (typOf b)}
     rednCxt (CONS b G) (CONS b G');
Refine rednCxtRec [G,G'|Cxt][_:rednCxt G G']
     {b|GB}{Vclb:Vclosed (typOf b)}
     rednCxt (CONS b G) (CONS b G');
intros;Refine rednCxt_red1;Refine red1CxtCONS;
Refine pair (Q_refl ?) (no_red1_refl ?);Immed;
intros; Refine rednCxt_trans; Refine +1 lt_ih; Refine +1 rt_ih;
Immed;
Save;

Goal rednCxtCONS:
     {b,b'|GB}{sc:and (Q (namOf b) (namOf b'))
                      (par_redn (typOf b) (typOf b'))}
     {G,G'|Cxt}{premG:rednCxt G G'}
      rednCxt (CONS b G) (CONS b' G');
intros; Refine rednCxt_VclCxt premG; intros;
Refine rednCxt_trans;
Refine +1 rednCxtCONS_C; Refine +2 fst (par_redn_Vclosed (snd sc));
Refine +2 rednCxtCONS_T;Immed;
Save;

Goal {K|Cxt}(rednCxt nilCxt K)->is_tt (Cxt_eq K nilCxt);
intros;
Refine rednCxtRec [G,G':Cxt][_:rednCxt G G']
                  {eq:is_tt (Cxt_eq G nilCxt)}is_tt (Cxt_eq G' nilCxt);
Immed;
intros;Refine red1Cxt_nil_character;Qrepl Q_sym (Cxt_eq_subst eq);Immed;
intros;Refine rt_ih;Refine lt_ih;Immed;
Refine Cxt_eq_refl;
Save rednCxt_nil_character;

Goal {p|PP}{A|Trm}{G,K|Cxt}(rednCxt (CONS (Gb p A) G) K)->
      Ex2 [G':Cxt][A':Trm]and3 (is_tt (Cxt_eq K (CONS (Gb p A') G')))
                               (rednCxt G G')
                               (par_redn A A');
intros;
Refine rednCxtRec [H,K:Cxt][_:rednCxt H K]{p|PP}{A|Trm}{G|Cxt}
                  {eq:is_tt (Cxt_eq H (CONS (Gb p A) G))}
                  Ex2 [G':Cxt][A':Trm]
                  and3 (is_tt (Cxt_eq K (CONS (Gb p A') G')))
                              (rednCxt G G')
                              (par_redn A A');Immed;
intros;Refine red1Cxt_cons_character (?:red1Cxt (CONS (Gb p1 A1) G2) G');
Qrepl Q_sym (Cxt_eq_subst eq);Immed;
intros G'' A'' hyp;Refine Ex2In G'' A'';
Refine pair3 (and3_out1 hyp) (rednCxt_red1 (and3_out2 hyp))
             (par_redn_red1 (no_par_red1 (and3_out3 hyp)));
intros;Refine lt_ih eq;
intros K' A' hyp;Refine rt_ih (and3_out1 hyp);
intros K'' A'' hyp';Refine Ex2In K'' A'';
Refine pair3 (and3_out1 hyp')
             (rednCxt_trans (and3_out2 hyp) (and3_out2 hyp'))
             (par_redn_trans (and3_out3 hyp) (and3_out3 hyp'));

Refine Cxt_eq_refl;
Save rednCxt_cons_character;

Goal {G,K|Cxt}(rednCxt G K)->Q (globalNames G) (globalNames K);
Refine rednCxtRec [G,K|Cxt][_:rednCxt G K]Q (globalNames G) (globalNames K);
intros;Refine red1Cxt_globalNames;Immed;
intros;Refine Q_trans;Immed;
Save rednCxt_globalNames;

Goal {G,K|Cxt}(rednCxt G K)->{p:PP}Q (Poccur p G) (Poccur p K);
intros;Expand Poccur;Qrepl rednCxt_globalNames H;Refine Q_refl;
Save rednCxt_Poccur_lem;

Goal {G,K|Cxt}(rednCxt G K)->{p|PP}(is_tt (POCCUR p K))->is_tt (POCCUR p G);
Refine rednCxtRec [G,K|Cxt][_:rednCxt G K]
                  {p|PP}{occ:is_tt (POCCUR p K)}is_tt (POCCUR p G);
intros;Refine red1Cxt_POCCUR_lem;Immed;
intros;Refine lt_ih;Refine rt_ih;Immed;
Save rednCxt_POCCUR_lem;

Goal {G,K|Cxt}(rednCxt G K)->{p|PP}(is_ff (POCCUR p G))->is_ff (POCCUR p K);
intros;Refine B_contrapos;Refine +1 rednCxt_POCCUR_lem;Immed;
Save rednCxt_not_POCCUR_lem;

Goal {G,GG|Cxt}(rednCxt G GG)->(wValid G)->wValid GG;
Refine rednCxtRec [G,K|Cxt][_:rednCxt G K](wValid G)->wValid K;
intros;Refine red1Cxt_preserves_wValid;Immed;
intros;Refine rt_ih;Refine lt_ih;Immed;
Save rednCxt_preserves_wValid;

Goal {G,GG|Cxt}(rednCxt G GG)->
     {p|PP}{A|Trm}(is_tt (GBoccur (Gb p A) G))->
     Ex [AA:Trm] and (is_tt (GBoccur (Gb p AA) GG)) (par_redn A AA);
Refine rednCxtRec [G,GG:Cxt][_:rednCxt G GG]
       {p|PP}{A|Trm}{occ:is_tt (GBoccur (Gb p A) G)}
       Ex [AA:Trm] and (is_tt (GBoccur (Gb p AA) GG)) (par_redn A AA);
intros;Refine red1Cxt_GBoccur_lem;Immed;
intros AA specAA;Refine ExIn AA;
Refine pair (fst specAA) (par_redn_red1 (no_par_red1 (snd specAA)));
intros;Refine lt_ih;Immed;
intros AA specAA;Refine rt_ih (fst specAA);
intros AA' specAA';Refine ExIn AA';
Refine pair (fst specAA') (par_redn_trans (snd specAA) (snd specAA'));
Save rednCxt_GBoccur_lem;

(* a more natural def'n of context reduction *)
Inductive [par_rednCxt: Cxt->Cxt->Prop] NoReductions Inversion
Constructors
[par_rednCxtNIL: par_rednCxt nilCxt nilCxt]
[par_rednCxtCONS:
 {b,c|GB}{sc:and (Q (namOf b) (namOf c)) (par_redn (typOf b) (typOf c))}
 {G,K|Cxt}{premG:par_rednCxt G K}
      par_rednCxt (CONS b G) (CONS c K)];

Goal par_rednCxt_cons_inv:
     {G,K|Cxt}{b|GB}(par_rednCxt (CONS b G) K)->
      Ex2 [J:Cxt][c:GB] and4 (Q K (CONS c J))
                             (Q (namOf b) (namOf c))
                             (par_redn (typOf b) (typOf c))
                             (par_rednCxt G J);
intros; Invert H Then Qnify;
Refine NIL_not_CONS par_rednCxtNIL_eq1;
intros; Refine Ex2In a2 a5;
  Refine new_eqCxtLem par_rednCxtCONS_eq5; intros;
  Qrepl Q_sym H1; Qrepl Q_sym H2; Qrepl Q_sym H3;
  Refine a4; intros; Refine pair4 (Q_refl ?); Immed;
Save;

Goal par_rednCxt_trans:
     {G,J|Cxt}(par_rednCxt G J)->{K|Cxt}(par_rednCxt J K)->par_rednCxt G K;
Refine par_rednCxt_elim [G,J|Cxt][_:par_rednCxt G J]
                                 {K|Cxt}(par_rednCxt J K)->par_rednCxt G K;
intros; Immed;
intros ________; Qrepl GB_surj_pair c; Qrepl GB_surj_pair b;
  Refine sc; intros; Refine par_rednCxt_cons_inv H2;
  intros; Refine H3; intros; Qrepl H4; Qrepl GB_surj_pair s;
  Refine par_rednCxtCONS; Qrepl Q_sym H5; Refine pair;
  Assumption; Refine par_redn_trans H1; Assumption;
  Refine premG_ih; Assumption;
Save;

(* the two context reductions are extensionally equivalent *)
Goal rednCxt_par_rednCxt:
     {G,K|Cxt}(rednCxt G K)->par_rednCxt G K;
Refine rednCxtRec [G,K|Cxt][_:rednCxt G K]par_rednCxt G K;
Refine red1CxtRec [G,K|Cxt][_:red1Cxt G K]par_rednCxt G K;
Refine par_rednCxtNIL;
intros; Refine sc; intros;
  Refine par_rednCxtCONS; Refine pair; Immed;
  Refine par_redn_red1 (no_par_red1 H1);
intros; Refine par_rednCxt_trans; Immed;
Save;

Goal par_rednCxt_rednCxt:
     {G,K|Cxt}(par_rednCxt G K)->rednCxt G K;
Refine par_rednCxt_elim [G,K|Cxt][_:par_rednCxt G K]rednCxt G K;
Refine rednCxtNIL;
intros; Refine rednCxtCONS; Immed;
Save;

Goal {G|Cxt}{M,A|Trm}(gts G M A)->{G'|Cxt}(rednCxt G G')->gts G' M A;
intros;
Refine rednCxtRec [G,G'|Cxt][_:rednCxt G G']{j:gts G M A}gts G' M A;
intros;
 Refine subject_reduction_lem j
        (red1SubjCT premG (no_red1_refl (fst (gts_Vclosed_lem j))));
intros;Refine rt_ih;Refine lt_ih;Immed;
Immed;
Save gtsCR;

Goal gtsAllRed: {G|Cxt}{M,A|Trm}(gts G M A)->
                {G'|Cxt}(rednCxt G G')->
                {M'|Trm}(par_redn M M')->
                {A'|Trm}(par_redn A A')->gts G' M' A';
intros; Refine gtsCR; Immed; Refine gtsSR; Immed; Refine gtsPR; Immed;
Save;


Goal {G,GG|Cxt}(alphaCxt G GG)->rednCxt G GG;
Refine alphaCxt_elim [G,GG:Cxt][_:alphaCxt G GG]rednCxt G GG;
Refine rednCxtNIL;
intros; Refine rednCxtCONS; Immed;
Refine sc; intros;
Refine pair; Refine +1 par_redn_red1; 
Refine +1 alpha_conv_par_red1; Immed;
Save alphaCxt_rednCxt;

Goal gts_alpha_closed: {G|Cxt}{M,A|Trm}(gts G M A)->
                       {GG|Cxt}(alphaCxt G GG)->
                       {MM|Trm}(alpha_conv M MM)->
                       {AA|Trm}(alpha_conv A AA)->gts GG MM AA;
intros; Refine gtsAllRed; Immed;
Refine alphaCxt_rednCxt;
Refine +1 par_redn_red1; Refine +1 alpha_conv_par_red1;
Refine +2 par_redn_red1; Refine +2 alpha_conv_par_red1;
Immed;
Save;
