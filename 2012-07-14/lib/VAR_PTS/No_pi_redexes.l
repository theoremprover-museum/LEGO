Module No_pi_redexes Import par_bp_red subject_reduction abstract_cnv;

(* observe that well formed judgments contain no pi redexes *)

$[No_pi_redexes:Trm->Prop];
$[No_pi_redexes_sort:{s:SS}No_pi_redexes (sort s)];
$[No_pi_redexes_par:{p:PP}No_pi_redexes (par p)];
$[No_pi_redexes_pi:{n|VV}{A,B|Trm}
                  {premA:No_pi_redexes A}
                  {p|PP}{noccB:is_ff (poccur p B)}
                        {premB:No_pi_redexes (alpha p n B)}
                   No_pi_redexes (pi n A B)];
$[No_pi_redexes_lda:{n|VV}{A,B|Trm}
                   {premA:No_pi_redexes A}
                   {p|PP}{noccB:is_ff (poccur p B)}
                         {premB:No_pi_redexes (alpha p n B)}
                    No_pi_redexes (lda n A B)];
$[No_pi_redexes_app:{A,B|Trm}{sc:is_ff (isPi A)}
                   {premA:No_pi_redexes A}{premB:No_pi_redexes B}
                    No_pi_redexes (app A B)];
$[No_pi_redexesRec:{C:{A|Trm}(No_pi_redexes A)->Prop}
                  {NPRSORT:{s:SS}C (No_pi_redexes_sort s)}
                  {NPRPAR:{p:PP}C (No_pi_redexes_par p)}
                  {NPRPI:{n|VV}{A,B|Trm}
                         {premA:No_pi_redexes A}{ihA:C premA}
                         {p|PP}{noccB:is_ff (poccur p B)}
                               {premB:No_pi_redexes (alpha p n B)}
                               {ihB:C premB}
                          C (No_pi_redexes_pi premA noccB premB)}
                  {NPRLDA:{n|VV}{A,B|Trm}
                          {premA:No_pi_redexes A}{ihA:C premA}
                          {p|PP}{noccB:is_ff (poccur p B)}
                                {premB:No_pi_redexes (alpha p n B)}
                                {ihB:C premB}
                           C (No_pi_redexes_lda premA noccB premB)}
                  {NPRAPP:{A,B|Trm}
                          {sc:is_ff (isPi A)}
                          {premA:No_pi_redexes A}{ihA:C premA}
                          {premB:No_pi_redexes B}{ihB:C premB}
                           C (No_pi_redexes_app sc premA premB)}
                  {A|Trm}{npr:No_pi_redexes A}C npr];

$[aNo_pi_redexes:Trm->Prop];
$[aNo_pi_redexes_sort:{s:SS}aNo_pi_redexes (sort s)];
$[aNo_pi_redexes_par:{p:PP}aNo_pi_redexes (par p)];
$[aNo_pi_redexes_pi:{n|VV}{A,B|Trm}
             {premA:aNo_pi_redexes A}
             {premB:{p|PP}aNo_pi_redexes (alpha p n B)}
              aNo_pi_redexes (pi n A B)];
$[aNo_pi_redexes_lda:{n|VV}{A,B|Trm}
              {premA:aNo_pi_redexes A}
              {premB:{p|PP}aNo_pi_redexes (alpha p n B)}
               aNo_pi_redexes (lda n A B)];
$[aNo_pi_redexes_app:{A,B|Trm}{sc:is_ff (isPi A)}
                    {premA:aNo_pi_redexes A}{premB:aNo_pi_redexes B}
                     aNo_pi_redexes (app A B)];

$[aNo_pi_redexesRec:{C:{A|Trm}(aNo_pi_redexes A)->Prop}
                   {NPRSORT:{s:SS}C (aNo_pi_redexes_sort s)}
                   {NPRPAR:{p:PP}C (aNo_pi_redexes_par p)}
                   {NPRPI:{n|VV}{A,B|Trm}
                          {premA:aNo_pi_redexes A}{ihA:C premA}
                          {premB:{p|PP}aNo_pi_redexes (alpha p n B)}
                          {ihB:{p|PP}C (premB|p)}
                           C (aNo_pi_redexes_pi premA premB)}
                   {NPRLDA:{n|VV}{A,B|Trm}
                           {premA:aNo_pi_redexes A}{ihA:C premA}
                           {premB:{p|PP}aNo_pi_redexes (alpha p n B)}
                           {ihB:{p|PP}C (premB|p)}
                            C (aNo_pi_redexes_lda premA premB)}
                   {NPRAPP:{A,B|Trm}
                           {sc:is_ff (isPi A)}
                           {premA:aNo_pi_redexes A}{ihA:C premA}
                           {premB:aNo_pi_redexes B}{ihB:C premB}
                            C (aNo_pi_redexes_app sc premA premB)}
                   {A|Trm}{npr:aNo_pi_redexes A}C npr];

Goal {A|Trm}(aNo_pi_redexes A)->No_pi_redexes A;
Refine aNo_pi_redexesRec [A:Trm][_:aNo_pi_redexes A]No_pi_redexes A;
intros;Refine No_pi_redexes_sort;
intros;Refine No_pi_redexes_par;
intros;Refine PPinf (params B);
intros p noccB;Refine No_pi_redexes_pi;Immed;
intros;Refine PPinf (params B);
intros p noccB;Refine No_pi_redexes_lda;Immed;
intros;Refine No_pi_redexes_app;Immed;
Save aNo_pi_redexes_No_pi_redexes;

Goal {A|Trm}(No_pi_redexes A)->{rho:Renaming}aNo_pi_redexes (renTrm rho A);
Refine No_pi_redexesRec [A:Trm][_:No_pi_redexes A]
                        {rho:Renaming}aNo_pi_redexes (renTrm rho A);
intros;Refine aNo_pi_redexes_sort;
intros;Refine aNo_pi_redexes_par;
intros;Equiv aNo_pi_redexes (pi n (renTrm rho A) (renTrm rho B));
       Refine aNo_pi_redexes_pi;Immed;
       intros q;
       Claim Ex [sigma:Renaming]and (Q (renPar sigma p) q)
                                    (Q (renTrm sigma B) (renTrm rho B));
       Refine ?+1;
       intros sigma sigmaSpec;Refine sigmaSpec;
       intros sigmaSpec1 sigmaSpec2;
       Qrepl Q_sym sigmaSpec1;
       Qrepl Q_sym sigmaSpec2;
       Qrepl alpha_renTrm_commutes sigma p n B;Immed;
       [sigma = CONS (Pr p q) rho:Renaming];
       Refine ExIn sigma;Refine pair;
       Equiv Q (if (PPeq p p) q (renPar ? ?)) q;Qrepl PPrefl p;Refine Q_refl;
       Qrepl triv_renTrm_lem rho q noccB;Refine Q_refl;

intros;Equiv aNo_pi_redexes (lda n (renTrm rho A) (renTrm rho B));
       Refine aNo_pi_redexes_lda;Immed;
       intros q;
       Claim Ex [sigma:Renaming]and (Q (renPar sigma p) q)
                                    (Q (renTrm sigma B) (renTrm rho B));
       Refine ?+1;
       intros sigma sigmaSpec;Refine sigmaSpec;
       intros sigmaSpec1 sigmaSpec2;
       Qrepl Q_sym sigmaSpec1;
       Qrepl Q_sym sigmaSpec2;
       Qrepl alpha_renTrm_commutes sigma p n B;Immed;
       [sigma = CONS (Pr p q) rho:Renaming];
       Refine ExIn sigma;Refine pair;
       Equiv Q (if (PPeq p p) q (renPar ? ?)) q;Qrepl PPrefl p;Refine Q_refl;
       Qrepl triv_renTrm_lem rho q noccB;Refine Q_refl;
       
intros;Equiv aNo_pi_redexes (app (renTrm rho A) (renTrm rho B));
       Refine aNo_pi_redexes_app;Qrepl renTrm_isPi rho A;Immed;

Save No_pi_redexes_aNo_pi_redexes_lem;

Goal {A|Trm}(No_pi_redexes A)->aNo_pi_redexes A;
intros;Qrepl renTrm_Id A;Refine No_pi_redexes_aNo_pi_redexes_lem H renId;
Save No_pi_redexes_aNo_pi_redexes;

Goal {A|Trm}(No_pi_redexes A)->{rho:Renaming}No_pi_redexes (renTrm rho A);
intros;Refine aNo_pi_redexes_No_pi_redexes;Refine No_pi_redexes_aNo_pi_redexes_lem;Immed;
Save renTrm_resp_No_pi_redexes;

Goal {A|Trm}(No_pi_redexes A)->Vclosed A;
Refine No_pi_redexesRec [A|Trm][_:No_pi_redexes A]Vclosed A;
intros;Refine Vclosed_sort;
intros;Refine Vclosed_par;
intros;Refine Vclosed_pi;Immed;
intros;Refine Vclosed_lda;Immed;
intros;Refine Vclosed_app;Immed;
Save No_pi_redexes_Vclosed;

Goal {u|VV}{A,B|Trm}(No_pi_redexes (pi u A B))->
                    and (No_pi_redexes A) ({p|PP}No_pi_redexes (alpha p u B));
intros;
Refine aNo_pi_redexesRec [X|Trm][_:aNo_pi_redexes X]
                         {eq:is_tt (Trm_eq X (pi u A B))}
                          and (No_pi_redexes A)
                              ({p|PP}No_pi_redexes (alpha p u B));
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine Trm_eq_pi_lem eq;
intros eqV eqA eqB;
Qrepl Q_sym (VVdecide eqV);
Qrepl Q_sym (Trm_eq_subst eqA);
Qrepl Q_sym (Trm_eq_subst eqB);
Refine pair;Refine aNo_pi_redexes_No_pi_redexes;Immed;
     intros;Refine aNo_pi_redexes_No_pi_redexes;Immed;
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
Refine +2 Trm_eq_refl;Refine No_pi_redexes_aNo_pi_redexes;Immed;
Save No_pi_redexes_pi_lem;

Goal {u|VV}{A,B|Trm}(No_pi_redexes (lda u A B))->
                    and (No_pi_redexes A) ({p|PP}No_pi_redexes (alpha p u B));
intros;
Refine aNo_pi_redexesRec [X|Trm][_:aNo_pi_redexes X]
                         {eq:is_tt (Trm_eq X (lda u A B))}
                          and (No_pi_redexes A)
                              ({p|PP}No_pi_redexes (alpha p u B));
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine Trm_eq_lda_lem eq;
intros eqV eqA eqB;
Qrepl Q_sym (VVdecide eqV);
Qrepl Q_sym (Trm_eq_subst eqA);
Qrepl Q_sym (Trm_eq_subst eqB);
Refine pair;Refine aNo_pi_redexes_No_pi_redexes;Immed;
     intros;Refine aNo_pi_redexes_No_pi_redexes;Immed;
intros;Refine tt_not_ff (Q_sym eq);
Refine +2 Trm_eq_refl;Refine No_pi_redexes_aNo_pi_redexes;Immed;
Save No_pi_redexes_lda_lem;

Goal {A,B|Trm}(No_pi_redexes (app A B))->
      and3 (is_ff (isPi A))
           (No_pi_redexes A)
           (No_pi_redexes B);
intros;
Refine aNo_pi_redexesRec [X|Trm][_:aNo_pi_redexes X]
                         {eq:is_tt (Trm_eq X (app A B))}
                          and3 (is_ff (isPi A))
                               (No_pi_redexes A)
                               (No_pi_redexes B);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine Trm_eq_app_lem eq;
intros eqA eqB;
Qrepl Q_sym (Trm_eq_subst eqA);Qrepl Q_sym (Trm_eq_subst eqB);
Refine pair3;Refine sc;
             Refine aNo_pi_redexes_No_pi_redexes;Immed;
             Refine aNo_pi_redexes_No_pi_redexes;Immed;
Refine +2 Trm_eq_refl;Refine No_pi_redexes_aNo_pi_redexes;Immed;
Save No_pi_redexes_app_lem;

Goal {u|VV}{A,A',B'|Trm}(No_pi_redexes (app (pi u A' B') A))->absurd;
intros;
Refine No_pi_redexesRec [X|Trm][_:No_pi_redexes X]
                        {eq:is_tt (Trm_eq X (app (pi u A' B') A))}absurd;
Immed;
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff;
Qrepl Q_sym sc;Qrepl Trm_eq_subst (fst (Trm_eq_app_lem eq));Refine Q_refl;
Refine Trm_eq_refl;
Save No_pi_redexes_npr_lem;

Goal {A,B|Trm}(par_bp_red1 A B)->{npr:No_pi_redexes A}par_red1 A B;
Refine par_bp_red1Rec [A,B|Trm][_:par_bp_red1 A B]
                                 {npr:No_pi_redexes A}par_red1 A B;
intros; Refine par_red1_refl (No_pi_redexes_Vclosed npr);
intros;Refine No_pi_redexes_npr_lem npr;
intros;Refine No_pi_redexes_app_lem npr;
intros sc nprL nprA;Refine No_pi_redexes_lda_lem nprL;
intros nprU nprB;Refine par_red1_beta ? (ihA nprA) noccB noccB' (ihB (nprB|?));
   Refine No_pi_redexes_Vclosed nprU;
intros;Refine No_pi_redexes_pi_lem npr;
intros nprA nprB;Refine par_red1_pi (ihA nprA) noccB noccB' (ihB (nprB|?));
intros;Refine No_pi_redexes_lda_lem npr;
intros nprA nprB;Refine par_red1_lda (ihA nprA) noccB noccB' (ihB (nprB|?));
intros;Refine No_pi_redexes_app_lem npr;
intros sc nprA nprB;Refine par_red1_app (ihA nprA) (ihB nprB);
Save par_bp_red1_red1;

Goal {G|Cxt}{M,A|Trm}(gts G M A)->No_pi_redexes M;
Refine gtsRec [G:Cxt][M,A:Trm][_:gts G M A] No_pi_redexes M;
(* ax *) intros;Refine No_pi_redexes_sort;
(* start *) intros;Refine No_pi_redexes_par;
(* vWeak *) intros;Refine No_pi_redexes_par;
(* sWeak *) intros;Refine l_ih;
(* pi *) intros;Refine No_pi_redexes_pi l_ih noccB r_ih;
(* lda *) intros;
Refine No_pi_redexes_lda (fst (No_pi_redexes_pi_lem r_ih)) noccM l_ih;
(* app *) intros;Refine No_pi_redexes_app ? l_ih r_ih;
Refine tt_or_ff (isPi M);
intros case;Refine isPi_lem case;intros u A' B' hyp;
            Refine gts_gen_pi (?:gts G (pi u A' B') (pi n A B));
            Qrepl Q_sym (Trm_eq_subst hyp);Refine l_prem;
            intros s1 s2 s3 p hypC;
            Refine cnv_sort_character_r (and5_out5 hypC); intros _ h;
            Refine par_redn_pi_character h;
            intros w A' B' hypP;Refine tt_not_ff (Q_sym (and3_out3 hypP));
intros case;Immed;
(* conv *) intros;Immed;
Save gts_No_pi_redexes_lem_subj;

Goal {G|Cxt}{M,A|Trm}(gts G M A)-> No_pi_redexes A;
intros;Refine type_correctness H;
intros s sHyp;Refine sHyp;
intros is_sort;Qrepl Trm_eq_subst is_sort;Refine No_pi_redexes_sort;
intros is_type;Refine gts_No_pi_redexes_lem_subj is_type;
Save gts_No_pi_redexes_lem_pred;

Goal {G|Cxt}{M,N,A|Trm}(gts G M A)->(par_bp_redn M N)->par_redn M N;
intros;
Refine par_bp_rednRec [M,N|Trm][_:par_bp_redn M N]
                      {G|Cxt}{A|Trm}{j:gts G M A}par_redn M N;Immed;
intros;Refine par_redn_red1;Refine par_bp_red1_red1;
Refine +1 gts_No_pi_redexes_lem_subj;Immed;
intros;Refine par_redn_trans (lt_ih j) (rt_ih (gtsSR j (lt_ih j)));
Save well_typed_No_pi_redexes_subj;

Goal {G|Cxt}{M,A,B|Trm}(gts G M A)->(par_bp_redn A B)->par_redn A B;
intros;
Refine par_bp_rednRec [A,B|Trm][_:par_bp_redn A B]
                      {G|Cxt}{M|Trm}{j:gts G M A}par_redn A B;Immed;
intros;Refine par_redn_red1;Refine par_bp_red1_red1;
Refine +1 gts_No_pi_redexes_lem_pred;Immed;
intros;Refine par_redn_trans (lt_ih j) (rt_ih (gtsPR j (lt_ih j)));
Save well_typed_No_pi_redexes_pred;
