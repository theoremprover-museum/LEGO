Module lvc Import vc;

(* smaller derivations by delaying the check for context validity *)

(* locally valid contexts presentation *)
Inductive [lvtyp:Cxt->Trm->Trm->Prop]  Constructors
[lvtSort:{s1,s2|SS}                                              {sc:ax s1 s2}
       {G:Cxt}lvtyp G (sort s1) (sort s2)]

[lvtPar:{G|Cxt}{p|PP}{A|Trm}                   {sc:is_tt (GBoccur (Gb p A) G)}
       lvtyp G (par p) A]

[lvtPi:{G|Cxt}{A,B|Trm}{s1,s2,s3|SS}{p|PP}{n|VV}              {sc:rl s1 s2 s3}
                                                    {noccB:is_ff (poccur p B)}
                                                    {noccG:is_ff (Poccur p G)}
       {l_prem:lvtyp G A (sort s1)}
       {r_prem:lvtyp (CONS (Gb p A) G) (vsub (par p) n B) (sort s2)}
     (*****************************************)
       lvtyp G (pi n A B) (sort s3)]

[lvtLda:{G|Cxt}{A,M,B|Trm}{s|SS}{p|PP}{n,m|VV}      {noccM:is_ff (poccur p M)}
                                                    {noccB:is_ff (poccur p B)}
                                                    {noccG:is_ff (Poccur p G)}
       {l_prem:lvtyp (CONS (Gb p A) G) (vsub (par p) n M) (vsub (par p) m B)}
       {r_prem:lvtyp G (pi m A B) (sort s)}
     (*****************************************)
       lvtyp G (lda n A M) (pi m A B)]

[lvtApp:{G|Cxt}{M,A,B,L|Trm}{n|VV}
       {l_prem:lvtyp G M (pi n A B)}
       {r_prem:lvtyp G L A}
     (*****************************************)
       lvtyp G (app M L) (vsub L n B)]

[lvtCnv:{G|Cxt}{M,A,B|Trm}{s|SS}                                  {sc:cnv A B}
       {l_prem:lvtyp G M A}
       {r_prem:lvtyp G B (sort s)}
     (*****************************************)
       lvtyp G M B];


Inductive [lvcxt:Cxt->Prop]  Constructors
[lvcNil:lvcxt nilCxt]

[lvcCons:{G|Cxt}{p|PP}{A|Trm}{s|SS}                 {noccG:is_ff (Poccur p G)}
                                                       {sc:lvtyp G A (sort s)}
       {prem:lvcxt G}
     (*****************************************)
       lvcxt (CONS (Gb p A) G)];

(* a generation lemma for later use *)
Goal lv_gen_pi:
     {G|Cxt}{A,B,C|Trm}{v|VV}(lvtyp G (pi v A B) C)->
     Ex4 [s1,s2,s3:SS][p:PP]
        and6 (rl s1 s2 s3)
             (is_ff (poccur p B))
             (is_ff (Poccur p G))
             (lvtyp G A (sort s1))
             (lvtyp (CONS (Gb p A) G) (vsub (par p) v B) (sort s2))
             (cnv (sort s3) C);
intros;
Refine lvtyp_elim [G:Cxt][M,C:Trm][_:lvtyp G M C]
     {eqPi:is_tt (Trm_eq M (pi v A B))}
     Ex4 [s1,s2,s3:SS][p:PP]
        and6 (rl s1 s2 s3)
             (is_ff (poccur p B))
             (is_ff (Poccur p G))
             (lvtyp G A (sort s1))
             (lvtyp (CONS (Gb p A) G) (vsub (par p) v B) (sort s2))
             (cnv (sort s3) C);
(* sort *)
intros; Refine tt_not_ff (Q_sym eqPi);
(* par *)
intros; Refine tt_not_ff (Q_sym eqPi);
(* pi *)
intros; Refine Trm_eq_pi_lem eqPi; intros eqV eqA eqB;
Refine Ex4In s1 s2 s3 p;
Qrepl Q_sym (VVdecide eqV);
Qrepl Q_sym (Trm_eq_subst eqA);
Qrepl Q_sym (Trm_eq_subst eqB);
Refine pair6; Immed; Refine cnv_refl; Refine Vclosed_sort;
(* lda *)
intros; Refine tt_not_ff (Q_sym eqPi);
(* app *)
intros; Refine tt_not_ff (Q_sym eqPi);
(* cnv *)
intros; Refine l_prem_ih eqPi; intros s1 s2 s3 p hyp;
Refine hyp; intros;
Refine Ex4In s1 s2 s3 p; Refine pair6; Immed;
Refine cnv_trans; Immed;
Immed; Refine Trm_eq_refl;
Save;


(* the idea is that lvtyp preserves vcxt *)
%\VerbFileOpen lvtyp_vcxt_vtyp
Goal lvtyp_vcxt_vtyp: {G|Cxt}{M,A|Trm}(lvtyp G M A)->(vcxt G)->vtyp G M A;
%\VerbFileClos lvtyp_vcxt_vtyp
Refine lvtyp_elim [G|Cxt][M,A|Trm][_:lvtyp G M A](vcxt G)->vtyp G M A;
(* sort *)
intros; Refine vtSort; Immed;
(* par *)
intros; Refine vtPar; Immed;
(* pi *)
intros; Refine vtPi; Immed;
Refine l_prem_ih; Immed;
Refine r_prem_ih; Refine vcCons noccG (l_prem_ih H);
(* lda *)
intros; Refine vtLda; Immed;
Refine l_prem_ih; Refine vtyp_gen_pi (r_prem_ih H); 
intros t1 t2 t3 q h;Refine vcCons noccG (and5_out2 h);
Refine r_prem_ih; Immed;
(* app *)
intros; Refine vtApp;
Refine +1 l_prem_ih  H; Refine r_prem_ih H;
(* cnv *)
intros; Refine vttCnv; Immed;
Refine l_prem_ih  H; Refine r_prem_ih H;
Save;


(* the general Well-Founded induction on pairs of judgements
 * (lvtyp G M A), (lvcxt G)
 *)
Goal wc_wt_WF_ind:
     {f:{G|Cxt}{M,A|Trm}(lvtyp G M A)->(lvcxt G)->NN}
     {C:{G|Cxt}{M,A|Trm}(lvtyp G M A)->(lvcxt G)->Prop}
     {wf_ih:{G|Cxt}{M,A|Trm}{t:lvtyp G M A}{c:lvcxt G}
            {ih:{g|Cxt}{m,a|Trm}{xt:lvtyp g m a}{xc:lvcxt g}
                (Lt (f xt xc) (f t c))->C xt xc}C t c}
     {G|Cxt}{M,A|Trm}{t:lvtyp G M A}{c:lvcxt G}C t c;
intros;
Refine complete_induction [n:NN]
       {G|Cxt}{M,A|Trm}{t:lvtyp G M A}{c:lvcxt G}(Q n (f t c))->C t c;
intros; Refine wf_ih;
intros; Refine H; Refine f xt xc; Qrepl H1; Refine H2; Refine Q_refl;
Refine +1 Q_refl;
Save;


(* we want to do induction on the sum of the lengths of
 * (lvcxt G) and (lvtyp G M A)
 *)
[lvtyp_ln : {G|Cxt}{M,A|Trm}(lvtyp G M A)->NN =
  lvtyp_elim ([G|Cxt][M,A|Trm][_:lvtyp G M A]NN)
             ([s1,s2|SS][sc:ax s1 s2][G:Cxt]Z)
             ([G|Cxt][p|PP][A|Trm][sc:is_tt (GBoccur (Gb p A) G)]Z)
             ([G|Cxt][A,B|Trm][s1,s2,s3|SS][p|PP][n|VV][sc:rl s1 s2 s3]
              [noccB:is_ff (poccur p B)][noccG:is_ff (Poccur p G)]
              [l_prem:lvtyp G A (sort s1)]
              [r_prem:lvtyp (CONS (Gb p A) G) (vsub (par p) n B) (sort s2)]
              [l,r:NN]S (add l r))
             ([G|Cxt][A,M,B|Trm][s|SS][p|PP][n,m|VV]
              [noccM:is_ff (poccur p M)][noccB:is_ff (poccur p B)]
              [noccG:is_ff (Poccur p G)]
              [l_prem:lvtyp (CONS (Gb p A) G)
                            (vsub (par p) n M) (vsub (par p) m B)]
              [r_prem:lvtyp G (pi m A B) (sort s)]
              [l,r:NN]S (add l r))
             ([G|Cxt][M,A,B,L|Trm][n|VV]
              [l_prem:lvtyp G M (pi n A B)]
              [r_prem:lvtyp G L A]
              [l,r:NN]S (add l r))
             ([G|Cxt][M,A,B|Trm][s|SS][sc:cnv A B]
              [l_prem:lvtyp G M A]
              [r_prem:lvtyp G B (sort s)]
              [l,r:NN]S (add l r))];
[lvcxt_ln : {G|Cxt}(lvcxt G)->NN =
  lvcxt_elim ([G|Cxt][_:lvcxt G]NN)
             (Z)
             ([G|Cxt][p|PP][A|Trm][s|SS][noccG:is_ff (Poccur p G)]
              [sc:lvtyp G A (sort s)]
              [prem:lvcxt G]
              [ih:NN]S (add (lvtyp_ln sc) ih))];
(* the sum of the lengths *)
[wc_wt_ln [G|Cxt][M,A|Trm][t:lvtyp G M A][c:lvcxt G] : NN
                                            = add (lvcxt_ln c) (lvtyp_ln t)];


Goal lvtyp_lvcxt_vtyp: {G|Cxt}{M,A|Trm}{t:lvtyp G M A}{c:lvcxt G}vtyp G M A;
Refine wc_wt_WF_ind wc_wt_ln
                    ([G:Cxt][M,A:Trm][_:lvtyp G M A][_:lvcxt G]vtyp G M A);
                                    (***  dependent elimination  ***)
Refine lvtyp_elim [G|Cxt][M,A|Trm][t:lvtyp G M A]{c:lvcxt G}
           {wf_ih:{g|Cxt}{m,a|Trm}{xt:lvtyp g m a}{xc:lvcxt g}
                          (Lt (wc_wt_ln xt xc) (wc_wt_ln t c))->vtyp g m a}
       vtyp G M A;
(* sort *)
intros ____;
Refine lvcxt_elim ([G|Cxt][c:lvcxt G]         (*** dependent elimination ***)
   {wf_ih:{g|Cxt}{m,a|Trm}{xt:lvtyp g m a}{xc:lvcxt g}
         (Lt (wc_wt_ln xt xc) (wc_wt_ln (lvtSort sc ?) c))->vtyp g m a}
   vtyp G (sort s1) (sort s2));
intros; Refine vtSort sc vcNil;
intros; Refine vtSort sc;
Refine vcCons noccG; Refine s;
Refine wf_ih sc1 prem;
Equiv Lt ? (S (add (add ? (lvcxt_ln ?)) ?));
Equiv Lt (add (lvcxt_ln ?) (lvtyp_ln ?)) ?;
Qrepl addCommute (lvcxt_ln prem) (lvtyp_ln sc1);
Refine Lt_add_S_right;
(* par *)
(* A subtle variable dependency requires re-ordering the variables:
 * the "G" in the type of "sc" must be bound in the IH, while the
 * induction is on {G|Cxt}{c:lvcxt G}.
 *)
Claim {G|Cxt}{c:lvcxt G}{p|PP}{A|Trm}{sc:is_tt (GBoccur (Gb p A) G)}
   ({g|Cxt}{m,a|Trm}{xt:lvtyp g m a}{xc:lvcxt g}
               (Lt (wc_wt_ln xt xc) (wc_wt_ln (lvtPar sc) c))->
       vtyp g m a)->vtyp G (par p) A;
intros; Refine ?70; Immed; Next 70;
Refine lvcxt_elim ([G|Cxt][c:lvcxt G]         (*** dependent elimination ***)
      {p|PP}{A|Trm}{sc:is_tt (GBoccur (Gb p A) G)}
        ({g|Cxt}{m,a|Trm}{xt:lvtyp g m a}{xc:lvcxt g}
                   (Lt (wc_wt_ln xt xc) (wc_wt_ln (lvtPar sc) c))->
        vtyp g m a)->vtyp G (par p) A);
intros; Refine tt_not_ff (Q_sym sc);
intros; Refine vtPar sc1;
Refine vcCons noccG; Refine s;
Refine H sc prem;
Equiv Lt ? (S (add (add ? (lvcxt_ln ?)) ?));
Equiv Lt (add (lvcxt_ln ?) (lvtyp_ln ?)) ?;
Qrepl addCommute (lvcxt_ln prem) (lvtyp_ln sc);
Refine Lt_add_S_right;
(* pi *)
intros; Refine vtPi; Immed;
Refine +1 lvtyp_vcxt_vtyp r_prem (vcCons noccG ?+0);
Refine wf_ih; Immed;
Equiv Lt (add ? ?) (add ? (S (add (lvtyp_ln ?) (lvtyp_ln ?))));
Qrepl addS (add (lvtyp_ln l_prem) (lvtyp_ln r_prem)) (lvcxt_ln c);
Qrepl Q_sym (addAssocR (lvtyp_ln l_prem) (lvtyp_ln r_prem) (lvcxt_ln c));
Refine Lt_add_S_right;
(* lda *)
intros; Refine vtLda; Immed;
Refine lvtyp_vcxt_vtyp l_prem;
Refine vtyp_gen_pi ?+1; intros s1 s2 s3 q hyp;
Refine vcCons noccG (and5_out2 hyp);
Refine wf_ih; Immed;
Equiv Lt (add ? ?) (add ? (S (add (lvtyp_ln ?) (lvtyp_ln ?))));
Qrepl addCommute (lvtyp_ln r_prem) (lvtyp_ln l_prem);
Qrepl addS (add (lvtyp_ln r_prem) (lvtyp_ln l_prem)) (lvcxt_ln c);
Qrepl Q_sym (addAssocR (lvtyp_ln r_prem) (lvtyp_ln l_prem) (lvcxt_ln c));
Refine Lt_add_S_right;
(* app *)
intros; Refine vtApp; Refine A;
Refine wf_ih; Immed;
Equiv Lt (add ? ?) (add ? (S (add (lvtyp_ln ?) (lvtyp_ln ?))));
Qrepl addS (add (lvtyp_ln l_prem) (lvtyp_ln r_prem)) (lvcxt_ln c);
Qrepl Q_sym (addAssocR (lvtyp_ln l_prem) (lvtyp_ln r_prem) (lvcxt_ln c));
Refine Lt_add_S_right;
Refine wf_ih; Immed;
Equiv Lt (add ? ?) (add ? (S (add (lvtyp_ln ?) (lvtyp_ln ?))));
Qrepl addS (add (lvtyp_ln l_prem) (lvtyp_ln r_prem)) (lvcxt_ln c);
Qrepl addCommute (lvtyp_ln r_prem) (lvtyp_ln l_prem);
Qrepl Q_sym (addAssocR (lvtyp_ln r_prem) (lvtyp_ln l_prem) (lvcxt_ln c));
Refine Lt_add_S_right;
(* cnv *)
intros; Refine vttCnv; Immed;
Refine wf_ih; Immed;
Equiv Lt (add ? ?) (add ? (S (add (lvtyp_ln ?) (lvtyp_ln ?))));
Qrepl addS (add (lvtyp_ln l_prem) (lvtyp_ln r_prem)) (lvcxt_ln c);
Qrepl Q_sym (addAssocR (lvtyp_ln l_prem) (lvtyp_ln r_prem) (lvcxt_ln c));
Refine Lt_add_S_right;
Refine wf_ih; Immed;
Equiv Lt (add ? ?) (add ? (S (add (lvtyp_ln ?) (lvtyp_ln ?))));
Qrepl addS (add (lvtyp_ln l_prem) (lvtyp_ln r_prem)) (lvcxt_ln c);
Qrepl addCommute (lvtyp_ln r_prem) (lvtyp_ln l_prem);
Qrepl Q_sym (addAssocR (lvtyp_ln r_prem) (lvtyp_ln l_prem) (lvcxt_ln c));
Refine Lt_add_S_right;
Save;

Goal {G|Cxt}{M,A|Trm}(lvtyp G M A)->(lvcxt G)->gts G M A;
intros; Refine vtyp_gts; Refine lvtyp_lvcxt_vtyp; Immed;
Save lvtyp_lvcxt_gts;


(**  Cannot prove lvtyp generation lemmas as lvtyp is stated, because
 ** contexts are not restricted to Vclosed terms, so transitivity of
 ** conversion doesn't hold.  The intermediate system vtyp is well
 ** behaved, so we work through that.
 **)


(* lvtyp is complete for vtyp *)
Goal {G|Cxt}{M,A|Trm}(vtyp G M A)->(lvtyp G M A);
Refine vtyp_elim ([G|Cxt][_:vcxt G]TT)
                 ([G|Cxt][M,A|Trm][_:vtyp G M A]lvtyp G M A);
(* nil *)
Refine true;
(* cons *)
intros; Refine true;
(* sort *)
intros; Refine lvtSort sc;
(* par *)
intros; Refine lvtPar sc;
(* pi *)
intros; Refine lvtPi; Immed;
Refine CxtCorrect0 (vtyp_gts r_prem);
(* lda *)
intros; Refine lvtLda; Immed;
Refine CxtCorrect0 (vtyp_gts l_prem);
(* app *)
intros; Refine lvtApp; Immed;
(* cnv *)
intros; Refine lvtCnv; Immed;
Save vtyp_lvtyp;


Goal {G|Cxt}(vcxt G)->(lvcxt G);
Refine vcxt_elim ([G|Cxt][_:vcxt G]lvcxt G)
                 ([G|Cxt][M,A|Trm][_:vtyp G M A]lvcxt G);
(* nil *)
Refine lvcNil;
(* cons *)
intros; Refine lvcCons; Immed; Refine vtyp_lvtyp prem;
(* sort *)
intros; Immed;
(* par *)
intros; Immed;
(* pi *)
intros; Immed;
(* lda *)
intros; Immed;
(* app *)
intros; Immed;
(* cnv *)
intros; Immed;
Save vcxt_lvcxt;

%\VerbFileOpen iff_gts_lvcxt_lvtyp
Goal iff_gts_lvcxt_lvtyp:
     {G:Cxt}{M,A:Trm}iff (gts G M A) (and (lvcxt G) (lvtyp G M A));
%\VerbFileClos iff_gts_lvcxt_lvtyp
intros; Refine pair;
intros; Refine pair;
Refine vcxt_lvcxt; Refine +1 vtyp_lvtyp; 
  Refine vtyp_vcxt ?+1; Refine gts_vtyp H;
intros; Refine lvtyp_lvcxt_gts (snd H) (fst H);
Save;
