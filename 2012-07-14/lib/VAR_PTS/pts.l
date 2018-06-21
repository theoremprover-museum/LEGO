Module pts Import gts apts;

(* the typing judgement as an inductive relation, older Lda rule *)
Inductive [pts:Cxt->Trm->Trm->Prop] Constructors

[pAx:{s1,s2|SS}
         {sc:ax s1 s2}
           pts nilCxt (sort s1) (sort s2)]

[pStart:{G|Cxt}{A|Trm}{s|SS}{p|PP}
         {noccG:is_ff (Poccur p G)}
         {prem:pts G A (sort s)}
     (*****************************************)
           pts (CONS (Gb p A) G) (par p) A]

[pvWeak:{G|Cxt}{D,A|Trm}{s|SS}{n,p|PP}
         {noccG:is_ff (Poccur p G)}
         {l_prem:pts G (par n) D}
         {r_prem:pts G A (sort s)}
     (*****************************************)
           pts (CONS (Gb p A) G) (par n) D]

[psWeak:{G|Cxt}{D,A|Trm}{t,s|SS}{p|PP}
         {noccG:is_ff (Poccur p G)}
         {l_prem:pts G (sort t) D}
         {r_prem:pts G A (sort s)}
     (*****************************************)
           pts (CONS (Gb p A) G) (sort t) D]

[pPi:{G|Cxt}{A,B|Trm}{s1,s2,s3|SS}{p|PP}{n|VV}
         {sc:rl s1 s2 s3}
         {noccB:is_ff (poccur p B)}
         {l_prem:pts G A (sort s1)}
         {r_prem:pts (CONS (Gb p A) G) (vsub (par p) n B) (sort s2)}
     (*****************************************)
           pts G (pi n A B) (sort s3)]

[pLda:{G|Cxt}{A,M,B|Trm}{s1,s2,s3|SS}{p|PP}{n,m|VV}
         {sc:rl s1 s2 s3}
         {noccM:is_ff (poccur p M)}{noccB:is_ff (poccur p B)}
         {l_prem:pts (CONS (Gb p A) G) (vsub (par p) n M) (vsub (par p) m B)}
         {r_prem1:pts G A (sort s1)}
         {r_prem2:pts (CONS (Gb p A) G) (vsub (par p) m B) (sort s2)}
     (*****************************************)
           pts G (lda n A M) (pi m A B)]

[pApp:{G|Cxt}{M,A,B,L|Trm}{n|VV}
         {l_prem:pts G M (pi n A B)}
         {r_prem:pts G L A}
     (*****************************************)
           pts G (app M L) (vsub L n B)]

[ptCnv:{G|Cxt}{M,A,B|Trm}{s|SS}
         {sc:cnv A B}
         {l_prem:pts G M A}
         {r_prem:pts G B (sort s)}
     (*****************************************)
           pts G M B];

[ptsRec = pts_elim
        : {C:{G|Cxt}{M,A|Trm}(pts G M A)->Prop}
      {AX:{s1,s2|SS}
         {sc:ax s1 s2}
           C (pAx sc)}
      {START:{G|Cxt}{A|Trm}{s|SS}{p|PP}
         {noccG:is_ff (Poccur p G)}
         {prem:pts G A (sort s)}
         {ih:C prem}
           C (pStart noccG prem)}
      {vWEAK:{G|Cxt}{D,A|Trm}{s|SS}{n,p|PP}
         {noccG:is_ff (Poccur p G)}
         {l_prem:pts G (par n) D}
         {r_prem:pts G A (sort s)}
         {l_ih:C l_prem}
         {r_ih:C r_prem}
           C (pvWeak noccG l_prem r_prem)}
      {sWEAK:{G|Cxt}{D,A|Trm}{t,s|SS}{p|PP}
         {noccG:is_ff (Poccur p G)}
         {l_prem:pts G (sort t) D}
         {r_prem:pts G A (sort s)}
         {l_ih:C l_prem}
         {r_ih:C r_prem}
           C (psWeak noccG l_prem r_prem)}
      {PI:{G|Cxt}{A,B|Trm}{s1,s2,s3|SS}{p|PP}{n|VV}
         {sc:rl s1 s2 s3}
         {noccB:is_ff (poccur p B)}
         {l_prem:pts G A (sort s1)}
         {r_prem:pts (CONS (Gb p A) G) (vsub (par p) n B) (sort s2)}
         {l_ih:C l_prem}
         {r_ih:C r_prem}
           C (pPi sc noccB l_prem r_prem)}
      {LDA:{G|Cxt}{A,M,B|Trm}{s1,s2,s3|SS}{p|PP}{n,m|VV}
         {sc:rl s1 s2 s3}{noccM:is_ff (poccur p M)}{noccB:is_ff (poccur p B)}
         {l_prem:pts (CONS (Gb p A) G) (vsub (par p) n M)
                                       (vsub (par p) m B)}
         {r_prem1:pts G A (sort s1)}
         {r_prem2:pts (CONS (Gb p A) G) (vsub (par p) m B) (sort s2)}
         {l_ih:C l_prem}
         {r_ih1:C r_prem1}{r_ih2:C r_prem2}
           C (pLda sc noccM noccB l_prem r_prem1 r_prem2)}
      {APP:{G|Cxt}{M,A,B,L|Trm}{n|VV}
         {l_prem:pts G M (pi n A B)}
         {r_prem:pts G L A}
         {l_ih:C l_prem}
         {r_ih:C r_prem}
           C (pApp l_prem r_prem)}
      {tCONV:{G|Cxt}{M,A,B|Trm}{s|SS}
         {sc:cnv A B}
         {l_prem:pts G M A}
         {r_prem:pts G B (sort s)}
         {l_ih:C l_prem}
         {r_ih:C r_prem}
           C (ptCnv sc l_prem r_prem)}
      {G|Cxt}{M,A|Trm}{t:pts G M A}C t];

Goal {G|Cxt}{M,A|Trm}(pts G M A)->gts G M A;
Refine ptsRec [G:Cxt][M,A:Trm][_:pts G M A]gts G M A;
intros;Refine Ax;Immed;
intros;Refine Start;Immed;
intros;Refine vWeak;Immed;
intros;Refine sWeak;Immed;
intros;Refine Pi;Immed;
intros;Refine Lda;Immed;
       Refine Pi;Immed;
intros;Refine App;Immed;
intros;Refine tCnv;Immed;
Save pts_gts;


Goal {G|Cxt}{M,A|Trm}(pts G M A)->and (Vclosed M) (Vclosed A);
intros; Refine gts_Vclosed_lem (pts_gts H);
Save pts_Vclosed_lem;


Goal {G|Cxt}{A,B,C|Trm}{v|VV}{d:pts G (pi v A B) C}
      Ex4 [s1,s2,s3:SS][p:PP]
          and5 (rl s1 s2 s3)
               (pts G A (sort s1))
               (is_ff (poccur p B))
               (pts (CONS (Gb p A) G) (vsub (par p) v B) (sort s2))
               (cnv (sort s3) C);
intros;
Refine ptsRec [G:Cxt][M,C:Trm][_:pts G M C]
     {A,B|Trm}{v|VV}{eqPi:is_tt (Trm_eq M (pi v A B))}
      Ex4 [s1,s2,s3:SS][p:PP]
          and5 (rl s1 s2 s3)
               (pts G A (sort s1))
               (is_ff (poccur p B))
               (pts (CONS (Gb p A) G) (vsub (par p) v B) (sort s2))
               (cnv (sort s3) C);
Immed;

(* ax *) intros;Refine tt_not_ff (Q_sym eqPi);
(* start *) intros;Refine tt_not_ff (Q_sym eqPi);
(* vWeak *) intros;Refine tt_not_ff (Q_sym eqPi);
(* sWeak *) intros;Refine tt_not_ff (Q_sym eqPi);
(* pi *) 
intros;
[eqV = and3_out1 (Trm_eq_pi_lem eqPi)];
[eqA = and3_out2 (Trm_eq_pi_lem eqPi)];
[eqB = and3_out3 (Trm_eq_pi_lem eqPi)];
Qrepl Q_sym (VVdecide eqV);
Qrepl Q_sym (Trm_eq_subst eqA);
Qrepl Q_sym (Trm_eq_subst eqB);
Refine Ex4In;Refine +4 pair5;Immed;
Refine cnv_refl; Refine Vclosed_sort;
(* lda *)
intros;Refine tt_not_ff (Q_sym eqPi);
(* app *)
intros;Refine tt_not_ff (Q_sym eqPi);
(* cnv *) 
intros;Refine l_ih eqPi;
intros s1 s2 s3 p hyp;
[vclA = snd (pts_Vclosed_lem l_prem)];
[rule = and5_out1 hyp];
[hypA = and5_out2 hyp];
[pFresh = and5_out3 hyp];
[hypB = and5_out4 hyp];
[hypCnv = and5_out5 hyp];
Refine Ex4In;Refine +4 pair5;Immed;
Refine cnv_trans;Immed;
Refine Trm_eq_refl;
Save pts_gen_pi;

Goal {G|Cxt}{M,A|Trm}(gts G M A)->pts G M A;
intros;Refine aptsRec [G:Cxt][M,A:Trm][_:apts G M A]pts G M A;
intros;Refine pAx;Immed;
intros;Refine pStart;Immed;
intros;Refine pvWeak;Immed;
intros;Refine psWeak;Immed;

intros;Refine fresh_params_lem1G G1 B;
intros p pFresh;Refine pFresh;
intros noccG noccB;Refine pPi;Refine +6 r_ih;Immed;

intros;Refine pts_gen_pi r_ih;
intros s1 s2 s3 p hyp;Refine hyp;
intros r pA noccB pB c;
[noccG : is_ff (Poccur p G1) = CxtCorrect0 (pts_gts pB)];
Refine fresh_params_lem1G G1 (par p);
intros q qFresh;Refine qFresh;Qrepl pocc_par_lem q p;
intros noccG' neqP;Refine pLda;Immed;
Refine not_pocc_vsub_lem2
    (fst (free_params_lem1 (apts_gts (l_prem noccG')) ?));
Refine CONS_Poccur_lem;Qrepl PPsym p q;
Refine +2 l_ih;Immed;

intros;Refine pApp;Immed;
intros;Refine ptCnv;Immed;
Refine gts_apts;Immed;
Save gts_pts;
