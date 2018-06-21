Module expPost Import subject_reduction;

(* expansion postponment *)

(* the typing judgement with reduction only *)
$[rts:Cxt->Trm->Trm->Prop];

$[rAx:{s1,s2|SS}
         {sc:ax s1 s2}
           rts nilCxt (sort s1) (sort s2)];

$[rStart:{G|Cxt}{A|Trm}{s|SS}{p|PP}
         {noccG:is_ff (Poccur p G)}
         {prem:rts G A (sort s)}
     (*****************************************)
           rts (CONS (Gb p A) G) (par p) A];

$[rvWeak:{G|Cxt}{D,A|Trm}{s|SS}{n,p|PP}
         {noccG:is_ff (Poccur p G)}
         {l_prem:rts G (par n) D}
         {r_prem:rts G A (sort s)}
     (*****************************************)
           rts (CONS (Gb p A) G) (par n) D];

$[rsWeak:{G|Cxt}{D,A|Trm}{t,s|SS}{p|PP}
         {noccG:is_ff (Poccur p G)}
         {l_prem:rts G (sort t) D}
         {r_prem:rts G A (sort s)}
     (*****************************************)
           rts (CONS (Gb p A) G) (sort t) D];

$[rPi:{G|Cxt}{A,B|Trm}{s1,s2,s3|SS}{p|PP}{n|VV}
         {sc:rl s1 s2 s3}
         {noccB:is_ff (poccur p B)}
         {l_prem:rts G A (sort s1)}
         {r_prem:rts (CONS (Gb p A) G) (vsub (par p) n B) (sort s2)}
     (*****************************************)
           rts G (pi n A B) (sort s3)];

$[rLda:{G|Cxt}{A,M,B|Trm}{s|SS}{p|PP}{n,m|VV}
         {noccM:is_ff (poccur p M)}{noccB:is_ff (poccur p B)}
         {l_prem:rts (CONS (Gb p A) G) (vsub (par p) n M) (vsub (par p) m B)}
         {r_prem:rts G (pi m A B) (sort s)}
     (*****************************************)
           rts G (lda n A M) (pi m A B)];

$[rApp:{G|Cxt}{M,A,B,L|Trm}{n|VV}
         {l_prem:rts G M (pi n A B)}
         {r_prem:rts G L A}
     (*****************************************)
           rts G (app M L) (vsub L n B)];

$[rRed:{G|Cxt}{M,A,B|Trm}
         {sc:par_redn A B}
         {prem:rts G M A}
     (*****************************************)
           rts G M B];


$[rtsRec:{C:{G|Cxt}{M,A|Trm}(rts G M A)->Prop}
      {AX:{s1,s2|SS}
         {sc:ax s1 s2}
           C (rAx sc)}
      {START:{G|Cxt}{A|Trm}{s|SS}{p|PP}
         {noccG:is_ff (Poccur p G)}
         {prem:rts G A (sort s)}
         {ih:C prem}
           C (rStart noccG prem)}
      {vWEAK:{G|Cxt}{D,A|Trm}{s|SS}{n,p|PP}
         {noccG:is_ff (Poccur p G)}
         {l_prem:rts G (par n) D}
         {r_prem:rts G A (sort s)}
         {l_ih:C l_prem}
         {r_ih:C r_prem}
           C (rvWeak noccG l_prem r_prem)}
      {sWEAK:{G|Cxt}{D,A|Trm}{t,s|SS}{p|PP}
         {noccG:is_ff (Poccur p G)}
         {l_prem:rts G (sort t) D}
         {r_prem:rts G A (sort s)}
         {l_ih:C l_prem}
         {r_ih:C r_prem}
           C (rsWeak noccG l_prem r_prem)}
      {PI:{G|Cxt}{A,B|Trm}{s1,s2,s3|SS}{p|PP}{n|VV}
         {sc:rl s1 s2 s3}
         {noccB:is_ff (poccur p B)}
         {l_prem:rts G A (sort s1)}
         {r_prem:rts (CONS (Gb p A) G) (vsub (par p) n B) (sort s2)}
         {l_ih:C l_prem}
         {r_ih:C r_prem}
           C (rPi sc noccB l_prem r_prem)}
      {LDA:{G|Cxt}{A,M,B|Trm}{s|SS}{p|PP}{n,m|VV}
         {noccM:is_ff (poccur p M)}{noccB:is_ff (poccur p B)}
         {l_prem:rts (CONS (Gb p A) G) (vsub (par p) n M) (vsub (par p) m B)}
         {r_prem:rts G (pi m A B) (sort s)}
         {l_ih:C l_prem}
         {r_ih:C r_prem}
           C (rLda noccM noccB l_prem r_prem)}
      {APP:{G|Cxt}{M,A,B,L|Trm}{n|VV}
         {l_prem:rts G M (pi n A B)}
         {r_prem:rts G L A}
         {l_ih:C l_prem}
         {r_ih:C r_prem}
           C (rApp l_prem r_prem)}
      {RED:{G|Cxt}{M,A,B|Trm}
         {sc:par_redn A B}
         {prem:rts G M A}
         {ih:C prem}
           C (rRed sc prem)}
      {G|Cxt}{M,A|Trm}{t:rts G M A}C t];


(* rts is sound for gts *)
Goal {G|Cxt}{M,A|Trm}(rts G M A)->gts G M A;
Refine rtsRec [G:Cxt][M,A:Trm][_:rts G M A]gts G M A;
(* ax *)
intros; Refine Ax sc;
(* Start *)
intros; Refine Start; Immed;
(* vWeak *)
intros; Refine vWeak; Immed;
(* sWeak *)
intros; Refine sWeak; Immed;
(* pi *)
intros; Refine Pi; Immed;
(* Lda *)
intros; Refine Lda; Immed;
(* app *)
intros; Refine App; Immed;
(* red *)
intros; Refine gtsPR; Immed;
Save rtsFaithfull;


(* a nearly-syntax-directed system *)
$[nsdts:Cxt->Trm->Trm->Prop];

$[nsdAx:{s1,s2|SS}
         {sc:ax s1 s2}
           nsdts nilCxt (sort s1) (sort s2)];

$[nsdStart:{G|Cxt}{A,X|Trm}{s|SS}{p|PP}
         {noccG:is_ff (Poccur p G)}
         {redX:par_redn X (sort s)}
         {prem:nsdts G A X}
     (*****************************************)
           nsdts (CONS (Gb p A) G) (par p) A];

$[nsdvWeak:{G|Cxt}{D,A,X|Trm}{s|SS}{n,p|PP}
         {noccG:is_ff (Poccur p G)}
         {redX:par_redn X (sort s)}
         {l_prem:nsdts G (par n) D}
         {r_prem:nsdts G A X}
     (*****************************************)
           nsdts (CONS (Gb p A) G) (par n) D];

$[nsdsWeak:{G|Cxt}{D,A,X|Trm}{t,s|SS}{p|PP}
         {noccG:is_ff (Poccur p G)}
         {redX:par_redn X (sort s)}
         {l_prem:nsdts G (sort t) D}
         {r_prem:nsdts G A X}
     (*****************************************)
           nsdts (CONS (Gb p A) G) (sort t) D];

$[nsdPi:{G|Cxt}{A,B,X,Y|Trm}{s1,s2,s3|SS}{p|PP}{n|VV}
         {sc:rl s1 s2 s3}
         {noccB:is_ff (poccur p B)}
         {redX:par_redn X (sort s1)}{redY:par_redn Y (sort s2)}
         {l_prem:nsdts G A X}
         {r_prem:nsdts (CONS (Gb p A) G) (vsub (par p) n B) Y}
     (*****************************************)
           nsdts G (pi n A B) (sort s3)];

$[nsdLda:{G|Cxt}{A,M,B,X|Trm}{s|SS}{p|PP}{n,m|VV}
         {noccM:is_ff (poccur p M)}{noccB:is_ff (poccur p B)}
         {redX:par_redn X (vsub (par p) m B)}
         {l_prem:nsdts (CONS (Gb p A) G) (vsub (par p) n M) X}
         {r_prem:nsdts G (pi m A B) (sort s)}
     (*****************************************)
           nsdts G (lda n A M) (pi m A B)];

$[nsdApp:{G|Cxt}{M,A,A',B,L,X|Trm}{n|VV}
         {redX:par_redn X (pi n A B)}
         {sc:conv A A'}
         {l_prem:nsdts G M X}
         {r_prem:nsdts G L A'}
     (*****************************************)
           nsdts G (app M L) (vsub L n B)];


$[nsdtsRec:{C:{G|Cxt}{M,A|Trm}(nsdts G M A)->Prop}
      {AX:{s1,s2|SS}
         {sc:ax s1 s2}
           C (nsdAx sc)}
      {START:{G|Cxt}{A,X|Trm}{s|SS}{p|PP}
         {noccG:is_ff (Poccur p G)}
         {redX:par_redn X (sort s)}
         {prem:nsdts G A X}
         {ih:C prem}
           C (nsdStart noccG redX prem)}
      {vWEAK:{G|Cxt}{D,A,X|Trm}{s|SS}{n,p|PP}
         {noccG:is_ff (Poccur p G)}
         {redX:par_redn X (sort s)}
         {l_prem:nsdts G (par n) D}
         {r_prem:nsdts G A X}
         {l_ih:C l_prem}
         {r_ih:C r_prem}
           C (nsdvWeak noccG redX l_prem r_prem)}
      {sWEAK:{G|Cxt}{D,A,X|Trm}{t,s|SS}{p|PP}
         {noccG:is_ff (Poccur p G)}
         {redX:par_redn X (sort s)}
         {l_prem:nsdts G (sort t) D}
         {r_prem:nsdts G A X}
         {l_ih:C l_prem}
         {r_ih:C r_prem}
           C (nsdsWeak noccG redX l_prem r_prem)}
      {PI:{G|Cxt}{A,B,X,Y|Trm}{s1,s2,s3|SS}{p|PP}{n|VV}
         {sc:rl s1 s2 s3}
         {noccB:is_ff (poccur p B)}
         {redX:par_redn X (sort s1)}{redY:par_redn Y (sort s2)}
         {l_prem:nsdts G A X}
         {r_prem:nsdts (CONS (Gb p A) G) (vsub (par p) n B) Y}
         {l_ih:C l_prem}
         {r_ih:C r_prem}
           C (nsdPi sc noccB redX redY l_prem r_prem)}
      {LDA:{G|Cxt}{A,M,B,X|Trm}{s|SS}{p|PP}{n,m|VV}
         {noccM:is_ff (poccur p M)}{noccB:is_ff (poccur p B)}
         {redX:par_redn X (vsub (par p) m B)}
         {l_prem:nsdts (CONS (Gb p A) G) (vsub (par p) n M) X}
         {r_prem:nsdts G (pi m A B) (sort s)}
         {l_ih:C l_prem}
         {r_ih:C r_prem}
           C (nsdLda noccM noccB redX l_prem r_prem)}
      {APP:{G|Cxt}{M,A,A',B,L,X|Trm}{n|VV}
         {redX:par_redn X (pi n A B)}
         {sc:conv A A'}
         {l_prem:nsdts G M X}
         {r_prem:nsdts G L A'}
         {l_ih:C l_prem}
         {r_ih:C r_prem}
           C (nsdApp redX sc l_prem r_prem)}
      {G|Cxt}{M,A|Trm}{t:nsdts G M A}C t];


Goal {G|Cxt}{M,A|Trm}(nsdts G M A)->and (Vclosed M) (Vclosed A);
Refine nsdtsRec [G:Cxt][M,A:Trm][_:nsdts G M A]and (Vclosed M) (Vclosed A);
(* ax *)
intros;Refine pair;Refine Vclosed_sort;Refine Vclosed_sort;
(* start *)
intros;Refine pair;Refine Vclosed_par;Refine fst ih;
(* vWeak *)
intros;Refine pair;Refine Vclosed_par;Refine snd l_ih;
(* sWeak *)
intros;Refine l_ih;
(* pi *)
intros;Refine pair;
Refine Vclosed_pi (fst l_ih) (fst r_ih);
Refine Vclosed_sort;
(* lda *)
intros;Refine pair;
Refine Vclosed_lda (fst (Vclosed_pi_lem (fst r_ih))) (fst l_ih);
Refine (fst r_ih);
(* app *)
intros;Refine pair;
Refine Vclosed_app (fst l_ih) (fst r_ih);
Refine PPinf (params B);intros p noccB;
Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha L n noccB));
Refine psub_resp_Vclosed;
Refine (fst r_ih);
Refine (snd (Vclosed_pi_lem (snd (par_redn_Vclosed redX))));
Save nsdts_Vclosed_lem;

(* nsdts is sound for rts *)
Goal {G|Cxt}{M,A|Trm}(nsdts G M A)->rts G M A;
[rtsPR = [G|Cxt][M,A,B|Trm][j:rts G M A][r:par_redn A B]rRed r j];
Refine nsdtsRec [G:Cxt][M,A:Trm][_:nsdts G M A]rts G M A;
(* Ax *)
intros; Refine rAx sc;
(* Start *)
intros; Refine rStart noccG (rtsPR ih redX);
(* vWeak *)
intros; Refine rvWeak noccG l_ih (rtsPR r_ih redX);
(* sWeak *)
intros; Refine rsWeak noccG l_ih (rtsPR r_ih redX);
(* Pi *)
intros;
Refine rPi sc noccB (rtsPR l_ih redX) (rtsPR r_ih redY);
(* Lda *)
intros; Refine rLda noccM noccB ? r_ih;
Refine rtsPR l_ih redX;
(* App *)
intros; 
[vclA : Vclosed A
      = fst (Vclosed_pi_lem
               (snd (par_redn_Vclosed redX)))];
[vclA'  = snd (nsdts_Vclosed_lem r_prem)];
Refine convCR sc; intros AA hypAA;
[vclB : Vclosed (alpha p0 n B)
      = snd (Vclosed_pi_lem (snd (par_redn_Vclosed redX))) p0];
Refine rApp
       (rtsPR l_ih (par_redn_trans redX (par_redn_pi_l vclB (fst hypAA))))
       (rtsPR r_ih (snd hypAA));
Save nsdts_rts;

(* a small lemma for the next result *)
Goal {G|Cxt}{v|VV}{C,D,A|Trm}(nsdts G (pi v C D) A)->
      Ex [s:SS]is_tt (Trm_eq A (sort s));
intros;
Refine nsdtsRec [G:Cxt][M,A:Trm][_:nsdts G M A]
                {eq:is_tt (Trm_eq M (pi v C D))}
                 Ex [s:SS]is_tt (Trm_eq A (sort s));
Immed;
(* Ax *)
intros; Refine tt_not_ff (Q_sym eq);
(* Start *)
intros; Refine tt_not_ff (Q_sym eq);
(* vWeak *)
intros; Refine tt_not_ff (Q_sym eq);
(* sWeak *)
intros; Refine tt_not_ff (Q_sym eq);
(* Pi *)
intros; Refine ExIn s3; Refine Trm_eq_refl;
(* Lda *)
intros; Refine tt_not_ff (Q_sym eq);
(* App *)
intros; Refine tt_not_ff (Q_sym eq);
Refine Trm_eq_refl;
Save nsdtsPiLem;

(* completeness of nsdts for rts *)
Goal {G|Cxt}{M,A|Trm}(rts G M A)->Ex [E:Trm]and (nsdts G M E) (par_redn E A);
Refine rtsRec [G:Cxt][M,A:Trm][_:rts G M A]
             Ex [E:Trm]and (nsdts G M E) (par_redn E A);
(* Ax *)
intros; Refine ExIn (sort s2); 
Refine pair (nsdAx sc) (par_redn_refl ?); Refine Vclosed_sort;
(* Start *)
intros; Refine ExIn A; Refine ih;
intros ss sshyp; Refine pair ? (par_redn_refl ?);
Refine nsdStart noccG (snd sshyp) (fst sshyp);
Refine fst (gts_Vclosed_lem (rtsFaithfull prem));
(* vWeak *)
intros; Refine l_ih; 
intros C Chyp; Refine r_ih; 
intros ss sshyp;
Refine ExIn C; Refine pair ? (snd Chyp);
Refine nsdvWeak noccG (snd sshyp) (fst Chyp) (fst sshyp);
(* sWeak *)
intros; Refine l_ih; 
intros C Chyp; Refine r_ih; 
intros ss sshyp;
Refine ExIn C; Refine pair ? (snd Chyp);
Refine nsdsWeak noccG (snd sshyp) (fst Chyp) (fst sshyp);
(* Pi *)
intros; Refine l_ih; 
intros lt lhyp; Refine r_ih; 
intros rt rhyp;
Refine ExIn (sort s3); Refine pair ? (par_redn_refl ?);
Refine nsdPi sc noccB (snd lhyp) (snd rhyp) (fst lhyp) (fst rhyp);
Refine Vclosed_sort;
(* Lda *)
intros; Refine l_ih; 
intros lt lhyp; Refine r_ih; 
intros rt rhyp;
Refine ExIn (pi m A B); Refine pair ? (par_redn_refl ?);
Refine nsdtsPiLem (fst rhyp); 
intros ss ssSpec;
Refine nsdLda noccM noccB (snd lhyp) (fst lhyp); Refine ss;
Qrepl Q_sym (Trm_eq_subst ssSpec); Refine fst rhyp;
Refine fst (gts_Vclosed_lem (rtsFaithfull r_prem));
(* App *)
intros; Refine l_ih; intros lt lhyp; Refine r_ih; intros rt rhyp;
Refine ExIn (vsub L n B); Refine pair ? (par_redn_refl ?);
Refine +1 snd (nsdts_Vclosed_lem ?+0);
Refine nsdApp (snd lhyp) (conv_sym (conv_redn (snd rhyp)));
Refine fst lhyp; Refine fst rhyp;
(* tConv *)
intros; Refine ih; intros t hyp; Refine ExIn t;
Refine pair (fst hyp) (par_redn_trans (snd hyp) sc);
Save rts_nsdts;




