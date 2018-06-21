Module thinning
Import gts apts generation;

(* thinning lemma and general weakening *)

(* first, thinning for apts *)
%\VerbFileOpen apts_thinning_lem
Goal apts_thinning_lem:
     {G|Cxt}{M,A|Trm}{j:apts G M A}
     {G'|Cxt}{sub:subCxt G G'}{val:Valid G'}apts G' M A;
%\VerbFileClos apts_thinning_lem
Refine aptsRec [G:Cxt][M,A:Trm][_:apts G M A]
     {G'|Cxt}{sub:subCxt G G'}{val:Valid G'}apts G' M A;
(* ax *)
intros; Refine gts_apts; Refine val; intros X Y gtsGXY;
Refine sStartLem; Immed;
(* start *)
intros; Refine gts_apts; Refine val; intros X Y gtsGXY;
Equiv gts ? (par (namOf (Gb p A))) (typOf (Gb p A));
Refine vStartLem gtsGXY; Refine sub; Refine hd_GBoccur_lem;
(* vWeak *)
intros; Refine l_ih; Immed; Refine subCxt_tail sub;
(* sWeak *)
intros; Refine l_ih; Immed; Refine subCxt_tail sub;
(* pi *) 
intros; Refine aPi sc (l_ih ??); Immed;
intros; Refine r_ih;
Refine Poccur_subCxt_lem sub noccG;
Refine subCxt_extension sub;
Refine Ex2In (par p) A; Refine Start noccG;
Refine +1 apts_gts; Refine +1 l_ih; Immed;
(* lda *) 
intros;Refine aLda;Refine +2 r_ih; Immed;
intros; Refine l_ih; 
Refine Poccur_subCxt_lem sub noccG;
Refine subCxt_extension sub;
Refine Ex2In (par p) A;
(* now use the pi case of the generation lemma *)
Refine gts_gen_pi (apts_gts (r_ih sub val));
intros s1 s2 s3 fresh lem;
[welltypedA : gts G' A (sort s1) = and5_out2 lem];
Refine Start noccG welltypedA;
(* app *) 
intros; Refine gts_apts;
Refine App; 
Refine +2 apts_gts; Refine +2 r_ih;
Refine apts_gts; Refine l_ih; Immed;
(* cnv *) 
intros; Refine gts_apts;
Refine tCnv sc;
Refine +2 apts_gts; Refine +2 r_ih;
Refine apts_gts; Refine l_ih; Immed;
Save apts_thinning_lem;

%\VerbFileOpen thinning_lemma
Goal thinning_lemma: {G|Cxt}{M,A|Trm}{j:gts G M A}
                     {G'|Cxt}{sub:subCxt G G'}{val:Valid G'}gts G' M A;
%\VerbFileClos thinning_lemma
intros; Refine apts_gts; Refine apts_thinning_lem;
Refine +1 gts_apts; Immed;
Save;

(* full weakening is now admissible *)
%\VerbFileOpen weakening
Goal weakening: {G|Cxt}{M,B|Trm}(gts G M B)->
                {p|PP}(is_ff (Poccur p G))->
                {A|Trm}{s|SS}(gts G A (sort s))->
                gts (CONS (Gb p A) G) M B;
%\VerbFileClos weakening
intros;Refine thinning_lemma;Immed;
Refine subCxt_hd;
Refine Ex2In;Refine +2 Start;Immed;
Save weakening;
