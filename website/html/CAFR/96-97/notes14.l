Module notes14 Import lib_nat_Lt lib_adt_basics lib_list_basics;

Record [Str_STACK:STR] ElimOver Type
Fields [Stack:Setoid]
       [emptyS:Stack.dom]
       [push :nat->Stack.dom->Stack.dom]
       [pop  :Stack.dom->Stack.dom]
       [top  :Stack.dom->nat];

(* axioms *)
[S:Str_STACK];
[EqSTACK  = Equivalence (eq|S.Stack)]; 
[AxSTACK1 = eq (S.pop S.emptyS) S.emptyS]; 
[AxSTACK2 = Eq (S.top S.emptyS) zero];  
[AxSTACK3 = {n:nat}{s:S.Stack.dom}eq (S.pop (S.push n s)) s];
[AxSTACK4 = {n:nat}{s:S.Stack.dom}Eq (S.top (S.push n s)) n];

[Ax_STACK = and5 EqSTACK AxSTACK1 AxSTACK2 AxSTACK3 AxSTACK4];
Discharge S;
[STACK = make_SPEC Str_STACK Ax_STACK];

Goal listStack : Str_STACK;
Refine make_Str_STACK;
Refine make_Setoid (list nat) (Eq|(list nat)); (* domain and Eq as eq *)
Refine (nil nat);                          (* empty stack *)
Refine cons;                               (* push *)
Refine tail;                               (* pop *)
Refine hd zero;                            (* top *)
(* QED *)
Save listStack;

Goal eqStackL : 
     listStack.EqSTACK;
Refine pair3;
Refine Eq_refl; Refine Eq_sym; Refine Eq_trans;
(* QED *)
Save eqStackL;

(* AxStack1 *)
Goal axStack1L : 
     listStack.AxSTACK1;
Refine Eq_refl;
(* QED *)
Save axStack1L;


(* AxSTACK2 *)
Goal axStack2L : 
     listStack.AxSTACK2; 
Refine Eq_refl;
(* QED *)
Save;

(* AxSTACK3 *)
Goal axStack3L : 
     listStack.AxSTACK3; 
Expand AxSTACK3; intros; 
Refine Eq_refl;
(* QED *)
Save;

(* AxSTACK4 *)
Goal axStack4L : 
     listStack.AxSTACK4; 
Expand AxSTACK4; intros; Refine Eq_refl;
(* QED *)
Save;

Goal listStack_correct : listStack.Ax_STACK;
Refine pair5; Refine eqStackL; 
Refine axStack1L; Refine axStack2L;
Refine axStack3L; Refine axStack4L;
Save;

Goal Mod STACK;
Refine dep_pair;
Refine listStack;
Refine listStack_correct;




[S:Str_STACK];
[RespSTACKpush= {n,m:nat}{s,s':S.Stack.dom}
                (Eq n m)->(eq s s')->eq (S.push n s) (S.push m s')];
[RespSTACKpop = {s,s':S.Stack.dom}(eq s s')->(eq (S.pop s) (S.pop s'))];
[RespSTACKtop = {s,s':S.Stack.dom}(eq s s')->(Eq  (S.top s) (S.top s'))];
[RespSTACK    = and3 RespSTACKpush RespSTACKpop RespSTACKtop];
Discharge S;

[STACK_CONG = Extend_AxOnly STACK RespSTACK : SPEC];


Goal respStackL : 
     listStack.RespSTACK;
Refine pair3; 
Expand RespSTACKpush; intros; Qrepl H; Qrepl H1; Refine Eq_refl;
Expand RespSTACKpop;  intros; Qrepl H; Refine Eq_refl;
Expand RespSTACKtop;  intros; Qrepl H; Refine Eq_refl;
Save;

Goal listStack_correct_cong : STACK_CONG.Ax listStack;
Refine pair; Refine listStack_correct; Refine respStackL;
Save;


(* structure type for Arrays *)
Record [Str_ARRAY:STR] ElimOver Type
Fields [Array   :Setoid]
       [newarray:Array.dom]
       [assign  :nat->Array.dom->nat->Array.dom]
       [access  :Array.dom->nat->nat];

(* axioms *)
[A:Str_ARRAY];
[EqARRAY  = Equivalence (eq|A.Array)];
[AxARRAY1 = {i:nat}Eq (A.access A.newarray i) zero]; 
[AxARRAY2 = {n,i,j:nat}{arr:A.Array.dom}
                and ((Eq i j) -> 
                     (Eq (A.access (A.assign n arr i) j) n))
                    ((not (Eq i j)) -> 
                     (Eq (A.access (A.assign n arr i) j) (A.access arr j)))
];
[Ax_ARRAY = and3 EqARRAY AxARRAY1 AxARRAY2];
Discharge A;

[ARRAY = make_SPEC Str_ARRAY Ax_ARRAY : SPEC];


Goal Lt_not_Eq : 
     {x,y:nat}(Lt x y)->(not (Eq x y));
intros; Refine H; intros; Qrepl Eq_sym H1; 
Intros _; Refine plus_suc_lemma x t; Refine Eq_sym H2;
Save;
Goal refnSA : 
     ARRAY.Str -> STACK.Str;
Intros A; Refine make_Str_STACK;
Refine make_Setoid; 
(* domain of impl of stack: arr-ptr pairs *)
[domImpl =  A.Array.dom # nat]; Refine domImpl;
(* equality over the impl domain *)
[eqImpl [s,s':domImpl] =
       and (Eq s.2 s'.2) 
          ({i:nat}(Lt i s.2)->
              (Eq (A.access s.1 i) (A.access s'.1 i)))];
 Refine eqImpl;
(* empty stack *)
Intros #;
Refine A.newarray;
Refine zero;
(* push *)
intros;Intros #;
Refine A.assign H H1.1 H1.2;
Refine suc H1.2;
(* pop *)
intros;Intros #;
Refine H.1;Refine pred H.2;
(* top *)
intros; 
Refine if_zero H.2 zero (A.access H.1 (pred H.2));
(* QED *)
Save;


[A:ARRAY.Str][ax_arrayA : ARRAY.Ax A];
Goal equivSTACK : 
     Equivalence (eq|A.refnSA.Stack);
intros; Refine pair3; 
Intros _;
Refine pair;
Refine Eq_refl;
intros; Refine Eq_refl;
Intros t u tu; Refine pair; Qrepl tu.fst; Refine Eq_refl;
intros; Refine Eq_sym;
Refine tu.snd;Qrepl tu.fst;
Immed;
Intros t u v tu uv;
Refine pair;
Qrepl tu.fst;Refine uv.fst;
intros; Refine Eq_trans;
Refine A.access u.1 i;
Refine tu.snd; Immed;
Refine uv.snd; Qrepl (Eq_sym tu.fst); Immed;
Save;

Goal axSTACK1 : 
     A.refnSA.AxSTACK1;
Expand AxSTACK1; Refine pair; 
Refine Eq_refl; 
intros; Refine not_n_Lt_zero i; Refine H;
(* QED *)
Save;

Goal axSTACK2 :
     A.refnSA.AxSTACK2;
Refine Eq_refl;
(* QED *)
Save;


Goal axSTACK3 : 
     A.refnSA.AxSTACK3;
Expand AxSTACK3; Refine ax_arrayA; Intros _ _ axA2;
intros; Refine pair; 
Refine Eq_refl;
intros; Refine axA2 n s.2 i s.1; intros; Refine H4;
Intros _; Refine Lt_not_Eq ? ? H2; Refine H5.Eq_sym;
(* QED *)
Save;


Goal axSTACK4 : 
     A.refnSA.AxSTACK4;
Expand AxSTACK4; Refine ax_arrayA; Intros _ _ axA2; 
intros; Refine axA2 n s.2 s.2 s.1; 
intros; Refine H2; Refine Eq_refl;
(* QED *)
Save;

Discharge A;

Goal refnSA.Sat; 
Intros A ax_arrayA; Refine pair5;

Refine equivSTACK;

Refine axSTACK1;
Refine axSTACK2;
Refine axSTACK3 A ax_arrayA;
Refine axSTACK4 A ax_arrayA;
(* QED *)
Save sat_refnSA;

