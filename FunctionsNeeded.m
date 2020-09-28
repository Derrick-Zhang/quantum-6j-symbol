(* ::Package:: *)

BeginPackage["FunctionsNeeded`"]


x::usage="Global variable";
k::usage="Global variable";
q::usage="Global variable";
A::usage="Global variable";
t::usage="Global variable";
Q::usage="Global variable";
\[Sigma]::usage="Global variable";
i0::usage="Global variable";
tr::usage="Global variable";
tc::usage="Global variable";
a::usage="Global variable";

aa=t/(1+t+t^2);
bb=Sqrt[t/(1+t+t^2)];
cc=Sqrt[1+t+t^2+t^3+t^4]/(1+t+t^2);
dd=(1-t+t^2)/(1+t^2);
ee=-(Sqrt[t (1+2 t+3 t^2+3 t^3+3 t^4+2 t^5+t^6)]/(1+t+2 t^2+t^3+t^4));
ff=t^2/(1+t+2 t^2+t^3+t^4); (* building components of SO(4) double box fusion matrix *)

qno[x_]:=(t^(x/2)-t^(-x/2))/(t^(1/2)-t^(-1/2))(*q-number*)
qfac[n_]:=Product[qno[m],{m,1,n}](*q-factorial*)
qbino[p_,q_]:=qfac[p]/(qfac[q]qfac[p-q])(*q-binomial*)
Rel[x_]:=x/.{a->\[Lambda]^(3/2)q^(-5/2)tr,Q->\[Lambda]^(3/4)q^(-5/4)tr^(1/2),tr->\[Lambda]^(-1/2)q^(3/2)}
(* change of variables from HOMFLY-PT to get Kauffman *)

(* functions needed for double box fusion matrix *)
cassimir[n_,r_]:=1/2 ((n-1)*Sum[r[[i]],{i,1,Length[r]}]+Sum[r[[i]],{i,1,Length[r]}]+Sum[r[[i]]^2-2*i*r[[i]],{i,1,Length[r]}])
(* casimir for SO(n) representation r *)
\[Lambda]pls[n_,1]:=t^(2cassimir[n,{2}]);
\[Lambda]pls[n_,2]:=-t^(2cassimir[n,{2}]-cassimir[n,{1,1}]/2);
\[Lambda]pls[n_,3]:=t^(2cassimir[n,{2}]-cassimir[n,{2}]/2);
\[Lambda]pls[n_,4]:=t^(2cassimir[n,{2}]-cassimir[n,{2,2}]/2);
\[Lambda]pls[n_,5]:=-t^(2cassimir[n,{2}]-cassimir[n,{3,1}]/2);
\[Lambda]pls[n_,6]:=t^(2cassimir[n,{2}]-cassimir[n,{4}]/2);
\[Lambda]mns[n_,1]:=t^(1/2 cassimir[n,{}]);
\[Lambda]mns[n_,2]:=-t^(1/2 cassimir[n,{1,1}]);
\[Lambda]mns[n_,3]:=t^(1/2 cassimir[n,{2}]);
\[Lambda]mns[n_,4]:=t^(1/2 cassimir[n,{2,2}]);
\[Lambda]mns[n_,5]:=-t^(1/2 cassimir[n,{3,1}]);
\[Lambda]mns[n_,6]:=t^(1/2 cassimir[n,{4}]);
(* braiding operator eigenvalues, n means SO(n) *)
dimR[n_]=qno[n-1]+(qno[n-1]qno[n])/qno[2]//Simplify;
(* quantum dimension of horizontal double box representation of SO(n) *)


(* functions needed for single box fusion matrix *)
qdimR[n_]= qno[n-1]+1;
(* quantum dimension of horizontal one box representation of SO(n) *)
qdim11=qno[n-1]+(qno[n-1]qno[n-2])/qno[2];
qdim2=qno[n-1]+(qno[n-1]qno[n])/qno[2];
xx=qno[n-2]/qno[2];
yy=1/qno[2] Sqrt[(qno[2]+qno[n])(qno[2]+qno[n-2])];
zz=qno[n]/qno[2];
\[Lambda]plus[n_,1]:=t^(2cassimir[n,{1}]-1/2 cassimir[n,{}])
\[Lambda]plus[n_,2]:=t^(2cassimir[n,{1}]-1/2 cassimir[n,{2}])
\[Lambda]plus[n_,3]:=-t^(2cassimir[n,{1}]-1/2 cassimir[n,{1,1}])
\[Lambda]minus[n_,1]:=t^(1/2 cassimir[n,{}])
\[Lambda]minus[n_,2]:=t^(1/2 cassimir[n,{2}])
\[Lambda]minus[n_,3]:=-t^(1/2 cassimir[n,{1,1}])


Begin["`CommonDefinition`"]

  bra[x_]:=x-1/x;

  ListL[r_,s_]:=Per[Table[r,s]];

  Per[\[Lambda]_]:={vlist=Table[Subscript[x, i],{i,Length@\[Lambda]}];Flatten[#,Length@\[Lambda]-1]&@(Table@@({vlist}
            ~Join~ {{First@vlist,0,First@\[Lambda]}}~Join~Reverse[Table[{vlist[[i]],0,Min[vlist[[i-1]],\[Lambda][[i]]]},{i,Length@\[Lambda],2,-1}]]))}[[1]];

  arm[box_,\[Lambda]_]:=\[Lambda][[box[[2]]]]-box[[1]];

  coarm[box_]:=box[[1]]-1;

  leg[box_,\[Lambda]_]:=Length[Select[\[Lambda],#>=box[[1]]&]]-box[[2]];

  coleg[box_]:=box[[2]]-1;

  MoL[Lambda_]:=Plus@@Lambda;
  
  Variable[x_,n_]:={Clear@x,ToExpression[ToString[x]<>ToString[n]]}[[2]];
   
  StringPartGenerate[x_,n_]:=If[ n==0, "",{Clear@x,","<>StringDrop[StringJoin[Table[ToString@x<>ToString@ii<>",",{ii,n}]],-1]}[[2]]];
  
  
End[]



Begin["`TwistFactor`"]
  
  arm := FunctionsNeeded`CommonDefinition`arm;
  leg := FunctionsNeeded`CommonDefinition`leg;
  coarm := FunctionsNeeded`CommonDefinition`coarm;
  coleg := FunctionsNeeded`CommonDefinition`coleg;
  MoL := FunctionsNeeded`CommonDefinition`MoL;
  bra := FunctionsNeeded`CommonDefinition`bra;
  Variable:=  FunctionsNeeded`CommonDefinition`Variable;
  StringPartGenerate :=  FunctionsNeeded`CommonDefinition`StringPartGenerate;
  Per := FunctionsNeeded`CommonDefinition`Per;
  
  
  
  (*Unrefined Twist Factor*)
  
  d[s_,\[Mu]_]:=Product[ bra[q^(s-coleg[{i,j}]) q^coarm[{i,j}]]/bra[q^(leg[{i,j},\[Mu]]+1) q^arm[{i,j},\[Mu]]],{j,Length[\[Mu]]},{i,\[Mu][[j]]}];
  
  QDMatrix[\[Lambda]_,\[Mu]_,m_]:=Module[{$\[Lambda] =\[Lambda], $\[Mu] =\[Mu], $m=m},
  $\[Mu]=Flatten[Append[$\[Mu],Table[0,$m-Length@$\[Mu]]]];
  $\[Lambda]=Flatten[Append[$\[Lambda],Table[0,$m-Length@$\[Lambda]]]];
Table[QBinomial[$\[Lambda][[i]]+$m-i,$\[Mu][[j]]+$m-j,q^(2)],{i,1,$m},{j,1,$m}]
];
  
  Prefactor[s_,\[Lambda]_,\[Mu]_]:=A^(2 MoL[\[Mu]]) q^(-(s-1)MoL[\[Lambda]]+(s-1) MoL[\[Mu]]) Product[q^(-4coleg[{i,j}]+4coarm[{i,j}]),{j,Length[\[Mu]]},{i,\[Mu][[j]]}];
  
  block[s_,\[Lambda]_,\[Mu]_]:=Prefactor[s,\[Lambda],\[Mu]]Det[QDMatrix[\[Lambda],\[Mu],s]];
  
  GenDiagramList[\[Lambda]_,m_]:=Module[{$\[Lambda] = \[Lambda], mm = m-1,\[Mu]List,i},
          \[Mu]List = Table[Variable[\[Mu],i],{i,0,mm}];
          \[Mu]List[[1]] = {$\[Lambda]};
          For[i=1,i<=mm,i++,
              \[Mu]List[[i+1]] = Map[Per,\[Mu]List[[i]],{i}];
             ];
          Return[\[Mu]List];
  ];
  
  Evaluateblock[\[Lambda]_,m_,s_]:=Module[{mm=m,i,result="",addterm},
      For[i=1,i<=mm-1,i++,
           addterm = "FunctionsNeeded`TwistFactor`block["<>ToString[s]<>",(FunctionsNeeded`TwistFactor`GenDiagramList["<>ToString[\[Lambda]]<>","<>ToString[mm]<>"])\[LeftDoubleBracket]"<>ToString[i]<>",1"<>StringPartGenerate[k,i-1]<>"\[RightDoubleBracket]"<>",FunctionsNeeded`TwistFactor`GenDiagramList["<>ToString[\[Lambda]]<>","<>ToString[m]<>"]\[LeftDoubleBracket]"<>ToString[i+1]<>",1"<>StringPartGenerate[k,i]<>"\[RightDoubleBracket]]";
           result = addterm<>result;
         ];
      Return[result<>"FunctionsNeeded`TwistFactor`d["<>ToString[s]<>",(FunctionsNeeded`TwistFactor`GenDiagramList["<>ToString[\[Lambda]]<>","<>ToString[mm]<>"])\[LeftDoubleBracket]"<>ToString[mm]<>",1"<>StringPartGenerate[k,mm-1]<>"\[RightDoubleBracket]]"];
];
  
  IteratorGenerator[\[Lambda]_,m_]:=Module[{mm=m,$\[Lambda] = \[Lambda]},
    Table[{ToString[Variable[k,i]]<>",Length@((FunctionsNeeded`TwistFactor`GenDiagramList["<>ToString[$\[Lambda]]<>","<>ToString[mm]<>"])\[LeftDoubleBracket]"<>ToString[i+1]<>",1"<>StringPartGenerate[k,i-1]<>"\[RightDoubleBracket])"},{i,1,mm-1}]
 ];
 
 UnrefinedFFactor[\[Lambda]_,m_,s_]:=ToExpression["Sum["<>Evaluateblock[\[Lambda],m,s]<>","<>StringDrop[StringDrop[ToString[IteratorGenerator[\[Lambda],m]],1],-1]<>"]"](d[s,\[Lambda]])^(-1);
  
 
 Ftrefoil[\[Lambda]_]:=(-A^2)^MoL@(\[Lambda]) Product[q^(2arm[{i,j},\[Lambda]]) q^(-2leg[{i,j},\[Lambda]]),{j,Length[\[Lambda]]},{i,\[Lambda][[j]]}];
 

 UnrefinedTWFactor[\[Lambda]_,m_,s_]:=If[m==-1,1,If[m==1,Ftrefoil[\[Lambda]],If[m<0,UnrefinedFFactor[\[Lambda],-m,s]/.{A->A^(-1),q->q^(-1)},UnrefinedFFactor[\[Lambda],m,s]Ftrefoil[\[Lambda]]]]];





(*Semistandard Young Tableaux*)

Shape[SSYT_]:=Table[Length[SSYT[[i]]],{i,1,Length@SSYT}];

ConjugateeTableau[tablea_]:=Module[{t=tablea,\[Lambda], con\[Lambda], i,j,kk},
     \[Lambda]=Shape[t];
     con\[Lambda] = If[\[Lambda]=={},{},Table[Length[Select[\[Lambda],#>=i&]],{i,1,\[Lambda][[1]]}]];
     Return[Table[t[[kk,j]],{j,Length@con\[Lambda]},{kk,con\[Lambda][[j]]}]];
]

row[length_,maxNum_]:=
Module[{iter,expr},
iter=Table[
{Symbol["i"<>ToString[kk]],Symbol["i"<>ToString[kk-1]],maxNum},
{kk,length}]/.i0->Nothing;
expr=Table[Symbol["i"<>ToString@kk],{kk,length}];
Flatten[
Table@@Join[{Evaluate@expr},Evaluate@iter],length-1]
]

tableaux[shape_,maxNum_]:=
Module[{rows},
rows=row[#,maxNum]&/@shape;
Flatten[
Outer[List,Sequence@@rows,1],Length[shape]-1]
]

validTableauxQ[p_]:=
AllTrue[p,OrderedQ[#,Less]&]


SemistandardTableaux[shape_,maxNum_]:=
Module[{p},
p=ConjugateeTableau/@tableaux[shape,maxNum];
ConjugateeTableau/@Select[p,validTableauxQ]
]

(*Reversed tableaux*)

Reverestablau[young_,max_]:=Module[{y=young,m= max,SSYTs},
SSYTs = SemistandardTableaux[y, m];
Return[m + 1 - SSYTs];
]

(*Horizontal Strips*)

RemoveFromYoung[SSYT_,number_]:=Module[{S=SSYT,n=number, ans={},i,removedrow},
For[i=1, i<=Length@S,i++,
removedrow = DeleteCases[S[[i]],n];
If[removedrow !={}, 
ans = Append[ans,removedrow]];
];
Return[ans];
]



HorizontalStrips[SSYT_, maxn_]:=Module[{S=SSYT,mn=maxn,ans={},rssyt,young,i},
   rssyt = S;
young = Shape[rssyt];
ans= Append[ans,young];
For[i=mn, i>0,i--,
rssyt = RemoveFromYoung[rssyt, i];
young = Shape[rssyt];
ans = Append[ans, young];
];
Return[ans];
]

(*psi and Psi*)

b[young_,i_,j_]:=(1-q^arm[{j,i},young] t^(leg[{j,i},young]+1))/(1-q^(arm[{j,i},young]+1) t^leg[{j,i},young])


SkewTableauChain[\[Mu]_,\[Lambda]_]:=Module[{m=\[Mu],l=\[Lambda],skewTableau,i,j},
     skewTableau=Table[1,{i,Length@l},{j,l[[i]]}];
     For[i=1,i<=Length@m,i++,
         For[j=1, j<=m[[i]],j++,
             skewTableau[[i,j]]= 0;
            ];
         ];
Return[skewTableau];
]



BoxInSkew[skewtableau_]:=Module[{skt=skewtableau,list={},ans={},j,i,kk,conskew},
conskew = ConjugateeTableau[skt];
For [j =1, j<=Length@conskew, j++,
If [conskew[[j,-1]]==0,list = Append[list,j]];];
For[i=1, i<=Length@skt, i++,
If[skt[[i,-1]]!=0,
For [kk =1, kk <=Length@list, kk++,
If[list[[kk]]<= Length@skt[[i]],
ans = Append[ans,{i,list[[kk]]}]];
];
];
];
Return[ans];
]

psi[\[Lambda]_,\[Mu]_]:=Module[{l=\[Lambda],m=\[Mu],list,i},
list = BoxInSkew[SkewTableauChain[m,l]];
Return[Product[b[m,list[[i,1]],list[[i,2]]]/b[l,list[[i,1]],list[[i,2]]],{i,1,Length@list}]];
]

Psi[SSYT_,number_]:=Module[{S=SSYT,n=number,youngs},
youngs=HorizontalStrips[S,n];
Return[Product[psi[youngs[[i]],youngs[[i+1]]],{i,Length@youngs-1}]];
]

(*shifted Macdonald polynomial*)


Variablex[n_]:={Clear@x,ToExpression[ToString[x]<>ToString[n]]}[[2]]

xTableShift[SSYT_]:=Product[t^(1-SSYT[[i,j]]) (Variablex[SSYT[[i,j]]]-q^coarm[{j,i}] t^-coleg[{j,i}]),{i,Length@SSYT},{j,Length@SSYT[[i]]}]

ShiftedMacdonald[young_,n_]:=Module[{y = young, nn=n,SST,Psilist,RSST,i,j},
If[young=={},Return[1],
SST = SemistandardTableaux[y,nn];
Psilist = Table[Psi[SST[[i]],nn],{i,Length@SST}];
RSST = Reverestablau[y,nn];
Return[Sum[Psilist[[j]]xTableShift[RSST[[j]]],{j,Length@SST}]];
]
]




(* qt- Binomial Formula*)

BinomialFormulaqtpre[\[Lambda]_,\[Mu]_]:=Module[{l=\[Lambda],m=\[Mu],xmTable,xlTable},
xmTable = Table[Variablex[i],{i,1,Length@m}];
xlTable = Table[Variablex[i],{i,1,Length@l}];
(ShiftedMacdonald[m,Length@l]/.Table[Rule[xlTable[[i]],q^l[[i]]],{i,1,Length@l}])/(ShiftedMacdonald[m,Length@m]/.Table[Rule[xmTable[[i]],q^m[[i]]],{i,1,Length@m}])
 ]
 
BinomialFormulaqt[\[Lambda]_,\[Mu]_,s_]:=(BinomialFormulaqtpre[\[Lambda],\[Mu]]/.{q->q^2,t->t^2})((ShiftedMacdonald[\[Lambda],s]/.Table[Rule[Variablex[i],0],{i,1,s}])/(ShiftedMacdonald[\[Mu],s]/.Table[Rule[Variablex[i],0],{i,1,s}])/.{q->q^-2,t->t^-2})


(*Refined Twist Factor*)

PerdZ[\[Lambda]_]:=Module[{$\[Lambda] = \[Lambda],m,llist },
If[$\[Lambda]=={},Return[{{}}];,
llist= Per[$\[Lambda]];
m= Length@llist;Return[Table[DeleteCases[llist[[i]],0],{i,1,m}]];
]
]

reprefactor[s_,\[Lambda]_,\[Mu]_]:=(-t^(1-s))^(MoL[\[Lambda]]-MoL[\[Mu]]) ((A q)/t)^(2MoL[\[Mu]]) Product[q^(2coarm[{i,j}])t^(-2coleg[{i,j}]),{j,Length[\[Lambda]]},{i,\[Lambda][[j]]}]Product[q^(2coarm[{i,j}])t^(-2coleg[{i,j}]),{j,Length[\[Mu]]},{i,\[Mu][[j]]}];

reblock[s_,\[Lambda]_,\[Mu]_]:=reprefactor[s,\[Lambda],\[Mu]]BinomialFormulaqt[\[Lambda],\[Mu],s];

dref[s_,\[Mu]_]:=Product[(bra[t^(s-coleg[{i,j}]) q^coarm[{i,j}]]/bra[t^(leg[{i,j},\[Mu]]+1) q^arm[{i,j},\[Mu]]]),{j,Length[\[Mu]]},{i,\[Mu][[j]]}];

reGenDiagramList[\[Lambda]_,m_]:=Module[{$\[Lambda] = \[Lambda], mm = m-1,\[Mu]List,i},
\[Mu]List = Table[Variable[\[Mu],i],{i,0,mm}];
\[Mu]List[[1]] = {$\[Lambda]};
For[i=1,i<=mm,i++,
\[Mu]List[[i+1]] = Map[PerdZ,\[Mu]List[[i]],{i}];
];
Return[\[Mu]List];
];

reEvaluateblock[\[Lambda]_,m_,s_]:=Module[{mm=m,i,result="",addterm},
      For[i=1,i<=mm-1,i++,
           addterm = "FunctionsNeeded`TwistFactor`reblock["<>ToString[s]<>",(FunctionsNeeded`TwistFactor`reGenDiagramList["<>ToString[\[Lambda]]<>","<>ToString[mm]<>"])\[LeftDoubleBracket]"<>ToString[i]<>",1"<>StringPartGenerate[k,i-1]<>"\[RightDoubleBracket]"<>",FunctionsNeeded`TwistFactor`reGenDiagramList["<>ToString[\[Lambda]]<>","<>ToString[mm]<>"]\[LeftDoubleBracket]"<>ToString[i+1]<>",1"<>StringPartGenerate[k,i]<>"\[RightDoubleBracket]]";
           result = addterm<>result;
         ];
      Return[result<>"FunctionsNeeded`TwistFactor`dref["<>ToString[s]<>",(FunctionsNeeded`TwistFactor`reGenDiagramList["<>ToString[\[Lambda]]<>","<>ToString[mm]<>"])\[LeftDoubleBracket]"<>ToString[mm]<>",1"<>StringPartGenerate[k,mm-1]<>"\[RightDoubleBracket]]"];
];

reIteratorGenerator[\[Lambda]_,m_]:=Module[{mm=m,$\[Lambda] = \[Lambda]},
    Table[{ToString[Variable[k,i]]<>",Length@((FunctionsNeeded`TwistFactor`reGenDiagramList["<>ToString[$\[Lambda]]<>","<>ToString[mm]<>"])\[LeftDoubleBracket]"<>ToString[i+1]<>",1"<>StringPartGenerate[k,i-1]<>"\[RightDoubleBracket])"},{i,1,mm-1}]
];

RefinedFFactor[\[Lambda]_,m_,s_]:=ToExpression["Sum["<>reEvaluateblock[\[Lambda],m,s]<>","<>StringDrop[StringDrop[ToString[reIteratorGenerator[\[Lambda],m]],1],-1]<>"]"](dref[s,\[Lambda]])^(-1);

reFtrefoil[\[Lambda]_,r_,s_]:=(t/q)^(r s) (-A^2 q/t)^MoL@(\[Lambda]) (Product[q^(2arm[{i,j},\[Lambda]]) t^(-2leg[{i,j},\[Lambda]]),{j,Length[\[Lambda]]},{i,\[Lambda][[j]]}]);

RefinedTwFactor[\[Lambda]_,m_,r_,s_]:=If[m==-1,1,If[m==1, reFtrefoil[\[Lambda],r,s],If[m<0,(RefinedFFactor[\[Lambda],-m,s]/.{A->a^(-1),t->t^(-1),q-> q^(-1)}), (RefinedFFactor[\[Lambda],m,s]/.{A->a})(reFtrefoil[\[Lambda],r,s])]]]


End[]


(*HOMFLYPT-double-braid*)
Begin["`HOMFLYPT`"]

   d:=FunctionsNeeded`TwistFactor`d;
   UnrefinedTWFactor:=FunctionsNeeded`TwistFactor`UnrefinedTWFactor;
     Per := FunctionsNeeded`CommonDefinition`Per;
     arm := FunctionsNeeded`CommonDefinition`arm;
     leg := FunctionsNeeded`CommonDefinition`leg;
     coarm := FunctionsNeeded`CommonDefinition`coarm;
     coleg := FunctionsNeeded`CommonDefinition`coleg;
     MoL := FunctionsNeeded`CommonDefinition`MoL;
     bra := FunctionsNeeded`CommonDefinition`bra;
   ListL[r_,s_]:=Per[Table[r,s]];
   
   Conjugatee[\[Lambda]_]:=If[\[Lambda]=={},{},Table[Length[Select[\[Lambda],#>=i&]],{i,1,\[Lambda][[1]]}]];
   
   DoubleBraidPolynomial[r_,s_,m_,n_]:=(Sum[
    d[s,ListL[r,s][[kk]]] (d[r,Conjugatee[ListL[r,s][[kk]]]]/.{q->1/q})Product[
   bra[A q^(r+coarm[{i,j}]) q^(-coleg[{i,j}]) ]bra[A q^coarm[{i,j}] q^(-s-coleg[{i,j}])],{j,Length[ListL[r,s][[kk]]]},{i,ListL[r,s][[kk]][[j]]}]UnrefinedTWFactor[ListL[r,s][[kk]],m,s] UnrefinedTWFactor[ListL[r,s][[kk]],n,s]/UnrefinedTWFactor[ListL[r,s][[kk]],1,s],{kk,1,Length@ListL[r,s]}])


End[]


(*Poincare polynomial*)
Begin["`PoincarePolynomial`"]

     dref:=FunctionsNeeded`TwistFactor`dref;
     RefinedTwFactor:=FunctionsNeeded`TwistFactor`RefinedTwFactor;
     PerdZ := FunctionsNeeded`TwistFactor`PerdZ;
     arm := FunctionsNeeded`CommonDefinition`arm;
     leg := FunctionsNeeded`CommonDefinition`leg;
     coarm := FunctionsNeeded`CommonDefinition`coarm;
     coleg := FunctionsNeeded`CommonDefinition`coleg;
     MoL := FunctionsNeeded`CommonDefinition`MoL;
     bra := FunctionsNeeded`CommonDefinition`bra;
     reListL[r_,s_]:=PerdZ[Table[r,s]];
     
     Conjugatee[\[Lambda]_]:=If[\[Lambda]=={},{},Table[Length[Select[\[Lambda],#>=i&]],{i,1,\[Lambda][[1]]}]];
     
     DoubleBraidPolynomial[r_,s_,m_,n_]:=Sum[dref[s,reListL[r,s][[ww]]] (dref[r,Conjugatee[reListL[r,s][[ww]]]]/.{q->1/t,t->1/q})
     Product[bra[A q^(r+coarm[{i,j}]) t^(-coleg[{i,j}]) /\[Sigma]]bra[A q^coarm[{i,j}] t^(-s-coleg[{i,j}])\[Sigma]],{j,Length[reListL[r,s][[ww]]]},{i,reListL[r,s][[ww]][[j]]}] 
     (RefinedTwFactor[reListL[r,s][[ww]],m,r,s]/RefinedTwFactor[reListL[r,s][[ww]],-1,r,s] RefinedTwFactor[reListL[r,s][[ww]],n,r,s]/RefinedTwFactor[reListL[r,s][[ww]],1,r,s]),{ww,1,Length@reListL[r,s]}]/.{q->-tc,t->1/tr, A->a Sqrt[-tr tc],\[Sigma]-> tr^(-s) Q^(-1)};
  
         


End[]


EndPackage[]
