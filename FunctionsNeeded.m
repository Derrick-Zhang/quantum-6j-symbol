(* ::Package:: *)

BeginPackage["FunctionsNeeded`"]

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
EndPackage[];
