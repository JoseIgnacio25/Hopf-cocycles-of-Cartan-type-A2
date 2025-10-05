##################### Fix n and q ############################
n:=3;;
q:=E(n);;

##############################################################

LoadPackage("GBNP");
GBNP.ConfigPrint("X2","X12","X1");

############################ Field ################################
e2:=Indeterminate(Rationals, "e2");;
e1:=Indeterminate(Rationals, "e1");;
e12:=Indeterminate(Rationals, "e12");;
e112:=Indeterminate(Rationals, "e112");;
e122:=Indeterminate(Rationals, "e122");;
b221:=Indeterminate(Rationals, "b221");;#b122->x_2^2x_1
b211:=Indeterminate(Rationals, "b211");;#b211->x_2x_1^2
b212:=Indeterminate(Rationals, "b212");;#b212->x_2x_12
b121:=Indeterminate(Rationals, "b121");;#b121->x_12x_1
b221211:=Indeterminate(Rationals, "b221211");;#b221211->x_2^2x_12x_1^2
b121211:=Indeterminate(Rationals, "b121211");;#b121211->x_12^2x_1^2
b221212:=Indeterminate(Rationals, "b221212");;#b221212->x_2^2x_12^2
b212121:=Indeterminate(Rationals, "b212121");;#b212121->x_2x_12^2x_1
#
F:=Field(e2,e1,e12,e112,e122,b221,b211,b212,b121,b221211,b121211,b221212,b212121);;
F1:=One(F);;
u:=[[[]],[F1]];;
s:=-F1;;
zero:=[[],[]];;


########################## Generators ########################################
X2:=[[[1]],[1]];;
X12:=[[[2]],[1]];;
X1:=[[[3]],[1]];;

################### Braiding c(x_2^ax_{12}^bx_1^c,x_2^Ax_{12}^Bx_1^C) ###########################
braiding:=function(a,b,c,A,B,C);
return q^((a+2*b+c)*(A+2*B+C));
end;

#########################   DELTA CONSTRUCTION   #########################################

############## First, construct the gaussian C(a,b)_q #################
#Recall 1+q+...+q^{n-1}=0#
SumOfPowers:= function(t)
local i, sum;
sum := 0;
	for i in [0..t-1] do
 		sum := sum + q^i;
	od;
return sum;
end;

#Recall Prodt(n)=0#
Prodt := function(m)
local i, prod;
prod := 1;
	for i in [1..m] do
		prod := prod * SumOfPowers(i);
	od;
return prod;
end;

C := function (x , y)
return Prodt(x)/(Prodt(y)*Prodt(x-y));
end;

## Second, construct coefficients of coproduct for fixed q ##
Coef := function (a , j , b , k , l , c , m)
return C(a , j)*C(b , k)*C(k , l)*C(c , m)*q^((a-j)*l+m*(b-k))*(1-(q*q))^(k-l)*(q)^((a-j)*k+m*(b+a-j-l)+(k-l-1)*(k-l)/2);
end;


### Multiplier of generator function ###

LeftX1:=function(K,L,M)
local s, t, t1;
t1:=[[[]],[F1]];
t:=K-L+M;
	for s in [1..t] do
		t1:=MulNP(X1,t1);
	od;
return t1;
end;

LeftX2:=function(J)
local s, t2;
t2:=[[[]],[F1]];
	for s in [1..J] do
		t2:=MulNP(X2,t2);
	od;
return t2;
end;

LeftX12:=function(L)
local s, t12;
t12:=[[[]],[F1]];
	for s in [1..L] do
		t12:=MulNP(X12,t12);
	od;
return t12;
end;

CenterX1:=function(k,l,m,M)
local s, t, t1;
t1:=[[[]],[F1]];
t:=k-l+m-M;
	for s in [1..t] do
		t1:=MulNP(X1,t1);
	od;
return t1;
end;

CenterX2:=function(j,J,K,L)
local s, t, t2;
t2:=[[[]],[F1]];
t:=j-J+K-L;
	for s in [1..t] do
		t2:=MulNP(X2,t2);
	od;
return t2;
end;

CenterX12:=function(l,K)
local s, t, t12;
t12:=[[[]],[F1]];
t:=l-K;
	for s in [1..t] do
		t12:=MulNP(X12,t12);
	od;
return t12;
end;


RightX1:=function(c,m)
local s, t, t1;
t1:=[[[]],[F1]];
t:=c-m;
	for s in [1..t] do
		t1:=MulNP(X1,t1);
	od;
return t1;
end;

RightX2:=function(a,j,k,l)
local s, t, t2;
t2:=[[[]],[F1]];
t:=a-j+k-l;
	for s in [1..t] do
		t2:=MulNP(X2,t2);
	od;
return t2;
end;

RightX12:=function(b,k)
local s, t, t12;
t12:=[[[]],[F1]];
t:=b-k;
	for s in [1..t] do
		t12:=MulNP(X12,t12);
	od;
return t12;
end;

###### Ideal generators and Grobner basis for Nichols algebra with q12=q21=q ######
GBX:=function(n)
local i,j,l,r3,m1,m2,m12,m112,m122,L;
m2:=[[[]],[F1]];
m1:=[[[]],[F1]];
m12:=[[[]],[F1]];
r3:=AddNP(X12,AddNP(MulNP(X1,X2),MulNP(X2,X1),F1,-q*F1),F1,s);
for i in [1..n] do
		m2:=MulNP(X2,m2);
	od;
for j in [1..n] do
		m12:=MulNP(X12,m12);
	od;
for l in [1..n] do
		m1:=MulNP(X1,m1);
	od;
m112:=AddNP(MulNP(X1,X12),MulNP(X12,X1),F1,-q*q*F1);
m122:=AddNP(MulNP(X12,X2),MulNP(X2,X12),F1,-q*q*F1);
L:=[r3,m2,m12,m1,m112,m122];
return SGrobner(L);
end;

## Fix Grobner Basis for Nichols algebra ##
GX:= GBX(n);;



################### Hochschild cocycles ####################

######################### Definitions of coboundaries concentrated in degree 3 and concentrated in degree 6  #########################
##### Coboundary values ######
Cob:=function(b);
if b=[[[ ]],[1]] then return zero;
elif b=[[[1,3,3]],[1]] then return [[[]],[b211*s]];
elif b=[[[1,1,3]],[1]] then return [[[]],[b221*s]];
elif b=[[[1,2]],[1]] then return [[[]],[b212*s]];
elif b=[[[2,3]],[1]] then return [[[]],[b121*s]];
elif b=[[[1,1,2,3,3]],[1]] then return [[[]],[b221211*s]];
elif b=[[[2,2,3,3]],[1]] then return [[[]],[b121211*s]];
elif b=[[[1,1,2,2]],[1]] then return [[[]],[b221212*s]];
elif b=[[[1,2,2,3]],[1]] then return [[[]],[b212121*s]];
else return zero;
fi;
end;

###### Linearization of Cob #######
LCob:=function(v)
local L,t,j;
L:=zero;
t:=Length(v[1]);
for j in[1..t] do
	L:=AddNP(L,MulNP(Cob([[v[1][j]],[1]]),[[[]],[v[2][j]]]),F1,F1);
od;
return L;
end;


################# Definition of coboundary BX ########################
BX:=function(v,w);
if v[1]=[[ ]] or w[1]=[[ ]] then
return zero;
else return LCob(StrongNormalFormNP(MulNP(v,w),GX));
fi;
end;

############### Definition of cocycle Eta without coboundary ##########################
eta:=function(v,w);
if v[1]=[[ ]] or w[1]=[[ ]] then
return zero;
elif v=[[[1]],[1]] and w=[[[1,1]],[1]] then return [[[]],[e2*F1]];
elif v=[[[1,1]],[1]] and w=[[[1]],[1]] then return [[[]],[e2*F1]];
elif v=[[[3]],[1]] and w=[[[3,3]],[1]] then return [[[]],[e1*F1]];
elif v=[[[3,3]],[1]] and w=[[[3]],[1]] then return [[[]],[e1*F1]];
elif v=[[[2]],[1]] and w=[[[2,2]],[1]] then return [[[]],[e12*F1]];
elif v=[[[2,2]],[1]] and w=[[[2]],[1]] then return [[[]],[e12*F1]];
elif v=[[[3]],[1]] and w=[[[1,2,2]],[1]] then return [[[]],[e12*F1]];
elif v=[[[2,2,3]],[1]] and w=[[[1]],[1]] then return [[[]],[e12*F1]];
elif v=[[[2,3]],[1]] and w=[[[1,2]],[1]] then return [[[]],[e12*F1]];
elif v=[[[2,3,3]],[1]] and w=[[[1,1]],[1]] then return [[[]],[e12*s]];
elif v=[[[3,3]],[1]] and w=[[[1,1,2]],[1]] then return [[[]],[e12*s]];
elif v=[[[3,3]],[1]] and w=[[[1]],[1]] then return [[[]],[e112*F1]];
elif v=[[[3]],[1]] and w=[[[2]],[1]] then return [[[]],[e112*F1]];
elif v=[[[3]],[1]] and w=[[[1,1]],[1]] then return [[[]],[e122*F1]];
elif v=[[[2]],[1]] and w=[[[1]],[1]] then return [[[]],[e122*F1]];
else return zero;
fi;
end;




################# 1Conmmutation_left: eta(x,y_1z_1)eta(y_2,z_2) #################
1CLeft:=function(a1,b1,c1,a,b,c,A,B,C)
local j, k, l, m, J, K, L, M, D, p1, P1, p2, P2, O, R, T, V, t, v, u, w,T1,x,O1;
D:=zero;
	for j in [0..a] do 
	for k in [0..b] do
	for l in [0..k] do 
	for m in [0..c] do
	for J in [0..A] do
	for K in [0..B] do
	for L in [0..K] do
	for M in [0..C] do
			if (k-l+m in [0,1,2]) and (K-L+M in [0,1,2]) and (a-j+k-l in [0,1,2]) and (A-J+K-L in [0,1,2]) then
			x:=StrongNormalFormNP(MulNP(MulNP(LeftX2(a1),LeftX12(b1)),LeftX1(0,0,c1)),GX);
			p1:=StrongNormalFormNP(MulNP(MulNP(LeftX2(j),LeftX12(l)),LeftX1(k,l,m)),GX);
			P1:=StrongNormalFormNP(MulNP(MulNP(LeftX2(J),LeftX12(L)),LeftX1(K,L,M)),GX);
			p2:=StrongNormalFormNP(MulNP(MulNP(RightX2(a,j,k,l),RightX12(b,k)),RightX1(c,m)),GX);
			P2:=StrongNormalFormNP(MulNP(MulNP(RightX2(A,J,K,L),RightX12(B,K)),RightX1(C,M)),GX);
			t:=[p1[1],[1]];
			v:=[P1[1],[1]];
			u:=[p2[1],[1]];
			w:=[P2[1],[1]];
			T1:=MulNP(t,v);
			O1:=MulNP(p1,P1);
			T:=eta([x[1],[1]],T1);
			V:=eta(u,w);
			O:=BX(x,O1);
			R:=BX(p2,P2);
			D:=AddNP(D,MulNP(AddNP(T,O,F1,F1),AddNP(V,R,F1,F1)),F1,Coef(a , j , b , k , l , c , m)*Coef(A , J , B , K , L , C , M)*braiding(a-j+k-l,b-k,c-m,J,L,K-L+M));
			else D:=D;
			fi;
	od;
	od;
	od;
	od;
	od;
	od;
	od;
	od;
return D;
end;



################# 1Conmmutation_right: eta(y_1,z_1)eta(x,y_2z_2) #################
1CRight:=function(a1,b1,c1,a,b,c,A,B,C)
local j, k, l, m, J, K, L, M, D, p1, P1, p2, P2, O, R, T, V, t, v, u, w,T2,O2,x;
D:=zero;
	for j in [0..a] do 
	for k in [0..b] do
	for l in [0..k] do 
	for m in [0..c] do
	for J in [0..A] do
	for K in [0..B] do
	for L in [0..K] do
	for M in [0..C] do
			if (k-l+m in [0,1,2]) and (K-L+M in [0,1,2]) and (a-j+k-l in [0,1,2]) and (A-J+K-L in [0,1,2]) then
			x:=StrongNormalFormNP(MulNP(MulNP(LeftX2(a1),LeftX12(b1)),LeftX1(0,0,c1)),GX);
			p1:=StrongNormalFormNP(MulNP(MulNP(LeftX2(j),LeftX12(l)),LeftX1(k,l,m)),GX);
			P1:=StrongNormalFormNP(MulNP(MulNP(LeftX2(J),LeftX12(L)),LeftX1(K,L,M)),GX);
			p2:=StrongNormalFormNP(MulNP(MulNP(RightX2(a,j,k,l),RightX12(b,k)),RightX1(c,m)),GX);
			P2:=StrongNormalFormNP(MulNP(MulNP(RightX2(A,J,K,L),RightX12(B,K)),RightX1(C,M)),GX);
			t:=[p1[1],[1]];
			v:=[P1[1],[1]];
			u:=[p2[1],[1]];
			w:=[P2[1],[1]];
			T2:=MulNP(u,w);
			O2:=MulNP(p2,P2);
			T:=eta(t,v);
			V:=eta([x[1],[1]],T2);
			O:=BX(p1,P1);
			R:=BX(x,O2);
			D:=AddNP(D,MulNP(AddNP(T,O,F1,F1),AddNP(V,R,F1,F1)),F1,Coef(a , j , b , k , l , c , m)*Coef(A , J , B , K , L , C , M)*braiding(a-j+k-l,b-k,c-m,J,L,K-L+M));
			else D:=D;
			fi;
	od;
	od;
	od;
	od;
	od;
	od;
	od;
	od;
return D;
end;


1Comparison:=function(a1,b1,c1,a,b,c,A,B,C);
return AddNP(1CLeft(a1,b1,c1,a,b,c,A,B,C),1CRight(a1,b1,c1,a,b,c,A,B,C),F1,s);
end;



################# 2Conmmutation_left: eta(x_1y_1,z)eta(x_2,y_2) #################
2CLeft:=function(a1,b1,c1,a,b,c,A,B,C)
local j, k, l, m, J, K, L, M, D, p1, P1, p2, P2, O, R, T, V, t, v, u, w,T1,x,O1;
D:=zero;
	for j in [0..a] do 
	for k in [0..b] do
	for l in [0..k] do 
	for m in [0..c] do
	for J in [0..A] do
	for K in [0..B] do
	for L in [0..K] do
	for M in [0..C] do
			if (k-l+m in [0,1,2]) and (K-L+M in [0,1,2]) and (a-j+k-l in [0,1,2]) and (A-J+K-L in [0,1,2]) then
			x:=StrongNormalFormNP(MulNP(MulNP(LeftX2(a1),LeftX12(b1)),LeftX1(0,0,c1)),GX);
			p1:=StrongNormalFormNP(MulNP(MulNP(LeftX2(j),LeftX12(l)),LeftX1(k,l,m)),GX);
			P1:=StrongNormalFormNP(MulNP(MulNP(LeftX2(J),LeftX12(L)),LeftX1(K,L,M)),GX);
			p2:=StrongNormalFormNP(MulNP(MulNP(RightX2(a,j,k,l),RightX12(b,k)),RightX1(c,m)),GX);
			P2:=StrongNormalFormNP(MulNP(MulNP(RightX2(A,J,K,L),RightX12(B,K)),RightX1(C,M)),GX);
			t:=[p1[1],[1]];
			v:=[P1[1],[1]];
			u:=[p2[1],[1]];
			w:=[P2[1],[1]];
			T1:=MulNP(t,v);
			O1:=MulNP(p1,P1);
			T:=eta(T1,[x[1],[1]]);
			V:=eta(u,w);
			O:=BX(O1,x);
			R:=BX(p2,P2);
			D:=AddNP(D,MulNP(AddNP(T,O,F1,F1),AddNP(V,R,F1,F1)),F1,Coef(a , j , b , k , l , c , m)*Coef(A , J , B , K , L , C , M)*braiding(a-j+k-l,b-k,c-m,J,L,K-L+M));
			else D:=D;
			fi;
	od;
	od;
	od;
	od;
	od;
	od;
	od;
	od;
return D;
end;



################# 2Conmmutation_right: eta(x_1,y_1)eta(x_2y_2,z) #################
2CRight:=function(a1,b1,c1,a,b,c,A,B,C)
local j, k, l, m, J, K, L, M, D, p1, P1, p2, P2, O, R, T, V, t, v, u, w,T2,O2,x;
D:=zero;
	for j in [0..a] do 
	for k in [0..b] do
	for l in [0..k] do 
	for m in [0..c] do
	for J in [0..A] do
	for K in [0..B] do
	for L in [0..K] do
	for M in [0..C] do
			if (k-l+m in [0,1,2]) and (K-L+M in [0,1,2]) and (a-j+k-l in [0,1,2]) and (A-J+K-L in [0,1,2]) then
			x:=StrongNormalFormNP(MulNP(MulNP(LeftX2(a1),LeftX12(b1)),LeftX1(0,0,c1)),GX);
			p1:=StrongNormalFormNP(MulNP(MulNP(LeftX2(j),LeftX12(l)),LeftX1(k,l,m)),GX);
			P1:=StrongNormalFormNP(MulNP(MulNP(LeftX2(J),LeftX12(L)),LeftX1(K,L,M)),GX);
			p2:=StrongNormalFormNP(MulNP(MulNP(RightX2(a,j,k,l),RightX12(b,k)),RightX1(c,m)),GX);
			P2:=StrongNormalFormNP(MulNP(MulNP(RightX2(A,J,K,L),RightX12(B,K)),RightX1(C,M)),GX);
			t:=[p1[1],[1]];
			v:=[P1[1],[1]];
			u:=[p2[1],[1]];
			w:=[P2[1],[1]];
			T2:=MulNP(u,w);
			O2:=MulNP(p2,P2);
			T:=eta(t,v);
			V:=eta(T2,[x[1],[1]]);
			O:=BX(p1,P1);
			R:=BX(O2,x);
			D:=AddNP(D,MulNP(AddNP(T,O,F1,F1),AddNP(V,R,F1,F1)),F1,Coef(a , j , b , k , l , c , m)*Coef(A , J , B , K , L , C , M)*braiding(a-j+k-l,b-k,c-m,J,L,K-L+M));
			else D:=D;
			fi;
	od;
	od;
	od;
	od;
	od;
	od;
	od;
	od;
return D;
end;

2Comparison:=function(a1,b1,c1,a,b,c,A,B,C);
return AddNP(2CLeft(a1,b1,c1,a,b,c,A,B,C),2CRight(a1,b1,c1,a,b,c,A,B,C),F1,s);
end;