##################### Fix n and q ############################
n:=3;;
q:=E(n);;
############################################################
LoadPackage("GBNP");
GBNP.ConfigPrint("X2","X12","X1");

############################ Field ################################
l2:=Indeterminate(Rationals, "l2");;
l1:=Indeterminate(Rationals, "l1");;
l12:=Indeterminate(Rationals, "l12");;
l112:=Indeterminate(Rationals, "l112");;
l122:=Indeterminate(Rationals, "l122");;
a221:=Indeterminate(Rationals, "a221");;#a122->x_2^2x_1
a211:=Indeterminate(Rationals, "a211");;#a211->x_2x_1^2
a212:=Indeterminate(Rationals, "a212");;#a212->x_2x_12
a121:=Indeterminate(Rationals, "a121");;#a121->x_12x_1
a221211:=Indeterminate(Rationals, "a221211");;#a122->x_2^2x_12x_1^2
a121211:=Indeterminate(Rationals, "a121211");;#a122->x_12^2x_1^2
a221212:=Indeterminate(Rationals, "a221212");;#a122->x_2^2x_12^2
a212121:=Indeterminate(Rationals, "a212121");;#a122->x_2x_12^2x_1
#
F:=Field(l2,l1,l12,l112,l122,a221,a211,a212,a121,a221211,a121211,a221212,a212121);;
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

############## First construct the gaussian C(a,b)_q #################
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

## Second construct coefficients of coproduct for fixed q ##
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

###### Ideal generators and Grobner basis for Cleft Object with q12=q21=q  ######
EGBY:=function(n)
local i,j,l,k,m1,m2,m12,r3,m112,m122,L;
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
L:=[AddNP(m2,u,F1,l2*s),AddNP(m12,u,F1,l12*s),AddNP(m1,u,F1,l1*s),r3,AddNP(m112,u,F1,l112*s),AddNP(m122,u,F1,l122*s)];
return SGrobner(L);
end;

## Fix Grobner Basis for Cleft Object ##
GY:= EGBY(n);;

############### Definition of alpha (on the basis) #######################
Alp:=function(b);
if b=[[[ ]],[1]] then return b;
elif b=[[[1,3,3]],[1]] then return [[[]],[a211*F1]];
elif b=[[[1,1,3]],[1]] then return [[[]],[a221*F1]];
elif b=[[[1,2]],[1]] then return [[[]],[a212*F1]];
elif b=[[[2,3]],[1]] then return [[[]],[a121*F1]];
elif b=[[[1,1,2,3,3]],[1]] then return [[[]],[a221211*F1]];
elif b=[[[2,2,3,3]],[1]] then return [[[]],[a121211*F1]];
elif b=[[[1,1,2,2]],[1]] then return [[[]],[a221212*F1]];
elif b=[[[1,2,2,3]],[1]] then return [[[]],[a212121*F1]];
else return zero;
fi;
end;

############### Definition of Beta=alpha^{-1} (on the basis) #######################
Bet:=function(b);
if b=[[[ ]],[1]] then return b;
elif b=[[[1,3,3]],[1]] then return [[[]],[a211*s]];
elif b=[[[1,1,3]],[1]] then return [[[]],[a221*s]];
elif b=[[[1,2]],[1]] then return [[[]],[a212*s]];
elif b=[[[2,3]],[1]] then return [[[]],[a121*s]];
elif b=[[[1,1,2,3,3]],[1]] then return [[[]],[a221211*s + (q-q^2)*a221*a211*F1+a221*a121*F1+a211*a212*F1]];
elif b=[[[2,2,3,3]],[1]] then return [[[]],[a121211*s+(q-q^2)*a121*a211*F1+a121^2*F1]];
elif b=[[[1,1,2,2]],[1]] then return [[[]],[a221212*s+(q-q^2)*a221*a212*F1+a212^2*F1]];
elif b=[[[1,2,2,3]],[1]] then return [[[]],[a212121*s-3*a221*a211*F1+(q-q^2)*a221*a121*F1+(q-q^2)*a211*a212*F1+a212*a121*F1]];
else return zero;
fi;
end;

###### Linearization of alpha^{-1}=Beta #######
LBet:=function(v)
local L,t,j;
L:=zero;
t:=Length(v[1]);
for j in[1..t] do
	L:=AddNP(L,MulNP(Bet([[v[1][j]],[1]]),[[[]],[v[2][j]]]),F1,F1);
od;
return L;
end;


##### The section Gamma #######
gamma:=function(b);
if b=[ [ [ 2, 2 ] ], [ 1 ] ] then return StrongNormalFormNP(AddNP(b,[[[1]],[1]],F1,s*(-q+q^2)*l112),GY);
elif b=[ [ [ 1, 2, 2 ] ], [ 1 ] ] then return StrongNormalFormNP(AddNP(b,[[[1,1]],[1]],F1,s*(-q+q^2)*l112),GY);
elif b=[ [ [ 2, 3, 3 ] ], [ 1 ] ] then return StrongNormalFormNP(AddNP(b,[[[1]],[1]],F1,s*(-q+q^2)*l1),GY);
elif b=[ [ [ 1, 2, 3, 3 ] ], [ 1 ] ] then return StrongNormalFormNP(AddNP(b,[[[1,1]],[1]],F1,s*(-E(3)+E(3)^2)*l1),GY);
elif b=[ [ [ 2, 2, 3 ] ], [ 1 ] ] then return StrongNormalFormNP(AddNP(b,AddNP([[[1,3]],[1]],[[[1,1]],[1]],s*(-q+q^2)*l112,3*q^2*l1*F1),F1,F1),GY);
elif b=[ [ [ 1, 2, 2, 3 ] ], [ 1 ] ] then return StrongNormalFormNP(AddNP(b,[[[1,1,3]],[1]],F1,s*(-q+q^2)*l112),GY);
elif b=[ [ [ 2, 2, 3, 3 ] ], [ 1 ] ] then return StrongNormalFormNP(AddNP(AddNP(b,[[[1,2]],[1]],F1,(q-q^2)*l1*s),AddNP([[[1,3,3]],[1]],[[[1,1,3]],[1]],(-q+q^2)*l112*s,3*q*l1*s),F1,F1),GY);
elif b=[ [ [ 1, 2, 2, 3, 3 ] ], [ 1 ] ] then return StrongNormalFormNP(AddNP(AddNP(b,[[[1,1,2]],[1]],F1,(q-q^2)*l1*s),[[[1,1,3,3]],[1]],F1,(-q+q^2)*l112*s),GY);
else return StrongNormalFormNP(b,GY);
fi;
end;


##### The associated cocycle Sigma #######
sigma:=function(a,b)
local i, L, t;
L:=zero;
t:=StrongNormalFormNP(MulNP(gamma(a),gamma(b)),GY);
for i in [1..Length(t[1])] do
if t[1][i]<>[] then continue; 
else L:=AddNP(L, [[[]],[t[2][i]]],F1,F1);
fi;
od;
return L;
end;
 

################# Definition alpha-->sigma(x_2^ax_{12}^bx_1^c,x_2^ex_{12}^fx_1^g), alpha acting on sigma #################
osigma:=function(a,b,c,A,B,C)
local j, k, l, m, jj, kk, ll, mm, J, K, L, M, JJ, KK, LL, MM, D, o, O, p, P, r, R, T,V,oO;
D:=zero;
	for j in [0..a] do 
	for k in [0..b] do
	for l in [0..k] do 
	for m in [0..c] do
	for J in [0..A] do
	for K in [0..B] do
	for L in [0..K] do
	for M in [0..C] do
			for jj in [0..j] do 
			for kk in [0..l] do
			for ll in [0..kk] do 
			for mm in [0..k-l+m] do
			for JJ in [0..J] do
			for KK in [0..L] do
			for LL in [0..KK] do
			for MM in [0..K-L+M] do
				if (k-l+m in [0,1,2]) and (K-L+M in [0,1,2]) and (a-j+k-l in [0,1,2]) and (A-J+K-L in [0,1,2]) and (kk-ll+mm in [0,1,2]) and (KK-LL+MM in [0,1,2]) and (j-jj+kk-ll in [0,1,2]) and (J-JJ+KK-LL in [0,1,2]) then
				o:=MulNP(StrongNormalFormNP(MulNP(MulNP(LeftX2(jj),LeftX12(ll)),LeftX1(kk,ll,mm)),GX),[[[]],[Coef(j , jj , l , kk , ll , k-l+m , mm)*F1]]);
				O:=MulNP(StrongNormalFormNP(MulNP(MulNP(LeftX2(JJ),LeftX12(LL)),LeftX1(KK,LL,MM)),GX),[[[]],[Coef(J , JJ , L , KK , LL , K-L+M , MM)*F1]]);
				p:=StrongNormalFormNP(MulNP(MulNP(CenterX2(j,jj,kk,ll),CenterX12(l,kk)),CenterX1(k,l,m,mm)),GX);
				P:=StrongNormalFormNP(MulNP(MulNP(CenterX2(J,JJ,KK,LL),CenterX12(L,KK)),CenterX1(K,L,M,MM)),GX);
				r:=StrongNormalFormNP(MulNP(MulNP(RightX2(a,j,k,l),RightX12(b,k)),RightX1(c,m)),GX);
				R:=StrongNormalFormNP(MulNP(MulNP(RightX2(A,J,K,L),RightX12(B,K)),RightX1(C,M)),GX);	
				T:=MulNP(sigma([p[1],[1]],[P[1],[1]]),[[[]],[Coef(a , j , b , k , l , c , m)*Coef(A , J , B , K , L , C , M)*braiding(a-j+k-l,b-k,c-m,J,L,K-L+M)*braiding(j-jj+kk-ll,l-kk,k-l+m-mm,JJ,LL,KK-LL+MM)]]);
				oO:=MulNP(MulNP(Alp([o[1],[1]]),Alp([O[1],[1]])),[[[]],[Coef(j , jj , l , kk , ll , k-l+m , mm)*Coef(J , JJ , L , KK , LL , K-L+M , MM)]]);
				V:=LBet(StrongNormalFormNP(MulNP(r,R),GX));
				D:=AddNP(D,MulNP(MulNP(oO,T),V),F1,F1);
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