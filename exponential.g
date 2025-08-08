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

################### Hochschild and Exponential ####################

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

############## Consider the Hochschild cocycle Et = eta + BX ###############

################# Definition Et*Et, where * is the convolution product #################
Et2:=function(a,b,c,A,B,C)
local j, k, l, m, J, K, L, M, D, p1, P1, p2, P2, O, R, T, V, t, v, u, w;
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
			p1:=StrongNormalFormNP(MulNP(MulNP(LeftX2(j),LeftX12(l)),LeftX1(k,l,m)),GX);
			P1:=StrongNormalFormNP(MulNP(MulNP(LeftX2(J),LeftX12(L)),LeftX1(K,L,M)),GX);
			p2:=StrongNormalFormNP(MulNP(MulNP(RightX2(a,j,k,l),RightX12(b,k)),RightX1(c,m)),GX);
			P2:=StrongNormalFormNP(MulNP(MulNP(RightX2(A,J,K,L),RightX12(B,K)),RightX1(C,M)),GX);
			t:=[p1[1],[1]];
			v:=[P1[1],[1]];
			u:=[p2[1],[1]];
			w:=[P2[1],[1]];
			T:=eta(t,v);
			V:=eta(u,w);
			O:=BX(p1,P1);
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

################# Definition Et*Et*Et, where * is the convolution product #################
Et3:=function(a,b,c,A,B,C)
local j, k, l, m, jj, kk, ll, mm, J, K, L, M, JJ, KK, LL, MM, D, p1, P1, p2, P2, p3, P3, T, V, U, t, v, tt, vv, ttt, vvv, oO, pP, rR, S;
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
				p1:=StrongNormalFormNP(MulNP(MulNP(LeftX2(jj),LeftX12(ll)),LeftX1(kk,ll,mm)),GX);
				P1:=StrongNormalFormNP(MulNP(MulNP(LeftX2(JJ),LeftX12(LL)),LeftX1(KK,LL,MM)),GX);
				p2:=StrongNormalFormNP(MulNP(MulNP(CenterX2(j,jj,kk,ll),CenterX12(l,kk)),CenterX1(k,l,m,mm)),GX);
				P2:=StrongNormalFormNP(MulNP(MulNP(CenterX2(J,JJ,KK,LL),CenterX12(L,KK)),CenterX1(K,L,M,MM)),GX);
				p3:=StrongNormalFormNP(MulNP(MulNP(RightX2(a,j,k,l),RightX12(b,k)),RightX1(c,m)),GX);
				P3:=StrongNormalFormNP(MulNP(MulNP(RightX2(A,J,K,L),RightX12(B,K)),RightX1(C,M)),GX);
				t:=[p1[1],[1]];
				v:=[P1[1],[1]];
				tt:=[p2[1],[1]];
				vv:=[P2[1],[1]];
				ttt:=[p3[1],[1]];
				vvv:=[P3[1],[1]];
				T:=eta(t,v);
				V:=eta(tt,vv);
				U:=eta(ttt,vvv);
				oO:=BX(p1,P1);
				pP:=BX(p2,P2);
				rR:=BX(p3,P3);
				S:=Coef(j , jj , l , kk , ll , k-l+m , mm)*Coef(J , JJ , L , KK , LL , K-L+M , MM)*Coef(a , j , b , k , l , c , m)*braiding(a-j+k-l,b-k,c-m,J,L,K-L+M)*Coef(A , J , B , K , L , C , M)*braiding(j-jj+kk-ll,l-kk,k-l+m-mm,JJ,LL,KK-LL+MM);
				D:=AddNP(D,MulNP(AddNP(T,oO,F1,F1),MulNP(AddNP(V,pP,F1,F1),AddNP(U,rR,F1,F1))),F1,S);
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

################# Definition Et*Et*Et*Et, where * is the convolution product #################
Et4:=function(a,b,c,A,B,C)
local j, k, l, m, jj, kk, ll, mm, jjj, kkk, lll, mmm, J, K, L, M, JJ, KK, LL, MM, JJJ, KKK, LLL, MMM, D, p1, P1, p2, P2, p3, P3, p4, P4, T, V, U, t, v, tt, vv, ttt, vvv, tttt, vvvv, T1, T2, T3, T4, O1, O2, O3, O4, S;
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
			for jjj in [0..jj] do
			for kkk in [0..ll] do
			for lll in [0..kkk] do
			for mmm in [0..kk-ll+mm] do
			for JJJ in [0..JJ] do
			for KKK in [0..LL] do
			for LLL in [0..KKK] do
			for MMM in [0..KK-LL+MM] do
				if (k-l+m in [0,1,2]) and (K-L+M in [0,1,2]) and (a-j+k-l in [0,1,2]) and (A-J+K-L in [0,1,2]) and (kk-ll+mm in [0,1,2]) and (KK-LL+MM in [0,1,2]) and (j-jj+kk-ll in [0,1,2]) and (J-JJ+KK-LL in [0,1,2]) and (kkk-lll+mmm in [0,1,2]) and (KKK-LLL+MMM in [0,1,2]) and (jj-jjj+kkk-lll in [0,1,2]) and (JJ-JJJ+KKK-LLL in [0,1,2]) then
				p1:=StrongNormalFormNP(MulNP(MulNP(LeftX2(jjj),LeftX12(lll)),LeftX1(kkk,lll,mmm)),GX);
				P1:=StrongNormalFormNP(MulNP(MulNP(LeftX2(JJJ),LeftX12(LLL)),LeftX1(KKK,LLL,MMM)),GX);
				p2:=StrongNormalFormNP(MulNP(MulNP(CenterX2(jj,jjj,kkk,lll),CenterX12(ll,kkk)),CenterX1(kk,ll,mm,mmm)),GX);
				P2:=StrongNormalFormNP(MulNP(MulNP(CenterX2(JJ,JJJ,KKK,LLL),CenterX12(LL,KKK)),CenterX1(KK,LL,MM,MMM)),GX);
				p3:=StrongNormalFormNP(MulNP(MulNP(CenterX2(j,jj,kk,ll),CenterX12(l,kk)),CenterX1(k,l,m,mm)),GX);
				P3:=StrongNormalFormNP(MulNP(MulNP(CenterX2(J,JJ,KK,LL),CenterX12(L,KK)),CenterX1(K,L,M,MM)),GX);
				p4:=StrongNormalFormNP(MulNP(MulNP(RightX2(a,j,k,l),RightX12(b,k)),RightX1(c,m)),GX);
				P4:=StrongNormalFormNP(MulNP(MulNP(RightX2(A,J,K,L),RightX12(B,K)),RightX1(C,M)),GX);
				t:=[p1[1],[1]];
				v:=[P1[1],[1]];
				tt:=[p2[1],[1]];
				vv:=[P2[1],[1]];
				ttt:=[p3[1],[1]];
				vvv:=[P3[1],[1]];
				tttt:=[p4[1],[1]];
				vvvv:=[P4[1],[1]];
				T1:=eta(t,v);
				T2:=eta(tt,vv);
				T3:=eta(ttt,vvv);
				T4:=eta(tttt,vvvv);
				O1:=BX(p1,P1);
				O2:=BX(p2,P2);
				O3:=BX(p3,P3);
				O4:=BX(p4,P4);
				S:=Coef(jj , jjj , ll , kkk , lll , kk-ll+mm , mmm)*Coef(JJ , JJJ , LL , KKK , LLL , KK-LL+MM , MMM)*Coef(j , jj , l , kk , ll , k-l+m , mm)*Coef(J , JJ , L , KK , LL , K-L+M , MM)*Coef(a , j , b , k , l , c , m)*braiding(a-j+k-l,b-k,c-m,J,L,K-L+M)*Coef(A , J , B , K , L , C , M)*braiding(j-jj+kk-ll,l-kk,k-l+m-mm,JJ,LL,KK-LL+MM)*braiding(jj-jjj+kkk-lll,ll-kkk,kk-ll+mm-mmm,JJJ,LLL,KKK-LLL+MMM);
				D:=AddNP(D,MulNP(AddNP(T1,O1,F1,F1),MulNP(AddNP(T2,O2,F1,F1),MulNP(AddNP(T3,O3,F1,F1),AddNP(T4,O4,F1,F1)))),F1,S);
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

################# Definition Et*Et*Et*Et*Et, where * is the convolution product #################
Et5:=function(a,b,c,A,B,C)
local j, k, l, m, jj, kk, ll, mm, jjj, kkk, lll, mmm, jjjj, kkkk, llll, mmmm, J, K, L, M, JJ, KK, LL, MM, JJJ, KKK, LLL, MMM, JJJJ, KKKK, LLLL, MMMM, D, p1, P1, p2, P2, p3, P3, p4, P4, p5, P5, t, v, tt, vv, ttt, vvv, tttt, vvvv, ttttt, vvvvv, T1, T2, T3, T4, T5, O1, O2, O3, O4, O5, S;
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
		for jjj in [0..jj] do
		for kkk in [0..ll] do
		for lll in [0..kkk] do
		for mmm in [0..kk-ll+mm] do
		for JJJ in [0..JJ] do
		for KKK in [0..LL] do
		for LLL in [0..KKK] do
		for MMM in [0..KK-LL+MM] do
			for jjjj in [0..jjj] do
			for kkkk in [0..lll] do
			for llll in [0..kkkk] do
			for mmmm in [0..kkk-lll+mmm] do
			for JJJJ in [0..JJJ] do
			for KKKK in [0..LLL] do
			for LLLL in [0..KKKK] do
			for MMMM in [0..KKK-LLL+MMM] do
				if (k-l+m in [0,1,2]) and (K-L+M in [0,1,2]) and (a-j+k-l in [0,1,2]) and (A-J+K-L in [0,1,2]) and (kk-ll+mm in [0,1,2]) and (KK-LL+MM in [0,1,2]) and (j-jj+kk-ll in [0,1,2]) and (J-JJ+KK-LL in [0,1,2]) and (kkk-lll+mmm in [0,1,2]) and (KKK-LLL+MMM in [0,1,2]) and (jj-jjj+kkk-lll in [0,1,2]) and (JJ-JJJ+KKK-LLL in [0,1,2]) and (kkkk-llll+mmmm in [0,1,2]) and (KKKK-LLLL+MMMM in [0,1,2]) and (jjj-jjjj+kkkk-llll in [0,1,2]) and (JJJ-JJJJ+KKKK-LLLL in [0,1,2]) then
				p1:=StrongNormalFormNP(MulNP(MulNP(LeftX2(jjjj),LeftX12(llll)),LeftX1(kkkk,llll,mmmm)),GX);
				P1:=StrongNormalFormNP(MulNP(MulNP(LeftX2(JJJJ),LeftX12(LLLL)),LeftX1(KKKK,LLLL,MMMM)),GX);
				p2:=StrongNormalFormNP(MulNP(MulNP(CenterX2(jjj,jjjj,kkkk,llll),CenterX12(lll,kkkk)),CenterX1(kkk,lll,mmm,mmmm)),GX);
				P2:=StrongNormalFormNP(MulNP(MulNP(CenterX2(JJJ,JJJJ,KKKK,LLLL),CenterX12(LLL,KKKK)),CenterX1(KKK,LLL,MMM,MMMM)),GX);
				p3:=StrongNormalFormNP(MulNP(MulNP(CenterX2(jj,jjj,kkk,lll),CenterX12(ll,kkk)),CenterX1(kk,ll,mm,mmm)),GX);
				P3:=StrongNormalFormNP(MulNP(MulNP(CenterX2(JJ,JJJ,KKK,LLL),CenterX12(LL,KKK)),CenterX1(KK,LL,MM,MMM)),GX);
				p4:=StrongNormalFormNP(MulNP(MulNP(CenterX2(j,jj,kk,ll),CenterX12(l,kk)),CenterX1(k,l,m,mm)),GX);
				P4:=StrongNormalFormNP(MulNP(MulNP(CenterX2(J,JJ,KK,LL),CenterX12(L,KK)),CenterX1(K,L,M,MM)),GX);
				p5:=StrongNormalFormNP(MulNP(MulNP(RightX2(a,j,k,l),RightX12(b,k)),RightX1(c,m)),GX);
				P5:=StrongNormalFormNP(MulNP(MulNP(RightX2(A,J,K,L),RightX12(B,K)),RightX1(C,M)),GX);
				t:=[p1[1],[1]];
				v:=[P1[1],[1]];
				tt:=[p2[1],[1]];
				vv:=[P2[1],[1]];
				ttt:=[p3[1],[1]];
				vvv:=[P3[1],[1]];
				tttt:=[p4[1],[1]];
				vvvv:=[P4[1],[1]];
				ttttt:=[p5[1],[1]];
				vvvvv:=[P5[1],[1]];
				T1:=eta(t,v);
				T2:=eta(tt,vv);
				T3:=eta(ttt,vvv);
				T4:=eta(tttt,vvvv);
				T5:=eta(ttttt,vvvvv);
				O1:=BX(p1,P1);
				O2:=BX(p2,P2);
				O3:=BX(p3,P3);
				O4:=BX(p4,P4);
				O5:=BX(p5,P5);
				S:=Coef(jjj, jjjj, lll, kkkk, llll, kkk-lll+mmm, mmmm)*Coef(JJJ, JJJJ, LLL, KKKK, LLLL, KKK-LLL+MMM , MMMM)*Coef(jj , jjj , ll , kkk , lll , kk-ll+mm , mmm)*Coef(JJ , JJJ , LL , KKK , LLL , KK-LL+MM , MMM)*Coef(j , jj , l , kk , ll , k-l+m , mm)*Coef(J , JJ , L , KK , LL , K-L+M , MM)*Coef(a , j , b , k , l , c , m)*braiding(a-j+k-l,b-k,c-m,J,L,K-L+M)*Coef(A , J , B , K , L , C , M)*braiding(j-jj+kk-ll,l-kk,k-l+m-mm,JJ,LL,KK-LL+MM)*braiding(jj-jjj+kkk-lll,ll-kkk,kk-ll+mm-mmm,JJJ,LLL,KKK-LLL+MMM)*braiding(jjj-jjjj+kkkk-llll,lll-kkkk,kkk-lll+mmm-mmmm,JJJJ,LLLL,KKKK-LLLL+MMMM);
				D:=AddNP(D,MulNP(AddNP(T1,O1,F1,F1),MulNP(AddNP(T2,O2,F1,F1),MulNP(AddNP(T3,O3,F1,F1),MulNP(AddNP(T4,O4,F1,F1),AddNP(T5,O5,F1,F1))))),F1,S);
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

################# Values of the exponencial ###################### 

################# truncated exponential up to 2 t###################### 
exponential2:=function(a,b,c,A,B,C)
local e, w, p, u, D, t, v;
if (a=0) and (b=0) and (c=0) and (A=0) and (B=0) and (C=0) then
return [[[]],[F1]];
fi;
D:=zero; 
p:=StrongNormalFormNP(MulNP(MulNP(LeftX2(a),LeftX12(b)),LeftX1(0,0,c)),GX);
u:=StrongNormalFormNP(MulNP(MulNP(LeftX2(A),LeftX12(B)),LeftX1(0,0,C)),GX);
t:=[p[1],[1]];
v:=[u[1],[1]];
e:=AddNP(eta(t,v),BX(p,u),F1,F1);
w:=Et2(a,b,c,A,B,C);
D:=AddNP(D,AddNP(e,w,F1,F1/2),F1,F1);
return D;
end;

################# truncated exponential up to 3 ###################### 
exponential3:=function(a,b,c,A,B,C)
local e, w, p, u, D, t, v, r;
if (a=0) and (b=0) and (c=0) and (A=0) and (B=0) and (C=0) then
return [[[]],[F1]];
fi;
D:=zero;
p:=StrongNormalFormNP(MulNP(MulNP(LeftX2(a),LeftX12(b)),LeftX1(0,0,c)),GX);
u:=StrongNormalFormNP(MulNP(MulNP(LeftX2(A),LeftX12(B)),LeftX1(0,0,C)),GX);
t:=[p[1],[1]];
v:=[u[1],[1]];
e:=AddNP(eta(t,v),BX(p,u),F1,F1);
w:=Et2(a,b,c,A,B,C);
r:=Et3(a,b,c,A,B,C);
D:=AddNP(D,AddNP(AddNP(e,w,F1,F1/2),r,F1,F1/6),F1,F1);
return D;
end;

################# truncated exponential up to 4 ###################### 
exponential4:=function(a,b,c,A,B,C)
local e, w, p, u, D, t, v, r, s;
if (a=0) and (b=0) and (c=0) and (A=0) and (B=0) and (C=0) then
return [[[]],[F1]];
fi;
D:=zero;
p:=StrongNormalFormNP(MulNP(MulNP(LeftX2(a),LeftX12(b)),LeftX1(0,0,c)),GX);
u:=StrongNormalFormNP(MulNP(MulNP(LeftX2(A),LeftX12(B)),LeftX1(0,0,C)),GX);
t:=[p[1],[1]];
v:=[u[1],[1]];
e:=AddNP(eta(t,v),BX(p,u),F1,F1);
w:=Et2(a,b,c,A,B,C);
r:=Et3(a,b,c,A,B,C);
s:=Et4(a,b,c,A,B,C);
D:=AddNP(D,AddNP(AddNP(AddNP(e,w,F1,F1/2),r,F1,F1/6),s,F1,F1/24),F1,F1);
return D;
end;

################# truncated exponential up to 5 ######################
exponential:=function(a,b,c,A,B,C)
local e, w, p, u, D, t, v, r, s,j;
if (a=0) and (b=0) and (c=0) and (A=0) and (B=0) and (C=0) then
return [[[]],[F1]];
fi;
D:=zero;
p:=StrongNormalFormNP(MulNP(MulNP(LeftX2(a),LeftX12(b)),LeftX1(0,0,c)),GX);
u:=StrongNormalFormNP(MulNP(MulNP(LeftX2(A),LeftX12(B)),LeftX1(0,0,C)),GX);
t:=[p[1],[1]];
v:=[u[1],[1]];
e:=AddNP(eta(t,v),BX(p,u),F1,F1);
w:=Et2(a,b,c,A,B,C);
r:=Et3(a,b,c,A,B,C);
s:=Et4(a,b,c,A,B,C);
j:=Et5(a,b,c,A,B,C);
D:=AddNP(D,AddNP(AddNP(AddNP(AddNP(e,w,F1,F1/2),r,F1,F1/6),s,F1,F1/24),j,F1,1/120),F1,F1);
return D;
end;
