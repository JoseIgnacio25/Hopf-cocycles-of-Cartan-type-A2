##################### Fix n and q  ############################
n:=3;;
q:=E(n);;
###############################################################

LoadPackage("GBNP");
GBNP.ConfigPrint("X2","X12","X1");

##################### Field ################################
l2:=Indeterminate(Rationals, "l2");;
l1:=Indeterminate(Rationals, "l1");;
l12:=Indeterminate(Rationals, "l12");;
q12:=Indeterminate(Rationals, "q12");;

F:=Field(l2,l1,l12,q12);;
F1:=One(F);;
u:=[[[]],[F1]];;
s:=-F1;;
zero:=[[],[]];;

########################## Generators ########################################
X2:=[[[1]],[1]];;
X12:=[[[2]],[1]];;
X1:=[[[3]],[1]];;

#########################   Coefficient in coproduct CONSTRUCTION   #########################

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

############## Second construct coefficients of coproduct for fixed q ##############
Coef := function (a , j , b , k , l , c , m)
return C(a , j)*C(b , k)*C(k , l)*C(c , m)*(1-q^-1)^(k-l)*(q*q12)^((-1)*((a-j)*(k+m)+m*(b-l)+(k-l-1)*(k-l)/2))*q^((a-j)*l+m*(b-k));
end;

#########################   Caracteristic functions   #########################

D:=function(t);
if t in [0,n,2*n] then return F1;
else return 0;
fi;
end;

d:=function(t)
if t in [0,n] then return F1;
else return 0;
fi;
end;

exponent_D:=function(t);
if t=n then return 1;
elif t=2*n then return 2;
else return 0;
fi;
end;

exponent_d:=function(t);
if t=n then return 1;
else return 0;
fi;
end;

#########################   Caracteristic sigma function   #########################
sigma1:=function(n2,n12,n1,s,m2,m12,m1)
local k;
k:=C(n1,s)*C(m2,s)*Prodt(s)*q12^(n1*m2-s*(s+1)/2)*(q*q12)^(n12*(m2-s)+m12*(n1-s))*D(n12+m12+s)*d(n2+m2-s)*d(n1+m1-s)*l2^(exponent_d(n2+m2-s))*l12^(exponent_D(n12+m12+s))*l1^(exponent_d(n1+m1-s));
return [[[]],[k]];
end;

#########################   The cocycle Sigma for fixed q   #########################
tigma:=function(n2,n12,n1,m2,m12,m1)
local k,m,r,t,s1,s2,s3,s4,s5,s6,s7,L1,L2,L3;
L1:=zero;
L2:=zero;
L3:=zero;
if (n12+n1<n) and (m12+m1<n) and (n1<m2 or n1=m2) then
	for s1 in [0..n1] do
	L1:=AddNP(L1,sigma1(n2,n12,n1,s1,m2,m12,m1),F1,F1);
	od;
elif (n12+n1<n) and (m12+m1<n) and (m2<n1) then
	for s1 in [0..m2] do
	L1:=AddNP(L1,sigma1(n2,n12,n1,s1,m2,m12,m1),F1,F1);
	od;
elif (n12+n1<n) and (n<m12+m1 or n=m12+m1) and (n1<m2 or n1=m2) then
	for s1 in [0..n1] do
	L1:=AddNP(L1,sigma1(n2,n12,n1,s1,m2,m12,m1),F1,F1);
	od;
	for r in [0..m12] do
	for t in [0..m1] do
		if (r+t=n) and (m2+r<n) then
		for s2 in [0..n1] do
		L2:=AddNP(L2,MulNP(sigma1(n2,n12,n1,s2,m2+r,m12-r,m1-t),[[[]],[Coef(m2,0,m12,r,0,m1,t)]]),F1,F1);
		od;
		else L2:=L2;
		fi;
	od;
	od;
	L1:=AddNP(L1,L2,F1,-l1);
elif (n12+n1<n) and (n<m12+m1 or n=m12+m1) and (m2<n1) then
	for s1 in [0..m2] do
	L1:=AddNP(L1,sigma1(n2,n12,n1,s1,m2,m12,m1),F1,F1);
	od;
	for r in [0..m12] do
	for t in [0..m1] do
		if (r+t=n) and (m2+r<n) and (n1<m2+r or n1=m2+r) then
		for s2 in [0..n1] do
		L2:=AddNP(L2,MulNP(sigma1(n2,n12,n1,s2,m2+r,m12-r,m1-t),[[[]],[Coef(m2,0,m12,r,0,m1,t)]]),F1,F1);
		od;
		elif (r+t=n) and (m2+r<n1) and (m2+r<n1) then
		for s3 in [0..m2+r] do 
		L2:=AddNP(L2,MulNP(sigma1(n2,n12,n1,s3,m2+r,m12-r,m1-t),[[[]],[Coef(m2,0,m12,r,0,m1,t)]]),F1,F1);
		od;
		else L2:=L2;
		fi;
	od;
	od;
	L1:=AddNP(L1,L2,F1,-l1);
elif (m12+m1<n) and (n<n12+n1 or n=n12+n1) and (n1<m2 or n1=m2) then
	for s1 in [0..n1] do
	L1:=AddNP(L1,sigma1(n2,n12,n1,s1,m2,m12,m1),F1,F1);
	od;
	for k in [0..n12] do
	for m in [0..n1] do
		if (k+m=n) and (n2+k<n) then
		for s2 in [0..n1-m] do
		L2:=AddNP(L2,MulNP(sigma1(n2+k,n12-k,n1-m,s2,m2,m12,m1),[[[]],[Coef(n2,0,n12,k,0,n1,m)]]),F1,F1);
		od;
		else L2:=L2;
		fi;
	od;
	od;
	L1:=AddNP(L1,L2,F1,-l1);
elif (m12+m1<n) and (n<n12+n1 or n=n12+n1) and (m2<n1) then
	for s1 in [0..m2] do
	L1:=AddNP(L1,sigma1(n2,n12,n1,s1,m2,m12,m1),F1,F1);
	od;
	for k in [0..n12] do
	for m in [0..n1] do
		if (k+m=n) and (n2+k<n) and (n1-m<m2 or n1-m=m2) then
		for s2 in [0..n1-m] do
		L2:=AddNP(L2,MulNP(sigma1(n2+k,n12-k,n1-m,s2,m2,m12,m1),[[[]],[Coef(n2,0,n12,k,0,n1,m)]]),F1,F1);
		od;
		elif (k+m=n) and (m2<n1-m) and (m2<n1-m) then
		for s3 in [0..m2] do
		L2:=AddNP(L2,MulNP(sigma1(n2+k,n12-k,n1-m,s3,m2,m12,m1),[[[]],[Coef(n2,0,n12,k,0,n1,m)]]),F1,F1);
		od;
		else L2:=L2;
		fi;
	od;
	od;
	L1:=AddNP(L1,L2,F1,-l1);
elif (n<n12+n1 or n=n12+n1) and (n<m12+m1 or n=m12+m1) and (n1<m2 or n1=m2) then
	for s1 in [0..n1] do
	L1:=AddNP(L1,sigma1(n2,n12,n1,s1,m2,m12,m1),F1,F1);
	od;
	for k in [0..n12] do
	for m in [0..n1] do
		if (k+m=n) and (n2+k<n) then
		for s2 in [0..n1-m] do
		L2:=AddNP(L2,MulNP(sigma1(n2+k,n12-k,n1-m,s2,m2,m12,m1),[[[]],[Coef(n2,0,n12,k,0,n1,m)]]),F1,F1);
		od;
		else L2:=L2;
		fi;
	od;
	od;
	for r in [0..m12] do 
	for t in [0..m1] do
		if (r+t=n) and (m2+r<n) then
		for s3 in [0..n1] do
		L2:=AddNP(L2,MulNP(sigma1(n2,n12,n1,s3,m2+r,m12-r,m1-t),[[[]],[Coef(m2,0,m12,r,0,m1,t)]]),F1,F1);
		od;
		else L2:=L2;
		fi;
	od;
	od;
	L1:=AddNP(L1,L2,F1,-l1);
	for k in [0..n12] do
	for m in [0..n1] do
	for r in [0..m12] do
	for t in [0..m1] do
		if (k+m=n) and (n2+k<n) and (r+t=n) and (m2+r<n) then
		for s4 in [0..n1-m] do
		L3:=AddNP(L3,MulNP(sigma1(n2+k,n12-k,n1-m,s4,m2+r,m12-r,m1-t),[[[]],[Coef(n2,0,n12,k,0,n1,m)*Coef(m2,0,m12,r,0,m1,t)]]),F1,F1);
		od;
		else L3:=L3;
		fi;
	od;
	od;
	od;
	od;
	L1:=AddNP(L1,L3,F1,l1*l1);
elif (n<n12+n1 or n=n12+n1) and (n<m12+m1 or n=m12+m1) and (m2<n1) then
	for s1 in [0..m1] do
	L1:=AddNP(L1,sigma1(n2,n12,n1,s1,m2,m12,m1),F1,F1);
	od;
	for k in [0..n12] do
	for m in [0..n1] do
		if (k+m=n) and (n2+k<n) and (n1-m<m2 or n1-m=m2) then
		for s2 in [0..n1-m] do
		L2:=AddNP(L2,MulNP(sigma1(n2+k,n12-k,n1-m,s2,m2,m12,m1),[[[]],[Coef(n2,0,n12,k,0,n1,m)]]),F1,F1);
		od;
		elif (k+m=n) and (n2+k<n) and (m2<n1-m) then
		for s3 in [0..m2] do
		L2:=AddNP(L2,MulNP(sigma1(n2+k,n12-k,n1-m,s3,m2,m12,m1),[[[]],[Coef(n2,0,n12,k,0,n1,m)]]),F1,F1);
		od;
		else L2:=L2;
		fi;
	od;
	od;
	for r in [0..m12] do
	for t in [0..m1] do
		if (r+t=n) and (m2+r<n) and (n1<m2+r or n1=m2+r) then
		for s4 in [0..n1] do
		L2:=AddNP(L2,MulNP(sigma1(n2,n12,n1,s4,m2+r,m12-r,m1-t),[[[]],[Coef(m2,0,m12,r,0,m1,t)]]),F1,F1);
		od;
		elif (r+t=n) and (m2+r<n) and (m2+r<n1) then
		for s5 in [0..m2+r] do
		L2:=AddNP(L2,MulNP(sigma1(n2,n12,n1,s5,m2+r,m12-r,m1-t),[[[]],[Coef(m2,0,m12,r,0,m1,t)]]),F1,F1);
		od;
		else L2:=L2;
		fi;
	od;
	od;
	L1:=AddNP(L1,L2,F1,-l1);
	for k in [0..n12] do
	for m in [0..n1] do
	for r in [0..m12] do
	for t in [0..m1] do
		if (k+m=n) and (n2+k<n) and (r+t=n) and (m2+r<n) and (n1-m<m2+r or n1-m=m2+r) then
		for s6 in [0..n1-m] do
		L3:=AddNP(L3,MulNP(sigma1(n2+k,n12-k,n1-m,s6,m2+r,m12-r,m1-t),[[[]],[Coef(n2,0,n12,k,0,n1,m)*Coef(m2,0,m12,r,0,m1,t)]]),F1,F1);
		od;
		elif (k+m=n) and (n2+k<n) and (r+t=n) and (m2+r<n) and (m2+r<n1-m) then
		for s7 in [0..m2+r] do
		L3:=AddNP(L3,MulNP(sigma1(n2+k,n12-k,n1-m,s7,m2+r,m12-r,m1-t),[[[]],[Coef(n2,0,n12,k,0,n1,m)*Coef(m2,0,m12,r,0,m1,t)]]),F1,F1);
		od;
		else L3:=L3;
		fi;
	od;
	od;
	od;
	od;
	L1:=AddNP(L1,L3,F1,l1*l1);
else L1:=L1;
fi;
return L1;
end;