SetSeed(1);
SetVerbose("EndoFind", 0);
SetVerbose("CurveRec", 0);

prec := 1400;

// This one takes quite some time!
R<t> := PolynomialRing(Rationals());
F<r> := BaseNumberFieldExtra(t^4 - 5*t^2 - 2*t + 1, prec);
//F := BaseNumberFieldExtra(t^8 - 4*t^7 + 10*t^5 + 7*t^4 - 10*t^3 - 18*t^2 - 6*t + 1);
//r := Roots(t^4 - 5*t^2 - 2*t + 1, F)[1][1];
R<x> := PolynomialRing(F);

f := x^8 + (-28*r^3 - 4*r^2 + 132*r + 84)*x^7 + (-600*r^3 - 160*r^2 + 2920*r + 2044)*x^6 + (-3532*r^3 - 940*r^2 + 17224*r + 11944)*x^5 + (9040*r^3 + 2890*r^2 - 44860*r - 31460)*x^4 + (167536*r^3 + 49480*r^2 - 824532*r - 576212)*x^3 + (-226976*r^3 - 64932*r^2 + 1113648*r + 776872)*x^2 + (-244204*r^3 - 69572*r^2 + 1197716*r + 835300)*x + 319956*r^3 + 94725*r^2 - 1575062*r - 1100801;

Fac := Factorization(f);
print Fac;
g1 := Fac[1][1];
g2 := Fac[2][1];

fCC := EmbedPolynomialExtra(f);
g1CC := EmbedPolynomialExtra(g1);
g2CC := EmbedPolynomialExtra(g2);

XCC := SE_Curve(fCC, 2 : Prec := Precision(F`CC));
CC := ComplexFieldExtra(prec - 100);
P := XCC`BigPeriodMatrix;
P := ChangeRing(P, CC);

bps := XCC`BranchPoints;
assert Abs(Evaluate(g1CC, bps[1])) lt 10^(-100);
assert Abs(Evaluate(g1CC, bps[2])) lt 10^(-100);
P1 := [ bps[1], 0 ];
P2 := [ bps[2], 0 ];

bps := XCC`BranchPoints;
assert Abs(Evaluate(g2CC, bps[5])) lt 10^(-100);
assert Abs(Evaluate(g2CC, bps[6])) lt 10^(-100);
Q1 := [ bps[5], 0 ];
Q2 := [ bps[6], 0 ];

g := #Rows(P);
char1 := SE_AbelJacobi(P1, P2, XCC);
char1 := Matrix(Rationals(), [ [ Round(2*c)/2 : c in Eltseq(char1) ] ]);
print char1;
char2 := SE_AbelJacobi(Q1, Q2, XCC);
char2 := Matrix(Rationals(), [ [ Round(2*c)/2 : c in Eltseq(char2) ] ]);
print char2;

char := char1 + char2;

char1 := Submatrix(char, 1,1,   1,g);
char2 := Submatrix(char, 1,g+1, 1,g);
char := HorizontalJoin(char2, char1);
print "";
print char;

M := IdentityMatrix(Rationals(), 6);
M := VerticalJoin(M, Matrix(Rationals(), char));
M := Matrix(Basis(LLL(Lattice(M))));

P1 := Submatrix(P, 1,1,   g,g);
P2 := Submatrix(P, 1,g+1, g,g);
P := HorizontalJoin(P2, P1);
assert IsBigPeriodMatrix(P);

print "";
GeoEndoRep := GeometricEndomorphismRepresentationCC(P);
print EndomorphismStructure(GeoEndoRep);

P := P*ChangeRing(Transpose(M), CC);
print "";
GeoEndoRep := GeometricEndomorphismRepresentationCC(P);
print EndomorphismStructure(GeoEndoRep : CalcPic := false);

/*
R<x> := PolynomialRing(Rationals());
f := x^6 + 10*x^4 + 21*x^2 + 4;
taushyp, tausnonhyp := FindHyperellipticCMFromPolynomial(f : prec := prec);
taushyp := [ ChangeRing(tau, CC) : tau in taushyp ];
tausnonhyp := [ ChangeRing(tau, CC) : tau in tausnonhyp ];

print "";
for tau in tausnonhyp do
    I3 := IdentityMatrix(CC, 3);
    Q := HorizontalJoin(tau, I3);
    GeoHomRep := GeometricHomomorphismRepresentationCC(P, Q);
    if #GeoHomRep ne 0 then
        break;
    end if;
end for;

print "";
print "Trying to find isomorphism...";
D := [-1..1];
Rs := [ tup[2] : tup in GeoHomRep ];
CP := CartesianPower(D, #Rs);
while true do
    tup := Random(CP);
    R := &+[ tup[i]*Rs[i] : i in [1..#Rs] ];
    if Abs(Determinant(R)) eq 1 then
        print R;
        break;
    end if;
end while;
print "done";
*/

print "";
print "Finding polarization...";
test, E := SomePrincipalPolarization(P);
print E;
print "done.";

E0, T := FrobeniusFormAlternatingRational(E);
TCC := ChangeRing(T, CC);
P := P*Transpose(TCC);
assert IsBigPeriodMatrix(P);

print "";
for tau in taushyp do
    I3 := IdentityMatrix(CC, 3);
    Q := HorizontalJoin(tau, I3);
    isos := SymplecticIsomorphismsCC(P, Q);
    print #isos;
end for;

/*
R<x> := PolynomialRing(Rationals());
f := x^6 + 10*x^4 + 21*x^2 + 4;

taushyp, tausnonhyp := FindHyperellipticCMFromPolynomial(f : prec := prec);
taushyp := [ ChangeRing(tau, CC) : tau in taushyp ];
tausnonhyp := [ ChangeRing(tau, CC) : tau in tausnonhyp ];

print "";
for tau in taushyp do
    I3 := IdentityMatrix(CC, 3);
    Q := HorizontalJoin(tau, I3);
    isos := SymplecticIsomorphismsCC(P, Q);
    print #isos;
end for;

print "";
for tau in tausnonhyp do
    I3 := IdentityMatrix(CC, 3);
    Q := HorizontalJoin(tau, I3);
    isos := SymplecticIsomorphismsCC(P, Q);
    print #isos;
end for;
*/

