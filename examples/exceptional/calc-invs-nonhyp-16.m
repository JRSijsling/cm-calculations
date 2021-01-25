SetSeed(1);

R<x> := PolynomialRing(Rationals());
fs := [
x^6 + 10*x^4 + 21*x^2 + 4,
x^6 - 3*x^5 + 14*x^4 - 23*x^3 + 28*x^2 - 17*x + 4,
x^6 - 2*x^5 + 12*x^4 - 31*x^3 + 59*x^2 - 117*x + 121,
x^6 + 14*x^4 + 43*x^2 + 36,
x^6 - 3*x^5 + 9*x^4 + 4*x^3 + 12*x^2 + 84*x + 236,
x^6 - 2*x^5 + x^4 - 4*x^3 + 5*x^2 - 50*x + 125,
x^6 + 29*x^4 + 246*x^2 + 512,
x^6 - 3*x^5 + 10*x^4 + 8*x^3 + x^2 + 90*x + 236,
x^6 + 21*x^4 + 60*x^2 + 4,
x^6 + 30*x^4 + 169*x^2 + 200,
x^6 + 23*x^4 + 112*x^2 + 36,
x^6 - 2*x^5 + 12*x^4 - 44*x^3 + 242*x^2 - 672*x + 1224,
x^6 + 26*x^4 + 177*x^2 + 128,
x^6 + 29*x^4 + 226*x^2 + 252,
x^6 - 2*x^5 - 7*x^4 + 45*x^3 - 63*x^2 - 162*x + 729,
x^6 - 2*x^5 + 11*x^4 + 42*x^3 - 11*x^2 + 340*x + 950,
x^6 - 3*x^5 + 29*x^4 - 53*x^3 + 200*x^2 - 174*x + 71
];

f := fs[16];
prec := 4100;
K := NumberFieldExtra(f : prec := prec);

Phis := AllCMTypes(K);
Kr := NumericalReflexField(Phis[1], K);
g := DefiningPolynomial(Kr);
print g;

load "taus-16.m";
load "syzygies.m";
SetVerbose("EndoFind", 3);

/*
F := RationalsExtra(prec);
CC := F`CC;
Ls := [ ];
tausnonhyp := [ tausnonhyp[i] : i in [3..6] ];
for tup in tausnonhyp do
    thetas := tup[2];
    thetas := [ CC ! t : t in thetas ];
    ICC := DixmierOhnoInvariantsFromThetas(thetas);
    ICC := [ ICC[2] ];
    L, I, hKL := NumberFieldExtra(ICC, F);
    //PrintFileMagma("invs-nonhyp-16.m", I);
    Append(~Ls, L);
end for;
//[
//    Number Field with defining polynomial x^8 + 18*x^6 + 32*x^4 - 120*x^2 + 16
//    over the Rational Field,
//    Number Field with defining polynomial x^8 + 18*x^6 + 32*x^4 - 120*x^2 + 16
//    over the Rational Field
//]
exit;
*/

R<x> := PolynomialRing(Rationals());
f := x^8 + 18*x^6 + 32*x^4 - 120*x^2 + 16;
L := NumberFieldExtra(f : prec := prec);
infsL := InfinitePlacesExtra(L);
L`iota := infsL[4];
CC := L`CC;

for tup in tausnonhyp[2..2] do
    thetas := tup[2];
    thetas := [ CC ! t : t in thetas ];
    ICC := DixmierOhnoInvariantsFromThetas(thetas);
    //ICC := ICC[1..#ICC - 1];
    test, I := AlgebraizeElementsExtra(ICC, L);
    print test;
end for;
exit;

R<x> := PolynomialRing(Rationals());
f := x^16 + 4*x^14 - 22*x^12 + 48*x^10 + 305*x^8 - 324*x^6 + 452*x^4 + 2272*x^2 + 256;
L := NumberFieldExtra(f : prec := prec);
infsL := InfinitePlacesExtra(L);
L`iota := infsL[3];
CC := L`CC;

minpols := [ ];
for tup in tausnonhyp[3..6] do
    thetas := tup[2];
    thetas := [ CC ! t : t in thetas ];
    ICC := DixmierOhnoInvariantsFromThetas(thetas);
    ICC := ICC[2..2];
    test, I := AlgebraizeElementsExtra(ICC, L);
    print test;
    minpol := MinimalPolynomial(I[1]);
    Append(~minpols, minpol);
end for;

