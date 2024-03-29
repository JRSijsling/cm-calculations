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

f := fs[14];
prec := 8100;
K := NumberFieldExtra(f : prec := prec);

Phis := AllCMTypes(K);
Kr := NumericalReflexField(Phis[1], K);
g := DefiningPolynomial(Kr);
print g;

load "taus-14.m";
load "syzygies.m";
SetVerbose("EndoFind", 3);

F := RationalsExtra(prec);
CC := F`CC;
Ls := [ ];
for tup in tausnonhyp do
    thetas := tup[2];
    thetas := [ CC ! t : t in thetas ];
    ICC := DixmierOhnoInvariantsFromThetas(thetas);
    ICC := [ ICC[2] ];
    L, I, hKL := NumberFieldExtra(ICC, F);
    PrintFileMagma("invs-nonhyp-14.m", I);
    Append(~Ls, L);
end for;
print Ls;
exit;

/*
R<x> := PolynomialRing(Rationals());
f := x^8 - 2*x^7 + 5*x^6 - 58*x^5 + 158*x^4 - 194*x^3 + 425*x^2 - 418*x + 127;
L := NumberFieldExtra(f : prec := prec);
infsL := InfinitePlacesExtra(L);
L`iota := infsL[1];
CC := L`CC;
*/

f := x^4 - 16*x^2 - 12*x + 15;
L := NumberFieldExtra(f : prec := prec);
infsL := InfinitePlacesExtra(L);
L`iota := infsL[4];
CC := L`CC;

//tausnonhyp := [ tausnonhyp[1], tausnonhyp[3] ];
for tup in tausnonhyp do
    thetas := tup[2];
    thetas := [ CC ! t : t in thetas ];
    ICC := DixmierOhnoInvariantsFromThetas(thetas);
    ICC := ICC[1..#ICC - 1];
    test, I := AlgebraizeElementsExtra(ICC, L);
    print test;

    AA := AffineSpace(L, 1);
    R<t> := CoordinateRing(AA);
    J := I cat [ t ];
    rels := DixmierOhnoAlgebraicRelations(J);
    S := Scheme(AA, rels);
    pts := Points(S);
    assert #pts eq 1;
    I27 := pts[1][1];
    I := I cat [ I27 ];

    //PrintFileMagma("invs-nonhyp-14.m", I);
end for;


