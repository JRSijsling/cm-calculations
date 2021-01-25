SetSeed(1);
SetVerbose("EndoFind", 0);
SetVerbose("CurveRec", 0);

prec := 1500;

// This one takes quite some time!
R<t> := PolynomialRing(Rationals());
F<r> := BaseNumberFieldExtra(t^4 - 5*t^2 - 2*t + 1, prec);
R<x> := PolynomialRing(F);

f := x^8 + (-28*r^3 - 4*r^2 + 132*r + 84)*x^7 + (-600*r^3 - 160*r^2 + 2920*r + 2044)*x^6 + (-3532*r^3 - 940*r^2 + 17224*r + 11944)*x^5 + (9040*r^3 + 2890*r^2 - 44860*r - 31460)*x^4 + (167536*r^3 + 49480*r^2 - 824532*r - 576212)*x^3 + (-226976*r^3 - 64932*r^2 + 1113648*r + 776872)*x^2 + (-244204*r^3 - 69572*r^2 + 1197716*r + 835300)*x + 319956*r^3 + 94725*r^2 - 1575062*r - 1100801;
X := HyperellipticCurve(f);

CC := ComplexFieldExtra(prec);
P := PeriodMatrix(X);
P := ChangeRing(P, CC);

R<x> := PolynomialRing(Rationals());
f := x^6 + 10*x^4 + 21*x^2 + 4;

taushyp, tausnonhyp := FullEnumerationG3(f : prec := prec);
tausnonhyp := [ ChangeRing(tau, CC) : tau in tausnonhyp ];

tau := tausnonhyp[3];
I3 := IdentityMatrix(CC, 3);
Q := HorizontalJoin(tau, I3);
test, Rs := AllSmallIsogenies(P, Q);
Rs := Rs[1..(#Rs div 2)];

Ps := [ P*ChangeRing(R, CC)^(-1) : R in Rs ];
for P in Ps do
    assert #SymplecticIsomorphismsCC(P, Q) ne 0;
end for;
//PrintFileMagma("Ps.m", Ps);

