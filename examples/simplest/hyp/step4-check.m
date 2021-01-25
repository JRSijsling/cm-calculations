SetVerbose("EndoFind", 3);
SetVerbose("CurveRec", 0);

prec := 3000;

R<t> := PolynomialRing(Rationals());
F<r> := BaseNumberFieldExtra(t^4 - 5*t^2 - 2*t + 1, prec);
R<x> := PolynomialRing(F);

f := x^8 + (-28*r^3 - 4*r^2 + 132*r + 84)*x^7 + (-600*r^3 - 160*r^2 + 2920*r + 2044)*x^6 + (-3532*r^3 - 940*r^2 + 17224*r + 11944)*x^5 + (9040*r^3 + 2890*r^2 - 44860*r - 31460)*x^4 + (167536*r^3 + 49480*r^2 - 824532*r - 576212)*x^3 + (-226976*r^3 - 64932*r^2 + 1113648*r + 776872)*x^2 + (-244204*r^3 - 69572*r^2 + 1197716*r + 835300)*x + 319956*r^3 + 94725*r^2 - 1575062*r - 1100801;
X := HyperellipticCurve(f);

print "";
print "Discriminant:";
ZZF := Integers(F);
I := ideal< ZZF | Discriminant(f) >;
Fac := Factorization(I);
print Fac;
print "";
print [ Norm(tup[1]) : tup in Fac ];

print "";
print "Curve:";
print X;

Lat := HeuristicEndomorphismLattice(X);
print "";
print "Heuristic endomorphism lattice:";
print Lat;

