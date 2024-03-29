SetSeed(1);
SetVerbose("EndoFind", 3);
SetVerbose("CurveRec", 2);
SetVerbose("CMExp", 2);
SetClassGroupBounds("GRH");

prec := 4300;
precred := 500;
prectheta := prec - 100;
F := RationalsExtra(prec);
R<x> := PolynomialRing(F);

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

f := fs[7];
taushyp, tausnonhyp := EnumerationUpToGalois(f : exp := 4, prec := prec, precred := precred, prectheta := prectheta, Labrande := true);
PrintFileMagma("taus-7.m", taushyp);
PrintFileMagma("taus-7.m", tausnonhyp);

exit;
