SetSeed(1);
SetVerbose("EndoFind", 3);
SetVerbose("CurveRec", 2);
SetVerbose("CMExp", 2);
SetClassGroupBounds("GRH");
load "D6/fields.m";

prec := 4300;
precred := 500;
prectheta := prec - 100;

F := RationalsExtra(prectheta); CC := F`CC;
R<x> := PolynomialRing(F);
datum := data[55];
f := R ! datum[2];

taushyp, tausnonhyp := EnumerationUpToGalois(f : exp := 2, prec := prec, precred := precred, prectheta := prectheta, Labrande := true);
print #taushyp, #tausnonhyp;

/* From nothing */
F := RationalsExtra(prectheta); CC := F`CC;
for tup in taushyp do
    thetas_sq := tup[3];
    thetas_sq := [ CC ! t : t in thetas_sq ];
    ICC := ShiodaInvariantsFromThetaSquares(thetas_sq);
    L, I, hKL := NumberFieldExtra(ICC, F);
    print I;
end for;
exit;

/* Alternatively, specify the field from a hunch */
K := NumberFieldExtra(f : prec := prectheta);
Phis := AllCMTypes(K : Primitive := true);
Kr := NumericalReflexField(Phis[1], K);
g := DefiningPolynomial(Kr);
print g;

f := x^9 - x^8 - 4*x^7 - 3*x^6 - 13*x^5 - 13*x^4 + x^3 + 2*x^2 - 2*x - 1;
L := NumberFieldExtra(f : prec := prectheta);
for tup in taushyp do
    thetas_sq := tup[3];
    thetas_sq := [ CC ! t : t in thetas_sq ];
    //ICC := ShiodaInvariantsFromThetaSquares(thetas_sq);
    for infL in InfinitePlacesExtra(L) do
        L`iota := infL;
        try
            test, I := AlgebraizeElementsExtra(ICC, L);
        catch e
            test := false;
        end try;
        if test then
            print "Managed to algebraize";
            print I;
            break;
        end if;
    end for;
    if not test then
        print "Failed to algebraize";
    end if;
end for;


