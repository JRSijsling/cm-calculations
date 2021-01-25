SetSeed(1);

load "thetas-16.m";
load "syzygies.m";
SetVerbose("EndoFind", 3);

prec := 20100;
R<x> := PolynomialRing(Rationals());
f := x^16 + 4*x^14 - 22*x^12 + 48*x^10 + 305*x^8 - 324*x^6 + 452*x^4 + 2272*x^2 + 256;
L := NumberFieldExtra(f : prec := prec);
infsL := InfinitePlacesExtra(L);
CC := L`CC;

thetas := [ CC ! t : t in thetas ];
ICC := DixmierOhnoInvariantsFromThetas(thetas);
/*
ICC := ICC[2..2];
for infL in infsL do
    L`iota := infL;
    test, I := AlgebraizeElementsExtra(ICC, L);
    print test;
end for;
*/

L`iota := infsL[5];
test, I := AlgebraizeElementsExtra(ICC, L);
print test;
PrintFileMagma("invs-nonhyp-16.m", I);

