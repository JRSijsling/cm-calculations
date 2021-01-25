SetVerbose("EndoFind", 0);
SetVerbose("CurveRec", 0);

R<t> := PolynomialRing(Rationals());
K<r> := NumberField(t^4 - 5*t^2 - 2*t + 1);
ZZK := Integers(K);

S<x,y,z> := PolynomialRing(K, 3);
F := (-78957*r^3 + 33269*r^2 + 439955*r + 43483)*x^4 + (480424*r^3 - 331576*r^2 - 1977512*r + 778448)*x^3*y + (-374800*r^3 - 81752*r^2 + 1099996*r - 272108)*x^3*z + (-1408632*r^3 + 1166920*r^2 + 6301856*r - 2134256)*x^2*y^2 + (1443248*r^3 - 1438456*r^2 - 6995512*r + 2104584)*x^2*y*z + (-298146*r^3 + 602894*r^2 + 1940148*r - 608572)*x^2*z^2 + (1978848*r^3 - 1418624*r^2 - 8611008*r + 2654240)*x*y^3 + (-3555184*r^3 + 1315824*r^2 + 13583088*r - 3977392)*x*y^2*z + (3918680*r^3 + 4020928*r^2 - 6036112*r + 1320200)*x*y*z^2 + (-4242148*r^3 - 9119828*r^2 - 1225988*r + 1236372)*x*z^3 + (-967424*r^3 + 771552*r^2 + 4358832*r - 1317392)*y^4 + (1810400*r^3 - 2255264*r^2 - 9491936*r + 2912576)*y^3*z + (539344*r^3 + 6643248*r^2 + 9087624*r - 3225064)*y^2*z^2 + (-7276216*r^3 - 19296920*r^2 - 8055944*r + 4165424)*y*z^3 + (10368524*r^3 + 24954126*r^2 + 7336147*r - 4512453)*z^4;
mons := Monomials(F);
cs := [ MonomialCoefficient(F, mon) : mon in mons ];

I := DixmierOhnoInvariants(F);
D := I[#I];
D := QuarticDiscriminant(F : IntegralNormalization := true);
I := ideal< ZZK | D >;
print "";
Fac := Factorization(I);
print Fac;
print "";
print [ Norm(tup[1]) : tup in Fac ];

infs := InfinitePlaces(K);
U, phiU := UnitGroup(K);
u1 := K ! phiU(U.2);
u2 := K ! phiU(U.3);
u3 := K ! phiU(U.4);
abs1 := [ Log(Abs(Evaluate(u1, inf))) : inf in infs ];
abs2 := [ Log(Abs(Evaluate(u2, inf))) : inf in infs ];
abs3 := [ Log(Abs(Evaluate(u3, inf))) : inf in infs ];
M := Matrix([abs1, abs2, abs3]);
Lat := Lattice(M);

F := Evaluate(F, [x,y,u1^(-1)*u3^(+1)*z]);
F := F*u3;
cs := [ MonomialCoefficient(F, mon) : mon in mons ];

print "";
for i:=1 to #mons do
    c := cs[i];
    absc := [ Log(Abs(Evaluate(c, inf))) : inf in infs ];
    v := Vector(absc);
    ws := ClosestVectors(Lat, v);
    w := ws[1];
    assert #ws eq 1;
    print mons[i];
    print [ Round(c) : c in Eltseq(NumericalSolution(M, w)) ];
end for;

print "";
print #Sprint(F);
print #Sprint(F*u1);
print #Sprint(F/u1);
print #Sprint(F*u3);
print #Sprint(F/u3);

/*
(14106*r^3 - 150652*r^2 + 185086*r + 292255)*x^4 + (-171112*r^3 + 44200*r^2 + 916008*r + 93360)*x^3*y + (-120788*r^3 + 49032*r^2 + 382244*r + 300708)*x^3*z + (467744*r^3 - 209864*r^2 - 2160704*r + 183416)*x^2*y^2 + (-72248*r^3 + 64768*r^2 + 347488*r - 362984)*x^2*y*z + (5720*r^3 - 12378*r^2 - 15628*r + 50692)*x^2*z^2 + (-512608*r^3 + 349824*r^2 + 2423616*r - 580448)*x*y^3 + (202192*r^3 - 151024*r^2 - 1180320*r + 403568)*x*y^2*z + (6512*r^3 - 11272*r^2 + 178120*r - 71336)*x*y*z^2 + (-11832*r^3 + 12268*r^2 - 844*r + 1376)*x*z^3 + (263424*r^3 - 176880*r^2 - 1159232*r + 335040)*y^4 + (-201216*r^3 + 100448*r^2 + 856096*r - 249632)*y^3*z + (62112*r^3 + 1984*r^2 - 226512*r + 71624)*y^2*z^2 + (-12520*r^3 - 13112*r^2 + 27736*r - 5360)*y*z^3 + (1526*r^3 + 2411*r^2 - 658*r + 197)*z^4
*/


