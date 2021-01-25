SetSeed(1);
SetVerbose("EndoFind", 3);
SetVerbose("CurveRec", 0);

//load "P.m";
load "Ps.m";
P := Ps[1];

tau := SmallPeriodMatrix(P);
taunew := ReduceSmallPeriodMatrix(tau);
assert IsBigPeriodMatrix(P);
assert IsSmallPeriodMatrix(taunew);

print "";
print "Calculating theta values...";
thetas, thetas_sq := ThetaValues(taunew);
print "done.";

// Find Riemann model over CC
load "riemann.m";
modsCC := ModuliFromTheta(thetas);
FCC := RiemannModelFromModuli(modsCC);

/* Test invariants */
ICC, W := DixmierOhnoInvariants(FCC);
ICC := WPSNormalizeCC(W, ICC);
R<t> := PolynomialRing(Rationals());
K<r> := BaseNumberFieldExtra(t^4 - 5*t^2 - 2*t + 1, prec - 100);
infsK := InfinitePlacesExtra(K);
K`iota := infsK[1];
assert AlgebraizeElementsExtra(ICC[1..5], K);

// Calculate period matrix of FCC using a trick
R<t> := PolynomialRing(Rationals());
CCQ<i> := NumberField(t^2 + 1);
S<x,y,z> := PolynomialRing(CCQ, 3);

print "";
print "Calculating period matrix...";
D := [-2..2];
repeat
    repeat
        T := Matrix(3,3, [ Random(D) : i in [1..9] ]);
        T := Matrix(3,3, [[ 0,  2, -1], [-2,  2,  0], [ 1, -2, -2]]);
    until Determinant(T) ne 0;
    TCC := ChangeRing(T, CC);
    GCC := FCC^TCC;

    G := 0;
    for mon in Monomials(GCC) do
        cCC := MonomialCoefficient(GCC, mon);
        c := (Round((10^prec)*Re(cCC)) + Round((10^prec)*Im(cCC))*i)/10^prec;
        G +:= c*Monomial(S, Exponents(mon));
    end for;

    done := true;
    try
        R<x,y> := PolynomialRing(CCQ, 2);
        h := hom< S -> R | [x,y,1] >;
        f := h(G);
        sigma := InfinitePlaces(CCQ)[1];
        X := RiemannSurface(f, sigma : Precision := prec);
        Pmod := X`BigPeriodMatrix;
        rowsPmod := Rows(Pmod);
        Pmod := Matrix([ rowsPmod[3], rowsPmod[2], rowsPmod[1] ]);
    catch e
        done := false;
    end try;
until done;
print "done.";

CC := K`CC;
P := ChangeRing(P, CC);
Pmod := ChangeRing(Pmod, CC);
cols := Rows(Transpose(Pmod));
Pmod := Transpose(Matrix([ cols[i] : i in [4,5,6,1,2,3] ]));
FCC := ChangeRing(GCC, CC);
/* At this point Pmod is the period matrix of FCC */

assert IsBigPeriodMatrix(P);
assert IsBigPeriodMatrix(Pmod);

isos := SymplecticIsomorphismsCC(P, Pmod);
for tup in isos do
    T, R := Explode(tup);
    R := ChangeRing(R, CC);
    assert Max([ Abs(c) : c in Eltseq(T*P - Pmod*R) ]) lt 10^(prec - 200);
end for;

T, R := Explode(isos[1]);
F0 := FCC^T;
S<x,y,z> := Parent(F0);
F0 /:= MonomialCoefficient(F0, x^4);

cCCs := Coefficients(F0);
print "Algebraizing...";
test, cs := AlgebraizeElementsExtra(cCCs, K);

exps := [ Exponents(mon) : mon in Monomials(F0) ];
S<x,y,z> := PolynomialRing(K, 3);
F0 := &+[ cs[i]*Monomial(S, exps[i]) : i in [1..#exps] ];

ZZK := Integers(K);
gcd := &+([ ideal< ZZK | c > : c in cs ]);
test, gcd := IsPrincipal(gcd);
F0 /:= gcd;

/*
Number Field with defining polynomial t^4 - 5*t^2 - 2*t + 1 over the Rational Field

x^8 + (-28*r^3 - 4*r^2 + 132*r + 84)*x^7 + (-600*r^3 - 160*r^2 + 2920*r + 2044)*x^6 + (-3532*r^3 - 940*r^2 + 17224*r + 11944)*x^5 + (9040*r^3 + 2890*r^2 - 44860*r - 31460)*x^4 + (167536*r^3 + 49480*r^2 - 824532*r - 576212)*x^3 + (-226976*r^3 - 64932*r^2 + 1113648*r + 776872)*x^2 + (-244204*r^3 - 69572*r^2 + 1197716*r + 835300)*x + 319956*r^3 + 94725*r^2 - 1575062*r - 1100801;

(-78957*r^3 + 33269*r^2 + 439955*r + 43483)*x^4 + (480424*r^3 - 331576*r^2 - 1977512*r + 778448)*x^3*y + (-374800*r^3 - 81752*r^2 + 1099996*r - 272108)*x^3*z + (-1408632*r^3 + 1166920*r^2 + 6301856*r - 2134256)*x^2*y^2 + (1443248*r^3 - 1438456*r^2 - 6995512*r + 2104584)*x^2*y*z + (-298146*r^3 + 602894*r^2 + 1940148*r - 608572)*x^2*z^2 + (1978848*r^3 - 1418624*r^2 - 8611008*r + 2654240)*x*y^3 + (-3555184*r^3 + 1315824*r^2 + 13583088*r - 3977392)*x*y^2*z + (3918680*r^3 + 4020928*r^2 - 6036112*r + 1320200)*x*y*z^2 + (-4242148*r^3 - 9119828*r^2 - 1225988*r + 1236372)*x*z^3 + (-967424*r^3 + 771552*r^2 + 4358832*r - 1317392)*y^4 + (1810400*r^3 - 2255264*r^2 - 9491936*r + 2912576)*y^3*z + (539344*r^3 + 6643248*r^2 + 9087624*r - 3225064)*y^2*z^2 + (-7276216*r^3 - 19296920*r^2 - 8055944*r + 4165424)*y*z^3 + (10368524*r^3 + 24954126*r^2 + 7336147*r - 4512453)*z^4

Current version gives different second curve (same invariants):
(-115320*r^3 + 118841*r^2 + 421864*r + 342064)*x^4 + (-436088*r^3 + 312664*r^2 + 1718152*r + 274560)*x^3*y + (14616*r^3 - 324556*r^2 - 580872*r + 140484)*x^3*z + (-8128608*r^3 - 2392032*r^2 + 40091600*r + 28889240)*x^2*y^2 + (-2167104*r^3 - 757656*r^2 + 10012296*r + 6442904)*x^2*y*z + (129268*r^3 + 620152*r^2 + 898100*r + 231186)*x^2*z^2 + (-16896480*r^3 - 4881600*r^2 + 82944768*r + 57757472)*x*y^3 + (-5162208*r^3 - 1433648*r^2 + 24762016*r + 16079392)*x*y^2*z + (410184*r^3 + 6000*r^2 - 301696*r + 2149896)*x*y*z^2 + (-592352*r^3 - 609580*r^2 + 946896*r - 153448)*x*z^3 + (-11924448*r^3 - 3374992*r^2 + 58641120*r + 40621776)*y^4 + (-3986464*r^3 - 1695072*r^2 + 19650784*r + 15708416)*y^3*z + (-1295888*r^3 + 675672*r^2 + 6609280*r + 977960)*y^2*z^2 + (356424*r^3 - 880616*r^2 - 2491032*r + 972608)*y*z^3 + (14058*r^3 + 486715*r^2 + 750290*r - 255959)*z^4
*/
