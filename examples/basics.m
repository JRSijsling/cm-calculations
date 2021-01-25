/*
 * Description:
 * 1. Compute CM pair (K, Phi)
 * 2. Compute Kr(Phi)
 * 3. Compute the set of all reflex CM-types
 * 4. Check that K is isomorphic to Kr. This is only for a certain Galois group the case and not true in general.
 * 5. For every generator gi of Cl(Kr) do:
 * 6.       I_gi := gi as an ideal in OK
 * 7.       embeed the generators of I_gi into CC by the set Phir.
 * 8.       compute the product in step 7, i.e. compute the type norm on the set of generators of I_gi
 * 9.       do an extra test if and check if the element in step 8 is an algebraic number in K. If so compute ideal I_giK as the corresponding
 * 10. Compute subgroup of Cl(K) corresponding to the image of the type norm.
*/

SetSeed(1);
SetVerbose("EndoFind", 0);
SetVerbose("CurveRec", 0);
SetVerbose("CMExp", 1);
SetClassGroupBounds("GRH");

R<x> := PolynomialRing(Rationals());
f := x^6 - x^5 + 387*x^4 - 14003*x^3 - 186709*x^2 - 5290239*x + 239442421;
f := x^6 - x^5 + 381*x^4 - 1607*x^3 - 548410*x^2 - 2158644*x + 186867008;
f := x^6 - x^5 + 352*x^4 - 13204*x^3 + 16417*x^2 - 9165325*x + 176131225;

K := NumberFieldExtra(f);
test, tup0, invK := IsCMField(K);

Phis := AllCMTypes(K);
Phis := AllCMTypesUpToEquivalence(K);

print "=======";
print "Check primitivity of primitive types:";
for Phi in Phis do
    print "-------";
    print IsCMType(Phi, K);
    print IsPrimitiveCMType(Phi, K);
end for;
print "-------";

Phis := AllCMTypes(K : Galois := true);
Phis := AllCMTypesUpToEquivalence(K : Galois := true);

print "";
print "=======";
print "Check primitivity of primitive types:";
for Phi in Phis do
    print "-------";
    print IsCMType(Phi, K : Galois := true);
    print IsPrimitiveCMType(Phi, K : Galois := true);
end for;
print "-------";

L := Explode(K`embL);
for Phi in Phis do
    print "";
    print "Testing ReflexField:";
    Kr, Phir := ReflexField(Phi, K);
    print Kr;

    print "";
    print "Testing TypeNorm and ReflexTypeNorm:";
    Nm := TypeNorm(Phi, K, Kr);
    print Nm(K.1);
    RefNm := ReflexTypeNorm(Phir, Kr, K);
    print RefNm(Kr.1);

    print "";
    print "Testing TypeNormIdeals and ReflexTypeNormIdeals:";
    Nm := TypeNormIdeals(Phi, K, Kr);
    ZZK := Integers(K);
    print Nm(ideal< ZZK | K.1 >);
    RefNm := ReflexTypeNormIdeals(Phir, Kr, K);
    ZZKr := Integers(Kr);
    print RefNm(ideal< ZZKr | Kr.1 >);

    print "";
    print "Testing TypeNormIdealClasses and ReflexTypeNormIdealClasses:";
    Nm, Ktup, Krtup := TypeNormIdealClasses(Phi, K, Kr);
    ClK, phiClK := Explode(Ktup);
    ClKr, phiClKr := Explode(Krtup);
    print Nm(ClK.1);
    print Nm(ClK.2);
    RefNm, Krtup, Ktup := ReflexTypeNormIdealClasses(Phir, Kr, K);
    ClKr, phiClKr := Explode(Krtup);
    ClK, phiClK := Explode(Ktup);
    print RefNm(ClKr.1);

    print "";
    print "Testing ClassGroupQuotient:";
    Q, Cl3, ImRef := ClassGroupQuotient(Phi, K);
    print "";
    print "Quotient:";
    print Q;
    print "";
    print "Kernel:";
    print Cl3;
    print "";
    print "Image:";
    print ImRef;
end for;

