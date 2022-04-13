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

f := x^6 - 3*x^5 + 9*x^4 - 13*x^3 + 15*x^2 - 9*x + 3;

/* Gal(Kr/QQ) = (C2)^3 x C3 */
//f := x^6 - 3*x^5 + 9*x^4 - 13*x^3 + 15*x^2 - 9*x + 3;
//f := x^6 - x^5 + 387*x^4 - 14003*x^3 - 186709*x^2 - 5290239*x + 239442421; // there is an error here in the reflex field computation


/* Gal(Kr/QQ) = (C2)^3 x S3 */
//f := x^6 - x^5 + 381*x^4 - 1607*x^3 - 548410*x^2 - 2158644*x + 186867008;
//f := x^6 - 55*x^4 + 32*x^3 + 1591*x^2 - 1888*x + 14431;

/* Gal(Kr/QQ) = D6 */
f := x^6 - 2*x^5 - 70*x^4 + 96*x^3 + 2245*x^2 - 1598*x + 20192;

/* Gal(K/QQ) = C6 */
//f := x^6 + 78*x^4 + 1521*x^2 + 676;

K := NumberFieldExtra(f : prec := 4000);
print "K", K;
Phis := AllCMTypes(K);
Phi := Phis[2];

/* We construct the reflex field as a subfield of CC, that is, as a number
 * field together with an embedding into CC */
time Kr := NumericalReflexField(Phi, K);
Phisr := AllCMTypes(Kr);
print "Kr", Kr;

/* We save K in an intermediate step for experimentation */
K0 := K;

/* We run over the CM types on the reflex field... one of these is the reflex
 * type, after all */
for i in [1..#Phisr] do
    Phir := Phisr[i];
    prec := Precision(Kr`CC);

    /* Recover the double reflex */
    Br := Basis(Kr);
    BrCC := [ &+[ EmbedExtra(br : iota := iotar) : iotar in Phir ] : br in Br ];
    K := NumberFieldExtra(BrCC, RationalsExtra(prec));

    /* Continue if the double reflex is isomorphic to the original field */
    if IsIsomorphic(K, K0) then
        //K := K0;
        ZZK := Integers(K);
        ZZKr := Integers(Kr);
        Cl, phiCl := ClassGroup(ZZK);
        Clr, phiClr := ClassGroup(ZZKr);

        gensr := Generators(Clr);
        imgensr := [ ];
        for genr in gensr do
            /* NOTE: The mistake is here, as the type norms of generators may not suffice a priori */
            /* Should think about this */
            gengensCC := [ &*[ EmbedExtra(Kr ! gengenr : iota := iotar) : iotar in Phir ] : gengenr in Generators(phiClr(genr)) ];
            gengens := [ ];
            for gengenCC in gengensCC do
                stop := false;
                test, gengen := AlgebraizeElementExtra(gengenCC, K);
                if not test then
                    stop := true;
                    break;
                end if;
                Append(~gengens, gengen);
            end for;
            if stop then break; end if;
            Append(~imgensr, ideal< ZZK | gengens >);
        end for;
        if stop then continue; end if;
        assert #gensr eq #imgensr;
        print "-------";

        print [ IsPrincipal(imgenr) : imgenr in imgensr ];
        imgensr := [ imgenr @@ phiCl : imgenr in imgensr ];
        H := sub< Cl | imgensr >;

        //print #Cl;
        //print #H;
        print "H: ", H;
        print "Cl/H: ", Cl/H;
    end if;
end for;
quit;
