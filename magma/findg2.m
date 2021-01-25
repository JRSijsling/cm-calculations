/***
 *  Enumerating as in Streng
 *
 *  Written by Jeroen Sijsling (jeroen.sijsling@uni-ulm.de)
 *
 *  See LICENSE.txt for license details.
 */


// TODO: UPDATE

intrinsic FullEnumerationG2(f::RngUPolElt : prec := 300, FixCMType := true) -> .
{Finds the equivalence classes of CM curves with maximal CM by the given polynomial.}

/* Global structures */
precsmall := 50; CCSmall := ComplexFieldExtra(precsmall);
F := RationalsExtra(prec); CC := F`CC; R<x> := PolynomialRing(F);
K := NumberFieldExtra(f);
Phis := AllCMTypesUpToEquivalence(K : Primitive := true);

/* Determine totally real subfield and corresponding involution */
K0s := [ tup[1] : tup in Subfields(K) | Degree(tup[1]) eq (Degree(K) div 2) ];
K0s := [ K0 : K0 in K0s | IsTotallyReal(K0) ];
assert #K0s eq 1; K0 := K0s[1];
G, _, phiG := AutomorphismGroupPari(K);
invs := [ ];
for g in G do
    inv := phiG(g);
    if Order(g) eq 2 and inv(K0.1) eq K0.1 then
        Append(~invs, inv);
    end if;
end for;
assert #invs eq 1; inv := invs[1];

/* Determine class group */
ZZK := Integers(K);
Diff := Different(ZZK);
aas := ClassGroupSmallRepresentatives(ZZK);
//print [ Norm(aa) : aa in aas] ;
vprint CMExp, 1 : "Done determining class group!", #aas;

/* Determine unit group quotients */
U, phiU := UnitGroup(ZZK : GRH := true);
gensU := Generators(U);
gensV := [ (phiU(gen)*inv(phiU(gen))) @@ phiU : gen in gensU ];
V := sub< U | gensV >;
Q, pQ := quo< U | V >;
vprint CMExp, 1 : "Done determining quotient of unit group!", #Q;

/* Now follow Streng's method */
taus := [ ];
counter := 0;
for aa in aas do
    vprint CMExp, 1 : "Norm of ideal:", Norm(aa);
    aabar := ideal< ZZK | [ inv(gen) : gen in Generators(aa) ] >;

    /* Need generator; can also exclude fields with i here */
    test1, xi0 := IsPrincipal((aa*aabar*Diff)^(-1));
    if not test1 then
        vprint CMExp, 1 : "Stopping at test1";
        continue;
    end if;

    for q in Q do
        u := q @@ pQ; xi := K ! (phiU(u)*xi0);

        /* Insist that xi be totally imaginary */
        test2 := xi^2 in K0 and not xi in K0;
        if not test2 then
            vprint CMExp, 1 : "Stopping at test2";
            continue;
        end if;
        assert ideal< ZZK | xi > eq (aa*aabar*Diff)^(-1);

        /* Find corresponding CM type if possible */
        test3 := false;
        if FixCMType then NPhis := 1; else NPhis := #Phis; end if;
        for iPhi in [1..NPhis] do
            Phi := Phis[iPhi];
            embs := [ EmbedExtra(xi : iota := inf) : inf in Phi ];
            assert &and[ Abs(Re(emb)) lt CC`epscomp : emb in embs ];
            if &and[ Im(emb) gt CC`epscomp : emb in embs ] then
                test3 := true;
                break;
            end if;
        end for;
        if not test3 then
            vprint CMExp, 1 : "Stopping at test3";
            continue;
        end if;

        /* If all tests pass, recover period matrix */
        B := Basis(aa);
        B := [ K ! b : b in B ];
        P := Matrix(CC, [ [ EmbedExtra(b : iota := iota) : b in B ] : iota in Phi ]);
        //PrintFileMagma("Ps1.m", P);

        /* Recover principal polarization */
        E := Matrix([ [ Trace(xi*inv(x)*y) : x in B ] : y in B ]);
        E := ChangeRing(E, Rationals());
        test4 := false;
        if IsPolarization(E, P) then
            test4 := true;
        elif IsPolarization(-E, P) then
            test4 := true;
            E := -E;
        end if;

        /* Assert and declare succes */
        assert test4;
        counter +:= 1;
        vprint CMExp, 1 : "New abelian variety number", counter;

        /* Convert to big period matrix */
        E := ChangeRing(E, Integers());
        E0, T := FrobeniusFormAlternating(E);
        P := P*ChangeRing(Transpose(T), CC);
        //assert IsBigPeriodMatrix(P);
        //PrintFileMagma("Ps2.m", P);

        /* Convert to small period matrix */
        tau := SmallPeriodMatrix(P);
        vprint CMExp, 1 : "Reducing period matrix...";
        tau := ReduceSmallPeriodMatrix(tau);
        vprint CMExp, 1 : "done with reduction.";
        Append(~taus, tau);
    end for;
end for;
return taus;

end intrinsic;


intrinsic FullEnumerationG2(datum::List : prec := 300, ClassBound := Infinity()) -> .
{Finds the equivalence classes of CM curves for the given datum. ClassBound bounds the class number.}

/* Recover polynomial */
R<x> := PolynomialRing(Rationals());
f := R ! datum[2];

/* Calculate if passes class test */
K := NumberField(f);
if #ClassGroup(K) gt ClassBound then
    return [ ];
end if;
return FullEnumerationG2(f : prec := prec);

end intrinsic;
