/***
 *  Enumerating as in Streng
 *
 *  Written by Jeroen Sijsling (jeroen.sijsling@uni-ulm.de)
 *
 *  See LICENSE.txt for license details.
 */

import "smallcl.m": MakeSmallPeriodMatrix;


/* First functions copied from curve_reconstruction */

/* The first two functions are for compatibility with Labrande's conventions */
/* The vectors returned are column vectors, not because I think that this is so
 * great, but because this respects Magma's conventions */
function VectorFromIndex(g, i)
j := i; v := [ ];
for k:=1 to 2*g do
    Append(~v, (j mod 2)/2);
    j := j div 2;
end for;
return Transpose(Matrix([Reverse(v)]));
end function;


/* Second return value is sign transition from standard value */
function IndexFromVector(g, v);
w := Reverse(Eltseq(v));
i := &+[ ((Integers() ! (2*w[j])) mod 2)*2^(j - 1) : j in [1..(2*g)] ];
if i eq 0 then
    return 2^(2*g);
end if;
v0 := VectorFromIndex(g, i); n := v - v0;
v0 := Eltseq(v0); n := Eltseq(n);
s := &+[ v0[i]*n[g + i] : i in [1..g] ];
if IsIntegral(s) then
    s := 1;
else
    s := -1;
end if;
return i, s;
end function;


/* Checks if a vector is even */
function IsEvenVector(v)
w := Eltseq(v); g := #w div 2;
w1 := w[1..g]; w2 := w[(g + 1)..(2*g)];
return IsZero((Integers() ! (4 * &+[ w1[i]*w2[i] : i in [1..g] ])) mod 2);
end function;


/* Finds even vanishing thetas */
function FindDelta(thetas : prec := 0)
if prec eq 0 then
    CC := Parent(thetas[1]); prec := 20;
end if;
CP := CartesianPower([0,1/2], 6);
vs := [ Transpose(Matrix([[ c : c in tup ]])) : tup in CP ];
v0s := [ ];
for v in vs do
    theta := thetas[IndexFromVector(3, v)];
    test := (Abs(theta) lt 10^(-prec)) and IsEvenVector(v);
    if test then
        Append(~v0s, v);
    end if;
end for;
return v0s;
end function;


intrinsic FullEnumerationG3(f::RngUPolElt : prec := 300, exp := Infinity(), FixCMType := false) -> .
{Finds the equivalence classes of CM curves given a polynomial.}

/* Global structures */
F := RationalsExtra(prec); CC := F`CC; R<x> := PolynomialRing(F);
K := NumberFieldExtra(f);
Phis := AllCMTypesUpToEquivalence(K : Primitive := true);
//Phis := AllCMTypes(K : Primitive := true);
precsmall := 50; CCSmall := ComplexFieldExtra(precsmall);

/* Determine totally real subfield and corresponding involution */
test, tup, inv := IsCMField(K);
K0, hK0K := Explode(tup);
assert inv(inv(K.1)) eq K.1;
K0sub := sub< K | hK0K(K0.1) >;

/* Determine class group */
ZZK := Integers(K);
Diff := Different(ZZK);
aas := ClassGroupSmallRepresentatives(ZZK, exp);
vprint CMExp, 1 : "Done determining small representatives of class group!", #aas;

/* Determine unit group quotients */
U, phiU := UnitGroup(ZZK : GRH := true);
//for i in [1..NumberOfGenerators(U)] do print [ EmbedExtra(phiU(U.1) : iota := inf) : inf in InfinitePlacesExtra(K) ]; end for;
gensU := Generators(U);
gensV := [ (phiU(gen)*inv(phiU(gen))) @@ phiU : gen in gensU ];
V := sub< U | gensV >;
Q, pQ := quo< U | V >;
vprint CMExp, 1 : "Done determining quotient of unit group!", #Q;

/* Now follow Streng's method */
taushyp := [ ]; tausnonhyp := [ ];
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
    //print [ EmbedExtra(xi0 : iota := inf) : inf in InfinitePlacesExtra(K) ];

    for q in Q do
        u := q @@ pQ; xi := K ! (phiU(u)*xi0);

        /* Insist that xi be totally imaginary */
        test2 := xi^2 in K0sub and not xi in K0sub;
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
            if &and[ Im(emb) gt CC`epscomp : emb in embs ] then
                test3 := true;
                break;
            end if;
        end for;
        if not test3 then
            vprint CMExp, 1 : "Stopping at test3";
            continue;
        end if;

        /* NOTE that the tests above costs time and are stupid */
        /* If all tests pass, recover period matrix */
        B := Basis(aa);
        B := [ K ! b : b in B ];
        P := Matrix(CC, [ [ EmbedExtra(b : iota := iota) : b in B ] : iota in Phi ]);
        P := ChangeRing(P, CC);
        //P0, U := MakeSmallPeriodMatrix(P);
        //print U;
        //PrintFileMagma("Ps1.m", P);

        /* Recover principal polarization */
        E := Matrix([ [ Trace(xi*inv(x)*y) : x in B ] : y in B ]);
        E := ChangeRing(E, Rationals());
        E := -E;
        /*
        test4 := false;
        if IsPolarization(E, P) then
            test4 := true;
        elif IsPolarization(-E, P) then
            test4 := true;
            E := -E;
        end if;
        */

        /* Declare success */
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
        /*
        print BaseRing(tau);
        print ChangeRing(tau, CCSmall);
        print Maximum([ Abs(c) : c in Eltseq(tau - Transpose(tau)) ]);
        A := Matrix([ [ Im(c) : c in Eltseq(row) ] : row in Rows(tau) ]);
        print Eigenvalues(A);
        */

        /* Reduce small period matrix */
        vprint CMExp, 1 : "Reducing period matrix...";
        tau := ReduceSmallPeriodMatrix(tau);
        vprint CMExp, 1 : "done with reduction.";
        tausmall := ChangeRing(tau, CCSmall);

        /* Test for vanishing even theta constants */
        g := #Rows(tausmall);
        M0 := ZeroMatrix(Rationals(), g, 1);

        /*
        print Maximum([ Abs(c) : c in Eltseq(tausmall - Transpose(tausmall)) ]);
        A := Matrix([ [ Im(c) : c in Eltseq(row) ] : row in Rows(tausmall) ]);
        print Eigenvalues(A);
        */
        /* Calculate thetas and return */
        thetas := ThetaValues(tausmall : Labrande := false);
        v0s := FindDelta(thetas);
        N := #v0s;
        if N eq 1 then Append(~taushyp, tau); end if;
        if N eq 0 then Append(~tausnonhyp, tau); end if;
    end for;
end for;
return taushyp, tausnonhyp;

end intrinsic;


intrinsic FullEnumerationG3(datum::List : prec := 300, exp := Infinity(), ClassBound := Infinity()) -> .
{Finds the equivalence classes of CM curves for the given datum. ClassBound bounds the class number.}

/* Recover polynomial */
R<x> := PolynomialRing(Rationals());
f := R ! datum[2];

/* Calculate if passes class test */
K := NumberField(f);
if #ClassGroup(K) gt ClassBound then return [ ]; end if;
return FullEnumerationG3(f : prec := prec, exp := exp);

end intrinsic;
