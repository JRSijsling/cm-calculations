SetSeed(1);
SetVerbose("EndoFind", 0);
SetVerbose("CurveRec", 0);
SetVerbose("CMExp", 2);
SetClassGroupBounds("GRH");

R<x> := PolynomialRing(Rationals());
data := [ [* "6.0.32993536.1",
    x^6 + 10*x^4 + 21*x^2 + 4,
    -32993536, 11, [* 2, 2 *]
*], [* "6.0.149234427.1",
    x^6 - 3*x^5 + 14*x^4 - 23*x^3 + 28*x^2 - 17*x + 4,
    -149234427, 11, [* 2, 2 *]
*], [* "6.0.186306967.1",
    x^6 - 2*x^5 + 12*x^4 - 31*x^3 + 59*x^2 - 117*x + 121,
    -186306967, 11, [* 4 *]
*], [* "6.0.301925376.2",
    x^6 + 14*x^4 + 43*x^2 + 36,
    -301925376, 11, [* 2 *]
*], [* "6.0.1389928896.1",
    x^6 - 3*x^5 + 9*x^4 + 4*x^3 + 12*x^2 + 84*x + 236,
    -1389928896, 11, [* 4 *]
*], [* "6.0.1621833984.1",
    x^6 - 2*x^5 + x^4 - 4*x^3 + 5*x^2 - 50*x + 125,
    -1621833984, 11, [* 2, 2 *]
*], [* "6.0.2217513608.1",
    x^6 + 29*x^4 + 246*x^2 + 512,
    -2217513608, 11, [* *]
*], [* "6.0.3630586487.2",
    x^6 - 3*x^5 + 10*x^4 + 8*x^3 + x^2 + 90*x + 236,
    -3630586487, 11, [* 2, 2 *]
*], [* "6.0.5471265024.1",
    x^6 + 21*x^4 + 60*x^2 + 4,
    -5471265024, 11, [* 2, 2 *]
*], [* "6.0.7577297408.1",
    x^6 + 30*x^4 + 169*x^2 + 200,
    -7577297408, 11, [* 2, 2 *]
*], [* "6.0.9961636864.3",
    x^6 + 23*x^4 + 112*x^2 + 36,
    -9961636864, 11, [* 2 *]
*], [* "6.0.11959609600.1",
    x^6 - 2*x^5 + 12*x^4 - 44*x^3 + 242*x^2 - 672*x + 1224,
    -11959609600, 11, [* 2, 6 *]
*], [* "6.0.12672320000.1",
    x^6 + 26*x^4 + 177*x^2 + 128,
    -12672320000, 11, [* 2, 2 *]
*], [* "6.0.15600166848.1",
    x^6 + 29*x^4 + 226*x^2 + 252,
    -15600166848, 11, [* 4 *]
*], [* "6.0.52289804287.1",
    x^6 - 2*x^5 - 7*x^4 + 45*x^3 - 63*x^2 - 162*x + 729,
    -52289804287, 11, [* 2, 2 *]
*], [* "6.0.52986843648.1",
    x^6 - 2*x^5 + 11*x^4 + 42*x^3 - 11*x^2 + 340*x + 950,
    -52986843648, 11, [* 2, 4 *]
*], [* "6.0.54014775983.1",
    x^6 - 3*x^5 + 29*x^4 - 53*x^3 + 200*x^2 - 174*x + 71,
    -54014775983, 11, [* 2, 6 *]
*] ];

//data := [ data[i] : i in [1..#data] | not i in [ 4, 7, 11 ] ];
fs := [ datum[2] : datum in data ];

function DescendIdeal(J, ZZK, h)
/* Descends ideal J in ZZL to ZZK under inclusion given by h */

ZZL := Order(J); BK := Basis(ZZK); BJ := Basis(J);
/* Take integral bases of ZZK as well as J */
MK := Matrix(Integers(), [ Eltseq(ZZL ! h(b)) : b in BK ]);
MJ := Matrix(Integers(), [ Eltseq(b) : b in BJ ]);
LatK := Lattice(MK);
LatJ := Lattice(MJ);

/* Intersect and solve relevant equations */
LatI := LatK meet LatJ;
MI := Matrix(Basis(LatI));
sol := Solution(MK, MI);
rows := [ Eltseq(row) : row in Rows(sol) ];
I := ideal< ZZK | [ &+[ row[i]*BK[i] : i in [1..#BK] ] : row in rows ] >;

/* Check and return */
IL := ideal< ZZL | [ h(gen) : gen in Generators(I) ] >;
assert J eq IL;
return I;

end function;

prec := 1000; precred := 300;
inds := [ ind : ind in [1..#fs] | not ind in [ 4, 7, 11 ] ];
inds := [ 14 ];
for B in [1..31] do
    for ind in inds do
        f := fs[ind];
        /* Create CM field and totally real subfield */
        F := RationalsExtra(prec); R := PolynomialRing(F);
        K := NumberFieldExtra(R ! f); CC := K`CC;
        test, tup, invK := IsCMField(K);
        K0, hK0K := Explode(tup);

        /* Create rings of integers */
        ZZK := Integers(K); ZZK0 := Integers(K0);
        /* Create class groups */
        ClK, phiClK := ClassGroup(ZZK); ClK0, phiClK0 := NarrowClassGroup(ZZK0);

        nClK := NumberOfGenerators(ClK);
        infsK := InfinitePlaces(K);
        gensClK := [ MakeSmallClassRepresentative(phiClK(ClK.i), infsK : precred := precred) : i in [1..nClK] ];

        /* First restrict to classes of ideals for which aa aabar is principal in K0 */
        gensh1 := [ ];
        for i in [1..nClK] do
            aa := gensClK[i];
            aabar := ideal< ZZK | [ invK(genaa) : genaa in Generators(aa) ] >;
            aaaabar0 := DescendIdeal(aa*aabar, ZZK0, hK0K);
            genh1 := aaaabar0 @@ phiClK0;
            Append(~gensh1, genh1);
        end for;
        h1 := hom< ClK -> ClK0 | gensh1 >;
        G2 := Kernel(h1);

        //print "";
        //print ind;
        //print ClK;
        //print G2;

        aas := IdealsUpTo(B, ZZK);
        cls := [ aa @@ phiClK : aa in aas ];
        cls := { cl : cl in cls | cl in G2 };

        print "";
        print B;
        print #cls;
        print #G2;
    end for;
end for;
