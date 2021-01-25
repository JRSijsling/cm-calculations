R<x> := PolynomialRing(Rationals());
load "fields.m";

N := 24;
datas := [ [* *] : i in [1..N] ];
for i in [1..#data] do
    Append(~datas[(i mod N) + 1], data[i]);
end for;
for i in [0..(N - 1)] do
    str := "fields-" cat IntegerToString(i) cat ".m";
    PrintFileMagma(str, datas[i + 1]);
end for;

