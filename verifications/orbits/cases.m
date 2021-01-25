S := Sym(6);
Gs := [ rec`subgroup : rec in Subgroups(S) ];
Gs := [ G : G in Gs | IsTransitive(G) ];
Gs := [ G : G in Gs | #Center(G) mod 2 eq 0 ];

GsNew := [ ];
for G in Gs do
    H := Stabilizer(G, 1);
    Z := Center(G);
    for inv in [ z : z in Z | Order(z) eq 2 ] do
        H0 := sub< G | H, inv >;
        C0 := Core(G, H0);
        if IsAbelian(C0) and Exponent(C0) eq 2 then
            Append(~GsNew, G);
            continue;
        end if;
    end for;
end for;
Gs := GsNew;
print #Gs;


