load "D6/results.m";
load "D6/fields.m";
Q := NumberField(x^2 + 1);
counter := 0;
for tup in L do
    f := data[tup[1]][2];
    K := NumberField(f);
    if IsSubfield(Q, K) then
        counter +:= 1;
    else
        print K;
    end if;
end for;
print counter;
