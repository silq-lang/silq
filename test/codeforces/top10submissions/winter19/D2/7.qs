namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (qs : Qubit[]) : Unit {
        for(i in 0..(Length(qs)-2))
        {
            for(j in 0..(Length(qs)-2-i))
            {
                Controlled H(qs[Length(qs)-i-1..Length(qs)-1], qs[j]);
            }
            X(qs[Length(qs)-i-1]);
        }
        for(i in 1..Length(qs)-1)
        {
            X(qs[i]);
        }
    }
}