namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (qs : Qubit[]) : Unit {
        for (i in Length(qs)-2..-1..0)
        {
            CNOT(qs[i], qs[i+1]);
        }
        H(qs[0]);
        for (i in 0..Length(qs)-2)
        {
            CNOT(qs[i], qs[i+1]);
        }
    }
}