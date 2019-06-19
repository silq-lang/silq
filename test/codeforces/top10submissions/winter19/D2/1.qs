namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (qs : Qubit[]) : Unit {
        for (i in 1 .. Length(qs) - 1) {
            (ControlledOnInt(1, ApplyToEachCA(H, _)))(qs[i .. Length(qs) - 1], qs[0 .. i - 1]);
        }
    }
}