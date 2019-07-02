namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;
    operation Solve (qs : Qubit[]) : Unit {
        body (...) {
            let N = Length(qs);
            // for N = 1, we need an identity
            if (N > 1) {
                // do the bottom-right quarter
                ApplyToEachCA(Controlled H([Tail(qs)], _), Most(qs));
                // do the top-left quarter by calling the same operation recursively
                (ControlledOnInt(0, Solve))([Tail(qs)], Most(qs));
            } 
        }
        adjoint auto;
        controlled auto;
        controlled adjoint auto;
    }
}