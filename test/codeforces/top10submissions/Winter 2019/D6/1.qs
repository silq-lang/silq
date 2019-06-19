namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Extensions.Diagnostics;
    open Microsoft.Quantum.Canon;

    operation Solve (qs : Qubit[]) : Unit {
        let n = Length(qs);
        for (i in (1 <<< n) - 2 .. -1 .. 0) {
            for (j in 1 .. n - 1) {
                if (((i ^^^ (i + 1)) &&& (1 <<< j)) != 0) {
                    CNOT(qs[0], qs[j]);
                }
                if (((i + 1) &&& (1 <<< j)) == 0) {
                    X(qs[j]);
                }
            }
            Controlled H(Rest(qs), qs[0]);
            for (j in 1 .. n - 1) {
                if (((i ^^^ (i + 1)) &&& (1 <<< j)) != 0) {
                    CNOT(qs[0], qs[j]);
                }
                if (((i + 1) &&& (1 <<< j)) == 0) {
                    X(qs[j]);
                }
            }
        }
    }
}