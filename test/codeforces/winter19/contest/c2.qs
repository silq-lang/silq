namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation EvaluatePeriodClauses (queryRegister : Qubit[], periodAncillas : Qubit[]) : Unit {
        body (...) {
            let N = Length(queryRegister);
            for (period in 1 .. Length(periodAncillas)) {
                // Evaluate the possibility of the string having period K.
                // For each pair of equal qubits, CNOT the last one into the first one.
                for (i in 0..N-period-1) {
                    CNOT(queryRegister[i + period], queryRegister[i]);
                }

                // If all pairs are equal, the first N-K qubits should be all in state 0.
                (ControlledOnInt(0, X))(queryRegister[0..N-period-1], periodAncillas[period-1]);

                // Uncompute
                for (i in N-period-1..-1..0) {
                    CNOT(queryRegister[i + period], queryRegister[i]);
                } 
            }
        }

        adjoint auto;
    }

    operation Solve (x : Qubit[], y : Qubit) : Unit {
        body (...) {
            // Try all possible periods and see whether any of them produces the necessary string
            // The result is OR on the period clauses
            let N = Length(x);
            // Valid periods are from 1 to N-1, so N-1 ancillas
            using (anc = Qubit[N - 1]) {
                EvaluatePeriodClauses(x, anc);
                (ControlledOnInt(0, X))(anc, y);
                X(y);
                Adjoint EvaluatePeriodClauses(x, anc);
            } 
        }
        adjoint self;
    }
}