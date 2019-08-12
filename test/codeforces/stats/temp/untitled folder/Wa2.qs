namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (qs : Qubit[], bits : Bool[][]) : Unit {
        using (anc = Qubit[2]) {
            // Put the ancillas into equal superposition of 2-qubit basis states
            ApplyToEach(H, anc);
            // Set up the right pattern on the main qubits with control on ancillas
            for (i in 0 .. 3) {
                for (j in 0 .. Length(qs) - 1) {
                    if ((bits[i])[j]) {
                        (ControlledOnInt(i, X))(anc, qs[j]);
                    } 
                }
            }
            // Uncompute the ancillas, using patterns on main qubits as control
            for (i in 0 .. 3) {
                if (i % 2 == 1) {
                    (ControlledOnBitString(bits[i], X))(qs, anc[0]);
                }
                if (i / 2 == 1) {
                    (ControlledOnBitString(bits[i], X))(qs, anc[1]);
                } 
            }
        }
    }
}