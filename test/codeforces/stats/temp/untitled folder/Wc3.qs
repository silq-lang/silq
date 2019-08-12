namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;
    operation AddBitsMod3 (queryRegister : Qubit[], ancillaRegister : Qubit[]) : Unit {
        body (...) {
            let sum = ancillaRegister[0];
            let carry = ancillaRegister[1];
            for (q in queryRegister) {
                // we need to implement addition mod 3:
                // bit sum carry | sum carry
                //  1   0    0   |  1    0
                //  1   1    0   |  0    1
                //  1   0    1   |  0    0
                // compute sum bit
                (ControlledOnBitString([true, false], X))([q, carry], sum);
                // bit sum carry | carry
                //  1   1    0   |   0
                //  1   0    0   |   1
                //  1   0    1   |   0
                (ControlledOnBitString([true, false], X))([q, sum], carry);
            }
        }

        adjoint auto;
    }

    operation Solve (x : Qubit[], y : Qubit) : Unit {
        body (...) {
            // Allocate two ancillas and implement a mini-adder on them:
            // add each qubit to one of the ancillas,
            // using the second one as a "carry".
            // If both qubits end up in 0 state, the number of 1s is divisible by 3.
            using (anc = Qubit[2]) {
                WithA(AddBitsMod3(x, _), (ControlledOnInt(0, X))(_, y), anc);
            }
        }
        adjoint auto;
    }
}