namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    // Helper function for Embedding_Perm: finds first location where bit strings differ.
    function FirstDiff (bits1 : Bool[], bits2 : Bool[]) : Int {
        for (i in 0 .. Length(bits1)-1) {
            if (bits1[i] != bits2[i]) {
                return i;
            } 
        }
        return -1; 
    }

    // Helper function for Embed_2x2_Operator: performs a Clifford to implement a base change
    // that maps basis states index1 to 111...10 and index2 to 111...11
    //(in big endian notation, i.e., LSB in qs[n-1])
    operation Embedding_Perm (index1 : Int, index2 : Int, qs : Qubit[]) : Unit {
        body (...) {
            let n = Length(qs);
            let bits1 = BoolArrFromPositiveInt(index1, n);
            let bits2 = BoolArrFromPositiveInt(index2, n);
            // find the index of the first bit at which the bit strings are different
            let diff = FirstDiff(bits1, bits2);
    
            // we care only about 2 inputs: basis state of bits1 and bits2
    
            // make sure that the state corresponding to bits1 has qs[diff] set to 0
            if (bits1[diff]) {
                X(qs[diff]);
            }
            
            // iterate through the bit strings again, setting the final state of qubits
            for (i in 0..n-1) {
                if (bits1[i] == bits2[i]) {
                    // if two bits are the same, set both to 1 using X or nothing
                    if (not bits1[i]) {
                        X(qs[i]);
                    }
                } else {
                    // if two bits are different, set both to 1 using CNOT
                    if (i > diff) {
                        if (not bits1[i]) {
                            X(qs[diff]);
                            CNOT(qs[diff], qs[i]);
                            X(qs[diff]);
                        }
                        if (not bits2[i]) {
                            CNOT(qs[diff], qs[i]);
                        }
                    }
                }
            }

            // move the differing bit to the last qubit
            if (diff < n-1) {
                SWAP(qs[n-1], qs[diff]);
            } 
        }
        adjoint auto;
    }

    // Helper function: apply the 2x2 unitary operator at the sub-matrix given by indices
    operation Embed_2x2_Operator (U : (Qubit => Unit : Controlled),
                                  index1 : Int, index2 : Int, qs : Qubit[]) : Unit {
        Embedding_Perm(index1, index2, qs);
        (Controlled U)(Most(qs), Tail(qs));
        (Adjoint Embedding_Perm)(index1, index2, qs);
    }

    operation Solve (qs : Qubit[]) : Unit {
        let n = Length(qs);
        for (i in 2^n-2..-1..0) {
            Embed_2x2_Operator(H, i, i+1, qs);
        }
    }
}