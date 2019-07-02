namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;
    operation FlipAlternatingPositionBits (register : Qubit[], firstIndex : Int) : Unit {
        body (...) {
            // iterate over elements in every second position, starting with firstIndex
            for (i in firstIndex .. 2 .. Length(register) - 1) {
                X(register[i]);
            }
        }
        adjoint auto;
    }

    operation Solve (x : Qubit[], y : Qubit) : Unit {
        body (...) {
            // first mark the state with 1s in even positions,
            // then mark the state with 1s in odd positions
            for (firstIndex in 0..1) {
                FlipAlternatingPositionBits(x, firstIndex);
                Controlled X(x, y);
                Adjoint FlipAlternatingPositionBits(x, firstIndex);
            } 
        }
        adjoint auto;
    }
}