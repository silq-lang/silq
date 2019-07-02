namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;
    
    operation Decrement (qs : Qubit[]) : Unit {
        X(qs[0]);
        for (i in 1..Length(qs)-1) {
            (Controlled X)(qs[0..i-1], qs[i]);
        } 
    }
    
    operation Reflect (qs : Qubit[]) : Unit {
        body (...) {
            ApplyToEachC(X, qs);
        }
        controlled auto;
    }
    
    operation Solve (qs : Qubit[]) : Unit {
        let n = Length(qs);
        X(qs[n-1]);
        (Controlled Reflect)([qs[n-1]], qs[0..(n-2)]);
        X(qs[n-1]);
        Decrement(qs[0..(n-2)]);
        H(qs[n-1]);
        (Controlled Reflect)([qs[n-1]], qs[0..(n-2)]);
    } 
}