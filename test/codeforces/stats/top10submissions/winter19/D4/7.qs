namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation sub1(qs : Qubit[]) : Unit {
    body (...) {
    
        if(Length(qs) == 1)
        {
            X(qs[0]);
        }
        else
        {
            X(qs[0]);
            Controlled sub1(qs[0..0], qs[1..(Length(qs)-1)]);
        }
        }
        adjoint invert;
        controlled distribute;
        controlled adjoint distribute;
    }

    operation add1(qs : Qubit[]) : Unit {
    body (...) {
    
        if(Length(qs) == 1)
        {
            X(qs[0]);
        }
        else
        {
            Controlled add1(qs[0..0], qs[1..(Length(qs)-1)]);
            X(qs[0]);
        }
        }
        adjoint invert;
        controlled distribute;
        controlled adjoint distribute;
    }

    operation Solve (qs : Qubit[]) : Unit {
        for(i in 0..Length(qs)-2)
        {
            X(qs[i]);
        }
        Controlled add1(qs[Length(qs)-1..Length(qs)-1], qs[0..Length(qs)-2]);
        X(qs[Length(qs)-1]);
        Controlled sub1(qs[Length(qs)-1..Length(qs)-1], qs[0..Length(qs)-2]);
        X(qs[Length(qs)-1]);
            for(i in 1..Length(qs)-1)
            {
                CNOT(qs[0], qs[i]);
            }
            H(qs[0]);
            for(i in 1..Length(qs)-1)
            {
                CNOT(qs[0], qs[i]);
            }
    }
}