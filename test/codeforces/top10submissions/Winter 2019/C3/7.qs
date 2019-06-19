namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation multThree (qs : Qubit[], div : Int, yy : Qubit) : Unit {
    body (...) {
    
        if(Length(qs) == 1)
        {
            if(div == 0)
            {
                X(qs[0]);
                CNOT(qs[0], yy);
                X(qs[0]);
            }
            elif(div == 1)
            {
                CNOT(qs[0], yy);
            }
        }
        else
        {
            Controlled multThree(qs[Length(qs)-1..Length(qs)-1], (qs[0..(Length(qs)-2)], (div+2)%3, yy));
            X(qs[Length(qs)-1]);
            Controlled multThree(qs[Length(qs)-1..Length(qs)-1], (qs[0..(Length(qs)-2)], div, yy));
            X(qs[Length(qs)-1]);
        }
        }
        adjoint invert;
        controlled distribute;
        controlled adjoint distribute;
    }
    operation Solve (x : Qubit[], y : Qubit) : Unit {
        body (...) {
            multThree(x, 0, y);
        }
        adjoint auto;
    }
}