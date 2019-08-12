namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    // operation Set (desired: Result, q1: Qubit) : ()
    // {
    //     body
    //     {
    //         let current = M(q1);
    //         if (desired != current) { X(q1); }
    //     }
    // }

    operation Solve (q : Qubit) : Int
    {
        body
        {
            Ry(3.1415926535/4.0,q);
            if (M(q) == Zero) {
                return 0;
            } else {
                return 1;
            }
        }
    }
}