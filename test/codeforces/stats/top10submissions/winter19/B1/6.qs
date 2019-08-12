namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation U3(qs : Qubit, a : Double, b : Double, c : Double) : Unit {
        body (...) {
            Rz(c, qs);
            Ry(a, qs);
            Rz(b, qs);
        }
        controlled auto;
        adjoint auto;
        controlled adjoint auto;
    }

    operation Solve (qs : Qubit[]) : Int {

        X(qs[0]);
        X(qs[1]);
        CCNOT(qs[0], qs[1], qs[2]);
        X(qs[0]);
        X(qs[1]);

        U3(qs[1], 0.0, 0.0, 0.0);
        (Controlled U3)(qs[1..1], (qs[0], 3.14159265358979,0.0,-3.66519142918809));
        U3(qs[0], 0.0, 0.0, -2.77555756156289e-17);
        (Controlled U3) (qs[0..0], (qs[1], 1.57079632679490,-2.87979326579064,-2.87979326579064));
        U3(qs[1], 0.0, 0.0, -2.77555756156289e-17);
        (Controlled U3)(qs[1..1], (qs[0], 1.91063323624902,0.785398163397448,1.83259571459405));
        U3(qs[0], 1.91063323624902,2.35619449019234,2.35619449019234);
        U3(qs[0], 0.0, 0.0, 0.0);
        (Controlled U3)(qs[0..0], (qs[1], 1.57079632679490,1.84889274661175e-32,9.61481343191782e-17));
        U3(qs[0], 3.14159265358979,2.74889357189107,-2.74889357189107);

        let res = M(qs[1]);
        if (res == One)
        {
            return 0;
        }
        return 1; 
    }
}