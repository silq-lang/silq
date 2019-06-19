namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation U(qs : Qubit, a : Double, b : Double, c : Double) : Unit {
        body (...) {
            Rz(c, qs);
            Ry(a, qs);
            Rz(b, qs);
        }
        controlled auto;
    }

    operation Solve (q: Qubit) : Int {
        mutable ans = 0;
        using (anc=Qubit())
        {
            Z(q);
			(Controlled U)([anc], (q, 3.14159265358979,0.0,-3.66519142918809));
			(Controlled U)([q], (anc, 1.57079632679490,-2.87979326579064,-2.87979326579064));
			(Controlled U)([anc], (q, 1.91063323624902,0.785398163397448,1.83259571459405));
			U(q, 1.91063323624902,2.35619449019234,2.35619449019234);
			(Controlled U)([q], (anc, 1.57079632679490,0.0,0.0));
			U(q, 3.14159265358979,2.74889357189107,-2.74889357189107);

            let res0 = M(q);
            let res1 = M(anc);

            if (res0 == Zero && res1 == Zero) {
                set ans = 0;
            }
            if (res0 == Zero && res1 == One) {
                set ans = 1;
                X(anc);
            }
            if (res0 == One && res1 == Zero) {
                set ans = 2;
            }
        }
        return ans;
        
    }
}