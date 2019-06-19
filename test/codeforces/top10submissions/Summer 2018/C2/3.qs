namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (q : Qubit) : Int
    {
        body
        {
            mutable result = -2;
            using (register = Qubit[1]) {
                let q1 = register[0];
                H(q1);
                (Controlled H)([q1], q);
                let work = M(q);
                if (work == Zero) {
                    set result = -1;
                }
                else {
                    let k = M(q1);
                    set result = 1 - ResultAsInt([k]);
                }
                ResetAll(register);
            }
            return result;
        }
    }
}