namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Extensions.Math;
    open Microsoft.Quantum.Extensions.Diagnostics;
    open Microsoft.Quantum.Canon;

    operation Solve (q : Qubit) : Int {
        H(q);
        mutable r = 0;
        using (q2 = Qubit()) {
            Controlled Ry([q], (1.9106332362490186, q2));
            S(q);
            H(q);
            set r = ResultAsInt(MultiM([q, q2]));
            Reset(q2);
        }
        return r == 1 ? 1 | (r == 0 ? 2 | 0);
    }
}