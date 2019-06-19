namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Extensions.Diagnostics;
    open Microsoft.Quantum.Canon;

    operation Solve (qs : Qubit[]) : Unit {
        let r = Rest(qs);
        Controlled MultiX([Head(qs)], r);
        H(Head(qs));
        MultiX(Most(r));
        for (i in Length(r) - 2 .. -1 .. 0) {
            Controlled X([Tail(r)] + r[0 .. i - 1], r[i]);
        }
        Controlled MultiX([Head(qs)], r);
    }
}