namespace Solution
{
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Extensions.Math;
    open Microsoft.Quantum.Extensions.Testing;
    open Microsoft.Quantum.Extensions.Diagnostics;

    // operation SolveTest() : Unit 
    // {
    // }

    operation Solve (x : Qubit[], y : Qubit) : Unit {
        body (...) 
        {
            let l = Length(x);

            for (i in 0 .. l-1) {
                if (i % 2 == 0) {
                    X(x[i]);
                }
            }

            (Controlled X)(x, y);

            for (i in 0 .. l-1) {
                X(x[i]);
            }

            (Controlled X)(x, y);

            for (i in 0 .. l-1) {
                if (i % 2 == 1) {
                    X(x[i]);
                }
            }
        }

        adjoint self;
    }
}