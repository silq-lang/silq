namespace Solution
{
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Extensions.Math;
    open Microsoft.Quantum.Extensions.Testing;
    open Microsoft.Quantum.Extensions.Diagnostics;

    // operation SolveTest() : Unit 
    // {
    //     using (qs = Qubit[2])
    //     {
    //         Solve(qs);

    //         DumpRegister((), qs);

    //         ResetAll(qs);
    //     }
    // }

    operation Solve (qs : Qubit[]) : Unit 
    {
        Ry(ArcCos(Sqrt(2.0 / 3.0)) * 2.0, qs[1]);

        X(qs[1]);
        (Controlled H)([qs[1]], qs[0]);
        X(qs[1]);
    }
}