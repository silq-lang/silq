namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (x : Qubit[], y : Qubit) : Unit {
        body (...) {
            let n = Length(x);
            for (l in 1 .. n / 2) {
                for (i in 0 .. (1 <<< l) - 1) {
                    mutable good = true;
                    for (ll in 1 .. l / 2) {
                        if (((i ^^^ (i >>> (l - ll))) &&& ((1 <<< ll) - 1)) == 0) {
                            set good = false;
                        }
                    }
                    if (good) {
                        (ControlledOnInt(i + (i <<< l), X))(x[0 .. l - 1] + x[n - l .. n - 1], y);
                    }
                }
            }
        }
        adjoint self;
    }
}