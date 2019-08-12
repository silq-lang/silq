def solve() {
    (q0, q1) := vector(2,false:𝔹);

    done := false:!𝔹;
    while !done {
        measure((q0, q1));
        (q0, q1) := vector(2,false:𝔹);

        q := false:𝔹;
        q0 := H(q0); q1 := H(q1);
        if q0 && q1 {
            q := X(q);
        }
        if !measure(q) {
            done = true;
        }
    }

    return (q0, q1);
}
