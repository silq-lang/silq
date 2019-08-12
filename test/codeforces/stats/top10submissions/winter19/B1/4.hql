def prepare(q0:𝔹, q1:𝔹, q2:𝔹) mfree {
    q0 := rotY(acos(1./sqrt(3.))·2, q0);
    if q0{
        q1 := H(q1);
        if q1{
            q2 := X(q2);
        }
        q1 := X(q1);
    }
    q0 := X(q0);
    if q1 {
        phase(2·π/3);
    }
    if q2 {
        phase(4·π/3)
    }
    return (q0, q1, q2)
}

def solve(q0:𝔹, q1:𝔹, q2:𝔹) {
    (q0, q1, q2) := reverse(prepare)(q0, q1, q2);
    return if measure(q0, q1, q2) == vector(3,0:!𝔹) {0} else {1};
}
