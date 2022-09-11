% generating command: chabagen -n -l 100 -a 20 -mco 2 -h 70 -rph 1 3 -lpb 0 7 -apb 0 7 a12
% number of literals in alphabet: 100
% number of assumptions: 20
% number of non-assumptions: 80
% maximum number of assumptions literals contrary of: 2
% number of distinct rule heads: 70
% minimum number of rules per head: 1
% maximum number of rules per head: 3
% minumum number of literals in bodies: 0
% maxumum number of literals in bodies: 7
% minimum number of assumptions per body: 0
% maximum number of assumptions per body: 7

% alphabet: { a0, b0, c0, d0, e0, f0, g0, h0, i0, j0, k0, l0, m0, a1, b1, c1, d1, e1, f1, g1, n0, o0, p0, q0, r0, s0, t0, u0, v0, w0, x0, y0, z0, n1, o1, p1, q1, r1, s1, t1, u1, v1, w1, x1, y1, z1, n2, o2, p2, q2, r2, s2, t2, u2, v2, w2, x2, y2, z2, n3, o3, p3, q3, r3, s3, t3, u3, v3, w3, x3, y3, z3, n4, o4, p4, q4, r4, s4, t4, u4, v4, w4, x4, y4, z4, n5, o5, p5, q5, r5, s5, t5, u5, v5, w5, x5, y5, z5, n6, o6 }
% nonAssumptions: { n0, o0, p0, q0, r0, s0, t0, u0, v0, w0, x0, y0, z0, n1, o1, p1, q1, r1, s1, t1, u1, v1, w1, x1, y1, z1, n2, o2, p2, q2, r2, s2, t2, u2, v2, w2, x2, y2, z2, n3, o3, p3, q3, r3, s3, t3, u3, v3, w3, x3, y3, z3, n4, o4, p4, q4, r4, s4, t4, u4, v4, w4, x4, y4, z4, n5, o5, p5, q5, r5, s5, t5, u5, v5, w5, x5, y5, z5, n6, o6 }
% ruleHeads: { u1, s3, u3, x3, x2, x4, r0, t3, r1, p3, t5, n3, w3, u4, w1, z4, y4, q5, w2, p1, t4, q3, w4, q4, r3, s5, s0, z5, v4, w0, u0, v5, o6, w5, n0, n4, o3, t1, x1, y0, p2, y5, p0, z3, s4, o2, s2, z0, s1, q0, o5, p5, n5, o4, r2, u2, r4, y3, o1, x0, n6, v3, n2, p4, z2, x5, v0, r5, q1, y1 }

toBeProved([y1]).

myAsm(a0).
myAsm(b0).
myAsm(c0).
myAsm(d0).
myAsm(e0).
myAsm(f0).
myAsm(g0).
myAsm(h0).
myAsm(i0).
myAsm(j0).
myAsm(k0).
myAsm(l0).
myAsm(m0).
myAsm(a1).
myAsm(b1).
myAsm(c1).
myAsm(d1).
myAsm(e1).
myAsm(f1).
myAsm(g1).

contrary(a0, v0).
contrary(b0, e1).
contrary(c0, u0).
contrary(d0, k0).
contrary(e0, n4).
contrary(f0, z0).
contrary(g0, q5).
contrary(h0, z0).
contrary(i0, w0).
contrary(j0, q1).
contrary(k0, q0).
contrary(l0, r3).
contrary(m0, o2).
contrary(a1, u5).
contrary(b1, s0).
contrary(c1, r3).
contrary(d1, p1).
contrary(e1, e0).
contrary(f1, o4).
contrary(g1, o1).

myRule(u1, [b1, g1, i0, d0, j0, f1, f0]).
myRule(u1, [l0, c1, b1, c0, e1, g1, f1]).
myRule(s3, [u1, d0, g1, j0, f1]).
myRule(u3, [d1, g1, g0, e1, s3, b0]).
myRule(u3, [u1, f1, s3]).
myRule(u3, [a1, h0, e1, j0, u1, k0, a0]).
myRule(x3, [d1, e0, u3, k0, m0]).
myRule(x3, [i0, s3, e1, u1, u3, d1, d0]).
myRule(x2, [x3, c1, g1, b1]).
myRule(x2, [i0, e0, g1, a1, c0, u3]).
myRule(x4, [g0, s3, b1]).
myRule(r0, [x2, u1, s3, x3, u3]).
myRule(r0, [g0, a0, c0, l0, u3]).
myRule(r0, [u1, x3]).
myRule(t3, [h0, g0, j0, l0, a0, x4, d1]).
myRule(r1, [x4, a0, s3, x2, u3]).
myRule(r1, [b0, k0, d0, a1, c1, f1, a0]).
myRule(p3, [d1, x3, t3, g0, u3]).
myRule(p3, [k0, b0, f0, b1, m0, t3, d1]).
myRule(t5, [m0, f0, d1, b1, k0, b0]).
myRule(t5, [h0]).
myRule(t5, [m0, e0]).
myRule(n3, [c1, g0, a0, p3, k0]).
myRule(w3, [k0, b1, f1, a0]).
myRule(u4, [d1, e1, n3, u3]).
myRule(u4, [g0, a0, g1, t3, e1]).
myRule(w1, [f1, x4]).
myRule(w1, [m0, e1]).
myRule(w1, [g1]).
myRule(z4, [u3, m0, w3, u4]).
myRule(y4, [a1, w3, d0, k0, l0, w1, f1]).
myRule(q5, [n3, t3, l0, j0, d0, d1, m0]).
myRule(q5, [j0, x3, y4, n3, u1]).
myRule(w2, [e1, n3, x2]).
myRule(w2, [p3, x2, s3, g1]).
myRule(p1, [l0]).
myRule(p1, [g1, c1, b1, m0]).
myRule(p1, [q5, x4, i0, w3, x2, g0]).
myRule(t4, [a1, f1, c1, m0, r1, d0]).
myRule(t4, [g1, r1, m0, k0, e1, u3, b0]).
myRule(q3, [x2, e1, t5, k0, y4, f0, f1]).
myRule(q3, []).
myRule(q3, [d1, p3, w3, h0, g1, u4]).
myRule(w4, [w1, w2, g0, x3, c1, e1, e0]).
myRule(w4, [u3, z4, w1, u1, x3, y4]).
myRule(q4, [t5, d0, p1, x3, q3]).
myRule(q4, [z4, r1, k0]).
myRule(q4, []).
myRule(r3, [z4, y4, c0, d0, u3]).
myRule(r3, [t4, r1]).
myRule(r3, [y4, u1, r1, x3, w4, m0]).
myRule(s5, [c1, l0, d0, i0, r3]).
myRule(s5, [w3, e1, f0]).
myRule(s5, [j0, g1]).
myRule(s0, []).
myRule(s0, [e1]).
myRule(s0, [e0]).
myRule(z5, [z4]).
myRule(z5, [q3, l0, k0, g1, w3, r1, s0]).
myRule(z5, [g1, r3]).
myRule(v4, [g0, e0, m0, i0, d0, a1, k0]).
myRule(v4, [e1]).
myRule(v4, [m0]).
myRule(w0, [u3, s5, t3, x2, y4]).
myRule(u0, [g1]).
myRule(u0, [s5, v4, z5]).
myRule(u0, [k0, b0, v4, g0, m0, d1]).
myRule(v5, [f1]).
myRule(v5, [a1, p3, e0, b1, f1, x2]).
myRule(v5, [p3, x2, a0, g1, i0]).
myRule(o6, [w0, p3, r1, r3, z4, u0, q5]).
myRule(o6, [u4, w1, k0, r0, q4]).
myRule(o6, [j0, i0, p1, e1, t5, k0]).
myRule(w5, [d0, a1, f0, j0, f1, h0]).
myRule(n0, [a0, r0, f0, w2, u0, w5, t5]).
myRule(n0, [s0, w4, r1, z4, t4]).
myRule(n4, [h0]).
myRule(n4, [t5]).
myRule(n4, [u0]).
myRule(o3, [c0, g0, m0, b1]).
myRule(t1, [j0, e0, b0, c0, f1, h0, w0]).
myRule(t1, [t3, i0, u1, x2, s0, x4]).
myRule(x1, []).
myRule(x1, [g0, j0, c0, b1]).
myRule(x1, [d0, r3]).
myRule(y0, [f0, b1, w2, n0, w1, o6]).
myRule(y0, [u3, m0, v4]).
myRule(y0, []).
myRule(p2, [x4, y4, q4]).
myRule(y5, [v4]).
myRule(p0, [y4, u3]).
myRule(p0, [b1, j0, y0, w4, g0, t3, x4]).
myRule(p0, [a1, r3]).
myRule(z3, [j0, x2, o3, h0, l0, p1, k0]).
myRule(z3, [d0]).
myRule(z3, [x4]).
myRule(s4, [h0, q5, s5, j0, e1, d1]).
myRule(s4, [w2, m0]).
myRule(o2, [t4]).
myRule(o2, [e0]).
myRule(s2, [u1, a1, y5, n0, x1, t5]).
myRule(s2, [p2, s0, u3, x1, s5, d0, s4]).
myRule(s2, [o3, k0, c0, d1, i0, p3, f0]).
myRule(z0, [a0, d0]).
myRule(z0, []).
myRule(z0, [k0]).
myRule(s1, [a0, c0, s4]).
myRule(q0, [t4, v4, p3, w3, u0, n0]).
myRule(q0, [s2, h0, s4, p1, n3, f0]).
myRule(q0, [e1, a0, o3, s3, x2, f1]).
myRule(o5, []).
myRule(p5, [p0, t5, q4, s4, u3]).
myRule(p5, []).
myRule(n5, [p5, j0]).
myRule(n5, [t4, s5, v4, t3, p5, u0, o5]).
myRule(n5, [g0]).
myRule(o4, [w0, s3]).
myRule(o4, [l0, s3]).
myRule(r2, [b0, k0, c1]).
myRule(r2, [n0]).
myRule(u2, [y0, w3, o5, o6, w5]).
myRule(u2, [d0, c0, a1, d1, b0, a0, i0]).
myRule(u2, [h0, c1]).
myRule(r4, [m0, r3, w0, i0, b0, c0]).
myRule(r4, [e1]).
myRule(y3, [m0, e0, h0, b1, c1, e1]).
myRule(y3, [a1, y0, y4, k0]).
myRule(o1, [n5, c0, a1, h0, y0, b1, d0]).
myRule(o1, [b0]).
myRule(x0, [p5, z4, t3, o6]).
myRule(x0, [y5, b0, j0, x2, d0]).
myRule(n6, [w5, r4, e0, g1]).
myRule(v3, [k0, u1, e0]).
myRule(n2, [z5, s3]).
myRule(p4, [b0]).
myRule(z2, [c1, v4, n4, g0]).
myRule(x5, [o5, o2, n4, n2]).
myRule(x5, [w3, i0]).
myRule(x5, [s4, b1, u4, o4]).
myRule(v0, [n0, p1, w5, z3, e1, w4]).
myRule(r5, []).
myRule(r5, [p4, j0, k0, a1]).
myRule(r5, [o5, u4, f0]).
myRule(q1, [e0, d0, f0, d1, t1, r2]).
myRule(y1, [b0]).
myRule(y1, [q1, p0, x3, t4, w3]).
