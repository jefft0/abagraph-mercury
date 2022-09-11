% generating command: chabagen -n -l 100 -a 20 -mco 2 -h 70 -rph 1 3 -lpb 0 7 -apb 0 7 a13
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
% ruleHeads: { o1, r3, q3, p5, u5, s0, o5, o0, p4, y2, r2, u3, x1, x2, o3, t1, w1, v2, v0, o2, x5, s2, v4, r1, n4, w2, y3, z1, w3, s1, y0, s4, z3, p3, r5, n3, q0, v5, x0, w4, t0, t4, o4, s5, r4, n1, t5, q2, x3, y4, p0, t3, q5, z4, p1, n6, w5, q4, q1, u1, u0, u4, t2, z5, v3, w0, y1, p2, u2, r0 }

toBeProved([r0]).

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

contrary(a0, t2).
contrary(b0, x3).
contrary(c0, u0).
contrary(d0, t4).
contrary(e0, f0).
contrary(f0, r3).
contrary(g0, w2).
contrary(h0, p0).
contrary(i0, b1).
contrary(j0, u1).
contrary(k0, e1).
contrary(l0, w3).
contrary(m0, v5).
contrary(a1, u0).
contrary(b1, k0).
contrary(c1, u5).
contrary(d1, u1).
contrary(e1, r2).
contrary(f1, n5).
contrary(g1, x5).

myRule(o1, [a0, h0, k0, g0]).
myRule(r3, [o1, b0]).
myRule(r3, [o1]).
myRule(q3, [r3, e0, m0, a0, k0, o1, l0]).
myRule(q3, [r3, k0, o1, c1]).
myRule(p5, []).
myRule(p5, [o1, r3]).
myRule(p5, [h0, c1, e0, l0]).
myRule(u5, [l0, r3]).
myRule(u5, [p5]).
myRule(s0, [o1, e1, q3]).
myRule(o5, []).
myRule(o5, [i0, f1, m0]).
myRule(o5, [c1]).
myRule(o0, [u5]).
myRule(o0, [u5, c1]).
myRule(p4, [u5, o0, i0, f0, s0, l0, e1]).
myRule(p4, []).
myRule(p4, [o0, e1, o5, o1, u5, f1]).
myRule(y2, [q3, u5, r3, o0, s0, p5, p4]).
myRule(y2, []).
myRule(r2, [o1, y2, q3, o0, o5, u5, p4]).
myRule(r2, [h0, r3, d0, b0, a0, f1]).
myRule(u3, [o1, o5]).
myRule(x1, [i0, m0, f0]).
myRule(x1, [p4, r2]).
myRule(x2, [f1, p5]).
myRule(x2, [o0]).
myRule(x2, [h0]).
myRule(o3, [i0, k0, f0, p5, e1, c0, c1]).
myRule(t1, [r2, a0, x2, s0]).
myRule(t1, [a1, l0, g0, h0, a0, j0, b1]).
myRule(w1, [q3, u3, y2, u5, f0]).
myRule(w1, [r3, q3]).
myRule(w1, [o3, m0, c1, o0, a1, g1, k0]).
myRule(v2, [g1]).
myRule(v0, [r3]).
myRule(o2, [o5, o1, r2]).
myRule(o2, [o5, p5, r3, l0, a1, c0]).
myRule(x5, [c0, o0, m0, e1, o1]).
myRule(x5, [b1]).
myRule(x5, [s0]).
myRule(s2, [a1, r2, e1, o1, b0, a0, o5]).
myRule(s2, [q3, x2, p5]).
myRule(s2, [c0, f0, m0, e0]).
myRule(v4, [g1, x2, r2, u5, m0, d0]).
myRule(v4, [u5, v0, e1, t1]).
myRule(r1, [v4, o0, o2, q3, x5, t1]).
myRule(r1, []).
myRule(n4, [o2, v2, p4, r2, s2, v4, r1]).
myRule(w2, []).
myRule(y3, [x5, b1, c1]).
myRule(z1, [a0, j0, b1, l0]).
myRule(w3, [a0, c1, d0, c0, e1]).
myRule(w3, [z1]).
myRule(s1, [c0, u3, j0, b1, x2, f1]).
myRule(s1, [r1, s0, u3, z1, e1]).
myRule(y0, [y3, q3]).
myRule(y0, []).
myRule(y0, [a1, d0, f0, v0]).
myRule(s4, [r1, w2, t1, r2, s1, u3, q3]).
myRule(s4, [d0]).
myRule(s4, [f1, x5, g1, r2, k0]).
myRule(z3, [v0, v4]).
myRule(z3, [x5, r2, y2, z1, i0]).
myRule(p3, []).
myRule(p3, [c1, m0]).
myRule(r5, [f0, g1, s4, d1, x2, h0, c0]).
myRule(r5, []).
myRule(n3, [r5, w2, n4, u5, f0, x5, c0]).
myRule(q0, [x5, v0, n4]).
myRule(q0, [g0, h0, e1, d0, c1, f0]).
myRule(v5, [p3]).
myRule(x0, [w3, v0, z3, r2, a1]).
myRule(x0, [o5, z3, s0]).
myRule(w4, [j0]).
myRule(w4, [d0, w1, o3]).
myRule(t0, []).
myRule(t0, [y3, j0, i0, e1, g0, b0]).
myRule(t0, [v2, x5, f1, c1, j0, c0, a0]).
myRule(t4, [f0, n4, p5, d0, f1, g0, j0]).
myRule(t4, [f1, k0, i0, l0, h0, c1]).
myRule(t4, []).
myRule(o4, [a0, o0, g1]).
myRule(s5, [x2, b0, r1, n3, b1, o3]).
myRule(r4, [s4, v5, x0]).
myRule(r4, [g0, f0, k0, h0, s1, r1, c1]).
myRule(n1, [b1, j0]).
myRule(n1, [w4, g0, i0, n3, y2]).
myRule(n1, [l0, b1, d1, d0, f0, k0, h0]).
myRule(t5, []).
myRule(t5, [u3, l0, b1, w4, y3, e0]).
myRule(t5, [o1, n1, x5, b1, w4, l0]).
myRule(q2, [b1, h0, f1, w2, r3, b0]).
myRule(q2, [s2, w1]).
myRule(q2, [y2, o0]).
myRule(x3, [t1, t4, e0, v2, e1, f1]).
myRule(x3, []).
myRule(x3, [b0, m0, s4, g1]).
myRule(y4, [n1, z1, x2, w3, x1, v4, u5]).
myRule(p0, []).
myRule(t3, [t4, y2, n4, g0]).
myRule(t3, [g1, k0, e1]).
myRule(t3, [m0, c1, l0, e1, f1]).
myRule(q5, [f0, x3, u3, e0, z3, o3, x0]).
myRule(q5, [e0, b1, a1, a0, i0]).
myRule(q5, [d0, a0, c0, c1]).
myRule(z4, [r4, k0]).
myRule(p1, [n3, m0, o5, s1]).
myRule(p1, [h0, v4, o0, a1, x3, t0, j0]).
myRule(p1, []).
myRule(n6, [w3, o2, g1]).
myRule(w5, []).
myRule(q4, [c0, o3, f1, h0, c1, t0, b0]).
myRule(q1, [e0, a0, g0, i0, x5, b0, b1]).
myRule(q1, [j0, c1, s1, k0]).
myRule(u1, [y4, y0, w3]).
myRule(u1, [s1, z4, q0]).
myRule(u1, [b0, e0, a1, m0, b1, g0, c1]).
myRule(u0, [v0, o1, w2, r3, t0]).
myRule(u4, [b1, w4, a0, z1, u3]).
myRule(t2, [b0, w3, e0, f0, f1, l0]).
myRule(t2, [i0, w5, p0, t0, o5]).
myRule(z5, [q4, u5, s4]).
myRule(v3, [z1, d0, h0, w1, c1, u4, g0]).
myRule(v3, [b0, q2, m0, b1, f1]).
myRule(w0, [s4, w5, x1]).
myRule(y1, [h0]).
myRule(y1, [c0, a0, f0, a1, q2, v0]).
myRule(y1, [u3, r5, f1, w1, z1]).
myRule(p2, [a0]).
myRule(u2, [p3, o1, x3, q0]).
myRule(r0, [e1, p2]).
myRule(r0, [u1, q0, y0, y2]).
