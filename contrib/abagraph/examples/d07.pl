% generating command: chabagen -n -l 150 -a 30 -mco 2 -h 90 -rph 1 3 -lpb 0 7 -apb 0 7 e02
% number of literals in alphabet: 150
% number of assumptions: 30
% number of non-assumptions: 120
% maximum number of assumptions literals contrary of: 2
% number of distinct rule heads: 90
% minimum number of rules per head: 1
% maximum number of rules per head: 3
% minumum number of literals in bodies: 0
% maxumum number of literals in bodies: 7
% minimum number of assumptions per body: 0
% maximum number of assumptions per body: 7

% alphabet: { a0, b0, c0, d0, e0, f0, g0, h0, i0, j0, k0, l0, m0, a1, b1, c1, d1, e1, f1, g1, h1, i1, j1, k1, l1, m1, a2, b2, c2, d2, n0, o0, p0, q0, r0, s0, t0, u0, v0, w0, x0, y0, z0, n1, o1, p1, q1, r1, s1, t1, u1, v1, w1, x1, y1, z1, n2, o2, p2, q2, r2, s2, t2, u2, v2, w2, x2, y2, z2, n3, o3, p3, q3, r3, s3, t3, u3, v3, w3, x3, y3, z3, n4, o4, p4, q4, r4, s4, t4, u4, v4, w4, x4, y4, z4, n5, o5, p5, q5, r5, s5, t5, u5, v5, w5, x5, y5, z5, n6, o6, p6, q6, r6, s6, t6, u6, v6, w6, x6, y6, z6, n7, o7, p7, q7, r7, s7, t7, u7, v7, w7, x7, y7, z7, n8, o8, p8, q8, r8, s8, t8, u8, v8, w8, x8, y8, z8, n9, o9, p9 }
% nonAssumptions: { n0, o0, p0, q0, r0, s0, t0, u0, v0, w0, x0, y0, z0, n1, o1, p1, q1, r1, s1, t1, u1, v1, w1, x1, y1, z1, n2, o2, p2, q2, r2, s2, t2, u2, v2, w2, x2, y2, z2, n3, o3, p3, q3, r3, s3, t3, u3, v3, w3, x3, y3, z3, n4, o4, p4, q4, r4, s4, t4, u4, v4, w4, x4, y4, z4, n5, o5, p5, q5, r5, s5, t5, u5, v5, w5, x5, y5, z5, n6, o6, p6, q6, r6, s6, t6, u6, v6, w6, x6, y6, z6, n7, o7, p7, q7, r7, s7, t7, u7, v7, w7, x7, y7, z7, n8, o8, p8, q8, r8, s8, t8, u8, v8, w8, x8, y8, z8, n9, o9, p9 }
% ruleHeads: { n6, t6, n4, w5, w3, p4, y8, p7, u1, o5, q5, y3, t7, n5, v7, x3, n3, t0, z7, q7, p9, r4, t4, p0, v5, n7, x5, n2, o8, v3, n1, s2, y2, r2, u0, o9, r1, s5, s8, x4, n9, o1, v2, q4, t5, s6, z5, t1, q0, t2, n0, w6, s7, y7, x8, p6, p8, r6, r8, u8, x1, y1, q6, n8, q1, o7, q8, v6, q2, p2, z4, v8, x0, w7, z3, y0, p1, r3, w1, t3, x6, o6, r5, w2, s1, t8, u7, w4, u3, s0 }

toBeProved([s0]).

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
myAsm(h1).
myAsm(i1).
myAsm(j1).
myAsm(k1).
myAsm(l1).
myAsm(m1).
myAsm(a2).
myAsm(b2).
myAsm(c2).
myAsm(d2).

contrary(a0, q0).
contrary(b0, n3).
contrary(c0, t6).
contrary(d0, c0).
contrary(e0, o3).
contrary(f0, t4).
contrary(g0, u0).
contrary(h0, w0).
contrary(i0, u0).
contrary(j0, h0).
contrary(k0, u1).
contrary(l0, z6).
contrary(m0, w5).
contrary(a1, z5).
contrary(b1, x8).
contrary(c1, n6).
contrary(d1, z5).
contrary(e1, k1).
contrary(f1, s4).
contrary(g1, o2).
contrary(h1, w2).
contrary(i1, r0).
contrary(j1, l0).
contrary(k1, u3).
contrary(l1, y1).
contrary(m1, w2).
contrary(a2, n9).
contrary(b2, q5).
contrary(c2, o8).
contrary(d2, s5).

myRule(n6, [b0, h0, a2, e1, d1, g1]).
myRule(t6, [n6, f0, f1, h1, l1, b1]).
myRule(n4, [n6, h1, t6]).
myRule(w5, []).
myRule(w3, []).
myRule(p4, [n4]).
myRule(p4, []).
myRule(p4, [w5, n6, w3]).
myRule(y8, [w3, n4, e0, f1, p4, k0, j0]).
myRule(p7, [n4, n6, p4, w5, t6]).
myRule(p7, [w3]).
myRule(p7, []).
myRule(u1, [w3, t6, y8, n6]).
myRule(u1, [d0, y8, c0, e1, l0]).
myRule(o5, [w5, k1]).
myRule(q5, [g1, m1, b1, m0, a0, c0, t6]).
myRule(q5, [i0]).
myRule(y3, [u1, h1, n6, p7, b1, y8, l0]).
myRule(y3, []).
myRule(t7, []).
myRule(n5, [w3, n6, d2, e1, t6, p4]).
myRule(v7, []).
myRule(x3, [k0]).
myRule(x3, [n4, n5, v7, n6, b1, a1]).
myRule(x3, [w3, i0, b2, d0]).
myRule(n3, [c0, e1, k0]).
myRule(n3, [t7, y8]).
myRule(n3, [t6]).
myRule(t0, []).
myRule(t0, [t7]).
myRule(z7, [t7, y3, x3]).
myRule(z7, []).
myRule(q7, [h1, n6, b2]).
myRule(q7, [z7, f1, w3, w5, n3, t0]).
myRule(p9, [t7, w5, w3, o5, v7, t0, p7]).
myRule(r4, [h1, p9, n4, v7, m0]).
myRule(r4, [b1, a0]).
myRule(t4, []).
myRule(t4, [f0, d0, q5]).
myRule(t4, [m1, y3, c2]).
myRule(p0, []).
myRule(v5, [j1, k1]).
myRule(n7, [x3]).
myRule(n7, [l1, i0, e0]).
myRule(x5, [l1, g0, j0]).
myRule(n2, [p9, w5, p0]).
myRule(o8, []).
myRule(v3, [t6, o8, w3, z7, y3, v5, n6]).
myRule(v3, []).
myRule(v3, [c0]).
myRule(n1, [k1, e1, d2, c0, b2, d0]).
myRule(n1, [g0, e0, d1, h1, a2]).
myRule(s2, [n3]).
myRule(s2, [x5, x3]).
myRule(s2, [w5]).
myRule(y2, [b2, a0, k1, j1, k0, a2]).
myRule(r2, [j0]).
myRule(r2, [c1, s2, o8, n5, m1, n3, a2]).
myRule(r2, [c2, r4, m1, h1]).
myRule(u0, [i1, n4, f0, j1, v7]).
myRule(o9, [e1, j1, g0, f1, m1, e0]).
myRule(r1, [l0, s2]).
myRule(r1, [m0, z7, p9, p7, j1, k0]).
myRule(s5, [e0, i1]).
myRule(s5, [n4, y2, v5, p7]).
myRule(s8, [c0, t7, u1, a0]).
myRule(x4, [y3, b0, s8, v3]).
myRule(n9, [l1]).
myRule(n9, [o9, g1, n3, s8, i0, k1, x4]).
myRule(n9, [v5]).
myRule(o1, [v3, f0]).
myRule(v2, [n6]).
myRule(v2, [n6, s5, r2]).
myRule(v2, [n3, d0, d1, s5, x3, p0, s8]).
myRule(q4, [o5, q5, p0, k0, d1, j1, t4]).
myRule(q4, []).
myRule(q4, [t0, c0, y2]).
myRule(t5, [r2, q5]).
myRule(t5, [g1, o5]).
myRule(s6, [n3, p7]).
myRule(z5, [c2]).
myRule(z5, [s8, q7, p9, r4]).
myRule(z5, [c0, k1, d1, m1]).
myRule(t1, []).
myRule(q0, [k1]).
myRule(q0, [h1, d0, a0, r4, n9, c2]).
myRule(q0, [u1, n3]).
myRule(t2, [q5, x5, f1]).
myRule(t2, [d0, z7, a1, i0]).
myRule(n0, [v2]).
myRule(n0, [c1, s5]).
myRule(n0, [n9, g0, o8, p4, k0]).
myRule(w6, [r1, p0, v7, o5, n9]).
myRule(w6, [u0, x4, c1]).
myRule(w6, [n0]).
myRule(s7, [t7, r2, s5, o8, z7, a2]).
myRule(s7, [l0, k1]).
myRule(s7, [p4, t1, t5]).
myRule(y7, [k1]).
myRule(y7, [o1, h1, d2, d1, x5, m1]).
myRule(x8, [c1, r4, o8, i0, y8, a0]).
myRule(x8, [n7, o1, n0, g1, k1]).
myRule(x8, [a1, k1]).
myRule(p6, [f1, b1, g0]).
myRule(p6, [p4, l0, n1]).
myRule(p6, [k0, w3, p7, y2, t2]).
myRule(p8, [b0, a1, c2, k1, i1, i0]).
myRule(p8, [d2, t6, d0, k0, t5, g1, c1]).
myRule(p8, [p4, u1, v5]).
myRule(r6, [b0, a0, x4]).
myRule(r8, [d0]).
myRule(r8, [c1, n1]).
myRule(r8, []).
myRule(u8, [t1, r2, t2]).
myRule(u8, [u1, d0, n5, k1, y8, q0]).
myRule(x1, [c1, k0, m1, p8]).
myRule(x1, [g1, e1, d2, m0, b2]).
myRule(y1, [g0, p0, x3, e0]).
myRule(y1, []).
myRule(y1, [b1, x8, m0, l0, s2, b2, h1]).
myRule(q6, [t7, s7, x4, r8, o8, k0, e0]).
myRule(n8, [i1, b2, m1, k1, b1]).
myRule(q1, [e0, i1, s8, s7, b0]).
myRule(q1, [y8, r2, y3, a1, n6, q4, n8]).
myRule(o7, [b0, g0, z5, m1, u1]).
myRule(o7, [a2, t4, d1, d2, q0, n6]).
myRule(q8, [s6, b2, y3, x4, h1]).
myRule(v6, [l0, r1]).
myRule(v6, [i0]).
myRule(v6, [p7, t2, s7, x4, t0]).
myRule(q2, [n6, w6, o7]).
myRule(q2, [t0, d0, c2, a1]).
myRule(p2, [n0, a1, i0, x3, m1, f0, c0]).
myRule(p2, [n1, t6, c1, g1, b0, g0]).
myRule(p2, [m1, l1, c2, k1, h0]).
myRule(z4, [o5, n2, n8, n6]).
myRule(v8, [n1, n7]).
myRule(v8, [q1]).
myRule(x0, [r6, q7, q5, t6, u1, n8, j1]).
myRule(x0, [c1, p6, g1]).
myRule(w7, [b1, t5, h0, p2, q8, u0, x1]).
myRule(w7, []).
myRule(z3, [f1, q6, e0, p7, b2]).
myRule(z3, []).
myRule(z3, [j1, i0, h1, g0]).
myRule(y0, [q0, l1]).
myRule(p1, [g0, n3, t1, p2, y8, o1]).
myRule(r3, [j0, n9, s5]).
myRule(r3, [q8, m1, q0]).
myRule(r3, [h1, e1]).
myRule(w1, [e1, y1, a2, c2, k0]).
myRule(w1, [j0, n3, c0, m1, p4]).
myRule(w1, [l0]).
myRule(t3, [c2, d1, y8, d2, p4, m1]).
myRule(t3, [g0, b0, d1, i0, f0, q4, f1]).
myRule(t3, [u0, x1, g0, v7, p1]).
myRule(x6, [a0, d1, j0, s2, c1, x0]).
myRule(o6, [y2, n2, t3, z7]).
myRule(r5, [v2]).
myRule(r5, [q8]).
myRule(r5, [c2, m0]).
myRule(w2, [t5, o9, k0]).
myRule(w2, [y2]).
myRule(s1, [u8, n5]).
myRule(s1, [m1, b0]).
myRule(s1, []).
myRule(t8, [f0, e0, m1, i1, g0, f1]).
myRule(t8, [r2, i1, n8]).
myRule(u7, [f1, f0, m1, m0, e0, l0]).
myRule(w4, [r2, p1, k0, w3, c1, o5, t0]).
myRule(u3, [a0, b2, m0, a2]).
myRule(u3, [r4, y1]).
myRule(s0, [l0, e1]).
