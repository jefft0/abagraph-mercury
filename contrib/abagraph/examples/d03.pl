% generating command: chabagen -n -l 150 -a 30 -mco 2 -h 90 -rph 1 3 -lpb 0 7 -apb 0 7 d03
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
% ruleHeads: { n1, s5, t2, x8, z6, o8, v8, v3, z3, v6, p9, w5, q8, p1, r0, u0, y2, n3, s1, r7, o9, s7, u8, p6, s3, z2, r8, t4, w6, t3, z4, u6, s6, q2, t6, x5, q5, q4, x4, p5, p2, s0, y3, v5, o1, y1, z7, v7, v1, s4, n0, v2, o0, s8, t5, z1, r1, q6, o2, r3, z0, y4, y7, w0, n4, p7, n9, w8, n8, q0, x6, p3, n6, q1, u7, p8, x7, p4, u2, r2, v4, q7, r6, o6, n5, o4, u3, p0, x3, o7 }

toBeProved([o7]).

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

contrary(a0, z0).
contrary(b0, r8).
contrary(c0, t2).
contrary(d0, s4).
contrary(e0, v0).
contrary(f0, n2).
contrary(g0, e1).
contrary(h0, q4).
contrary(i0, y1).
contrary(j0, w7).
contrary(k0, r8).
contrary(l0, o3).
contrary(m0, q3).
contrary(a1, e0).
contrary(b1, o6).
contrary(c1, y5).
contrary(d1, u8).
contrary(e1, h1).
contrary(f1, z2).
contrary(g1, o5).
contrary(h1, b2).
contrary(i1, s7).
contrary(j1, r3).
contrary(k1, v7).
contrary(l1, q3).
contrary(m1, c2).
contrary(a2, q0).
contrary(b2, z8).
contrary(c2, z3).
contrary(d2, e1).

myRule(n1, [k1, g1]).
myRule(n1, []).
myRule(n1, [j0, c0, c2, a2, l0, m0, b2]).
myRule(s5, []).
myRule(s5, [d1, e1, f0, c1, a1, m1]).
myRule(s5, [d2, b0, k1]).
myRule(t2, [h1, d1]).
myRule(x8, [s5]).
myRule(z6, [x8, s5]).
myRule(z6, [t2, n1, s5, m0]).
myRule(o8, [g0, l0, x8, d0, g1]).
myRule(v8, [x8, f0, d2, b2]).
myRule(v8, [s5, o8, n1, t2, k0, x8, z6]).
myRule(v3, [t2, x8, s5]).
myRule(z3, [v8, e0, z6]).
myRule(v6, [i1]).
myRule(v6, [v8, a1, n1, z3, h0]).
myRule(v6, [l1, j1]).
myRule(p9, [v6, z3, x8]).
myRule(p9, [s5, n1, z6, l1, v8]).
myRule(p9, [g0, f0, h1, a2]).
myRule(w5, []).
myRule(w5, [b2, p9, a0, v3, n1, v6, a2]).
myRule(w5, [f0, s5, c1, f1, e1, z6]).
myRule(q8, [d1, c0, d2, n1, h0]).
myRule(q8, [c0, j0, h0]).
myRule(q8, [f1, c0, l1, h0, c2]).
myRule(p1, [x8, f0]).
myRule(p1, [p9]).
myRule(p1, [z6, k0, l0]).
myRule(r0, [k1]).
myRule(r0, [x8, q8, z6, o8, s5, t2]).
myRule(u0, [t2, r0]).
myRule(u0, [v6, q8, z6, o8, v3, k0]).
myRule(u0, []).
myRule(y2, [v8, t2, s5, d0, q8, u0, z3]).
myRule(n3, []).
myRule(n3, [c0, s5, z6, l1, h1]).
myRule(n3, [u0, n1]).
myRule(s1, []).
myRule(s1, [b0, t2]).
myRule(s1, [n3]).
myRule(r7, []).
myRule(o9, [m1, d1]).
myRule(s7, [q8, p1, z3, y2, s1, o9, n1]).
myRule(u8, [o9, w5, z6, s7, o8]).
myRule(u8, [d2, v3, b1, k0, g1, v8]).
myRule(p6, [f0, t2, n1, c0, g0, c1]).
myRule(p6, [r0, v6]).
myRule(p6, [b1, c0, p1, s7, z6]).
myRule(s3, [m1, s1]).
myRule(s3, [v3, p1, t2]).
myRule(s3, [r0, r7, h1, l0, e1, u8]).
myRule(z2, [c0]).
myRule(z2, [p6]).
myRule(r8, [p6, t2]).
myRule(r8, [e1, l1, c1, d2, f0]).
myRule(r8, [p1, s7, u8, z3, c2]).
myRule(t4, []).
myRule(t4, [m0, s7, u8]).
myRule(t4, [a0]).
myRule(w6, []).
myRule(w6, [j1]).
myRule(w6, [u0, o9, g1]).
myRule(t3, [v6, m1, v3, n1]).
myRule(z4, []).
myRule(z4, [d0]).
myRule(z4, [e1, t4, m1]).
myRule(u6, [q8, m1, g0, x8, y2, c2]).
myRule(u6, [g1]).
myRule(u6, []).
myRule(s6, [i1]).
myRule(q2, [l1, e1, d0, m1]).
myRule(t6, [i0, t2, y2, b0, z6, j0, c1]).
myRule(x5, [v8, s7]).
myRule(q5, [l1, k1, h1, m1, k0, j1, c1]).
myRule(q5, [o8, r7, s1, x5, q8]).
myRule(q5, []).
myRule(q4, [s5, t3, a0, g0, x5, s7, c1]).
myRule(q4, [l0, k1, q2]).
myRule(q4, [v6, i1]).
myRule(x4, [y2, t2, s1, r0, z4, p1]).
myRule(p5, [g1, c0, l0, m1]).
myRule(p5, [z2, d0, u8, n3, q8]).
myRule(p2, [d0, b2, c1, l0]).
myRule(s0, []).
myRule(y3, [i0, s1, h1, k1]).
myRule(v5, [r0]).
myRule(o1, [q2, m0, h0]).
myRule(o1, [i0, f0, p1, v8]).
myRule(o1, [q4, v8, u0]).
myRule(y1, [d0, a1, j1, e0, k1]).
myRule(z7, [c1, u8, k1]).
myRule(z7, [b1, d1, w6, g1, m0, a2]).
myRule(v7, [o9, d0, u0, c0, t2]).
myRule(v1, [c0, e1, o1, t6]).
myRule(v1, []).
myRule(s4, [g1]).
myRule(n0, [b2, d1, b1]).
myRule(v2, [x8, m0, q2, n3, j0, b0, a0]).
myRule(o0, []).
myRule(o0, [m0, j1, c0, c2]).
myRule(o0, [r8, t4, p9, v3, s1]).
myRule(s8, [c1]).
myRule(s8, [u6, v7, s5, q5, q2, z3, s1]).
myRule(t5, [b1, f0, a2, a1, v3, z2, b2]).
myRule(t5, []).
myRule(t5, [h1, m0, l0, k1, c1, x5, b1]).
myRule(z1, [l0, d2, e1, q5, g0, d1]).
myRule(z1, [s4, b0, d0, y2, v1]).
myRule(r1, [l1, z4]).
myRule(r1, []).
myRule(q6, []).
myRule(q6, [v8, q5, u0, y1, v6, r7]).
myRule(o2, [h0, n1, b1]).
myRule(o2, [y3, t6]).
myRule(o2, [j0, k0]).
myRule(r3, [s3, r7, s4, y2, p5]).
myRule(r3, [a2, g1, o2, v3, u8, s5]).
myRule(z0, [d1, e1, g1]).
myRule(y4, [r7, z7, x5, k0, l0, e1]).
myRule(y4, [e1, h1, b1, i1, m0, c1]).
myRule(y4, [c2]).
myRule(y7, [q8, p1, o2, s0]).
myRule(y7, [x4, g0, r3, p6, y3, h0, i0]).
myRule(y7, [t3, o1, z3]).
myRule(w0, [e1, j1, i1, u8, b1, f0, s8]).
myRule(n4, [o1, w0, l1, y2]).
myRule(n4, [c2, k0, b1, j0, h0, b0, g0]).
myRule(n4, [v5, d0, e1]).
myRule(p7, [l0, g0, i0]).
myRule(n9, [m1, i1]).
myRule(w8, [d1, s4]).
myRule(w8, [h1, j1, b1]).
myRule(n8, [p1, s1, b0, z7]).
myRule(n8, [f0, j0, f1, b0, k0, c1, l1]).
myRule(q0, [t4, k0, c1]).
myRule(q0, [p1, t4, c0, o0]).
myRule(x6, [z6, r0, v8, p1, l0, s5, z3]).
myRule(p3, [q0]).
myRule(p3, [b1, b2, t4]).
myRule(p3, [s5]).
myRule(n6, [d0, k1]).
myRule(q1, []).
myRule(u7, [n9, y2]).
myRule(u7, [c2, o9]).
myRule(u7, [k1, m0, m1, c2]).
myRule(p8, [t3, k0]).
myRule(p8, [q8, s8, p6, h1, z3, r3, s0]).
myRule(p8, [k0, f0, k1, i1, p3]).
myRule(x7, [t6]).
myRule(p4, [c0, s6]).
myRule(p4, [i1, s1, c0, s6, l0, i0]).
myRule(u2, []).
myRule(u2, [j1, k1, n8, s6]).
myRule(u2, [o0, y7, f1, s8]).
myRule(r2, [h1, y3, r8, y4, s6]).
myRule(v4, []).
myRule(v4, [e1, j0, j1, f0]).
myRule(v4, [k1, z7, p6]).
myRule(q7, [p3, s1]).
myRule(r6, [a2, f1]).
myRule(r6, [e0, j0, b0]).
myRule(o6, []).
myRule(o6, [s5, d1, g1, n9, c1, q4]).
myRule(o6, [z4]).
myRule(n5, [n8, b2, x5, f1]).
myRule(o4, [k0, f1, c2, m0, v4, h0]).
myRule(u3, [d2, u8, s1]).
myRule(u3, [d2, c0, k0, t4]).
myRule(u3, [o9, z6, j0, t4, z1, p7]).
myRule(p0, [l1, e0]).
myRule(p0, [a2, w8, m1, k0, i1, c2, h0]).
myRule(p0, [c1, g0]).
myRule(x3, [j1, e0, b2, a1, d0, q2]).
myRule(x3, []).
myRule(x3, [o4, u6]).
myRule(o7, [c1, s0, z2, v3, g0, b1]).
myRule(o7, [e0, l0, k1]).
