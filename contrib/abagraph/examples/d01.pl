% generating command: chabagen -n -l 150 -a 30 -mco 2 -h 90 -rph 1 3 -lpb 0 7 -apb 0 7 d01
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
% ruleHeads: { u0, r8, p4, s3, x5, r0, t2, n6, r1, v3, o0, z2, u4, s0, n5, v6, w5, p2, o2, q5, y5, o6, q7, x1, s6, o7, t4, q3, v5, p8, y0, x0, n0, p9, w3, u8, y2, u5, w8, p3, x3, p6, u1, n7, r2, q8, t3, s5, r6, x2, n4, o3, t7, p5, o9, r3, s1, z3, v8, u7, p0, x6, u6, r4, w0, p7, v4, u2, v7, s4, q0, s2, z4, u3, z6, t8, t1, y6, q2, n2, t6, w2, z5, n9, z1, o1, y7, z0, v1, n1 }

toBeProved([n1]).

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

contrary(a0, v6).
contrary(b0, x5).
contrary(c0, d2).
contrary(d0, t6).
contrary(e0, p4).
contrary(f0, n1).
contrary(g0, w4).
contrary(h0, l0).
contrary(i0, n0).
contrary(j0, p4).
contrary(k0, i1).
contrary(l0, o3).
contrary(m0, c1).
contrary(a1, a0).
contrary(b1, v8).
contrary(c1, v5).
contrary(d1, d0).
contrary(e1, z7).
contrary(f1, x0).
contrary(g1, c2).
contrary(h1, u0).
contrary(i1, q3).
contrary(j1, w4).
contrary(k1, e0).
contrary(l1, m0).
contrary(m1, x3).
contrary(a2, e0).
contrary(b2, b0).
contrary(c2, s6).
contrary(d2, n5).

myRule(u0, [c1]).
myRule(r8, [f1, u0, c0]).
myRule(p4, [g1, r8, j1, u0]).
myRule(s3, []).
myRule(x5, [b1, d0, d1, p4, s3]).
myRule(r0, [e0]).
myRule(t2, [r0, s3]).
myRule(t2, [d2, d1, g0, g1, j0]).
myRule(t2, [r8, x5, b2, u0, r0]).
myRule(n6, [h1]).
myRule(r1, [s3, u0, x5, a1, r0]).
myRule(r1, [x5, g1]).
myRule(v3, [b0, g0, g1, a0, n6]).
myRule(o0, [c0, a1, c1]).
myRule(o0, [f0, n6, i1]).
myRule(z2, []).
myRule(z2, [f1, g0, h1, f0]).
myRule(z2, [j0, r1, r8, l0, m0, a1, o0]).
myRule(u4, [b2, d1, l1, c0, m1, j0, e0]).
myRule(u4, []).
myRule(s0, [d0, a2, f0, a0, k0, s3]).
myRule(s0, [z2]).
myRule(s0, [b1, j0, d0]).
myRule(n5, [a0, d0, c1, e1, a2]).
myRule(v6, [a0, m0, a2, c0]).
myRule(w5, [i0, d1, c0]).
myRule(w5, [v6, i0, o0, h1, r8]).
myRule(w5, [g0, h0, i1]).
myRule(p2, [j0, w5, e1, t2]).
myRule(p2, [i0, c1, e1]).
myRule(o2, [g0, e0]).
myRule(o2, [x5, v3]).
myRule(o2, []).
myRule(q5, []).
myRule(q5, [u0, s3, n5]).
myRule(y5, [b2, o2, v3, a0, z2]).
myRule(y5, [i1, i0]).
myRule(y5, [j0, j1]).
myRule(o6, [v3, d0, z2, p2, q5]).
myRule(q7, [c2, s3, n6, d0, w5, x5]).
myRule(x1, [l1, d0, f0, c1, f1, h1]).
myRule(x1, [e1, b2, a1, m1, e0, o2, r0]).
myRule(x1, [v6]).
myRule(s6, [d1, c2, a1, l1]).
myRule(o7, [b2, r1]).
myRule(t4, [l1, h1, a2, m0, m1, g0, d2]).
myRule(q3, [g1, p2, t4, v3]).
myRule(q3, [q7, q5, r8, u0]).
myRule(v5, [x5, s6, b1, q7]).
myRule(v5, [q3, x1, p4, o0, g1, z2]).
myRule(v5, [q3, o2]).
myRule(p8, [h0, p4, q3, n6]).
myRule(p8, []).
myRule(p8, [w5, s0, s6]).
myRule(y0, [f1, y5]).
myRule(y0, [w5, p4, l1, b1]).
myRule(y0, [t2, p8, c1, n6, r1, o7, q3]).
myRule(x0, [r1, v6, l0]).
myRule(n0, [r1]).
myRule(n0, [w5, o0, o2, q3, n6, s6, q5]).
myRule(n0, [o2]).
myRule(p9, [p4, i0, q3, d0, a2, m1]).
myRule(w3, [l1, b1, e0, j0, t4, j1]).
myRule(w3, []).
myRule(w3, [h0, b0, d0]).
myRule(u8, [c1, c2, e1]).
myRule(y2, [e1, i0, g1, h1]).
myRule(u5, [t4, n6, f1, q5]).
myRule(w8, [r8, r0, p4, i1, c2, g0]).
myRule(p3, [g1, l0, x0, v6, n6, i0]).
myRule(p3, [p9, v5, z2, f0]).
myRule(x3, [i1, l1, d2, h1, w8, q7]).
myRule(p6, [q3, s6, h1]).
myRule(p6, [z2, r1, g1, p3, e1]).
myRule(u1, [p4, u0, v5, o6, s0, w8]).
myRule(n7, [q5]).
myRule(n7, [a1, b2]).
myRule(r2, [p9, o0, o7, p2, u0, p8, w3]).
myRule(q8, [b1, r8, v6, h1, l0]).
myRule(q8, [u4, r1, p4, y5, v6, n0]).
myRule(t3, [w8, g0, u8, v5, q7]).
myRule(t3, [g0, e1, a0, l0, b2, i0, a1]).
myRule(t3, [p4, p9, f0, l0, c2]).
myRule(s5, []).
myRule(s5, [t3, x5, l0, w5, r8, g1]).
myRule(r6, []).
myRule(r6, [x3, o6, r8, c2, x5]).
myRule(x2, [h1, d0]).
myRule(x2, [v3, u5]).
myRule(x2, []).
myRule(n4, [e1, a0]).
myRule(o3, [f1, t4, r0]).
myRule(o3, [c0, e0, i0, d1]).
myRule(o3, []).
myRule(t7, []).
myRule(t7, [r1]).
myRule(t7, [w8, j1]).
myRule(p5, [x1, u4, i1, x5, j1]).
myRule(p5, [x1, w5]).
myRule(o9, [g1]).
myRule(o9, [u5, o6, u4, r1, s6]).
myRule(o9, [o0, q3, x5]).
myRule(r3, [c2, x2]).
myRule(s1, []).
myRule(s1, [c1, a0, h0, b1]).
myRule(s1, [e1, s0]).
myRule(z3, [b1, l0, l1, g1]).
myRule(v8, [x0, c0, x1, u0, b2, t2, p8]).
myRule(v8, [x3, a1]).
myRule(v8, [s5, q8, c2, w5, g0, r3]).
myRule(u7, [x3, q7, n6, t4, p4, r6]).
myRule(u7, [k0, f0, y5, l0, l1, e1, h1]).
myRule(p0, [p8, f1]).
myRule(x6, [p4, t7, x1, o7, r0, t3, v3]).
myRule(u6, []).
myRule(u6, [a2, k1, h0, e1, m1]).
myRule(r4, [c1, k1]).
myRule(r4, [o3, q5, u6, c1]).
myRule(w0, [l0, e0, m0, d0, s0, f1, b2]).
myRule(w0, [j0]).
myRule(w0, [h0, n5, o2, p9, l0, z2, o0]).
myRule(p7, [d1]).
myRule(p7, [v6, u0, p3, i1]).
myRule(v4, [v3, t4, n4, r2]).
myRule(u2, [o3, n7, p0, y0, p5, s3]).
myRule(u2, [f0, i0, b2, f1, d1, u4]).
myRule(u2, [v8, w0, b1, m1, v6, u4, p4]).
myRule(v7, [u1, o2, q8, x6, o3]).
myRule(v7, [u7]).
myRule(s4, [m1, e1, v8, g1]).
myRule(s4, [p0]).
myRule(q0, [z2, v4, i1]).
myRule(q0, [o0]).
myRule(s2, []).
myRule(z4, [s3, s5, r4, o2]).
myRule(z4, [p0, e1, v8, q8]).
myRule(z4, [h0, c1]).
myRule(u3, [p9, b2]).
myRule(u3, [d2, c0, h0, z3, q8]).
myRule(z6, [i1]).
myRule(t8, [e1, b0, l1, x1, c2, u0, f1]).
myRule(t1, [c2, u4, d1, b0, t4, i1]).
myRule(y6, [x1, r8, z2, h0, x0, j1, b0]).
myRule(y6, [e1, c2, j0, m1, h1]).
myRule(y6, []).
myRule(q2, [r4, d1, s6, x6, r6, f1, t1]).
myRule(n2, [v8, t8, o3, q2, u5, p0, t2]).
myRule(n2, [f0, c0, a2, g0, m1, h0]).
myRule(t6, [i0, c1, a2]).
myRule(t6, [i0]).
myRule(w2, [c0, d2, g0, t6, k0]).
myRule(w2, [l0, p6, g0, d2, i0]).
myRule(z5, [m0, o3]).
myRule(z5, [n7, a2, j1, q7, x6]).
myRule(n9, [q3, o3, r4, q8]).
myRule(n9, [x0, s5]).
myRule(n9, [c0, m1, i0, g0, b0]).
myRule(z1, []).
myRule(z1, [i0, t2, l1, t7, b0, y6]).
myRule(z1, [b1, t7, p8, z5, q0, s6, y0]).
myRule(o1, [m1, f1]).
myRule(y7, []).
myRule(z0, [z1, s0]).
myRule(v1, [t8, j1, m1, b0, a2, x1]).
myRule(v1, [m1, r0, c1, i0, i1, b1]).
myRule(v1, [v4, u4, a2]).
myRule(n1, [x5]).
myRule(n1, [f1, l1]).
