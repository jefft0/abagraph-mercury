% generating command: chabagen -n -l 150 -a 30 -mco 2 -h 90 -rph 1 3 -lpb 0 7 -apb 0 7 d02
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
% ruleHeads: { r5, p8, o8, v7, w4, s5, n9, z6, u1, q3, n5, t3, r2, y4, y7, z8, s4, w6, v1, r0, r4, p3, w8, y1, x6, v5, r8, y2, u6, y6, v3, w1, u5, z5, w0, p2, q7, s6, y8, v0, s7, q4, z2, z1, p0, r3, w3, t1, u3, t5, q5, v6, o4, o9, q0, q2, x0, o5, w2, w5, s1, x4, p5, n4, u2, x2, x7, t8, t7, q6, u0, x5, y5, o6, o7, o1, y0, q1, p6, x8, p1, q8, v8, z4, r1, y3, z7, r6, s3, u7 }

toBeProved([u7]).

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

contrary(a0, r4).
contrary(b0, s1).
contrary(c0, y3).
contrary(d0, p3).
contrary(e0, c0).
contrary(f0, x2).
contrary(g0, v0).
contrary(h0, x3).
contrary(i0, y8).
contrary(j0, s8).
contrary(k0, e0).
contrary(l0, w5).
contrary(m0, t0).
contrary(a1, f0).
contrary(b1, x1).
contrary(c1, g1).
contrary(d1, z7).
contrary(e1, p9).
contrary(f1, d0).
contrary(g1, y2).
contrary(h1, v5).
contrary(i1, s1).
contrary(j1, y6).
contrary(k1, v2).
contrary(l1, m0).
contrary(m1, h1).
contrary(a2, t1).
contrary(b2, s8).
contrary(c2, o7).
contrary(d2, w4).

myRule(r5, [l1, h1, f0]).
myRule(r5, [b2, j1, e1]).
myRule(p8, [d2, m0, l0, g0, l1]).
myRule(o8, [r5, c0, p8]).
myRule(o8, [j1, c2, g1, l0, a2, h1, g0]).
myRule(o8, [r5, m1]).
myRule(v7, [m0, a1]).
myRule(v7, []).
myRule(v7, [h1, h0, m0, b2, a2, i0]).
myRule(w4, [p8, v7, o8, m1, r5]).
myRule(w4, [o8, p8, v7, d1, e1, f0, r5]).
myRule(s5, [o8, w4, p8, v7]).
myRule(n9, [h1, w4, a2, v7]).
myRule(n9, []).
myRule(n9, [e1, c0, g1, s5, g0, o8, i0]).
myRule(z6, [a0, a2, l0, s5]).
myRule(u1, [c0, i1, a0]).
myRule(q3, [r5, w4]).
myRule(q3, [k1, g1]).
myRule(n5, [c1, p8, z6]).
myRule(n5, [k0, d0, q3, f1, c1, f0]).
myRule(n5, [s5]).
myRule(t3, []).
myRule(t3, [b0, m1, h1]).
myRule(t3, [k0, p8, a0, n5, s5, l0, n9]).
myRule(r2, [k1, n5]).
myRule(r2, [t3, l0]).
myRule(y4, [r5]).
myRule(y4, [s5]).
myRule(y7, [t3, y4, w4]).
myRule(z8, []).
myRule(s4, [n5, a2, j0, t3, w4, i1, u1]).
myRule(s4, [e1, i0, e0, i1, q3]).
myRule(s4, [r2, e0, o8, y7, h1]).
myRule(w6, [b0, q3, s5, n9, r5, f1, y4]).
myRule(w6, [g0, e0, y7, h0, k0, t3]).
myRule(v1, [y7, n5, f1]).
myRule(v1, []).
myRule(v1, [b2, v7]).
myRule(r0, [z8, y7, c2, v7, v1, y4, r5]).
myRule(r0, [u1, o8, p8, c0, m1, c1]).
myRule(r4, [n5, a1]).
myRule(r4, [t3, n9, u1, e1, w4]).
myRule(r4, [y7, p8, t3, s4]).
myRule(p3, []).
myRule(p3, [j0]).
myRule(w8, [j1, s5, u1]).
myRule(w8, [z8, p8]).
myRule(y1, [j0]).
myRule(y1, [e1]).
myRule(y1, [a0, c0, t3, i1, w6]).
myRule(x6, [m0, b0, v1, l1]).
myRule(x6, [r0, p3, i1, e1]).
myRule(x6, [v1, z8, q3]).
myRule(v5, [f0, h1, b0, c2]).
myRule(r8, [v1, p3, h0]).
myRule(y2, [k0, w6, d2, c2]).
myRule(u6, [x6, v7, r5]).
myRule(u6, [y2, s4, c1, r0, w4, r5, p3]).
myRule(y6, [s5, r4, z8]).
myRule(v3, [v7, y2, c0, p3, c1]).
myRule(w1, [d0, h0, h1, m1, e1, g1, e0]).
myRule(w1, [r4, i1, y2, t3, w6]).
myRule(u5, [n5, r2, o8]).
myRule(u5, [w1, t3, g0]).
myRule(u5, [v1]).
myRule(z5, [v3, g1, k0]).
myRule(z5, [p8, l1, i1, a0, b2]).
myRule(w0, [c0, w8, o8]).
myRule(p2, [n5]).
myRule(p2, [e1]).
myRule(q7, [g1, m1, w0, r8, i1, z5]).
myRule(q7, [r8]).
myRule(s6, [c0, m0, k1, g1, l1, u6, w6]).
myRule(s6, [s4, w0, o8, q7]).
myRule(y8, [c2]).
myRule(y8, []).
myRule(y8, [s6, x6, v7, z8, q3, v1, u6]).
myRule(v0, [e0]).
myRule(v0, [v1, u5, w1, r8]).
myRule(s7, [m1, z8, g0, n5]).
myRule(q4, []).
myRule(q4, [y1, z8, y7, z6]).
myRule(q4, [k0, s6, p2, r8]).
myRule(z2, [l1, a2, j1, m0, j0, f0, h1]).
myRule(z2, [d2, a1, b0, g0]).
myRule(z1, [s5, p2, p3, w0]).
myRule(z1, []).
myRule(p0, [w4, l1, i1, j1, d0, z8]).
myRule(r3, [b0, k0, p0, r2, u1]).
myRule(r3, [r0, o8, c0, p3]).
myRule(r3, [y1, u5]).
myRule(w3, [r4, p2, q3]).
myRule(w3, [a1, g1, a0, p0, e0]).
myRule(w3, [q3, s4, b1, w1]).
myRule(t1, [u1, p3, q3, b2, c0, v1]).
myRule(u3, [p3, g1, y1, v1, z6]).
myRule(u3, [o8, y6, g1]).
myRule(t5, [j0, e0, d1, r8, b1, k0, h0]).
myRule(t5, [p8]).
myRule(t5, [i0, d0, h1]).
myRule(q5, [d2, e1, w0, q7, l1, z5, h0]).
myRule(v6, [x6, s6, k0, a2, b1]).
myRule(o4, [z2]).
myRule(o4, [u5, v6, v7, z6, r8, y6]).
myRule(o4, [a1, r8, t3, q4, r0]).
myRule(o9, [q7, b1, e0, i0]).
myRule(o9, []).
myRule(q0, []).
myRule(q0, [i0, w4, s6, w0, n5, r2]).
myRule(q2, [r8, v6]).
myRule(q2, [y7, t3, h0, w4, y1, n5, j1]).
myRule(x0, [u3, c2, a0, g0, d0, k1, w1]).
myRule(x0, [m0, u5, v1, y1, g0, p0, d1]).
myRule(x0, [v1, l1, q2, c1]).
myRule(o5, [n5, r0, o4, r3, t1, u1]).
myRule(w2, [u1, r2, y2]).
myRule(w5, [r0, z8, u6, u5, f1, a2]).
myRule(w5, [d0, u3, d2, e0]).
myRule(w5, [k0, h1, w2]).
myRule(s1, [q4, o4, w5, l0, t3, b1]).
myRule(s1, [a0, z6, i0, z5, i1, v3, w2]).
myRule(x4, [d2]).
myRule(p5, [e0, d1, s7, h0, f1]).
myRule(n4, [m1, c2, a1, y7, f0, n5, y4]).
myRule(n4, [l1, x4, p3, y2, g1]).
myRule(n4, [i0, c2, h1, v1, c1]).
myRule(u2, [m0]).
myRule(u2, [s5, r0, p2, r3, u1, o9, q0]).
myRule(u2, []).
myRule(x2, [k0, r4, z8, a2, n5, p0]).
myRule(x2, [b1, b2, h0, c1, a1]).
myRule(x2, [p5, s5]).
myRule(x7, [p0, t1, u5, y8, p3, v7]).
myRule(x7, [a2, t1]).
myRule(t8, [c0, h0]).
myRule(t8, [z5, f0, u1, c1, c0, k0, h0]).
myRule(t7, [t5, u2, g0]).
myRule(q6, [i1, b0, u5, h1, t8]).
myRule(q6, [b1, a2, y1, i1, i0, a1, f1]).
myRule(u0, [i1, f1]).
myRule(x5, [x7, t1, x4, i1, w1, q5]).
myRule(x5, [y8]).
myRule(x5, [q4, a2, b2, w0, q6, y1, r0]).
myRule(y5, [d2, v6, f0, q7, t3, f1]).
myRule(o6, [m1, h0, s5, e1, h1, m0]).
myRule(o6, []).
myRule(o6, [o5, c0, m1, a2, b0]).
myRule(o7, [y4, q3, z2, z8, q2, x0]).
myRule(o7, [a2, v3]).
myRule(o7, [s1, q4, w2, j0, n4]).
myRule(o1, []).
myRule(o1, [u1, u6, b1, p5, c1, r3]).
myRule(y0, [t8, n4, z1, z5, j1, o4]).
myRule(y0, [x4, r0, o4, y5, n4]).
myRule(y0, [m1, h1, t7, q3]).
myRule(q1, []).
myRule(q1, [a0, y8, f0, b0, j1]).
myRule(q1, [v5, v0, x2, r4, e1]).
myRule(p6, [c1]).
myRule(p6, [r2, c1, i0, c0, b2, a1]).
myRule(x8, [g1, d1, b1, l1, q5, f0]).
myRule(x8, [d1]).
myRule(p1, [q4, x4, t3, i0, q2]).
myRule(p1, [f1]).
myRule(q8, [d2, o9, r5]).
myRule(v8, [h0, f0, v7, p8, f1, n4, z5]).
myRule(z4, []).
myRule(z4, [t3, l0, h1, e1, v3, j1]).
myRule(z4, [c0, b0]).
myRule(r1, [p5, c0, r2, q0]).
myRule(r1, [c2, q4, q6, d2, j1, i1, a2]).
myRule(r1, [g0, x5, v1, p3, a2]).
myRule(y3, [o9, d2]).
myRule(z7, [o9, m1]).
myRule(z7, [w3, b2, k0]).
myRule(r6, []).
myRule(s3, [u5, q6, z4, p2, h1]).
myRule(u7, [f0, y5, z8, w2]).
