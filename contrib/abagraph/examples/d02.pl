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
% ruleHeads: { o3, r8, w6, o9, o4, p7, y1, y5, y7, x5, y6, s5, u8, t2, z6, v1, n7, q5, v4, t3, z3, t4, v5, s1, v2, y4, w3, u6, r1, t8, y2, p3, u7, n9, r3, u3, n0, z7, n4, n5, u4, r6, p8, o6, o7, p1, s4, z2, p9, w4, n2, w8, r2, x0, v3, q4, x1, o1, p6, y8, s7, o8, p2, t7, u2, q8, x2, v6, u0, z4, w5, w7, r7, u1, s3, o0, p4, y3, q2, v8, t6, w2, o2, v0, q0, n1, x8, x7, w1, t1 }

toBeProved([t1]).

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

contrary(a0, x7).
contrary(b0, f1).
contrary(c0, k0).
contrary(d0, q7).
contrary(e0, x0).
contrary(f0, o4).
contrary(g0, x8).
contrary(h0, p4).
contrary(i0, n9).
contrary(j0, b0).
contrary(k0, w2).
contrary(l0, c1).
contrary(m0, z6).
contrary(a1, w0).
contrary(b1, p4).
contrary(c1, n1).
contrary(d1, p4).
contrary(e1, e0).
contrary(f1, x7).
contrary(g1, p9).
contrary(h1, p7).
contrary(i1, q1).
contrary(j1, r3).
contrary(k1, o8).
contrary(l1, v2).
contrary(m1, n2).
contrary(a2, u5).
contrary(b2, t7).
contrary(c2, t3).
contrary(d2, j1).

myRule(o3, [g1, e0, h1, i0, d1]).
myRule(r8, [m0, l1, l0, o3]).
myRule(w6, [r8, o3, i1]).
myRule(w6, [d1, e1, r8, b2, a1, o3]).
myRule(o9, []).
myRule(o9, [a2, o3]).
myRule(o4, [r8, b0]).
myRule(p7, [k1, o4, r8]).
myRule(p7, [o4, g0, w6, i0, o3, o9]).
myRule(p7, [h1, r8]).
myRule(y1, [r8, d2, d1, a1, o3, a0, b1]).
myRule(y5, [o4, y1]).
myRule(y7, []).
myRule(y7, [f0, b0, l1, b1]).
myRule(y7, [o9, o4, o3, w6, j0, y1, y5]).
myRule(x5, [b1, w6, y1, r8]).
myRule(x5, [o4, h0, y1, o9]).
myRule(y6, []).
myRule(y6, [k0, o9, d2, y1, f1, i0, y7]).
myRule(s5, [y5]).
myRule(u8, [w6, f1, o3]).
myRule(t2, [h1, y6]).
myRule(t2, [c1, e1, d1, e0, c0, d2, c2]).
myRule(t2, []).
myRule(z6, [y5, x5]).
myRule(v1, [c0, d2]).
myRule(v1, [h1, f0, u8, m1, j1, a0]).
myRule(v1, [u8, p7, l1]).
myRule(n7, []).
myRule(n7, [a0, i0]).
myRule(q5, [d0, e1, m1, b0, g0, c2, a2]).
myRule(v4, [p7, u8, s5]).
myRule(v4, [r8]).
myRule(t3, [w6]).
myRule(z3, [a0, w6, l0, l1]).
myRule(z3, [q5, t2, w6, s5, o4, u8]).
myRule(t4, [i0]).
myRule(t4, [y7, u8, k1]).
myRule(t4, [h1, y6, v4, z6, y1, y7]).
myRule(v5, [a0, l0, y7]).
myRule(s1, [b2, x5]).
myRule(s1, [y7, y1]).
myRule(v2, [q5, l1, u8]).
myRule(y4, [z6, t3, y5, q5]).
myRule(y4, [r8]).
myRule(w3, [u8, z6, q5]).
myRule(w3, [c2, t4, p7, k0]).
myRule(w3, [s1, i0, y5, w6, a0, o4, x5]).
myRule(u6, [y4, l0, a1, t2, y6, u8, h0]).
myRule(u6, [o4, o9, k1, x5]).
myRule(r1, [i0, t2, t3]).
myRule(r1, [b0, h1, c0, b2, a1]).
myRule(r1, [y1, k1, j0, c0, g0]).
myRule(t8, [m0, f1, b0, f0, h0]).
myRule(t8, [t2, k0, u6, y1, s5]).
myRule(t8, [l0, o9, t2, y7, h1]).
myRule(y2, [l1, c1, u6, f0, a1]).
myRule(y2, [m1, f0, r1, k1]).
myRule(y2, [b1, a0, i1]).
myRule(p3, [h1, s5, w3, j1]).
myRule(p3, [d2, f0, y1]).
myRule(u7, [t2]).
myRule(u7, [e1, c0, l0, i1, m1]).
myRule(n9, [d2, i1, b0, j0, e0, m1, c2]).
myRule(n9, [w6, i0, t8, z6, y4]).
myRule(r3, [o3, n7, t2, g1, w3]).
myRule(r3, [k0, u6]).
myRule(r3, [c0]).
myRule(u3, []).
myRule(u3, [h0, o3, t2, w3, y4, b2, f1]).
myRule(u3, [z3, o3, o9, r8, n7]).
myRule(n0, [y7]).
myRule(n0, [s1, r1]).
myRule(z7, [t8, w6]).
myRule(n4, [y4, y5, z7, y6, u6, u8, o9]).
myRule(n5, [j0]).
myRule(n5, []).
myRule(u4, [b2, l1]).
myRule(u4, [c2, i0, d1, b2, u3]).
myRule(r6, [l0, j1]).
myRule(p8, [a1, b1]).
myRule(o6, [t8, x5, y6, s5, n4]).
myRule(o6, [c0, c2, z6, u3, o9, s1, w6]).
myRule(o7, [y2, t2]).
myRule(o7, [n4, w3, w6, p7, u6, c2, e1]).
myRule(p1, [r8, j1, b2, e0]).
myRule(s4, [f0, d0, a2, c0]).
myRule(s4, [k0, i0, f1, r6]).
myRule(s4, []).
myRule(z2, [c1, h1, d1, b1, f0, o4, a1]).
myRule(z2, [w6, r6, y7, t2, t8, y1]).
myRule(p9, [u7, d0]).
myRule(p9, [d2, b0, y1, d0, i1, k1]).
myRule(w4, [y6, m1, a1, n5]).
myRule(w4, [r8, v4]).
myRule(w4, []).
myRule(n2, [a0, v4, y2, a2, m1, y6, y7]).
myRule(w8, [u4, o9, n7, s1, l0]).
myRule(w8, [w3, b2, k0, g1, f0, h0]).
myRule(w8, [y7, p7, p1, o7]).
myRule(r2, [n2, y1, p8, c1, s4]).
myRule(x0, [m1, s1, i1, a1]).
myRule(v3, [d0, g0, h1, f0, a1, m1]).
myRule(v3, [e0, r3, o9, p7, u6]).
myRule(v3, [c1, c2, m0, e1, f1]).
myRule(q4, [l0, k0, c1, d2, a1, h1, d1]).
myRule(x1, [v3, u3, v5, y7, y1]).
myRule(x1, []).
myRule(o1, [o3, s1, v1, n9, s5, v2, r2]).
myRule(o1, [s1]).
myRule(o1, [o3, d0, u7, m1, q4, t2, o6]).
myRule(p6, [o3, g1, v3, r3]).
myRule(y8, [h1, l1, m0, c2]).
myRule(y8, [z2, u6, a2]).
myRule(s7, [a0, l0, b2, d1, k1, l1]).
myRule(o8, []).
myRule(o8, [g1]).
myRule(p2, [l1, b1, i1, c2, m1]).
myRule(p2, []).
myRule(p2, [w8]).
myRule(t7, [y7]).
myRule(t7, [w6, v1, b0, r6]).
myRule(t7, [g1]).
myRule(u2, [c1, m1]).
myRule(u2, [d1, b2, a0, k1, y4]).
myRule(q8, [g0, a0, c2, h0, i1, l0]).
myRule(q8, [w6, r8, u2]).
myRule(q8, [n0, r8, p7, w8, v2, z7, z6]).
myRule(x2, [d0, t8, l1]).
myRule(v6, [p1, x1, r6, q8, w6]).
myRule(v6, [i0, w4, t7, w3, u2, x2, e0]).
myRule(v6, [z7, c1, i1, h0]).
myRule(u0, []).
myRule(u0, [s5]).
myRule(z4, [i0]).
myRule(w5, [x1]).
myRule(w5, [x2]).
myRule(w7, [v1]).
myRule(w7, [b1]).
myRule(r7, [l1, b2, c2, c1]).
myRule(r7, [y1, f0, e1, m0, b1]).
myRule(u1, []).
myRule(u1, [i0]).
myRule(s3, [m1, w6, w8]).
myRule(s3, [a0]).
myRule(s3, [o1, s1, q5, r3, w4]).
myRule(o0, [h0, w8]).
myRule(p4, [e0]).
myRule(y3, [x0, p8, s5, y4, t8]).
myRule(y3, [m1, t3, u4]).
myRule(q2, [r3, k0, v6, a0]).
myRule(q2, [f0, o9, m0, u2, y2]).
myRule(v8, [e0, k0, l0, b1, s3]).
myRule(t6, [n0, h1, k1, s4]).
myRule(w2, [c2, d2, t6, w6]).
myRule(w2, [m0, d0, a1, a2, g0, i0]).
myRule(w2, [q2]).
myRule(o2, [n4, r6]).
myRule(o2, [z2, r3, c1, y8, y4, z7, y3]).
myRule(o2, [n5, q4, s5, n4]).
myRule(v0, [h0, a2]).
myRule(v0, [l0, x5, t2, d0, g0, p3]).
myRule(q0, [n5, t7, v4]).
myRule(n1, [q5, b2, r6, b1]).
myRule(x8, [g0, c0, p9, a1, h0, v5, d0]).
myRule(x7, [u1, f1]).
myRule(x7, [d0, j1]).
myRule(x7, [d2]).
myRule(w1, [o0, w7, o8]).
myRule(t1, [w2, x5, o3, v1, z3]).
myRule(t1, [c0]).
