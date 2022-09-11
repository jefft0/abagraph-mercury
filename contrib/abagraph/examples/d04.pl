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
% ruleHeads: { w8, s2, z1, v4, r1, u4, n8, y1, n6, u0, u1, w3, w7, v5, p7, r2, w5, q0, y6, y4, o7, q7, z5, y2, t4, y5, u7, q3, w6, x0, o6, r3, x8, s1, v6, p9, u6, w1, t3, y8, r8, u8, n9, s0, o0, n7, n5, s7, w0, q6, v2, u3, q1, s8, v7, t0, x7, r7, t1, p4, q2, z8, u2, x6, n2, x4, p0, o3, x1, n4, z4, x5, v3, r0, u5, s6, p6, p5, v8, t2, v1, r5, x3, s3, p8, t7, t5, x2, q4, z7 }

toBeProved([z7]).

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

contrary(a0, b1).
contrary(b0, k0).
contrary(c0, v7).
contrary(d0, n2).
contrary(e0, o7).
contrary(f0, c0).
contrary(g0, o3).
contrary(h0, k1).
contrary(i0, g0).
contrary(j0, c0).
contrary(k0, x5).
contrary(l0, y6).
contrary(m0, x0).
contrary(a1, p7).
contrary(b1, u4).
contrary(c1, y3).
contrary(d1, u2).
contrary(e1, j1).
contrary(f1, q6).
contrary(g1, t4).
contrary(h1, m0).
contrary(i1, u4).
contrary(j1, l1).
contrary(k1, z7).
contrary(l1, p3).
contrary(m1, r1).
contrary(a2, s1).
contrary(b2, t2).
contrary(c2, t0).
contrary(d2, z7).

myRule(w8, [k0, e1, m0, f0, i1, d1]).
myRule(w8, [e0]).
myRule(w8, [e1, d0, b1, j0]).
myRule(s2, [c2, j1, j0]).
myRule(s2, [m1, w8, a1, e1]).
myRule(z1, [s2, w8, m1, h0]).
myRule(z1, [s2, w8, i1, g0, h0, c1, i0]).
myRule(v4, [s2, i1]).
myRule(v4, [c1, f0, i1]).
myRule(r1, [v4, d0, e0, w8]).
myRule(u4, [r1]).
myRule(n8, [c2, b1, j0, a0, m0, h0, g1]).
myRule(n8, [w8, e1, h1]).
myRule(n8, [c2, a2, w8, v4]).
myRule(y1, [a2]).
myRule(n6, [s2, w8, n8, u4, y1, z1, v4]).
myRule(n6, [v4, z1, w8, s2, u4, n8, r1]).
myRule(n6, [v4, y1, w8, c1, d0, m1]).
myRule(u0, [r1, y1, s2, n6, w8, u4]).
myRule(u1, [c2, d0]).
myRule(u1, [r1, k1, a2, n8, h0, v4]).
myRule(w3, [d2, i0]).
myRule(w3, [r1, f1, b2, u4, v4, j0]).
myRule(w7, []).
myRule(v5, []).
myRule(v5, [g0, w8, r1, a0, v4, d0, w3]).
myRule(p7, [n8, i1, c1, u1]).
myRule(r2, [d0, i0]).
myRule(r2, [y1, v5, p7]).
myRule(w5, [d2, v4, r2]).
myRule(q0, [d0, a0, j1, l0, c1, b0]).
myRule(q0, [b2, r1]).
myRule(y6, [s2, c2]).
myRule(y6, [u1, r1, u4, r2]).
myRule(y6, [p7, q0, a2, v4]).
myRule(y4, [w8, s2]).
myRule(y4, [r2, k0, h0]).
myRule(o7, [y1, y6, r2]).
myRule(o7, [v4, n6, a2, c1, l1, d2, j1]).
myRule(o7, []).
myRule(q7, [r2]).
myRule(q7, [q0, a0]).
myRule(q7, [v4]).
myRule(z5, [b1, z1, o7]).
myRule(z5, [d0, k0, f1]).
myRule(y2, [w3]).
myRule(y2, []).
myRule(t4, [n6, q7, l1, r1, j0, z1]).
myRule(t4, [v5, y2, r2, y1, p7]).
myRule(y5, []).
myRule(u7, [f1, a0, q0, u4]).
myRule(q3, [i1, u4, b2, a1]).
myRule(q3, [z5, w5]).
myRule(q3, [f1, q7, c0, k0, d2]).
myRule(w6, [o7, e1, u0, f1, u1]).
myRule(x0, [u4, e0, t4]).
myRule(x0, [w5, v4, w7, v5]).
myRule(o6, [k1, b2, b1, g0, h0]).
myRule(r3, [e1, y6, n8]).
myRule(r3, [l1, b1, u1, j1, w8]).
myRule(r3, [l0]).
myRule(x8, [k1, c1, a0, c0, c2, w3, l1]).
myRule(x8, [e1, m1]).
myRule(s1, [c1, z1]).
myRule(v6, []).
myRule(p9, [c1, w5]).
myRule(p9, [r3, u4, c0, z1, r1]).
myRule(p9, [y1, w6, x8, n8, r1]).
myRule(u6, [a0, u4, d0, q3, u0]).
myRule(u6, [q3, y1, y5]).
myRule(u6, [r3, a0, p9, p7, o6, g0, a1]).
myRule(w1, [e1, r2, d2, a0, t4, r1]).
myRule(w1, [n8, k1, b2, g1, o6, g0]).
myRule(w1, [y4, a2, z1, q3, p7]).
myRule(t3, [w5, m0, g1]).
myRule(t3, [d2, r1, b2, a1, b0, d1]).
myRule(t3, [k1, d0, b2, b0, g1, a0, h1]).
myRule(y8, [o7, z1, y5, v4, q3]).
myRule(y8, [h0, c2]).
myRule(r8, [x0, y2, y1, k1, y4]).
myRule(r8, []).
myRule(r8, [d1, e0]).
myRule(u8, []).
myRule(u8, [l1, q7, c1, p7, y4]).
myRule(u8, [z5, w3, h1]).
myRule(n9, [u7]).
myRule(n9, [b0, a2, d2, d0, f1]).
myRule(s0, [u7, v4, r2, k0, b1, w8]).
myRule(o0, [c0, y1, x0, a1, q7]).
myRule(o0, [w1, s2, o6, x8, b1]).
myRule(o0, [c1, u4, q0, p7, w7, m1, w3]).
myRule(n7, [u7, r8, n6, w8]).
myRule(n5, [u4, u1, u6, a0, n8, q0]).
myRule(n5, []).
myRule(n5, [s2, w8, u4, q0]).
myRule(s7, [d2, l1, b1, y4, a1, d0, a2]).
myRule(s7, [u4, p7]).
myRule(s7, [l0, e0]).
myRule(w0, [f0, i0, a1]).
myRule(q6, []).
myRule(v2, [u7, q7, t3]).
myRule(v2, [s7, a1, u6, i1]).
myRule(v2, [a1, a0, n6, n7, w3]).
myRule(u3, [r8]).
myRule(u3, []).
myRule(u3, [n7, e1, s2]).
myRule(q1, [t4, y6, h1, t3, n9, j1, q0]).
myRule(q1, [k0, b2, h0, b1, p9]).
myRule(s8, [j1, b1, f1, b0, c2, h1]).
myRule(v7, [c0, c1, d2, g0]).
myRule(t0, [d2, q0, u3]).
myRule(t0, [r1]).
myRule(t0, [w7, w5, r3]).
myRule(x7, [k1, u7]).
myRule(x7, [k0, p7]).
myRule(x7, [b2, n6, a2, p7, e1, m1]).
myRule(r7, [d2]).
myRule(t1, [c1, v2, w6, p7, y2, i1, m1]).
myRule(p4, []).
myRule(q2, [x8, q6]).
myRule(z8, [l0, d1, d0, m1, k1, j0]).
myRule(z8, [c0, h0, b1, v5]).
myRule(z8, [a0, s2]).
myRule(u2, [j0, v6, q1, m0]).
myRule(u2, [o0, s8, g0, q0, v4, t4]).
myRule(u2, []).
myRule(x6, [y5, n7, a2]).
myRule(x6, [n9]).
myRule(n2, [s2, o6]).
myRule(x4, [g1, a2]).
myRule(p0, []).
myRule(p0, [s8, u1, l0, w1, r1, n8]).
myRule(o3, [n8, z1, o0, t4, x4, u7]).
myRule(x1, [z1, v6, j1, t1, f1, n6]).
myRule(n4, [u7, i0]).
myRule(n4, [o7, v4, q3, h0, t3, c2, d0]).
myRule(z4, [t0, c0, v4]).
myRule(z4, [u2, n9, x4]).
myRule(z4, []).
myRule(x5, [p9, n8, q0]).
myRule(v3, [p0, n4, n8, m0, a0, y6, z1]).
myRule(r0, []).
myRule(u5, [g1]).
myRule(u5, [k1]).
myRule(s6, [k1, u6, y2]).
myRule(s6, [p0, q7, r1, u0, x4]).
myRule(p6, [f1, l0, j1, e1, b2, k0]).
myRule(p5, [w8]).
myRule(v8, [f1, q7, y1, w1]).
myRule(v8, [e0, s7, k0, h0, l1, q7, q0]).
myRule(v8, [r1, q6, x8, n8]).
myRule(t2, [c0, a1, j1, b0, b1, m1, k1]).
myRule(t2, [h1]).
myRule(v1, [o6, d0, e1, f1, u3, l1]).
myRule(v1, [w3, y5, x5, z5, o6, r0, t3]).
myRule(r5, [z1, s2, u6]).
myRule(r5, [v7, d0]).
myRule(x3, [q3, c0, r5]).
myRule(s3, [r5, q7, u6, s8, p7, w3, x1]).
myRule(s3, [x6, q2, x1, q3]).
myRule(p8, [h1, g0, q6, s0, s8, z8]).
myRule(t7, [u0, c1]).
myRule(t7, [f0, l1]).
myRule(t7, [i1]).
myRule(t5, [i1, h0, l1, c0]).
myRule(x2, [k0, n6]).
myRule(q4, [i0]).
myRule(q4, [f0, t0, c1, n4, n6, x3]).
myRule(q4, [y1, w8, t4, r0, k0, w1, v4]).
myRule(z7, [x5, c2, y6, s7, a0]).
myRule(z7, [b1, d0, b2]).
