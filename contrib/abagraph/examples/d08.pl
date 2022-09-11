% generating command: chabagen -n -l 150 -a 30 -mco 2 -h 90 -rph 1 3 -lpb 0 7 -apb 0 7 e03
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
% ruleHeads: { r8, t8, z2, s4, o0, z8, q8, q5, y6, o1, n0, t5, s3, r2, q7, u2, n1, t3, t6, v7, r4, y8, w6, q4, x4, s2, x8, o9, u7, w0, v4, z3, w8, s1, y0, p9, v8, s5, r1, u4, z7, p4, s7, o2, q3, n7, v1, y4, v2, y2, q6, u5, o7, o6, n9, t2, p2, r7, p3, s6, s0, z4, u6, z0, p7, w1, r5, y1, r0, t4, s8, q2, t0, o4, n8, u1, w7, x1, w4, u8, w5, w2, p0, n2, x3, p1, r6, n4, o5, z1 }

toBeProved([z1]).

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

contrary(a0, s0).
contrary(b0, q8).
contrary(c0, z3).
contrary(d0, p5).
contrary(e0, n0).
contrary(f0, n9).
contrary(g0, q2).
contrary(h0, l0).
contrary(i0, e0).
contrary(j0, c2).
contrary(k0, o1).
contrary(l0, y3).
contrary(m0, f1).
contrary(a1, o9).
contrary(b1, q2).
contrary(c1, r3).
contrary(d1, p5).
contrary(e1, r7).
contrary(f1, r8).
contrary(g1, s7).
contrary(h1, b0).
contrary(i1, r7).
contrary(j1, o1).
contrary(k1, q4).
contrary(l1, s2).
contrary(m1, r4).
contrary(a2, y3).
contrary(b2, u7).
contrary(c2, o0).
contrary(d2, q1).

myRule(r8, [i0, b2, j1, d0, c0, a0, i1]).
myRule(r8, [h1, a2, a1, d1]).
myRule(t8, [d2, m0, g1, r8, c0, j1]).
myRule(z2, []).
myRule(z2, [t8]).
myRule(z2, [i1]).
myRule(s4, [r8]).
myRule(s4, [t8, j1]).
myRule(s4, [g1, a2, t8]).
myRule(o0, [t8, s4, c2, h0, g1, d2]).
myRule(o0, []).
myRule(o0, [m1, k0, i1, e1, f1, c1]).
myRule(z8, [e1, m1, i1, c1, j0, z2]).
myRule(z8, [c0]).
myRule(z8, [a1, b0, i1, j0, l0, h0]).
myRule(q8, [o0]).
myRule(q8, []).
myRule(q8, [j1, s4, i1]).
myRule(q5, [z2, z8, b0, c2, a1, b1]).
myRule(q5, [b2]).
myRule(y6, [l1, d2, s4, r8, f0, a2, m0]).
myRule(o1, [s4, o0, m0, c2, a1, y6]).
myRule(o1, [z8, b1, y6, j1, b0, k0, k1]).
myRule(o1, [t8, i1, c1, s4, a0, f0]).
myRule(n0, [h0, z8]).
myRule(n0, [o0, m0, i1]).
myRule(t5, [t8, r8, s4, b0, g1, q8]).
myRule(s3, [f1]).
myRule(r2, [d2]).
myRule(r2, [c0, l0]).
myRule(q7, [r2, m1]).
myRule(u2, [c1]).
myRule(u2, [q5]).
myRule(n1, [c0]).
myRule(n1, []).
myRule(n1, [a0, s4, c0, q5, h0, b1]).
myRule(t3, [s3]).
myRule(t3, [q7, t5, r2, d2, k0]).
myRule(t6, [a0, t3, g0, d0, z8]).
myRule(v7, [r8, g1, t6]).
myRule(v7, [e0, q5, q8, r2, a2]).
myRule(r4, []).
myRule(r4, [n1, t3]).
myRule(r4, [n0, z2]).
myRule(y8, []).
myRule(y8, [z2, q5, r4, t5]).
myRule(y8, [q5, s3, h0, n0, z8, g0, n1]).
myRule(w6, [e1, b1, y6, b2, n1, a0, e0]).
myRule(w6, [z2, s3, u2, z8, q7]).
myRule(q4, [t3, y6, o1, z2, t6, r8, n1]).
myRule(q4, [o1, z2, a0, g1, t8]).
myRule(x4, [k1, u2, e0, s3, j0]).
myRule(x4, [e0, f0, f1, a0, a2, d0]).
myRule(s2, []).
myRule(x8, [a2, e0]).
myRule(x8, [f0, d0, c2]).
myRule(o9, [x8, c1]).
myRule(o9, [q4, o0, n1, t5, t6, s2, o1]).
myRule(o9, [h1, h0, m0, v7, t6]).
myRule(u7, [x4, q8, s3, s2]).
myRule(w0, []).
myRule(v4, []).
myRule(v4, [l0, g1, d1, a1]).
myRule(v4, [n1, b0]).
myRule(z3, [c2, k0, l0, e1, k1]).
myRule(z3, [z2, w6, i1, h1, h0, l0]).
myRule(z3, [i1, a2, c2, d1]).
myRule(w8, [j1, h1, b2, g1, i0, b1]).
myRule(s1, [d2, a1, m1, v7]).
myRule(s1, [k1, y6, b0]).
myRule(y0, [q5, v7, k1, w0, j1, t3, a0]).
myRule(p9, [s2, u7, w6, c1, c2]).
myRule(p9, [b1, j0, v7, s1, i1, c1]).
myRule(v8, [j1, l0, c1, b2, d0]).
myRule(s5, [y6, r2, l1]).
myRule(s5, [i0, j0, v8, y0, u7]).
myRule(s5, [x8]).
myRule(r1, [e0, c2, f0, k1, l0, d2]).
myRule(u4, [b0, a1, l0, d2]).
myRule(u4, []).
myRule(z7, [y0, b1, e0, y8]).
myRule(z7, [q8, v7]).
myRule(z7, [s3, y8, v4]).
myRule(p4, [n0]).
myRule(s7, [z3, r8, i0, w0, z7]).
myRule(s7, []).
myRule(s7, [w8, v8, p9, n1, z7]).
myRule(o2, [d0, c2, x8, i0, j1]).
myRule(o2, []).
myRule(q3, [n1, c0, i1, u4, u7, z2, n0]).
myRule(q3, []).
myRule(q3, [w6, h1, s7]).
myRule(n7, [b1, f0]).
myRule(v1, []).
myRule(v1, [r2, f1, z2, y8]).
myRule(y4, [a2, e1, m0, d0, k0, q4, b1]).
myRule(y4, [j1, t8]).
myRule(v2, [i1]).
myRule(y2, [e0, o0, o9, h1, q3, r1]).
myRule(q6, [x8, s5, n1, d1, v4, d0]).
myRule(q6, [y4, w8, a1, v2, j1]).
myRule(q6, [r2, b2, q8, h0, z8]).
myRule(u5, [o2, t6]).
myRule(u5, [q4, y8, g0, q7, h0, d2, t6]).
myRule(o7, [r1, z3, y8, t5]).
myRule(o7, [a1, s7, k0]).
myRule(o6, [j0, b1, f0, m0, l0]).
myRule(o6, [i1, z2, g0, d0, f1, c1]).
myRule(n9, []).
myRule(t2, [q5]).
myRule(t2, [t3, q4, r4]).
myRule(t2, [c2, h0, a1]).
myRule(p2, [j1, u2]).
myRule(p2, [t8, g1, q4, n1]).
myRule(r7, [f1, b0, k0, j1, l0]).
myRule(r7, [y2, r1, e0, j1, h1]).
myRule(p3, [q7]).
myRule(p3, [s4, k1]).
myRule(s6, [e0, h0, m1, b1, c0, r8]).
myRule(s6, [z7, c0, q4]).
myRule(s0, [e1]).
myRule(s0, [j1, j0, c0, k0]).
myRule(s0, [n1, x8, v4, s6]).
myRule(z4, [v1, h0, c0, e0, d2]).
myRule(u6, []).
myRule(z0, [a0, t3, w8, b0, s6, q6]).
myRule(p7, []).
myRule(p7, [i1, y8]).
myRule(w1, [q8, e1, r7, y6, u6, s3, x4]).
myRule(w1, [v7, x8, k0]).
myRule(r5, [d1, s3, z0, i0]).
myRule(y1, [j0, o6, c2, u7, s2, r7, o7]).
myRule(r0, [i1]).
myRule(r0, []).
myRule(t4, []).
myRule(t4, [q7, c1, d1, o6]).
myRule(t4, [e1, j0, a0, c2, k1, f0]).
myRule(s8, [g1]).
myRule(s8, [f0]).
myRule(s8, [x8]).
myRule(q2, [a2, m0]).
myRule(q2, [a1, b0]).
myRule(q2, [a0, a1, k1, z0]).
myRule(t0, [p7, r7, b0, l1, d0, l0, r2]).
myRule(o4, [p3]).
myRule(o4, []).
myRule(n8, [y0, r2, v1, r7]).
myRule(n8, [u7, h1, o0, j1, s0]).
myRule(n8, [c0, k1, a0, b1]).
myRule(u1, [j1]).
myRule(u1, []).
myRule(w7, [h1, p7, s4]).
myRule(w7, [t0, v1, z4, w1, s4, h1, n8]).
myRule(w7, [i0, h1, m0]).
myRule(x1, [e0]).
myRule(w4, []).
myRule(w4, [g0, b2, d0, d2, m1, j0]).
myRule(u8, [r5, v4]).
myRule(u8, [i0, d1, d0, b1, a0, l1]).
myRule(w5, [z7, y2, r5, o0, c2]).
myRule(w2, [g0, d0, c1, j1, u6, v1]).
myRule(w2, [g0]).
myRule(w2, [u6, y1, v8, k0]).
myRule(p0, [i0, e1, j0, b1, g0, h0, g1]).
myRule(p0, [i1]).
myRule(p0, [j0, d1, h0, a2, q7, g0]).
myRule(n2, [e1]).
myRule(n2, []).
myRule(n2, [r2, y2, q4, s0, r4, s8]).
myRule(x3, [b1, i0, l1, m1, j1, d1]).
myRule(x3, []).
myRule(p1, [q3, e0, u1, y6, h0, a0, j1]).
myRule(p1, [s1, u4, r4, t0]).
myRule(p1, [o9, m1, c1, q6, o2, y6]).
myRule(r6, [y4, d0, w1]).
myRule(r6, [y2, t6, w2]).
myRule(n4, [d0, r6, y2, e1, e0, j1]).
myRule(n4, [d2, i0]).
myRule(o5, [q8, r1, y4]).
myRule(o5, [u7]).
myRule(o5, [w2, x1, y2, y6, r8, x8]).
myRule(z1, [r2, q4, o0]).
myRule(z1, [f1, a2, i0, d0, c2, a1, i1]).
myRule(z1, [e0, v2, g0, k0]).
