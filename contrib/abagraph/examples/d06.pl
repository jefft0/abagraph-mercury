% generating command: chabagen -n -l 150 -a 30 -mco 2 -h 90 -rph 1 3 -lpb 0 7 -apb 0 7 e01
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
% ruleHeads: { n4, q1, o0, y2, o6, w4, n1, z5, o2, z4, x0, t7, u4, s5, p4, w1, x2, x7, r2, t0, z2, w0, q6, n7, u6, r1, z1, q0, x1, n6, v1, n2, y8, p7, y1, o4, u3, t1, o3, q3, o1, z0, v8, w2, p5, v7, y4, p1, s1, w7, u2, n3, t2, q2, p0, x3, r0, y7, q8, t4, x5, x8, q5, z7, s6, v2, t5, q7, p8, n8, n9, s7, v5, o9, z6, u7, v0, x6, y5, p9, w6, r7, w5, q4, r5, z3, v4, y0, u8, o5 }

toBeProved([o5]).

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

contrary(a0, r8).
contrary(b0, v0).
contrary(c0, c1).
contrary(d0, v4).
contrary(e0, k0).
contrary(f0, x4).
contrary(g0, q3).
contrary(h0, v8).
contrary(i0, h1).
contrary(j0, i0).
contrary(k0, o0).
contrary(l0, d0).
contrary(m0, t2).
contrary(a1, t8).
contrary(b1, u2).
contrary(c1, w2).
contrary(d1, o4).
contrary(e1, d1).
contrary(f1, d0).
contrary(g1, v6).
contrary(h1, c2).
contrary(i1, k0).
contrary(j1, i0).
contrary(k1, g1).
contrary(l1, q6).
contrary(m1, q5).
contrary(a2, u7).
contrary(b2, y6).
contrary(c2, o2).
contrary(d2, o6).

myRule(n4, [c2, f0, k1, l0, c0, j1, d1]).
myRule(n4, [m1, k0, e1, b1, a0, i0, a1]).
myRule(q1, [m0, c1, k0, m1, a1]).
myRule(o0, [j0, f1, i1, f0, b2, q1, e1]).
myRule(y2, [j0, k0, m1, c2, h1]).
myRule(y2, [n4, c2]).
myRule(y2, [q1]).
myRule(o6, [y2, j1, o0, b0]).
myRule(w4, [e1]).
myRule(w4, [e1, h0, n4, q1, a2, o6]).
myRule(w4, [l0, c0, y2, i1, b0]).
myRule(n1, [l1, j1, n4, h1, q1]).
myRule(n1, []).
myRule(n1, [n4, q1, y2]).
myRule(z5, [o6]).
myRule(z5, [w4, o0, q1, n4]).
myRule(o2, [a0, a1, c2, k1]).
myRule(o2, [y2, n4, h0, w4, o6]).
myRule(z4, [k0, o0, e1, o6, o2]).
myRule(x0, [m1, o2, z5]).
myRule(x0, [k1, a2, j0, g1, a0]).
myRule(x0, [o2, b1]).
myRule(t7, [y2, w4, n4, o6, x0, o0, o2]).
myRule(t7, [w4, g0, f1, k0, o0, h0]).
myRule(t7, [z4, o6, z5, y2, o2, j0]).
myRule(u4, [q1, z5, n1, o0, o2, z4, x0]).
myRule(u4, [f0, q1, y2, e0]).
myRule(u4, []).
myRule(s5, [c1, d2, a1, g1, i0, g0, l1]).
myRule(s5, [f0, l0]).
myRule(s5, [b1, k0, f0]).
myRule(p4, [j0, g0, l1, f1]).
myRule(w1, [n1, n4, c2, b0, i0, j0]).
myRule(w1, [o0, d0, c0]).
myRule(x2, [s5, z4, o6, p4, y2, x0, n4]).
myRule(x7, [w1, s5, z4, x0, l1]).
myRule(r2, [c1]).
myRule(t0, [x0, z4, z5, u4, w4, s5]).
myRule(t0, [o6, r2]).
myRule(z2, [m0]).
myRule(z2, [b0, d2]).
myRule(z2, [o0, d0, w4, j0, c2, n1, g1]).
myRule(w0, []).
myRule(w0, [g0]).
myRule(q6, [b0, k0, i0, o2]).
myRule(q6, [r2, s5, n1, z2, u4]).
myRule(q6, [n1, w0, f0, s5, x2, x0]).
myRule(n7, [z4, b0, x0, w4, j1, a2]).
myRule(n7, [w4]).
myRule(n7, [b1, g0]).
myRule(u6, [o6, t0]).
myRule(u6, [o0, j1]).
myRule(u6, [o0, r2, b0, d2, z2]).
myRule(r1, [q1, y2, u4, w1, d1, e0]).
myRule(r1, [i1, o6, i0, o2, y2]).
myRule(r1, [y2, n7, r2, d2, c0, i1, x2]).
myRule(z1, [p4, d2, e0, o6, n4, y2]).
myRule(z1, [q1, c0, p4, y2, h1, o6, f0]).
myRule(q0, [a1, d1, g1, a2]).
myRule(q0, [o0]).
myRule(q0, [w0, b2, l1, l0, r1, z2]).
myRule(x1, [q0]).
myRule(x1, [a2, j1, d0, k1, h0]).
myRule(x1, [z5, n4, z1, b2, b1]).
myRule(n6, [l0, j0, k0]).
myRule(n6, [g0]).
myRule(n6, [z5, c0, u4, o6]).
myRule(v1, [q6, e1]).
myRule(n2, [z4, e1, h0, c1, o6, c2, w1]).
myRule(y8, [q6, t0]).
myRule(p7, []).
myRule(y1, [x7, n6, b2, n2]).
myRule(y1, [n4, r2, q0, q6]).
myRule(y1, [b0, a2, n6]).
myRule(o4, [f0, j1]).
myRule(u3, [e0, d2, m1, q0, c2, x0, n6]).
myRule(u3, [o4, r2, y2]).
myRule(t1, [b1, h0, j0, j1, e1]).
myRule(t1, [x1, t7, v1, p4, z4, w4]).
myRule(o3, [b0, j1, a1, l1]).
myRule(o3, [b2, e0, d0]).
myRule(o3, [z2, d1, w4]).
myRule(q3, [h1, a0, e0]).
myRule(o1, [k1, n6]).
myRule(z0, [g0, a2, d2, c1, f1, e0]).
myRule(z0, []).
myRule(z0, [p4, b0, l0, d0]).
myRule(v8, []).
myRule(w2, [m1, c2, d1]).
myRule(p5, [o3, p7, t0, z0, q6]).
myRule(p5, []).
myRule(v7, [n1]).
myRule(y4, [s5, x2]).
myRule(y4, []).
myRule(y4, [y8, q0, g0]).
myRule(p1, [y1, i1, q3, b0, s5]).
myRule(s1, [d2]).
myRule(w7, []).
myRule(w7, [n7, o4, u4, a2, x0, i0, q6]).
myRule(u2, [e1, a1]).
myRule(u2, [v7]).
myRule(n3, []).
myRule(n3, [j1, e1, d2, u3, g1, d0]).
myRule(n3, [n6, z1, n1, x7]).
myRule(t2, [s5, z2, o0, l1, c1]).
myRule(t2, [s5, t7, s1, d1, n7, n1]).
myRule(t2, [t0, y1, s1, y8, z0, q6, o4]).
myRule(q2, []).
myRule(q2, [p4, u6]).
myRule(p0, [e1, y1, r1, p7, u4]).
myRule(x3, [o3, y4, z4, y8, o0, s5, q1]).
myRule(x3, [t1, v7, z4, n2]).
myRule(x3, [i1, c2, a2, l1]).
myRule(r0, [p7, g0]).
myRule(r0, [j1, a1, x1, r2, o2]).
myRule(r0, [o0, r1, q3]).
myRule(y7, [s5, q0, u6]).
myRule(y7, [z4]).
myRule(y7, [k1, n2]).
myRule(q8, [y8]).
myRule(q8, []).
myRule(t4, [f1, i1, h0, n7, d2, i0, b1]).
myRule(t4, [c2, b2, f1, h0]).
myRule(t4, [c0, b0]).
myRule(x5, [k0, w7]).
myRule(x5, [m0]).
myRule(x5, [c0, a2, j1, l0, i0, b1]).
myRule(x8, [b1]).
myRule(q5, [w4, r1, x8]).
myRule(z7, [t1, e1, n3, o2, u6, t4]).
myRule(z7, [y2, t7]).
myRule(s6, [l1]).
myRule(v2, [o0, n3, z0, w2, q3]).
myRule(t5, [q8, p4, n1, x0, o1]).
myRule(t5, [h1, y8, x2, k1, q5]).
myRule(t5, [b2, c1, a2, c0, a0, a1, l1]).
myRule(q7, [c0, v1, q6]).
myRule(q7, [z5, l1, n4, k1, x0, v1, q2]).
myRule(p8, [r0, z5, q7, o3, d0]).
myRule(p8, [y1, x0, j0, n6]).
myRule(p8, [n1, w4, q6, w2, x7, n6, r1]).
myRule(n8, [o6]).
myRule(n9, [o0, n2, p5, w2]).
myRule(s7, [h1, f1]).
myRule(v5, [z2, a0, q0]).
myRule(o9, []).
myRule(o9, [c0, c1, q8, v1, a0]).
myRule(z6, [x2, h1]).
myRule(u7, [e0, f1, h0, g0, d0, c1]).
myRule(u7, [m0, i0, i1, j0, g0]).
myRule(u7, [j1, l1]).
myRule(v0, [g0, y7]).
myRule(v0, [l0, b1, z6, z1]).
myRule(v0, [g1, c2, t1, i0, i1, m1]).
myRule(x6, [u7, d1, l1]).
myRule(x6, [h1, a1, j0, z1, h0, e1, t2]).
myRule(y5, [z6, u4, u2, d0, e0, d1, f0]).
myRule(y5, [r2, q0, p5, q8]).
myRule(p9, [q8, n4, q1, s1, p7, x1]).
myRule(p9, [c1]).
myRule(w6, [v8, h0, t5, c1, x3, e1]).
myRule(w6, []).
myRule(r7, [n6]).
myRule(r7, [a2, b2, f1, k0]).
myRule(r7, [l1, c2, r1, i0]).
myRule(w5, [x8, i0, c1, a0, v2, n1]).
myRule(w5, [g0, z7, i1, o1]).
myRule(q4, []).
myRule(q4, [k1, e0, z5]).
myRule(q4, [v2, o1]).
myRule(r5, [c2, z0, i1, f0]).
myRule(r5, [t5]).
myRule(r5, []).
myRule(z3, [f0, b0]).
myRule(z3, [o6, t2]).
myRule(v4, [o2, g0, o0, e0, v1, b0]).
myRule(v4, [a2, v7]).
myRule(y0, [p1, d2, e0, l1]).
myRule(u8, [t2, r0, p9, x7]).
myRule(u8, [s1, m1, z4, z0, w0]).
myRule(o5, [b1, a0, m0, d0, f0]).
myRule(o5, [a2]).
