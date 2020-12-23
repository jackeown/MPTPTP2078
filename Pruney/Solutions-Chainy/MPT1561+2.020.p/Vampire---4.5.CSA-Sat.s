%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:10 EST 2020

% Result     : CounterSatisfiable 8.60s
% Output     : Saturation 8.60s
% Verified   : 
% Statistics : Number of clauses        :  273 ( 273 expanded)
%              Number of leaves         :  273 ( 273 expanded)
%              Depth                    :    0
%              Number of atoms          : 1237 (1237 expanded)
%              Number of equality atoms : 1009 (1009 expanded)
%              Maximal clause size      :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u42,negated_conjecture,
    ( v5_orders_2(sK0) )).

cnf(u3355,axiom,
    ( r2_lattice3(X12,k2_tarski(X11,X11),X13)
    | sK2(sK4(X12,k2_tarski(X11,X11),X13),sK2(X14,X15,k2_tarski(X11,X11)),k2_tarski(X11,X11)) = X11
    | sK2(X14,X15,k2_tarski(X11,X11)) = X15
    | sK2(X14,X15,k2_tarski(X11,X11)) = X14
    | k2_tarski(X14,X15) = k2_tarski(X11,X11)
    | k2_tarski(X11,X11) = k2_tarski(sK4(X12,k2_tarski(X11,X11),X13),sK2(X14,X15,k2_tarski(X11,X11)))
    | ~ m1_subset_1(X13,u1_struct_0(X12))
    | ~ l1_orders_2(X12) )).

cnf(u2618,axiom,
    ( r2_lattice3(X16,k2_tarski(X15,X15),X17)
    | sK2(sK2(X13,X14,k2_tarski(X15,X15)),sK4(X16,k2_tarski(X15,X15),X17),k2_tarski(X15,X15)) = X15
    | k2_tarski(X15,X15) = k2_tarski(sK2(X13,X14,k2_tarski(X15,X15)),sK4(X16,k2_tarski(X15,X15),X17))
    | ~ m1_subset_1(X17,u1_struct_0(X16))
    | ~ l1_orders_2(X16)
    | sK2(X13,X14,k2_tarski(X15,X15)) = X14
    | sK2(X13,X14,k2_tarski(X15,X15)) = X13
    | k2_tarski(X13,X14) = k2_tarski(X15,X15) )).

cnf(u2610,axiom,
    ( r2_lattice3(X16,k2_tarski(X15,X15),X17)
    | sK2(sK4(X16,k2_tarski(X15,X15),X17),sK2(X13,X14,k2_tarski(X15,X15)),k2_tarski(X15,X15)) = X15
    | k2_tarski(X15,X15) = k2_tarski(sK2(X13,X14,k2_tarski(X15,X15)),sK4(X16,k2_tarski(X15,X15),X17))
    | ~ m1_subset_1(X17,u1_struct_0(X16))
    | ~ l1_orders_2(X16)
    | sK2(X13,X14,k2_tarski(X15,X15)) = X14
    | sK2(X13,X14,k2_tarski(X15,X15)) = X13
    | k2_tarski(X13,X14) = k2_tarski(X15,X15) )).

cnf(u2445,axiom,
    ( r2_lattice3(X18,k2_tarski(X17,X17),X19)
    | ~ m1_subset_1(X19,u1_struct_0(X18))
    | ~ l1_orders_2(X18)
    | sK2(X15,X16,k2_tarski(X17,X17)) = sK4(X18,k2_tarski(X17,X17),X19)
    | sK4(X18,k2_tarski(X17,X17),X19) = X17
    | sK2(X15,X16,k2_tarski(X17,X17)) = X16
    | sK2(X15,X16,k2_tarski(X17,X17)) = X15
    | k2_tarski(X17,X17) = k2_tarski(X15,X16) )).

cnf(u2259,axiom,
    ( r2_lattice3(X9,k2_tarski(X10,X10),X11)
    | sK2(X8,sK4(X9,k2_tarski(X10,X10),X11),k2_tarski(X10,X10)) = X8
    | sK2(X8,sK4(X9,k2_tarski(X10,X10),X11),k2_tarski(X10,X10)) = X10
    | k2_tarski(X10,X10) = k2_tarski(X8,sK4(X9,k2_tarski(X10,X10),X11))
    | ~ m1_subset_1(X11,u1_struct_0(X9))
    | ~ l1_orders_2(X9) )).

cnf(u2247,axiom,
    ( r2_lattice3(X9,k2_tarski(X8,X8),X10)
    | sK2(sK4(X9,k2_tarski(X8,X8),X10),X11,k2_tarski(X8,X8)) = X11
    | sK2(sK4(X9,k2_tarski(X8,X8),X10),X11,k2_tarski(X8,X8)) = X8
    | k2_tarski(X8,X8) = k2_tarski(sK4(X9,k2_tarski(X8,X8),X10),X11)
    | ~ m1_subset_1(X10,u1_struct_0(X9))
    | ~ l1_orders_2(X9) )).

cnf(u991,axiom,
    ( r2_lattice3(X6,k2_tarski(X5,X5),X7)
    | k2_tarski(X5,X5) = k2_tarski(X5,sK4(X6,k2_tarski(X5,X5),X7))
    | ~ m1_subset_1(X7,u1_struct_0(X6))
    | ~ l1_orders_2(X6) )).

cnf(u418,axiom,
    ( r2_lattice3(X5,k2_tarski(X6,X6),X7)
    | sK2(sK4(X5,k2_tarski(X6,X6),X7),sK4(X5,k2_tarski(X6,X6),X7),k2_tarski(X6,X6)) = X6
    | k2_tarski(X6,X6) = k2_tarski(sK4(X5,k2_tarski(X6,X6),X7),sK4(X5,k2_tarski(X6,X6),X7))
    | ~ m1_subset_1(X7,u1_struct_0(X5))
    | ~ l1_orders_2(X5) )).

cnf(u2780,axiom,
    ( r2_lattice3(X16,k2_tarski(X14,X15),X17)
    | sK2(sK4(X16,k2_tarski(X14,X15),X17),sK2(X18,X19,k2_tarski(X14,X15)),k2_tarski(X14,X15)) = X14
    | sK2(sK4(X16,k2_tarski(X14,X15),X17),sK2(X18,X19,k2_tarski(X14,X15)),k2_tarski(X14,X15)) = X15
    | sK2(X18,X19,k2_tarski(X14,X15)) = X19
    | sK2(X18,X19,k2_tarski(X14,X15)) = X18
    | k2_tarski(X14,X15) = k2_tarski(X18,X19)
    | k2_tarski(X14,X15) = k2_tarski(sK4(X16,k2_tarski(X14,X15),X17),sK2(X18,X19,k2_tarski(X14,X15)))
    | ~ m1_subset_1(X17,u1_struct_0(X16))
    | ~ l1_orders_2(X16) )).

cnf(u2659,axiom,
    ( r2_lattice3(X18,k2_tarski(X14,X15),X19)
    | sK2(sK2(X16,X17,k2_tarski(X14,X15)),sK4(X18,k2_tarski(X14,X15),X19),k2_tarski(X14,X15)) = X14
    | sK2(sK2(X16,X17,k2_tarski(X14,X15)),sK4(X18,k2_tarski(X14,X15),X19),k2_tarski(X14,X15)) = X15
    | sK2(X16,X17,k2_tarski(X14,X15)) = X17
    | sK2(X16,X17,k2_tarski(X14,X15)) = X16
    | k2_tarski(X14,X15) = k2_tarski(X16,X17)
    | k2_tarski(X14,X15) = k2_tarski(sK2(X16,X17,k2_tarski(X14,X15)),sK4(X18,k2_tarski(X14,X15),X19))
    | ~ m1_subset_1(X19,u1_struct_0(X18))
    | ~ l1_orders_2(X18) )).

cnf(u2615,axiom,
    ( r2_lattice3(X2,k2_tarski(X1,X0),X3)
    | sK2(X0,sK4(X2,k2_tarski(X1,X0),X3),k2_tarski(X1,X0)) = X1
    | k2_tarski(X1,X0) = k2_tarski(X0,sK4(X2,k2_tarski(X1,X0),X3))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_orders_2(X2) )).

cnf(u2607,axiom,
    ( r2_lattice3(X2,k2_tarski(X1,X0),X3)
    | sK2(sK4(X2,k2_tarski(X1,X0),X3),X0,k2_tarski(X1,X0)) = X1
    | k2_tarski(X1,X0) = k2_tarski(X0,sK4(X2,k2_tarski(X1,X0),X3))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_orders_2(X2) )).

cnf(u2252,axiom,
    ( r2_lattice3(X10,k2_tarski(X8,X9),X11)
    | sK2(X8,sK4(X10,k2_tarski(X8,X9),X11),k2_tarski(X8,X9)) = X9
    | k2_tarski(X8,X9) = k2_tarski(X8,sK4(X10,k2_tarski(X8,X9),X11))
    | ~ m1_subset_1(X11,u1_struct_0(X10))
    | ~ l1_orders_2(X10) )).

cnf(u1942,axiom,
    ( r2_lattice3(X8,k2_tarski(X9,X10),X11)
    | sK2(sK4(X8,k2_tarski(X9,X10),X11),X9,k2_tarski(X9,X10)) = X10
    | k2_tarski(X9,X10) = k2_tarski(X9,sK4(X8,k2_tarski(X9,X10),X11))
    | ~ m1_subset_1(X11,u1_struct_0(X8))
    | ~ l1_orders_2(X8) )).

cnf(u1779,axiom,
    ( r2_lattice3(X10,k2_tarski(X8,X9),X11)
    | sK2(sK4(X10,k2_tarski(X8,X9),X11),sK4(X10,k2_tarski(X8,X9),X11),k2_tarski(X8,X9)) = X8
    | sK2(sK4(X10,k2_tarski(X8,X9),X11),sK4(X10,k2_tarski(X8,X9),X11),k2_tarski(X8,X9)) = X9
    | k2_tarski(X8,X9) = k2_tarski(sK4(X10,k2_tarski(X8,X9),X11),sK4(X10,k2_tarski(X8,X9),X11))
    | ~ m1_subset_1(X11,u1_struct_0(X10))
    | ~ l1_orders_2(X10) )).

cnf(u313,axiom,
    ( r2_lattice3(X14,k2_tarski(X11,X12),X15)
    | sK2(X13,sK4(X14,k2_tarski(X11,X12),X15),k2_tarski(X11,X12)) = X13
    | sK2(X13,sK4(X14,k2_tarski(X11,X12),X15),k2_tarski(X11,X12)) = X11
    | sK2(X13,sK4(X14,k2_tarski(X11,X12),X15),k2_tarski(X11,X12)) = X12
    | k2_tarski(X11,X12) = k2_tarski(X13,sK4(X14,k2_tarski(X11,X12),X15))
    | ~ m1_subset_1(X15,u1_struct_0(X14))
    | ~ l1_orders_2(X14) )).

cnf(u287,axiom,
    ( r2_lattice3(X13,k2_tarski(X11,X12),X14)
    | sK2(sK4(X13,k2_tarski(X11,X12),X14),X15,k2_tarski(X11,X12)) = X15
    | sK2(sK4(X13,k2_tarski(X11,X12),X14),X15,k2_tarski(X11,X12)) = X11
    | sK2(sK4(X13,k2_tarski(X11,X12),X14),X15,k2_tarski(X11,X12)) = X12
    | k2_tarski(X11,X12) = k2_tarski(sK4(X13,k2_tarski(X11,X12),X14),X15)
    | ~ m1_subset_1(X14,u1_struct_0(X13))
    | ~ l1_orders_2(X13) )).

cnf(u83,axiom,
    ( r2_lattice3(X0,k2_tarski(X1,X2),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK4(X0,k2_tarski(X1,X2),X3) = X1
    | sK4(X0,k2_tarski(X1,X2),X3) = X2 )).

cnf(u64,axiom,
    ( r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u85,negated_conjecture,
    ( r2_lattice3(sK0,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | k2_tarski(sK4(sK0,X0,X1),sK4(sK0,X0,X1)) = k6_domain_1(u1_struct_0(sK0),sK4(sK0,X0,X1))
    | ~ l1_struct_0(sK0) )).

cnf(u3354,axiom,
    ( r1_lattice3(X7,k2_tarski(X6,X6),X8)
    | sK2(sK3(X7,k2_tarski(X6,X6),X8),sK2(X9,X10,k2_tarski(X6,X6)),k2_tarski(X6,X6)) = X6
    | sK2(X9,X10,k2_tarski(X6,X6)) = X10
    | sK2(X9,X10,k2_tarski(X6,X6)) = X9
    | k2_tarski(X6,X6) = k2_tarski(X9,X10)
    | k2_tarski(X6,X6) = k2_tarski(sK3(X7,k2_tarski(X6,X6),X8),sK2(X9,X10,k2_tarski(X6,X6)))
    | ~ m1_subset_1(X8,u1_struct_0(X7))
    | ~ l1_orders_2(X7) )).

cnf(u2614,axiom,
    ( r1_lattice3(X16,k2_tarski(X15,X15),X17)
    | sK2(sK2(X13,X14,k2_tarski(X15,X15)),sK3(X16,k2_tarski(X15,X15),X17),k2_tarski(X15,X15)) = X15
    | k2_tarski(X15,X15) = k2_tarski(sK2(X13,X14,k2_tarski(X15,X15)),sK3(X16,k2_tarski(X15,X15),X17))
    | ~ m1_subset_1(X17,u1_struct_0(X16))
    | ~ l1_orders_2(X16)
    | sK2(X13,X14,k2_tarski(X15,X15)) = X14
    | sK2(X13,X14,k2_tarski(X15,X15)) = X13
    | k2_tarski(X13,X14) = k2_tarski(X15,X15) )).

cnf(u2606,axiom,
    ( r1_lattice3(X16,k2_tarski(X15,X15),X17)
    | sK2(sK3(X16,k2_tarski(X15,X15),X17),sK2(X13,X14,k2_tarski(X15,X15)),k2_tarski(X15,X15)) = X15
    | k2_tarski(X15,X15) = k2_tarski(sK2(X13,X14,k2_tarski(X15,X15)),sK3(X16,k2_tarski(X15,X15),X17))
    | ~ m1_subset_1(X17,u1_struct_0(X16))
    | ~ l1_orders_2(X16)
    | sK2(X13,X14,k2_tarski(X15,X15)) = X14
    | sK2(X13,X14,k2_tarski(X15,X15)) = X13
    | k2_tarski(X13,X14) = k2_tarski(X15,X15) )).

cnf(u2444,axiom,
    ( r1_lattice3(X13,k2_tarski(X12,X12),X14)
    | ~ m1_subset_1(X14,u1_struct_0(X13))
    | ~ l1_orders_2(X13)
    | sK2(X10,X11,k2_tarski(X12,X12)) = sK3(X13,k2_tarski(X12,X12),X14)
    | sK3(X13,k2_tarski(X12,X12),X14) = X12
    | sK2(X10,X11,k2_tarski(X12,X12)) = X11
    | sK2(X10,X11,k2_tarski(X12,X12)) = X10
    | k2_tarski(X10,X11) = k2_tarski(X12,X12) )).

cnf(u2258,axiom,
    ( r1_lattice3(X5,k2_tarski(X6,X6),X7)
    | sK2(X4,sK3(X5,k2_tarski(X6,X6),X7),k2_tarski(X6,X6)) = X4
    | sK2(X4,sK3(X5,k2_tarski(X6,X6),X7),k2_tarski(X6,X6)) = X6
    | k2_tarski(X6,X6) = k2_tarski(X4,sK3(X5,k2_tarski(X6,X6),X7))
    | ~ m1_subset_1(X7,u1_struct_0(X5))
    | ~ l1_orders_2(X5) )).

cnf(u2246,axiom,
    ( r1_lattice3(X5,k2_tarski(X4,X4),X6)
    | sK2(sK3(X5,k2_tarski(X4,X4),X6),X7,k2_tarski(X4,X4)) = X7
    | sK2(sK3(X5,k2_tarski(X4,X4),X6),X7,k2_tarski(X4,X4)) = X4
    | k2_tarski(X4,X4) = k2_tarski(sK3(X5,k2_tarski(X4,X4),X6),X7)
    | ~ m1_subset_1(X6,u1_struct_0(X5))
    | ~ l1_orders_2(X5) )).

cnf(u990,axiom,
    ( r1_lattice3(X3,k2_tarski(X2,X2),X4)
    | k2_tarski(X2,X2) = k2_tarski(X2,sK3(X3,k2_tarski(X2,X2),X4))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ l1_orders_2(X3) )).

cnf(u417,axiom,
    ( r1_lattice3(X2,k2_tarski(X3,X3),X4)
    | sK2(sK3(X2,k2_tarski(X3,X3),X4),sK3(X2,k2_tarski(X3,X3),X4),k2_tarski(X3,X3)) = X3
    | k2_tarski(X3,X3) = k2_tarski(sK3(X2,k2_tarski(X3,X3),X4),sK3(X2,k2_tarski(X3,X3),X4))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X2) )).

cnf(u2779,axiom,
    ( r1_lattice3(X10,k2_tarski(X8,X9),X11)
    | sK2(sK3(X10,k2_tarski(X8,X9),X11),sK2(X12,X13,k2_tarski(X8,X9)),k2_tarski(X8,X9)) = X8
    | sK2(sK3(X10,k2_tarski(X8,X9),X11),sK2(X12,X13,k2_tarski(X8,X9)),k2_tarski(X8,X9)) = X9
    | sK2(X12,X13,k2_tarski(X8,X9)) = X13
    | sK2(X12,X13,k2_tarski(X8,X9)) = X12
    | k2_tarski(X8,X9) = k2_tarski(X12,X13)
    | k2_tarski(X8,X9) = k2_tarski(sK3(X10,k2_tarski(X8,X9),X11),sK2(X12,X13,k2_tarski(X8,X9)))
    | ~ m1_subset_1(X11,u1_struct_0(X10))
    | ~ l1_orders_2(X10) )).

cnf(u2658,axiom,
    ( r1_lattice3(X12,k2_tarski(X8,X9),X13)
    | sK2(sK2(X10,X11,k2_tarski(X8,X9)),sK3(X12,k2_tarski(X8,X9),X13),k2_tarski(X8,X9)) = X8
    | sK2(sK2(X10,X11,k2_tarski(X8,X9)),sK3(X12,k2_tarski(X8,X9),X13),k2_tarski(X8,X9)) = X9
    | sK2(X10,X11,k2_tarski(X8,X9)) = X11
    | sK2(X10,X11,k2_tarski(X8,X9)) = X10
    | k2_tarski(X10,X11) = k2_tarski(X8,X9)
    | k2_tarski(X8,X9) = k2_tarski(sK2(X10,X11,k2_tarski(X8,X9)),sK3(X12,k2_tarski(X8,X9),X13))
    | ~ m1_subset_1(X13,u1_struct_0(X12))
    | ~ l1_orders_2(X12) )).

cnf(u2611,axiom,
    ( r1_lattice3(X2,k2_tarski(X1,X0),X3)
    | sK2(X0,sK3(X2,k2_tarski(X1,X0),X3),k2_tarski(X1,X0)) = X1
    | k2_tarski(X1,X0) = k2_tarski(X0,sK3(X2,k2_tarski(X1,X0),X3))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_orders_2(X2) )).

cnf(u2603,axiom,
    ( r1_lattice3(X2,k2_tarski(X1,X0),X3)
    | sK2(sK3(X2,k2_tarski(X1,X0),X3),X0,k2_tarski(X1,X0)) = X1
    | k2_tarski(X1,X0) = k2_tarski(X0,sK3(X2,k2_tarski(X1,X0),X3))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_orders_2(X2) )).

cnf(u2251,axiom,
    ( r1_lattice3(X6,k2_tarski(X4,X5),X7)
    | sK2(X4,sK3(X6,k2_tarski(X4,X5),X7),k2_tarski(X4,X5)) = X5
    | k2_tarski(X4,X5) = k2_tarski(X4,sK3(X6,k2_tarski(X4,X5),X7))
    | ~ m1_subset_1(X7,u1_struct_0(X6))
    | ~ l1_orders_2(X6) )).

cnf(u1941,axiom,
    ( r1_lattice3(X4,k2_tarski(X5,X6),X7)
    | sK2(sK3(X4,k2_tarski(X5,X6),X7),X5,k2_tarski(X5,X6)) = X6
    | k2_tarski(X5,X6) = k2_tarski(X5,sK3(X4,k2_tarski(X5,X6),X7))
    | ~ m1_subset_1(X7,u1_struct_0(X4))
    | ~ l1_orders_2(X4) )).

cnf(u1778,axiom,
    ( r1_lattice3(X6,k2_tarski(X4,X5),X7)
    | sK2(sK3(X6,k2_tarski(X4,X5),X7),sK3(X6,k2_tarski(X4,X5),X7),k2_tarski(X4,X5)) = X4
    | sK2(sK3(X6,k2_tarski(X4,X5),X7),sK3(X6,k2_tarski(X4,X5),X7),k2_tarski(X4,X5)) = X5
    | k2_tarski(X4,X5) = k2_tarski(sK3(X6,k2_tarski(X4,X5),X7),sK3(X6,k2_tarski(X4,X5),X7))
    | ~ m1_subset_1(X7,u1_struct_0(X6))
    | ~ l1_orders_2(X6) )).

cnf(u312,axiom,
    ( r1_lattice3(X9,k2_tarski(X6,X7),X10)
    | sK2(X8,sK3(X9,k2_tarski(X6,X7),X10),k2_tarski(X6,X7)) = X8
    | sK2(X8,sK3(X9,k2_tarski(X6,X7),X10),k2_tarski(X6,X7)) = X6
    | sK2(X8,sK3(X9,k2_tarski(X6,X7),X10),k2_tarski(X6,X7)) = X7
    | k2_tarski(X6,X7) = k2_tarski(X8,sK3(X9,k2_tarski(X6,X7),X10))
    | ~ m1_subset_1(X10,u1_struct_0(X9))
    | ~ l1_orders_2(X9) )).

cnf(u286,axiom,
    ( r1_lattice3(X8,k2_tarski(X6,X7),X9)
    | sK2(sK3(X8,k2_tarski(X6,X7),X9),X10,k2_tarski(X6,X7)) = X10
    | sK2(sK3(X8,k2_tarski(X6,X7),X9),X10,k2_tarski(X6,X7)) = X6
    | sK2(sK3(X8,k2_tarski(X6,X7),X9),X10,k2_tarski(X6,X7)) = X7
    | k2_tarski(X6,X7) = k2_tarski(sK3(X8,k2_tarski(X6,X7),X9),X10)
    | ~ m1_subset_1(X9,u1_struct_0(X8))
    | ~ l1_orders_2(X8) )).

cnf(u82,axiom,
    ( r1_lattice3(X0,k2_tarski(X1,X2),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK3(X0,k2_tarski(X1,X2),X3) = X1
    | sK3(X0,k2_tarski(X1,X2),X3) = X2 )).

cnf(u60,axiom,
    ( r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u84,negated_conjecture,
    ( r1_lattice3(sK0,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | k2_tarski(sK3(sK0,X0,X1),sK3(sK0,X0,X1)) = k6_domain_1(u1_struct_0(sK0),sK3(sK0,X0,X1))
    | ~ l1_struct_0(sK0) )).

cnf(u57,axiom,
    ( r1_orders_2(X0,X2,X4)
    | ~ r2_hidden(X4,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u61,axiom,
    ( r1_orders_2(X0,X4,X2)
    | ~ r2_hidden(X4,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u54,axiom,
    ( r1_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u41,negated_conjecture,
    ( v3_orders_2(sK0) )).

cnf(u62,axiom,
    ( m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
    | r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u58,axiom,
    ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
    | r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u44,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

cnf(u76,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k2_tarski(X0,X0) = k6_domain_1(u1_struct_0(sK0),X0)
    | ~ l1_struct_0(sK0) )).

cnf(u43,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u65,axiom,
    ( v1_xboole_0(X0)
    | ~ m1_subset_1(X1,X0)
    | k6_domain_1(X0,X1) = k2_tarski(X1,X1) )).

cnf(u73,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(sK0) )).

cnf(u56,axiom,
    ( l1_struct_0(X0)
    | ~ l1_orders_2(X0) )).

cnf(u55,axiom,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) )).

cnf(u40,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u49,axiom,
    ( r2_hidden(sK2(X0,X1,X2),X2)
    | sK2(X0,X1,X2) = X1
    | sK2(X0,X1,X2) = X0
    | k2_tarski(X0,X1) = X2 )).

cnf(u63,axiom,
    ( r2_hidden(sK4(X0,X1,X2),X1)
    | r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u59,axiom,
    ( r2_hidden(sK3(X0,X1,X2),X1)
    | r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u69,axiom,
    ( r2_hidden(X4,k2_tarski(X4,X1)) )).

cnf(u67,axiom,
    ( r2_hidden(X4,k2_tarski(X0,X4)) )).

cnf(u943,axiom,
    ( ~ r2_hidden(X40,k2_tarski(X40,X40))
    | k2_tarski(X40,X40) = k2_tarski(X39,X40)
    | sK2(X39,X40,k2_tarski(X40,X40)) = X39 )).

cnf(u1703,axiom,
    ( ~ r2_hidden(X58,k2_tarski(X58,X58))
    | k2_tarski(X58,X59) = k2_tarski(X58,X58)
    | sK2(X58,X59,k2_tarski(X58,X58)) = X59 )).

cnf(u214,axiom,
    ( ~ r2_hidden(X12,k2_tarski(X12,X13))
    | k2_tarski(X12,X12) = k2_tarski(X12,X13)
    | sK2(X12,X12,k2_tarski(X12,X13)) = X13 )).

cnf(u818,axiom,
    ( ~ r2_hidden(X38,k2_tarski(X38,X37))
    | k2_tarski(X38,X37) = k2_tarski(X37,X38) )).

cnf(u410,axiom,
    ( ~ r2_hidden(X19,k2_tarski(X19,X20))
    | k2_tarski(X19,X20) = k2_tarski(X18,X19)
    | sK2(X18,X19,k2_tarski(X19,X20)) = X18
    | sK2(X18,X19,k2_tarski(X19,X20)) = X20 )).

cnf(u570,axiom,
    ( ~ r2_hidden(X27,k2_tarski(X27,X29))
    | k2_tarski(X27,X29) = k2_tarski(X27,X28)
    | sK2(X27,X28,k2_tarski(X27,X29)) = X28
    | sK2(X27,X28,k2_tarski(X27,X29)) = X29 )).

cnf(u2511,axiom,
    ( ~ r2_hidden(X294,k2_tarski(X293,X293))
    | k2_tarski(X293,X293) = k2_tarski(sK2(X291,X292,k2_tarski(X293,X293)),X294)
    | sK2(sK2(X291,X292,k2_tarski(X293,X293)),X294,k2_tarski(X293,X293)) = X293
    | sK2(X291,X292,k2_tarski(X293,X293)) = X292
    | sK2(X291,X292,k2_tarski(X293,X293)) = X291
    | k2_tarski(X293,X293) = k2_tarski(X291,X292) )).

cnf(u2503,axiom,
    ( ~ r2_hidden(X262,k2_tarski(X261,X261))
    | k2_tarski(X261,X261) = k2_tarski(X262,sK2(X259,X260,k2_tarski(X261,X261)))
    | sK2(X262,sK2(X259,X260,k2_tarski(X261,X261)),k2_tarski(X261,X261)) = X261
    | sK2(X259,X260,k2_tarski(X261,X261)) = X260
    | sK2(X259,X260,k2_tarski(X261,X261)) = X259
    | k2_tarski(X261,X261) = k2_tarski(X259,X260) )).

cnf(u2443,axiom,
    ( ~ r2_hidden(X9,k2_tarski(X8,X8))
    | sK2(X6,X7,k2_tarski(X8,X8)) = X9
    | X8 = X9
    | sK2(X6,X7,k2_tarski(X8,X8)) = X7
    | sK2(X6,X7,k2_tarski(X8,X8)) = X6
    | k2_tarski(X6,X7) = k2_tarski(X8,X8) )).

cnf(u1755,axiom,
    ( ~ r2_hidden(X65,k2_tarski(X64,X64))
    | k2_tarski(X64,X64) = k2_tarski(X64,X65) )).

cnf(u981,axiom,
    ( ~ r2_hidden(X41,k2_tarski(X42,X42))
    | k2_tarski(X42,X42) = k2_tarski(X41,X42) )).

cnf(u796,axiom,
    ( ~ r2_hidden(X45,k2_tarski(X46,X46))
    | k2_tarski(X44,X45) = k2_tarski(X46,X46)
    | sK2(X44,X45,k2_tarski(X46,X46)) = X44
    | sK2(X44,X45,k2_tarski(X46,X46)) = X46 )).

cnf(u794,axiom,
    ( ~ r2_hidden(X41,k2_tarski(X43,X43))
    | k2_tarski(X43,X43) = k2_tarski(X41,X42)
    | sK2(X41,X42,k2_tarski(X43,X43)) = X42
    | sK2(X41,X42,k2_tarski(X43,X43)) = X43 )).

cnf(u346,axiom,
    ( ~ r2_hidden(X12,k2_tarski(X13,X13))
    | k2_tarski(X12,X12) = k2_tarski(X13,X13)
    | sK2(X12,X12,k2_tarski(X13,X13)) = X13 )).

cnf(u275,axiom,
    ( ~ r2_hidden(X12,k2_tarski(X13,X12))
    | k2_tarski(X12,X12) = k2_tarski(X13,X12)
    | sK2(X12,X12,k2_tarski(X13,X12)) = X13 )).

cnf(u700,axiom,
    ( ~ r2_hidden(X28,k2_tarski(X29,X28))
    | k2_tarski(X29,X28) = k2_tarski(X28,X29)
    | sK2(X28,X29,k2_tarski(X29,X28)) = X29 )).

cnf(u484,axiom,
    ( ~ r2_hidden(X25,k2_tarski(X26,X25))
    | k2_tarski(X26,X25) = k2_tarski(X24,X25)
    | sK2(X24,X25,k2_tarski(X26,X25)) = X24
    | sK2(X24,X25,k2_tarski(X26,X25)) = X26 )).

cnf(u658,axiom,
    ( ~ r2_hidden(X33,k2_tarski(X35,X33))
    | k2_tarski(X33,X34) = k2_tarski(X35,X33)
    | sK2(X33,X34,k2_tarski(X35,X33)) = X34
    | sK2(X33,X34,k2_tarski(X35,X33)) = X35 )).

cnf(u2254,axiom,
    ( ~ r2_hidden(X2,k2_tarski(X1,X0))
    | k2_tarski(X1,X0) = k2_tarski(X0,X2)
    | sK2(X0,X2,k2_tarski(X1,X0)) = X1 )).

cnf(u2231,axiom,
    ( ~ r2_hidden(X96,k2_tarski(X95,X97))
    | k2_tarski(X95,X97) = k2_tarski(X95,X96)
    | sK2(X95,X96,k2_tarski(X95,X97)) = X97 )).

cnf(u1939,axiom,
    ( ~ r2_hidden(X2,k2_tarski(X1,X0))
    | k2_tarski(X1,X0) = k2_tarski(X2,X0)
    | sK2(X2,X0,k2_tarski(X1,X0)) = X1 )).

cnf(u1911,axiom,
    ( ~ r2_hidden(X87,k2_tarski(X88,X89))
    | k2_tarski(X87,X88) = k2_tarski(X88,X89)
    | sK2(X87,X88,k2_tarski(X88,X89)) = X89 )).

cnf(u1563,axiom,
    ( ~ r2_hidden(X79,k2_tarski(X82,X83))
    | k2_tarski(X82,X83) = k2_tarski(X79,sK2(X80,X81,k2_tarski(X82,X83)))
    | sK2(X79,sK2(X80,X81,k2_tarski(X82,X83)),k2_tarski(X82,X83)) = X82
    | sK2(X79,sK2(X80,X81,k2_tarski(X82,X83)),k2_tarski(X82,X83)) = X83
    | sK2(X80,X81,k2_tarski(X82,X83)) = X81
    | sK2(X80,X81,k2_tarski(X82,X83)) = X80
    | k2_tarski(X82,X83) = k2_tarski(X80,X81) )).

cnf(u1227,axiom,
    ( ~ r2_hidden(X79,k2_tarski(X77,X78))
    | k2_tarski(X77,X78) = k2_tarski(sK2(X75,X76,k2_tarski(X77,X78)),X79)
    | sK2(sK2(X75,X76,k2_tarski(X77,X78)),X79,k2_tarski(X77,X78)) = X77
    | sK2(sK2(X75,X76,k2_tarski(X77,X78)),X79,k2_tarski(X77,X78)) = X78
    | sK2(X75,X76,k2_tarski(X77,X78)) = X76
    | sK2(X75,X76,k2_tarski(X77,X78)) = X75
    | k2_tarski(X75,X76) = k2_tarski(X77,X78) )).

cnf(u663,axiom,
    ( ~ r2_hidden(X37,k2_tarski(X38,X36))
    | k2_tarski(X36,X37) = k2_tarski(X38,X36)
    | sK2(X36,X37,k2_tarski(X38,X36)) = X38
    | sK2(X36,X37,k2_tarski(X38,X36)) = X36 )).

cnf(u572,axiom,
    ( ~ r2_hidden(X31,k2_tarski(X30,X32))
    | k2_tarski(X30,X32) = k2_tarski(X30,X31)
    | sK2(X30,X31,k2_tarski(X30,X32)) = X30
    | sK2(X30,X31,k2_tarski(X30,X32)) = X32 )).

cnf(u491,axiom,
    ( ~ r2_hidden(X21,k2_tarski(X23,X22))
    | k2_tarski(X23,X22) = k2_tarski(X21,X22)
    | sK2(X21,X22,k2_tarski(X23,X22)) = X23
    | sK2(X21,X22,k2_tarski(X23,X22)) = X22 )).

cnf(u414,axiom,
    ( ~ r2_hidden(X15,k2_tarski(X16,X17))
    | k2_tarski(X16,X17) = k2_tarski(X15,X16)
    | sK2(X15,X16,k2_tarski(X16,X17)) = X16
    | sK2(X15,X16,k2_tarski(X16,X17)) = X17 )).

cnf(u181,axiom,
    ( ~ r2_hidden(X18,k2_tarski(X19,X20))
    | k2_tarski(X19,X20) = k2_tarski(X18,X18)
    | sK2(X18,X18,k2_tarski(X19,X20)) = X19
    | sK2(X18,X18,k2_tarski(X19,X20)) = X20 )).

cnf(u133,axiom,
    ( ~ r2_hidden(X9,k2_tarski(X10,X11))
    | k2_tarski(X10,X11) = k2_tarski(X8,X9)
    | sK2(X8,X9,k2_tarski(X10,X11)) = X8
    | sK2(X8,X9,k2_tarski(X10,X11)) = X10
    | sK2(X8,X9,k2_tarski(X10,X11)) = X11 )).

cnf(u131,axiom,
    ( ~ r2_hidden(X4,k2_tarski(X6,X7))
    | k2_tarski(X6,X7) = k2_tarski(X4,X5)
    | sK2(X4,X5,k2_tarski(X6,X7)) = X5
    | sK2(X4,X5,k2_tarski(X6,X7)) = X6
    | sK2(X4,X5,k2_tarski(X6,X7)) = X7 )).

cnf(u70,axiom,
    ( ~ r2_hidden(X4,k2_tarski(X0,X1))
    | X0 = X4
    | X1 = X4 )).

cnf(u1763,axiom,
    ( k2_tarski(X8,X8) = k2_tarski(X8,sK2(X9,X10,k2_tarski(X8,X8)))
    | sK2(X9,X10,k2_tarski(X8,X8)) = X10
    | sK2(X9,X10,k2_tarski(X8,X8)) = X9
    | k2_tarski(X8,X8) = k2_tarski(X9,X10) )).

cnf(u989,axiom,
    ( k2_tarski(X8,X8) = k2_tarski(sK2(X9,X10,k2_tarski(X8,X8)),X8)
    | sK2(X9,X10,k2_tarski(X8,X8)) = X10
    | sK2(X9,X10,k2_tarski(X8,X8)) = X9
    | k2_tarski(X8,X8) = k2_tarski(X9,X10) )).

cnf(u823,axiom,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) )).

cnf(u5150,axiom,
    ( sK2(sK2(X0,X1,k2_tarski(X2,X2)),sK2(X3,X4,k2_tarski(X2,X2)),k2_tarski(X2,X2)) = X2
    | k2_tarski(X2,X2) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X2)),sK2(X3,X4,k2_tarski(X2,X2)))
    | sK2(X0,X1,k2_tarski(X2,X2)) = X1
    | sK2(X0,X1,k2_tarski(X2,X2)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X2)
    | sK2(X3,X4,k2_tarski(X2,X2)) = X4
    | sK2(X3,X4,k2_tarski(X2,X2)) = X3
    | k2_tarski(X2,X2) = k2_tarski(X3,X4) )).

cnf(u2724,axiom,
    ( sK2(sK2(X16,X17,k2_tarski(X15,X15)),sK2(X13,X14,k2_tarski(X15,X15)),k2_tarski(X15,X15)) = X15
    | k2_tarski(X15,X15) = k2_tarski(sK2(X13,X14,k2_tarski(X15,X15)),sK2(X16,X17,k2_tarski(X15,X15)))
    | sK2(X16,X17,k2_tarski(X15,X15)) = X17
    | sK2(X16,X17,k2_tarski(X15,X15)) = X16
    | k2_tarski(X16,X17) = k2_tarski(X15,X15)
    | sK2(X13,X14,k2_tarski(X15,X15)) = X14
    | sK2(X13,X14,k2_tarski(X15,X15)) = X13
    | k2_tarski(X13,X14) = k2_tarski(X15,X15) )).

cnf(u419,axiom,
    ( sK2(sK2(X8,X9,k2_tarski(X10,X10)),sK2(X8,X9,k2_tarski(X10,X10)),k2_tarski(X10,X10)) = X10
    | k2_tarski(X10,X10) = k2_tarski(sK2(X8,X9,k2_tarski(X10,X10)),sK2(X8,X9,k2_tarski(X10,X10)))
    | sK2(X8,X9,k2_tarski(X10,X10)) = X9
    | sK2(X8,X9,k2_tarski(X10,X10)) = X8
    | k2_tarski(X8,X9) = k2_tarski(X10,X10) )).

cnf(u2248,axiom,
    ( sK2(sK2(X13,X14,k2_tarski(X12,X12)),X15,k2_tarski(X12,X12)) = X15
    | sK2(sK2(X13,X14,k2_tarski(X12,X12)),X15,k2_tarski(X12,X12)) = X12
    | k2_tarski(X12,X12) = k2_tarski(sK2(X13,X14,k2_tarski(X12,X12)),X15)
    | sK2(X13,X14,k2_tarski(X12,X12)) = X14
    | sK2(X13,X14,k2_tarski(X12,X12)) = X13
    | k2_tarski(X13,X14) = k2_tarski(X12,X12) )).

cnf(u2248_001,axiom,
    ( sK2(sK2(X13,X14,k2_tarski(X12,X12)),X15,k2_tarski(X12,X12)) = X15
    | sK2(sK2(X13,X14,k2_tarski(X12,X12)),X15,k2_tarski(X12,X12)) = X12
    | k2_tarski(X12,X12) = k2_tarski(sK2(X13,X14,k2_tarski(X12,X12)),X15)
    | sK2(X13,X14,k2_tarski(X12,X12)) = X14
    | sK2(X13,X14,k2_tarski(X12,X12)) = X13
    | k2_tarski(X13,X14) = k2_tarski(X12,X12) )).

cnf(u2660,axiom,
    ( sK2(sK2(X22,X23,k2_tarski(X20,X21)),sK2(X24,X25,k2_tarski(X20,X21)),k2_tarski(X20,X21)) = X20
    | sK2(sK2(X22,X23,k2_tarski(X20,X21)),sK2(X24,X25,k2_tarski(X20,X21)),k2_tarski(X20,X21)) = X21
    | k2_tarski(X20,X21) = k2_tarski(sK2(X22,X23,k2_tarski(X20,X21)),sK2(X24,X25,k2_tarski(X20,X21)))
    | sK2(X22,X23,k2_tarski(X20,X21)) = X23
    | sK2(X22,X23,k2_tarski(X20,X21)) = X22
    | k2_tarski(X20,X21) = k2_tarski(X22,X23)
    | sK2(X24,X25,k2_tarski(X20,X21)) = X25
    | sK2(X24,X25,k2_tarski(X20,X21)) = X24
    | k2_tarski(X20,X21) = k2_tarski(X24,X25) )).

cnf(u2660_002,axiom,
    ( sK2(sK2(X22,X23,k2_tarski(X20,X21)),sK2(X24,X25,k2_tarski(X20,X21)),k2_tarski(X20,X21)) = X20
    | sK2(sK2(X22,X23,k2_tarski(X20,X21)),sK2(X24,X25,k2_tarski(X20,X21)),k2_tarski(X20,X21)) = X21
    | k2_tarski(X20,X21) = k2_tarski(sK2(X22,X23,k2_tarski(X20,X21)),sK2(X24,X25,k2_tarski(X20,X21)))
    | sK2(X22,X23,k2_tarski(X20,X21)) = X23
    | sK2(X22,X23,k2_tarski(X20,X21)) = X22
    | k2_tarski(X20,X21) = k2_tarski(X22,X23)
    | sK2(X24,X25,k2_tarski(X20,X21)) = X25
    | sK2(X24,X25,k2_tarski(X20,X21)) = X24
    | k2_tarski(X20,X21) = k2_tarski(X24,X25) )).

cnf(u1780,axiom,
    ( sK2(sK2(X14,X15,k2_tarski(X12,X13)),sK2(X14,X15,k2_tarski(X12,X13)),k2_tarski(X12,X13)) = X12
    | sK2(sK2(X14,X15,k2_tarski(X12,X13)),sK2(X14,X15,k2_tarski(X12,X13)),k2_tarski(X12,X13)) = X13
    | k2_tarski(X12,X13) = k2_tarski(sK2(X14,X15,k2_tarski(X12,X13)),sK2(X14,X15,k2_tarski(X12,X13)))
    | sK2(X14,X15,k2_tarski(X12,X13)) = X15
    | sK2(X14,X15,k2_tarski(X12,X13)) = X14
    | k2_tarski(X14,X15) = k2_tarski(X12,X13) )).

cnf(u1780_003,axiom,
    ( sK2(sK2(X14,X15,k2_tarski(X12,X13)),sK2(X14,X15,k2_tarski(X12,X13)),k2_tarski(X12,X13)) = X12
    | sK2(sK2(X14,X15,k2_tarski(X12,X13)),sK2(X14,X15,k2_tarski(X12,X13)),k2_tarski(X12,X13)) = X13
    | k2_tarski(X12,X13) = k2_tarski(sK2(X14,X15,k2_tarski(X12,X13)),sK2(X14,X15,k2_tarski(X12,X13)))
    | sK2(X14,X15,k2_tarski(X12,X13)) = X15
    | sK2(X14,X15,k2_tarski(X12,X13)) = X14
    | k2_tarski(X14,X15) = k2_tarski(X12,X13) )).

cnf(u288,axiom,
    ( sK2(sK2(X18,X19,k2_tarski(X16,X17)),X20,k2_tarski(X16,X17)) = X20
    | sK2(sK2(X18,X19,k2_tarski(X16,X17)),X20,k2_tarski(X16,X17)) = X16
    | sK2(sK2(X18,X19,k2_tarski(X16,X17)),X20,k2_tarski(X16,X17)) = X17
    | k2_tarski(X16,X17) = k2_tarski(sK2(X18,X19,k2_tarski(X16,X17)),X20)
    | sK2(X18,X19,k2_tarski(X16,X17)) = X19
    | sK2(X18,X19,k2_tarski(X16,X17)) = X18
    | k2_tarski(X16,X17) = k2_tarski(X18,X19) )).

cnf(u288_004,axiom,
    ( sK2(sK2(X18,X19,k2_tarski(X16,X17)),X20,k2_tarski(X16,X17)) = X20
    | sK2(sK2(X18,X19,k2_tarski(X16,X17)),X20,k2_tarski(X16,X17)) = X16
    | sK2(sK2(X18,X19,k2_tarski(X16,X17)),X20,k2_tarski(X16,X17)) = X17
    | k2_tarski(X16,X17) = k2_tarski(sK2(X18,X19,k2_tarski(X16,X17)),X20)
    | sK2(X18,X19,k2_tarski(X16,X17)) = X19
    | sK2(X18,X19,k2_tarski(X16,X17)) = X18
    | k2_tarski(X16,X17) = k2_tarski(X18,X19) )).

cnf(u288_005,axiom,
    ( sK2(sK2(X18,X19,k2_tarski(X16,X17)),X20,k2_tarski(X16,X17)) = X20
    | sK2(sK2(X18,X19,k2_tarski(X16,X17)),X20,k2_tarski(X16,X17)) = X16
    | sK2(sK2(X18,X19,k2_tarski(X16,X17)),X20,k2_tarski(X16,X17)) = X17
    | k2_tarski(X16,X17) = k2_tarski(sK2(X18,X19,k2_tarski(X16,X17)),X20)
    | sK2(X18,X19,k2_tarski(X16,X17)) = X19
    | sK2(X18,X19,k2_tarski(X16,X17)) = X18
    | k2_tarski(X16,X17) = k2_tarski(X18,X19) )).

cnf(u2721,axiom,
    ( sK2(sK2(X2,X3,k2_tarski(X1,X0)),X0,k2_tarski(X1,X0)) = X1
    | k2_tarski(X1,X0) = k2_tarski(X0,sK2(X2,X3,k2_tarski(X1,X0)))
    | sK2(X2,X3,k2_tarski(X1,X0)) = X3
    | sK2(X2,X3,k2_tarski(X1,X0)) = X2
    | k2_tarski(X1,X0) = k2_tarski(X2,X3) )).

cnf(u1943,axiom,
    ( sK2(sK2(X12,X13,k2_tarski(X14,X15)),X14,k2_tarski(X14,X15)) = X15
    | k2_tarski(X14,X15) = k2_tarski(X14,sK2(X12,X13,k2_tarski(X14,X15)))
    | sK2(X12,X13,k2_tarski(X14,X15)) = X13
    | sK2(X12,X13,k2_tarski(X14,X15)) = X12
    | k2_tarski(X14,X15) = k2_tarski(X12,X13) )).

cnf(u2253,axiom,
    ( sK2(X12,sK2(X14,X15,k2_tarski(X12,X13)),k2_tarski(X12,X13)) = X13
    | k2_tarski(X12,X13) = k2_tarski(X12,sK2(X14,X15,k2_tarski(X12,X13)))
    | sK2(X14,X15,k2_tarski(X12,X13)) = X15
    | sK2(X14,X15,k2_tarski(X12,X13)) = X14
    | k2_tarski(X14,X15) = k2_tarski(X12,X13) )).

cnf(u2260,axiom,
    ( sK2(X12,sK2(X13,X14,k2_tarski(X15,X15)),k2_tarski(X15,X15)) = X12
    | sK2(X12,sK2(X13,X14,k2_tarski(X15,X15)),k2_tarski(X15,X15)) = X15
    | k2_tarski(X15,X15) = k2_tarski(X12,sK2(X13,X14,k2_tarski(X15,X15)))
    | sK2(X13,X14,k2_tarski(X15,X15)) = X14
    | sK2(X13,X14,k2_tarski(X15,X15)) = X13
    | k2_tarski(X13,X14) = k2_tarski(X15,X15) )).

cnf(u2260_006,axiom,
    ( sK2(X12,sK2(X13,X14,k2_tarski(X15,X15)),k2_tarski(X15,X15)) = X12
    | sK2(X12,sK2(X13,X14,k2_tarski(X15,X15)),k2_tarski(X15,X15)) = X15
    | k2_tarski(X15,X15) = k2_tarski(X12,sK2(X13,X14,k2_tarski(X15,X15)))
    | sK2(X13,X14,k2_tarski(X15,X15)) = X14
    | sK2(X13,X14,k2_tarski(X15,X15)) = X13
    | k2_tarski(X13,X14) = k2_tarski(X15,X15) )).

cnf(u2842,axiom,
    ( sK2(X0,sK2(X2,X3,k2_tarski(X1,X0)),k2_tarski(X1,X0)) = X1
    | k2_tarski(X1,X0) = k2_tarski(X0,sK2(X2,X3,k2_tarski(X1,X0)))
    | sK2(X2,X3,k2_tarski(X1,X0)) = X3
    | sK2(X2,X3,k2_tarski(X1,X0)) = X2
    | k2_tarski(X1,X0) = k2_tarski(X2,X3) )).

cnf(u314,axiom,
    ( sK2(X18,sK2(X19,X20,k2_tarski(X16,X17)),k2_tarski(X16,X17)) = X18
    | sK2(X18,sK2(X19,X20,k2_tarski(X16,X17)),k2_tarski(X16,X17)) = X16
    | sK2(X18,sK2(X19,X20,k2_tarski(X16,X17)),k2_tarski(X16,X17)) = X17
    | k2_tarski(X16,X17) = k2_tarski(X18,sK2(X19,X20,k2_tarski(X16,X17)))
    | sK2(X19,X20,k2_tarski(X16,X17)) = X20
    | sK2(X19,X20,k2_tarski(X16,X17)) = X19
    | k2_tarski(X16,X17) = k2_tarski(X19,X20) )).

cnf(u314_007,axiom,
    ( sK2(X18,sK2(X19,X20,k2_tarski(X16,X17)),k2_tarski(X16,X17)) = X18
    | sK2(X18,sK2(X19,X20,k2_tarski(X16,X17)),k2_tarski(X16,X17)) = X16
    | sK2(X18,sK2(X19,X20,k2_tarski(X16,X17)),k2_tarski(X16,X17)) = X17
    | k2_tarski(X16,X17) = k2_tarski(X18,sK2(X19,X20,k2_tarski(X16,X17)))
    | sK2(X19,X20,k2_tarski(X16,X17)) = X20
    | sK2(X19,X20,k2_tarski(X16,X17)) = X19
    | k2_tarski(X16,X17) = k2_tarski(X19,X20) )).

cnf(u314_008,axiom,
    ( sK2(X18,sK2(X19,X20,k2_tarski(X16,X17)),k2_tarski(X16,X17)) = X18
    | sK2(X18,sK2(X19,X20,k2_tarski(X16,X17)),k2_tarski(X16,X17)) = X16
    | sK2(X18,sK2(X19,X20,k2_tarski(X16,X17)),k2_tarski(X16,X17)) = X17
    | k2_tarski(X16,X17) = k2_tarski(X18,sK2(X19,X20,k2_tarski(X16,X17)))
    | sK2(X19,X20,k2_tarski(X16,X17)) = X20
    | sK2(X19,X20,k2_tarski(X16,X17)) = X19
    | k2_tarski(X16,X17) = k2_tarski(X19,X20) )).

cnf(u185,axiom,
    ( sK2(X0,X0,k2_tarski(X0,X1)) = X0
    | sK2(X0,X0,k2_tarski(X0,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X0,X0) )).

cnf(u222,axiom,
    ( sK2(X1,X1,k2_tarski(X1,X2)) = X2
    | k2_tarski(X1,X1) = k2_tarski(X1,X2) )).

cnf(u185_009,axiom,
    ( sK2(X0,X0,k2_tarski(X0,X1)) = X0
    | sK2(X0,X0,k2_tarski(X0,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X0,X0) )).

cnf(u317,axiom,
    ( sK2(X0,X0,k2_tarski(X1,X1)) = X0
    | sK2(X0,X0,k2_tarski(X1,X1)) = X1
    | k2_tarski(X0,X0) = k2_tarski(X1,X1) )).

cnf(u317_010,axiom,
    ( sK2(X0,X0,k2_tarski(X1,X1)) = X0
    | sK2(X0,X0,k2_tarski(X1,X1)) = X1
    | k2_tarski(X0,X0) = k2_tarski(X1,X1) )).

cnf(u248,axiom,
    ( sK2(X0,X0,k2_tarski(X1,X0)) = X1
    | sK2(X0,X0,k2_tarski(X1,X0)) = X0
    | k2_tarski(X0,X0) = k2_tarski(X1,X0) )).

cnf(u248_011,axiom,
    ( sK2(X0,X0,k2_tarski(X1,X0)) = X1
    | sK2(X0,X0,k2_tarski(X1,X0)) = X0
    | k2_tarski(X0,X0) = k2_tarski(X1,X0) )).

cnf(u289,axiom,
    ( sK2(X0,X0,k2_tarski(X1,X0)) = X1
    | k2_tarski(X0,X0) = k2_tarski(X1,X0) )).

cnf(u135,axiom,
    ( sK2(X0,X0,k2_tarski(X1,X2)) = X0
    | sK2(X0,X0,k2_tarski(X1,X2)) = X1
    | sK2(X0,X0,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X0) = k2_tarski(X1,X2) )).

cnf(u135_012,axiom,
    ( sK2(X0,X0,k2_tarski(X1,X2)) = X0
    | sK2(X0,X0,k2_tarski(X1,X2)) = X1
    | sK2(X0,X0,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X0) = k2_tarski(X1,X2) )).

cnf(u135_013,axiom,
    ( sK2(X0,X0,k2_tarski(X1,X2)) = X0
    | sK2(X0,X0,k2_tarski(X1,X2)) = X1
    | sK2(X0,X0,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X0) = k2_tarski(X1,X2) )).

cnf(u1646,axiom,
    ( sK2(X0,X1,k2_tarski(X0,X0)) = X1
    | sK2(X0,X1,k2_tarski(X0,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X0,X0) )).

cnf(u1646_014,axiom,
    ( sK2(X0,X1,k2_tarski(X0,X0)) = X1
    | sK2(X0,X1,k2_tarski(X0,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X0,X0) )).

cnf(u1714,axiom,
    ( sK2(X0,X1,k2_tarski(X0,X0)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X0,X0) )).

cnf(u219,axiom,
    ( sK2(X0,X1,k2_tarski(X0,X2)) = X1
    | sK2(X0,X1,k2_tarski(X0,X2)) = X0
    | sK2(X0,X1,k2_tarski(X0,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u1965,axiom,
    ( sK2(X2,X4,k2_tarski(X2,X3)) = X4
    | sK2(X2,X4,k2_tarski(X2,X3)) = X3
    | k2_tarski(X2,X3) = k2_tarski(X2,X4) )).

cnf(u219_015,axiom,
    ( sK2(X0,X1,k2_tarski(X0,X2)) = X1
    | sK2(X0,X1,k2_tarski(X0,X2)) = X0
    | sK2(X0,X1,k2_tarski(X0,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u219_016,axiom,
    ( sK2(X0,X1,k2_tarski(X0,X2)) = X1
    | sK2(X0,X1,k2_tarski(X0,X2)) = X0
    | sK2(X0,X1,k2_tarski(X0,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u1965_017,axiom,
    ( sK2(X2,X4,k2_tarski(X2,X3)) = X4
    | sK2(X2,X4,k2_tarski(X2,X3)) = X3
    | k2_tarski(X2,X3) = k2_tarski(X2,X4) )).

cnf(u903,axiom,
    ( sK2(X0,X1,k2_tarski(X1,X1)) = X0
    | sK2(X0,X1,k2_tarski(X1,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X1,X1) )).

cnf(u903_018,axiom,
    ( sK2(X0,X1,k2_tarski(X1,X1)) = X0
    | sK2(X0,X1,k2_tarski(X1,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X1,X1) )).

cnf(u954,axiom,
    ( sK2(X1,X0,k2_tarski(X0,X0)) = X1
    | k2_tarski(X0,X0) = k2_tarski(X1,X0) )).

cnf(u667,axiom,
    ( sK2(X0,X1,k2_tarski(X1,X0)) = X1
    | sK2(X0,X1,k2_tarski(X1,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

cnf(u667_019,axiom,
    ( sK2(X0,X1,k2_tarski(X1,X0)) = X1
    | sK2(X0,X1,k2_tarski(X1,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

cnf(u800,axiom,
    ( sK2(X1,X0,k2_tarski(X0,X1)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

cnf(u136,axiom,
    ( sK2(X0,X1,k2_tarski(X1,X2)) = X0
    | sK2(X0,X1,k2_tarski(X1,X2)) = X1
    | sK2(X0,X1,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u1784,axiom,
    ( sK2(X4,X2,k2_tarski(X2,X3)) = X4
    | sK2(X4,X2,k2_tarski(X2,X3)) = X3
    | k2_tarski(X2,X3) = k2_tarski(X4,X2) )).

cnf(u136_020,axiom,
    ( sK2(X0,X1,k2_tarski(X1,X2)) = X0
    | sK2(X0,X1,k2_tarski(X1,X2)) = X1
    | sK2(X0,X1,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u136_021,axiom,
    ( sK2(X0,X1,k2_tarski(X1,X2)) = X0
    | sK2(X0,X1,k2_tarski(X1,X2)) = X1
    | sK2(X0,X1,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u1784_022,axiom,
    ( sK2(X4,X2,k2_tarski(X2,X3)) = X4
    | sK2(X4,X2,k2_tarski(X2,X3)) = X3
    | k2_tarski(X2,X3) = k2_tarski(X4,X2) )).

cnf(u86,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | sK2(X0,X1,k2_tarski(X2,X3)) = X2
    | sK2(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u86_023,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | sK2(X0,X1,k2_tarski(X2,X3)) = X2
    | sK2(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u86_024,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | sK2(X0,X1,k2_tarski(X2,X3)) = X2
    | sK2(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u86_025,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | sK2(X0,X1,k2_tarski(X2,X3)) = X2
    | sK2(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u246,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X2)) = X1
    | sK2(X0,X1,k2_tarski(X2,X2)) = X0
    | sK2(X0,X1,k2_tarski(X2,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u246_026,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X2)) = X1
    | sK2(X0,X1,k2_tarski(X2,X2)) = X0
    | sK2(X0,X1,k2_tarski(X2,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u246_027,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X2)) = X1
    | sK2(X0,X1,k2_tarski(X2,X2)) = X0
    | sK2(X0,X1,k2_tarski(X2,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u184,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X1)) = X0
    | sK2(X0,X1,k2_tarski(X2,X1)) = X2
    | sK2(X0,X1,k2_tarski(X2,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u184_028,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X1)) = X0
    | sK2(X0,X1,k2_tarski(X2,X1)) = X2
    | sK2(X0,X1,k2_tarski(X2,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u1930,axiom,
    ( sK2(X2,X1,k2_tarski(X0,X1)) = X2
    | sK2(X2,X1,k2_tarski(X0,X1)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u184_029,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X1)) = X0
    | sK2(X0,X1,k2_tarski(X2,X1)) = X2
    | sK2(X0,X1,k2_tarski(X2,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u1930_030,axiom,
    ( sK2(X2,X1,k2_tarski(X0,X1)) = X2
    | sK2(X2,X1,k2_tarski(X0,X1)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u223,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X0)) = X1
    | sK2(X0,X1,k2_tarski(X2,X0)) = X2
    | sK2(X0,X1,k2_tarski(X2,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u223_031,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X0)) = X1
    | sK2(X0,X1,k2_tarski(X2,X0)) = X2
    | sK2(X0,X1,k2_tarski(X2,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u2100,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X0)) = X1
    | sK2(X0,X1,k2_tarski(X2,X0)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u223_032,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X0)) = X1
    | sK2(X0,X1,k2_tarski(X2,X0)) = X2
    | sK2(X0,X1,k2_tarski(X2,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u2100_033,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X0)) = X1
    | sK2(X0,X1,k2_tarski(X2,X0)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u79,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) )).

cnf(u4839,axiom,
    ( X2 != X3
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X4,X5,k2_tarski(X2,X3)),k2_tarski(X2,X3)) = X2
    | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X4,X5,k2_tarski(X2,X3)))
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X3)
    | sK2(X4,X5,k2_tarski(X2,X3)) = X5
    | sK2(X4,X5,k2_tarski(X2,X3)) = X4
    | k2_tarski(X2,X3) = k2_tarski(X4,X5) )).

cnf(u4838,axiom,
    ( X2 != X3
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X4,X5,k2_tarski(X2,X3)),k2_tarski(X2,X3)) = X3
    | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X4,X5,k2_tarski(X2,X3)))
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X3)
    | sK2(X4,X5,k2_tarski(X2,X3)) = X5
    | sK2(X4,X5,k2_tarski(X2,X3)) = X4
    | k2_tarski(X2,X3) = k2_tarski(X4,X5) )).

cnf(u4277,axiom,
    ( X2 != X3
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X0,X1,k2_tarski(X2,X3)),k2_tarski(X2,X3)) = X2
    | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X0,X1,k2_tarski(X2,X3)))
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u4276,axiom,
    ( X2 != X3
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X0,X1,k2_tarski(X2,X3)),k2_tarski(X2,X3)) = X3
    | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X0,X1,k2_tarski(X2,X3)))
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u3858,axiom,
    ( X0 != X3
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X3)),k2_tarski(X3,X3)) = X0
    | k2_tarski(X3,X3) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X3)))
    | sK2(X1,X2,k2_tarski(X3,X3)) = X2
    | sK2(X1,X2,k2_tarski(X3,X3)) = X1
    | k2_tarski(X1,X2) = k2_tarski(X3,X3) )).

cnf(u3857,axiom,
    ( X0 != X3
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X3)),k2_tarski(X3,X3)) = X3
    | k2_tarski(X3,X3) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X3)))
    | sK2(X1,X2,k2_tarski(X3,X3)) = X2
    | sK2(X1,X2,k2_tarski(X3,X3)) = X1
    | k2_tarski(X1,X2) = k2_tarski(X3,X3) )).

cnf(u3581,axiom,
    ( X2 != X3
    | sK2(sK2(X0,X1,k2_tarski(X2,X2)),X3,k2_tarski(X2,X2)) = X3
    | k2_tarski(X2,X2) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X2)),X3)
    | sK2(X0,X1,k2_tarski(X2,X2)) = X1
    | sK2(X0,X1,k2_tarski(X2,X2)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u3580,axiom,
    ( X2 != X3
    | sK2(sK2(X0,X1,k2_tarski(X2,X2)),X3,k2_tarski(X2,X2)) = X2
    | k2_tarski(X2,X2) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X2)),X3)
    | sK2(X0,X1,k2_tarski(X2,X2)) = X1
    | sK2(X0,X1,k2_tarski(X2,X2)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u3035,axiom,
    ( X138 != X139
    | k2_tarski(X138,X139) = k2_tarski(X139,sK2(X136,X137,k2_tarski(X138,X139)))
    | ~ r2_hidden(X139,k2_tarski(X138,X139))
    | sK2(X136,X137,k2_tarski(X138,X139)) = X137
    | sK2(X136,X137,k2_tarski(X138,X139)) = X136
    | k2_tarski(X136,X137) = k2_tarski(X138,X139) )).

cnf(u2776,axiom,
    ( X127 != X128
    | k2_tarski(X127,X128) = k2_tarski(X127,sK2(X125,X126,k2_tarski(X127,X128)))
    | ~ r2_hidden(X127,k2_tarski(X127,X128))
    | sK2(X125,X126,k2_tarski(X127,X128)) = X126
    | sK2(X125,X126,k2_tarski(X127,X128)) = X125
    | k2_tarski(X125,X126) = k2_tarski(X127,X128) )).

cnf(u2404,axiom,
    ( X99 != X100
    | k2_tarski(X99,X100) = k2_tarski(X101,X99)
    | ~ r2_hidden(X99,k2_tarski(X101,X99))
    | sK2(X99,X100,k2_tarski(X101,X99)) = X101 )).

cnf(u2389,axiom,
    ( X99 != X101
    | k2_tarski(X99,X100) = k2_tarski(X101,X99)
    | ~ r2_hidden(X99,k2_tarski(X101,X99))
    | sK2(X99,X100,k2_tarski(X101,X99)) = X100 )).

cnf(u2387,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X2,X0)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u2386,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X2,X0)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u2232,axiom,
    ( X92 != X93
    | k2_tarski(X92,X93) = k2_tarski(X92,X94)
    | ~ r2_hidden(X92,k2_tarski(X92,X94))
    | sK2(X92,X93,k2_tarski(X92,X94)) = X94 )).

cnf(u2217,axiom,
    ( X92 != X94
    | k2_tarski(X92,X93) = k2_tarski(X92,X94)
    | ~ r2_hidden(X92,k2_tarski(X92,X94))
    | sK2(X92,X93,k2_tarski(X92,X94)) = X93 )).

cnf(u2215,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X0,X2)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u2214,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X0,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u2086,axiom,
    ( X91 != X92
    | k2_tarski(X93,X92) = k2_tarski(X91,X92)
    | ~ r2_hidden(X92,k2_tarski(X93,X92))
    | sK2(X91,X92,k2_tarski(X93,X92)) = X93 )).

cnf(u2072,axiom,
    ( X92 != X93
    | k2_tarski(X93,X92) = k2_tarski(X91,X92)
    | ~ r2_hidden(X92,k2_tarski(X93,X92))
    | sK2(X91,X92,k2_tarski(X93,X92)) = X91 )).

cnf(u2071,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X2,X1)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u2070,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X2,X1)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u1909,axiom,
    ( X90 != X91
    | k2_tarski(X90,X91) = k2_tarski(X91,X92)
    | ~ r2_hidden(X91,k2_tarski(X91,X92))
    | sK2(X90,X91,k2_tarski(X91,X92)) = X92 )).

cnf(u1895,axiom,
    ( X91 != X92
    | k2_tarski(X90,X91) = k2_tarski(X91,X92)
    | ~ r2_hidden(X91,k2_tarski(X91,X92))
    | sK2(X90,X91,k2_tarski(X91,X92)) = X90 )).

cnf(u1894,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X1,X2)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u1893,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u1756,axiom,
    ( X62 != X63
    | k2_tarski(X62,X62) = k2_tarski(X62,X63)
    | ~ r2_hidden(X62,k2_tarski(X62,X62)) )).

cnf(u1700,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X0,X0)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X0,X0) )).

cnf(u1699,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X0,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X0,X0) )).

cnf(u1545,axiom,
    ( X3 != X4
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X0
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X3
    | k2_tarski(X3,X4) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X4)))
    | sK2(X1,X2,k2_tarski(X3,X4)) = X2
    | sK2(X1,X2,k2_tarski(X3,X4)) = X1
    | k2_tarski(X1,X2) = k2_tarski(X3,X4) )).

cnf(u1544,axiom,
    ( X0 != X4
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X0
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X3
    | k2_tarski(X3,X4) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X4)))
    | sK2(X1,X2,k2_tarski(X3,X4)) = X2
    | sK2(X1,X2,k2_tarski(X3,X4)) = X1
    | k2_tarski(X1,X2) = k2_tarski(X3,X4) )).

cnf(u1543,axiom,
    ( X3 != X4
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X0
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X4
    | k2_tarski(X3,X4) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X4)))
    | sK2(X1,X2,k2_tarski(X3,X4)) = X2
    | sK2(X1,X2,k2_tarski(X3,X4)) = X1
    | k2_tarski(X1,X2) = k2_tarski(X3,X4) )).

cnf(u1542,axiom,
    ( X0 != X3
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X0
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X4
    | k2_tarski(X3,X4) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X4)))
    | sK2(X1,X2,k2_tarski(X3,X4)) = X2
    | sK2(X1,X2,k2_tarski(X3,X4)) = X1
    | k2_tarski(X1,X2) = k2_tarski(X3,X4) )).

cnf(u1541,axiom,
    ( X0 != X4
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X3
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X4
    | k2_tarski(X3,X4) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X4)))
    | sK2(X1,X2,k2_tarski(X3,X4)) = X2
    | sK2(X1,X2,k2_tarski(X3,X4)) = X1
    | k2_tarski(X1,X2) = k2_tarski(X3,X4) )).

cnf(u1540,axiom,
    ( X0 != X3
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X3
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X4
    | k2_tarski(X3,X4) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X4)))
    | sK2(X1,X2,k2_tarski(X3,X4)) = X2
    | sK2(X1,X2,k2_tarski(X3,X4)) = X1
    | k2_tarski(X1,X2) = k2_tarski(X3,X4) )).

cnf(u1219,axiom,
    ( X2 != X3
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X4
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X2
    | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),X4)
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u1218,axiom,
    ( X3 != X4
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X4
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X2
    | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),X4)
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u1217,axiom,
    ( X2 != X3
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X4
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X3
    | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),X4)
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u1216,axiom,
    ( X2 != X4
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X4
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X3
    | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),X4)
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u1215,axiom,
    ( X3 != X4
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X2
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X3
    | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),X4)
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u1214,axiom,
    ( X2 != X4
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X2
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X3
    | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),X4)
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u979,axiom,
    ( X43 != X44
    | k2_tarski(X44,X44) = k2_tarski(X43,X44)
    | ~ r2_hidden(X44,k2_tarski(X44,X44)) )).

cnf(u941,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X1,X1)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X1,X1) )).

cnf(u940,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X1,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X1,X1) )).

cnf(u788,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X2,X2)) = X1
    | sK2(X0,X1,k2_tarski(X2,X2)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u787,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X2,X2)) = X1
    | sK2(X0,X1,k2_tarski(X2,X2)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u786,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X2,X2)) = X1
    | sK2(X0,X1,k2_tarski(X2,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u785,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X2,X2)) = X1
    | sK2(X0,X1,k2_tarski(X2,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u784,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X2,X2)) = X0
    | sK2(X0,X1,k2_tarski(X2,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u783,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X2,X2)) = X0
    | sK2(X0,X1,k2_tarski(X2,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u697,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X1,X0)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

cnf(u696,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X1,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

cnf(u655,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X2,X0)) = X1
    | sK2(X0,X1,k2_tarski(X2,X0)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u654,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X2,X0)) = X1
    | sK2(X0,X1,k2_tarski(X2,X0)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u653,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X2,X0)) = X1
    | sK2(X0,X1,k2_tarski(X2,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u652,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X2,X0)) = X1
    | sK2(X0,X1,k2_tarski(X2,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u651,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X2,X0)) = X2
    | sK2(X0,X1,k2_tarski(X2,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u650,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X2,X0)) = X2
    | sK2(X0,X1,k2_tarski(X2,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u564,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X0,X2)) = X1
    | sK2(X0,X1,k2_tarski(X0,X2)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u563,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X0,X2)) = X1
    | sK2(X0,X1,k2_tarski(X0,X2)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u562,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X0,X2)) = X1
    | sK2(X0,X1,k2_tarski(X0,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u561,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X0,X2)) = X1
    | sK2(X0,X1,k2_tarski(X0,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u560,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X0,X2)) = X0
    | sK2(X0,X1,k2_tarski(X0,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u559,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X0,X2)) = X0
    | sK2(X0,X1,k2_tarski(X0,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u482,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X2,X1)) = X0
    | sK2(X0,X1,k2_tarski(X2,X1)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u481,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X2,X1)) = X0
    | sK2(X0,X1,k2_tarski(X2,X1)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u480,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X2,X1)) = X0
    | sK2(X0,X1,k2_tarski(X2,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u479,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X2,X1)) = X0
    | sK2(X0,X1,k2_tarski(X2,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u478,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X2,X1)) = X2
    | sK2(X0,X1,k2_tarski(X2,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u477,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X2,X1)) = X2
    | sK2(X0,X1,k2_tarski(X2,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u405,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X1,X2)) = X0
    | sK2(X0,X1,k2_tarski(X1,X2)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u404,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X1,X2)) = X0
    | sK2(X0,X1,k2_tarski(X1,X2)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u403,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X1,X2)) = X0
    | sK2(X0,X1,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u402,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X1,X2)) = X0
    | sK2(X0,X1,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u401,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X1,X2)) = X1
    | sK2(X0,X1,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u400,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X1,X2)) = X1
    | sK2(X0,X1,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u341,axiom,
    ( X0 != X1
    | sK2(X0,X0,k2_tarski(X1,X1)) = X0
    | k2_tarski(X0,X0) = k2_tarski(X1,X1) )).

cnf(u340,axiom,
    ( X0 != X1
    | sK2(X0,X0,k2_tarski(X1,X1)) = X1
    | k2_tarski(X0,X0) = k2_tarski(X1,X1) )).

cnf(u306,axiom,
    ( X12 != X13
    | k2_tarski(X12,X12) = k2_tarski(X13,X12)
    | ~ r2_hidden(X12,k2_tarski(X13,X12)) )).

cnf(u273,axiom,
    ( X0 != X1
    | sK2(X0,X0,k2_tarski(X1,X0)) = X1
    | k2_tarski(X0,X0) = k2_tarski(X1,X0) )).

cnf(u272,axiom,
    ( X0 != X1
    | sK2(X0,X0,k2_tarski(X1,X0)) = X0
    | k2_tarski(X0,X0) = k2_tarski(X1,X0) )).

cnf(u239,axiom,
    ( X12 != X13
    | k2_tarski(X12,X12) = k2_tarski(X12,X13)
    | ~ r2_hidden(X12,k2_tarski(X12,X13)) )).

cnf(u209,axiom,
    ( X0 != X1
    | sK2(X0,X0,k2_tarski(X0,X1)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X0,X0) )).

cnf(u208,axiom,
    ( X0 != X1
    | sK2(X0,X0,k2_tarski(X0,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X0,X0) )).

cnf(u173,axiom,
    ( X1 != X2
    | sK2(X0,X0,k2_tarski(X1,X2)) = X0
    | sK2(X0,X0,k2_tarski(X1,X2)) = X1
    | k2_tarski(X0,X0) = k2_tarski(X1,X2) )).

cnf(u172,axiom,
    ( X0 != X2
    | sK2(X0,X0,k2_tarski(X1,X2)) = X0
    | sK2(X0,X0,k2_tarski(X1,X2)) = X1
    | k2_tarski(X0,X0) = k2_tarski(X1,X2) )).

cnf(u171,axiom,
    ( X1 != X2
    | sK2(X0,X0,k2_tarski(X1,X2)) = X0
    | sK2(X0,X0,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X0) = k2_tarski(X1,X2) )).

cnf(u170,axiom,
    ( X0 != X1
    | sK2(X0,X0,k2_tarski(X1,X2)) = X0
    | sK2(X0,X0,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X0) = k2_tarski(X1,X2) )).

cnf(u169,axiom,
    ( X0 != X2
    | sK2(X0,X0,k2_tarski(X1,X2)) = X1
    | sK2(X0,X0,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X0) = k2_tarski(X1,X2) )).

cnf(u168,axiom,
    ( X0 != X1
    | sK2(X0,X0,k2_tarski(X1,X2)) = X1
    | sK2(X0,X0,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X0) = k2_tarski(X1,X2) )).

cnf(u122,axiom,
    ( X2 != X3
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | sK2(X0,X1,k2_tarski(X2,X3)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u121,axiom,
    ( X0 != X3
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | sK2(X0,X1,k2_tarski(X2,X3)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u120,axiom,
    ( X1 != X3
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | sK2(X0,X1,k2_tarski(X2,X3)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u119,axiom,
    ( X2 != X3
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | sK2(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u118,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | sK2(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u117,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | sK2(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u116,axiom,
    ( X0 != X3
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X2
    | sK2(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u115,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X2
    | sK2(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u114,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X2
    | sK2(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u113,axiom,
    ( X1 != X3
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | sK2(X0,X1,k2_tarski(X2,X3)) = X2
    | sK2(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u112,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | sK2(X0,X1,k2_tarski(X2,X3)) = X2
    | sK2(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u111,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | sK2(X0,X1,k2_tarski(X2,X3)) = X2
    | sK2(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u81,negated_conjecture,
    ( sK1 != k2_yellow_0(sK0,k2_tarski(sK1,sK1))
    | sK1 != k1_yellow_0(sK0,k2_tarski(sK1,sK1)) )).

cnf(u3598,axiom,
    ( sK2(X153,X154,k2_tarski(X155,X155)) != X156
    | k2_tarski(X155,X155) = k2_tarski(sK2(X153,X154,k2_tarski(X155,X155)),X156)
    | ~ r2_hidden(sK2(X153,X154,k2_tarski(X155,X155)),k2_tarski(X155,X155))
    | sK2(sK2(X153,X154,k2_tarski(X155,X155)),X156,k2_tarski(X155,X155)) = X155
    | sK2(X153,X154,k2_tarski(X155,X155)) = X154
    | sK2(X153,X154,k2_tarski(X155,X155)) = X153
    | k2_tarski(X155,X155) = k2_tarski(X153,X154) )).

cnf(u3877,axiom,
    ( sK2(X168,X169,k2_tarski(X170,X170)) != X167
    | k2_tarski(X170,X170) = k2_tarski(X167,sK2(X168,X169,k2_tarski(X170,X170)))
    | ~ r2_hidden(sK2(X168,X169,k2_tarski(X170,X170)),k2_tarski(X170,X170))
    | sK2(X167,sK2(X168,X169,k2_tarski(X170,X170)),k2_tarski(X170,X170)) = X170
    | sK2(X168,X169,k2_tarski(X170,X170)) = X169
    | sK2(X168,X169,k2_tarski(X170,X170)) = X168
    | k2_tarski(X170,X170) = k2_tarski(X168,X169) )).

cnf(u1228,axiom,
    ( sK2(X70,X71,k2_tarski(X72,X73)) != X74
    | k2_tarski(X72,X73) = k2_tarski(sK2(X70,X71,k2_tarski(X72,X73)),X74)
    | ~ r2_hidden(sK2(X70,X71,k2_tarski(X72,X73)),k2_tarski(X72,X73))
    | sK2(sK2(X70,X71,k2_tarski(X72,X73)),X74,k2_tarski(X72,X73)) = X72
    | sK2(sK2(X70,X71,k2_tarski(X72,X73)),X74,k2_tarski(X72,X73)) = X73
    | sK2(X70,X71,k2_tarski(X72,X73)) = X71
    | sK2(X70,X71,k2_tarski(X72,X73)) = X70
    | k2_tarski(X70,X71) = k2_tarski(X72,X73) )).

cnf(u1561,axiom,
    ( sK2(X85,X86,k2_tarski(X87,X88)) != X84
    | k2_tarski(X87,X88) = k2_tarski(X84,sK2(X85,X86,k2_tarski(X87,X88)))
    | ~ r2_hidden(sK2(X85,X86,k2_tarski(X87,X88)),k2_tarski(X87,X88))
    | sK2(X84,sK2(X85,X86,k2_tarski(X87,X88)),k2_tarski(X87,X88)) = X87
    | sK2(X84,sK2(X85,X86,k2_tarski(X87,X88)),k2_tarski(X87,X88)) = X88
    | sK2(X85,X86,k2_tarski(X87,X88)) = X86
    | sK2(X85,X86,k2_tarski(X87,X88)) = X85
    | k2_tarski(X87,X88) = k2_tarski(X85,X86) )).

cnf(u72,axiom,
    ( sK2(X0,X1,X2) != X0
    | k2_tarski(X0,X1) = X2
    | ~ r2_hidden(X0,X2) )).

cnf(u71,axiom,
    ( sK2(X0,X1,X2) != X1
    | k2_tarski(X0,X1) = X2
    | ~ r2_hidden(X1,X2) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:20:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (4463)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (4479)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.16/0.52  % (4471)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.16/0.53  % (4465)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.16/0.53  % (4471)Refutation not found, incomplete strategy% (4471)------------------------------
% 1.16/0.53  % (4471)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.16/0.53  % (4473)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.16/0.53  % (4479)Refutation not found, incomplete strategy% (4479)------------------------------
% 1.16/0.53  % (4479)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.16/0.53  % (4471)Termination reason: Refutation not found, incomplete strategy
% 1.16/0.53  
% 1.16/0.53  % (4471)Memory used [KB]: 10746
% 1.16/0.53  % (4471)Time elapsed: 0.110 s
% 1.16/0.53  % (4471)------------------------------
% 1.16/0.53  % (4471)------------------------------
% 1.16/0.53  % (4483)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.16/0.53  % (4473)Refutation not found, incomplete strategy% (4473)------------------------------
% 1.16/0.53  % (4473)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.16/0.53  % (4473)Termination reason: Refutation not found, incomplete strategy
% 1.16/0.53  
% 1.16/0.53  % (4473)Memory used [KB]: 10618
% 1.16/0.53  % (4473)Time elapsed: 0.107 s
% 1.16/0.53  % (4473)------------------------------
% 1.16/0.53  % (4473)------------------------------
% 1.16/0.53  % (4479)Termination reason: Refutation not found, incomplete strategy
% 1.16/0.53  
% 1.16/0.53  % (4479)Memory used [KB]: 1663
% 1.16/0.53  % (4479)Time elapsed: 0.106 s
% 1.16/0.53  % (4479)------------------------------
% 1.16/0.53  % (4479)------------------------------
% 1.16/0.53  % (4467)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.16/0.53  % (4475)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.30/0.54  % (4461)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.30/0.54  % (4468)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.30/0.54  % (4466)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.30/0.54  % (4489)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.30/0.54  % (4464)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.30/0.54  % (4484)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.30/0.54  % (4487)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.30/0.55  % (4487)Refutation not found, incomplete strategy% (4487)------------------------------
% 1.30/0.55  % (4487)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.55  % (4487)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.55  
% 1.30/0.55  % (4487)Memory used [KB]: 6268
% 1.30/0.55  % (4487)Time elapsed: 0.130 s
% 1.30/0.55  % (4487)------------------------------
% 1.30/0.55  % (4487)------------------------------
% 1.30/0.55  % (4481)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.30/0.55  % (4485)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.30/0.55  % (4465)Refutation not found, incomplete strategy% (4465)------------------------------
% 1.30/0.55  % (4465)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.55  % (4465)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.55  
% 1.30/0.55  % (4465)Memory used [KB]: 1791
% 1.30/0.55  % (4465)Time elapsed: 0.110 s
% 1.30/0.55  % (4465)------------------------------
% 1.30/0.55  % (4465)------------------------------
% 1.30/0.55  % (4476)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.30/0.55  % (4485)Refutation not found, incomplete strategy% (4485)------------------------------
% 1.30/0.55  % (4485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.55  % (4485)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.55  
% 1.30/0.55  % (4485)Memory used [KB]: 10746
% 1.30/0.55  % (4485)Time elapsed: 0.128 s
% 1.30/0.55  % (4485)------------------------------
% 1.30/0.55  % (4485)------------------------------
% 1.30/0.55  % (4488)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.30/0.55  % (4490)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.30/0.55  % (4477)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.30/0.55  % (4482)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.30/0.56  % (4489)Refutation not found, incomplete strategy% (4489)------------------------------
% 1.30/0.56  % (4489)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.56  % (4489)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.56  
% 1.30/0.56  % (4489)Memory used [KB]: 10746
% 1.30/0.56  % (4489)Time elapsed: 0.143 s
% 1.30/0.56  % (4489)------------------------------
% 1.30/0.56  % (4489)------------------------------
% 1.30/0.56  % (4480)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.30/0.56  % (4478)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.30/0.56  % (4474)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.30/0.56  % (4462)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.30/0.56  % (4469)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.30/0.56  % (4462)Refutation not found, incomplete strategy% (4462)------------------------------
% 1.30/0.56  % (4462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.56  % (4462)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.56  
% 1.30/0.56  % (4462)Memory used [KB]: 1663
% 1.30/0.56  % (4462)Time elapsed: 0.134 s
% 1.30/0.56  % (4462)------------------------------
% 1.30/0.56  % (4462)------------------------------
% 1.30/0.56  % (4472)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.30/0.56  % (4490)Refutation not found, incomplete strategy% (4490)------------------------------
% 1.30/0.56  % (4490)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.56  % (4477)Refutation not found, incomplete strategy% (4477)------------------------------
% 1.30/0.56  % (4477)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.56  % (4477)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.56  
% 1.30/0.56  % (4477)Memory used [KB]: 10618
% 1.30/0.56  % (4477)Time elapsed: 0.150 s
% 1.30/0.56  % (4477)------------------------------
% 1.30/0.56  % (4477)------------------------------
% 1.30/0.56  % (4490)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.56  
% 1.30/0.56  % (4490)Memory used [KB]: 1663
% 1.30/0.56  % (4490)Time elapsed: 0.144 s
% 1.30/0.56  % (4490)------------------------------
% 1.30/0.56  % (4490)------------------------------
% 1.30/0.57  % (4470)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.30/0.57  % (4486)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.30/0.57  % (4486)Refutation not found, incomplete strategy% (4486)------------------------------
% 1.30/0.57  % (4486)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.57  % (4488)Refutation not found, incomplete strategy% (4488)------------------------------
% 1.30/0.57  % (4488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.57  % (4488)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.57  
% 1.30/0.57  % (4488)Memory used [KB]: 6140
% 1.30/0.57  % (4488)Time elapsed: 0.147 s
% 1.30/0.57  % (4488)------------------------------
% 1.30/0.57  % (4488)------------------------------
% 1.30/0.58  % (4478)Refutation not found, incomplete strategy% (4478)------------------------------
% 1.30/0.58  % (4478)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.58  % (4478)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.58  
% 1.30/0.58  % (4478)Memory used [KB]: 1663
% 1.30/0.58  % (4478)Time elapsed: 0.140 s
% 1.30/0.58  % (4478)------------------------------
% 1.30/0.58  % (4478)------------------------------
% 1.30/0.58  % (4486)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.58  
% 1.30/0.58  % (4486)Memory used [KB]: 6268
% 1.30/0.58  % (4486)Time elapsed: 0.149 s
% 1.30/0.58  % (4486)------------------------------
% 1.30/0.58  % (4486)------------------------------
% 1.30/0.62  % (4463)Refutation not found, incomplete strategy% (4463)------------------------------
% 1.30/0.62  % (4463)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.63  % (4498)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 1.87/0.63  % (4499)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 1.87/0.63  % (4463)Termination reason: Refutation not found, incomplete strategy
% 1.87/0.63  
% 1.87/0.63  % (4463)Memory used [KB]: 6268
% 1.87/0.63  % (4463)Time elapsed: 0.198 s
% 1.87/0.63  % (4463)------------------------------
% 1.87/0.63  % (4463)------------------------------
% 1.87/0.67  % (4508)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 1.87/0.67  % (4508)Refutation not found, incomplete strategy% (4508)------------------------------
% 1.87/0.67  % (4508)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.67  % (4464)Refutation not found, incomplete strategy% (4464)------------------------------
% 1.87/0.67  % (4464)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.67  % (4464)Termination reason: Refutation not found, incomplete strategy
% 1.87/0.67  
% 1.87/0.67  % (4464)Memory used [KB]: 6140
% 1.87/0.67  % (4464)Time elapsed: 0.240 s
% 1.87/0.67  % (4464)------------------------------
% 1.87/0.67  % (4464)------------------------------
% 1.87/0.68  % (4516)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 1.87/0.68  % (4512)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 1.87/0.68  % (4512)Refutation not found, incomplete strategy% (4512)------------------------------
% 1.87/0.68  % (4512)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.68  % (4512)Termination reason: Refutation not found, incomplete strategy
% 1.87/0.68  
% 1.87/0.68  % (4512)Memory used [KB]: 10746
% 1.87/0.68  % (4512)Time elapsed: 0.107 s
% 1.87/0.68  % (4512)------------------------------
% 1.87/0.68  % (4512)------------------------------
% 1.87/0.68  % (4514)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.16/0.69  % (4518)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.16/0.69  % (4508)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.69  
% 2.16/0.69  % (4508)Memory used [KB]: 6140
% 2.16/0.69  % (4508)Time elapsed: 0.100 s
% 2.16/0.69  % (4508)------------------------------
% 2.16/0.69  % (4508)------------------------------
% 2.16/0.69  % (4522)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.16/0.69  % (4535)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 2.16/0.69  % (4518)Refutation not found, incomplete strategy% (4518)------------------------------
% 2.16/0.69  % (4518)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.69  % (4533)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 2.16/0.70  % (4523)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.16/0.70  % (4518)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.70  
% 2.16/0.70  % (4518)Memory used [KB]: 10746
% 2.16/0.70  % (4518)Time elapsed: 0.115 s
% 2.16/0.70  % (4518)------------------------------
% 2.16/0.70  % (4518)------------------------------
% 2.16/0.70  % (4469)Refutation not found, incomplete strategy% (4469)------------------------------
% 2.16/0.70  % (4469)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.71  % (4514)Refutation not found, incomplete strategy% (4514)------------------------------
% 2.16/0.71  % (4514)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.71  % (4514)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.71  
% 2.16/0.71  % (4514)Memory used [KB]: 10746
% 2.16/0.71  % (4514)Time elapsed: 0.125 s
% 2.16/0.71  % (4514)------------------------------
% 2.16/0.71  % (4514)------------------------------
% 2.16/0.71  % (4524)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 2.16/0.71  % (4524)Refutation not found, incomplete strategy% (4524)------------------------------
% 2.16/0.71  % (4524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.71  % (4524)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.71  
% 2.16/0.71  % (4524)Memory used [KB]: 10746
% 2.16/0.71  % (4524)Time elapsed: 0.115 s
% 2.16/0.71  % (4524)------------------------------
% 2.16/0.71  % (4524)------------------------------
% 2.16/0.72  % (4528)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 2.16/0.72  % (4469)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.72  
% 2.16/0.72  % (4469)Memory used [KB]: 6268
% 2.16/0.72  % (4469)Time elapsed: 0.277 s
% 2.16/0.72  % (4469)------------------------------
% 2.16/0.72  % (4469)------------------------------
% 2.16/0.74  % (4560)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 2.61/0.79  % (4583)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 2.74/0.82  % (4586)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 2.74/0.82  % (4593)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 2.74/0.83  % (4602)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 2.86/0.85  % (4609)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 2.86/0.85  % (4621)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 2.86/0.85  % (4614)dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 2.86/0.88  % (4523)Refutation not found, incomplete strategy% (4523)------------------------------
% 2.86/0.88  % (4523)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.86/0.88  % (4523)Termination reason: Refutation not found, incomplete strategy
% 2.86/0.88  
% 2.86/0.88  % (4523)Memory used [KB]: 6268
% 2.86/0.88  % (4523)Time elapsed: 0.275 s
% 2.86/0.88  % (4523)------------------------------
% 2.86/0.88  % (4523)------------------------------
% 2.86/0.92  % (4583)Refutation not found, incomplete strategy% (4583)------------------------------
% 2.86/0.92  % (4583)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.29/0.94  % (4583)Termination reason: Refutation not found, incomplete strategy
% 3.29/0.94  
% 3.29/0.94  % (4583)Memory used [KB]: 6268
% 3.29/0.94  % (4583)Time elapsed: 0.211 s
% 3.29/0.94  % (4583)------------------------------
% 3.29/0.94  % (4583)------------------------------
% 3.29/0.97  % (4586)Refutation not found, incomplete strategy% (4586)------------------------------
% 3.29/0.97  % (4586)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.29/0.98  % (4586)Termination reason: Refutation not found, incomplete strategy
% 3.29/0.98  
% 3.29/0.98  % (4586)Memory used [KB]: 6268
% 3.29/0.98  % (4586)Time elapsed: 0.266 s
% 3.29/0.98  % (4586)------------------------------
% 3.29/0.98  % (4586)------------------------------
% 3.69/0.99  % (4475)Time limit reached!
% 3.69/0.99  % (4475)------------------------------
% 3.69/0.99  % (4475)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.69/0.99  % (4475)Termination reason: Time limit
% 3.69/0.99  
% 3.69/0.99  % (4475)Memory used [KB]: 5884
% 3.69/0.99  % (4475)Time elapsed: 0.508 s
% 3.69/0.99  % (4475)------------------------------
% 3.69/0.99  % (4475)------------------------------
% 3.69/1.00  % (4609)Refutation not found, incomplete strategy% (4609)------------------------------
% 3.69/1.00  % (4609)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.69/1.00  % (4609)Termination reason: Refutation not found, incomplete strategy
% 3.69/1.00  
% 3.69/1.00  % (4609)Memory used [KB]: 6268
% 3.69/1.00  % (4609)Time elapsed: 0.261 s
% 3.69/1.00  % (4609)------------------------------
% 3.69/1.00  % (4609)------------------------------
% 3.69/1.01  % (4467)Time limit reached!
% 3.69/1.01  % (4467)------------------------------
% 3.69/1.01  % (4467)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.69/1.02  % (4467)Termination reason: Time limit
% 3.69/1.02  
% 3.69/1.02  % (4467)Memory used [KB]: 12920
% 3.69/1.02  % (4467)Time elapsed: 0.539 s
% 3.69/1.02  % (4467)------------------------------
% 3.69/1.02  % (4467)------------------------------
% 3.69/1.03  % (4468)Time limit reached!
% 3.69/1.03  % (4468)------------------------------
% 3.69/1.03  % (4468)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.69/1.03  % (4468)Termination reason: Time limit
% 3.69/1.03  
% 3.69/1.03  % (4468)Memory used [KB]: 3198
% 3.69/1.03  % (4468)Time elapsed: 0.614 s
% 3.69/1.03  % (4468)------------------------------
% 3.69/1.03  % (4468)------------------------------
% 5.57/1.10  % (4560)Time limit reached!
% 5.57/1.10  % (4560)------------------------------
% 5.57/1.10  % (4560)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.57/1.10  % (4560)Termination reason: Time limit
% 5.57/1.10  
% 5.57/1.10  % (4560)Memory used [KB]: 14072
% 5.57/1.10  % (4560)Time elapsed: 0.425 s
% 5.57/1.10  % (4560)------------------------------
% 5.57/1.10  % (4560)------------------------------
% 5.93/1.14  % (4602)Time limit reached!
% 5.93/1.14  % (4602)------------------------------
% 5.93/1.14  % (4602)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.93/1.14  % (4602)Termination reason: Time limit
% 5.93/1.14  
% 5.93/1.14  % (4602)Memory used [KB]: 6908
% 5.93/1.14  % (4602)Time elapsed: 0.415 s
% 5.93/1.14  % (4602)------------------------------
% 5.93/1.14  % (4602)------------------------------
% 6.20/1.16  % (4614)Time limit reached!
% 6.20/1.16  % (4614)------------------------------
% 6.20/1.16  % (4614)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.20/1.16  % (4614)Termination reason: Time limit
% 6.20/1.16  % (4614)Termination phase: Saturation
% 6.20/1.16  
% 6.20/1.16  % (4614)Memory used [KB]: 4733
% 6.20/1.16  % (4614)Time elapsed: 0.400 s
% 6.20/1.16  % (4614)------------------------------
% 6.20/1.16  % (4614)------------------------------
% 6.20/1.16  % (4621)Time limit reached!
% 6.20/1.16  % (4621)------------------------------
% 6.20/1.16  % (4621)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.20/1.16  % (4621)Termination reason: Time limit
% 6.20/1.16  
% 6.20/1.16  % (4621)Memory used [KB]: 7931
% 6.20/1.16  % (4621)Time elapsed: 0.425 s
% 6.20/1.16  % (4621)------------------------------
% 6.20/1.16  % (4621)------------------------------
% 6.88/1.23  % (4593)Time limit reached!
% 6.88/1.23  % (4593)------------------------------
% 6.88/1.23  % (4593)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.88/1.23  % (4593)Termination reason: Time limit
% 6.88/1.23  % (4593)Termination phase: Saturation
% 6.88/1.23  
% 6.88/1.23  % (4593)Memory used [KB]: 10746
% 6.88/1.23  % (4593)Time elapsed: 0.500 s
% 6.88/1.23  % (4593)------------------------------
% 6.88/1.23  % (4593)------------------------------
% 8.60/1.47  % SZS status CounterSatisfiable for theBenchmark
% 8.60/1.49  % (4466)# SZS output start Saturation.
% 8.60/1.49  cnf(u42,negated_conjecture,
% 8.60/1.49      v5_orders_2(sK0)).
% 8.60/1.49  
% 8.60/1.49  cnf(u3355,axiom,
% 8.60/1.49      r2_lattice3(X12,k2_tarski(X11,X11),X13) | sK2(sK4(X12,k2_tarski(X11,X11),X13),sK2(X14,X15,k2_tarski(X11,X11)),k2_tarski(X11,X11)) = X11 | sK2(X14,X15,k2_tarski(X11,X11)) = X15 | sK2(X14,X15,k2_tarski(X11,X11)) = X14 | k2_tarski(X14,X15) = k2_tarski(X11,X11) | k2_tarski(X11,X11) = k2_tarski(sK4(X12,k2_tarski(X11,X11),X13),sK2(X14,X15,k2_tarski(X11,X11))) | ~m1_subset_1(X13,u1_struct_0(X12)) | ~l1_orders_2(X12)).
% 8.60/1.49  
% 8.60/1.49  cnf(u2618,axiom,
% 8.60/1.49      r2_lattice3(X16,k2_tarski(X15,X15),X17) | sK2(sK2(X13,X14,k2_tarski(X15,X15)),sK4(X16,k2_tarski(X15,X15),X17),k2_tarski(X15,X15)) = X15 | k2_tarski(X15,X15) = k2_tarski(sK2(X13,X14,k2_tarski(X15,X15)),sK4(X16,k2_tarski(X15,X15),X17)) | ~m1_subset_1(X17,u1_struct_0(X16)) | ~l1_orders_2(X16) | sK2(X13,X14,k2_tarski(X15,X15)) = X14 | sK2(X13,X14,k2_tarski(X15,X15)) = X13 | k2_tarski(X13,X14) = k2_tarski(X15,X15)).
% 8.60/1.49  
% 8.60/1.49  cnf(u2610,axiom,
% 8.60/1.49      r2_lattice3(X16,k2_tarski(X15,X15),X17) | sK2(sK4(X16,k2_tarski(X15,X15),X17),sK2(X13,X14,k2_tarski(X15,X15)),k2_tarski(X15,X15)) = X15 | k2_tarski(X15,X15) = k2_tarski(sK2(X13,X14,k2_tarski(X15,X15)),sK4(X16,k2_tarski(X15,X15),X17)) | ~m1_subset_1(X17,u1_struct_0(X16)) | ~l1_orders_2(X16) | sK2(X13,X14,k2_tarski(X15,X15)) = X14 | sK2(X13,X14,k2_tarski(X15,X15)) = X13 | k2_tarski(X13,X14) = k2_tarski(X15,X15)).
% 8.60/1.49  
% 8.60/1.49  cnf(u2445,axiom,
% 8.60/1.49      r2_lattice3(X18,k2_tarski(X17,X17),X19) | ~m1_subset_1(X19,u1_struct_0(X18)) | ~l1_orders_2(X18) | sK2(X15,X16,k2_tarski(X17,X17)) = sK4(X18,k2_tarski(X17,X17),X19) | sK4(X18,k2_tarski(X17,X17),X19) = X17 | sK2(X15,X16,k2_tarski(X17,X17)) = X16 | sK2(X15,X16,k2_tarski(X17,X17)) = X15 | k2_tarski(X17,X17) = k2_tarski(X15,X16)).
% 8.60/1.49  
% 8.60/1.49  cnf(u2259,axiom,
% 8.60/1.49      r2_lattice3(X9,k2_tarski(X10,X10),X11) | sK2(X8,sK4(X9,k2_tarski(X10,X10),X11),k2_tarski(X10,X10)) = X8 | sK2(X8,sK4(X9,k2_tarski(X10,X10),X11),k2_tarski(X10,X10)) = X10 | k2_tarski(X10,X10) = k2_tarski(X8,sK4(X9,k2_tarski(X10,X10),X11)) | ~m1_subset_1(X11,u1_struct_0(X9)) | ~l1_orders_2(X9)).
% 8.60/1.49  
% 8.60/1.49  cnf(u2247,axiom,
% 8.60/1.49      r2_lattice3(X9,k2_tarski(X8,X8),X10) | sK2(sK4(X9,k2_tarski(X8,X8),X10),X11,k2_tarski(X8,X8)) = X11 | sK2(sK4(X9,k2_tarski(X8,X8),X10),X11,k2_tarski(X8,X8)) = X8 | k2_tarski(X8,X8) = k2_tarski(sK4(X9,k2_tarski(X8,X8),X10),X11) | ~m1_subset_1(X10,u1_struct_0(X9)) | ~l1_orders_2(X9)).
% 8.60/1.49  
% 8.60/1.49  cnf(u991,axiom,
% 8.60/1.49      r2_lattice3(X6,k2_tarski(X5,X5),X7) | k2_tarski(X5,X5) = k2_tarski(X5,sK4(X6,k2_tarski(X5,X5),X7)) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~l1_orders_2(X6)).
% 8.60/1.49  
% 8.60/1.49  cnf(u418,axiom,
% 8.60/1.49      r2_lattice3(X5,k2_tarski(X6,X6),X7) | sK2(sK4(X5,k2_tarski(X6,X6),X7),sK4(X5,k2_tarski(X6,X6),X7),k2_tarski(X6,X6)) = X6 | k2_tarski(X6,X6) = k2_tarski(sK4(X5,k2_tarski(X6,X6),X7),sK4(X5,k2_tarski(X6,X6),X7)) | ~m1_subset_1(X7,u1_struct_0(X5)) | ~l1_orders_2(X5)).
% 8.60/1.49  
% 8.60/1.49  cnf(u2780,axiom,
% 8.60/1.49      r2_lattice3(X16,k2_tarski(X14,X15),X17) | sK2(sK4(X16,k2_tarski(X14,X15),X17),sK2(X18,X19,k2_tarski(X14,X15)),k2_tarski(X14,X15)) = X14 | sK2(sK4(X16,k2_tarski(X14,X15),X17),sK2(X18,X19,k2_tarski(X14,X15)),k2_tarski(X14,X15)) = X15 | sK2(X18,X19,k2_tarski(X14,X15)) = X19 | sK2(X18,X19,k2_tarski(X14,X15)) = X18 | k2_tarski(X14,X15) = k2_tarski(X18,X19) | k2_tarski(X14,X15) = k2_tarski(sK4(X16,k2_tarski(X14,X15),X17),sK2(X18,X19,k2_tarski(X14,X15))) | ~m1_subset_1(X17,u1_struct_0(X16)) | ~l1_orders_2(X16)).
% 8.60/1.49  
% 8.60/1.49  cnf(u2659,axiom,
% 8.60/1.49      r2_lattice3(X18,k2_tarski(X14,X15),X19) | sK2(sK2(X16,X17,k2_tarski(X14,X15)),sK4(X18,k2_tarski(X14,X15),X19),k2_tarski(X14,X15)) = X14 | sK2(sK2(X16,X17,k2_tarski(X14,X15)),sK4(X18,k2_tarski(X14,X15),X19),k2_tarski(X14,X15)) = X15 | sK2(X16,X17,k2_tarski(X14,X15)) = X17 | sK2(X16,X17,k2_tarski(X14,X15)) = X16 | k2_tarski(X14,X15) = k2_tarski(X16,X17) | k2_tarski(X14,X15) = k2_tarski(sK2(X16,X17,k2_tarski(X14,X15)),sK4(X18,k2_tarski(X14,X15),X19)) | ~m1_subset_1(X19,u1_struct_0(X18)) | ~l1_orders_2(X18)).
% 8.60/1.49  
% 8.60/1.49  cnf(u2615,axiom,
% 8.60/1.49      r2_lattice3(X2,k2_tarski(X1,X0),X3) | sK2(X0,sK4(X2,k2_tarski(X1,X0),X3),k2_tarski(X1,X0)) = X1 | k2_tarski(X1,X0) = k2_tarski(X0,sK4(X2,k2_tarski(X1,X0),X3)) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_orders_2(X2)).
% 8.60/1.49  
% 8.60/1.49  cnf(u2607,axiom,
% 8.60/1.49      r2_lattice3(X2,k2_tarski(X1,X0),X3) | sK2(sK4(X2,k2_tarski(X1,X0),X3),X0,k2_tarski(X1,X0)) = X1 | k2_tarski(X1,X0) = k2_tarski(X0,sK4(X2,k2_tarski(X1,X0),X3)) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_orders_2(X2)).
% 8.60/1.49  
% 8.60/1.49  cnf(u2252,axiom,
% 8.60/1.49      r2_lattice3(X10,k2_tarski(X8,X9),X11) | sK2(X8,sK4(X10,k2_tarski(X8,X9),X11),k2_tarski(X8,X9)) = X9 | k2_tarski(X8,X9) = k2_tarski(X8,sK4(X10,k2_tarski(X8,X9),X11)) | ~m1_subset_1(X11,u1_struct_0(X10)) | ~l1_orders_2(X10)).
% 8.60/1.49  
% 8.60/1.49  cnf(u1942,axiom,
% 8.60/1.49      r2_lattice3(X8,k2_tarski(X9,X10),X11) | sK2(sK4(X8,k2_tarski(X9,X10),X11),X9,k2_tarski(X9,X10)) = X10 | k2_tarski(X9,X10) = k2_tarski(X9,sK4(X8,k2_tarski(X9,X10),X11)) | ~m1_subset_1(X11,u1_struct_0(X8)) | ~l1_orders_2(X8)).
% 8.60/1.49  
% 8.60/1.49  cnf(u1779,axiom,
% 8.60/1.49      r2_lattice3(X10,k2_tarski(X8,X9),X11) | sK2(sK4(X10,k2_tarski(X8,X9),X11),sK4(X10,k2_tarski(X8,X9),X11),k2_tarski(X8,X9)) = X8 | sK2(sK4(X10,k2_tarski(X8,X9),X11),sK4(X10,k2_tarski(X8,X9),X11),k2_tarski(X8,X9)) = X9 | k2_tarski(X8,X9) = k2_tarski(sK4(X10,k2_tarski(X8,X9),X11),sK4(X10,k2_tarski(X8,X9),X11)) | ~m1_subset_1(X11,u1_struct_0(X10)) | ~l1_orders_2(X10)).
% 8.60/1.49  
% 8.60/1.49  cnf(u313,axiom,
% 8.60/1.49      r2_lattice3(X14,k2_tarski(X11,X12),X15) | sK2(X13,sK4(X14,k2_tarski(X11,X12),X15),k2_tarski(X11,X12)) = X13 | sK2(X13,sK4(X14,k2_tarski(X11,X12),X15),k2_tarski(X11,X12)) = X11 | sK2(X13,sK4(X14,k2_tarski(X11,X12),X15),k2_tarski(X11,X12)) = X12 | k2_tarski(X11,X12) = k2_tarski(X13,sK4(X14,k2_tarski(X11,X12),X15)) | ~m1_subset_1(X15,u1_struct_0(X14)) | ~l1_orders_2(X14)).
% 8.60/1.49  
% 8.60/1.49  cnf(u287,axiom,
% 8.60/1.49      r2_lattice3(X13,k2_tarski(X11,X12),X14) | sK2(sK4(X13,k2_tarski(X11,X12),X14),X15,k2_tarski(X11,X12)) = X15 | sK2(sK4(X13,k2_tarski(X11,X12),X14),X15,k2_tarski(X11,X12)) = X11 | sK2(sK4(X13,k2_tarski(X11,X12),X14),X15,k2_tarski(X11,X12)) = X12 | k2_tarski(X11,X12) = k2_tarski(sK4(X13,k2_tarski(X11,X12),X14),X15) | ~m1_subset_1(X14,u1_struct_0(X13)) | ~l1_orders_2(X13)).
% 8.60/1.49  
% 8.60/1.49  cnf(u83,axiom,
% 8.60/1.49      r2_lattice3(X0,k2_tarski(X1,X2),X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_orders_2(X0) | sK4(X0,k2_tarski(X1,X2),X3) = X1 | sK4(X0,k2_tarski(X1,X2),X3) = X2).
% 8.60/1.49  
% 8.60/1.49  cnf(u64,axiom,
% 8.60/1.49      r2_lattice3(X0,X1,X2) | ~r1_orders_2(X0,sK4(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 8.60/1.49  
% 8.60/1.49  cnf(u85,negated_conjecture,
% 8.60/1.49      r2_lattice3(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | k2_tarski(sK4(sK0,X0,X1),sK4(sK0,X0,X1)) = k6_domain_1(u1_struct_0(sK0),sK4(sK0,X0,X1)) | ~l1_struct_0(sK0)).
% 8.60/1.49  
% 8.60/1.49  cnf(u3354,axiom,
% 8.60/1.49      r1_lattice3(X7,k2_tarski(X6,X6),X8) | sK2(sK3(X7,k2_tarski(X6,X6),X8),sK2(X9,X10,k2_tarski(X6,X6)),k2_tarski(X6,X6)) = X6 | sK2(X9,X10,k2_tarski(X6,X6)) = X10 | sK2(X9,X10,k2_tarski(X6,X6)) = X9 | k2_tarski(X6,X6) = k2_tarski(X9,X10) | k2_tarski(X6,X6) = k2_tarski(sK3(X7,k2_tarski(X6,X6),X8),sK2(X9,X10,k2_tarski(X6,X6))) | ~m1_subset_1(X8,u1_struct_0(X7)) | ~l1_orders_2(X7)).
% 8.60/1.49  
% 8.60/1.49  cnf(u2614,axiom,
% 8.60/1.49      r1_lattice3(X16,k2_tarski(X15,X15),X17) | sK2(sK2(X13,X14,k2_tarski(X15,X15)),sK3(X16,k2_tarski(X15,X15),X17),k2_tarski(X15,X15)) = X15 | k2_tarski(X15,X15) = k2_tarski(sK2(X13,X14,k2_tarski(X15,X15)),sK3(X16,k2_tarski(X15,X15),X17)) | ~m1_subset_1(X17,u1_struct_0(X16)) | ~l1_orders_2(X16) | sK2(X13,X14,k2_tarski(X15,X15)) = X14 | sK2(X13,X14,k2_tarski(X15,X15)) = X13 | k2_tarski(X13,X14) = k2_tarski(X15,X15)).
% 8.60/1.49  
% 8.60/1.49  cnf(u2606,axiom,
% 8.60/1.49      r1_lattice3(X16,k2_tarski(X15,X15),X17) | sK2(sK3(X16,k2_tarski(X15,X15),X17),sK2(X13,X14,k2_tarski(X15,X15)),k2_tarski(X15,X15)) = X15 | k2_tarski(X15,X15) = k2_tarski(sK2(X13,X14,k2_tarski(X15,X15)),sK3(X16,k2_tarski(X15,X15),X17)) | ~m1_subset_1(X17,u1_struct_0(X16)) | ~l1_orders_2(X16) | sK2(X13,X14,k2_tarski(X15,X15)) = X14 | sK2(X13,X14,k2_tarski(X15,X15)) = X13 | k2_tarski(X13,X14) = k2_tarski(X15,X15)).
% 8.60/1.49  
% 8.60/1.49  cnf(u2444,axiom,
% 8.60/1.49      r1_lattice3(X13,k2_tarski(X12,X12),X14) | ~m1_subset_1(X14,u1_struct_0(X13)) | ~l1_orders_2(X13) | sK2(X10,X11,k2_tarski(X12,X12)) = sK3(X13,k2_tarski(X12,X12),X14) | sK3(X13,k2_tarski(X12,X12),X14) = X12 | sK2(X10,X11,k2_tarski(X12,X12)) = X11 | sK2(X10,X11,k2_tarski(X12,X12)) = X10 | k2_tarski(X10,X11) = k2_tarski(X12,X12)).
% 8.60/1.49  
% 8.60/1.49  cnf(u2258,axiom,
% 8.60/1.49      r1_lattice3(X5,k2_tarski(X6,X6),X7) | sK2(X4,sK3(X5,k2_tarski(X6,X6),X7),k2_tarski(X6,X6)) = X4 | sK2(X4,sK3(X5,k2_tarski(X6,X6),X7),k2_tarski(X6,X6)) = X6 | k2_tarski(X6,X6) = k2_tarski(X4,sK3(X5,k2_tarski(X6,X6),X7)) | ~m1_subset_1(X7,u1_struct_0(X5)) | ~l1_orders_2(X5)).
% 8.60/1.49  
% 8.60/1.49  cnf(u2246,axiom,
% 8.60/1.49      r1_lattice3(X5,k2_tarski(X4,X4),X6) | sK2(sK3(X5,k2_tarski(X4,X4),X6),X7,k2_tarski(X4,X4)) = X7 | sK2(sK3(X5,k2_tarski(X4,X4),X6),X7,k2_tarski(X4,X4)) = X4 | k2_tarski(X4,X4) = k2_tarski(sK3(X5,k2_tarski(X4,X4),X6),X7) | ~m1_subset_1(X6,u1_struct_0(X5)) | ~l1_orders_2(X5)).
% 8.60/1.49  
% 8.60/1.49  cnf(u990,axiom,
% 8.60/1.49      r1_lattice3(X3,k2_tarski(X2,X2),X4) | k2_tarski(X2,X2) = k2_tarski(X2,sK3(X3,k2_tarski(X2,X2),X4)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~l1_orders_2(X3)).
% 8.60/1.49  
% 8.60/1.49  cnf(u417,axiom,
% 8.60/1.49      r1_lattice3(X2,k2_tarski(X3,X3),X4) | sK2(sK3(X2,k2_tarski(X3,X3),X4),sK3(X2,k2_tarski(X3,X3),X4),k2_tarski(X3,X3)) = X3 | k2_tarski(X3,X3) = k2_tarski(sK3(X2,k2_tarski(X3,X3),X4),sK3(X2,k2_tarski(X3,X3),X4)) | ~m1_subset_1(X4,u1_struct_0(X2)) | ~l1_orders_2(X2)).
% 8.60/1.49  
% 8.60/1.49  cnf(u2779,axiom,
% 8.60/1.49      r1_lattice3(X10,k2_tarski(X8,X9),X11) | sK2(sK3(X10,k2_tarski(X8,X9),X11),sK2(X12,X13,k2_tarski(X8,X9)),k2_tarski(X8,X9)) = X8 | sK2(sK3(X10,k2_tarski(X8,X9),X11),sK2(X12,X13,k2_tarski(X8,X9)),k2_tarski(X8,X9)) = X9 | sK2(X12,X13,k2_tarski(X8,X9)) = X13 | sK2(X12,X13,k2_tarski(X8,X9)) = X12 | k2_tarski(X8,X9) = k2_tarski(X12,X13) | k2_tarski(X8,X9) = k2_tarski(sK3(X10,k2_tarski(X8,X9),X11),sK2(X12,X13,k2_tarski(X8,X9))) | ~m1_subset_1(X11,u1_struct_0(X10)) | ~l1_orders_2(X10)).
% 8.60/1.49  
% 8.60/1.49  cnf(u2658,axiom,
% 8.60/1.49      r1_lattice3(X12,k2_tarski(X8,X9),X13) | sK2(sK2(X10,X11,k2_tarski(X8,X9)),sK3(X12,k2_tarski(X8,X9),X13),k2_tarski(X8,X9)) = X8 | sK2(sK2(X10,X11,k2_tarski(X8,X9)),sK3(X12,k2_tarski(X8,X9),X13),k2_tarski(X8,X9)) = X9 | sK2(X10,X11,k2_tarski(X8,X9)) = X11 | sK2(X10,X11,k2_tarski(X8,X9)) = X10 | k2_tarski(X10,X11) = k2_tarski(X8,X9) | k2_tarski(X8,X9) = k2_tarski(sK2(X10,X11,k2_tarski(X8,X9)),sK3(X12,k2_tarski(X8,X9),X13)) | ~m1_subset_1(X13,u1_struct_0(X12)) | ~l1_orders_2(X12)).
% 8.60/1.49  
% 8.60/1.49  cnf(u2611,axiom,
% 8.60/1.49      r1_lattice3(X2,k2_tarski(X1,X0),X3) | sK2(X0,sK3(X2,k2_tarski(X1,X0),X3),k2_tarski(X1,X0)) = X1 | k2_tarski(X1,X0) = k2_tarski(X0,sK3(X2,k2_tarski(X1,X0),X3)) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_orders_2(X2)).
% 8.60/1.49  
% 8.60/1.49  cnf(u2603,axiom,
% 8.60/1.49      r1_lattice3(X2,k2_tarski(X1,X0),X3) | sK2(sK3(X2,k2_tarski(X1,X0),X3),X0,k2_tarski(X1,X0)) = X1 | k2_tarski(X1,X0) = k2_tarski(X0,sK3(X2,k2_tarski(X1,X0),X3)) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_orders_2(X2)).
% 8.60/1.49  
% 8.60/1.49  cnf(u2251,axiom,
% 8.60/1.49      r1_lattice3(X6,k2_tarski(X4,X5),X7) | sK2(X4,sK3(X6,k2_tarski(X4,X5),X7),k2_tarski(X4,X5)) = X5 | k2_tarski(X4,X5) = k2_tarski(X4,sK3(X6,k2_tarski(X4,X5),X7)) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~l1_orders_2(X6)).
% 8.60/1.49  
% 8.60/1.49  cnf(u1941,axiom,
% 8.60/1.49      r1_lattice3(X4,k2_tarski(X5,X6),X7) | sK2(sK3(X4,k2_tarski(X5,X6),X7),X5,k2_tarski(X5,X6)) = X6 | k2_tarski(X5,X6) = k2_tarski(X5,sK3(X4,k2_tarski(X5,X6),X7)) | ~m1_subset_1(X7,u1_struct_0(X4)) | ~l1_orders_2(X4)).
% 8.60/1.49  
% 8.60/1.49  cnf(u1778,axiom,
% 8.60/1.49      r1_lattice3(X6,k2_tarski(X4,X5),X7) | sK2(sK3(X6,k2_tarski(X4,X5),X7),sK3(X6,k2_tarski(X4,X5),X7),k2_tarski(X4,X5)) = X4 | sK2(sK3(X6,k2_tarski(X4,X5),X7),sK3(X6,k2_tarski(X4,X5),X7),k2_tarski(X4,X5)) = X5 | k2_tarski(X4,X5) = k2_tarski(sK3(X6,k2_tarski(X4,X5),X7),sK3(X6,k2_tarski(X4,X5),X7)) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~l1_orders_2(X6)).
% 8.60/1.49  
% 8.60/1.49  cnf(u312,axiom,
% 8.60/1.49      r1_lattice3(X9,k2_tarski(X6,X7),X10) | sK2(X8,sK3(X9,k2_tarski(X6,X7),X10),k2_tarski(X6,X7)) = X8 | sK2(X8,sK3(X9,k2_tarski(X6,X7),X10),k2_tarski(X6,X7)) = X6 | sK2(X8,sK3(X9,k2_tarski(X6,X7),X10),k2_tarski(X6,X7)) = X7 | k2_tarski(X6,X7) = k2_tarski(X8,sK3(X9,k2_tarski(X6,X7),X10)) | ~m1_subset_1(X10,u1_struct_0(X9)) | ~l1_orders_2(X9)).
% 8.60/1.49  
% 8.60/1.49  cnf(u286,axiom,
% 8.60/1.49      r1_lattice3(X8,k2_tarski(X6,X7),X9) | sK2(sK3(X8,k2_tarski(X6,X7),X9),X10,k2_tarski(X6,X7)) = X10 | sK2(sK3(X8,k2_tarski(X6,X7),X9),X10,k2_tarski(X6,X7)) = X6 | sK2(sK3(X8,k2_tarski(X6,X7),X9),X10,k2_tarski(X6,X7)) = X7 | k2_tarski(X6,X7) = k2_tarski(sK3(X8,k2_tarski(X6,X7),X9),X10) | ~m1_subset_1(X9,u1_struct_0(X8)) | ~l1_orders_2(X8)).
% 8.60/1.49  
% 8.60/1.49  cnf(u82,axiom,
% 8.60/1.49      r1_lattice3(X0,k2_tarski(X1,X2),X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_orders_2(X0) | sK3(X0,k2_tarski(X1,X2),X3) = X1 | sK3(X0,k2_tarski(X1,X2),X3) = X2).
% 8.60/1.49  
% 8.60/1.49  cnf(u60,axiom,
% 8.60/1.49      r1_lattice3(X0,X1,X2) | ~r1_orders_2(X0,X2,sK3(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 8.60/1.49  
% 8.60/1.49  cnf(u84,negated_conjecture,
% 8.60/1.49      r1_lattice3(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | k2_tarski(sK3(sK0,X0,X1),sK3(sK0,X0,X1)) = k6_domain_1(u1_struct_0(sK0),sK3(sK0,X0,X1)) | ~l1_struct_0(sK0)).
% 8.60/1.49  
% 8.60/1.49  cnf(u57,axiom,
% 8.60/1.49      r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 8.60/1.49  
% 8.60/1.49  cnf(u61,axiom,
% 8.60/1.49      r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 8.60/1.49  
% 8.60/1.49  cnf(u54,axiom,
% 8.60/1.49      r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)).
% 8.60/1.49  
% 8.60/1.49  cnf(u41,negated_conjecture,
% 8.60/1.49      v3_orders_2(sK0)).
% 8.60/1.49  
% 8.60/1.49  cnf(u62,axiom,
% 8.60/1.49      m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 8.60/1.49  
% 8.60/1.49  cnf(u58,axiom,
% 8.60/1.49      m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 8.60/1.49  
% 8.60/1.49  cnf(u44,negated_conjecture,
% 8.60/1.49      m1_subset_1(sK1,u1_struct_0(sK0))).
% 8.60/1.49  
% 8.60/1.49  cnf(u76,negated_conjecture,
% 8.60/1.49      ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_tarski(X0,X0) = k6_domain_1(u1_struct_0(sK0),X0) | ~l1_struct_0(sK0)).
% 8.60/1.49  
% 8.60/1.49  cnf(u43,negated_conjecture,
% 8.60/1.49      l1_orders_2(sK0)).
% 8.60/1.49  
% 8.60/1.49  cnf(u65,axiom,
% 8.60/1.49      v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1)).
% 8.60/1.49  
% 8.60/1.49  cnf(u73,negated_conjecture,
% 8.60/1.49      ~v1_xboole_0(u1_struct_0(sK0)) | ~l1_struct_0(sK0)).
% 8.60/1.49  
% 8.60/1.49  cnf(u56,axiom,
% 8.60/1.49      l1_struct_0(X0) | ~l1_orders_2(X0)).
% 8.60/1.49  
% 8.60/1.49  cnf(u55,axiom,
% 8.60/1.49      v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0))).
% 8.60/1.49  
% 8.60/1.49  cnf(u40,negated_conjecture,
% 8.60/1.49      ~v2_struct_0(sK0)).
% 8.60/1.49  
% 8.60/1.49  cnf(u49,axiom,
% 8.60/1.49      r2_hidden(sK2(X0,X1,X2),X2) | sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | k2_tarski(X0,X1) = X2).
% 8.60/1.49  
% 8.60/1.49  cnf(u63,axiom,
% 8.60/1.49      r2_hidden(sK4(X0,X1,X2),X1) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 8.60/1.49  
% 8.60/1.49  cnf(u59,axiom,
% 8.60/1.49      r2_hidden(sK3(X0,X1,X2),X1) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 8.60/1.49  
% 8.60/1.49  cnf(u69,axiom,
% 8.60/1.49      r2_hidden(X4,k2_tarski(X4,X1))).
% 8.60/1.49  
% 8.60/1.49  cnf(u67,axiom,
% 8.60/1.49      r2_hidden(X4,k2_tarski(X0,X4))).
% 8.60/1.49  
% 8.60/1.49  cnf(u943,axiom,
% 8.60/1.49      ~r2_hidden(X40,k2_tarski(X40,X40)) | k2_tarski(X40,X40) = k2_tarski(X39,X40) | sK2(X39,X40,k2_tarski(X40,X40)) = X39).
% 8.60/1.49  
% 8.60/1.49  cnf(u1703,axiom,
% 8.60/1.49      ~r2_hidden(X58,k2_tarski(X58,X58)) | k2_tarski(X58,X59) = k2_tarski(X58,X58) | sK2(X58,X59,k2_tarski(X58,X58)) = X59).
% 8.60/1.49  
% 8.60/1.49  cnf(u214,axiom,
% 8.60/1.49      ~r2_hidden(X12,k2_tarski(X12,X13)) | k2_tarski(X12,X12) = k2_tarski(X12,X13) | sK2(X12,X12,k2_tarski(X12,X13)) = X13).
% 8.60/1.49  
% 8.60/1.49  cnf(u818,axiom,
% 8.60/1.49      ~r2_hidden(X38,k2_tarski(X38,X37)) | k2_tarski(X38,X37) = k2_tarski(X37,X38)).
% 8.60/1.49  
% 8.60/1.49  cnf(u410,axiom,
% 8.60/1.49      ~r2_hidden(X19,k2_tarski(X19,X20)) | k2_tarski(X19,X20) = k2_tarski(X18,X19) | sK2(X18,X19,k2_tarski(X19,X20)) = X18 | sK2(X18,X19,k2_tarski(X19,X20)) = X20).
% 8.60/1.49  
% 8.60/1.49  cnf(u570,axiom,
% 8.60/1.49      ~r2_hidden(X27,k2_tarski(X27,X29)) | k2_tarski(X27,X29) = k2_tarski(X27,X28) | sK2(X27,X28,k2_tarski(X27,X29)) = X28 | sK2(X27,X28,k2_tarski(X27,X29)) = X29).
% 8.60/1.49  
% 8.60/1.49  cnf(u2511,axiom,
% 8.60/1.49      ~r2_hidden(X294,k2_tarski(X293,X293)) | k2_tarski(X293,X293) = k2_tarski(sK2(X291,X292,k2_tarski(X293,X293)),X294) | sK2(sK2(X291,X292,k2_tarski(X293,X293)),X294,k2_tarski(X293,X293)) = X293 | sK2(X291,X292,k2_tarski(X293,X293)) = X292 | sK2(X291,X292,k2_tarski(X293,X293)) = X291 | k2_tarski(X293,X293) = k2_tarski(X291,X292)).
% 8.60/1.49  
% 8.60/1.49  cnf(u2503,axiom,
% 8.60/1.49      ~r2_hidden(X262,k2_tarski(X261,X261)) | k2_tarski(X261,X261) = k2_tarski(X262,sK2(X259,X260,k2_tarski(X261,X261))) | sK2(X262,sK2(X259,X260,k2_tarski(X261,X261)),k2_tarski(X261,X261)) = X261 | sK2(X259,X260,k2_tarski(X261,X261)) = X260 | sK2(X259,X260,k2_tarski(X261,X261)) = X259 | k2_tarski(X261,X261) = k2_tarski(X259,X260)).
% 8.60/1.49  
% 8.60/1.49  cnf(u2443,axiom,
% 8.60/1.49      ~r2_hidden(X9,k2_tarski(X8,X8)) | sK2(X6,X7,k2_tarski(X8,X8)) = X9 | X8 = X9 | sK2(X6,X7,k2_tarski(X8,X8)) = X7 | sK2(X6,X7,k2_tarski(X8,X8)) = X6 | k2_tarski(X6,X7) = k2_tarski(X8,X8)).
% 8.60/1.49  
% 8.60/1.49  cnf(u1755,axiom,
% 8.60/1.49      ~r2_hidden(X65,k2_tarski(X64,X64)) | k2_tarski(X64,X64) = k2_tarski(X64,X65)).
% 8.60/1.49  
% 8.60/1.49  cnf(u981,axiom,
% 8.60/1.49      ~r2_hidden(X41,k2_tarski(X42,X42)) | k2_tarski(X42,X42) = k2_tarski(X41,X42)).
% 8.60/1.49  
% 8.60/1.49  cnf(u796,axiom,
% 8.60/1.49      ~r2_hidden(X45,k2_tarski(X46,X46)) | k2_tarski(X44,X45) = k2_tarski(X46,X46) | sK2(X44,X45,k2_tarski(X46,X46)) = X44 | sK2(X44,X45,k2_tarski(X46,X46)) = X46).
% 8.60/1.49  
% 8.60/1.49  cnf(u794,axiom,
% 8.60/1.49      ~r2_hidden(X41,k2_tarski(X43,X43)) | k2_tarski(X43,X43) = k2_tarski(X41,X42) | sK2(X41,X42,k2_tarski(X43,X43)) = X42 | sK2(X41,X42,k2_tarski(X43,X43)) = X43).
% 8.60/1.49  
% 8.60/1.49  cnf(u346,axiom,
% 8.60/1.49      ~r2_hidden(X12,k2_tarski(X13,X13)) | k2_tarski(X12,X12) = k2_tarski(X13,X13) | sK2(X12,X12,k2_tarski(X13,X13)) = X13).
% 8.60/1.49  
% 8.60/1.49  cnf(u275,axiom,
% 8.60/1.49      ~r2_hidden(X12,k2_tarski(X13,X12)) | k2_tarski(X12,X12) = k2_tarski(X13,X12) | sK2(X12,X12,k2_tarski(X13,X12)) = X13).
% 8.60/1.49  
% 8.60/1.49  cnf(u700,axiom,
% 8.60/1.49      ~r2_hidden(X28,k2_tarski(X29,X28)) | k2_tarski(X29,X28) = k2_tarski(X28,X29) | sK2(X28,X29,k2_tarski(X29,X28)) = X29).
% 8.60/1.49  
% 8.60/1.49  cnf(u484,axiom,
% 8.60/1.49      ~r2_hidden(X25,k2_tarski(X26,X25)) | k2_tarski(X26,X25) = k2_tarski(X24,X25) | sK2(X24,X25,k2_tarski(X26,X25)) = X24 | sK2(X24,X25,k2_tarski(X26,X25)) = X26).
% 8.60/1.49  
% 8.60/1.49  cnf(u658,axiom,
% 8.60/1.49      ~r2_hidden(X33,k2_tarski(X35,X33)) | k2_tarski(X33,X34) = k2_tarski(X35,X33) | sK2(X33,X34,k2_tarski(X35,X33)) = X34 | sK2(X33,X34,k2_tarski(X35,X33)) = X35).
% 8.60/1.49  
% 8.60/1.49  cnf(u2254,axiom,
% 8.60/1.49      ~r2_hidden(X2,k2_tarski(X1,X0)) | k2_tarski(X1,X0) = k2_tarski(X0,X2) | sK2(X0,X2,k2_tarski(X1,X0)) = X1).
% 8.60/1.49  
% 8.60/1.49  cnf(u2231,axiom,
% 8.60/1.49      ~r2_hidden(X96,k2_tarski(X95,X97)) | k2_tarski(X95,X97) = k2_tarski(X95,X96) | sK2(X95,X96,k2_tarski(X95,X97)) = X97).
% 8.60/1.49  
% 8.60/1.49  cnf(u1939,axiom,
% 8.60/1.49      ~r2_hidden(X2,k2_tarski(X1,X0)) | k2_tarski(X1,X0) = k2_tarski(X2,X0) | sK2(X2,X0,k2_tarski(X1,X0)) = X1).
% 8.60/1.49  
% 8.60/1.49  cnf(u1911,axiom,
% 8.60/1.49      ~r2_hidden(X87,k2_tarski(X88,X89)) | k2_tarski(X87,X88) = k2_tarski(X88,X89) | sK2(X87,X88,k2_tarski(X88,X89)) = X89).
% 8.60/1.49  
% 8.60/1.49  cnf(u1563,axiom,
% 8.60/1.49      ~r2_hidden(X79,k2_tarski(X82,X83)) | k2_tarski(X82,X83) = k2_tarski(X79,sK2(X80,X81,k2_tarski(X82,X83))) | sK2(X79,sK2(X80,X81,k2_tarski(X82,X83)),k2_tarski(X82,X83)) = X82 | sK2(X79,sK2(X80,X81,k2_tarski(X82,X83)),k2_tarski(X82,X83)) = X83 | sK2(X80,X81,k2_tarski(X82,X83)) = X81 | sK2(X80,X81,k2_tarski(X82,X83)) = X80 | k2_tarski(X82,X83) = k2_tarski(X80,X81)).
% 8.60/1.49  
% 8.60/1.49  cnf(u1227,axiom,
% 8.60/1.49      ~r2_hidden(X79,k2_tarski(X77,X78)) | k2_tarski(X77,X78) = k2_tarski(sK2(X75,X76,k2_tarski(X77,X78)),X79) | sK2(sK2(X75,X76,k2_tarski(X77,X78)),X79,k2_tarski(X77,X78)) = X77 | sK2(sK2(X75,X76,k2_tarski(X77,X78)),X79,k2_tarski(X77,X78)) = X78 | sK2(X75,X76,k2_tarski(X77,X78)) = X76 | sK2(X75,X76,k2_tarski(X77,X78)) = X75 | k2_tarski(X75,X76) = k2_tarski(X77,X78)).
% 8.60/1.49  
% 8.60/1.49  cnf(u663,axiom,
% 8.60/1.49      ~r2_hidden(X37,k2_tarski(X38,X36)) | k2_tarski(X36,X37) = k2_tarski(X38,X36) | sK2(X36,X37,k2_tarski(X38,X36)) = X38 | sK2(X36,X37,k2_tarski(X38,X36)) = X36).
% 8.60/1.49  
% 8.60/1.49  cnf(u572,axiom,
% 8.60/1.49      ~r2_hidden(X31,k2_tarski(X30,X32)) | k2_tarski(X30,X32) = k2_tarski(X30,X31) | sK2(X30,X31,k2_tarski(X30,X32)) = X30 | sK2(X30,X31,k2_tarski(X30,X32)) = X32).
% 8.60/1.49  
% 8.60/1.49  cnf(u491,axiom,
% 8.60/1.49      ~r2_hidden(X21,k2_tarski(X23,X22)) | k2_tarski(X23,X22) = k2_tarski(X21,X22) | sK2(X21,X22,k2_tarski(X23,X22)) = X23 | sK2(X21,X22,k2_tarski(X23,X22)) = X22).
% 8.60/1.49  
% 8.60/1.49  cnf(u414,axiom,
% 8.60/1.49      ~r2_hidden(X15,k2_tarski(X16,X17)) | k2_tarski(X16,X17) = k2_tarski(X15,X16) | sK2(X15,X16,k2_tarski(X16,X17)) = X16 | sK2(X15,X16,k2_tarski(X16,X17)) = X17).
% 8.60/1.49  
% 8.60/1.49  cnf(u181,axiom,
% 8.60/1.49      ~r2_hidden(X18,k2_tarski(X19,X20)) | k2_tarski(X19,X20) = k2_tarski(X18,X18) | sK2(X18,X18,k2_tarski(X19,X20)) = X19 | sK2(X18,X18,k2_tarski(X19,X20)) = X20).
% 8.60/1.49  
% 8.60/1.49  cnf(u133,axiom,
% 8.60/1.49      ~r2_hidden(X9,k2_tarski(X10,X11)) | k2_tarski(X10,X11) = k2_tarski(X8,X9) | sK2(X8,X9,k2_tarski(X10,X11)) = X8 | sK2(X8,X9,k2_tarski(X10,X11)) = X10 | sK2(X8,X9,k2_tarski(X10,X11)) = X11).
% 8.60/1.49  
% 8.60/1.49  cnf(u131,axiom,
% 8.60/1.49      ~r2_hidden(X4,k2_tarski(X6,X7)) | k2_tarski(X6,X7) = k2_tarski(X4,X5) | sK2(X4,X5,k2_tarski(X6,X7)) = X5 | sK2(X4,X5,k2_tarski(X6,X7)) = X6 | sK2(X4,X5,k2_tarski(X6,X7)) = X7).
% 8.60/1.49  
% 8.60/1.49  cnf(u70,axiom,
% 8.60/1.49      ~r2_hidden(X4,k2_tarski(X0,X1)) | X0 = X4 | X1 = X4).
% 8.60/1.49  
% 8.60/1.49  cnf(u1763,axiom,
% 8.60/1.49      k2_tarski(X8,X8) = k2_tarski(X8,sK2(X9,X10,k2_tarski(X8,X8))) | sK2(X9,X10,k2_tarski(X8,X8)) = X10 | sK2(X9,X10,k2_tarski(X8,X8)) = X9 | k2_tarski(X8,X8) = k2_tarski(X9,X10)).
% 8.60/1.49  
% 8.60/1.49  cnf(u989,axiom,
% 8.60/1.49      k2_tarski(X8,X8) = k2_tarski(sK2(X9,X10,k2_tarski(X8,X8)),X8) | sK2(X9,X10,k2_tarski(X8,X8)) = X10 | sK2(X9,X10,k2_tarski(X8,X8)) = X9 | k2_tarski(X8,X8) = k2_tarski(X9,X10)).
% 8.60/1.49  
% 8.60/1.49  cnf(u823,axiom,
% 8.60/1.49      k2_tarski(X1,X2) = k2_tarski(X2,X1)).
% 8.60/1.49  
% 8.60/1.49  cnf(u5150,axiom,
% 8.60/1.49      sK2(sK2(X0,X1,k2_tarski(X2,X2)),sK2(X3,X4,k2_tarski(X2,X2)),k2_tarski(X2,X2)) = X2 | k2_tarski(X2,X2) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X2)),sK2(X3,X4,k2_tarski(X2,X2))) | sK2(X0,X1,k2_tarski(X2,X2)) = X1 | sK2(X0,X1,k2_tarski(X2,X2)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X2) | sK2(X3,X4,k2_tarski(X2,X2)) = X4 | sK2(X3,X4,k2_tarski(X2,X2)) = X3 | k2_tarski(X2,X2) = k2_tarski(X3,X4)).
% 8.60/1.49  
% 8.60/1.49  cnf(u2724,axiom,
% 8.60/1.49      sK2(sK2(X16,X17,k2_tarski(X15,X15)),sK2(X13,X14,k2_tarski(X15,X15)),k2_tarski(X15,X15)) = X15 | k2_tarski(X15,X15) = k2_tarski(sK2(X13,X14,k2_tarski(X15,X15)),sK2(X16,X17,k2_tarski(X15,X15))) | sK2(X16,X17,k2_tarski(X15,X15)) = X17 | sK2(X16,X17,k2_tarski(X15,X15)) = X16 | k2_tarski(X16,X17) = k2_tarski(X15,X15) | sK2(X13,X14,k2_tarski(X15,X15)) = X14 | sK2(X13,X14,k2_tarski(X15,X15)) = X13 | k2_tarski(X13,X14) = k2_tarski(X15,X15)).
% 8.60/1.49  
% 8.60/1.49  cnf(u419,axiom,
% 8.60/1.49      sK2(sK2(X8,X9,k2_tarski(X10,X10)),sK2(X8,X9,k2_tarski(X10,X10)),k2_tarski(X10,X10)) = X10 | k2_tarski(X10,X10) = k2_tarski(sK2(X8,X9,k2_tarski(X10,X10)),sK2(X8,X9,k2_tarski(X10,X10))) | sK2(X8,X9,k2_tarski(X10,X10)) = X9 | sK2(X8,X9,k2_tarski(X10,X10)) = X8 | k2_tarski(X8,X9) = k2_tarski(X10,X10)).
% 8.60/1.49  
% 8.60/1.49  cnf(u2248,axiom,
% 8.60/1.49      sK2(sK2(X13,X14,k2_tarski(X12,X12)),X15,k2_tarski(X12,X12)) = X15 | sK2(sK2(X13,X14,k2_tarski(X12,X12)),X15,k2_tarski(X12,X12)) = X12 | k2_tarski(X12,X12) = k2_tarski(sK2(X13,X14,k2_tarski(X12,X12)),X15) | sK2(X13,X14,k2_tarski(X12,X12)) = X14 | sK2(X13,X14,k2_tarski(X12,X12)) = X13 | k2_tarski(X13,X14) = k2_tarski(X12,X12)).
% 8.60/1.49  
% 8.60/1.49  cnf(u2248,axiom,
% 8.60/1.49      sK2(sK2(X13,X14,k2_tarski(X12,X12)),X15,k2_tarski(X12,X12)) = X15 | sK2(sK2(X13,X14,k2_tarski(X12,X12)),X15,k2_tarski(X12,X12)) = X12 | k2_tarski(X12,X12) = k2_tarski(sK2(X13,X14,k2_tarski(X12,X12)),X15) | sK2(X13,X14,k2_tarski(X12,X12)) = X14 | sK2(X13,X14,k2_tarski(X12,X12)) = X13 | k2_tarski(X13,X14) = k2_tarski(X12,X12)).
% 8.60/1.49  
% 8.60/1.49  cnf(u2660,axiom,
% 8.60/1.49      sK2(sK2(X22,X23,k2_tarski(X20,X21)),sK2(X24,X25,k2_tarski(X20,X21)),k2_tarski(X20,X21)) = X20 | sK2(sK2(X22,X23,k2_tarski(X20,X21)),sK2(X24,X25,k2_tarski(X20,X21)),k2_tarski(X20,X21)) = X21 | k2_tarski(X20,X21) = k2_tarski(sK2(X22,X23,k2_tarski(X20,X21)),sK2(X24,X25,k2_tarski(X20,X21))) | sK2(X22,X23,k2_tarski(X20,X21)) = X23 | sK2(X22,X23,k2_tarski(X20,X21)) = X22 | k2_tarski(X20,X21) = k2_tarski(X22,X23) | sK2(X24,X25,k2_tarski(X20,X21)) = X25 | sK2(X24,X25,k2_tarski(X20,X21)) = X24 | k2_tarski(X20,X21) = k2_tarski(X24,X25)).
% 8.60/1.49  
% 8.60/1.49  cnf(u2660,axiom,
% 8.60/1.49      sK2(sK2(X22,X23,k2_tarski(X20,X21)),sK2(X24,X25,k2_tarski(X20,X21)),k2_tarski(X20,X21)) = X20 | sK2(sK2(X22,X23,k2_tarski(X20,X21)),sK2(X24,X25,k2_tarski(X20,X21)),k2_tarski(X20,X21)) = X21 | k2_tarski(X20,X21) = k2_tarski(sK2(X22,X23,k2_tarski(X20,X21)),sK2(X24,X25,k2_tarski(X20,X21))) | sK2(X22,X23,k2_tarski(X20,X21)) = X23 | sK2(X22,X23,k2_tarski(X20,X21)) = X22 | k2_tarski(X20,X21) = k2_tarski(X22,X23) | sK2(X24,X25,k2_tarski(X20,X21)) = X25 | sK2(X24,X25,k2_tarski(X20,X21)) = X24 | k2_tarski(X20,X21) = k2_tarski(X24,X25)).
% 8.60/1.49  
% 8.60/1.49  cnf(u1780,axiom,
% 8.60/1.49      sK2(sK2(X14,X15,k2_tarski(X12,X13)),sK2(X14,X15,k2_tarski(X12,X13)),k2_tarski(X12,X13)) = X12 | sK2(sK2(X14,X15,k2_tarski(X12,X13)),sK2(X14,X15,k2_tarski(X12,X13)),k2_tarski(X12,X13)) = X13 | k2_tarski(X12,X13) = k2_tarski(sK2(X14,X15,k2_tarski(X12,X13)),sK2(X14,X15,k2_tarski(X12,X13))) | sK2(X14,X15,k2_tarski(X12,X13)) = X15 | sK2(X14,X15,k2_tarski(X12,X13)) = X14 | k2_tarski(X14,X15) = k2_tarski(X12,X13)).
% 8.60/1.49  
% 8.60/1.49  cnf(u1780,axiom,
% 8.60/1.49      sK2(sK2(X14,X15,k2_tarski(X12,X13)),sK2(X14,X15,k2_tarski(X12,X13)),k2_tarski(X12,X13)) = X12 | sK2(sK2(X14,X15,k2_tarski(X12,X13)),sK2(X14,X15,k2_tarski(X12,X13)),k2_tarski(X12,X13)) = X13 | k2_tarski(X12,X13) = k2_tarski(sK2(X14,X15,k2_tarski(X12,X13)),sK2(X14,X15,k2_tarski(X12,X13))) | sK2(X14,X15,k2_tarski(X12,X13)) = X15 | sK2(X14,X15,k2_tarski(X12,X13)) = X14 | k2_tarski(X14,X15) = k2_tarski(X12,X13)).
% 8.60/1.49  
% 8.60/1.49  cnf(u288,axiom,
% 8.60/1.49      sK2(sK2(X18,X19,k2_tarski(X16,X17)),X20,k2_tarski(X16,X17)) = X20 | sK2(sK2(X18,X19,k2_tarski(X16,X17)),X20,k2_tarski(X16,X17)) = X16 | sK2(sK2(X18,X19,k2_tarski(X16,X17)),X20,k2_tarski(X16,X17)) = X17 | k2_tarski(X16,X17) = k2_tarski(sK2(X18,X19,k2_tarski(X16,X17)),X20) | sK2(X18,X19,k2_tarski(X16,X17)) = X19 | sK2(X18,X19,k2_tarski(X16,X17)) = X18 | k2_tarski(X16,X17) = k2_tarski(X18,X19)).
% 8.60/1.49  
% 8.60/1.49  cnf(u288,axiom,
% 8.60/1.49      sK2(sK2(X18,X19,k2_tarski(X16,X17)),X20,k2_tarski(X16,X17)) = X20 | sK2(sK2(X18,X19,k2_tarski(X16,X17)),X20,k2_tarski(X16,X17)) = X16 | sK2(sK2(X18,X19,k2_tarski(X16,X17)),X20,k2_tarski(X16,X17)) = X17 | k2_tarski(X16,X17) = k2_tarski(sK2(X18,X19,k2_tarski(X16,X17)),X20) | sK2(X18,X19,k2_tarski(X16,X17)) = X19 | sK2(X18,X19,k2_tarski(X16,X17)) = X18 | k2_tarski(X16,X17) = k2_tarski(X18,X19)).
% 8.60/1.49  
% 8.60/1.49  cnf(u288,axiom,
% 8.60/1.49      sK2(sK2(X18,X19,k2_tarski(X16,X17)),X20,k2_tarski(X16,X17)) = X20 | sK2(sK2(X18,X19,k2_tarski(X16,X17)),X20,k2_tarski(X16,X17)) = X16 | sK2(sK2(X18,X19,k2_tarski(X16,X17)),X20,k2_tarski(X16,X17)) = X17 | k2_tarski(X16,X17) = k2_tarski(sK2(X18,X19,k2_tarski(X16,X17)),X20) | sK2(X18,X19,k2_tarski(X16,X17)) = X19 | sK2(X18,X19,k2_tarski(X16,X17)) = X18 | k2_tarski(X16,X17) = k2_tarski(X18,X19)).
% 8.60/1.49  
% 8.60/1.49  cnf(u2721,axiom,
% 8.60/1.49      sK2(sK2(X2,X3,k2_tarski(X1,X0)),X0,k2_tarski(X1,X0)) = X1 | k2_tarski(X1,X0) = k2_tarski(X0,sK2(X2,X3,k2_tarski(X1,X0))) | sK2(X2,X3,k2_tarski(X1,X0)) = X3 | sK2(X2,X3,k2_tarski(X1,X0)) = X2 | k2_tarski(X1,X0) = k2_tarski(X2,X3)).
% 8.60/1.49  
% 8.60/1.49  cnf(u1943,axiom,
% 8.60/1.49      sK2(sK2(X12,X13,k2_tarski(X14,X15)),X14,k2_tarski(X14,X15)) = X15 | k2_tarski(X14,X15) = k2_tarski(X14,sK2(X12,X13,k2_tarski(X14,X15))) | sK2(X12,X13,k2_tarski(X14,X15)) = X13 | sK2(X12,X13,k2_tarski(X14,X15)) = X12 | k2_tarski(X14,X15) = k2_tarski(X12,X13)).
% 8.60/1.49  
% 8.60/1.49  cnf(u2253,axiom,
% 8.60/1.49      sK2(X12,sK2(X14,X15,k2_tarski(X12,X13)),k2_tarski(X12,X13)) = X13 | k2_tarski(X12,X13) = k2_tarski(X12,sK2(X14,X15,k2_tarski(X12,X13))) | sK2(X14,X15,k2_tarski(X12,X13)) = X15 | sK2(X14,X15,k2_tarski(X12,X13)) = X14 | k2_tarski(X14,X15) = k2_tarski(X12,X13)).
% 8.60/1.49  
% 8.60/1.49  cnf(u2260,axiom,
% 8.60/1.49      sK2(X12,sK2(X13,X14,k2_tarski(X15,X15)),k2_tarski(X15,X15)) = X12 | sK2(X12,sK2(X13,X14,k2_tarski(X15,X15)),k2_tarski(X15,X15)) = X15 | k2_tarski(X15,X15) = k2_tarski(X12,sK2(X13,X14,k2_tarski(X15,X15))) | sK2(X13,X14,k2_tarski(X15,X15)) = X14 | sK2(X13,X14,k2_tarski(X15,X15)) = X13 | k2_tarski(X13,X14) = k2_tarski(X15,X15)).
% 8.60/1.49  
% 8.60/1.49  cnf(u2260,axiom,
% 8.60/1.49      sK2(X12,sK2(X13,X14,k2_tarski(X15,X15)),k2_tarski(X15,X15)) = X12 | sK2(X12,sK2(X13,X14,k2_tarski(X15,X15)),k2_tarski(X15,X15)) = X15 | k2_tarski(X15,X15) = k2_tarski(X12,sK2(X13,X14,k2_tarski(X15,X15))) | sK2(X13,X14,k2_tarski(X15,X15)) = X14 | sK2(X13,X14,k2_tarski(X15,X15)) = X13 | k2_tarski(X13,X14) = k2_tarski(X15,X15)).
% 8.60/1.49  
% 8.60/1.49  cnf(u2842,axiom,
% 8.60/1.49      sK2(X0,sK2(X2,X3,k2_tarski(X1,X0)),k2_tarski(X1,X0)) = X1 | k2_tarski(X1,X0) = k2_tarski(X0,sK2(X2,X3,k2_tarski(X1,X0))) | sK2(X2,X3,k2_tarski(X1,X0)) = X3 | sK2(X2,X3,k2_tarski(X1,X0)) = X2 | k2_tarski(X1,X0) = k2_tarski(X2,X3)).
% 8.60/1.49  
% 8.60/1.49  cnf(u314,axiom,
% 8.60/1.49      sK2(X18,sK2(X19,X20,k2_tarski(X16,X17)),k2_tarski(X16,X17)) = X18 | sK2(X18,sK2(X19,X20,k2_tarski(X16,X17)),k2_tarski(X16,X17)) = X16 | sK2(X18,sK2(X19,X20,k2_tarski(X16,X17)),k2_tarski(X16,X17)) = X17 | k2_tarski(X16,X17) = k2_tarski(X18,sK2(X19,X20,k2_tarski(X16,X17))) | sK2(X19,X20,k2_tarski(X16,X17)) = X20 | sK2(X19,X20,k2_tarski(X16,X17)) = X19 | k2_tarski(X16,X17) = k2_tarski(X19,X20)).
% 8.60/1.49  
% 8.60/1.49  cnf(u314,axiom,
% 8.60/1.49      sK2(X18,sK2(X19,X20,k2_tarski(X16,X17)),k2_tarski(X16,X17)) = X18 | sK2(X18,sK2(X19,X20,k2_tarski(X16,X17)),k2_tarski(X16,X17)) = X16 | sK2(X18,sK2(X19,X20,k2_tarski(X16,X17)),k2_tarski(X16,X17)) = X17 | k2_tarski(X16,X17) = k2_tarski(X18,sK2(X19,X20,k2_tarski(X16,X17))) | sK2(X19,X20,k2_tarski(X16,X17)) = X20 | sK2(X19,X20,k2_tarski(X16,X17)) = X19 | k2_tarski(X16,X17) = k2_tarski(X19,X20)).
% 8.60/1.49  
% 8.60/1.49  cnf(u314,axiom,
% 8.60/1.49      sK2(X18,sK2(X19,X20,k2_tarski(X16,X17)),k2_tarski(X16,X17)) = X18 | sK2(X18,sK2(X19,X20,k2_tarski(X16,X17)),k2_tarski(X16,X17)) = X16 | sK2(X18,sK2(X19,X20,k2_tarski(X16,X17)),k2_tarski(X16,X17)) = X17 | k2_tarski(X16,X17) = k2_tarski(X18,sK2(X19,X20,k2_tarski(X16,X17))) | sK2(X19,X20,k2_tarski(X16,X17)) = X20 | sK2(X19,X20,k2_tarski(X16,X17)) = X19 | k2_tarski(X16,X17) = k2_tarski(X19,X20)).
% 8.60/1.49  
% 8.60/1.49  cnf(u185,axiom,
% 8.60/1.49      sK2(X0,X0,k2_tarski(X0,X1)) = X0 | sK2(X0,X0,k2_tarski(X0,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X0,X0)).
% 8.60/1.49  
% 8.60/1.49  cnf(u222,axiom,
% 8.60/1.49      sK2(X1,X1,k2_tarski(X1,X2)) = X2 | k2_tarski(X1,X1) = k2_tarski(X1,X2)).
% 8.60/1.49  
% 8.60/1.49  cnf(u185,axiom,
% 8.60/1.49      sK2(X0,X0,k2_tarski(X0,X1)) = X0 | sK2(X0,X0,k2_tarski(X0,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X0,X0)).
% 8.60/1.49  
% 8.60/1.49  cnf(u317,axiom,
% 8.60/1.49      sK2(X0,X0,k2_tarski(X1,X1)) = X0 | sK2(X0,X0,k2_tarski(X1,X1)) = X1 | k2_tarski(X0,X0) = k2_tarski(X1,X1)).
% 8.60/1.49  
% 8.60/1.49  cnf(u317,axiom,
% 8.60/1.49      sK2(X0,X0,k2_tarski(X1,X1)) = X0 | sK2(X0,X0,k2_tarski(X1,X1)) = X1 | k2_tarski(X0,X0) = k2_tarski(X1,X1)).
% 8.60/1.49  
% 8.60/1.49  cnf(u248,axiom,
% 8.60/1.49      sK2(X0,X0,k2_tarski(X1,X0)) = X1 | sK2(X0,X0,k2_tarski(X1,X0)) = X0 | k2_tarski(X0,X0) = k2_tarski(X1,X0)).
% 8.60/1.49  
% 8.60/1.49  cnf(u248,axiom,
% 8.60/1.49      sK2(X0,X0,k2_tarski(X1,X0)) = X1 | sK2(X0,X0,k2_tarski(X1,X0)) = X0 | k2_tarski(X0,X0) = k2_tarski(X1,X0)).
% 8.60/1.49  
% 8.60/1.49  cnf(u289,axiom,
% 8.60/1.49      sK2(X0,X0,k2_tarski(X1,X0)) = X1 | k2_tarski(X0,X0) = k2_tarski(X1,X0)).
% 8.60/1.49  
% 8.60/1.49  cnf(u135,axiom,
% 8.60/1.49      sK2(X0,X0,k2_tarski(X1,X2)) = X0 | sK2(X0,X0,k2_tarski(X1,X2)) = X1 | sK2(X0,X0,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X0) = k2_tarski(X1,X2)).
% 8.60/1.49  
% 8.60/1.49  cnf(u135,axiom,
% 8.60/1.49      sK2(X0,X0,k2_tarski(X1,X2)) = X0 | sK2(X0,X0,k2_tarski(X1,X2)) = X1 | sK2(X0,X0,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X0) = k2_tarski(X1,X2)).
% 8.60/1.49  
% 8.60/1.49  cnf(u135,axiom,
% 8.60/1.49      sK2(X0,X0,k2_tarski(X1,X2)) = X0 | sK2(X0,X0,k2_tarski(X1,X2)) = X1 | sK2(X0,X0,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X0) = k2_tarski(X1,X2)).
% 8.60/1.49  
% 8.60/1.49  cnf(u1646,axiom,
% 8.60/1.49      sK2(X0,X1,k2_tarski(X0,X0)) = X1 | sK2(X0,X1,k2_tarski(X0,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X0,X0)).
% 8.60/1.49  
% 8.60/1.49  cnf(u1646,axiom,
% 8.60/1.49      sK2(X0,X1,k2_tarski(X0,X0)) = X1 | sK2(X0,X1,k2_tarski(X0,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X0,X0)).
% 8.60/1.49  
% 8.60/1.49  cnf(u1714,axiom,
% 8.60/1.49      sK2(X0,X1,k2_tarski(X0,X0)) = X1 | k2_tarski(X0,X1) = k2_tarski(X0,X0)).
% 8.60/1.49  
% 8.60/1.49  cnf(u219,axiom,
% 8.60/1.49      sK2(X0,X1,k2_tarski(X0,X2)) = X1 | sK2(X0,X1,k2_tarski(X0,X2)) = X0 | sK2(X0,X1,k2_tarski(X0,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 8.60/1.49  
% 8.60/1.49  cnf(u1965,axiom,
% 8.60/1.49      sK2(X2,X4,k2_tarski(X2,X3)) = X4 | sK2(X2,X4,k2_tarski(X2,X3)) = X3 | k2_tarski(X2,X3) = k2_tarski(X2,X4)).
% 8.60/1.49  
% 8.60/1.49  cnf(u219,axiom,
% 8.60/1.49      sK2(X0,X1,k2_tarski(X0,X2)) = X1 | sK2(X0,X1,k2_tarski(X0,X2)) = X0 | sK2(X0,X1,k2_tarski(X0,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 8.60/1.49  
% 8.60/1.49  cnf(u219,axiom,
% 8.60/1.49      sK2(X0,X1,k2_tarski(X0,X2)) = X1 | sK2(X0,X1,k2_tarski(X0,X2)) = X0 | sK2(X0,X1,k2_tarski(X0,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 8.60/1.49  
% 8.60/1.49  cnf(u1965,axiom,
% 8.60/1.49      sK2(X2,X4,k2_tarski(X2,X3)) = X4 | sK2(X2,X4,k2_tarski(X2,X3)) = X3 | k2_tarski(X2,X3) = k2_tarski(X2,X4)).
% 8.60/1.49  
% 8.60/1.49  cnf(u903,axiom,
% 8.60/1.49      sK2(X0,X1,k2_tarski(X1,X1)) = X0 | sK2(X0,X1,k2_tarski(X1,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X1,X1)).
% 8.60/1.49  
% 8.60/1.49  cnf(u903,axiom,
% 8.60/1.49      sK2(X0,X1,k2_tarski(X1,X1)) = X0 | sK2(X0,X1,k2_tarski(X1,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X1,X1)).
% 8.60/1.49  
% 8.60/1.49  cnf(u954,axiom,
% 8.60/1.49      sK2(X1,X0,k2_tarski(X0,X0)) = X1 | k2_tarski(X0,X0) = k2_tarski(X1,X0)).
% 8.60/1.49  
% 8.60/1.49  cnf(u667,axiom,
% 8.60/1.49      sK2(X0,X1,k2_tarski(X1,X0)) = X1 | sK2(X0,X1,k2_tarski(X1,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X1,X0)).
% 8.60/1.49  
% 8.60/1.49  cnf(u667,axiom,
% 8.60/1.49      sK2(X0,X1,k2_tarski(X1,X0)) = X1 | sK2(X0,X1,k2_tarski(X1,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X1,X0)).
% 8.60/1.49  
% 8.60/1.49  cnf(u800,axiom,
% 8.60/1.49      sK2(X1,X0,k2_tarski(X0,X1)) = X0 | k2_tarski(X0,X1) = k2_tarski(X1,X0)).
% 8.60/1.49  
% 8.60/1.49  cnf(u136,axiom,
% 8.60/1.49      sK2(X0,X1,k2_tarski(X1,X2)) = X0 | sK2(X0,X1,k2_tarski(X1,X2)) = X1 | sK2(X0,X1,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 8.60/1.49  
% 8.60/1.49  cnf(u1784,axiom,
% 8.60/1.49      sK2(X4,X2,k2_tarski(X2,X3)) = X4 | sK2(X4,X2,k2_tarski(X2,X3)) = X3 | k2_tarski(X2,X3) = k2_tarski(X4,X2)).
% 8.60/1.49  
% 8.60/1.49  cnf(u136,axiom,
% 8.60/1.49      sK2(X0,X1,k2_tarski(X1,X2)) = X0 | sK2(X0,X1,k2_tarski(X1,X2)) = X1 | sK2(X0,X1,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 8.60/1.49  
% 8.60/1.49  cnf(u136,axiom,
% 8.60/1.49      sK2(X0,X1,k2_tarski(X1,X2)) = X0 | sK2(X0,X1,k2_tarski(X1,X2)) = X1 | sK2(X0,X1,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 8.60/1.49  
% 8.60/1.49  cnf(u1784,axiom,
% 8.60/1.49      sK2(X4,X2,k2_tarski(X2,X3)) = X4 | sK2(X4,X2,k2_tarski(X2,X3)) = X3 | k2_tarski(X2,X3) = k2_tarski(X4,X2)).
% 8.60/1.49  
% 8.60/1.49  cnf(u86,axiom,
% 8.60/1.49      sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | sK2(X0,X1,k2_tarski(X2,X3)) = X2 | sK2(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 8.60/1.49  
% 8.60/1.49  cnf(u86,axiom,
% 8.60/1.49      sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | sK2(X0,X1,k2_tarski(X2,X3)) = X2 | sK2(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 8.60/1.49  
% 8.60/1.49  cnf(u86,axiom,
% 8.60/1.49      sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | sK2(X0,X1,k2_tarski(X2,X3)) = X2 | sK2(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 8.60/1.49  
% 8.60/1.49  cnf(u86,axiom,
% 8.60/1.49      sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | sK2(X0,X1,k2_tarski(X2,X3)) = X2 | sK2(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 8.60/1.49  
% 8.60/1.49  cnf(u246,axiom,
% 8.60/1.49      sK2(X0,X1,k2_tarski(X2,X2)) = X1 | sK2(X0,X1,k2_tarski(X2,X2)) = X0 | sK2(X0,X1,k2_tarski(X2,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 8.60/1.49  
% 8.60/1.49  cnf(u246,axiom,
% 8.60/1.49      sK2(X0,X1,k2_tarski(X2,X2)) = X1 | sK2(X0,X1,k2_tarski(X2,X2)) = X0 | sK2(X0,X1,k2_tarski(X2,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 8.60/1.49  
% 8.60/1.49  cnf(u246,axiom,
% 8.60/1.49      sK2(X0,X1,k2_tarski(X2,X2)) = X1 | sK2(X0,X1,k2_tarski(X2,X2)) = X0 | sK2(X0,X1,k2_tarski(X2,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 8.60/1.49  
% 8.60/1.49  cnf(u184,axiom,
% 8.60/1.49      sK2(X0,X1,k2_tarski(X2,X1)) = X0 | sK2(X0,X1,k2_tarski(X2,X1)) = X2 | sK2(X0,X1,k2_tarski(X2,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 8.60/1.49  
% 8.60/1.49  cnf(u184,axiom,
% 8.60/1.49      sK2(X0,X1,k2_tarski(X2,X1)) = X0 | sK2(X0,X1,k2_tarski(X2,X1)) = X2 | sK2(X0,X1,k2_tarski(X2,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 8.60/1.49  
% 8.60/1.49  cnf(u1930,axiom,
% 8.60/1.49      sK2(X2,X1,k2_tarski(X0,X1)) = X2 | sK2(X2,X1,k2_tarski(X0,X1)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 8.60/1.49  
% 8.60/1.49  cnf(u184,axiom,
% 8.60/1.49      sK2(X0,X1,k2_tarski(X2,X1)) = X0 | sK2(X0,X1,k2_tarski(X2,X1)) = X2 | sK2(X0,X1,k2_tarski(X2,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 8.60/1.49  
% 8.60/1.49  cnf(u1930,axiom,
% 8.60/1.49      sK2(X2,X1,k2_tarski(X0,X1)) = X2 | sK2(X2,X1,k2_tarski(X0,X1)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 8.60/1.49  
% 8.60/1.49  cnf(u223,axiom,
% 8.60/1.49      sK2(X0,X1,k2_tarski(X2,X0)) = X1 | sK2(X0,X1,k2_tarski(X2,X0)) = X2 | sK2(X0,X1,k2_tarski(X2,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 8.60/1.49  
% 8.60/1.49  cnf(u223,axiom,
% 8.60/1.49      sK2(X0,X1,k2_tarski(X2,X0)) = X1 | sK2(X0,X1,k2_tarski(X2,X0)) = X2 | sK2(X0,X1,k2_tarski(X2,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 8.60/1.49  
% 8.60/1.49  cnf(u2100,axiom,
% 8.60/1.49      sK2(X0,X1,k2_tarski(X2,X0)) = X1 | sK2(X0,X1,k2_tarski(X2,X0)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 8.60/1.49  
% 8.60/1.49  cnf(u223,axiom,
% 8.60/1.49      sK2(X0,X1,k2_tarski(X2,X0)) = X1 | sK2(X0,X1,k2_tarski(X2,X0)) = X2 | sK2(X0,X1,k2_tarski(X2,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 8.60/1.49  
% 8.60/1.49  cnf(u2100,axiom,
% 8.60/1.49      sK2(X0,X1,k2_tarski(X2,X0)) = X1 | sK2(X0,X1,k2_tarski(X2,X0)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 8.60/1.49  
% 8.60/1.49  cnf(u79,negated_conjecture,
% 8.60/1.49      k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)).
% 8.60/1.49  
% 8.60/1.49  cnf(u4839,axiom,
% 8.60/1.49      X2 != X3 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X4,X5,k2_tarski(X2,X3)),k2_tarski(X2,X3)) = X2 | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X4,X5,k2_tarski(X2,X3))) | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X3) | sK2(X4,X5,k2_tarski(X2,X3)) = X5 | sK2(X4,X5,k2_tarski(X2,X3)) = X4 | k2_tarski(X2,X3) = k2_tarski(X4,X5)).
% 8.60/1.49  
% 8.60/1.49  cnf(u4838,axiom,
% 8.60/1.49      X2 != X3 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X4,X5,k2_tarski(X2,X3)),k2_tarski(X2,X3)) = X3 | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X4,X5,k2_tarski(X2,X3))) | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X3) | sK2(X4,X5,k2_tarski(X2,X3)) = X5 | sK2(X4,X5,k2_tarski(X2,X3)) = X4 | k2_tarski(X2,X3) = k2_tarski(X4,X5)).
% 8.60/1.49  
% 8.60/1.49  cnf(u4277,axiom,
% 8.60/1.49      X2 != X3 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X0,X1,k2_tarski(X2,X3)),k2_tarski(X2,X3)) = X2 | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X0,X1,k2_tarski(X2,X3))) | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 8.60/1.49  
% 8.60/1.49  cnf(u4276,axiom,
% 8.60/1.49      X2 != X3 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X0,X1,k2_tarski(X2,X3)),k2_tarski(X2,X3)) = X3 | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X0,X1,k2_tarski(X2,X3))) | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 8.60/1.49  
% 8.60/1.49  cnf(u3858,axiom,
% 8.60/1.49      X0 != X3 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X3)),k2_tarski(X3,X3)) = X0 | k2_tarski(X3,X3) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X3))) | sK2(X1,X2,k2_tarski(X3,X3)) = X2 | sK2(X1,X2,k2_tarski(X3,X3)) = X1 | k2_tarski(X1,X2) = k2_tarski(X3,X3)).
% 8.60/1.49  
% 8.60/1.49  cnf(u3857,axiom,
% 8.60/1.49      X0 != X3 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X3)),k2_tarski(X3,X3)) = X3 | k2_tarski(X3,X3) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X3))) | sK2(X1,X2,k2_tarski(X3,X3)) = X2 | sK2(X1,X2,k2_tarski(X3,X3)) = X1 | k2_tarski(X1,X2) = k2_tarski(X3,X3)).
% 8.60/1.49  
% 8.60/1.49  cnf(u3581,axiom,
% 8.60/1.49      X2 != X3 | sK2(sK2(X0,X1,k2_tarski(X2,X2)),X3,k2_tarski(X2,X2)) = X3 | k2_tarski(X2,X2) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X2)),X3) | sK2(X0,X1,k2_tarski(X2,X2)) = X1 | sK2(X0,X1,k2_tarski(X2,X2)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 8.60/1.49  
% 8.60/1.49  cnf(u3580,axiom,
% 8.60/1.49      X2 != X3 | sK2(sK2(X0,X1,k2_tarski(X2,X2)),X3,k2_tarski(X2,X2)) = X2 | k2_tarski(X2,X2) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X2)),X3) | sK2(X0,X1,k2_tarski(X2,X2)) = X1 | sK2(X0,X1,k2_tarski(X2,X2)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 8.60/1.49  
% 8.60/1.49  cnf(u3035,axiom,
% 8.60/1.49      X138 != X139 | k2_tarski(X138,X139) = k2_tarski(X139,sK2(X136,X137,k2_tarski(X138,X139))) | ~r2_hidden(X139,k2_tarski(X138,X139)) | sK2(X136,X137,k2_tarski(X138,X139)) = X137 | sK2(X136,X137,k2_tarski(X138,X139)) = X136 | k2_tarski(X136,X137) = k2_tarski(X138,X139)).
% 8.60/1.49  
% 8.60/1.49  cnf(u2776,axiom,
% 8.60/1.49      X127 != X128 | k2_tarski(X127,X128) = k2_tarski(X127,sK2(X125,X126,k2_tarski(X127,X128))) | ~r2_hidden(X127,k2_tarski(X127,X128)) | sK2(X125,X126,k2_tarski(X127,X128)) = X126 | sK2(X125,X126,k2_tarski(X127,X128)) = X125 | k2_tarski(X125,X126) = k2_tarski(X127,X128)).
% 8.60/1.49  
% 8.60/1.49  cnf(u2404,axiom,
% 8.60/1.49      X99 != X100 | k2_tarski(X99,X100) = k2_tarski(X101,X99) | ~r2_hidden(X99,k2_tarski(X101,X99)) | sK2(X99,X100,k2_tarski(X101,X99)) = X101).
% 8.60/1.49  
% 8.60/1.49  cnf(u2389,axiom,
% 8.60/1.49      X99 != X101 | k2_tarski(X99,X100) = k2_tarski(X101,X99) | ~r2_hidden(X99,k2_tarski(X101,X99)) | sK2(X99,X100,k2_tarski(X101,X99)) = X100).
% 8.60/1.49  
% 8.60/1.49  cnf(u2387,axiom,
% 8.60/1.49      X1 != X2 | sK2(X0,X1,k2_tarski(X2,X0)) = X1 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 8.60/1.49  
% 8.60/1.49  cnf(u2386,axiom,
% 8.60/1.49      X1 != X2 | sK2(X0,X1,k2_tarski(X2,X0)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 8.60/1.49  
% 8.60/1.49  cnf(u2232,axiom,
% 8.60/1.49      X92 != X93 | k2_tarski(X92,X93) = k2_tarski(X92,X94) | ~r2_hidden(X92,k2_tarski(X92,X94)) | sK2(X92,X93,k2_tarski(X92,X94)) = X94).
% 8.60/1.49  
% 8.60/1.49  cnf(u2217,axiom,
% 8.60/1.49      X92 != X94 | k2_tarski(X92,X93) = k2_tarski(X92,X94) | ~r2_hidden(X92,k2_tarski(X92,X94)) | sK2(X92,X93,k2_tarski(X92,X94)) = X93).
% 8.60/1.49  
% 8.60/1.49  cnf(u2215,axiom,
% 8.60/1.49      X1 != X2 | sK2(X0,X1,k2_tarski(X0,X2)) = X1 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 8.60/1.49  
% 8.60/1.49  cnf(u2214,axiom,
% 8.60/1.49      X1 != X2 | sK2(X0,X1,k2_tarski(X0,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 8.60/1.49  
% 8.60/1.49  cnf(u2086,axiom,
% 8.60/1.49      X91 != X92 | k2_tarski(X93,X92) = k2_tarski(X91,X92) | ~r2_hidden(X92,k2_tarski(X93,X92)) | sK2(X91,X92,k2_tarski(X93,X92)) = X93).
% 8.60/1.49  
% 8.60/1.49  cnf(u2072,axiom,
% 8.60/1.49      X92 != X93 | k2_tarski(X93,X92) = k2_tarski(X91,X92) | ~r2_hidden(X92,k2_tarski(X93,X92)) | sK2(X91,X92,k2_tarski(X93,X92)) = X91).
% 8.60/1.49  
% 8.60/1.49  cnf(u2071,axiom,
% 8.60/1.49      X0 != X2 | sK2(X0,X1,k2_tarski(X2,X1)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 8.60/1.49  
% 8.60/1.49  cnf(u2070,axiom,
% 8.60/1.49      X0 != X2 | sK2(X0,X1,k2_tarski(X2,X1)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 8.60/1.49  
% 8.60/1.49  cnf(u1909,axiom,
% 8.60/1.49      X90 != X91 | k2_tarski(X90,X91) = k2_tarski(X91,X92) | ~r2_hidden(X91,k2_tarski(X91,X92)) | sK2(X90,X91,k2_tarski(X91,X92)) = X92).
% 8.60/1.49  
% 8.60/1.49  cnf(u1895,axiom,
% 8.60/1.49      X91 != X92 | k2_tarski(X90,X91) = k2_tarski(X91,X92) | ~r2_hidden(X91,k2_tarski(X91,X92)) | sK2(X90,X91,k2_tarski(X91,X92)) = X90).
% 8.60/1.49  
% 8.60/1.49  cnf(u1894,axiom,
% 8.60/1.49      X0 != X2 | sK2(X0,X1,k2_tarski(X1,X2)) = X0 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 8.60/1.49  
% 8.60/1.49  cnf(u1893,axiom,
% 8.60/1.49      X0 != X2 | sK2(X0,X1,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 8.60/1.49  
% 8.60/1.49  cnf(u1756,axiom,
% 8.60/1.49      X62 != X63 | k2_tarski(X62,X62) = k2_tarski(X62,X63) | ~r2_hidden(X62,k2_tarski(X62,X62))).
% 8.60/1.49  
% 8.60/1.49  cnf(u1700,axiom,
% 8.60/1.49      X0 != X1 | sK2(X0,X1,k2_tarski(X0,X0)) = X1 | k2_tarski(X0,X1) = k2_tarski(X0,X0)).
% 8.60/1.49  
% 8.60/1.49  cnf(u1699,axiom,
% 8.60/1.49      X0 != X1 | sK2(X0,X1,k2_tarski(X0,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X0,X0)).
% 8.60/1.49  
% 8.60/1.49  cnf(u1545,axiom,
% 8.60/1.49      X3 != X4 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X0 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X3 | k2_tarski(X3,X4) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X4))) | sK2(X1,X2,k2_tarski(X3,X4)) = X2 | sK2(X1,X2,k2_tarski(X3,X4)) = X1 | k2_tarski(X1,X2) = k2_tarski(X3,X4)).
% 8.60/1.49  
% 8.60/1.49  cnf(u1544,axiom,
% 8.60/1.49      X0 != X4 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X0 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X3 | k2_tarski(X3,X4) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X4))) | sK2(X1,X2,k2_tarski(X3,X4)) = X2 | sK2(X1,X2,k2_tarski(X3,X4)) = X1 | k2_tarski(X1,X2) = k2_tarski(X3,X4)).
% 8.60/1.49  
% 8.60/1.49  cnf(u1543,axiom,
% 8.60/1.49      X3 != X4 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X0 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X4 | k2_tarski(X3,X4) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X4))) | sK2(X1,X2,k2_tarski(X3,X4)) = X2 | sK2(X1,X2,k2_tarski(X3,X4)) = X1 | k2_tarski(X1,X2) = k2_tarski(X3,X4)).
% 8.60/1.49  
% 8.60/1.49  cnf(u1542,axiom,
% 8.60/1.49      X0 != X3 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X0 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X4 | k2_tarski(X3,X4) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X4))) | sK2(X1,X2,k2_tarski(X3,X4)) = X2 | sK2(X1,X2,k2_tarski(X3,X4)) = X1 | k2_tarski(X1,X2) = k2_tarski(X3,X4)).
% 8.60/1.49  
% 8.60/1.49  cnf(u1541,axiom,
% 8.60/1.49      X0 != X4 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X3 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X4 | k2_tarski(X3,X4) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X4))) | sK2(X1,X2,k2_tarski(X3,X4)) = X2 | sK2(X1,X2,k2_tarski(X3,X4)) = X1 | k2_tarski(X1,X2) = k2_tarski(X3,X4)).
% 8.60/1.49  
% 8.60/1.49  cnf(u1540,axiom,
% 8.60/1.49      X0 != X3 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X3 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X4 | k2_tarski(X3,X4) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X4))) | sK2(X1,X2,k2_tarski(X3,X4)) = X2 | sK2(X1,X2,k2_tarski(X3,X4)) = X1 | k2_tarski(X1,X2) = k2_tarski(X3,X4)).
% 8.60/1.49  
% 8.60/1.49  cnf(u1219,axiom,
% 8.60/1.49      X2 != X3 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X4 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X2 | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),X4) | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 8.60/1.49  
% 8.60/1.49  cnf(u1218,axiom,
% 8.60/1.49      X3 != X4 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X4 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X2 | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),X4) | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 8.60/1.49  
% 8.60/1.49  cnf(u1217,axiom,
% 8.60/1.49      X2 != X3 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X4 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X3 | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),X4) | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 8.60/1.49  
% 8.60/1.49  cnf(u1216,axiom,
% 8.60/1.49      X2 != X4 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X4 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X3 | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),X4) | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 8.60/1.49  
% 8.60/1.49  cnf(u1215,axiom,
% 8.60/1.49      X3 != X4 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X2 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X3 | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),X4) | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 8.60/1.49  
% 8.60/1.49  cnf(u1214,axiom,
% 8.60/1.49      X2 != X4 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X2 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X3 | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),X4) | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 8.60/1.49  
% 8.60/1.49  cnf(u979,axiom,
% 8.60/1.49      X43 != X44 | k2_tarski(X44,X44) = k2_tarski(X43,X44) | ~r2_hidden(X44,k2_tarski(X44,X44))).
% 8.60/1.49  
% 8.60/1.49  cnf(u941,axiom,
% 8.60/1.49      X0 != X1 | sK2(X0,X1,k2_tarski(X1,X1)) = X0 | k2_tarski(X0,X1) = k2_tarski(X1,X1)).
% 8.60/1.49  
% 8.60/1.49  cnf(u940,axiom,
% 8.60/1.49      X0 != X1 | sK2(X0,X1,k2_tarski(X1,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X1,X1)).
% 8.60/1.49  
% 8.60/1.49  cnf(u788,axiom,
% 8.60/1.49      X0 != X2 | sK2(X0,X1,k2_tarski(X2,X2)) = X1 | sK2(X0,X1,k2_tarski(X2,X2)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 8.60/1.49  
% 8.60/1.49  cnf(u787,axiom,
% 8.60/1.49      X1 != X2 | sK2(X0,X1,k2_tarski(X2,X2)) = X1 | sK2(X0,X1,k2_tarski(X2,X2)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 8.60/1.49  
% 8.60/1.49  cnf(u786,axiom,
% 8.60/1.49      X0 != X2 | sK2(X0,X1,k2_tarski(X2,X2)) = X1 | sK2(X0,X1,k2_tarski(X2,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 8.60/1.49  
% 8.60/1.49  cnf(u785,axiom,
% 8.60/1.49      X0 != X1 | sK2(X0,X1,k2_tarski(X2,X2)) = X1 | sK2(X0,X1,k2_tarski(X2,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 8.60/1.49  
% 8.60/1.49  cnf(u784,axiom,
% 8.60/1.49      X1 != X2 | sK2(X0,X1,k2_tarski(X2,X2)) = X0 | sK2(X0,X1,k2_tarski(X2,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 8.60/1.49  
% 8.60/1.49  cnf(u783,axiom,
% 8.60/1.49      X0 != X1 | sK2(X0,X1,k2_tarski(X2,X2)) = X0 | sK2(X0,X1,k2_tarski(X2,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 8.60/1.49  
% 8.60/1.49  cnf(u697,axiom,
% 8.60/1.49      X0 != X1 | sK2(X0,X1,k2_tarski(X1,X0)) = X1 | k2_tarski(X0,X1) = k2_tarski(X1,X0)).
% 8.60/1.49  
% 8.60/1.49  cnf(u696,axiom,
% 8.60/1.49      X0 != X1 | sK2(X0,X1,k2_tarski(X1,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X1,X0)).
% 8.60/1.49  
% 8.60/1.49  cnf(u655,axiom,
% 8.60/1.49      X0 != X2 | sK2(X0,X1,k2_tarski(X2,X0)) = X1 | sK2(X0,X1,k2_tarski(X2,X0)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 8.60/1.49  
% 8.60/1.49  cnf(u654,axiom,
% 8.60/1.49      X0 != X1 | sK2(X0,X1,k2_tarski(X2,X0)) = X1 | sK2(X0,X1,k2_tarski(X2,X0)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 8.60/1.49  
% 8.60/1.49  cnf(u653,axiom,
% 8.60/1.49      X0 != X2 | sK2(X0,X1,k2_tarski(X2,X0)) = X1 | sK2(X0,X1,k2_tarski(X2,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 8.60/1.49  
% 8.60/1.49  cnf(u652,axiom,
% 8.60/1.49      X1 != X2 | sK2(X0,X1,k2_tarski(X2,X0)) = X1 | sK2(X0,X1,k2_tarski(X2,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 8.60/1.49  
% 8.60/1.49  cnf(u651,axiom,
% 8.60/1.49      X0 != X1 | sK2(X0,X1,k2_tarski(X2,X0)) = X2 | sK2(X0,X1,k2_tarski(X2,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 8.60/1.49  
% 8.60/1.49  cnf(u650,axiom,
% 8.60/1.49      X1 != X2 | sK2(X0,X1,k2_tarski(X2,X0)) = X2 | sK2(X0,X1,k2_tarski(X2,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 8.60/1.49  
% 8.60/1.49  cnf(u564,axiom,
% 8.60/1.49      X0 != X2 | sK2(X0,X1,k2_tarski(X0,X2)) = X1 | sK2(X0,X1,k2_tarski(X0,X2)) = X0 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 8.60/1.49  
% 8.60/1.49  cnf(u563,axiom,
% 8.60/1.49      X1 != X2 | sK2(X0,X1,k2_tarski(X0,X2)) = X1 | sK2(X0,X1,k2_tarski(X0,X2)) = X0 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 8.60/1.49  
% 8.60/1.49  cnf(u562,axiom,
% 8.60/1.49      X0 != X2 | sK2(X0,X1,k2_tarski(X0,X2)) = X1 | sK2(X0,X1,k2_tarski(X0,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 8.60/1.49  
% 8.60/1.49  cnf(u561,axiom,
% 8.60/1.49      X0 != X1 | sK2(X0,X1,k2_tarski(X0,X2)) = X1 | sK2(X0,X1,k2_tarski(X0,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 8.60/1.49  
% 8.60/1.49  cnf(u560,axiom,
% 8.60/1.49      X1 != X2 | sK2(X0,X1,k2_tarski(X0,X2)) = X0 | sK2(X0,X1,k2_tarski(X0,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 8.60/1.49  
% 8.60/1.49  cnf(u559,axiom,
% 8.60/1.49      X0 != X1 | sK2(X0,X1,k2_tarski(X0,X2)) = X0 | sK2(X0,X1,k2_tarski(X0,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 8.60/1.49  
% 8.60/1.49  cnf(u482,axiom,
% 8.60/1.49      X1 != X2 | sK2(X0,X1,k2_tarski(X2,X1)) = X0 | sK2(X0,X1,k2_tarski(X2,X1)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 8.60/1.49  
% 8.60/1.49  cnf(u481,axiom,
% 8.60/1.49      X0 != X1 | sK2(X0,X1,k2_tarski(X2,X1)) = X0 | sK2(X0,X1,k2_tarski(X2,X1)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 8.60/1.49  
% 8.60/1.49  cnf(u480,axiom,
% 8.60/1.49      X1 != X2 | sK2(X0,X1,k2_tarski(X2,X1)) = X0 | sK2(X0,X1,k2_tarski(X2,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 8.60/1.49  
% 8.60/1.49  cnf(u479,axiom,
% 8.60/1.49      X0 != X2 | sK2(X0,X1,k2_tarski(X2,X1)) = X0 | sK2(X0,X1,k2_tarski(X2,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 8.60/1.49  
% 8.60/1.49  cnf(u478,axiom,
% 8.60/1.49      X0 != X1 | sK2(X0,X1,k2_tarski(X2,X1)) = X2 | sK2(X0,X1,k2_tarski(X2,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 8.60/1.49  
% 8.60/1.49  cnf(u477,axiom,
% 8.60/1.49      X0 != X2 | sK2(X0,X1,k2_tarski(X2,X1)) = X2 | sK2(X0,X1,k2_tarski(X2,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 8.60/1.49  
% 8.60/1.49  cnf(u405,axiom,
% 8.60/1.49      X1 != X2 | sK2(X0,X1,k2_tarski(X1,X2)) = X0 | sK2(X0,X1,k2_tarski(X1,X2)) = X1 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 8.60/1.49  
% 8.60/1.49  cnf(u404,axiom,
% 8.60/1.49      X0 != X2 | sK2(X0,X1,k2_tarski(X1,X2)) = X0 | sK2(X0,X1,k2_tarski(X1,X2)) = X1 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 8.60/1.49  
% 8.60/1.49  cnf(u403,axiom,
% 8.60/1.49      X1 != X2 | sK2(X0,X1,k2_tarski(X1,X2)) = X0 | sK2(X0,X1,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 8.60/1.49  
% 8.60/1.49  cnf(u402,axiom,
% 8.60/1.49      X0 != X1 | sK2(X0,X1,k2_tarski(X1,X2)) = X0 | sK2(X0,X1,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 8.60/1.49  
% 8.60/1.49  cnf(u401,axiom,
% 8.60/1.49      X0 != X2 | sK2(X0,X1,k2_tarski(X1,X2)) = X1 | sK2(X0,X1,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 8.60/1.49  
% 8.60/1.49  cnf(u400,axiom,
% 8.60/1.49      X0 != X1 | sK2(X0,X1,k2_tarski(X1,X2)) = X1 | sK2(X0,X1,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 8.60/1.49  
% 8.60/1.49  cnf(u341,axiom,
% 8.60/1.49      X0 != X1 | sK2(X0,X0,k2_tarski(X1,X1)) = X0 | k2_tarski(X0,X0) = k2_tarski(X1,X1)).
% 8.60/1.49  
% 8.60/1.49  cnf(u340,axiom,
% 8.60/1.49      X0 != X1 | sK2(X0,X0,k2_tarski(X1,X1)) = X1 | k2_tarski(X0,X0) = k2_tarski(X1,X1)).
% 8.60/1.49  
% 8.60/1.49  cnf(u306,axiom,
% 8.60/1.49      X12 != X13 | k2_tarski(X12,X12) = k2_tarski(X13,X12) | ~r2_hidden(X12,k2_tarski(X13,X12))).
% 8.60/1.49  
% 8.60/1.49  cnf(u273,axiom,
% 8.60/1.49      X0 != X1 | sK2(X0,X0,k2_tarski(X1,X0)) = X1 | k2_tarski(X0,X0) = k2_tarski(X1,X0)).
% 8.60/1.49  
% 8.60/1.49  cnf(u272,axiom,
% 8.60/1.49      X0 != X1 | sK2(X0,X0,k2_tarski(X1,X0)) = X0 | k2_tarski(X0,X0) = k2_tarski(X1,X0)).
% 8.60/1.49  
% 8.60/1.49  cnf(u239,axiom,
% 8.60/1.49      X12 != X13 | k2_tarski(X12,X12) = k2_tarski(X12,X13) | ~r2_hidden(X12,k2_tarski(X12,X13))).
% 8.60/1.49  
% 8.60/1.49  cnf(u209,axiom,
% 8.60/1.49      X0 != X1 | sK2(X0,X0,k2_tarski(X0,X1)) = X0 | k2_tarski(X0,X1) = k2_tarski(X0,X0)).
% 8.60/1.49  
% 8.60/1.49  cnf(u208,axiom,
% 8.60/1.49      X0 != X1 | sK2(X0,X0,k2_tarski(X0,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X0,X0)).
% 8.60/1.49  
% 8.60/1.49  cnf(u173,axiom,
% 8.60/1.49      X1 != X2 | sK2(X0,X0,k2_tarski(X1,X2)) = X0 | sK2(X0,X0,k2_tarski(X1,X2)) = X1 | k2_tarski(X0,X0) = k2_tarski(X1,X2)).
% 8.60/1.49  
% 8.60/1.49  cnf(u172,axiom,
% 8.60/1.49      X0 != X2 | sK2(X0,X0,k2_tarski(X1,X2)) = X0 | sK2(X0,X0,k2_tarski(X1,X2)) = X1 | k2_tarski(X0,X0) = k2_tarski(X1,X2)).
% 8.60/1.49  
% 8.60/1.49  cnf(u171,axiom,
% 8.60/1.49      X1 != X2 | sK2(X0,X0,k2_tarski(X1,X2)) = X0 | sK2(X0,X0,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X0) = k2_tarski(X1,X2)).
% 8.60/1.49  
% 8.60/1.49  cnf(u170,axiom,
% 8.60/1.49      X0 != X1 | sK2(X0,X0,k2_tarski(X1,X2)) = X0 | sK2(X0,X0,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X0) = k2_tarski(X1,X2)).
% 8.60/1.49  
% 8.60/1.49  cnf(u169,axiom,
% 8.60/1.49      X0 != X2 | sK2(X0,X0,k2_tarski(X1,X2)) = X1 | sK2(X0,X0,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X0) = k2_tarski(X1,X2)).
% 8.60/1.49  
% 8.60/1.49  cnf(u168,axiom,
% 8.60/1.49      X0 != X1 | sK2(X0,X0,k2_tarski(X1,X2)) = X1 | sK2(X0,X0,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X0) = k2_tarski(X1,X2)).
% 8.60/1.49  
% 8.60/1.49  cnf(u122,axiom,
% 8.60/1.49      X2 != X3 | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | sK2(X0,X1,k2_tarski(X2,X3)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 8.60/1.49  
% 8.60/1.49  cnf(u121,axiom,
% 8.60/1.49      X0 != X3 | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | sK2(X0,X1,k2_tarski(X2,X3)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 8.60/1.49  
% 8.60/1.49  cnf(u120,axiom,
% 8.60/1.49      X1 != X3 | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | sK2(X0,X1,k2_tarski(X2,X3)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 8.60/1.49  
% 8.60/1.49  cnf(u119,axiom,
% 8.60/1.49      X2 != X3 | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | sK2(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 8.60/1.49  
% 8.60/1.49  cnf(u118,axiom,
% 8.60/1.49      X0 != X2 | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | sK2(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 8.60/1.49  
% 8.60/1.49  cnf(u117,axiom,
% 8.60/1.49      X1 != X2 | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | sK2(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 8.60/1.49  
% 8.60/1.49  cnf(u116,axiom,
% 8.60/1.49      X0 != X3 | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X2 | sK2(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 8.60/1.49  
% 8.60/1.49  cnf(u115,axiom,
% 8.60/1.49      X0 != X2 | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X2 | sK2(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 8.60/1.49  
% 8.60/1.49  cnf(u114,axiom,
% 8.60/1.49      X0 != X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X2 | sK2(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 8.60/1.49  
% 8.60/1.49  cnf(u113,axiom,
% 8.60/1.49      X1 != X3 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | sK2(X0,X1,k2_tarski(X2,X3)) = X2 | sK2(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 8.60/1.49  
% 8.60/1.49  cnf(u112,axiom,
% 8.60/1.49      X1 != X2 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | sK2(X0,X1,k2_tarski(X2,X3)) = X2 | sK2(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 8.60/1.49  
% 8.60/1.49  cnf(u111,axiom,
% 8.60/1.49      X0 != X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | sK2(X0,X1,k2_tarski(X2,X3)) = X2 | sK2(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 8.60/1.49  
% 8.60/1.49  cnf(u81,negated_conjecture,
% 8.60/1.49      sK1 != k2_yellow_0(sK0,k2_tarski(sK1,sK1)) | sK1 != k1_yellow_0(sK0,k2_tarski(sK1,sK1))).
% 8.60/1.49  
% 8.60/1.49  cnf(u3598,axiom,
% 8.60/1.49      sK2(X153,X154,k2_tarski(X155,X155)) != X156 | k2_tarski(X155,X155) = k2_tarski(sK2(X153,X154,k2_tarski(X155,X155)),X156) | ~r2_hidden(sK2(X153,X154,k2_tarski(X155,X155)),k2_tarski(X155,X155)) | sK2(sK2(X153,X154,k2_tarski(X155,X155)),X156,k2_tarski(X155,X155)) = X155 | sK2(X153,X154,k2_tarski(X155,X155)) = X154 | sK2(X153,X154,k2_tarski(X155,X155)) = X153 | k2_tarski(X155,X155) = k2_tarski(X153,X154)).
% 8.60/1.49  
% 8.60/1.49  cnf(u3877,axiom,
% 8.60/1.49      sK2(X168,X169,k2_tarski(X170,X170)) != X167 | k2_tarski(X170,X170) = k2_tarski(X167,sK2(X168,X169,k2_tarski(X170,X170))) | ~r2_hidden(sK2(X168,X169,k2_tarski(X170,X170)),k2_tarski(X170,X170)) | sK2(X167,sK2(X168,X169,k2_tarski(X170,X170)),k2_tarski(X170,X170)) = X170 | sK2(X168,X169,k2_tarski(X170,X170)) = X169 | sK2(X168,X169,k2_tarski(X170,X170)) = X168 | k2_tarski(X170,X170) = k2_tarski(X168,X169)).
% 8.60/1.49  
% 8.60/1.49  cnf(u1228,axiom,
% 8.60/1.49      sK2(X70,X71,k2_tarski(X72,X73)) != X74 | k2_tarski(X72,X73) = k2_tarski(sK2(X70,X71,k2_tarski(X72,X73)),X74) | ~r2_hidden(sK2(X70,X71,k2_tarski(X72,X73)),k2_tarski(X72,X73)) | sK2(sK2(X70,X71,k2_tarski(X72,X73)),X74,k2_tarski(X72,X73)) = X72 | sK2(sK2(X70,X71,k2_tarski(X72,X73)),X74,k2_tarski(X72,X73)) = X73 | sK2(X70,X71,k2_tarski(X72,X73)) = X71 | sK2(X70,X71,k2_tarski(X72,X73)) = X70 | k2_tarski(X70,X71) = k2_tarski(X72,X73)).
% 8.60/1.49  
% 8.60/1.49  cnf(u1561,axiom,
% 8.60/1.49      sK2(X85,X86,k2_tarski(X87,X88)) != X84 | k2_tarski(X87,X88) = k2_tarski(X84,sK2(X85,X86,k2_tarski(X87,X88))) | ~r2_hidden(sK2(X85,X86,k2_tarski(X87,X88)),k2_tarski(X87,X88)) | sK2(X84,sK2(X85,X86,k2_tarski(X87,X88)),k2_tarski(X87,X88)) = X87 | sK2(X84,sK2(X85,X86,k2_tarski(X87,X88)),k2_tarski(X87,X88)) = X88 | sK2(X85,X86,k2_tarski(X87,X88)) = X86 | sK2(X85,X86,k2_tarski(X87,X88)) = X85 | k2_tarski(X87,X88) = k2_tarski(X85,X86)).
% 8.60/1.49  
% 8.60/1.49  cnf(u72,axiom,
% 8.60/1.49      sK2(X0,X1,X2) != X0 | k2_tarski(X0,X1) = X2 | ~r2_hidden(X0,X2)).
% 8.60/1.49  
% 8.60/1.49  cnf(u71,axiom,
% 8.60/1.49      sK2(X0,X1,X2) != X1 | k2_tarski(X0,X1) = X2 | ~r2_hidden(X1,X2)).
% 8.60/1.49  
% 8.60/1.49  % (4466)# SZS output end Saturation.
% 8.60/1.49  % (4466)------------------------------
% 8.60/1.49  % (4466)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.60/1.49  % (4466)Termination reason: Satisfiable
% 8.60/1.49  
% 8.60/1.49  % (4466)Memory used [KB]: 4733
% 8.60/1.49  % (4466)Time elapsed: 1.050 s
% 8.60/1.49  % (4466)------------------------------
% 8.60/1.49  % (4466)------------------------------
% 8.60/1.50  % (4460)Success in time 1.116 s
%------------------------------------------------------------------------------
