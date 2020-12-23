%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:11 EST 2020

% Result     : CounterSatisfiable 8.79s
% Output     : Saturation 8.79s
% Verified   : 
% Statistics : Number of clauses        :  250 ( 250 expanded)
%              Number of leaves         :  250 ( 250 expanded)
%              Depth                    :    0
%              Number of atoms          : 1098 (1098 expanded)
%              Number of equality atoms :  946 ( 946 expanded)
%              Maximal clause size      :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u35,negated_conjecture,
    ( v5_orders_2(sK0) )).

cnf(u72,negated_conjecture,
    ( r2_lattice3(sK0,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | k2_tarski(sK3(sK0,X0,X1),sK3(sK0,X0,X1)) = k6_domain_1(u1_struct_0(sK0),sK3(sK0,X0,X1))
    | ~ l1_struct_0(sK0) )).

cnf(u3117,axiom,
    ( r2_lattice3(X7,k2_tarski(X6,X6),X8)
    | sK2(sK3(X7,k2_tarski(X6,X6),X8),sK2(X9,X10,k2_tarski(X6,X6)),k2_tarski(X6,X6)) = X6
    | sK2(X9,X10,k2_tarski(X6,X6)) = X10
    | sK2(X9,X10,k2_tarski(X6,X6)) = X9
    | k2_tarski(X6,X6) = k2_tarski(X9,X10)
    | k2_tarski(X6,X6) = k2_tarski(sK3(X7,k2_tarski(X6,X6),X8),sK2(X9,X10,k2_tarski(X6,X6)))
    | ~ m1_subset_1(X8,u1_struct_0(X7))
    | ~ l1_orders_2(X7) )).

cnf(u2564,axiom,
    ( r2_lattice3(X16,k2_tarski(X15,X15),X17)
    | sK2(sK2(X13,X14,k2_tarski(X15,X15)),sK3(X16,k2_tarski(X15,X15),X17),k2_tarski(X15,X15)) = X15
    | k2_tarski(X15,X15) = k2_tarski(sK2(X13,X14,k2_tarski(X15,X15)),sK3(X16,k2_tarski(X15,X15),X17))
    | ~ m1_subset_1(X17,u1_struct_0(X16))
    | ~ l1_orders_2(X16)
    | sK2(X13,X14,k2_tarski(X15,X15)) = X14
    | sK2(X13,X14,k2_tarski(X15,X15)) = X13
    | k2_tarski(X13,X14) = k2_tarski(X15,X15) )).

cnf(u2560,axiom,
    ( r2_lattice3(X16,k2_tarski(X15,X15),X17)
    | sK2(sK3(X16,k2_tarski(X15,X15),X17),sK2(X13,X14,k2_tarski(X15,X15)),k2_tarski(X15,X15)) = X15
    | k2_tarski(X15,X15) = k2_tarski(sK2(X13,X14,k2_tarski(X15,X15)),sK3(X16,k2_tarski(X15,X15),X17))
    | ~ m1_subset_1(X17,u1_struct_0(X16))
    | ~ l1_orders_2(X16)
    | sK2(X13,X14,k2_tarski(X15,X15)) = X14
    | sK2(X13,X14,k2_tarski(X15,X15)) = X13
    | k2_tarski(X13,X14) = k2_tarski(X15,X15) )).

cnf(u2404,axiom,
    ( r2_lattice3(X13,k2_tarski(X12,X12),X14)
    | ~ m1_subset_1(X14,u1_struct_0(X13))
    | ~ l1_orders_2(X13)
    | sK2(X10,X11,k2_tarski(X12,X12)) = sK3(X13,k2_tarski(X12,X12),X14)
    | sK3(X13,k2_tarski(X12,X12),X14) = X12
    | sK2(X10,X11,k2_tarski(X12,X12)) = X11
    | sK2(X10,X11,k2_tarski(X12,X12)) = X10
    | k2_tarski(X10,X11) = k2_tarski(X12,X12) )).

cnf(u2214,axiom,
    ( r2_lattice3(X5,k2_tarski(X6,X6),X7)
    | sK2(X4,sK3(X5,k2_tarski(X6,X6),X7),k2_tarski(X6,X6)) = X4
    | sK2(X4,sK3(X5,k2_tarski(X6,X6),X7),k2_tarski(X6,X6)) = X6
    | k2_tarski(X6,X6) = k2_tarski(X4,sK3(X5,k2_tarski(X6,X6),X7))
    | ~ m1_subset_1(X7,u1_struct_0(X5))
    | ~ l1_orders_2(X5) )).

cnf(u2209,axiom,
    ( r2_lattice3(X5,k2_tarski(X4,X4),X6)
    | sK2(sK3(X5,k2_tarski(X4,X4),X6),X7,k2_tarski(X4,X4)) = X7
    | sK2(sK3(X5,k2_tarski(X4,X4),X6),X7,k2_tarski(X4,X4)) = X4
    | k2_tarski(X4,X4) = k2_tarski(sK3(X5,k2_tarski(X4,X4),X6),X7)
    | ~ m1_subset_1(X6,u1_struct_0(X5))
    | ~ l1_orders_2(X5) )).

cnf(u1272,axiom,
    ( r2_lattice3(X3,k2_tarski(X2,X2),X4)
    | k2_tarski(X2,X2) = k2_tarski(X2,sK3(X3,k2_tarski(X2,X2),X4))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ l1_orders_2(X3) )).

cnf(u338,axiom,
    ( r2_lattice3(X2,k2_tarski(X3,X3),X4)
    | sK2(sK3(X2,k2_tarski(X3,X3),X4),sK3(X2,k2_tarski(X3,X3),X4),k2_tarski(X3,X3)) = X3
    | k2_tarski(X3,X3) = k2_tarski(sK3(X2,k2_tarski(X3,X3),X4),sK3(X2,k2_tarski(X3,X3),X4))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X2) )).

cnf(u3109,axiom,
    ( r2_lattice3(X10,k2_tarski(X8,X9),X11)
    | sK2(sK3(X10,k2_tarski(X8,X9),X11),sK2(X12,X13,k2_tarski(X8,X9)),k2_tarski(X8,X9)) = X8
    | sK2(sK3(X10,k2_tarski(X8,X9),X11),sK2(X12,X13,k2_tarski(X8,X9)),k2_tarski(X8,X9)) = X9
    | sK2(X12,X13,k2_tarski(X8,X9)) = X13
    | sK2(X12,X13,k2_tarski(X8,X9)) = X12
    | k2_tarski(X8,X9) = k2_tarski(X12,X13)
    | k2_tarski(X8,X9) = k2_tarski(sK3(X10,k2_tarski(X8,X9),X11),sK2(X12,X13,k2_tarski(X8,X9)))
    | ~ m1_subset_1(X11,u1_struct_0(X10))
    | ~ l1_orders_2(X10) )).

cnf(u3099,axiom,
    ( r2_lattice3(X12,k2_tarski(X8,X9),X13)
    | sK2(sK2(X10,X11,k2_tarski(X8,X9)),sK3(X12,k2_tarski(X8,X9),X13),k2_tarski(X8,X9)) = X8
    | sK2(sK2(X10,X11,k2_tarski(X8,X9)),sK3(X12,k2_tarski(X8,X9),X13),k2_tarski(X8,X9)) = X9
    | sK2(X10,X11,k2_tarski(X8,X9)) = X11
    | sK2(X10,X11,k2_tarski(X8,X9)) = X10
    | k2_tarski(X10,X11) = k2_tarski(X8,X9)
    | k2_tarski(X8,X9) = k2_tarski(sK2(X10,X11,k2_tarski(X8,X9)),sK3(X12,k2_tarski(X8,X9),X13))
    | ~ m1_subset_1(X13,u1_struct_0(X12))
    | ~ l1_orders_2(X12) )).

cnf(u2561,axiom,
    ( r2_lattice3(X2,k2_tarski(X1,X0),X3)
    | sK2(X0,sK3(X2,k2_tarski(X1,X0),X3),k2_tarski(X1,X0)) = X1
    | k2_tarski(X1,X0) = k2_tarski(X0,sK3(X2,k2_tarski(X1,X0),X3))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_orders_2(X2) )).

cnf(u2557,axiom,
    ( r2_lattice3(X2,k2_tarski(X1,X0),X3)
    | sK2(sK3(X2,k2_tarski(X1,X0),X3),X0,k2_tarski(X1,X0)) = X1
    | k2_tarski(X1,X0) = k2_tarski(X0,sK3(X2,k2_tarski(X1,X0),X3))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_orders_2(X2) )).

cnf(u2218,axiom,
    ( r2_lattice3(X5,k2_tarski(X4,X6),X7)
    | sK2(X4,sK3(X5,k2_tarski(X4,X6),X7),k2_tarski(X4,X6)) = X6
    | k2_tarski(X4,X6) = k2_tarski(X4,sK3(X5,k2_tarski(X4,X6),X7))
    | ~ m1_subset_1(X7,u1_struct_0(X5))
    | ~ l1_orders_2(X5) )).

cnf(u1920,axiom,
    ( r2_lattice3(X6,k2_tarski(X4,X5),X7)
    | sK2(sK3(X6,k2_tarski(X4,X5),X7),X4,k2_tarski(X4,X5)) = X5
    | k2_tarski(X4,X5) = k2_tarski(X4,sK3(X6,k2_tarski(X4,X5),X7))
    | ~ m1_subset_1(X7,u1_struct_0(X6))
    | ~ l1_orders_2(X6) )).

cnf(u1753,axiom,
    ( r2_lattice3(X6,k2_tarski(X4,X5),X7)
    | sK2(sK3(X6,k2_tarski(X4,X5),X7),sK3(X6,k2_tarski(X4,X5),X7),k2_tarski(X4,X5)) = X4
    | sK2(sK3(X6,k2_tarski(X4,X5),X7),sK3(X6,k2_tarski(X4,X5),X7),k2_tarski(X4,X5)) = X5
    | k2_tarski(X4,X5) = k2_tarski(sK3(X6,k2_tarski(X4,X5),X7),sK3(X6,k2_tarski(X4,X5),X7))
    | ~ m1_subset_1(X7,u1_struct_0(X6))
    | ~ l1_orders_2(X6) )).

cnf(u299,axiom,
    ( r2_lattice3(X9,k2_tarski(X6,X7),X10)
    | sK2(X8,sK3(X9,k2_tarski(X6,X7),X10),k2_tarski(X6,X7)) = X8
    | sK2(X8,sK3(X9,k2_tarski(X6,X7),X10),k2_tarski(X6,X7)) = X6
    | sK2(X8,sK3(X9,k2_tarski(X6,X7),X10),k2_tarski(X6,X7)) = X7
    | k2_tarski(X6,X7) = k2_tarski(X8,sK3(X9,k2_tarski(X6,X7),X10))
    | ~ m1_subset_1(X10,u1_struct_0(X9))
    | ~ l1_orders_2(X9) )).

cnf(u275,axiom,
    ( r2_lattice3(X8,k2_tarski(X6,X7),X9)
    | sK2(sK3(X8,k2_tarski(X6,X7),X9),X10,k2_tarski(X6,X7)) = X10
    | sK2(sK3(X8,k2_tarski(X6,X7),X9),X10,k2_tarski(X6,X7)) = X6
    | sK2(sK3(X8,k2_tarski(X6,X7),X9),X10,k2_tarski(X6,X7)) = X7
    | k2_tarski(X6,X7) = k2_tarski(sK3(X8,k2_tarski(X6,X7),X9),X10)
    | ~ m1_subset_1(X9,u1_struct_0(X8))
    | ~ l1_orders_2(X8) )).

cnf(u71,axiom,
    ( r2_lattice3(X0,k2_tarski(X1,X2),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK3(X0,k2_tarski(X1,X2),X3) = X1
    | sK3(X0,k2_tarski(X1,X2),X3) = X2 )).

cnf(u53,axiom,
    ( r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u50,axiom,
    ( r1_orders_2(X0,X4,X2)
    | ~ r2_hidden(X4,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u47,axiom,
    ( r1_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u34,negated_conjecture,
    ( v3_orders_2(sK0) )).

cnf(u51,axiom,
    ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
    | r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u37,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

cnf(u65,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k2_tarski(X0,X0) = k6_domain_1(u1_struct_0(sK0),X0)
    | ~ l1_struct_0(sK0) )).

cnf(u36,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u54,axiom,
    ( v1_xboole_0(X0)
    | ~ m1_subset_1(X1,X0)
    | k6_domain_1(X0,X1) = k2_tarski(X1,X1) )).

cnf(u62,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(sK0) )).

cnf(u49,axiom,
    ( l1_struct_0(X0)
    | ~ l1_orders_2(X0) )).

cnf(u48,axiom,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) )).

cnf(u33,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u42,axiom,
    ( r2_hidden(sK2(X0,X1,X2),X2)
    | sK2(X0,X1,X2) = X1
    | sK2(X0,X1,X2) = X0
    | k2_tarski(X0,X1) = X2 )).

cnf(u52,axiom,
    ( r2_hidden(sK3(X0,X1,X2),X1)
    | r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u58,axiom,
    ( r2_hidden(X4,k2_tarski(X4,X1)) )).

cnf(u56,axiom,
    ( r2_hidden(X4,k2_tarski(X0,X4)) )).

cnf(u923,axiom,
    ( ~ r2_hidden(X40,k2_tarski(X40,X40))
    | k2_tarski(X40,X40) = k2_tarski(X39,X40)
    | sK2(X39,X40,k2_tarski(X40,X40)) = X39 )).

cnf(u1679,axiom,
    ( ~ r2_hidden(X58,k2_tarski(X58,X58))
    | k2_tarski(X58,X59) = k2_tarski(X58,X58)
    | sK2(X58,X59,k2_tarski(X58,X58)) = X59 )).

cnf(u201,axiom,
    ( ~ r2_hidden(X12,k2_tarski(X12,X13))
    | k2_tarski(X12,X12) = k2_tarski(X12,X13)
    | sK2(X12,X12,k2_tarski(X12,X13)) = X13 )).

cnf(u802,axiom,
    ( ~ r2_hidden(X38,k2_tarski(X38,X37))
    | k2_tarski(X38,X37) = k2_tarski(X37,X38) )).

cnf(u399,axiom,
    ( ~ r2_hidden(X19,k2_tarski(X19,X20))
    | k2_tarski(X19,X20) = k2_tarski(X18,X19)
    | sK2(X18,X19,k2_tarski(X19,X20)) = X18
    | sK2(X18,X19,k2_tarski(X19,X20)) = X20 )).

cnf(u554,axiom,
    ( ~ r2_hidden(X27,k2_tarski(X27,X29))
    | k2_tarski(X27,X29) = k2_tarski(X27,X28)
    | sK2(X27,X28,k2_tarski(X27,X29)) = X28
    | sK2(X27,X28,k2_tarski(X27,X29)) = X29 )).

cnf(u2468,axiom,
    ( ~ r2_hidden(X277,k2_tarski(X276,X276))
    | k2_tarski(X276,X276) = k2_tarski(sK2(X274,X275,k2_tarski(X276,X276)),X277)
    | sK2(sK2(X274,X275,k2_tarski(X276,X276)),X277,k2_tarski(X276,X276)) = X276
    | sK2(X274,X275,k2_tarski(X276,X276)) = X275
    | sK2(X274,X275,k2_tarski(X276,X276)) = X274
    | k2_tarski(X276,X276) = k2_tarski(X274,X275) )).

cnf(u2460,axiom,
    ( ~ r2_hidden(X245,k2_tarski(X244,X244))
    | k2_tarski(X244,X244) = k2_tarski(X245,sK2(X242,X243,k2_tarski(X244,X244)))
    | sK2(X245,sK2(X242,X243,k2_tarski(X244,X244)),k2_tarski(X244,X244)) = X244
    | sK2(X242,X243,k2_tarski(X244,X244)) = X243
    | sK2(X242,X243,k2_tarski(X244,X244)) = X242
    | k2_tarski(X244,X244) = k2_tarski(X242,X243) )).

cnf(u2403,axiom,
    ( ~ r2_hidden(X9,k2_tarski(X8,X8))
    | sK2(X6,X7,k2_tarski(X8,X8)) = X9
    | X8 = X9
    | sK2(X6,X7,k2_tarski(X8,X8)) = X7
    | sK2(X6,X7,k2_tarski(X8,X8)) = X6
    | k2_tarski(X6,X7) = k2_tarski(X8,X8) )).

cnf(u1732,axiom,
    ( ~ r2_hidden(X65,k2_tarski(X64,X64))
    | k2_tarski(X64,X65) = k2_tarski(X64,X64) )).

cnf(u1266,axiom,
    ( ~ r2_hidden(X50,k2_tarski(X51,X51))
    | k2_tarski(X51,X51) = k2_tarski(X50,X51) )).

cnf(u781,axiom,
    ( ~ r2_hidden(X45,k2_tarski(X46,X46))
    | k2_tarski(X44,X45) = k2_tarski(X46,X46)
    | sK2(X44,X45,k2_tarski(X46,X46)) = X44
    | sK2(X44,X45,k2_tarski(X46,X46)) = X46 )).

cnf(u779,axiom,
    ( ~ r2_hidden(X41,k2_tarski(X43,X43))
    | k2_tarski(X43,X43) = k2_tarski(X41,X42)
    | sK2(X41,X42,k2_tarski(X43,X43)) = X42
    | sK2(X41,X42,k2_tarski(X43,X43)) = X43 )).

cnf(u331,axiom,
    ( ~ r2_hidden(X12,k2_tarski(X13,X13))
    | k2_tarski(X12,X12) = k2_tarski(X13,X13)
    | sK2(X12,X12,k2_tarski(X13,X13)) = X13 )).

cnf(u261,axiom,
    ( ~ r2_hidden(X12,k2_tarski(X13,X12))
    | k2_tarski(X12,X12) = k2_tarski(X13,X12)
    | sK2(X12,X12,k2_tarski(X13,X12)) = X13 )).

cnf(u684,axiom,
    ( ~ r2_hidden(X28,k2_tarski(X29,X28))
    | k2_tarski(X29,X28) = k2_tarski(X28,X29)
    | sK2(X28,X29,k2_tarski(X29,X28)) = X29 )).

cnf(u468,axiom,
    ( ~ r2_hidden(X25,k2_tarski(X26,X25))
    | k2_tarski(X26,X25) = k2_tarski(X24,X25)
    | sK2(X24,X25,k2_tarski(X26,X25)) = X24
    | sK2(X24,X25,k2_tarski(X26,X25)) = X26 )).

cnf(u643,axiom,
    ( ~ r2_hidden(X33,k2_tarski(X35,X33))
    | k2_tarski(X33,X34) = k2_tarski(X35,X33)
    | sK2(X33,X34,k2_tarski(X35,X33)) = X34
    | sK2(X33,X34,k2_tarski(X35,X33)) = X35 )).

cnf(u2220,axiom,
    ( ~ r2_hidden(X2,k2_tarski(X1,X0))
    | k2_tarski(X1,X0) = k2_tarski(X0,X2)
    | sK2(X0,X2,k2_tarski(X1,X0)) = X1 )).

cnf(u2202,axiom,
    ( ~ r2_hidden(X96,k2_tarski(X95,X97))
    | k2_tarski(X95,X96) = k2_tarski(X95,X97)
    | sK2(X95,X96,k2_tarski(X95,X97)) = X97 )).

cnf(u1918,axiom,
    ( ~ r2_hidden(X2,k2_tarski(X1,X0))
    | k2_tarski(X1,X0) = k2_tarski(X2,X0)
    | sK2(X2,X0,k2_tarski(X1,X0)) = X1 )).

cnf(u1893,axiom,
    ( ~ r2_hidden(X87,k2_tarski(X88,X89))
    | k2_tarski(X88,X89) = k2_tarski(X87,X88)
    | sK2(X87,X88,k2_tarski(X88,X89)) = X89 )).

cnf(u1538,axiom,
    ( ~ r2_hidden(X79,k2_tarski(X82,X83))
    | k2_tarski(X82,X83) = k2_tarski(X79,sK2(X80,X81,k2_tarski(X82,X83)))
    | sK2(X79,sK2(X80,X81,k2_tarski(X82,X83)),k2_tarski(X82,X83)) = X82
    | sK2(X79,sK2(X80,X81,k2_tarski(X82,X83)),k2_tarski(X82,X83)) = X83
    | sK2(X80,X81,k2_tarski(X82,X83)) = X81
    | sK2(X80,X81,k2_tarski(X82,X83)) = X80
    | k2_tarski(X80,X81) = k2_tarski(X82,X83) )).

cnf(u1162,axiom,
    ( ~ r2_hidden(X76,k2_tarski(X74,X75))
    | k2_tarski(X74,X75) = k2_tarski(sK2(X72,X73,k2_tarski(X74,X75)),X76)
    | sK2(sK2(X72,X73,k2_tarski(X74,X75)),X76,k2_tarski(X74,X75)) = X74
    | sK2(sK2(X72,X73,k2_tarski(X74,X75)),X76,k2_tarski(X74,X75)) = X75
    | sK2(X72,X73,k2_tarski(X74,X75)) = X73
    | sK2(X72,X73,k2_tarski(X74,X75)) = X72
    | k2_tarski(X74,X75) = k2_tarski(X72,X73) )).

cnf(u648,axiom,
    ( ~ r2_hidden(X37,k2_tarski(X38,X36))
    | k2_tarski(X36,X37) = k2_tarski(X38,X36)
    | sK2(X36,X37,k2_tarski(X38,X36)) = X38
    | sK2(X36,X37,k2_tarski(X38,X36)) = X36 )).

cnf(u556,axiom,
    ( ~ r2_hidden(X31,k2_tarski(X30,X32))
    | k2_tarski(X30,X32) = k2_tarski(X30,X31)
    | sK2(X30,X31,k2_tarski(X30,X32)) = X30
    | sK2(X30,X31,k2_tarski(X30,X32)) = X32 )).

cnf(u475,axiom,
    ( ~ r2_hidden(X21,k2_tarski(X23,X22))
    | k2_tarski(X23,X22) = k2_tarski(X21,X22)
    | sK2(X21,X22,k2_tarski(X23,X22)) = X23
    | sK2(X21,X22,k2_tarski(X23,X22)) = X22 )).

cnf(u403,axiom,
    ( ~ r2_hidden(X15,k2_tarski(X16,X17))
    | k2_tarski(X16,X17) = k2_tarski(X15,X16)
    | sK2(X15,X16,k2_tarski(X16,X17)) = X16
    | sK2(X15,X16,k2_tarski(X16,X17)) = X17 )).

cnf(u167,axiom,
    ( ~ r2_hidden(X18,k2_tarski(X19,X20))
    | k2_tarski(X19,X20) = k2_tarski(X18,X18)
    | sK2(X18,X18,k2_tarski(X19,X20)) = X19
    | sK2(X18,X18,k2_tarski(X19,X20)) = X20 )).

cnf(u120,axiom,
    ( ~ r2_hidden(X9,k2_tarski(X10,X11))
    | k2_tarski(X10,X11) = k2_tarski(X8,X9)
    | sK2(X8,X9,k2_tarski(X10,X11)) = X8
    | sK2(X8,X9,k2_tarski(X10,X11)) = X10
    | sK2(X8,X9,k2_tarski(X10,X11)) = X11 )).

cnf(u118,axiom,
    ( ~ r2_hidden(X4,k2_tarski(X6,X7))
    | k2_tarski(X6,X7) = k2_tarski(X4,X5)
    | sK2(X4,X5,k2_tarski(X6,X7)) = X5
    | sK2(X4,X5,k2_tarski(X6,X7)) = X6
    | sK2(X4,X5,k2_tarski(X6,X7)) = X7 )).

cnf(u59,axiom,
    ( ~ r2_hidden(X4,k2_tarski(X0,X1))
    | X0 = X4
    | X1 = X4 )).

cnf(u1739,axiom,
    ( k2_tarski(X5,X5) = k2_tarski(X5,sK2(X6,X7,k2_tarski(X5,X5)))
    | sK2(X6,X7,k2_tarski(X5,X5)) = X7
    | sK2(X6,X7,k2_tarski(X5,X5)) = X6
    | k2_tarski(X6,X7) = k2_tarski(X5,X5) )).

cnf(u1271,axiom,
    ( k2_tarski(X5,X5) = k2_tarski(sK2(X6,X7,k2_tarski(X5,X5)),X5)
    | sK2(X6,X7,k2_tarski(X5,X5)) = X7
    | sK2(X6,X7,k2_tarski(X5,X5)) = X6
    | k2_tarski(X6,X7) = k2_tarski(X5,X5) )).

cnf(u807,axiom,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) )).

cnf(u2210,axiom,
    ( sK2(sK2(X9,X10,k2_tarski(X8,X8)),X11,k2_tarski(X8,X8)) = X11
    | sK2(sK2(X9,X10,k2_tarski(X8,X8)),X11,k2_tarski(X8,X8)) = X8
    | k2_tarski(X8,X8) = k2_tarski(sK2(X9,X10,k2_tarski(X8,X8)),X11)
    | sK2(X9,X10,k2_tarski(X8,X8)) = X10
    | sK2(X9,X10,k2_tarski(X8,X8)) = X9
    | k2_tarski(X8,X8) = k2_tarski(X9,X10) )).

cnf(u2210_001,axiom,
    ( sK2(sK2(X9,X10,k2_tarski(X8,X8)),X11,k2_tarski(X8,X8)) = X11
    | sK2(sK2(X9,X10,k2_tarski(X8,X8)),X11,k2_tarski(X8,X8)) = X8
    | k2_tarski(X8,X8) = k2_tarski(sK2(X9,X10,k2_tarski(X8,X8)),X11)
    | sK2(X9,X10,k2_tarski(X8,X8)) = X10
    | sK2(X9,X10,k2_tarski(X8,X8)) = X9
    | k2_tarski(X8,X8) = k2_tarski(X9,X10) )).

cnf(u5071,axiom,
    ( sK2(sK2(X0,X1,k2_tarski(X2,X2)),sK2(X3,X4,k2_tarski(X2,X2)),k2_tarski(X2,X2)) = X2
    | k2_tarski(X2,X2) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X2)),sK2(X3,X4,k2_tarski(X2,X2)))
    | sK2(X0,X1,k2_tarski(X2,X2)) = X1
    | sK2(X0,X1,k2_tarski(X2,X2)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X2)
    | sK2(X3,X4,k2_tarski(X2,X2)) = X4
    | sK2(X3,X4,k2_tarski(X2,X2)) = X3
    | k2_tarski(X2,X2) = k2_tarski(X3,X4) )).

cnf(u2644,axiom,
    ( sK2(sK2(X16,X17,k2_tarski(X15,X15)),sK2(X13,X14,k2_tarski(X15,X15)),k2_tarski(X15,X15)) = X15
    | k2_tarski(X15,X15) = k2_tarski(sK2(X13,X14,k2_tarski(X15,X15)),sK2(X16,X17,k2_tarski(X15,X15)))
    | sK2(X16,X17,k2_tarski(X15,X15)) = X17
    | sK2(X16,X17,k2_tarski(X15,X15)) = X16
    | k2_tarski(X16,X17) = k2_tarski(X15,X15)
    | sK2(X13,X14,k2_tarski(X15,X15)) = X14
    | sK2(X13,X14,k2_tarski(X15,X15)) = X13
    | k2_tarski(X13,X14) = k2_tarski(X15,X15) )).

cnf(u339,axiom,
    ( sK2(sK2(X5,X6,k2_tarski(X7,X7)),sK2(X5,X6,k2_tarski(X7,X7)),k2_tarski(X7,X7)) = X7
    | k2_tarski(X7,X7) = k2_tarski(sK2(X5,X6,k2_tarski(X7,X7)),sK2(X5,X6,k2_tarski(X7,X7)))
    | sK2(X5,X6,k2_tarski(X7,X7)) = X6
    | sK2(X5,X6,k2_tarski(X7,X7)) = X5
    | k2_tarski(X7,X7) = k2_tarski(X5,X6) )).

cnf(u3100,axiom,
    ( sK2(sK2(X16,X17,k2_tarski(X14,X15)),sK2(X18,X19,k2_tarski(X14,X15)),k2_tarski(X14,X15)) = X14
    | sK2(sK2(X16,X17,k2_tarski(X14,X15)),sK2(X18,X19,k2_tarski(X14,X15)),k2_tarski(X14,X15)) = X15
    | k2_tarski(X14,X15) = k2_tarski(sK2(X16,X17,k2_tarski(X14,X15)),sK2(X18,X19,k2_tarski(X14,X15)))
    | sK2(X16,X17,k2_tarski(X14,X15)) = X17
    | sK2(X16,X17,k2_tarski(X14,X15)) = X16
    | k2_tarski(X14,X15) = k2_tarski(X16,X17)
    | sK2(X18,X19,k2_tarski(X14,X15)) = X19
    | sK2(X18,X19,k2_tarski(X14,X15)) = X18
    | k2_tarski(X14,X15) = k2_tarski(X18,X19) )).

cnf(u3100_002,axiom,
    ( sK2(sK2(X16,X17,k2_tarski(X14,X15)),sK2(X18,X19,k2_tarski(X14,X15)),k2_tarski(X14,X15)) = X14
    | sK2(sK2(X16,X17,k2_tarski(X14,X15)),sK2(X18,X19,k2_tarski(X14,X15)),k2_tarski(X14,X15)) = X15
    | k2_tarski(X14,X15) = k2_tarski(sK2(X16,X17,k2_tarski(X14,X15)),sK2(X18,X19,k2_tarski(X14,X15)))
    | sK2(X16,X17,k2_tarski(X14,X15)) = X17
    | sK2(X16,X17,k2_tarski(X14,X15)) = X16
    | k2_tarski(X14,X15) = k2_tarski(X16,X17)
    | sK2(X18,X19,k2_tarski(X14,X15)) = X19
    | sK2(X18,X19,k2_tarski(X14,X15)) = X18
    | k2_tarski(X14,X15) = k2_tarski(X18,X19) )).

cnf(u1754,axiom,
    ( sK2(sK2(X10,X11,k2_tarski(X8,X9)),sK2(X10,X11,k2_tarski(X8,X9)),k2_tarski(X8,X9)) = X8
    | sK2(sK2(X10,X11,k2_tarski(X8,X9)),sK2(X10,X11,k2_tarski(X8,X9)),k2_tarski(X8,X9)) = X9
    | k2_tarski(X8,X9) = k2_tarski(sK2(X10,X11,k2_tarski(X8,X9)),sK2(X10,X11,k2_tarski(X8,X9)))
    | sK2(X10,X11,k2_tarski(X8,X9)) = X11
    | sK2(X10,X11,k2_tarski(X8,X9)) = X10
    | k2_tarski(X10,X11) = k2_tarski(X8,X9) )).

cnf(u1754_003,axiom,
    ( sK2(sK2(X10,X11,k2_tarski(X8,X9)),sK2(X10,X11,k2_tarski(X8,X9)),k2_tarski(X8,X9)) = X8
    | sK2(sK2(X10,X11,k2_tarski(X8,X9)),sK2(X10,X11,k2_tarski(X8,X9)),k2_tarski(X8,X9)) = X9
    | k2_tarski(X8,X9) = k2_tarski(sK2(X10,X11,k2_tarski(X8,X9)),sK2(X10,X11,k2_tarski(X8,X9)))
    | sK2(X10,X11,k2_tarski(X8,X9)) = X11
    | sK2(X10,X11,k2_tarski(X8,X9)) = X10
    | k2_tarski(X10,X11) = k2_tarski(X8,X9) )).

cnf(u276,axiom,
    ( sK2(sK2(X13,X14,k2_tarski(X11,X12)),X15,k2_tarski(X11,X12)) = X15
    | sK2(sK2(X13,X14,k2_tarski(X11,X12)),X15,k2_tarski(X11,X12)) = X11
    | sK2(sK2(X13,X14,k2_tarski(X11,X12)),X15,k2_tarski(X11,X12)) = X12
    | k2_tarski(X11,X12) = k2_tarski(sK2(X13,X14,k2_tarski(X11,X12)),X15)
    | sK2(X13,X14,k2_tarski(X11,X12)) = X14
    | sK2(X13,X14,k2_tarski(X11,X12)) = X13
    | k2_tarski(X13,X14) = k2_tarski(X11,X12) )).

cnf(u276_004,axiom,
    ( sK2(sK2(X13,X14,k2_tarski(X11,X12)),X15,k2_tarski(X11,X12)) = X15
    | sK2(sK2(X13,X14,k2_tarski(X11,X12)),X15,k2_tarski(X11,X12)) = X11
    | sK2(sK2(X13,X14,k2_tarski(X11,X12)),X15,k2_tarski(X11,X12)) = X12
    | k2_tarski(X11,X12) = k2_tarski(sK2(X13,X14,k2_tarski(X11,X12)),X15)
    | sK2(X13,X14,k2_tarski(X11,X12)) = X14
    | sK2(X13,X14,k2_tarski(X11,X12)) = X13
    | k2_tarski(X13,X14) = k2_tarski(X11,X12) )).

cnf(u276_005,axiom,
    ( sK2(sK2(X13,X14,k2_tarski(X11,X12)),X15,k2_tarski(X11,X12)) = X15
    | sK2(sK2(X13,X14,k2_tarski(X11,X12)),X15,k2_tarski(X11,X12)) = X11
    | sK2(sK2(X13,X14,k2_tarski(X11,X12)),X15,k2_tarski(X11,X12)) = X12
    | k2_tarski(X11,X12) = k2_tarski(sK2(X13,X14,k2_tarski(X11,X12)),X15)
    | sK2(X13,X14,k2_tarski(X11,X12)) = X14
    | sK2(X13,X14,k2_tarski(X11,X12)) = X13
    | k2_tarski(X13,X14) = k2_tarski(X11,X12) )).

cnf(u2641,axiom,
    ( sK2(sK2(X2,X3,k2_tarski(X1,X0)),X0,k2_tarski(X1,X0)) = X1
    | k2_tarski(X1,X0) = k2_tarski(X0,sK2(X2,X3,k2_tarski(X1,X0)))
    | sK2(X2,X3,k2_tarski(X1,X0)) = X3
    | sK2(X2,X3,k2_tarski(X1,X0)) = X2
    | k2_tarski(X1,X0) = k2_tarski(X2,X3) )).

cnf(u1921,axiom,
    ( sK2(sK2(X10,X11,k2_tarski(X8,X9)),X8,k2_tarski(X8,X9)) = X9
    | k2_tarski(X8,X9) = k2_tarski(X8,sK2(X10,X11,k2_tarski(X8,X9)))
    | sK2(X10,X11,k2_tarski(X8,X9)) = X11
    | sK2(X10,X11,k2_tarski(X8,X9)) = X10
    | k2_tarski(X10,X11) = k2_tarski(X8,X9) )).

cnf(u2219,axiom,
    ( sK2(X8,sK2(X9,X10,k2_tarski(X8,X11)),k2_tarski(X8,X11)) = X11
    | k2_tarski(X8,X11) = k2_tarski(X8,sK2(X9,X10,k2_tarski(X8,X11)))
    | sK2(X9,X10,k2_tarski(X8,X11)) = X10
    | sK2(X9,X10,k2_tarski(X8,X11)) = X9
    | k2_tarski(X9,X10) = k2_tarski(X8,X11) )).

cnf(u2215,axiom,
    ( sK2(X8,sK2(X9,X10,k2_tarski(X11,X11)),k2_tarski(X11,X11)) = X8
    | sK2(X8,sK2(X9,X10,k2_tarski(X11,X11)),k2_tarski(X11,X11)) = X11
    | k2_tarski(X11,X11) = k2_tarski(X8,sK2(X9,X10,k2_tarski(X11,X11)))
    | sK2(X9,X10,k2_tarski(X11,X11)) = X10
    | sK2(X9,X10,k2_tarski(X11,X11)) = X9
    | k2_tarski(X11,X11) = k2_tarski(X9,X10) )).

cnf(u2215_006,axiom,
    ( sK2(X8,sK2(X9,X10,k2_tarski(X11,X11)),k2_tarski(X11,X11)) = X8
    | sK2(X8,sK2(X9,X10,k2_tarski(X11,X11)),k2_tarski(X11,X11)) = X11
    | k2_tarski(X11,X11) = k2_tarski(X8,sK2(X9,X10,k2_tarski(X11,X11)))
    | sK2(X9,X10,k2_tarski(X11,X11)) = X10
    | sK2(X9,X10,k2_tarski(X11,X11)) = X9
    | k2_tarski(X11,X11) = k2_tarski(X9,X10) )).

cnf(u2755,axiom,
    ( sK2(X0,sK2(X2,X3,k2_tarski(X1,X0)),k2_tarski(X1,X0)) = X1
    | k2_tarski(X1,X0) = k2_tarski(X0,sK2(X2,X3,k2_tarski(X1,X0)))
    | sK2(X2,X3,k2_tarski(X1,X0)) = X3
    | sK2(X2,X3,k2_tarski(X1,X0)) = X2
    | k2_tarski(X1,X0) = k2_tarski(X2,X3) )).

cnf(u300,axiom,
    ( sK2(X13,sK2(X14,X15,k2_tarski(X11,X12)),k2_tarski(X11,X12)) = X13
    | sK2(X13,sK2(X14,X15,k2_tarski(X11,X12)),k2_tarski(X11,X12)) = X11
    | sK2(X13,sK2(X14,X15,k2_tarski(X11,X12)),k2_tarski(X11,X12)) = X12
    | k2_tarski(X11,X12) = k2_tarski(X13,sK2(X14,X15,k2_tarski(X11,X12)))
    | sK2(X14,X15,k2_tarski(X11,X12)) = X15
    | sK2(X14,X15,k2_tarski(X11,X12)) = X14
    | k2_tarski(X14,X15) = k2_tarski(X11,X12) )).

cnf(u300_007,axiom,
    ( sK2(X13,sK2(X14,X15,k2_tarski(X11,X12)),k2_tarski(X11,X12)) = X13
    | sK2(X13,sK2(X14,X15,k2_tarski(X11,X12)),k2_tarski(X11,X12)) = X11
    | sK2(X13,sK2(X14,X15,k2_tarski(X11,X12)),k2_tarski(X11,X12)) = X12
    | k2_tarski(X11,X12) = k2_tarski(X13,sK2(X14,X15,k2_tarski(X11,X12)))
    | sK2(X14,X15,k2_tarski(X11,X12)) = X15
    | sK2(X14,X15,k2_tarski(X11,X12)) = X14
    | k2_tarski(X14,X15) = k2_tarski(X11,X12) )).

cnf(u300_008,axiom,
    ( sK2(X13,sK2(X14,X15,k2_tarski(X11,X12)),k2_tarski(X11,X12)) = X13
    | sK2(X13,sK2(X14,X15,k2_tarski(X11,X12)),k2_tarski(X11,X12)) = X11
    | sK2(X13,sK2(X14,X15,k2_tarski(X11,X12)),k2_tarski(X11,X12)) = X12
    | k2_tarski(X11,X12) = k2_tarski(X13,sK2(X14,X15,k2_tarski(X11,X12)))
    | sK2(X14,X15,k2_tarski(X11,X12)) = X15
    | sK2(X14,X15,k2_tarski(X11,X12)) = X14
    | k2_tarski(X14,X15) = k2_tarski(X11,X12) )).

cnf(u171,axiom,
    ( sK2(X0,X0,k2_tarski(X0,X1)) = X0
    | sK2(X0,X0,k2_tarski(X0,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X0,X0) )).

cnf(u209,axiom,
    ( sK2(X1,X1,k2_tarski(X1,X2)) = X2
    | k2_tarski(X1,X1) = k2_tarski(X1,X2) )).

cnf(u171_009,axiom,
    ( sK2(X0,X0,k2_tarski(X0,X1)) = X0
    | sK2(X0,X0,k2_tarski(X0,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X0,X0) )).

cnf(u302,axiom,
    ( sK2(X0,X0,k2_tarski(X1,X1)) = X0
    | sK2(X0,X0,k2_tarski(X1,X1)) = X1
    | k2_tarski(X0,X0) = k2_tarski(X1,X1) )).

cnf(u302_010,axiom,
    ( sK2(X0,X0,k2_tarski(X1,X1)) = X0
    | sK2(X0,X0,k2_tarski(X1,X1)) = X1
    | k2_tarski(X0,X0) = k2_tarski(X1,X1) )).

cnf(u234,axiom,
    ( sK2(X0,X0,k2_tarski(X1,X0)) = X1
    | sK2(X0,X0,k2_tarski(X1,X0)) = X0
    | k2_tarski(X0,X0) = k2_tarski(X1,X0) )).

cnf(u234_011,axiom,
    ( sK2(X0,X0,k2_tarski(X1,X0)) = X1
    | sK2(X0,X0,k2_tarski(X1,X0)) = X0
    | k2_tarski(X0,X0) = k2_tarski(X1,X0) )).

cnf(u271,axiom,
    ( sK2(X0,X0,k2_tarski(X1,X0)) = X1
    | k2_tarski(X0,X0) = k2_tarski(X1,X0) )).

cnf(u122,axiom,
    ( sK2(X0,X0,k2_tarski(X1,X2)) = X0
    | sK2(X0,X0,k2_tarski(X1,X2)) = X1
    | sK2(X0,X0,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X0) = k2_tarski(X1,X2) )).

cnf(u122_012,axiom,
    ( sK2(X0,X0,k2_tarski(X1,X2)) = X0
    | sK2(X0,X0,k2_tarski(X1,X2)) = X1
    | sK2(X0,X0,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X0) = k2_tarski(X1,X2) )).

cnf(u122_013,axiom,
    ( sK2(X0,X0,k2_tarski(X1,X2)) = X0
    | sK2(X0,X0,k2_tarski(X1,X2)) = X1
    | sK2(X0,X0,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X0) = k2_tarski(X1,X2) )).

cnf(u1622,axiom,
    ( sK2(X0,X1,k2_tarski(X0,X0)) = X1
    | sK2(X0,X1,k2_tarski(X0,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X0,X0) )).

cnf(u1622_014,axiom,
    ( sK2(X0,X1,k2_tarski(X0,X0)) = X1
    | sK2(X0,X1,k2_tarski(X0,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X0,X0) )).

cnf(u1690,axiom,
    ( sK2(X0,X1,k2_tarski(X0,X0)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X0,X0) )).

cnf(u207,axiom,
    ( sK2(X0,X1,k2_tarski(X0,X2)) = X1
    | sK2(X0,X1,k2_tarski(X0,X2)) = X0
    | sK2(X0,X1,k2_tarski(X0,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u1931,axiom,
    ( sK2(X2,X4,k2_tarski(X2,X3)) = X4
    | sK2(X2,X4,k2_tarski(X2,X3)) = X3
    | k2_tarski(X2,X3) = k2_tarski(X2,X4) )).

cnf(u207_015,axiom,
    ( sK2(X0,X1,k2_tarski(X0,X2)) = X1
    | sK2(X0,X1,k2_tarski(X0,X2)) = X0
    | sK2(X0,X1,k2_tarski(X0,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u207_016,axiom,
    ( sK2(X0,X1,k2_tarski(X0,X2)) = X1
    | sK2(X0,X1,k2_tarski(X0,X2)) = X0
    | sK2(X0,X1,k2_tarski(X0,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u1931_017,axiom,
    ( sK2(X2,X4,k2_tarski(X2,X3)) = X4
    | sK2(X2,X4,k2_tarski(X2,X3)) = X3
    | k2_tarski(X2,X3) = k2_tarski(X2,X4) )).

cnf(u885,axiom,
    ( sK2(X0,X1,k2_tarski(X1,X1)) = X0
    | sK2(X0,X1,k2_tarski(X1,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X1,X1) )).

cnf(u885_018,axiom,
    ( sK2(X0,X1,k2_tarski(X1,X1)) = X0
    | sK2(X0,X1,k2_tarski(X1,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X1,X1) )).

cnf(u934,axiom,
    ( sK2(X1,X0,k2_tarski(X0,X0)) = X1
    | k2_tarski(X0,X0) = k2_tarski(X1,X0) )).

cnf(u651,axiom,
    ( sK2(X0,X1,k2_tarski(X1,X0)) = X1
    | sK2(X0,X1,k2_tarski(X1,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

cnf(u651_019,axiom,
    ( sK2(X0,X1,k2_tarski(X1,X0)) = X1
    | sK2(X0,X1,k2_tarski(X1,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

cnf(u784,axiom,
    ( sK2(X1,X0,k2_tarski(X0,X1)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

cnf(u170,axiom,
    ( sK2(X0,X1,k2_tarski(X1,X2)) = X0
    | sK2(X0,X1,k2_tarski(X1,X2)) = X1
    | sK2(X0,X1,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u1758,axiom,
    ( sK2(X4,X2,k2_tarski(X2,X3)) = X4
    | sK2(X4,X2,k2_tarski(X2,X3)) = X3
    | k2_tarski(X2,X3) = k2_tarski(X4,X2) )).

cnf(u170_020,axiom,
    ( sK2(X0,X1,k2_tarski(X1,X2)) = X0
    | sK2(X0,X1,k2_tarski(X1,X2)) = X1
    | sK2(X0,X1,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u170_021,axiom,
    ( sK2(X0,X1,k2_tarski(X1,X2)) = X0
    | sK2(X0,X1,k2_tarski(X1,X2)) = X1
    | sK2(X0,X1,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u1758_022,axiom,
    ( sK2(X4,X2,k2_tarski(X2,X3)) = X4
    | sK2(X4,X2,k2_tarski(X2,X3)) = X3
    | k2_tarski(X2,X3) = k2_tarski(X4,X2) )).

cnf(u73,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | sK2(X0,X1,k2_tarski(X2,X3)) = X2
    | sK2(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u73_023,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | sK2(X0,X1,k2_tarski(X2,X3)) = X2
    | sK2(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u73_024,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | sK2(X0,X1,k2_tarski(X2,X3)) = X2
    | sK2(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u73_025,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | sK2(X0,X1,k2_tarski(X2,X3)) = X2
    | sK2(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u233,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X2)) = X1
    | sK2(X0,X1,k2_tarski(X2,X2)) = X0
    | sK2(X0,X1,k2_tarski(X2,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u233_026,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X2)) = X1
    | sK2(X0,X1,k2_tarski(X2,X2)) = X0
    | sK2(X0,X1,k2_tarski(X2,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u233_027,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X2)) = X1
    | sK2(X0,X1,k2_tarski(X2,X2)) = X0
    | sK2(X0,X1,k2_tarski(X2,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u172,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X1)) = X0
    | sK2(X0,X1,k2_tarski(X2,X1)) = X2
    | sK2(X0,X1,k2_tarski(X2,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u172_028,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X1)) = X0
    | sK2(X0,X1,k2_tarski(X2,X1)) = X2
    | sK2(X0,X1,k2_tarski(X2,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u1901,axiom,
    ( sK2(X2,X1,k2_tarski(X0,X1)) = X2
    | sK2(X2,X1,k2_tarski(X0,X1)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u172_029,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X1)) = X0
    | sK2(X0,X1,k2_tarski(X2,X1)) = X2
    | sK2(X0,X1,k2_tarski(X2,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u1901_030,axiom,
    ( sK2(X2,X1,k2_tarski(X0,X1)) = X2
    | sK2(X2,X1,k2_tarski(X0,X1)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u229,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X0)) = X1
    | sK2(X0,X1,k2_tarski(X2,X0)) = X2
    | sK2(X0,X1,k2_tarski(X2,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u229_031,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X0)) = X1
    | sK2(X0,X1,k2_tarski(X2,X0)) = X2
    | sK2(X0,X1,k2_tarski(X2,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u2064,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X0)) = X1
    | sK2(X0,X1,k2_tarski(X2,X0)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u229_032,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X0)) = X1
    | sK2(X0,X1,k2_tarski(X2,X0)) = X2
    | sK2(X0,X1,k2_tarski(X2,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u2064_033,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X0)) = X1
    | sK2(X0,X1,k2_tarski(X2,X0)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u68,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) )).

cnf(u4688,axiom,
    ( X2 != X3
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X4,X5,k2_tarski(X2,X3)),k2_tarski(X2,X3)) = X2
    | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X4,X5,k2_tarski(X2,X3)))
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X3)
    | sK2(X4,X5,k2_tarski(X2,X3)) = X5
    | sK2(X4,X5,k2_tarski(X2,X3)) = X4
    | k2_tarski(X2,X3) = k2_tarski(X4,X5) )).

cnf(u4687,axiom,
    ( X2 != X3
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X4,X5,k2_tarski(X2,X3)),k2_tarski(X2,X3)) = X3
    | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X4,X5,k2_tarski(X2,X3)))
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X3)
    | sK2(X4,X5,k2_tarski(X2,X3)) = X5
    | sK2(X4,X5,k2_tarski(X2,X3)) = X4
    | k2_tarski(X2,X3) = k2_tarski(X4,X5) )).

cnf(u4206,axiom,
    ( X2 != X3
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X0,X1,k2_tarski(X2,X3)),k2_tarski(X2,X3)) = X2
    | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X0,X1,k2_tarski(X2,X3)))
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u4205,axiom,
    ( X2 != X3
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X0,X1,k2_tarski(X2,X3)),k2_tarski(X2,X3)) = X3
    | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X0,X1,k2_tarski(X2,X3)))
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u3910,axiom,
    ( X0 != X3
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X3)),k2_tarski(X3,X3)) = X0
    | k2_tarski(X3,X3) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X3)))
    | sK2(X1,X2,k2_tarski(X3,X3)) = X2
    | sK2(X1,X2,k2_tarski(X3,X3)) = X1
    | k2_tarski(X1,X2) = k2_tarski(X3,X3) )).

cnf(u3909,axiom,
    ( X0 != X3
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X3)),k2_tarski(X3,X3)) = X3
    | k2_tarski(X3,X3) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X3)))
    | sK2(X1,X2,k2_tarski(X3,X3)) = X2
    | sK2(X1,X2,k2_tarski(X3,X3)) = X1
    | k2_tarski(X1,X2) = k2_tarski(X3,X3) )).

cnf(u3624,axiom,
    ( X2 != X3
    | sK2(sK2(X0,X1,k2_tarski(X2,X2)),X3,k2_tarski(X2,X2)) = X3
    | k2_tarski(X2,X2) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X2)),X3)
    | sK2(X0,X1,k2_tarski(X2,X2)) = X1
    | sK2(X0,X1,k2_tarski(X2,X2)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u3623,axiom,
    ( X2 != X3
    | sK2(sK2(X0,X1,k2_tarski(X2,X2)),X3,k2_tarski(X2,X2)) = X2
    | k2_tarski(X2,X2) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X2)),X3)
    | sK2(X0,X1,k2_tarski(X2,X2)) = X1
    | sK2(X0,X1,k2_tarski(X2,X2)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u2948,axiom,
    ( X138 != X139
    | k2_tarski(X138,X139) = k2_tarski(X139,sK2(X136,X137,k2_tarski(X138,X139)))
    | ~ r2_hidden(X139,k2_tarski(X138,X139))
    | sK2(X136,X137,k2_tarski(X138,X139)) = X137
    | sK2(X136,X137,k2_tarski(X138,X139)) = X136
    | k2_tarski(X136,X137) = k2_tarski(X138,X139) )).

cnf(u2696,axiom,
    ( X127 != X128
    | k2_tarski(X127,X128) = k2_tarski(X127,sK2(X125,X126,k2_tarski(X127,X128)))
    | ~ r2_hidden(X127,k2_tarski(X127,X128))
    | sK2(X125,X126,k2_tarski(X127,X128)) = X126
    | sK2(X125,X126,k2_tarski(X127,X128)) = X125
    | k2_tarski(X125,X126) = k2_tarski(X127,X128) )).

cnf(u2364,axiom,
    ( X99 != X100
    | k2_tarski(X99,X100) = k2_tarski(X101,X99)
    | ~ r2_hidden(X99,k2_tarski(X101,X99))
    | sK2(X99,X100,k2_tarski(X101,X99)) = X101 )).

cnf(u2349,axiom,
    ( X99 != X101
    | k2_tarski(X99,X100) = k2_tarski(X101,X99)
    | ~ r2_hidden(X99,k2_tarski(X101,X99))
    | sK2(X99,X100,k2_tarski(X101,X99)) = X100 )).

cnf(u2347,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X2,X0)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u2346,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X2,X0)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u2203,axiom,
    ( X92 != X93
    | k2_tarski(X92,X93) = k2_tarski(X92,X94)
    | ~ r2_hidden(X92,k2_tarski(X92,X94))
    | sK2(X92,X93,k2_tarski(X92,X94)) = X94 )).

cnf(u2188,axiom,
    ( X92 != X94
    | k2_tarski(X92,X93) = k2_tarski(X92,X94)
    | ~ r2_hidden(X92,k2_tarski(X92,X94))
    | sK2(X92,X93,k2_tarski(X92,X94)) = X93 )).

cnf(u2186,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X0,X2)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u2185,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X0,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u2058,axiom,
    ( X91 != X92
    | k2_tarski(X93,X92) = k2_tarski(X91,X92)
    | ~ r2_hidden(X92,k2_tarski(X93,X92))
    | sK2(X91,X92,k2_tarski(X93,X92)) = X93 )).

cnf(u2044,axiom,
    ( X92 != X93
    | k2_tarski(X93,X92) = k2_tarski(X91,X92)
    | ~ r2_hidden(X92,k2_tarski(X93,X92))
    | sK2(X91,X92,k2_tarski(X93,X92)) = X91 )).

cnf(u2043,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X2,X1)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u2042,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X2,X1)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u1891,axiom,
    ( X90 != X91
    | k2_tarski(X90,X91) = k2_tarski(X91,X92)
    | ~ r2_hidden(X91,k2_tarski(X91,X92))
    | sK2(X90,X91,k2_tarski(X91,X92)) = X92 )).

cnf(u1877,axiom,
    ( X91 != X92
    | k2_tarski(X90,X91) = k2_tarski(X91,X92)
    | ~ r2_hidden(X91,k2_tarski(X91,X92))
    | sK2(X90,X91,k2_tarski(X91,X92)) = X90 )).

cnf(u1876,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X1,X2)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u1875,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u1733,axiom,
    ( X62 != X63
    | k2_tarski(X62,X62) = k2_tarski(X62,X63)
    | ~ r2_hidden(X62,k2_tarski(X62,X62)) )).

cnf(u1676,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X0,X0)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X0,X0) )).

cnf(u1675,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X0,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X0,X0) )).

cnf(u1520,axiom,
    ( X3 != X4
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X0
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X3
    | k2_tarski(X3,X4) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X4)))
    | sK2(X1,X2,k2_tarski(X3,X4)) = X2
    | sK2(X1,X2,k2_tarski(X3,X4)) = X1
    | k2_tarski(X1,X2) = k2_tarski(X3,X4) )).

cnf(u1519,axiom,
    ( X0 != X4
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X0
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X3
    | k2_tarski(X3,X4) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X4)))
    | sK2(X1,X2,k2_tarski(X3,X4)) = X2
    | sK2(X1,X2,k2_tarski(X3,X4)) = X1
    | k2_tarski(X1,X2) = k2_tarski(X3,X4) )).

cnf(u1518,axiom,
    ( X3 != X4
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X0
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X4
    | k2_tarski(X3,X4) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X4)))
    | sK2(X1,X2,k2_tarski(X3,X4)) = X2
    | sK2(X1,X2,k2_tarski(X3,X4)) = X1
    | k2_tarski(X1,X2) = k2_tarski(X3,X4) )).

cnf(u1517,axiom,
    ( X0 != X3
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X0
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X4
    | k2_tarski(X3,X4) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X4)))
    | sK2(X1,X2,k2_tarski(X3,X4)) = X2
    | sK2(X1,X2,k2_tarski(X3,X4)) = X1
    | k2_tarski(X1,X2) = k2_tarski(X3,X4) )).

cnf(u1516,axiom,
    ( X0 != X4
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X3
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X4
    | k2_tarski(X3,X4) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X4)))
    | sK2(X1,X2,k2_tarski(X3,X4)) = X2
    | sK2(X1,X2,k2_tarski(X3,X4)) = X1
    | k2_tarski(X1,X2) = k2_tarski(X3,X4) )).

cnf(u1515,axiom,
    ( X0 != X3
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X3
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X4
    | k2_tarski(X3,X4) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X4)))
    | sK2(X1,X2,k2_tarski(X3,X4)) = X2
    | sK2(X1,X2,k2_tarski(X3,X4)) = X1
    | k2_tarski(X1,X2) = k2_tarski(X3,X4) )).

cnf(u1264,axiom,
    ( X52 != X53
    | k2_tarski(X53,X53) = k2_tarski(X52,X53)
    | ~ r2_hidden(X53,k2_tarski(X53,X53)) )).

cnf(u1154,axiom,
    ( X2 != X3
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X4
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X2
    | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),X4)
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u1153,axiom,
    ( X3 != X4
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X4
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X2
    | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),X4)
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u1152,axiom,
    ( X2 != X3
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X4
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X3
    | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),X4)
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u1151,axiom,
    ( X2 != X4
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X4
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X3
    | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),X4)
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u1150,axiom,
    ( X3 != X4
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X2
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X3
    | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),X4)
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u1149,axiom,
    ( X2 != X4
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X2
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X3
    | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),X4)
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u921,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X1,X1)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X1,X1) )).

cnf(u920,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X1,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X1,X1) )).

cnf(u773,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X2,X2)) = X1
    | sK2(X0,X1,k2_tarski(X2,X2)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u772,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X2,X2)) = X1
    | sK2(X0,X1,k2_tarski(X2,X2)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u771,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X2,X2)) = X1
    | sK2(X0,X1,k2_tarski(X2,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u770,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X2,X2)) = X1
    | sK2(X0,X1,k2_tarski(X2,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u769,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X2,X2)) = X0
    | sK2(X0,X1,k2_tarski(X2,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u768,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X2,X2)) = X0
    | sK2(X0,X1,k2_tarski(X2,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u681,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X1,X0)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

cnf(u680,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X1,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

cnf(u640,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X2,X0)) = X1
    | sK2(X0,X1,k2_tarski(X2,X0)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u639,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X2,X0)) = X1
    | sK2(X0,X1,k2_tarski(X2,X0)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u638,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X2,X0)) = X1
    | sK2(X0,X1,k2_tarski(X2,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u637,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X2,X0)) = X1
    | sK2(X0,X1,k2_tarski(X2,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u636,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X2,X0)) = X2
    | sK2(X0,X1,k2_tarski(X2,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u635,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X2,X0)) = X2
    | sK2(X0,X1,k2_tarski(X2,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u548,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X0,X2)) = X1
    | sK2(X0,X1,k2_tarski(X0,X2)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u547,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X0,X2)) = X1
    | sK2(X0,X1,k2_tarski(X0,X2)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u546,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X0,X2)) = X1
    | sK2(X0,X1,k2_tarski(X0,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u545,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X0,X2)) = X1
    | sK2(X0,X1,k2_tarski(X0,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u544,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X0,X2)) = X0
    | sK2(X0,X1,k2_tarski(X0,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u543,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X0,X2)) = X0
    | sK2(X0,X1,k2_tarski(X0,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u466,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X2,X1)) = X0
    | sK2(X0,X1,k2_tarski(X2,X1)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u465,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X2,X1)) = X0
    | sK2(X0,X1,k2_tarski(X2,X1)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u464,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X2,X1)) = X0
    | sK2(X0,X1,k2_tarski(X2,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u463,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X2,X1)) = X0
    | sK2(X0,X1,k2_tarski(X2,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u462,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X2,X1)) = X2
    | sK2(X0,X1,k2_tarski(X2,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u461,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X2,X1)) = X2
    | sK2(X0,X1,k2_tarski(X2,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u394,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X1,X2)) = X0
    | sK2(X0,X1,k2_tarski(X1,X2)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u393,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X1,X2)) = X0
    | sK2(X0,X1,k2_tarski(X1,X2)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u392,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X1,X2)) = X0
    | sK2(X0,X1,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u391,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X1,X2)) = X0
    | sK2(X0,X1,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u390,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X1,X2)) = X1
    | sK2(X0,X1,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u389,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X1,X2)) = X1
    | sK2(X0,X1,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u326,axiom,
    ( X0 != X1
    | sK2(X0,X0,k2_tarski(X1,X1)) = X0
    | k2_tarski(X0,X0) = k2_tarski(X1,X1) )).

cnf(u325,axiom,
    ( X0 != X1
    | sK2(X0,X0,k2_tarski(X1,X1)) = X1
    | k2_tarski(X0,X0) = k2_tarski(X1,X1) )).

cnf(u292,axiom,
    ( X12 != X13
    | k2_tarski(X12,X12) = k2_tarski(X13,X12)
    | ~ r2_hidden(X12,k2_tarski(X13,X12)) )).

cnf(u259,axiom,
    ( X0 != X1
    | sK2(X0,X0,k2_tarski(X1,X0)) = X1
    | k2_tarski(X0,X0) = k2_tarski(X1,X0) )).

cnf(u258,axiom,
    ( X0 != X1
    | sK2(X0,X0,k2_tarski(X1,X0)) = X0
    | k2_tarski(X0,X0) = k2_tarski(X1,X0) )).

cnf(u225,axiom,
    ( X12 != X13
    | k2_tarski(X12,X12) = k2_tarski(X12,X13)
    | ~ r2_hidden(X12,k2_tarski(X12,X13)) )).

cnf(u196,axiom,
    ( X0 != X1
    | sK2(X0,X0,k2_tarski(X0,X1)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X0,X0) )).

cnf(u195,axiom,
    ( X0 != X1
    | sK2(X0,X0,k2_tarski(X0,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X0,X0) )).

cnf(u159,axiom,
    ( X1 != X2
    | sK2(X0,X0,k2_tarski(X1,X2)) = X0
    | sK2(X0,X0,k2_tarski(X1,X2)) = X1
    | k2_tarski(X0,X0) = k2_tarski(X1,X2) )).

cnf(u158,axiom,
    ( X0 != X2
    | sK2(X0,X0,k2_tarski(X1,X2)) = X0
    | sK2(X0,X0,k2_tarski(X1,X2)) = X1
    | k2_tarski(X0,X0) = k2_tarski(X1,X2) )).

cnf(u157,axiom,
    ( X1 != X2
    | sK2(X0,X0,k2_tarski(X1,X2)) = X0
    | sK2(X0,X0,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X0) = k2_tarski(X1,X2) )).

cnf(u156,axiom,
    ( X0 != X1
    | sK2(X0,X0,k2_tarski(X1,X2)) = X0
    | sK2(X0,X0,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X0) = k2_tarski(X1,X2) )).

cnf(u155,axiom,
    ( X0 != X2
    | sK2(X0,X0,k2_tarski(X1,X2)) = X1
    | sK2(X0,X0,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X0) = k2_tarski(X1,X2) )).

cnf(u154,axiom,
    ( X0 != X1
    | sK2(X0,X0,k2_tarski(X1,X2)) = X1
    | sK2(X0,X0,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X0) = k2_tarski(X1,X2) )).

cnf(u109,axiom,
    ( X2 != X3
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | sK2(X0,X1,k2_tarski(X2,X3)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u108,axiom,
    ( X0 != X3
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | sK2(X0,X1,k2_tarski(X2,X3)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u107,axiom,
    ( X1 != X3
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | sK2(X0,X1,k2_tarski(X2,X3)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u106,axiom,
    ( X2 != X3
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | sK2(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u105,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | sK2(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u104,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | sK2(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u103,axiom,
    ( X0 != X3
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X2
    | sK2(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u102,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X2
    | sK2(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u101,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X2
    | sK2(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u100,axiom,
    ( X1 != X3
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | sK2(X0,X1,k2_tarski(X2,X3)) = X2
    | sK2(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u99,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | sK2(X0,X1,k2_tarski(X2,X3)) = X2
    | sK2(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u98,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | sK2(X0,X1,k2_tarski(X2,X3)) = X2
    | sK2(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u70,negated_conjecture,
    ( sK1 != k2_yellow_0(sK0,k2_tarski(sK1,sK1))
    | sK1 != k1_yellow_0(sK0,k2_tarski(sK1,sK1)) )).

cnf(u3641,axiom,
    ( sK2(X160,X161,k2_tarski(X162,X162)) != X163
    | k2_tarski(X162,X162) = k2_tarski(sK2(X160,X161,k2_tarski(X162,X162)),X163)
    | ~ r2_hidden(sK2(X160,X161,k2_tarski(X162,X162)),k2_tarski(X162,X162))
    | sK2(sK2(X160,X161,k2_tarski(X162,X162)),X163,k2_tarski(X162,X162)) = X162
    | sK2(X160,X161,k2_tarski(X162,X162)) = X161
    | sK2(X160,X161,k2_tarski(X162,X162)) = X160
    | k2_tarski(X160,X161) = k2_tarski(X162,X162) )).

cnf(u3930,axiom,
    ( sK2(X172,X173,k2_tarski(X174,X174)) != X171
    | k2_tarski(X174,X174) = k2_tarski(X171,sK2(X172,X173,k2_tarski(X174,X174)))
    | ~ r2_hidden(sK2(X172,X173,k2_tarski(X174,X174)),k2_tarski(X174,X174))
    | sK2(X171,sK2(X172,X173,k2_tarski(X174,X174)),k2_tarski(X174,X174)) = X174
    | sK2(X172,X173,k2_tarski(X174,X174)) = X173
    | sK2(X172,X173,k2_tarski(X174,X174)) = X172
    | k2_tarski(X172,X173) = k2_tarski(X174,X174) )).

cnf(u1163,axiom,
    ( sK2(X67,X68,k2_tarski(X69,X70)) != X71
    | k2_tarski(X69,X70) = k2_tarski(sK2(X67,X68,k2_tarski(X69,X70)),X71)
    | ~ r2_hidden(sK2(X67,X68,k2_tarski(X69,X70)),k2_tarski(X69,X70))
    | sK2(sK2(X67,X68,k2_tarski(X69,X70)),X71,k2_tarski(X69,X70)) = X69
    | sK2(sK2(X67,X68,k2_tarski(X69,X70)),X71,k2_tarski(X69,X70)) = X70
    | sK2(X67,X68,k2_tarski(X69,X70)) = X68
    | sK2(X67,X68,k2_tarski(X69,X70)) = X67
    | k2_tarski(X69,X70) = k2_tarski(X67,X68) )).

cnf(u1536,axiom,
    ( sK2(X85,X86,k2_tarski(X87,X88)) != X84
    | k2_tarski(X87,X88) = k2_tarski(X84,sK2(X85,X86,k2_tarski(X87,X88)))
    | ~ r2_hidden(sK2(X85,X86,k2_tarski(X87,X88)),k2_tarski(X87,X88))
    | sK2(X84,sK2(X85,X86,k2_tarski(X87,X88)),k2_tarski(X87,X88)) = X87
    | sK2(X84,sK2(X85,X86,k2_tarski(X87,X88)),k2_tarski(X87,X88)) = X88
    | sK2(X85,X86,k2_tarski(X87,X88)) = X86
    | sK2(X85,X86,k2_tarski(X87,X88)) = X85
    | k2_tarski(X85,X86) = k2_tarski(X87,X88) )).

cnf(u61,axiom,
    ( sK2(X0,X1,X2) != X0
    | k2_tarski(X0,X1) = X2
    | ~ r2_hidden(X0,X2) )).

cnf(u60,axiom,
    ( sK2(X0,X1,X2) != X1
    | k2_tarski(X0,X1) = X2
    | ~ r2_hidden(X1,X2) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:30:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.52  % (6914)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (6932)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.27/0.53  % (6915)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.27/0.53  % (6921)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.27/0.54  % (6924)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.27/0.54  % (6917)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.27/0.54  % (6913)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.27/0.54  % (6918)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.27/0.54  % (6914)Refutation not found, incomplete strategy% (6914)------------------------------
% 1.27/0.54  % (6914)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.54  % (6914)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.54  
% 1.27/0.54  % (6914)Memory used [KB]: 1791
% 1.27/0.54  % (6914)Time elapsed: 0.116 s
% 1.27/0.54  % (6914)------------------------------
% 1.27/0.54  % (6914)------------------------------
% 1.27/0.54  % (6911)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.27/0.54  % (6919)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.27/0.54  % (6933)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.27/0.54  % (6912)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.27/0.54  % (6939)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.27/0.54  % (6939)Refutation not found, incomplete strategy% (6939)------------------------------
% 1.27/0.54  % (6939)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.54  % (6939)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.54  
% 1.27/0.54  % (6939)Memory used [KB]: 1663
% 1.27/0.54  % (6939)Time elapsed: 0.127 s
% 1.27/0.54  % (6939)------------------------------
% 1.27/0.54  % (6939)------------------------------
% 1.27/0.54  % (6922)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.27/0.54  % (6929)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.27/0.55  % (6922)Refutation not found, incomplete strategy% (6922)------------------------------
% 1.27/0.55  % (6922)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.55  % (6937)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.27/0.55  % (6922)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.55  
% 1.27/0.55  % (6922)Memory used [KB]: 10618
% 1.27/0.55  % (6922)Time elapsed: 0.130 s
% 1.27/0.55  % (6922)------------------------------
% 1.27/0.55  % (6922)------------------------------
% 1.27/0.55  % (6911)Refutation not found, incomplete strategy% (6911)------------------------------
% 1.27/0.55  % (6911)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.55  % (6911)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.55  
% 1.27/0.55  % (6911)Memory used [KB]: 1663
% 1.27/0.55  % (6911)Time elapsed: 0.126 s
% 1.27/0.55  % (6911)------------------------------
% 1.27/0.55  % (6911)------------------------------
% 1.27/0.55  % (6930)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.27/0.55  % (6937)Refutation not found, incomplete strategy% (6937)------------------------------
% 1.27/0.55  % (6937)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.55  % (6937)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.55  
% 1.27/0.55  % (6937)Memory used [KB]: 6140
% 1.27/0.55  % (6937)Time elapsed: 0.126 s
% 1.27/0.55  % (6937)------------------------------
% 1.27/0.55  % (6937)------------------------------
% 1.27/0.55  % (6935)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.27/0.55  % (6920)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.27/0.55  % (6910)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.27/0.55  % (6923)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.27/0.55  % (6934)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.27/0.55  % (6931)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.27/0.55  % (6936)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.27/0.55  % (6938)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.27/0.55  % (6934)Refutation not found, incomplete strategy% (6934)------------------------------
% 1.27/0.55  % (6934)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.55  % (6934)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.55  
% 1.27/0.55  % (6934)Memory used [KB]: 10746
% 1.27/0.55  % (6934)Time elapsed: 0.140 s
% 1.27/0.55  % (6934)------------------------------
% 1.27/0.55  % (6934)------------------------------
% 1.27/0.55  % (6916)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.27/0.55  % (6926)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.27/0.55  % (6927)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.27/0.56  % (6938)Refutation not found, incomplete strategy% (6938)------------------------------
% 1.27/0.56  % (6938)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.56  % (6938)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.56  
% 1.27/0.56  % (6938)Memory used [KB]: 10746
% 1.27/0.56  % (6938)Time elapsed: 0.138 s
% 1.27/0.56  % (6938)------------------------------
% 1.27/0.56  % (6938)------------------------------
% 1.27/0.56  % (6927)Refutation not found, incomplete strategy% (6927)------------------------------
% 1.27/0.56  % (6927)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.56  % (6927)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.56  
% 1.27/0.56  % (6927)Memory used [KB]: 1663
% 1.27/0.56  % (6927)Time elapsed: 0.134 s
% 1.27/0.56  % (6927)------------------------------
% 1.27/0.56  % (6927)------------------------------
% 1.27/0.56  % (6928)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.55/0.56  % (6920)Refutation not found, incomplete strategy% (6920)------------------------------
% 1.55/0.56  % (6920)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.56  % (6926)Refutation not found, incomplete strategy% (6926)------------------------------
% 1.55/0.56  % (6926)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.56  % (6926)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.56  
% 1.55/0.56  % (6926)Memory used [KB]: 10618
% 1.55/0.56  % (6926)Time elapsed: 0.148 s
% 1.55/0.56  % (6926)------------------------------
% 1.55/0.56  % (6926)------------------------------
% 1.55/0.57  % (6920)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.57  
% 1.55/0.57  % (6920)Memory used [KB]: 10746
% 1.55/0.57  % (6920)Time elapsed: 0.151 s
% 1.55/0.57  % (6920)------------------------------
% 1.55/0.57  % (6920)------------------------------
% 1.55/0.57  % (6925)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 2.02/0.66  % (6913)Refutation not found, incomplete strategy% (6913)------------------------------
% 2.02/0.66  % (6913)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.02/0.66  % (6913)Termination reason: Refutation not found, incomplete strategy
% 2.02/0.66  
% 2.02/0.66  % (6913)Memory used [KB]: 6140
% 2.02/0.66  % (6913)Time elapsed: 0.239 s
% 2.02/0.66  % (6913)------------------------------
% 2.02/0.66  % (6913)------------------------------
% 2.02/0.66  % (6989)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.02/0.67  % (6981)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.02/0.67  % (6979)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.02/0.68  % (6984)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.22/0.68  % (6983)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.22/0.68  % (6983)Refutation not found, incomplete strategy% (6983)------------------------------
% 2.22/0.68  % (6983)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.68  % (6983)Termination reason: Refutation not found, incomplete strategy
% 2.22/0.68  
% 2.22/0.68  % (6983)Memory used [KB]: 6140
% 2.22/0.68  % (6983)Time elapsed: 0.104 s
% 2.22/0.68  % (6983)------------------------------
% 2.22/0.68  % (6983)------------------------------
% 2.22/0.68  % (6987)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.22/0.69  % (6992)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.22/0.69  % (6987)Refutation not found, incomplete strategy% (6987)------------------------------
% 2.22/0.69  % (6987)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.69  % (6987)Termination reason: Refutation not found, incomplete strategy
% 2.22/0.69  
% 2.22/0.69  % (6987)Memory used [KB]: 10746
% 2.22/0.69  % (6987)Time elapsed: 0.097 s
% 2.22/0.69  % (6987)------------------------------
% 2.22/0.69  % (6987)------------------------------
% 2.22/0.69  % (6984)Refutation not found, incomplete strategy% (6984)------------------------------
% 2.22/0.69  % (6984)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.69  % (6984)Termination reason: Refutation not found, incomplete strategy
% 2.22/0.69  
% 2.22/0.69  % (6984)Memory used [KB]: 10746
% 2.22/0.69  % (6984)Time elapsed: 0.102 s
% 2.22/0.69  % (6984)------------------------------
% 2.22/0.69  % (6984)------------------------------
% 2.22/0.69  % (6990)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.22/0.70  % (6990)Refutation not found, incomplete strategy% (6990)------------------------------
% 2.22/0.70  % (6990)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.70  % (6912)Refutation not found, incomplete strategy% (6912)------------------------------
% 2.22/0.70  % (6912)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.70  % (6912)Termination reason: Refutation not found, incomplete strategy
% 2.22/0.70  
% 2.22/0.70  % (6912)Memory used [KB]: 6268
% 2.22/0.70  % (6912)Time elapsed: 0.261 s
% 2.22/0.70  % (6912)------------------------------
% 2.22/0.70  % (6912)------------------------------
% 2.22/0.70  % (6995)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.22/0.70  % (6990)Termination reason: Refutation not found, incomplete strategy
% 2.22/0.70  
% 2.22/0.70  % (6990)Memory used [KB]: 10746
% 2.22/0.70  % (6990)Time elapsed: 0.108 s
% 2.22/0.70  % (6990)------------------------------
% 2.22/0.70  % (6990)------------------------------
% 2.22/0.70  % (6999)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 2.22/0.71  % (6999)Refutation not found, incomplete strategy% (6999)------------------------------
% 2.22/0.71  % (6999)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.71  % (6999)Termination reason: Refutation not found, incomplete strategy
% 2.22/0.71  
% 2.22/0.71  % (6999)Memory used [KB]: 10746
% 2.22/0.71  % (6999)Time elapsed: 0.100 s
% 2.22/0.71  % (6999)------------------------------
% 2.22/0.71  % (6999)------------------------------
% 2.77/0.80  % (7050)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 2.77/0.81  % (7079)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 2.77/0.81  % (7071)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 3.07/0.82  % (7072)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 3.07/0.82  % (7070)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 3.07/0.83  % (7077)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 3.07/0.85  % (7085)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 3.27/0.89  % (6995)Refutation not found, incomplete strategy% (6995)------------------------------
% 3.27/0.89  % (6995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.27/0.89  % (6995)Termination reason: Refutation not found, incomplete strategy
% 3.27/0.89  
% 3.27/0.89  % (6995)Memory used [KB]: 6268
% 3.27/0.89  % (6995)Time elapsed: 0.286 s
% 3.27/0.89  % (6995)------------------------------
% 3.27/0.89  % (6995)------------------------------
% 3.27/0.93  % (7079)Refutation not found, incomplete strategy% (7079)------------------------------
% 3.27/0.93  % (7079)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.27/0.93  % (7079)Termination reason: Refutation not found, incomplete strategy
% 3.27/0.93  
% 3.27/0.93  % (7079)Memory used [KB]: 6268
% 3.27/0.93  % (7079)Time elapsed: 0.166 s
% 3.27/0.93  % (7079)------------------------------
% 3.27/0.93  % (7079)------------------------------
% 3.27/0.94  % (7077)Refutation not found, incomplete strategy% (7077)------------------------------
% 3.27/0.94  % (7077)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.85/0.95  % (7077)Termination reason: Refutation not found, incomplete strategy
% 3.85/0.95  
% 3.85/0.95  % (7077)Memory used [KB]: 6268
% 3.85/0.95  % (7077)Time elapsed: 0.202 s
% 3.85/0.95  % (7077)------------------------------
% 3.85/0.95  % (7077)------------------------------
% 3.85/0.96  % (6916)Time limit reached!
% 3.85/0.96  % (6916)------------------------------
% 3.85/0.96  % (6916)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.85/0.96  % (6916)Termination reason: Time limit
% 3.85/0.96  
% 3.85/0.96  % (6916)Memory used [KB]: 12281
% 3.85/0.96  % (6916)Time elapsed: 0.511 s
% 3.85/0.96  % (6916)------------------------------
% 3.85/0.96  % (6916)------------------------------
% 3.85/0.97  % (6924)Time limit reached!
% 3.85/0.97  % (6924)------------------------------
% 3.85/0.97  % (6924)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.85/0.97  % (6924)Termination reason: Time limit
% 3.85/0.97  
% 3.85/0.97  % (6924)Memory used [KB]: 4605
% 3.85/0.97  % (6924)Time elapsed: 0.516 s
% 3.85/0.97  % (6924)------------------------------
% 3.85/0.97  % (6924)------------------------------
% 4.10/1.02  % (7141)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 4.10/1.03  % (7161)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 5.47/1.06  % (7174)dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 5.47/1.06  % (7181)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 5.99/1.12  % (7072)Time limit reached!
% 5.99/1.12  % (7072)------------------------------
% 5.99/1.12  % (7072)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.99/1.13  % (7072)Termination reason: Time limit
% 5.99/1.13  % (7072)Termination phase: Saturation
% 5.99/1.13  
% 5.99/1.13  % (7072)Memory used [KB]: 12792
% 5.99/1.13  % (7072)Time elapsed: 0.410 s
% 5.99/1.13  % (7072)------------------------------
% 5.99/1.13  % (7072)------------------------------
% 5.99/1.13  % (6917)Time limit reached!
% 5.99/1.13  % (6917)------------------------------
% 5.99/1.13  % (6917)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.99/1.14  % (7161)Refutation not found, incomplete strategy% (7161)------------------------------
% 5.99/1.14  % (7161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.99/1.14  % (6917)Termination reason: Time limit
% 5.99/1.14  % (6917)Termination phase: Saturation
% 5.99/1.14  
% 5.99/1.14  % (6917)Memory used [KB]: 3198
% 5.99/1.14  % (6917)Time elapsed: 0.600 s
% 5.99/1.14  % (6917)------------------------------
% 5.99/1.14  % (6917)------------------------------
% 5.99/1.14  % (7161)Termination reason: Refutation not found, incomplete strategy
% 5.99/1.14  
% 5.99/1.14  % (7161)Memory used [KB]: 6268
% 5.99/1.14  % (7161)Time elapsed: 0.184 s
% 5.99/1.14  % (7161)------------------------------
% 5.99/1.14  % (7161)------------------------------
% 6.93/1.24  % (7085)Time limit reached!
% 6.93/1.24  % (7085)------------------------------
% 6.93/1.24  % (7085)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.93/1.25  % (7085)Termination reason: Time limit
% 6.93/1.25  
% 6.93/1.25  % (7085)Memory used [KB]: 8187
% 6.93/1.25  % (7085)Time elapsed: 0.512 s
% 6.93/1.25  % (7085)------------------------------
% 6.93/1.25  % (7085)------------------------------
% 7.61/1.34  % (7141)Time limit reached!
% 7.61/1.34  % (7141)------------------------------
% 7.61/1.34  % (7141)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.61/1.34  % (7141)Termination reason: Time limit
% 7.61/1.34  
% 7.61/1.34  % (7141)Memory used [KB]: 6908
% 7.61/1.34  % (7141)Time elapsed: 0.423 s
% 7.61/1.34  % (7141)------------------------------
% 7.61/1.34  % (7141)------------------------------
% 7.83/1.39  % (7181)Time limit reached!
% 7.83/1.39  % (7181)------------------------------
% 7.83/1.39  % (7181)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.83/1.41  % (7174)Time limit reached!
% 7.83/1.41  % (7174)------------------------------
% 7.83/1.41  % (7174)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.83/1.41  % (7174)Termination reason: Time limit
% 7.83/1.41  % (7174)Termination phase: Saturation
% 7.83/1.41  
% 7.83/1.41  % (7174)Memory used [KB]: 4221
% 7.83/1.41  % (7174)Time elapsed: 0.400 s
% 7.83/1.41  % (7174)------------------------------
% 7.83/1.41  % (7174)------------------------------
% 7.83/1.41  % (7181)Termination reason: Time limit
% 7.83/1.41  % (7181)Termination phase: Saturation
% 7.83/1.41  
% 7.83/1.41  % (7181)Memory used [KB]: 7803
% 7.83/1.41  % (7181)Time elapsed: 0.400 s
% 7.83/1.41  % (7181)------------------------------
% 7.83/1.41  % (7181)------------------------------
% 8.79/1.50  % SZS status CounterSatisfiable for theBenchmark
% 8.79/1.50  % (6915)# SZS output start Saturation.
% 8.79/1.50  cnf(u35,negated_conjecture,
% 8.79/1.50      v5_orders_2(sK0)).
% 8.79/1.50  
% 8.79/1.50  cnf(u72,negated_conjecture,
% 8.79/1.50      r2_lattice3(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | k2_tarski(sK3(sK0,X0,X1),sK3(sK0,X0,X1)) = k6_domain_1(u1_struct_0(sK0),sK3(sK0,X0,X1)) | ~l1_struct_0(sK0)).
% 8.79/1.50  
% 8.79/1.50  cnf(u3117,axiom,
% 8.79/1.50      r2_lattice3(X7,k2_tarski(X6,X6),X8) | sK2(sK3(X7,k2_tarski(X6,X6),X8),sK2(X9,X10,k2_tarski(X6,X6)),k2_tarski(X6,X6)) = X6 | sK2(X9,X10,k2_tarski(X6,X6)) = X10 | sK2(X9,X10,k2_tarski(X6,X6)) = X9 | k2_tarski(X6,X6) = k2_tarski(X9,X10) | k2_tarski(X6,X6) = k2_tarski(sK3(X7,k2_tarski(X6,X6),X8),sK2(X9,X10,k2_tarski(X6,X6))) | ~m1_subset_1(X8,u1_struct_0(X7)) | ~l1_orders_2(X7)).
% 8.79/1.50  
% 8.79/1.50  cnf(u2564,axiom,
% 8.79/1.50      r2_lattice3(X16,k2_tarski(X15,X15),X17) | sK2(sK2(X13,X14,k2_tarski(X15,X15)),sK3(X16,k2_tarski(X15,X15),X17),k2_tarski(X15,X15)) = X15 | k2_tarski(X15,X15) = k2_tarski(sK2(X13,X14,k2_tarski(X15,X15)),sK3(X16,k2_tarski(X15,X15),X17)) | ~m1_subset_1(X17,u1_struct_0(X16)) | ~l1_orders_2(X16) | sK2(X13,X14,k2_tarski(X15,X15)) = X14 | sK2(X13,X14,k2_tarski(X15,X15)) = X13 | k2_tarski(X13,X14) = k2_tarski(X15,X15)).
% 8.79/1.50  
% 8.79/1.50  cnf(u2560,axiom,
% 8.79/1.50      r2_lattice3(X16,k2_tarski(X15,X15),X17) | sK2(sK3(X16,k2_tarski(X15,X15),X17),sK2(X13,X14,k2_tarski(X15,X15)),k2_tarski(X15,X15)) = X15 | k2_tarski(X15,X15) = k2_tarski(sK2(X13,X14,k2_tarski(X15,X15)),sK3(X16,k2_tarski(X15,X15),X17)) | ~m1_subset_1(X17,u1_struct_0(X16)) | ~l1_orders_2(X16) | sK2(X13,X14,k2_tarski(X15,X15)) = X14 | sK2(X13,X14,k2_tarski(X15,X15)) = X13 | k2_tarski(X13,X14) = k2_tarski(X15,X15)).
% 8.79/1.50  
% 8.79/1.50  cnf(u2404,axiom,
% 8.79/1.50      r2_lattice3(X13,k2_tarski(X12,X12),X14) | ~m1_subset_1(X14,u1_struct_0(X13)) | ~l1_orders_2(X13) | sK2(X10,X11,k2_tarski(X12,X12)) = sK3(X13,k2_tarski(X12,X12),X14) | sK3(X13,k2_tarski(X12,X12),X14) = X12 | sK2(X10,X11,k2_tarski(X12,X12)) = X11 | sK2(X10,X11,k2_tarski(X12,X12)) = X10 | k2_tarski(X10,X11) = k2_tarski(X12,X12)).
% 8.79/1.50  
% 8.79/1.50  cnf(u2214,axiom,
% 8.79/1.50      r2_lattice3(X5,k2_tarski(X6,X6),X7) | sK2(X4,sK3(X5,k2_tarski(X6,X6),X7),k2_tarski(X6,X6)) = X4 | sK2(X4,sK3(X5,k2_tarski(X6,X6),X7),k2_tarski(X6,X6)) = X6 | k2_tarski(X6,X6) = k2_tarski(X4,sK3(X5,k2_tarski(X6,X6),X7)) | ~m1_subset_1(X7,u1_struct_0(X5)) | ~l1_orders_2(X5)).
% 8.79/1.50  
% 8.79/1.50  cnf(u2209,axiom,
% 8.79/1.50      r2_lattice3(X5,k2_tarski(X4,X4),X6) | sK2(sK3(X5,k2_tarski(X4,X4),X6),X7,k2_tarski(X4,X4)) = X7 | sK2(sK3(X5,k2_tarski(X4,X4),X6),X7,k2_tarski(X4,X4)) = X4 | k2_tarski(X4,X4) = k2_tarski(sK3(X5,k2_tarski(X4,X4),X6),X7) | ~m1_subset_1(X6,u1_struct_0(X5)) | ~l1_orders_2(X5)).
% 8.79/1.50  
% 8.79/1.50  cnf(u1272,axiom,
% 8.79/1.50      r2_lattice3(X3,k2_tarski(X2,X2),X4) | k2_tarski(X2,X2) = k2_tarski(X2,sK3(X3,k2_tarski(X2,X2),X4)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~l1_orders_2(X3)).
% 8.79/1.50  
% 8.79/1.50  cnf(u338,axiom,
% 8.79/1.50      r2_lattice3(X2,k2_tarski(X3,X3),X4) | sK2(sK3(X2,k2_tarski(X3,X3),X4),sK3(X2,k2_tarski(X3,X3),X4),k2_tarski(X3,X3)) = X3 | k2_tarski(X3,X3) = k2_tarski(sK3(X2,k2_tarski(X3,X3),X4),sK3(X2,k2_tarski(X3,X3),X4)) | ~m1_subset_1(X4,u1_struct_0(X2)) | ~l1_orders_2(X2)).
% 8.79/1.50  
% 8.79/1.50  cnf(u3109,axiom,
% 8.79/1.50      r2_lattice3(X10,k2_tarski(X8,X9),X11) | sK2(sK3(X10,k2_tarski(X8,X9),X11),sK2(X12,X13,k2_tarski(X8,X9)),k2_tarski(X8,X9)) = X8 | sK2(sK3(X10,k2_tarski(X8,X9),X11),sK2(X12,X13,k2_tarski(X8,X9)),k2_tarski(X8,X9)) = X9 | sK2(X12,X13,k2_tarski(X8,X9)) = X13 | sK2(X12,X13,k2_tarski(X8,X9)) = X12 | k2_tarski(X8,X9) = k2_tarski(X12,X13) | k2_tarski(X8,X9) = k2_tarski(sK3(X10,k2_tarski(X8,X9),X11),sK2(X12,X13,k2_tarski(X8,X9))) | ~m1_subset_1(X11,u1_struct_0(X10)) | ~l1_orders_2(X10)).
% 8.79/1.50  
% 8.79/1.51  cnf(u3099,axiom,
% 8.79/1.51      r2_lattice3(X12,k2_tarski(X8,X9),X13) | sK2(sK2(X10,X11,k2_tarski(X8,X9)),sK3(X12,k2_tarski(X8,X9),X13),k2_tarski(X8,X9)) = X8 | sK2(sK2(X10,X11,k2_tarski(X8,X9)),sK3(X12,k2_tarski(X8,X9),X13),k2_tarski(X8,X9)) = X9 | sK2(X10,X11,k2_tarski(X8,X9)) = X11 | sK2(X10,X11,k2_tarski(X8,X9)) = X10 | k2_tarski(X10,X11) = k2_tarski(X8,X9) | k2_tarski(X8,X9) = k2_tarski(sK2(X10,X11,k2_tarski(X8,X9)),sK3(X12,k2_tarski(X8,X9),X13)) | ~m1_subset_1(X13,u1_struct_0(X12)) | ~l1_orders_2(X12)).
% 8.79/1.51  
% 8.79/1.51  cnf(u2561,axiom,
% 8.79/1.51      r2_lattice3(X2,k2_tarski(X1,X0),X3) | sK2(X0,sK3(X2,k2_tarski(X1,X0),X3),k2_tarski(X1,X0)) = X1 | k2_tarski(X1,X0) = k2_tarski(X0,sK3(X2,k2_tarski(X1,X0),X3)) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_orders_2(X2)).
% 8.79/1.51  
% 8.79/1.51  cnf(u2557,axiom,
% 8.79/1.51      r2_lattice3(X2,k2_tarski(X1,X0),X3) | sK2(sK3(X2,k2_tarski(X1,X0),X3),X0,k2_tarski(X1,X0)) = X1 | k2_tarski(X1,X0) = k2_tarski(X0,sK3(X2,k2_tarski(X1,X0),X3)) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_orders_2(X2)).
% 8.79/1.51  
% 8.79/1.51  cnf(u2218,axiom,
% 8.79/1.51      r2_lattice3(X5,k2_tarski(X4,X6),X7) | sK2(X4,sK3(X5,k2_tarski(X4,X6),X7),k2_tarski(X4,X6)) = X6 | k2_tarski(X4,X6) = k2_tarski(X4,sK3(X5,k2_tarski(X4,X6),X7)) | ~m1_subset_1(X7,u1_struct_0(X5)) | ~l1_orders_2(X5)).
% 8.79/1.51  
% 8.79/1.51  cnf(u1920,axiom,
% 8.79/1.51      r2_lattice3(X6,k2_tarski(X4,X5),X7) | sK2(sK3(X6,k2_tarski(X4,X5),X7),X4,k2_tarski(X4,X5)) = X5 | k2_tarski(X4,X5) = k2_tarski(X4,sK3(X6,k2_tarski(X4,X5),X7)) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~l1_orders_2(X6)).
% 8.79/1.51  
% 8.79/1.51  cnf(u1753,axiom,
% 8.79/1.51      r2_lattice3(X6,k2_tarski(X4,X5),X7) | sK2(sK3(X6,k2_tarski(X4,X5),X7),sK3(X6,k2_tarski(X4,X5),X7),k2_tarski(X4,X5)) = X4 | sK2(sK3(X6,k2_tarski(X4,X5),X7),sK3(X6,k2_tarski(X4,X5),X7),k2_tarski(X4,X5)) = X5 | k2_tarski(X4,X5) = k2_tarski(sK3(X6,k2_tarski(X4,X5),X7),sK3(X6,k2_tarski(X4,X5),X7)) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~l1_orders_2(X6)).
% 8.79/1.51  
% 8.79/1.51  cnf(u299,axiom,
% 8.79/1.51      r2_lattice3(X9,k2_tarski(X6,X7),X10) | sK2(X8,sK3(X9,k2_tarski(X6,X7),X10),k2_tarski(X6,X7)) = X8 | sK2(X8,sK3(X9,k2_tarski(X6,X7),X10),k2_tarski(X6,X7)) = X6 | sK2(X8,sK3(X9,k2_tarski(X6,X7),X10),k2_tarski(X6,X7)) = X7 | k2_tarski(X6,X7) = k2_tarski(X8,sK3(X9,k2_tarski(X6,X7),X10)) | ~m1_subset_1(X10,u1_struct_0(X9)) | ~l1_orders_2(X9)).
% 8.79/1.51  
% 8.79/1.51  cnf(u275,axiom,
% 8.79/1.51      r2_lattice3(X8,k2_tarski(X6,X7),X9) | sK2(sK3(X8,k2_tarski(X6,X7),X9),X10,k2_tarski(X6,X7)) = X10 | sK2(sK3(X8,k2_tarski(X6,X7),X9),X10,k2_tarski(X6,X7)) = X6 | sK2(sK3(X8,k2_tarski(X6,X7),X9),X10,k2_tarski(X6,X7)) = X7 | k2_tarski(X6,X7) = k2_tarski(sK3(X8,k2_tarski(X6,X7),X9),X10) | ~m1_subset_1(X9,u1_struct_0(X8)) | ~l1_orders_2(X8)).
% 8.79/1.51  
% 8.79/1.51  cnf(u71,axiom,
% 8.79/1.51      r2_lattice3(X0,k2_tarski(X1,X2),X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_orders_2(X0) | sK3(X0,k2_tarski(X1,X2),X3) = X1 | sK3(X0,k2_tarski(X1,X2),X3) = X2).
% 8.79/1.51  
% 8.79/1.51  cnf(u53,axiom,
% 8.79/1.51      r2_lattice3(X0,X1,X2) | ~r1_orders_2(X0,sK3(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 8.79/1.51  
% 8.79/1.51  cnf(u50,axiom,
% 8.79/1.51      r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 8.79/1.51  
% 8.79/1.51  cnf(u47,axiom,
% 8.79/1.51      r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)).
% 8.79/1.51  
% 8.79/1.51  cnf(u34,negated_conjecture,
% 8.79/1.51      v3_orders_2(sK0)).
% 8.79/1.51  
% 8.79/1.51  cnf(u51,axiom,
% 8.79/1.51      m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 8.79/1.51  
% 8.79/1.51  cnf(u37,negated_conjecture,
% 8.79/1.51      m1_subset_1(sK1,u1_struct_0(sK0))).
% 8.79/1.51  
% 8.79/1.51  cnf(u65,negated_conjecture,
% 8.79/1.51      ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_tarski(X0,X0) = k6_domain_1(u1_struct_0(sK0),X0) | ~l1_struct_0(sK0)).
% 8.79/1.51  
% 8.79/1.51  cnf(u36,negated_conjecture,
% 8.79/1.51      l1_orders_2(sK0)).
% 8.79/1.51  
% 8.79/1.51  cnf(u54,axiom,
% 8.79/1.51      v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1)).
% 8.79/1.51  
% 8.79/1.51  cnf(u62,negated_conjecture,
% 8.79/1.51      ~v1_xboole_0(u1_struct_0(sK0)) | ~l1_struct_0(sK0)).
% 8.79/1.51  
% 8.79/1.51  cnf(u49,axiom,
% 8.79/1.51      l1_struct_0(X0) | ~l1_orders_2(X0)).
% 8.79/1.51  
% 8.79/1.51  cnf(u48,axiom,
% 8.79/1.51      v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0))).
% 8.79/1.51  
% 8.79/1.51  cnf(u33,negated_conjecture,
% 8.79/1.51      ~v2_struct_0(sK0)).
% 8.79/1.51  
% 8.79/1.51  cnf(u42,axiom,
% 8.79/1.51      r2_hidden(sK2(X0,X1,X2),X2) | sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | k2_tarski(X0,X1) = X2).
% 8.79/1.51  
% 8.79/1.51  cnf(u52,axiom,
% 8.79/1.51      r2_hidden(sK3(X0,X1,X2),X1) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 8.79/1.51  
% 8.79/1.51  cnf(u58,axiom,
% 8.79/1.51      r2_hidden(X4,k2_tarski(X4,X1))).
% 8.79/1.51  
% 8.79/1.51  cnf(u56,axiom,
% 8.79/1.51      r2_hidden(X4,k2_tarski(X0,X4))).
% 8.79/1.51  
% 8.79/1.51  cnf(u923,axiom,
% 8.79/1.51      ~r2_hidden(X40,k2_tarski(X40,X40)) | k2_tarski(X40,X40) = k2_tarski(X39,X40) | sK2(X39,X40,k2_tarski(X40,X40)) = X39).
% 8.79/1.51  
% 8.79/1.51  cnf(u1679,axiom,
% 8.79/1.51      ~r2_hidden(X58,k2_tarski(X58,X58)) | k2_tarski(X58,X59) = k2_tarski(X58,X58) | sK2(X58,X59,k2_tarski(X58,X58)) = X59).
% 8.79/1.51  
% 8.79/1.51  cnf(u201,axiom,
% 8.79/1.51      ~r2_hidden(X12,k2_tarski(X12,X13)) | k2_tarski(X12,X12) = k2_tarski(X12,X13) | sK2(X12,X12,k2_tarski(X12,X13)) = X13).
% 8.79/1.51  
% 8.79/1.51  cnf(u802,axiom,
% 8.79/1.51      ~r2_hidden(X38,k2_tarski(X38,X37)) | k2_tarski(X38,X37) = k2_tarski(X37,X38)).
% 8.79/1.51  
% 8.79/1.51  cnf(u399,axiom,
% 8.79/1.51      ~r2_hidden(X19,k2_tarski(X19,X20)) | k2_tarski(X19,X20) = k2_tarski(X18,X19) | sK2(X18,X19,k2_tarski(X19,X20)) = X18 | sK2(X18,X19,k2_tarski(X19,X20)) = X20).
% 8.79/1.51  
% 8.79/1.51  cnf(u554,axiom,
% 8.79/1.51      ~r2_hidden(X27,k2_tarski(X27,X29)) | k2_tarski(X27,X29) = k2_tarski(X27,X28) | sK2(X27,X28,k2_tarski(X27,X29)) = X28 | sK2(X27,X28,k2_tarski(X27,X29)) = X29).
% 8.79/1.51  
% 8.79/1.51  cnf(u2468,axiom,
% 8.79/1.51      ~r2_hidden(X277,k2_tarski(X276,X276)) | k2_tarski(X276,X276) = k2_tarski(sK2(X274,X275,k2_tarski(X276,X276)),X277) | sK2(sK2(X274,X275,k2_tarski(X276,X276)),X277,k2_tarski(X276,X276)) = X276 | sK2(X274,X275,k2_tarski(X276,X276)) = X275 | sK2(X274,X275,k2_tarski(X276,X276)) = X274 | k2_tarski(X276,X276) = k2_tarski(X274,X275)).
% 8.79/1.51  
% 8.79/1.51  cnf(u2460,axiom,
% 8.79/1.51      ~r2_hidden(X245,k2_tarski(X244,X244)) | k2_tarski(X244,X244) = k2_tarski(X245,sK2(X242,X243,k2_tarski(X244,X244))) | sK2(X245,sK2(X242,X243,k2_tarski(X244,X244)),k2_tarski(X244,X244)) = X244 | sK2(X242,X243,k2_tarski(X244,X244)) = X243 | sK2(X242,X243,k2_tarski(X244,X244)) = X242 | k2_tarski(X244,X244) = k2_tarski(X242,X243)).
% 8.79/1.51  
% 8.79/1.51  cnf(u2403,axiom,
% 8.79/1.51      ~r2_hidden(X9,k2_tarski(X8,X8)) | sK2(X6,X7,k2_tarski(X8,X8)) = X9 | X8 = X9 | sK2(X6,X7,k2_tarski(X8,X8)) = X7 | sK2(X6,X7,k2_tarski(X8,X8)) = X6 | k2_tarski(X6,X7) = k2_tarski(X8,X8)).
% 8.79/1.51  
% 8.79/1.51  cnf(u1732,axiom,
% 8.79/1.51      ~r2_hidden(X65,k2_tarski(X64,X64)) | k2_tarski(X64,X65) = k2_tarski(X64,X64)).
% 8.79/1.51  
% 8.79/1.51  cnf(u1266,axiom,
% 8.79/1.51      ~r2_hidden(X50,k2_tarski(X51,X51)) | k2_tarski(X51,X51) = k2_tarski(X50,X51)).
% 8.79/1.51  
% 8.79/1.51  cnf(u781,axiom,
% 8.79/1.51      ~r2_hidden(X45,k2_tarski(X46,X46)) | k2_tarski(X44,X45) = k2_tarski(X46,X46) | sK2(X44,X45,k2_tarski(X46,X46)) = X44 | sK2(X44,X45,k2_tarski(X46,X46)) = X46).
% 8.79/1.51  
% 8.79/1.51  cnf(u779,axiom,
% 8.79/1.51      ~r2_hidden(X41,k2_tarski(X43,X43)) | k2_tarski(X43,X43) = k2_tarski(X41,X42) | sK2(X41,X42,k2_tarski(X43,X43)) = X42 | sK2(X41,X42,k2_tarski(X43,X43)) = X43).
% 8.79/1.51  
% 8.79/1.51  cnf(u331,axiom,
% 8.79/1.51      ~r2_hidden(X12,k2_tarski(X13,X13)) | k2_tarski(X12,X12) = k2_tarski(X13,X13) | sK2(X12,X12,k2_tarski(X13,X13)) = X13).
% 8.79/1.51  
% 8.79/1.51  cnf(u261,axiom,
% 8.79/1.51      ~r2_hidden(X12,k2_tarski(X13,X12)) | k2_tarski(X12,X12) = k2_tarski(X13,X12) | sK2(X12,X12,k2_tarski(X13,X12)) = X13).
% 8.79/1.51  
% 8.79/1.51  cnf(u684,axiom,
% 8.79/1.51      ~r2_hidden(X28,k2_tarski(X29,X28)) | k2_tarski(X29,X28) = k2_tarski(X28,X29) | sK2(X28,X29,k2_tarski(X29,X28)) = X29).
% 8.79/1.51  
% 8.79/1.51  cnf(u468,axiom,
% 8.79/1.51      ~r2_hidden(X25,k2_tarski(X26,X25)) | k2_tarski(X26,X25) = k2_tarski(X24,X25) | sK2(X24,X25,k2_tarski(X26,X25)) = X24 | sK2(X24,X25,k2_tarski(X26,X25)) = X26).
% 8.79/1.51  
% 8.79/1.51  cnf(u643,axiom,
% 8.79/1.51      ~r2_hidden(X33,k2_tarski(X35,X33)) | k2_tarski(X33,X34) = k2_tarski(X35,X33) | sK2(X33,X34,k2_tarski(X35,X33)) = X34 | sK2(X33,X34,k2_tarski(X35,X33)) = X35).
% 8.79/1.51  
% 8.79/1.51  cnf(u2220,axiom,
% 8.79/1.51      ~r2_hidden(X2,k2_tarski(X1,X0)) | k2_tarski(X1,X0) = k2_tarski(X0,X2) | sK2(X0,X2,k2_tarski(X1,X0)) = X1).
% 8.79/1.51  
% 8.79/1.51  cnf(u2202,axiom,
% 8.79/1.51      ~r2_hidden(X96,k2_tarski(X95,X97)) | k2_tarski(X95,X96) = k2_tarski(X95,X97) | sK2(X95,X96,k2_tarski(X95,X97)) = X97).
% 8.79/1.51  
% 8.79/1.51  cnf(u1918,axiom,
% 8.79/1.51      ~r2_hidden(X2,k2_tarski(X1,X0)) | k2_tarski(X1,X0) = k2_tarski(X2,X0) | sK2(X2,X0,k2_tarski(X1,X0)) = X1).
% 8.79/1.51  
% 8.79/1.51  cnf(u1893,axiom,
% 8.79/1.51      ~r2_hidden(X87,k2_tarski(X88,X89)) | k2_tarski(X88,X89) = k2_tarski(X87,X88) | sK2(X87,X88,k2_tarski(X88,X89)) = X89).
% 8.79/1.51  
% 8.79/1.51  cnf(u1538,axiom,
% 8.79/1.51      ~r2_hidden(X79,k2_tarski(X82,X83)) | k2_tarski(X82,X83) = k2_tarski(X79,sK2(X80,X81,k2_tarski(X82,X83))) | sK2(X79,sK2(X80,X81,k2_tarski(X82,X83)),k2_tarski(X82,X83)) = X82 | sK2(X79,sK2(X80,X81,k2_tarski(X82,X83)),k2_tarski(X82,X83)) = X83 | sK2(X80,X81,k2_tarski(X82,X83)) = X81 | sK2(X80,X81,k2_tarski(X82,X83)) = X80 | k2_tarski(X80,X81) = k2_tarski(X82,X83)).
% 8.79/1.51  
% 8.79/1.51  cnf(u1162,axiom,
% 8.79/1.51      ~r2_hidden(X76,k2_tarski(X74,X75)) | k2_tarski(X74,X75) = k2_tarski(sK2(X72,X73,k2_tarski(X74,X75)),X76) | sK2(sK2(X72,X73,k2_tarski(X74,X75)),X76,k2_tarski(X74,X75)) = X74 | sK2(sK2(X72,X73,k2_tarski(X74,X75)),X76,k2_tarski(X74,X75)) = X75 | sK2(X72,X73,k2_tarski(X74,X75)) = X73 | sK2(X72,X73,k2_tarski(X74,X75)) = X72 | k2_tarski(X74,X75) = k2_tarski(X72,X73)).
% 8.79/1.51  
% 8.79/1.51  cnf(u648,axiom,
% 8.79/1.51      ~r2_hidden(X37,k2_tarski(X38,X36)) | k2_tarski(X36,X37) = k2_tarski(X38,X36) | sK2(X36,X37,k2_tarski(X38,X36)) = X38 | sK2(X36,X37,k2_tarski(X38,X36)) = X36).
% 8.79/1.51  
% 8.79/1.51  cnf(u556,axiom,
% 8.79/1.51      ~r2_hidden(X31,k2_tarski(X30,X32)) | k2_tarski(X30,X32) = k2_tarski(X30,X31) | sK2(X30,X31,k2_tarski(X30,X32)) = X30 | sK2(X30,X31,k2_tarski(X30,X32)) = X32).
% 8.79/1.51  
% 8.79/1.51  cnf(u475,axiom,
% 8.79/1.51      ~r2_hidden(X21,k2_tarski(X23,X22)) | k2_tarski(X23,X22) = k2_tarski(X21,X22) | sK2(X21,X22,k2_tarski(X23,X22)) = X23 | sK2(X21,X22,k2_tarski(X23,X22)) = X22).
% 8.79/1.51  
% 8.79/1.51  cnf(u403,axiom,
% 8.79/1.51      ~r2_hidden(X15,k2_tarski(X16,X17)) | k2_tarski(X16,X17) = k2_tarski(X15,X16) | sK2(X15,X16,k2_tarski(X16,X17)) = X16 | sK2(X15,X16,k2_tarski(X16,X17)) = X17).
% 8.79/1.51  
% 8.79/1.51  cnf(u167,axiom,
% 8.79/1.51      ~r2_hidden(X18,k2_tarski(X19,X20)) | k2_tarski(X19,X20) = k2_tarski(X18,X18) | sK2(X18,X18,k2_tarski(X19,X20)) = X19 | sK2(X18,X18,k2_tarski(X19,X20)) = X20).
% 8.79/1.51  
% 8.79/1.51  cnf(u120,axiom,
% 8.79/1.51      ~r2_hidden(X9,k2_tarski(X10,X11)) | k2_tarski(X10,X11) = k2_tarski(X8,X9) | sK2(X8,X9,k2_tarski(X10,X11)) = X8 | sK2(X8,X9,k2_tarski(X10,X11)) = X10 | sK2(X8,X9,k2_tarski(X10,X11)) = X11).
% 8.79/1.51  
% 8.79/1.51  cnf(u118,axiom,
% 8.79/1.51      ~r2_hidden(X4,k2_tarski(X6,X7)) | k2_tarski(X6,X7) = k2_tarski(X4,X5) | sK2(X4,X5,k2_tarski(X6,X7)) = X5 | sK2(X4,X5,k2_tarski(X6,X7)) = X6 | sK2(X4,X5,k2_tarski(X6,X7)) = X7).
% 8.79/1.51  
% 8.79/1.51  cnf(u59,axiom,
% 8.79/1.51      ~r2_hidden(X4,k2_tarski(X0,X1)) | X0 = X4 | X1 = X4).
% 8.79/1.51  
% 8.79/1.51  cnf(u1739,axiom,
% 8.79/1.51      k2_tarski(X5,X5) = k2_tarski(X5,sK2(X6,X7,k2_tarski(X5,X5))) | sK2(X6,X7,k2_tarski(X5,X5)) = X7 | sK2(X6,X7,k2_tarski(X5,X5)) = X6 | k2_tarski(X6,X7) = k2_tarski(X5,X5)).
% 8.79/1.51  
% 8.79/1.51  cnf(u1271,axiom,
% 8.79/1.51      k2_tarski(X5,X5) = k2_tarski(sK2(X6,X7,k2_tarski(X5,X5)),X5) | sK2(X6,X7,k2_tarski(X5,X5)) = X7 | sK2(X6,X7,k2_tarski(X5,X5)) = X6 | k2_tarski(X6,X7) = k2_tarski(X5,X5)).
% 8.79/1.51  
% 8.79/1.51  cnf(u807,axiom,
% 8.79/1.51      k2_tarski(X1,X2) = k2_tarski(X2,X1)).
% 8.79/1.51  
% 8.79/1.51  cnf(u2210,axiom,
% 8.79/1.51      sK2(sK2(X9,X10,k2_tarski(X8,X8)),X11,k2_tarski(X8,X8)) = X11 | sK2(sK2(X9,X10,k2_tarski(X8,X8)),X11,k2_tarski(X8,X8)) = X8 | k2_tarski(X8,X8) = k2_tarski(sK2(X9,X10,k2_tarski(X8,X8)),X11) | sK2(X9,X10,k2_tarski(X8,X8)) = X10 | sK2(X9,X10,k2_tarski(X8,X8)) = X9 | k2_tarski(X8,X8) = k2_tarski(X9,X10)).
% 8.79/1.51  
% 8.79/1.51  cnf(u2210,axiom,
% 8.79/1.51      sK2(sK2(X9,X10,k2_tarski(X8,X8)),X11,k2_tarski(X8,X8)) = X11 | sK2(sK2(X9,X10,k2_tarski(X8,X8)),X11,k2_tarski(X8,X8)) = X8 | k2_tarski(X8,X8) = k2_tarski(sK2(X9,X10,k2_tarski(X8,X8)),X11) | sK2(X9,X10,k2_tarski(X8,X8)) = X10 | sK2(X9,X10,k2_tarski(X8,X8)) = X9 | k2_tarski(X8,X8) = k2_tarski(X9,X10)).
% 8.79/1.51  
% 8.79/1.51  cnf(u5071,axiom,
% 8.79/1.51      sK2(sK2(X0,X1,k2_tarski(X2,X2)),sK2(X3,X4,k2_tarski(X2,X2)),k2_tarski(X2,X2)) = X2 | k2_tarski(X2,X2) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X2)),sK2(X3,X4,k2_tarski(X2,X2))) | sK2(X0,X1,k2_tarski(X2,X2)) = X1 | sK2(X0,X1,k2_tarski(X2,X2)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X2) | sK2(X3,X4,k2_tarski(X2,X2)) = X4 | sK2(X3,X4,k2_tarski(X2,X2)) = X3 | k2_tarski(X2,X2) = k2_tarski(X3,X4)).
% 8.79/1.51  
% 8.79/1.51  cnf(u2644,axiom,
% 8.79/1.51      sK2(sK2(X16,X17,k2_tarski(X15,X15)),sK2(X13,X14,k2_tarski(X15,X15)),k2_tarski(X15,X15)) = X15 | k2_tarski(X15,X15) = k2_tarski(sK2(X13,X14,k2_tarski(X15,X15)),sK2(X16,X17,k2_tarski(X15,X15))) | sK2(X16,X17,k2_tarski(X15,X15)) = X17 | sK2(X16,X17,k2_tarski(X15,X15)) = X16 | k2_tarski(X16,X17) = k2_tarski(X15,X15) | sK2(X13,X14,k2_tarski(X15,X15)) = X14 | sK2(X13,X14,k2_tarski(X15,X15)) = X13 | k2_tarski(X13,X14) = k2_tarski(X15,X15)).
% 8.79/1.51  
% 8.79/1.51  cnf(u339,axiom,
% 8.79/1.51      sK2(sK2(X5,X6,k2_tarski(X7,X7)),sK2(X5,X6,k2_tarski(X7,X7)),k2_tarski(X7,X7)) = X7 | k2_tarski(X7,X7) = k2_tarski(sK2(X5,X6,k2_tarski(X7,X7)),sK2(X5,X6,k2_tarski(X7,X7))) | sK2(X5,X6,k2_tarski(X7,X7)) = X6 | sK2(X5,X6,k2_tarski(X7,X7)) = X5 | k2_tarski(X7,X7) = k2_tarski(X5,X6)).
% 8.79/1.51  
% 8.79/1.51  cnf(u3100,axiom,
% 8.79/1.51      sK2(sK2(X16,X17,k2_tarski(X14,X15)),sK2(X18,X19,k2_tarski(X14,X15)),k2_tarski(X14,X15)) = X14 | sK2(sK2(X16,X17,k2_tarski(X14,X15)),sK2(X18,X19,k2_tarski(X14,X15)),k2_tarski(X14,X15)) = X15 | k2_tarski(X14,X15) = k2_tarski(sK2(X16,X17,k2_tarski(X14,X15)),sK2(X18,X19,k2_tarski(X14,X15))) | sK2(X16,X17,k2_tarski(X14,X15)) = X17 | sK2(X16,X17,k2_tarski(X14,X15)) = X16 | k2_tarski(X14,X15) = k2_tarski(X16,X17) | sK2(X18,X19,k2_tarski(X14,X15)) = X19 | sK2(X18,X19,k2_tarski(X14,X15)) = X18 | k2_tarski(X14,X15) = k2_tarski(X18,X19)).
% 8.79/1.51  
% 8.79/1.51  cnf(u3100,axiom,
% 8.79/1.51      sK2(sK2(X16,X17,k2_tarski(X14,X15)),sK2(X18,X19,k2_tarski(X14,X15)),k2_tarski(X14,X15)) = X14 | sK2(sK2(X16,X17,k2_tarski(X14,X15)),sK2(X18,X19,k2_tarski(X14,X15)),k2_tarski(X14,X15)) = X15 | k2_tarski(X14,X15) = k2_tarski(sK2(X16,X17,k2_tarski(X14,X15)),sK2(X18,X19,k2_tarski(X14,X15))) | sK2(X16,X17,k2_tarski(X14,X15)) = X17 | sK2(X16,X17,k2_tarski(X14,X15)) = X16 | k2_tarski(X14,X15) = k2_tarski(X16,X17) | sK2(X18,X19,k2_tarski(X14,X15)) = X19 | sK2(X18,X19,k2_tarski(X14,X15)) = X18 | k2_tarski(X14,X15) = k2_tarski(X18,X19)).
% 8.79/1.51  
% 8.79/1.51  cnf(u1754,axiom,
% 8.79/1.51      sK2(sK2(X10,X11,k2_tarski(X8,X9)),sK2(X10,X11,k2_tarski(X8,X9)),k2_tarski(X8,X9)) = X8 | sK2(sK2(X10,X11,k2_tarski(X8,X9)),sK2(X10,X11,k2_tarski(X8,X9)),k2_tarski(X8,X9)) = X9 | k2_tarski(X8,X9) = k2_tarski(sK2(X10,X11,k2_tarski(X8,X9)),sK2(X10,X11,k2_tarski(X8,X9))) | sK2(X10,X11,k2_tarski(X8,X9)) = X11 | sK2(X10,X11,k2_tarski(X8,X9)) = X10 | k2_tarski(X10,X11) = k2_tarski(X8,X9)).
% 8.79/1.51  
% 8.79/1.51  cnf(u1754,axiom,
% 8.79/1.51      sK2(sK2(X10,X11,k2_tarski(X8,X9)),sK2(X10,X11,k2_tarski(X8,X9)),k2_tarski(X8,X9)) = X8 | sK2(sK2(X10,X11,k2_tarski(X8,X9)),sK2(X10,X11,k2_tarski(X8,X9)),k2_tarski(X8,X9)) = X9 | k2_tarski(X8,X9) = k2_tarski(sK2(X10,X11,k2_tarski(X8,X9)),sK2(X10,X11,k2_tarski(X8,X9))) | sK2(X10,X11,k2_tarski(X8,X9)) = X11 | sK2(X10,X11,k2_tarski(X8,X9)) = X10 | k2_tarski(X10,X11) = k2_tarski(X8,X9)).
% 8.79/1.51  
% 8.79/1.51  cnf(u276,axiom,
% 8.79/1.51      sK2(sK2(X13,X14,k2_tarski(X11,X12)),X15,k2_tarski(X11,X12)) = X15 | sK2(sK2(X13,X14,k2_tarski(X11,X12)),X15,k2_tarski(X11,X12)) = X11 | sK2(sK2(X13,X14,k2_tarski(X11,X12)),X15,k2_tarski(X11,X12)) = X12 | k2_tarski(X11,X12) = k2_tarski(sK2(X13,X14,k2_tarski(X11,X12)),X15) | sK2(X13,X14,k2_tarski(X11,X12)) = X14 | sK2(X13,X14,k2_tarski(X11,X12)) = X13 | k2_tarski(X13,X14) = k2_tarski(X11,X12)).
% 8.79/1.51  
% 8.79/1.51  cnf(u276,axiom,
% 8.79/1.51      sK2(sK2(X13,X14,k2_tarski(X11,X12)),X15,k2_tarski(X11,X12)) = X15 | sK2(sK2(X13,X14,k2_tarski(X11,X12)),X15,k2_tarski(X11,X12)) = X11 | sK2(sK2(X13,X14,k2_tarski(X11,X12)),X15,k2_tarski(X11,X12)) = X12 | k2_tarski(X11,X12) = k2_tarski(sK2(X13,X14,k2_tarski(X11,X12)),X15) | sK2(X13,X14,k2_tarski(X11,X12)) = X14 | sK2(X13,X14,k2_tarski(X11,X12)) = X13 | k2_tarski(X13,X14) = k2_tarski(X11,X12)).
% 8.79/1.51  
% 8.79/1.51  cnf(u276,axiom,
% 8.79/1.51      sK2(sK2(X13,X14,k2_tarski(X11,X12)),X15,k2_tarski(X11,X12)) = X15 | sK2(sK2(X13,X14,k2_tarski(X11,X12)),X15,k2_tarski(X11,X12)) = X11 | sK2(sK2(X13,X14,k2_tarski(X11,X12)),X15,k2_tarski(X11,X12)) = X12 | k2_tarski(X11,X12) = k2_tarski(sK2(X13,X14,k2_tarski(X11,X12)),X15) | sK2(X13,X14,k2_tarski(X11,X12)) = X14 | sK2(X13,X14,k2_tarski(X11,X12)) = X13 | k2_tarski(X13,X14) = k2_tarski(X11,X12)).
% 8.79/1.51  
% 8.79/1.51  cnf(u2641,axiom,
% 8.79/1.51      sK2(sK2(X2,X3,k2_tarski(X1,X0)),X0,k2_tarski(X1,X0)) = X1 | k2_tarski(X1,X0) = k2_tarski(X0,sK2(X2,X3,k2_tarski(X1,X0))) | sK2(X2,X3,k2_tarski(X1,X0)) = X3 | sK2(X2,X3,k2_tarski(X1,X0)) = X2 | k2_tarski(X1,X0) = k2_tarski(X2,X3)).
% 8.79/1.51  
% 8.79/1.51  cnf(u1921,axiom,
% 8.79/1.51      sK2(sK2(X10,X11,k2_tarski(X8,X9)),X8,k2_tarski(X8,X9)) = X9 | k2_tarski(X8,X9) = k2_tarski(X8,sK2(X10,X11,k2_tarski(X8,X9))) | sK2(X10,X11,k2_tarski(X8,X9)) = X11 | sK2(X10,X11,k2_tarski(X8,X9)) = X10 | k2_tarski(X10,X11) = k2_tarski(X8,X9)).
% 8.79/1.51  
% 8.79/1.51  cnf(u2219,axiom,
% 8.79/1.51      sK2(X8,sK2(X9,X10,k2_tarski(X8,X11)),k2_tarski(X8,X11)) = X11 | k2_tarski(X8,X11) = k2_tarski(X8,sK2(X9,X10,k2_tarski(X8,X11))) | sK2(X9,X10,k2_tarski(X8,X11)) = X10 | sK2(X9,X10,k2_tarski(X8,X11)) = X9 | k2_tarski(X9,X10) = k2_tarski(X8,X11)).
% 8.79/1.51  
% 8.79/1.51  cnf(u2215,axiom,
% 8.79/1.51      sK2(X8,sK2(X9,X10,k2_tarski(X11,X11)),k2_tarski(X11,X11)) = X8 | sK2(X8,sK2(X9,X10,k2_tarski(X11,X11)),k2_tarski(X11,X11)) = X11 | k2_tarski(X11,X11) = k2_tarski(X8,sK2(X9,X10,k2_tarski(X11,X11))) | sK2(X9,X10,k2_tarski(X11,X11)) = X10 | sK2(X9,X10,k2_tarski(X11,X11)) = X9 | k2_tarski(X11,X11) = k2_tarski(X9,X10)).
% 8.79/1.51  
% 8.79/1.51  cnf(u2215,axiom,
% 8.79/1.51      sK2(X8,sK2(X9,X10,k2_tarski(X11,X11)),k2_tarski(X11,X11)) = X8 | sK2(X8,sK2(X9,X10,k2_tarski(X11,X11)),k2_tarski(X11,X11)) = X11 | k2_tarski(X11,X11) = k2_tarski(X8,sK2(X9,X10,k2_tarski(X11,X11))) | sK2(X9,X10,k2_tarski(X11,X11)) = X10 | sK2(X9,X10,k2_tarski(X11,X11)) = X9 | k2_tarski(X11,X11) = k2_tarski(X9,X10)).
% 8.79/1.51  
% 8.79/1.51  cnf(u2755,axiom,
% 8.79/1.51      sK2(X0,sK2(X2,X3,k2_tarski(X1,X0)),k2_tarski(X1,X0)) = X1 | k2_tarski(X1,X0) = k2_tarski(X0,sK2(X2,X3,k2_tarski(X1,X0))) | sK2(X2,X3,k2_tarski(X1,X0)) = X3 | sK2(X2,X3,k2_tarski(X1,X0)) = X2 | k2_tarski(X1,X0) = k2_tarski(X2,X3)).
% 8.79/1.51  
% 8.79/1.51  cnf(u300,axiom,
% 8.79/1.51      sK2(X13,sK2(X14,X15,k2_tarski(X11,X12)),k2_tarski(X11,X12)) = X13 | sK2(X13,sK2(X14,X15,k2_tarski(X11,X12)),k2_tarski(X11,X12)) = X11 | sK2(X13,sK2(X14,X15,k2_tarski(X11,X12)),k2_tarski(X11,X12)) = X12 | k2_tarski(X11,X12) = k2_tarski(X13,sK2(X14,X15,k2_tarski(X11,X12))) | sK2(X14,X15,k2_tarski(X11,X12)) = X15 | sK2(X14,X15,k2_tarski(X11,X12)) = X14 | k2_tarski(X14,X15) = k2_tarski(X11,X12)).
% 8.79/1.51  
% 8.79/1.51  cnf(u300,axiom,
% 8.79/1.51      sK2(X13,sK2(X14,X15,k2_tarski(X11,X12)),k2_tarski(X11,X12)) = X13 | sK2(X13,sK2(X14,X15,k2_tarski(X11,X12)),k2_tarski(X11,X12)) = X11 | sK2(X13,sK2(X14,X15,k2_tarski(X11,X12)),k2_tarski(X11,X12)) = X12 | k2_tarski(X11,X12) = k2_tarski(X13,sK2(X14,X15,k2_tarski(X11,X12))) | sK2(X14,X15,k2_tarski(X11,X12)) = X15 | sK2(X14,X15,k2_tarski(X11,X12)) = X14 | k2_tarski(X14,X15) = k2_tarski(X11,X12)).
% 8.79/1.51  
% 8.79/1.51  cnf(u300,axiom,
% 8.79/1.51      sK2(X13,sK2(X14,X15,k2_tarski(X11,X12)),k2_tarski(X11,X12)) = X13 | sK2(X13,sK2(X14,X15,k2_tarski(X11,X12)),k2_tarski(X11,X12)) = X11 | sK2(X13,sK2(X14,X15,k2_tarski(X11,X12)),k2_tarski(X11,X12)) = X12 | k2_tarski(X11,X12) = k2_tarski(X13,sK2(X14,X15,k2_tarski(X11,X12))) | sK2(X14,X15,k2_tarski(X11,X12)) = X15 | sK2(X14,X15,k2_tarski(X11,X12)) = X14 | k2_tarski(X14,X15) = k2_tarski(X11,X12)).
% 8.79/1.51  
% 8.79/1.51  cnf(u171,axiom,
% 8.79/1.51      sK2(X0,X0,k2_tarski(X0,X1)) = X0 | sK2(X0,X0,k2_tarski(X0,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X0,X0)).
% 8.79/1.51  
% 8.79/1.51  cnf(u209,axiom,
% 8.79/1.51      sK2(X1,X1,k2_tarski(X1,X2)) = X2 | k2_tarski(X1,X1) = k2_tarski(X1,X2)).
% 8.79/1.51  
% 8.79/1.51  cnf(u171,axiom,
% 8.79/1.51      sK2(X0,X0,k2_tarski(X0,X1)) = X0 | sK2(X0,X0,k2_tarski(X0,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X0,X0)).
% 8.79/1.51  
% 8.79/1.51  cnf(u302,axiom,
% 8.79/1.51      sK2(X0,X0,k2_tarski(X1,X1)) = X0 | sK2(X0,X0,k2_tarski(X1,X1)) = X1 | k2_tarski(X0,X0) = k2_tarski(X1,X1)).
% 8.79/1.51  
% 8.79/1.51  cnf(u302,axiom,
% 8.79/1.51      sK2(X0,X0,k2_tarski(X1,X1)) = X0 | sK2(X0,X0,k2_tarski(X1,X1)) = X1 | k2_tarski(X0,X0) = k2_tarski(X1,X1)).
% 8.79/1.51  
% 8.79/1.51  cnf(u234,axiom,
% 8.79/1.51      sK2(X0,X0,k2_tarski(X1,X0)) = X1 | sK2(X0,X0,k2_tarski(X1,X0)) = X0 | k2_tarski(X0,X0) = k2_tarski(X1,X0)).
% 8.79/1.51  
% 8.79/1.51  cnf(u234,axiom,
% 8.79/1.51      sK2(X0,X0,k2_tarski(X1,X0)) = X1 | sK2(X0,X0,k2_tarski(X1,X0)) = X0 | k2_tarski(X0,X0) = k2_tarski(X1,X0)).
% 8.79/1.51  
% 8.79/1.51  cnf(u271,axiom,
% 8.79/1.51      sK2(X0,X0,k2_tarski(X1,X0)) = X1 | k2_tarski(X0,X0) = k2_tarski(X1,X0)).
% 8.79/1.51  
% 8.79/1.51  cnf(u122,axiom,
% 8.79/1.51      sK2(X0,X0,k2_tarski(X1,X2)) = X0 | sK2(X0,X0,k2_tarski(X1,X2)) = X1 | sK2(X0,X0,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X0) = k2_tarski(X1,X2)).
% 8.79/1.51  
% 8.79/1.51  cnf(u122,axiom,
% 8.79/1.51      sK2(X0,X0,k2_tarski(X1,X2)) = X0 | sK2(X0,X0,k2_tarski(X1,X2)) = X1 | sK2(X0,X0,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X0) = k2_tarski(X1,X2)).
% 8.79/1.51  
% 8.79/1.51  cnf(u122,axiom,
% 8.79/1.51      sK2(X0,X0,k2_tarski(X1,X2)) = X0 | sK2(X0,X0,k2_tarski(X1,X2)) = X1 | sK2(X0,X0,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X0) = k2_tarski(X1,X2)).
% 8.79/1.51  
% 8.79/1.51  cnf(u1622,axiom,
% 8.79/1.51      sK2(X0,X1,k2_tarski(X0,X0)) = X1 | sK2(X0,X1,k2_tarski(X0,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X0,X0)).
% 8.79/1.51  
% 8.79/1.51  cnf(u1622,axiom,
% 8.79/1.51      sK2(X0,X1,k2_tarski(X0,X0)) = X1 | sK2(X0,X1,k2_tarski(X0,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X0,X0)).
% 8.79/1.51  
% 8.79/1.51  cnf(u1690,axiom,
% 8.79/1.51      sK2(X0,X1,k2_tarski(X0,X0)) = X1 | k2_tarski(X0,X1) = k2_tarski(X0,X0)).
% 8.79/1.51  
% 8.79/1.51  cnf(u207,axiom,
% 8.79/1.51      sK2(X0,X1,k2_tarski(X0,X2)) = X1 | sK2(X0,X1,k2_tarski(X0,X2)) = X0 | sK2(X0,X1,k2_tarski(X0,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 8.79/1.51  
% 8.79/1.51  cnf(u1931,axiom,
% 8.79/1.51      sK2(X2,X4,k2_tarski(X2,X3)) = X4 | sK2(X2,X4,k2_tarski(X2,X3)) = X3 | k2_tarski(X2,X3) = k2_tarski(X2,X4)).
% 8.79/1.51  
% 8.79/1.51  cnf(u207,axiom,
% 8.79/1.51      sK2(X0,X1,k2_tarski(X0,X2)) = X1 | sK2(X0,X1,k2_tarski(X0,X2)) = X0 | sK2(X0,X1,k2_tarski(X0,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 8.79/1.51  
% 8.79/1.51  cnf(u207,axiom,
% 8.79/1.51      sK2(X0,X1,k2_tarski(X0,X2)) = X1 | sK2(X0,X1,k2_tarski(X0,X2)) = X0 | sK2(X0,X1,k2_tarski(X0,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 8.79/1.51  
% 8.79/1.51  cnf(u1931,axiom,
% 8.79/1.51      sK2(X2,X4,k2_tarski(X2,X3)) = X4 | sK2(X2,X4,k2_tarski(X2,X3)) = X3 | k2_tarski(X2,X3) = k2_tarski(X2,X4)).
% 8.79/1.51  
% 8.79/1.51  cnf(u885,axiom,
% 8.79/1.51      sK2(X0,X1,k2_tarski(X1,X1)) = X0 | sK2(X0,X1,k2_tarski(X1,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X1,X1)).
% 8.79/1.51  
% 8.79/1.51  cnf(u885,axiom,
% 8.79/1.51      sK2(X0,X1,k2_tarski(X1,X1)) = X0 | sK2(X0,X1,k2_tarski(X1,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X1,X1)).
% 8.79/1.51  
% 8.79/1.51  cnf(u934,axiom,
% 8.79/1.51      sK2(X1,X0,k2_tarski(X0,X0)) = X1 | k2_tarski(X0,X0) = k2_tarski(X1,X0)).
% 8.79/1.51  
% 8.79/1.51  cnf(u651,axiom,
% 8.79/1.51      sK2(X0,X1,k2_tarski(X1,X0)) = X1 | sK2(X0,X1,k2_tarski(X1,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X1,X0)).
% 8.79/1.51  
% 8.79/1.51  cnf(u651,axiom,
% 8.79/1.51      sK2(X0,X1,k2_tarski(X1,X0)) = X1 | sK2(X0,X1,k2_tarski(X1,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X1,X0)).
% 8.79/1.51  
% 8.79/1.51  cnf(u784,axiom,
% 8.79/1.51      sK2(X1,X0,k2_tarski(X0,X1)) = X0 | k2_tarski(X0,X1) = k2_tarski(X1,X0)).
% 8.79/1.51  
% 8.79/1.51  cnf(u170,axiom,
% 8.79/1.51      sK2(X0,X1,k2_tarski(X1,X2)) = X0 | sK2(X0,X1,k2_tarski(X1,X2)) = X1 | sK2(X0,X1,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 8.79/1.51  
% 8.79/1.51  cnf(u1758,axiom,
% 8.79/1.51      sK2(X4,X2,k2_tarski(X2,X3)) = X4 | sK2(X4,X2,k2_tarski(X2,X3)) = X3 | k2_tarski(X2,X3) = k2_tarski(X4,X2)).
% 8.79/1.51  
% 8.79/1.51  cnf(u170,axiom,
% 8.79/1.51      sK2(X0,X1,k2_tarski(X1,X2)) = X0 | sK2(X0,X1,k2_tarski(X1,X2)) = X1 | sK2(X0,X1,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 8.79/1.51  
% 8.79/1.51  cnf(u170,axiom,
% 8.79/1.51      sK2(X0,X1,k2_tarski(X1,X2)) = X0 | sK2(X0,X1,k2_tarski(X1,X2)) = X1 | sK2(X0,X1,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 8.79/1.51  
% 8.79/1.51  cnf(u1758,axiom,
% 8.79/1.51      sK2(X4,X2,k2_tarski(X2,X3)) = X4 | sK2(X4,X2,k2_tarski(X2,X3)) = X3 | k2_tarski(X2,X3) = k2_tarski(X4,X2)).
% 8.79/1.51  
% 8.79/1.51  cnf(u73,axiom,
% 8.79/1.51      sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | sK2(X0,X1,k2_tarski(X2,X3)) = X2 | sK2(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 8.79/1.51  
% 8.79/1.51  cnf(u73,axiom,
% 8.79/1.51      sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | sK2(X0,X1,k2_tarski(X2,X3)) = X2 | sK2(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 8.79/1.51  
% 8.79/1.51  cnf(u73,axiom,
% 8.79/1.51      sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | sK2(X0,X1,k2_tarski(X2,X3)) = X2 | sK2(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 8.79/1.51  
% 8.79/1.51  cnf(u73,axiom,
% 8.79/1.51      sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | sK2(X0,X1,k2_tarski(X2,X3)) = X2 | sK2(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 8.79/1.51  
% 8.79/1.51  cnf(u233,axiom,
% 8.79/1.51      sK2(X0,X1,k2_tarski(X2,X2)) = X1 | sK2(X0,X1,k2_tarski(X2,X2)) = X0 | sK2(X0,X1,k2_tarski(X2,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 8.79/1.51  
% 8.79/1.51  cnf(u233,axiom,
% 8.79/1.51      sK2(X0,X1,k2_tarski(X2,X2)) = X1 | sK2(X0,X1,k2_tarski(X2,X2)) = X0 | sK2(X0,X1,k2_tarski(X2,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 8.79/1.51  
% 8.79/1.51  cnf(u233,axiom,
% 8.79/1.51      sK2(X0,X1,k2_tarski(X2,X2)) = X1 | sK2(X0,X1,k2_tarski(X2,X2)) = X0 | sK2(X0,X1,k2_tarski(X2,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 8.79/1.51  
% 8.79/1.51  cnf(u172,axiom,
% 8.79/1.51      sK2(X0,X1,k2_tarski(X2,X1)) = X0 | sK2(X0,X1,k2_tarski(X2,X1)) = X2 | sK2(X0,X1,k2_tarski(X2,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 8.79/1.51  
% 8.79/1.51  cnf(u172,axiom,
% 8.79/1.51      sK2(X0,X1,k2_tarski(X2,X1)) = X0 | sK2(X0,X1,k2_tarski(X2,X1)) = X2 | sK2(X0,X1,k2_tarski(X2,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 8.79/1.51  
% 8.79/1.51  cnf(u1901,axiom,
% 8.79/1.51      sK2(X2,X1,k2_tarski(X0,X1)) = X2 | sK2(X2,X1,k2_tarski(X0,X1)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 8.79/1.51  
% 8.79/1.51  cnf(u172,axiom,
% 8.79/1.51      sK2(X0,X1,k2_tarski(X2,X1)) = X0 | sK2(X0,X1,k2_tarski(X2,X1)) = X2 | sK2(X0,X1,k2_tarski(X2,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 8.79/1.51  
% 8.79/1.51  cnf(u1901,axiom,
% 8.79/1.51      sK2(X2,X1,k2_tarski(X0,X1)) = X2 | sK2(X2,X1,k2_tarski(X0,X1)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 8.79/1.51  
% 8.79/1.51  cnf(u229,axiom,
% 8.79/1.51      sK2(X0,X1,k2_tarski(X2,X0)) = X1 | sK2(X0,X1,k2_tarski(X2,X0)) = X2 | sK2(X0,X1,k2_tarski(X2,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 8.79/1.51  
% 8.79/1.51  cnf(u229,axiom,
% 8.79/1.51      sK2(X0,X1,k2_tarski(X2,X0)) = X1 | sK2(X0,X1,k2_tarski(X2,X0)) = X2 | sK2(X0,X1,k2_tarski(X2,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 8.79/1.51  
% 8.79/1.51  cnf(u2064,axiom,
% 8.79/1.51      sK2(X0,X1,k2_tarski(X2,X0)) = X1 | sK2(X0,X1,k2_tarski(X2,X0)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 8.79/1.51  
% 8.79/1.51  cnf(u229,axiom,
% 8.79/1.51      sK2(X0,X1,k2_tarski(X2,X0)) = X1 | sK2(X0,X1,k2_tarski(X2,X0)) = X2 | sK2(X0,X1,k2_tarski(X2,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 8.79/1.51  
% 8.79/1.51  cnf(u2064,axiom,
% 8.79/1.51      sK2(X0,X1,k2_tarski(X2,X0)) = X1 | sK2(X0,X1,k2_tarski(X2,X0)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 8.79/1.51  
% 8.79/1.51  cnf(u68,negated_conjecture,
% 8.79/1.51      k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)).
% 8.79/1.51  
% 8.79/1.51  cnf(u4688,axiom,
% 8.79/1.51      X2 != X3 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X4,X5,k2_tarski(X2,X3)),k2_tarski(X2,X3)) = X2 | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X4,X5,k2_tarski(X2,X3))) | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X3) | sK2(X4,X5,k2_tarski(X2,X3)) = X5 | sK2(X4,X5,k2_tarski(X2,X3)) = X4 | k2_tarski(X2,X3) = k2_tarski(X4,X5)).
% 8.79/1.51  
% 8.79/1.51  cnf(u4687,axiom,
% 8.79/1.51      X2 != X3 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X4,X5,k2_tarski(X2,X3)),k2_tarski(X2,X3)) = X3 | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X4,X5,k2_tarski(X2,X3))) | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X3) | sK2(X4,X5,k2_tarski(X2,X3)) = X5 | sK2(X4,X5,k2_tarski(X2,X3)) = X4 | k2_tarski(X2,X3) = k2_tarski(X4,X5)).
% 8.79/1.51  
% 8.79/1.51  cnf(u4206,axiom,
% 8.79/1.51      X2 != X3 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X0,X1,k2_tarski(X2,X3)),k2_tarski(X2,X3)) = X2 | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X0,X1,k2_tarski(X2,X3))) | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 8.79/1.51  
% 8.79/1.51  cnf(u4205,axiom,
% 8.79/1.51      X2 != X3 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X0,X1,k2_tarski(X2,X3)),k2_tarski(X2,X3)) = X3 | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X0,X1,k2_tarski(X2,X3))) | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 8.79/1.51  
% 8.79/1.51  cnf(u3910,axiom,
% 8.79/1.51      X0 != X3 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X3)),k2_tarski(X3,X3)) = X0 | k2_tarski(X3,X3) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X3))) | sK2(X1,X2,k2_tarski(X3,X3)) = X2 | sK2(X1,X2,k2_tarski(X3,X3)) = X1 | k2_tarski(X1,X2) = k2_tarski(X3,X3)).
% 8.79/1.51  
% 8.79/1.51  cnf(u3909,axiom,
% 8.79/1.51      X0 != X3 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X3)),k2_tarski(X3,X3)) = X3 | k2_tarski(X3,X3) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X3))) | sK2(X1,X2,k2_tarski(X3,X3)) = X2 | sK2(X1,X2,k2_tarski(X3,X3)) = X1 | k2_tarski(X1,X2) = k2_tarski(X3,X3)).
% 8.79/1.51  
% 8.79/1.51  cnf(u3624,axiom,
% 8.79/1.51      X2 != X3 | sK2(sK2(X0,X1,k2_tarski(X2,X2)),X3,k2_tarski(X2,X2)) = X3 | k2_tarski(X2,X2) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X2)),X3) | sK2(X0,X1,k2_tarski(X2,X2)) = X1 | sK2(X0,X1,k2_tarski(X2,X2)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 8.79/1.51  
% 8.79/1.51  cnf(u3623,axiom,
% 8.79/1.51      X2 != X3 | sK2(sK2(X0,X1,k2_tarski(X2,X2)),X3,k2_tarski(X2,X2)) = X2 | k2_tarski(X2,X2) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X2)),X3) | sK2(X0,X1,k2_tarski(X2,X2)) = X1 | sK2(X0,X1,k2_tarski(X2,X2)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 8.79/1.51  
% 8.79/1.51  cnf(u2948,axiom,
% 8.79/1.51      X138 != X139 | k2_tarski(X138,X139) = k2_tarski(X139,sK2(X136,X137,k2_tarski(X138,X139))) | ~r2_hidden(X139,k2_tarski(X138,X139)) | sK2(X136,X137,k2_tarski(X138,X139)) = X137 | sK2(X136,X137,k2_tarski(X138,X139)) = X136 | k2_tarski(X136,X137) = k2_tarski(X138,X139)).
% 8.79/1.51  
% 8.79/1.51  cnf(u2696,axiom,
% 8.79/1.51      X127 != X128 | k2_tarski(X127,X128) = k2_tarski(X127,sK2(X125,X126,k2_tarski(X127,X128))) | ~r2_hidden(X127,k2_tarski(X127,X128)) | sK2(X125,X126,k2_tarski(X127,X128)) = X126 | sK2(X125,X126,k2_tarski(X127,X128)) = X125 | k2_tarski(X125,X126) = k2_tarski(X127,X128)).
% 8.79/1.51  
% 8.79/1.51  cnf(u2364,axiom,
% 8.79/1.51      X99 != X100 | k2_tarski(X99,X100) = k2_tarski(X101,X99) | ~r2_hidden(X99,k2_tarski(X101,X99)) | sK2(X99,X100,k2_tarski(X101,X99)) = X101).
% 8.79/1.51  
% 8.79/1.51  cnf(u2349,axiom,
% 8.79/1.51      X99 != X101 | k2_tarski(X99,X100) = k2_tarski(X101,X99) | ~r2_hidden(X99,k2_tarski(X101,X99)) | sK2(X99,X100,k2_tarski(X101,X99)) = X100).
% 8.79/1.51  
% 8.79/1.51  cnf(u2347,axiom,
% 8.79/1.51      X1 != X2 | sK2(X0,X1,k2_tarski(X2,X0)) = X1 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 8.79/1.51  
% 8.79/1.51  cnf(u2346,axiom,
% 8.79/1.51      X1 != X2 | sK2(X0,X1,k2_tarski(X2,X0)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 8.79/1.51  
% 8.79/1.51  cnf(u2203,axiom,
% 8.79/1.51      X92 != X93 | k2_tarski(X92,X93) = k2_tarski(X92,X94) | ~r2_hidden(X92,k2_tarski(X92,X94)) | sK2(X92,X93,k2_tarski(X92,X94)) = X94).
% 8.79/1.51  
% 8.79/1.51  cnf(u2188,axiom,
% 8.79/1.51      X92 != X94 | k2_tarski(X92,X93) = k2_tarski(X92,X94) | ~r2_hidden(X92,k2_tarski(X92,X94)) | sK2(X92,X93,k2_tarski(X92,X94)) = X93).
% 8.79/1.51  
% 8.79/1.51  cnf(u2186,axiom,
% 8.79/1.51      X1 != X2 | sK2(X0,X1,k2_tarski(X0,X2)) = X1 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 8.79/1.51  
% 8.79/1.51  cnf(u2185,axiom,
% 8.79/1.51      X1 != X2 | sK2(X0,X1,k2_tarski(X0,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 8.79/1.51  
% 8.79/1.51  cnf(u2058,axiom,
% 8.79/1.51      X91 != X92 | k2_tarski(X93,X92) = k2_tarski(X91,X92) | ~r2_hidden(X92,k2_tarski(X93,X92)) | sK2(X91,X92,k2_tarski(X93,X92)) = X93).
% 8.79/1.51  
% 8.79/1.51  cnf(u2044,axiom,
% 8.79/1.51      X92 != X93 | k2_tarski(X93,X92) = k2_tarski(X91,X92) | ~r2_hidden(X92,k2_tarski(X93,X92)) | sK2(X91,X92,k2_tarski(X93,X92)) = X91).
% 8.79/1.51  
% 8.79/1.51  cnf(u2043,axiom,
% 8.79/1.51      X0 != X2 | sK2(X0,X1,k2_tarski(X2,X1)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 8.79/1.51  
% 8.79/1.51  cnf(u2042,axiom,
% 8.79/1.51      X0 != X2 | sK2(X0,X1,k2_tarski(X2,X1)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 8.79/1.51  
% 8.79/1.51  cnf(u1891,axiom,
% 8.79/1.51      X90 != X91 | k2_tarski(X90,X91) = k2_tarski(X91,X92) | ~r2_hidden(X91,k2_tarski(X91,X92)) | sK2(X90,X91,k2_tarski(X91,X92)) = X92).
% 8.79/1.51  
% 8.79/1.51  cnf(u1877,axiom,
% 8.79/1.51      X91 != X92 | k2_tarski(X90,X91) = k2_tarski(X91,X92) | ~r2_hidden(X91,k2_tarski(X91,X92)) | sK2(X90,X91,k2_tarski(X91,X92)) = X90).
% 8.79/1.51  
% 8.79/1.51  cnf(u1876,axiom,
% 8.79/1.51      X0 != X2 | sK2(X0,X1,k2_tarski(X1,X2)) = X0 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 8.79/1.51  
% 8.79/1.51  cnf(u1875,axiom,
% 8.79/1.51      X0 != X2 | sK2(X0,X1,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 8.79/1.51  
% 8.79/1.51  cnf(u1733,axiom,
% 8.79/1.51      X62 != X63 | k2_tarski(X62,X62) = k2_tarski(X62,X63) | ~r2_hidden(X62,k2_tarski(X62,X62))).
% 8.79/1.51  
% 8.79/1.51  cnf(u1676,axiom,
% 8.79/1.51      X0 != X1 | sK2(X0,X1,k2_tarski(X0,X0)) = X1 | k2_tarski(X0,X1) = k2_tarski(X0,X0)).
% 8.79/1.51  
% 8.79/1.51  cnf(u1675,axiom,
% 8.79/1.51      X0 != X1 | sK2(X0,X1,k2_tarski(X0,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X0,X0)).
% 8.79/1.51  
% 8.79/1.51  cnf(u1520,axiom,
% 8.79/1.51      X3 != X4 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X0 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X3 | k2_tarski(X3,X4) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X4))) | sK2(X1,X2,k2_tarski(X3,X4)) = X2 | sK2(X1,X2,k2_tarski(X3,X4)) = X1 | k2_tarski(X1,X2) = k2_tarski(X3,X4)).
% 8.79/1.51  
% 8.79/1.51  cnf(u1519,axiom,
% 8.79/1.51      X0 != X4 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X0 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X3 | k2_tarski(X3,X4) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X4))) | sK2(X1,X2,k2_tarski(X3,X4)) = X2 | sK2(X1,X2,k2_tarski(X3,X4)) = X1 | k2_tarski(X1,X2) = k2_tarski(X3,X4)).
% 8.79/1.51  
% 8.79/1.51  cnf(u1518,axiom,
% 8.79/1.51      X3 != X4 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X0 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X4 | k2_tarski(X3,X4) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X4))) | sK2(X1,X2,k2_tarski(X3,X4)) = X2 | sK2(X1,X2,k2_tarski(X3,X4)) = X1 | k2_tarski(X1,X2) = k2_tarski(X3,X4)).
% 8.79/1.51  
% 8.79/1.51  cnf(u1517,axiom,
% 8.79/1.51      X0 != X3 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X0 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X4 | k2_tarski(X3,X4) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X4))) | sK2(X1,X2,k2_tarski(X3,X4)) = X2 | sK2(X1,X2,k2_tarski(X3,X4)) = X1 | k2_tarski(X1,X2) = k2_tarski(X3,X4)).
% 8.79/1.51  
% 8.79/1.51  cnf(u1516,axiom,
% 8.79/1.51      X0 != X4 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X3 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X4 | k2_tarski(X3,X4) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X4))) | sK2(X1,X2,k2_tarski(X3,X4)) = X2 | sK2(X1,X2,k2_tarski(X3,X4)) = X1 | k2_tarski(X1,X2) = k2_tarski(X3,X4)).
% 8.79/1.51  
% 8.79/1.51  cnf(u1515,axiom,
% 8.79/1.51      X0 != X3 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X3 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X4 | k2_tarski(X3,X4) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X4))) | sK2(X1,X2,k2_tarski(X3,X4)) = X2 | sK2(X1,X2,k2_tarski(X3,X4)) = X1 | k2_tarski(X1,X2) = k2_tarski(X3,X4)).
% 8.79/1.51  
% 8.79/1.51  cnf(u1264,axiom,
% 8.79/1.51      X52 != X53 | k2_tarski(X53,X53) = k2_tarski(X52,X53) | ~r2_hidden(X53,k2_tarski(X53,X53))).
% 8.79/1.51  
% 8.79/1.51  cnf(u1154,axiom,
% 8.79/1.51      X2 != X3 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X4 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X2 | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),X4) | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 8.79/1.51  
% 8.79/1.51  cnf(u1153,axiom,
% 8.79/1.51      X3 != X4 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X4 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X2 | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),X4) | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 8.79/1.51  
% 8.79/1.51  cnf(u1152,axiom,
% 8.79/1.51      X2 != X3 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X4 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X3 | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),X4) | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 8.79/1.51  
% 8.79/1.51  cnf(u1151,axiom,
% 8.79/1.51      X2 != X4 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X4 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X3 | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),X4) | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 8.79/1.51  
% 8.79/1.51  cnf(u1150,axiom,
% 8.79/1.51      X3 != X4 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X2 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X3 | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),X4) | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 8.79/1.51  
% 8.79/1.51  cnf(u1149,axiom,
% 8.79/1.51      X2 != X4 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X2 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X3 | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),X4) | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 8.79/1.51  
% 8.79/1.51  cnf(u921,axiom,
% 8.79/1.51      X0 != X1 | sK2(X0,X1,k2_tarski(X1,X1)) = X0 | k2_tarski(X0,X1) = k2_tarski(X1,X1)).
% 8.79/1.51  
% 8.79/1.51  cnf(u920,axiom,
% 8.79/1.51      X0 != X1 | sK2(X0,X1,k2_tarski(X1,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X1,X1)).
% 8.79/1.51  
% 8.79/1.51  cnf(u773,axiom,
% 8.79/1.51      X0 != X2 | sK2(X0,X1,k2_tarski(X2,X2)) = X1 | sK2(X0,X1,k2_tarski(X2,X2)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 8.79/1.51  
% 8.79/1.51  cnf(u772,axiom,
% 8.79/1.51      X1 != X2 | sK2(X0,X1,k2_tarski(X2,X2)) = X1 | sK2(X0,X1,k2_tarski(X2,X2)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 8.79/1.51  
% 8.79/1.51  cnf(u771,axiom,
% 8.79/1.51      X0 != X2 | sK2(X0,X1,k2_tarski(X2,X2)) = X1 | sK2(X0,X1,k2_tarski(X2,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 8.79/1.51  
% 8.79/1.51  cnf(u770,axiom,
% 8.79/1.51      X0 != X1 | sK2(X0,X1,k2_tarski(X2,X2)) = X1 | sK2(X0,X1,k2_tarski(X2,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 8.79/1.51  
% 8.79/1.51  cnf(u769,axiom,
% 8.79/1.51      X1 != X2 | sK2(X0,X1,k2_tarski(X2,X2)) = X0 | sK2(X0,X1,k2_tarski(X2,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 8.79/1.51  
% 8.79/1.51  cnf(u768,axiom,
% 8.79/1.51      X0 != X1 | sK2(X0,X1,k2_tarski(X2,X2)) = X0 | sK2(X0,X1,k2_tarski(X2,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 8.79/1.51  
% 8.79/1.51  cnf(u681,axiom,
% 8.79/1.51      X0 != X1 | sK2(X0,X1,k2_tarski(X1,X0)) = X1 | k2_tarski(X0,X1) = k2_tarski(X1,X0)).
% 8.79/1.51  
% 8.79/1.51  cnf(u680,axiom,
% 8.79/1.51      X0 != X1 | sK2(X0,X1,k2_tarski(X1,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X1,X0)).
% 8.79/1.51  
% 8.79/1.51  cnf(u640,axiom,
% 8.79/1.51      X0 != X2 | sK2(X0,X1,k2_tarski(X2,X0)) = X1 | sK2(X0,X1,k2_tarski(X2,X0)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 8.79/1.51  
% 8.79/1.51  cnf(u639,axiom,
% 8.79/1.51      X0 != X1 | sK2(X0,X1,k2_tarski(X2,X0)) = X1 | sK2(X0,X1,k2_tarski(X2,X0)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 8.79/1.51  
% 8.79/1.51  cnf(u638,axiom,
% 8.79/1.51      X0 != X2 | sK2(X0,X1,k2_tarski(X2,X0)) = X1 | sK2(X0,X1,k2_tarski(X2,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 8.79/1.51  
% 8.79/1.51  cnf(u637,axiom,
% 8.79/1.51      X1 != X2 | sK2(X0,X1,k2_tarski(X2,X0)) = X1 | sK2(X0,X1,k2_tarski(X2,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 8.79/1.51  
% 8.79/1.51  cnf(u636,axiom,
% 8.79/1.51      X0 != X1 | sK2(X0,X1,k2_tarski(X2,X0)) = X2 | sK2(X0,X1,k2_tarski(X2,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 8.79/1.51  
% 8.79/1.51  cnf(u635,axiom,
% 8.79/1.51      X1 != X2 | sK2(X0,X1,k2_tarski(X2,X0)) = X2 | sK2(X0,X1,k2_tarski(X2,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 8.79/1.51  
% 8.79/1.51  cnf(u548,axiom,
% 8.79/1.51      X0 != X2 | sK2(X0,X1,k2_tarski(X0,X2)) = X1 | sK2(X0,X1,k2_tarski(X0,X2)) = X0 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 8.79/1.51  
% 8.79/1.51  cnf(u547,axiom,
% 8.79/1.51      X1 != X2 | sK2(X0,X1,k2_tarski(X0,X2)) = X1 | sK2(X0,X1,k2_tarski(X0,X2)) = X0 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 8.79/1.51  
% 8.79/1.51  cnf(u546,axiom,
% 8.79/1.51      X0 != X2 | sK2(X0,X1,k2_tarski(X0,X2)) = X1 | sK2(X0,X1,k2_tarski(X0,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 8.79/1.51  
% 8.79/1.51  cnf(u545,axiom,
% 8.79/1.51      X0 != X1 | sK2(X0,X1,k2_tarski(X0,X2)) = X1 | sK2(X0,X1,k2_tarski(X0,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 8.79/1.51  
% 8.79/1.51  cnf(u544,axiom,
% 8.79/1.51      X1 != X2 | sK2(X0,X1,k2_tarski(X0,X2)) = X0 | sK2(X0,X1,k2_tarski(X0,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 8.79/1.51  
% 8.79/1.51  cnf(u543,axiom,
% 8.79/1.51      X0 != X1 | sK2(X0,X1,k2_tarski(X0,X2)) = X0 | sK2(X0,X1,k2_tarski(X0,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 8.79/1.51  
% 8.79/1.51  cnf(u466,axiom,
% 8.79/1.51      X1 != X2 | sK2(X0,X1,k2_tarski(X2,X1)) = X0 | sK2(X0,X1,k2_tarski(X2,X1)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 8.79/1.51  
% 8.79/1.51  cnf(u465,axiom,
% 8.79/1.51      X0 != X1 | sK2(X0,X1,k2_tarski(X2,X1)) = X0 | sK2(X0,X1,k2_tarski(X2,X1)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 8.79/1.51  
% 8.79/1.51  cnf(u464,axiom,
% 8.79/1.51      X1 != X2 | sK2(X0,X1,k2_tarski(X2,X1)) = X0 | sK2(X0,X1,k2_tarski(X2,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 8.79/1.51  
% 8.79/1.51  cnf(u463,axiom,
% 8.79/1.51      X0 != X2 | sK2(X0,X1,k2_tarski(X2,X1)) = X0 | sK2(X0,X1,k2_tarski(X2,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 8.79/1.51  
% 8.79/1.51  cnf(u462,axiom,
% 8.79/1.51      X0 != X1 | sK2(X0,X1,k2_tarski(X2,X1)) = X2 | sK2(X0,X1,k2_tarski(X2,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 8.79/1.51  
% 8.79/1.51  cnf(u461,axiom,
% 8.79/1.51      X0 != X2 | sK2(X0,X1,k2_tarski(X2,X1)) = X2 | sK2(X0,X1,k2_tarski(X2,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 8.79/1.51  
% 8.79/1.51  cnf(u394,axiom,
% 8.79/1.51      X1 != X2 | sK2(X0,X1,k2_tarski(X1,X2)) = X0 | sK2(X0,X1,k2_tarski(X1,X2)) = X1 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 8.79/1.51  
% 8.79/1.51  cnf(u393,axiom,
% 8.79/1.51      X0 != X2 | sK2(X0,X1,k2_tarski(X1,X2)) = X0 | sK2(X0,X1,k2_tarski(X1,X2)) = X1 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 8.79/1.51  
% 8.79/1.51  cnf(u392,axiom,
% 8.79/1.51      X1 != X2 | sK2(X0,X1,k2_tarski(X1,X2)) = X0 | sK2(X0,X1,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 8.79/1.51  
% 8.79/1.51  cnf(u391,axiom,
% 8.79/1.51      X0 != X1 | sK2(X0,X1,k2_tarski(X1,X2)) = X0 | sK2(X0,X1,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 8.79/1.51  
% 8.79/1.51  cnf(u390,axiom,
% 8.79/1.51      X0 != X2 | sK2(X0,X1,k2_tarski(X1,X2)) = X1 | sK2(X0,X1,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 8.79/1.51  
% 8.79/1.51  cnf(u389,axiom,
% 8.79/1.51      X0 != X1 | sK2(X0,X1,k2_tarski(X1,X2)) = X1 | sK2(X0,X1,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 8.79/1.51  
% 8.79/1.51  cnf(u326,axiom,
% 8.79/1.51      X0 != X1 | sK2(X0,X0,k2_tarski(X1,X1)) = X0 | k2_tarski(X0,X0) = k2_tarski(X1,X1)).
% 8.79/1.51  
% 8.79/1.51  cnf(u325,axiom,
% 8.79/1.51      X0 != X1 | sK2(X0,X0,k2_tarski(X1,X1)) = X1 | k2_tarski(X0,X0) = k2_tarski(X1,X1)).
% 8.79/1.51  
% 8.79/1.51  cnf(u292,axiom,
% 8.79/1.51      X12 != X13 | k2_tarski(X12,X12) = k2_tarski(X13,X12) | ~r2_hidden(X12,k2_tarski(X13,X12))).
% 8.79/1.51  
% 8.79/1.51  cnf(u259,axiom,
% 8.79/1.51      X0 != X1 | sK2(X0,X0,k2_tarski(X1,X0)) = X1 | k2_tarski(X0,X0) = k2_tarski(X1,X0)).
% 8.79/1.51  
% 8.79/1.51  cnf(u258,axiom,
% 8.79/1.51      X0 != X1 | sK2(X0,X0,k2_tarski(X1,X0)) = X0 | k2_tarski(X0,X0) = k2_tarski(X1,X0)).
% 8.79/1.51  
% 8.79/1.51  cnf(u225,axiom,
% 8.79/1.51      X12 != X13 | k2_tarski(X12,X12) = k2_tarski(X12,X13) | ~r2_hidden(X12,k2_tarski(X12,X13))).
% 8.79/1.51  
% 8.79/1.51  cnf(u196,axiom,
% 8.79/1.51      X0 != X1 | sK2(X0,X0,k2_tarski(X0,X1)) = X0 | k2_tarski(X0,X1) = k2_tarski(X0,X0)).
% 8.79/1.51  
% 8.79/1.51  cnf(u195,axiom,
% 8.79/1.51      X0 != X1 | sK2(X0,X0,k2_tarski(X0,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X0,X0)).
% 8.79/1.51  
% 8.79/1.51  cnf(u159,axiom,
% 8.79/1.51      X1 != X2 | sK2(X0,X0,k2_tarski(X1,X2)) = X0 | sK2(X0,X0,k2_tarski(X1,X2)) = X1 | k2_tarski(X0,X0) = k2_tarski(X1,X2)).
% 8.79/1.51  
% 8.79/1.51  cnf(u158,axiom,
% 8.79/1.51      X0 != X2 | sK2(X0,X0,k2_tarski(X1,X2)) = X0 | sK2(X0,X0,k2_tarski(X1,X2)) = X1 | k2_tarski(X0,X0) = k2_tarski(X1,X2)).
% 8.79/1.51  
% 8.79/1.51  cnf(u157,axiom,
% 8.79/1.51      X1 != X2 | sK2(X0,X0,k2_tarski(X1,X2)) = X0 | sK2(X0,X0,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X0) = k2_tarski(X1,X2)).
% 8.79/1.51  
% 8.79/1.51  cnf(u156,axiom,
% 8.79/1.51      X0 != X1 | sK2(X0,X0,k2_tarski(X1,X2)) = X0 | sK2(X0,X0,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X0) = k2_tarski(X1,X2)).
% 8.79/1.51  
% 8.79/1.51  cnf(u155,axiom,
% 8.79/1.51      X0 != X2 | sK2(X0,X0,k2_tarski(X1,X2)) = X1 | sK2(X0,X0,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X0) = k2_tarski(X1,X2)).
% 8.79/1.51  
% 8.79/1.51  cnf(u154,axiom,
% 8.79/1.51      X0 != X1 | sK2(X0,X0,k2_tarski(X1,X2)) = X1 | sK2(X0,X0,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X0) = k2_tarski(X1,X2)).
% 8.79/1.51  
% 8.79/1.51  cnf(u109,axiom,
% 8.79/1.51      X2 != X3 | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | sK2(X0,X1,k2_tarski(X2,X3)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 8.79/1.51  
% 8.79/1.51  cnf(u108,axiom,
% 8.79/1.51      X0 != X3 | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | sK2(X0,X1,k2_tarski(X2,X3)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 8.79/1.51  
% 8.79/1.51  cnf(u107,axiom,
% 8.79/1.51      X1 != X3 | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | sK2(X0,X1,k2_tarski(X2,X3)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 8.79/1.51  
% 8.79/1.51  cnf(u106,axiom,
% 8.79/1.51      X2 != X3 | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | sK2(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 8.79/1.51  
% 8.79/1.51  cnf(u105,axiom,
% 8.79/1.51      X0 != X2 | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | sK2(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 8.79/1.51  
% 8.79/1.51  cnf(u104,axiom,
% 8.79/1.51      X1 != X2 | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | sK2(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 8.79/1.51  
% 8.79/1.51  cnf(u103,axiom,
% 8.79/1.51      X0 != X3 | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X2 | sK2(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 8.79/1.51  
% 8.79/1.51  cnf(u102,axiom,
% 8.79/1.51      X0 != X2 | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X2 | sK2(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 8.79/1.51  
% 8.79/1.51  cnf(u101,axiom,
% 8.79/1.51      X0 != X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X2 | sK2(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 8.79/1.51  
% 8.79/1.51  cnf(u100,axiom,
% 8.79/1.51      X1 != X3 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | sK2(X0,X1,k2_tarski(X2,X3)) = X2 | sK2(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 8.79/1.51  
% 8.79/1.51  cnf(u99,axiom,
% 8.79/1.51      X1 != X2 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | sK2(X0,X1,k2_tarski(X2,X3)) = X2 | sK2(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 8.79/1.51  
% 8.79/1.51  cnf(u98,axiom,
% 8.79/1.51      X0 != X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | sK2(X0,X1,k2_tarski(X2,X3)) = X2 | sK2(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 8.79/1.51  
% 8.79/1.51  cnf(u70,negated_conjecture,
% 8.79/1.51      sK1 != k2_yellow_0(sK0,k2_tarski(sK1,sK1)) | sK1 != k1_yellow_0(sK0,k2_tarski(sK1,sK1))).
% 8.79/1.51  
% 8.79/1.51  cnf(u3641,axiom,
% 8.79/1.51      sK2(X160,X161,k2_tarski(X162,X162)) != X163 | k2_tarski(X162,X162) = k2_tarski(sK2(X160,X161,k2_tarski(X162,X162)),X163) | ~r2_hidden(sK2(X160,X161,k2_tarski(X162,X162)),k2_tarski(X162,X162)) | sK2(sK2(X160,X161,k2_tarski(X162,X162)),X163,k2_tarski(X162,X162)) = X162 | sK2(X160,X161,k2_tarski(X162,X162)) = X161 | sK2(X160,X161,k2_tarski(X162,X162)) = X160 | k2_tarski(X160,X161) = k2_tarski(X162,X162)).
% 8.79/1.51  
% 8.79/1.51  cnf(u3930,axiom,
% 8.79/1.51      sK2(X172,X173,k2_tarski(X174,X174)) != X171 | k2_tarski(X174,X174) = k2_tarski(X171,sK2(X172,X173,k2_tarski(X174,X174))) | ~r2_hidden(sK2(X172,X173,k2_tarski(X174,X174)),k2_tarski(X174,X174)) | sK2(X171,sK2(X172,X173,k2_tarski(X174,X174)),k2_tarski(X174,X174)) = X174 | sK2(X172,X173,k2_tarski(X174,X174)) = X173 | sK2(X172,X173,k2_tarski(X174,X174)) = X172 | k2_tarski(X172,X173) = k2_tarski(X174,X174)).
% 8.79/1.51  
% 8.79/1.51  cnf(u1163,axiom,
% 8.79/1.51      sK2(X67,X68,k2_tarski(X69,X70)) != X71 | k2_tarski(X69,X70) = k2_tarski(sK2(X67,X68,k2_tarski(X69,X70)),X71) | ~r2_hidden(sK2(X67,X68,k2_tarski(X69,X70)),k2_tarski(X69,X70)) | sK2(sK2(X67,X68,k2_tarski(X69,X70)),X71,k2_tarski(X69,X70)) = X69 | sK2(sK2(X67,X68,k2_tarski(X69,X70)),X71,k2_tarski(X69,X70)) = X70 | sK2(X67,X68,k2_tarski(X69,X70)) = X68 | sK2(X67,X68,k2_tarski(X69,X70)) = X67 | k2_tarski(X69,X70) = k2_tarski(X67,X68)).
% 8.79/1.51  
% 8.79/1.51  cnf(u1536,axiom,
% 8.79/1.51      sK2(X85,X86,k2_tarski(X87,X88)) != X84 | k2_tarski(X87,X88) = k2_tarski(X84,sK2(X85,X86,k2_tarski(X87,X88))) | ~r2_hidden(sK2(X85,X86,k2_tarski(X87,X88)),k2_tarski(X87,X88)) | sK2(X84,sK2(X85,X86,k2_tarski(X87,X88)),k2_tarski(X87,X88)) = X87 | sK2(X84,sK2(X85,X86,k2_tarski(X87,X88)),k2_tarski(X87,X88)) = X88 | sK2(X85,X86,k2_tarski(X87,X88)) = X86 | sK2(X85,X86,k2_tarski(X87,X88)) = X85 | k2_tarski(X85,X86) = k2_tarski(X87,X88)).
% 8.79/1.51  
% 8.79/1.51  cnf(u61,axiom,
% 8.79/1.51      sK2(X0,X1,X2) != X0 | k2_tarski(X0,X1) = X2 | ~r2_hidden(X0,X2)).
% 8.79/1.51  
% 8.79/1.51  cnf(u60,axiom,
% 8.79/1.51      sK2(X0,X1,X2) != X1 | k2_tarski(X0,X1) = X2 | ~r2_hidden(X1,X2)).
% 8.79/1.51  
% 8.79/1.51  % (6915)# SZS output end Saturation.
% 8.79/1.51  % (6915)------------------------------
% 8.79/1.51  % (6915)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.79/1.51  % (6915)Termination reason: Satisfiable
% 8.79/1.51  
% 8.79/1.51  % (6915)Memory used [KB]: 4605
% 8.79/1.51  % (6915)Time elapsed: 1.090 s
% 8.79/1.51  % (6915)------------------------------
% 8.79/1.51  % (6915)------------------------------
% 8.79/1.51  % (6909)Success in time 1.13 s
%------------------------------------------------------------------------------
