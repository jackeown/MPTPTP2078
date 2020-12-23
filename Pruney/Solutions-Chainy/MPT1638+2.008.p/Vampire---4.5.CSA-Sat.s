%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:58 EST 2020

% Result     : CounterSatisfiable 7.27s
% Output     : Saturation 7.27s
% Verified   : 
% Statistics : Number of clauses        :  230 ( 230 expanded)
%              Number of leaves         :  230 ( 230 expanded)
%              Depth                    :    0
%              Number of atoms          :  965 ( 965 expanded)
%              Number of equality atoms :  882 ( 882 expanded)
%              Maximal clause size      :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u30,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u115,negated_conjecture,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) )).

cnf(u64,negated_conjecture,
    ( m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) )).

cnf(u41,axiom,
    ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
    | ~ m1_subset_1(X1,X0)
    | v1_xboole_0(X0) )).

cnf(u32,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) )).

cnf(u31,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

cnf(u58,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k2_tarski(X0,X0) = k6_domain_1(u1_struct_0(sK0),X0)
    | ~ l1_struct_0(sK0) )).

cnf(u46,axiom,
    ( v1_xboole_0(X0)
    | ~ m1_subset_1(X1,X0)
    | k6_domain_1(X0,X1) = k2_tarski(X1,X1) )).

cnf(u55,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(sK0) )).

cnf(u44,axiom,
    ( l1_struct_0(X0)
    | ~ l1_orders_2(X0) )).

cnf(u43,axiom,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) )).

cnf(u29,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u38,axiom,
    ( r2_hidden(sK3(X0,X1,X2),X2)
    | sK3(X0,X1,X2) = X1
    | sK3(X0,X1,X2) = X0
    | k2_tarski(X0,X1) = X2 )).

cnf(u50,axiom,
    ( r2_hidden(X4,k2_tarski(X4,X1)) )).

cnf(u48,axiom,
    ( r2_hidden(X4,k2_tarski(X0,X4)) )).

cnf(u33,negated_conjecture,
    ( r2_hidden(sK2,k6_waybel_0(sK0,sK1))
    | r1_orders_2(sK0,sK1,sK2) )).

cnf(u912,axiom,
    ( ~ r2_hidden(X40,k2_tarski(X40,X40))
    | k2_tarski(X40,X40) = k2_tarski(X39,X40)
    | sK3(X39,X40,k2_tarski(X40,X40)) = X39 )).

cnf(u1662,axiom,
    ( ~ r2_hidden(X58,k2_tarski(X58,X58))
    | k2_tarski(X58,X59) = k2_tarski(X58,X58)
    | sK3(X58,X59,k2_tarski(X58,X58)) = X59 )).

cnf(u195,axiom,
    ( ~ r2_hidden(X12,k2_tarski(X12,X13))
    | k2_tarski(X12,X12) = k2_tarski(X12,X13)
    | sK3(X12,X12,k2_tarski(X12,X13)) = X13 )).

cnf(u793,axiom,
    ( ~ r2_hidden(X38,k2_tarski(X38,X37))
    | k2_tarski(X38,X37) = k2_tarski(X37,X38) )).

cnf(u390,axiom,
    ( ~ r2_hidden(X19,k2_tarski(X19,X20))
    | k2_tarski(X19,X20) = k2_tarski(X18,X19)
    | sK3(X18,X19,k2_tarski(X19,X20)) = X18
    | sK3(X18,X19,k2_tarski(X19,X20)) = X20 )).

cnf(u545,axiom,
    ( ~ r2_hidden(X27,k2_tarski(X27,X29))
    | k2_tarski(X27,X29) = k2_tarski(X27,X28)
    | sK3(X27,X28,k2_tarski(X27,X29)) = X28
    | sK3(X27,X28,k2_tarski(X27,X29)) = X29 )).

cnf(u2432,axiom,
    ( ~ r2_hidden(X260,k2_tarski(X259,X259))
    | k2_tarski(X259,X259) = k2_tarski(sK3(X257,X258,k2_tarski(X259,X259)),X260)
    | sK3(sK3(X257,X258,k2_tarski(X259,X259)),X260,k2_tarski(X259,X259)) = X259
    | sK3(X257,X258,k2_tarski(X259,X259)) = X258
    | sK3(X257,X258,k2_tarski(X259,X259)) = X257
    | k2_tarski(X259,X259) = k2_tarski(X257,X258) )).

cnf(u2424,axiom,
    ( ~ r2_hidden(X228,k2_tarski(X227,X227))
    | k2_tarski(X227,X227) = k2_tarski(X228,sK3(X225,X226,k2_tarski(X227,X227)))
    | sK3(X228,sK3(X225,X226,k2_tarski(X227,X227)),k2_tarski(X227,X227)) = X227
    | sK3(X225,X226,k2_tarski(X227,X227)) = X226
    | sK3(X225,X226,k2_tarski(X227,X227)) = X225
    | k2_tarski(X227,X227) = k2_tarski(X225,X226) )).

cnf(u2370,axiom,
    ( ~ r2_hidden(X9,k2_tarski(X8,X8))
    | sK3(X6,X7,k2_tarski(X8,X8)) = X9
    | X8 = X9
    | sK3(X6,X7,k2_tarski(X8,X8)) = X7
    | sK3(X6,X7,k2_tarski(X8,X8)) = X6
    | k2_tarski(X6,X7) = k2_tarski(X8,X8) )).

cnf(u1715,axiom,
    ( ~ r2_hidden(X65,k2_tarski(X64,X64))
    | k2_tarski(X64,X65) = k2_tarski(X64,X64) )).

cnf(u1589,axiom,
    ( ~ r2_hidden(X59,k2_tarski(X60,X60))
    | k2_tarski(X60,X60) = k2_tarski(X59,X60) )).

cnf(u772,axiom,
    ( ~ r2_hidden(X45,k2_tarski(X46,X46))
    | k2_tarski(X44,X45) = k2_tarski(X46,X46)
    | sK3(X44,X45,k2_tarski(X46,X46)) = X44
    | sK3(X44,X45,k2_tarski(X46,X46)) = X46 )).

cnf(u770,axiom,
    ( ~ r2_hidden(X41,k2_tarski(X43,X43))
    | k2_tarski(X43,X43) = k2_tarski(X41,X42)
    | sK3(X41,X42,k2_tarski(X43,X43)) = X42
    | sK3(X41,X42,k2_tarski(X43,X43)) = X43 )).

cnf(u323,axiom,
    ( ~ r2_hidden(X12,k2_tarski(X13,X13))
    | k2_tarski(X12,X12) = k2_tarski(X13,X13)
    | sK3(X12,X12,k2_tarski(X13,X13)) = X13 )).

cnf(u255,axiom,
    ( ~ r2_hidden(X12,k2_tarski(X13,X12))
    | k2_tarski(X12,X12) = k2_tarski(X13,X12)
    | sK3(X12,X12,k2_tarski(X13,X12)) = X13 )).

cnf(u675,axiom,
    ( ~ r2_hidden(X28,k2_tarski(X29,X28))
    | k2_tarski(X29,X28) = k2_tarski(X28,X29)
    | sK3(X28,X29,k2_tarski(X29,X28)) = X29 )).

cnf(u459,axiom,
    ( ~ r2_hidden(X25,k2_tarski(X26,X25))
    | k2_tarski(X26,X25) = k2_tarski(X24,X25)
    | sK3(X24,X25,k2_tarski(X26,X25)) = X24
    | sK3(X24,X25,k2_tarski(X26,X25)) = X26 )).

cnf(u633,axiom,
    ( ~ r2_hidden(X33,k2_tarski(X35,X33))
    | k2_tarski(X33,X34) = k2_tarski(X35,X33)
    | sK3(X33,X34,k2_tarski(X35,X33)) = X34
    | sK3(X33,X34,k2_tarski(X35,X33)) = X35 )).

cnf(u2188,axiom,
    ( ~ r2_hidden(X2,k2_tarski(X1,X0))
    | k2_tarski(X1,X0) = k2_tarski(X0,X2)
    | sK3(X0,X2,k2_tarski(X1,X0)) = X1 )).

cnf(u2173,axiom,
    ( ~ r2_hidden(X96,k2_tarski(X95,X97))
    | k2_tarski(X95,X96) = k2_tarski(X95,X97)
    | sK3(X95,X96,k2_tarski(X95,X97)) = X97 )).

cnf(u1894,axiom,
    ( ~ r2_hidden(X2,k2_tarski(X1,X0))
    | k2_tarski(X1,X0) = k2_tarski(X2,X0)
    | sK3(X2,X0,k2_tarski(X1,X0)) = X1 )).

cnf(u1872,axiom,
    ( ~ r2_hidden(X87,k2_tarski(X88,X89))
    | k2_tarski(X88,X89) = k2_tarski(X87,X88)
    | sK3(X87,X88,k2_tarski(X88,X89)) = X89 )).

cnf(u1473,axiom,
    ( ~ r2_hidden(X79,k2_tarski(X82,X83))
    | k2_tarski(X82,X83) = k2_tarski(X79,sK3(X80,X81,k2_tarski(X82,X83)))
    | sK3(X79,sK3(X80,X81,k2_tarski(X82,X83)),k2_tarski(X82,X83)) = X82
    | sK3(X79,sK3(X80,X81,k2_tarski(X82,X83)),k2_tarski(X82,X83)) = X83
    | sK3(X80,X81,k2_tarski(X82,X83)) = X81
    | sK3(X80,X81,k2_tarski(X82,X83)) = X80
    | k2_tarski(X82,X83) = k2_tarski(X80,X81) )).

cnf(u1143,axiom,
    ( ~ r2_hidden(X76,k2_tarski(X74,X75))
    | k2_tarski(X74,X75) = k2_tarski(sK3(X72,X73,k2_tarski(X74,X75)),X76)
    | sK3(sK3(X72,X73,k2_tarski(X74,X75)),X76,k2_tarski(X74,X75)) = X74
    | sK3(sK3(X72,X73,k2_tarski(X74,X75)),X76,k2_tarski(X74,X75)) = X75
    | sK3(X72,X73,k2_tarski(X74,X75)) = X73
    | sK3(X72,X73,k2_tarski(X74,X75)) = X72
    | k2_tarski(X74,X75) = k2_tarski(X72,X73) )).

cnf(u638,axiom,
    ( ~ r2_hidden(X37,k2_tarski(X38,X36))
    | k2_tarski(X36,X37) = k2_tarski(X38,X36)
    | sK3(X36,X37,k2_tarski(X38,X36)) = X38
    | sK3(X36,X37,k2_tarski(X38,X36)) = X36 )).

cnf(u547,axiom,
    ( ~ r2_hidden(X31,k2_tarski(X30,X32))
    | k2_tarski(X30,X32) = k2_tarski(X30,X31)
    | sK3(X30,X31,k2_tarski(X30,X32)) = X30
    | sK3(X30,X31,k2_tarski(X30,X32)) = X32 )).

cnf(u466,axiom,
    ( ~ r2_hidden(X21,k2_tarski(X23,X22))
    | k2_tarski(X23,X22) = k2_tarski(X21,X22)
    | sK3(X21,X22,k2_tarski(X23,X22)) = X23
    | sK3(X21,X22,k2_tarski(X23,X22)) = X22 )).

cnf(u394,axiom,
    ( ~ r2_hidden(X15,k2_tarski(X16,X17))
    | k2_tarski(X16,X17) = k2_tarski(X15,X16)
    | sK3(X15,X16,k2_tarski(X16,X17)) = X16
    | sK3(X15,X16,k2_tarski(X16,X17)) = X17 )).

cnf(u162,axiom,
    ( ~ r2_hidden(X18,k2_tarski(X19,X20))
    | k2_tarski(X19,X20) = k2_tarski(X18,X18)
    | sK3(X18,X18,k2_tarski(X19,X20)) = X19
    | sK3(X18,X18,k2_tarski(X19,X20)) = X20 )).

cnf(u113,axiom,
    ( ~ r2_hidden(X9,k2_tarski(X10,X11))
    | k2_tarski(X10,X11) = k2_tarski(X8,X9)
    | sK3(X8,X9,k2_tarski(X10,X11)) = X8
    | sK3(X8,X9,k2_tarski(X10,X11)) = X10
    | sK3(X8,X9,k2_tarski(X10,X11)) = X11 )).

cnf(u111,axiom,
    ( ~ r2_hidden(X4,k2_tarski(X6,X7))
    | k2_tarski(X6,X7) = k2_tarski(X4,X5)
    | sK3(X4,X5,k2_tarski(X6,X7)) = X5
    | sK3(X4,X5,k2_tarski(X6,X7)) = X6
    | sK3(X4,X5,k2_tarski(X6,X7)) = X7 )).

cnf(u51,axiom,
    ( ~ r2_hidden(X4,k2_tarski(X0,X1))
    | X0 = X4
    | X1 = X4 )).

cnf(u34,negated_conjecture,
    ( ~ r2_hidden(sK2,k6_waybel_0(sK0,sK1))
    | ~ r1_orders_2(sK0,sK1,sK2) )).

cnf(u2180,axiom,
    ( sK3(sK3(X5,X6,k2_tarski(X4,X4)),X7,k2_tarski(X4,X4)) = X7
    | sK3(sK3(X5,X6,k2_tarski(X4,X4)),X7,k2_tarski(X4,X4)) = X4
    | k2_tarski(X4,X4) = k2_tarski(sK3(X5,X6,k2_tarski(X4,X4)),X7)
    | sK3(X5,X6,k2_tarski(X4,X4)) = X6
    | sK3(X5,X6,k2_tarski(X4,X4)) = X5
    | k2_tarski(X4,X4) = k2_tarski(X5,X6) )).

cnf(u2180_001,axiom,
    ( sK3(sK3(X5,X6,k2_tarski(X4,X4)),X7,k2_tarski(X4,X4)) = X7
    | sK3(sK3(X5,X6,k2_tarski(X4,X4)),X7,k2_tarski(X4,X4)) = X4
    | k2_tarski(X4,X4) = k2_tarski(sK3(X5,X6,k2_tarski(X4,X4)),X7)
    | sK3(X5,X6,k2_tarski(X4,X4)) = X6
    | sK3(X5,X6,k2_tarski(X4,X4)) = X5
    | k2_tarski(X4,X4) = k2_tarski(X5,X6) )).

cnf(u4999,axiom,
    ( sK3(sK3(X0,X1,k2_tarski(X2,X2)),sK3(X3,X4,k2_tarski(X2,X2)),k2_tarski(X2,X2)) = X2
    | k2_tarski(X2,X2) = k2_tarski(sK3(X0,X1,k2_tarski(X2,X2)),sK3(X3,X4,k2_tarski(X2,X2)))
    | sK3(X0,X1,k2_tarski(X2,X2)) = X1
    | sK3(X0,X1,k2_tarski(X2,X2)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X2)
    | sK3(X3,X4,k2_tarski(X2,X2)) = X4
    | sK3(X3,X4,k2_tarski(X2,X2)) = X3
    | k2_tarski(X2,X2) = k2_tarski(X3,X4) )).

cnf(u2578,axiom,
    ( sK3(sK3(X16,X17,k2_tarski(X15,X15)),sK3(X13,X14,k2_tarski(X15,X15)),k2_tarski(X15,X15)) = X15
    | k2_tarski(X15,X15) = k2_tarski(sK3(X13,X14,k2_tarski(X15,X15)),sK3(X16,X17,k2_tarski(X15,X15)))
    | sK3(X16,X17,k2_tarski(X15,X15)) = X17
    | sK3(X16,X17,k2_tarski(X15,X15)) = X16
    | k2_tarski(X16,X17) = k2_tarski(X15,X15)
    | sK3(X13,X14,k2_tarski(X15,X15)) = X14
    | sK3(X13,X14,k2_tarski(X15,X15)) = X13
    | k2_tarski(X13,X14) = k2_tarski(X15,X15) )).

cnf(u330,axiom,
    ( sK3(sK3(X2,X3,k2_tarski(X4,X4)),sK3(X2,X3,k2_tarski(X4,X4)),k2_tarski(X4,X4)) = X4
    | k2_tarski(X4,X4) = k2_tarski(sK3(X2,X3,k2_tarski(X4,X4)),sK3(X2,X3,k2_tarski(X4,X4)))
    | sK3(X2,X3,k2_tarski(X4,X4)) = X3
    | sK3(X2,X3,k2_tarski(X4,X4)) = X2
    | k2_tarski(X2,X3) = k2_tarski(X4,X4) )).

cnf(u3149,axiom,
    ( sK3(sK3(X10,X11,k2_tarski(X8,X9)),sK3(X12,X13,k2_tarski(X8,X9)),k2_tarski(X8,X9)) = X8
    | sK3(sK3(X10,X11,k2_tarski(X8,X9)),sK3(X12,X13,k2_tarski(X8,X9)),k2_tarski(X8,X9)) = X9
    | k2_tarski(X8,X9) = k2_tarski(sK3(X10,X11,k2_tarski(X8,X9)),sK3(X12,X13,k2_tarski(X8,X9)))
    | sK3(X10,X11,k2_tarski(X8,X9)) = X11
    | sK3(X10,X11,k2_tarski(X8,X9)) = X10
    | k2_tarski(X10,X11) = k2_tarski(X8,X9)
    | sK3(X12,X13,k2_tarski(X8,X9)) = X13
    | sK3(X12,X13,k2_tarski(X8,X9)) = X12
    | k2_tarski(X8,X9) = k2_tarski(X12,X13) )).

cnf(u3149_002,axiom,
    ( sK3(sK3(X10,X11,k2_tarski(X8,X9)),sK3(X12,X13,k2_tarski(X8,X9)),k2_tarski(X8,X9)) = X8
    | sK3(sK3(X10,X11,k2_tarski(X8,X9)),sK3(X12,X13,k2_tarski(X8,X9)),k2_tarski(X8,X9)) = X9
    | k2_tarski(X8,X9) = k2_tarski(sK3(X10,X11,k2_tarski(X8,X9)),sK3(X12,X13,k2_tarski(X8,X9)))
    | sK3(X10,X11,k2_tarski(X8,X9)) = X11
    | sK3(X10,X11,k2_tarski(X8,X9)) = X10
    | k2_tarski(X10,X11) = k2_tarski(X8,X9)
    | sK3(X12,X13,k2_tarski(X8,X9)) = X13
    | sK3(X12,X13,k2_tarski(X8,X9)) = X12
    | k2_tarski(X8,X9) = k2_tarski(X12,X13) )).

cnf(u1735,axiom,
    ( sK3(sK3(X6,X7,k2_tarski(X4,X5)),sK3(X6,X7,k2_tarski(X4,X5)),k2_tarski(X4,X5)) = X4
    | sK3(sK3(X6,X7,k2_tarski(X4,X5)),sK3(X6,X7,k2_tarski(X4,X5)),k2_tarski(X4,X5)) = X5
    | k2_tarski(X4,X5) = k2_tarski(sK3(X6,X7,k2_tarski(X4,X5)),sK3(X6,X7,k2_tarski(X4,X5)))
    | sK3(X6,X7,k2_tarski(X4,X5)) = X7
    | sK3(X6,X7,k2_tarski(X4,X5)) = X6
    | k2_tarski(X6,X7) = k2_tarski(X4,X5) )).

cnf(u1735_003,axiom,
    ( sK3(sK3(X6,X7,k2_tarski(X4,X5)),sK3(X6,X7,k2_tarski(X4,X5)),k2_tarski(X4,X5)) = X4
    | sK3(sK3(X6,X7,k2_tarski(X4,X5)),sK3(X6,X7,k2_tarski(X4,X5)),k2_tarski(X4,X5)) = X5
    | k2_tarski(X4,X5) = k2_tarski(sK3(X6,X7,k2_tarski(X4,X5)),sK3(X6,X7,k2_tarski(X4,X5)))
    | sK3(X6,X7,k2_tarski(X4,X5)) = X7
    | sK3(X6,X7,k2_tarski(X4,X5)) = X6
    | k2_tarski(X6,X7) = k2_tarski(X4,X5) )).

cnf(u269,axiom,
    ( sK3(sK3(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X10
    | sK3(sK3(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X6
    | sK3(sK3(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X7
    | k2_tarski(X6,X7) = k2_tarski(sK3(X8,X9,k2_tarski(X6,X7)),X10)
    | sK3(X8,X9,k2_tarski(X6,X7)) = X9
    | sK3(X8,X9,k2_tarski(X6,X7)) = X8
    | k2_tarski(X6,X7) = k2_tarski(X8,X9) )).

cnf(u269_004,axiom,
    ( sK3(sK3(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X10
    | sK3(sK3(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X6
    | sK3(sK3(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X7
    | k2_tarski(X6,X7) = k2_tarski(sK3(X8,X9,k2_tarski(X6,X7)),X10)
    | sK3(X8,X9,k2_tarski(X6,X7)) = X9
    | sK3(X8,X9,k2_tarski(X6,X7)) = X8
    | k2_tarski(X6,X7) = k2_tarski(X8,X9) )).

cnf(u269_005,axiom,
    ( sK3(sK3(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X10
    | sK3(sK3(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X6
    | sK3(sK3(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X7
    | k2_tarski(X6,X7) = k2_tarski(sK3(X8,X9,k2_tarski(X6,X7)),X10)
    | sK3(X8,X9,k2_tarski(X6,X7)) = X9
    | sK3(X8,X9,k2_tarski(X6,X7)) = X8
    | k2_tarski(X6,X7) = k2_tarski(X8,X9) )).

cnf(u2575,axiom,
    ( sK3(sK3(X2,X3,k2_tarski(X1,X0)),X0,k2_tarski(X1,X0)) = X1
    | k2_tarski(X1,X0) = k2_tarski(X0,sK3(X2,X3,k2_tarski(X1,X0)))
    | sK3(X2,X3,k2_tarski(X1,X0)) = X3
    | sK3(X2,X3,k2_tarski(X1,X0)) = X2
    | k2_tarski(X1,X0) = k2_tarski(X2,X3) )).

cnf(u1896,axiom,
    ( sK3(sK3(X6,X7,k2_tarski(X4,X5)),X4,k2_tarski(X4,X5)) = X5
    | k2_tarski(X4,X5) = k2_tarski(X4,sK3(X6,X7,k2_tarski(X4,X5)))
    | sK3(X6,X7,k2_tarski(X4,X5)) = X7
    | sK3(X6,X7,k2_tarski(X4,X5)) = X6
    | k2_tarski(X6,X7) = k2_tarski(X4,X5) )).

cnf(u2187,axiom,
    ( sK3(X4,sK3(X5,X6,k2_tarski(X4,X7)),k2_tarski(X4,X7)) = X7
    | k2_tarski(X4,X7) = k2_tarski(X4,sK3(X5,X6,k2_tarski(X4,X7)))
    | sK3(X5,X6,k2_tarski(X4,X7)) = X6
    | sK3(X5,X6,k2_tarski(X4,X7)) = X5
    | k2_tarski(X5,X6) = k2_tarski(X4,X7) )).

cnf(u2184,axiom,
    ( sK3(X4,sK3(X5,X6,k2_tarski(X7,X7)),k2_tarski(X7,X7)) = X4
    | sK3(X4,sK3(X5,X6,k2_tarski(X7,X7)),k2_tarski(X7,X7)) = X7
    | k2_tarski(X7,X7) = k2_tarski(X4,sK3(X5,X6,k2_tarski(X7,X7)))
    | sK3(X5,X6,k2_tarski(X7,X7)) = X6
    | sK3(X5,X6,k2_tarski(X7,X7)) = X5
    | k2_tarski(X7,X7) = k2_tarski(X5,X6) )).

cnf(u2184_006,axiom,
    ( sK3(X4,sK3(X5,X6,k2_tarski(X7,X7)),k2_tarski(X7,X7)) = X4
    | sK3(X4,sK3(X5,X6,k2_tarski(X7,X7)),k2_tarski(X7,X7)) = X7
    | k2_tarski(X7,X7) = k2_tarski(X4,sK3(X5,X6,k2_tarski(X7,X7)))
    | sK3(X5,X6,k2_tarski(X7,X7)) = X6
    | sK3(X5,X6,k2_tarski(X7,X7)) = X5
    | k2_tarski(X7,X7) = k2_tarski(X5,X6) )).

cnf(u2691,axiom,
    ( sK3(X0,sK3(X2,X3,k2_tarski(X1,X0)),k2_tarski(X1,X0)) = X1
    | k2_tarski(X1,X0) = k2_tarski(X0,sK3(X2,X3,k2_tarski(X1,X0)))
    | sK3(X2,X3,k2_tarski(X1,X0)) = X3
    | sK3(X2,X3,k2_tarski(X1,X0)) = X2
    | k2_tarski(X1,X0) = k2_tarski(X2,X3) )).

cnf(u291,axiom,
    ( sK3(X8,sK3(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X8
    | sK3(X8,sK3(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X6
    | sK3(X8,sK3(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X7
    | k2_tarski(X6,X7) = k2_tarski(X8,sK3(X9,X10,k2_tarski(X6,X7)))
    | sK3(X9,X10,k2_tarski(X6,X7)) = X10
    | sK3(X9,X10,k2_tarski(X6,X7)) = X9
    | k2_tarski(X6,X7) = k2_tarski(X9,X10) )).

cnf(u291_007,axiom,
    ( sK3(X8,sK3(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X8
    | sK3(X8,sK3(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X6
    | sK3(X8,sK3(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X7
    | k2_tarski(X6,X7) = k2_tarski(X8,sK3(X9,X10,k2_tarski(X6,X7)))
    | sK3(X9,X10,k2_tarski(X6,X7)) = X10
    | sK3(X9,X10,k2_tarski(X6,X7)) = X9
    | k2_tarski(X6,X7) = k2_tarski(X9,X10) )).

cnf(u291_008,axiom,
    ( sK3(X8,sK3(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X8
    | sK3(X8,sK3(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X6
    | sK3(X8,sK3(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X7
    | k2_tarski(X6,X7) = k2_tarski(X8,sK3(X9,X10,k2_tarski(X6,X7)))
    | sK3(X9,X10,k2_tarski(X6,X7)) = X10
    | sK3(X9,X10,k2_tarski(X6,X7)) = X9
    | k2_tarski(X6,X7) = k2_tarski(X9,X10) )).

cnf(u165,axiom,
    ( sK3(X0,X0,k2_tarski(X0,X1)) = X0
    | sK3(X0,X0,k2_tarski(X0,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X0,X0) )).

cnf(u203,axiom,
    ( sK3(X1,X1,k2_tarski(X1,X2)) = X2
    | k2_tarski(X1,X1) = k2_tarski(X1,X2) )).

cnf(u165_009,axiom,
    ( sK3(X0,X0,k2_tarski(X0,X1)) = X0
    | sK3(X0,X0,k2_tarski(X0,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X0,X0) )).

cnf(u294,axiom,
    ( sK3(X0,X0,k2_tarski(X1,X1)) = X0
    | sK3(X0,X0,k2_tarski(X1,X1)) = X1
    | k2_tarski(X0,X0) = k2_tarski(X1,X1) )).

cnf(u294_010,axiom,
    ( sK3(X0,X0,k2_tarski(X1,X1)) = X0
    | sK3(X0,X0,k2_tarski(X1,X1)) = X1
    | k2_tarski(X0,X0) = k2_tarski(X1,X1) )).

cnf(u229,axiom,
    ( sK3(X0,X0,k2_tarski(X1,X0)) = X1
    | sK3(X0,X0,k2_tarski(X1,X0)) = X0
    | k2_tarski(X0,X0) = k2_tarski(X1,X0) )).

cnf(u229_011,axiom,
    ( sK3(X0,X0,k2_tarski(X1,X0)) = X1
    | sK3(X0,X0,k2_tarski(X1,X0)) = X0
    | k2_tarski(X0,X0) = k2_tarski(X1,X0) )).

cnf(u265,axiom,
    ( sK3(X0,X0,k2_tarski(X1,X0)) = X1
    | k2_tarski(X0,X0) = k2_tarski(X1,X0) )).

cnf(u116,axiom,
    ( sK3(X0,X0,k2_tarski(X1,X2)) = X0
    | sK3(X0,X0,k2_tarski(X1,X2)) = X1
    | sK3(X0,X0,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X0) = k2_tarski(X1,X2) )).

cnf(u116_012,axiom,
    ( sK3(X0,X0,k2_tarski(X1,X2)) = X0
    | sK3(X0,X0,k2_tarski(X1,X2)) = X1
    | sK3(X0,X0,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X0) = k2_tarski(X1,X2) )).

cnf(u116_013,axiom,
    ( sK3(X0,X0,k2_tarski(X1,X2)) = X0
    | sK3(X0,X0,k2_tarski(X1,X2)) = X1
    | sK3(X0,X0,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X0) = k2_tarski(X1,X2) )).

cnf(u1605,axiom,
    ( sK3(X0,X1,k2_tarski(X0,X0)) = X1
    | sK3(X0,X1,k2_tarski(X0,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X0,X0) )).

cnf(u1605_014,axiom,
    ( sK3(X0,X1,k2_tarski(X0,X0)) = X1
    | sK3(X0,X1,k2_tarski(X0,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X0,X0) )).

cnf(u1673,axiom,
    ( sK3(X0,X1,k2_tarski(X0,X0)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X0,X0) )).

cnf(u201,axiom,
    ( sK3(X0,X1,k2_tarski(X0,X2)) = X1
    | sK3(X0,X1,k2_tarski(X0,X2)) = X0
    | sK3(X0,X1,k2_tarski(X0,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u1904,axiom,
    ( sK3(X2,X4,k2_tarski(X2,X3)) = X4
    | sK3(X2,X4,k2_tarski(X2,X3)) = X3
    | k2_tarski(X2,X3) = k2_tarski(X2,X4) )).

cnf(u201_015,axiom,
    ( sK3(X0,X1,k2_tarski(X0,X2)) = X1
    | sK3(X0,X1,k2_tarski(X0,X2)) = X0
    | sK3(X0,X1,k2_tarski(X0,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u201_016,axiom,
    ( sK3(X0,X1,k2_tarski(X0,X2)) = X1
    | sK3(X0,X1,k2_tarski(X0,X2)) = X0
    | sK3(X0,X1,k2_tarski(X0,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u1904_017,axiom,
    ( sK3(X2,X4,k2_tarski(X2,X3)) = X4
    | sK3(X2,X4,k2_tarski(X2,X3)) = X3
    | k2_tarski(X2,X3) = k2_tarski(X2,X4) )).

cnf(u874,axiom,
    ( sK3(X0,X1,k2_tarski(X1,X1)) = X0
    | sK3(X0,X1,k2_tarski(X1,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X1,X1) )).

cnf(u874_018,axiom,
    ( sK3(X0,X1,k2_tarski(X1,X1)) = X0
    | sK3(X0,X1,k2_tarski(X1,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X1,X1) )).

cnf(u1546,axiom,
    ( sK3(X1,X0,k2_tarski(X0,X0)) = X1
    | k2_tarski(X0,X0) = k2_tarski(X1,X0) )).

cnf(u642,axiom,
    ( sK3(X0,X1,k2_tarski(X1,X0)) = X1
    | sK3(X0,X1,k2_tarski(X1,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

cnf(u642_019,axiom,
    ( sK3(X0,X1,k2_tarski(X1,X0)) = X1
    | sK3(X0,X1,k2_tarski(X1,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

cnf(u775,axiom,
    ( sK3(X1,X0,k2_tarski(X0,X1)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

cnf(u117,axiom,
    ( sK3(X0,X1,k2_tarski(X1,X2)) = X0
    | sK3(X0,X1,k2_tarski(X1,X2)) = X1
    | sK3(X0,X1,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u1739,axiom,
    ( sK3(X4,X2,k2_tarski(X2,X3)) = X4
    | sK3(X4,X2,k2_tarski(X2,X3)) = X3
    | k2_tarski(X2,X3) = k2_tarski(X4,X2) )).

cnf(u117_020,axiom,
    ( sK3(X0,X1,k2_tarski(X1,X2)) = X0
    | sK3(X0,X1,k2_tarski(X1,X2)) = X1
    | sK3(X0,X1,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u117_021,axiom,
    ( sK3(X0,X1,k2_tarski(X1,X2)) = X0
    | sK3(X0,X1,k2_tarski(X1,X2)) = X1
    | sK3(X0,X1,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u1739_022,axiom,
    ( sK3(X4,X2,k2_tarski(X2,X3)) = X4
    | sK3(X4,X2,k2_tarski(X2,X3)) = X3
    | k2_tarski(X2,X3) = k2_tarski(X4,X2) )).

cnf(u65,axiom,
    ( sK3(X0,X1,k2_tarski(X2,X3)) = X1
    | sK3(X0,X1,k2_tarski(X2,X3)) = X0
    | sK3(X0,X1,k2_tarski(X2,X3)) = X2
    | sK3(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u65_023,axiom,
    ( sK3(X0,X1,k2_tarski(X2,X3)) = X1
    | sK3(X0,X1,k2_tarski(X2,X3)) = X0
    | sK3(X0,X1,k2_tarski(X2,X3)) = X2
    | sK3(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u65_024,axiom,
    ( sK3(X0,X1,k2_tarski(X2,X3)) = X1
    | sK3(X0,X1,k2_tarski(X2,X3)) = X0
    | sK3(X0,X1,k2_tarski(X2,X3)) = X2
    | sK3(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u65_025,axiom,
    ( sK3(X0,X1,k2_tarski(X2,X3)) = X1
    | sK3(X0,X1,k2_tarski(X2,X3)) = X0
    | sK3(X0,X1,k2_tarski(X2,X3)) = X2
    | sK3(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u227,axiom,
    ( sK3(X0,X1,k2_tarski(X2,X2)) = X1
    | sK3(X0,X1,k2_tarski(X2,X2)) = X0
    | sK3(X0,X1,k2_tarski(X2,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u227_026,axiom,
    ( sK3(X0,X1,k2_tarski(X2,X2)) = X1
    | sK3(X0,X1,k2_tarski(X2,X2)) = X0
    | sK3(X0,X1,k2_tarski(X2,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u227_027,axiom,
    ( sK3(X0,X1,k2_tarski(X2,X2)) = X1
    | sK3(X0,X1,k2_tarski(X2,X2)) = X0
    | sK3(X0,X1,k2_tarski(X2,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u166,axiom,
    ( sK3(X0,X1,k2_tarski(X2,X1)) = X0
    | sK3(X0,X1,k2_tarski(X2,X1)) = X2
    | sK3(X0,X1,k2_tarski(X2,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u166_028,axiom,
    ( sK3(X0,X1,k2_tarski(X2,X1)) = X0
    | sK3(X0,X1,k2_tarski(X2,X1)) = X2
    | sK3(X0,X1,k2_tarski(X2,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u1880,axiom,
    ( sK3(X2,X1,k2_tarski(X0,X1)) = X2
    | sK3(X2,X1,k2_tarski(X0,X1)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u166_029,axiom,
    ( sK3(X0,X1,k2_tarski(X2,X1)) = X0
    | sK3(X0,X1,k2_tarski(X2,X1)) = X2
    | sK3(X0,X1,k2_tarski(X2,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u1880_030,axiom,
    ( sK3(X2,X1,k2_tarski(X0,X1)) = X2
    | sK3(X2,X1,k2_tarski(X0,X1)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u204,axiom,
    ( sK3(X0,X1,k2_tarski(X2,X0)) = X1
    | sK3(X0,X1,k2_tarski(X2,X0)) = X2
    | sK3(X0,X1,k2_tarski(X2,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u204_031,axiom,
    ( sK3(X0,X1,k2_tarski(X2,X0)) = X1
    | sK3(X0,X1,k2_tarski(X2,X0)) = X2
    | sK3(X0,X1,k2_tarski(X2,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u2036,axiom,
    ( sK3(X0,X1,k2_tarski(X2,X0)) = X1
    | sK3(X0,X1,k2_tarski(X2,X0)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u204_032,axiom,
    ( sK3(X0,X1,k2_tarski(X2,X0)) = X1
    | sK3(X0,X1,k2_tarski(X2,X0)) = X2
    | sK3(X0,X1,k2_tarski(X2,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u2036_033,axiom,
    ( sK3(X0,X1,k2_tarski(X2,X0)) = X1
    | sK3(X0,X1,k2_tarski(X2,X0)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u1721,axiom,
    ( k2_tarski(X2,X2) = k2_tarski(X2,sK3(X3,X4,k2_tarski(X2,X2)))
    | sK3(X3,X4,k2_tarski(X2,X2)) = X4
    | sK3(X3,X4,k2_tarski(X2,X2)) = X3
    | k2_tarski(X2,X2) = k2_tarski(X3,X4) )).

cnf(u1594,axiom,
    ( k2_tarski(X2,X2) = k2_tarski(sK3(X3,X4,k2_tarski(X2,X2)),X2)
    | sK3(X3,X4,k2_tarski(X2,X2)) = X4
    | sK3(X3,X4,k2_tarski(X2,X2)) = X3
    | k2_tarski(X2,X2) = k2_tarski(X3,X4) )).

cnf(u798,axiom,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) )).

cnf(u66,negated_conjecture,
    ( k2_tarski(sK2,sK2) = k6_domain_1(u1_struct_0(sK0),sK2) )).

cnf(u63,negated_conjecture,
    ( k2_tarski(sK1,sK1) = k6_domain_1(u1_struct_0(sK0),sK1) )).

cnf(u4615,axiom,
    ( X2 != X3
    | sK3(sK3(X0,X1,k2_tarski(X2,X3)),sK3(X4,X5,k2_tarski(X2,X3)),k2_tarski(X2,X3)) = X2
    | k2_tarski(X2,X3) = k2_tarski(sK3(X0,X1,k2_tarski(X2,X3)),sK3(X4,X5,k2_tarski(X2,X3)))
    | sK3(X0,X1,k2_tarski(X2,X3)) = X1
    | sK3(X0,X1,k2_tarski(X2,X3)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X3)
    | sK3(X4,X5,k2_tarski(X2,X3)) = X5
    | sK3(X4,X5,k2_tarski(X2,X3)) = X4
    | k2_tarski(X2,X3) = k2_tarski(X4,X5) )).

cnf(u4614,axiom,
    ( X2 != X3
    | sK3(sK3(X0,X1,k2_tarski(X2,X3)),sK3(X4,X5,k2_tarski(X2,X3)),k2_tarski(X2,X3)) = X3
    | k2_tarski(X2,X3) = k2_tarski(sK3(X0,X1,k2_tarski(X2,X3)),sK3(X4,X5,k2_tarski(X2,X3)))
    | sK3(X0,X1,k2_tarski(X2,X3)) = X1
    | sK3(X0,X1,k2_tarski(X2,X3)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X3)
    | sK3(X4,X5,k2_tarski(X2,X3)) = X5
    | sK3(X4,X5,k2_tarski(X2,X3)) = X4
    | k2_tarski(X2,X3) = k2_tarski(X4,X5) )).

cnf(u4142,axiom,
    ( X2 != X3
    | sK3(sK3(X0,X1,k2_tarski(X2,X3)),sK3(X0,X1,k2_tarski(X2,X3)),k2_tarski(X2,X3)) = X2
    | k2_tarski(X2,X3) = k2_tarski(sK3(X0,X1,k2_tarski(X2,X3)),sK3(X0,X1,k2_tarski(X2,X3)))
    | sK3(X0,X1,k2_tarski(X2,X3)) = X1
    | sK3(X0,X1,k2_tarski(X2,X3)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u4141,axiom,
    ( X2 != X3
    | sK3(sK3(X0,X1,k2_tarski(X2,X3)),sK3(X0,X1,k2_tarski(X2,X3)),k2_tarski(X2,X3)) = X3
    | k2_tarski(X2,X3) = k2_tarski(sK3(X0,X1,k2_tarski(X2,X3)),sK3(X0,X1,k2_tarski(X2,X3)))
    | sK3(X0,X1,k2_tarski(X2,X3)) = X1
    | sK3(X0,X1,k2_tarski(X2,X3)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u3665,axiom,
    ( X0 != X3
    | sK3(X0,sK3(X1,X2,k2_tarski(X3,X3)),k2_tarski(X3,X3)) = X0
    | k2_tarski(X3,X3) = k2_tarski(X0,sK3(X1,X2,k2_tarski(X3,X3)))
    | sK3(X1,X2,k2_tarski(X3,X3)) = X2
    | sK3(X1,X2,k2_tarski(X3,X3)) = X1
    | k2_tarski(X1,X2) = k2_tarski(X3,X3) )).

cnf(u3664,axiom,
    ( X0 != X3
    | sK3(X0,sK3(X1,X2,k2_tarski(X3,X3)),k2_tarski(X3,X3)) = X3
    | k2_tarski(X3,X3) = k2_tarski(X0,sK3(X1,X2,k2_tarski(X3,X3)))
    | sK3(X1,X2,k2_tarski(X3,X3)) = X2
    | sK3(X1,X2,k2_tarski(X3,X3)) = X1
    | k2_tarski(X1,X2) = k2_tarski(X3,X3) )).

cnf(u3384,axiom,
    ( X2 != X3
    | sK3(sK3(X0,X1,k2_tarski(X2,X2)),X3,k2_tarski(X2,X2)) = X3
    | k2_tarski(X2,X2) = k2_tarski(sK3(X0,X1,k2_tarski(X2,X2)),X3)
    | sK3(X0,X1,k2_tarski(X2,X2)) = X1
    | sK3(X0,X1,k2_tarski(X2,X2)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u3383,axiom,
    ( X2 != X3
    | sK3(sK3(X0,X1,k2_tarski(X2,X2)),X3,k2_tarski(X2,X2)) = X2
    | k2_tarski(X2,X2) = k2_tarski(sK3(X0,X1,k2_tarski(X2,X2)),X3)
    | sK3(X0,X1,k2_tarski(X2,X2)) = X1
    | sK3(X0,X1,k2_tarski(X2,X2)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u2884,axiom,
    ( X138 != X139
    | k2_tarski(X138,X139) = k2_tarski(X139,sK3(X136,X137,k2_tarski(X138,X139)))
    | ~ r2_hidden(X139,k2_tarski(X138,X139))
    | sK3(X136,X137,k2_tarski(X138,X139)) = X137
    | sK3(X136,X137,k2_tarski(X138,X139)) = X136
    | k2_tarski(X138,X139) = k2_tarski(X136,X137) )).

cnf(u2630,axiom,
    ( X127 != X128
    | k2_tarski(X127,X128) = k2_tarski(X127,sK3(X125,X126,k2_tarski(X127,X128)))
    | ~ r2_hidden(X127,k2_tarski(X127,X128))
    | sK3(X125,X126,k2_tarski(X127,X128)) = X126
    | sK3(X125,X126,k2_tarski(X127,X128)) = X125
    | k2_tarski(X125,X126) = k2_tarski(X127,X128) )).

cnf(u2331,axiom,
    ( X99 != X100
    | k2_tarski(X99,X100) = k2_tarski(X101,X99)
    | ~ r2_hidden(X99,k2_tarski(X101,X99))
    | sK3(X99,X100,k2_tarski(X101,X99)) = X101 )).

cnf(u2316,axiom,
    ( X99 != X101
    | k2_tarski(X99,X100) = k2_tarski(X101,X99)
    | ~ r2_hidden(X99,k2_tarski(X101,X99))
    | sK3(X99,X100,k2_tarski(X101,X99)) = X100 )).

cnf(u2314,axiom,
    ( X1 != X2
    | sK3(X0,X1,k2_tarski(X2,X0)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u2313,axiom,
    ( X1 != X2
    | sK3(X0,X1,k2_tarski(X2,X0)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u2174,axiom,
    ( X92 != X93
    | k2_tarski(X92,X93) = k2_tarski(X92,X94)
    | ~ r2_hidden(X92,k2_tarski(X92,X94))
    | sK3(X92,X93,k2_tarski(X92,X94)) = X94 )).

cnf(u2159,axiom,
    ( X92 != X94
    | k2_tarski(X92,X93) = k2_tarski(X92,X94)
    | ~ r2_hidden(X92,k2_tarski(X92,X94))
    | sK3(X92,X93,k2_tarski(X92,X94)) = X93 )).

cnf(u2157,axiom,
    ( X1 != X2
    | sK3(X0,X1,k2_tarski(X0,X2)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u2156,axiom,
    ( X1 != X2
    | sK3(X0,X1,k2_tarski(X0,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u2030,axiom,
    ( X91 != X92
    | k2_tarski(X93,X92) = k2_tarski(X91,X92)
    | ~ r2_hidden(X92,k2_tarski(X93,X92))
    | sK3(X91,X92,k2_tarski(X93,X92)) = X93 )).

cnf(u2016,axiom,
    ( X92 != X93
    | k2_tarski(X93,X92) = k2_tarski(X91,X92)
    | ~ r2_hidden(X92,k2_tarski(X93,X92))
    | sK3(X91,X92,k2_tarski(X93,X92)) = X91 )).

cnf(u2015,axiom,
    ( X0 != X2
    | sK3(X0,X1,k2_tarski(X2,X1)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u2014,axiom,
    ( X0 != X2
    | sK3(X0,X1,k2_tarski(X2,X1)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u1870,axiom,
    ( X90 != X91
    | k2_tarski(X90,X91) = k2_tarski(X91,X92)
    | ~ r2_hidden(X91,k2_tarski(X91,X92))
    | sK3(X90,X91,k2_tarski(X91,X92)) = X92 )).

cnf(u1856,axiom,
    ( X91 != X92
    | k2_tarski(X90,X91) = k2_tarski(X91,X92)
    | ~ r2_hidden(X91,k2_tarski(X91,X92))
    | sK3(X90,X91,k2_tarski(X91,X92)) = X90 )).

cnf(u1855,axiom,
    ( X0 != X2
    | sK3(X0,X1,k2_tarski(X1,X2)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u1854,axiom,
    ( X0 != X2
    | sK3(X0,X1,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u1716,axiom,
    ( X62 != X63
    | k2_tarski(X62,X62) = k2_tarski(X62,X63)
    | ~ r2_hidden(X62,k2_tarski(X62,X62)) )).

cnf(u1659,axiom,
    ( X0 != X1
    | sK3(X0,X1,k2_tarski(X0,X0)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X0,X0) )).

cnf(u1658,axiom,
    ( X0 != X1
    | sK3(X0,X1,k2_tarski(X0,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X0,X0) )).

cnf(u1587,axiom,
    ( X61 != X62
    | k2_tarski(X62,X62) = k2_tarski(X61,X62)
    | ~ r2_hidden(X62,k2_tarski(X62,X62)) )).

cnf(u1455,axiom,
    ( X3 != X4
    | sK3(X0,sK3(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X0
    | sK3(X0,sK3(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X3
    | k2_tarski(X3,X4) = k2_tarski(X0,sK3(X1,X2,k2_tarski(X3,X4)))
    | sK3(X1,X2,k2_tarski(X3,X4)) = X2
    | sK3(X1,X2,k2_tarski(X3,X4)) = X1
    | k2_tarski(X1,X2) = k2_tarski(X3,X4) )).

cnf(u1454,axiom,
    ( X0 != X4
    | sK3(X0,sK3(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X0
    | sK3(X0,sK3(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X3
    | k2_tarski(X3,X4) = k2_tarski(X0,sK3(X1,X2,k2_tarski(X3,X4)))
    | sK3(X1,X2,k2_tarski(X3,X4)) = X2
    | sK3(X1,X2,k2_tarski(X3,X4)) = X1
    | k2_tarski(X1,X2) = k2_tarski(X3,X4) )).

cnf(u1453,axiom,
    ( X3 != X4
    | sK3(X0,sK3(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X0
    | sK3(X0,sK3(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X4
    | k2_tarski(X3,X4) = k2_tarski(X0,sK3(X1,X2,k2_tarski(X3,X4)))
    | sK3(X1,X2,k2_tarski(X3,X4)) = X2
    | sK3(X1,X2,k2_tarski(X3,X4)) = X1
    | k2_tarski(X1,X2) = k2_tarski(X3,X4) )).

cnf(u1452,axiom,
    ( X0 != X3
    | sK3(X0,sK3(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X0
    | sK3(X0,sK3(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X4
    | k2_tarski(X3,X4) = k2_tarski(X0,sK3(X1,X2,k2_tarski(X3,X4)))
    | sK3(X1,X2,k2_tarski(X3,X4)) = X2
    | sK3(X1,X2,k2_tarski(X3,X4)) = X1
    | k2_tarski(X1,X2) = k2_tarski(X3,X4) )).

cnf(u1451,axiom,
    ( X0 != X4
    | sK3(X0,sK3(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X3
    | sK3(X0,sK3(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X4
    | k2_tarski(X3,X4) = k2_tarski(X0,sK3(X1,X2,k2_tarski(X3,X4)))
    | sK3(X1,X2,k2_tarski(X3,X4)) = X2
    | sK3(X1,X2,k2_tarski(X3,X4)) = X1
    | k2_tarski(X1,X2) = k2_tarski(X3,X4) )).

cnf(u1450,axiom,
    ( X0 != X3
    | sK3(X0,sK3(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X3
    | sK3(X0,sK3(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X4
    | k2_tarski(X3,X4) = k2_tarski(X0,sK3(X1,X2,k2_tarski(X3,X4)))
    | sK3(X1,X2,k2_tarski(X3,X4)) = X2
    | sK3(X1,X2,k2_tarski(X3,X4)) = X1
    | k2_tarski(X1,X2) = k2_tarski(X3,X4) )).

cnf(u1135,axiom,
    ( X2 != X3
    | sK3(sK3(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X4
    | sK3(sK3(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X2
    | k2_tarski(X2,X3) = k2_tarski(sK3(X0,X1,k2_tarski(X2,X3)),X4)
    | sK3(X0,X1,k2_tarski(X2,X3)) = X1
    | sK3(X0,X1,k2_tarski(X2,X3)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u1134,axiom,
    ( X3 != X4
    | sK3(sK3(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X4
    | sK3(sK3(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X2
    | k2_tarski(X2,X3) = k2_tarski(sK3(X0,X1,k2_tarski(X2,X3)),X4)
    | sK3(X0,X1,k2_tarski(X2,X3)) = X1
    | sK3(X0,X1,k2_tarski(X2,X3)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u1133,axiom,
    ( X2 != X3
    | sK3(sK3(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X4
    | sK3(sK3(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X3
    | k2_tarski(X2,X3) = k2_tarski(sK3(X0,X1,k2_tarski(X2,X3)),X4)
    | sK3(X0,X1,k2_tarski(X2,X3)) = X1
    | sK3(X0,X1,k2_tarski(X2,X3)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u1132,axiom,
    ( X2 != X4
    | sK3(sK3(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X4
    | sK3(sK3(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X3
    | k2_tarski(X2,X3) = k2_tarski(sK3(X0,X1,k2_tarski(X2,X3)),X4)
    | sK3(X0,X1,k2_tarski(X2,X3)) = X1
    | sK3(X0,X1,k2_tarski(X2,X3)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u1131,axiom,
    ( X3 != X4
    | sK3(sK3(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X2
    | sK3(sK3(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X3
    | k2_tarski(X2,X3) = k2_tarski(sK3(X0,X1,k2_tarski(X2,X3)),X4)
    | sK3(X0,X1,k2_tarski(X2,X3)) = X1
    | sK3(X0,X1,k2_tarski(X2,X3)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u1130,axiom,
    ( X2 != X4
    | sK3(sK3(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X2
    | sK3(sK3(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X3
    | k2_tarski(X2,X3) = k2_tarski(sK3(X0,X1,k2_tarski(X2,X3)),X4)
    | sK3(X0,X1,k2_tarski(X2,X3)) = X1
    | sK3(X0,X1,k2_tarski(X2,X3)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u910,axiom,
    ( X0 != X1
    | sK3(X0,X1,k2_tarski(X1,X1)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X1,X1) )).

cnf(u909,axiom,
    ( X0 != X1
    | sK3(X0,X1,k2_tarski(X1,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X1,X1) )).

cnf(u764,axiom,
    ( X0 != X2
    | sK3(X0,X1,k2_tarski(X2,X2)) = X1
    | sK3(X0,X1,k2_tarski(X2,X2)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u763,axiom,
    ( X1 != X2
    | sK3(X0,X1,k2_tarski(X2,X2)) = X1
    | sK3(X0,X1,k2_tarski(X2,X2)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u762,axiom,
    ( X0 != X2
    | sK3(X0,X1,k2_tarski(X2,X2)) = X1
    | sK3(X0,X1,k2_tarski(X2,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u761,axiom,
    ( X0 != X1
    | sK3(X0,X1,k2_tarski(X2,X2)) = X1
    | sK3(X0,X1,k2_tarski(X2,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u760,axiom,
    ( X1 != X2
    | sK3(X0,X1,k2_tarski(X2,X2)) = X0
    | sK3(X0,X1,k2_tarski(X2,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u759,axiom,
    ( X0 != X1
    | sK3(X0,X1,k2_tarski(X2,X2)) = X0
    | sK3(X0,X1,k2_tarski(X2,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u672,axiom,
    ( X0 != X1
    | sK3(X0,X1,k2_tarski(X1,X0)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

cnf(u671,axiom,
    ( X0 != X1
    | sK3(X0,X1,k2_tarski(X1,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

cnf(u630,axiom,
    ( X0 != X2
    | sK3(X0,X1,k2_tarski(X2,X0)) = X1
    | sK3(X0,X1,k2_tarski(X2,X0)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u629,axiom,
    ( X0 != X1
    | sK3(X0,X1,k2_tarski(X2,X0)) = X1
    | sK3(X0,X1,k2_tarski(X2,X0)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u628,axiom,
    ( X0 != X2
    | sK3(X0,X1,k2_tarski(X2,X0)) = X1
    | sK3(X0,X1,k2_tarski(X2,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u627,axiom,
    ( X1 != X2
    | sK3(X0,X1,k2_tarski(X2,X0)) = X1
    | sK3(X0,X1,k2_tarski(X2,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u626,axiom,
    ( X0 != X1
    | sK3(X0,X1,k2_tarski(X2,X0)) = X2
    | sK3(X0,X1,k2_tarski(X2,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u625,axiom,
    ( X1 != X2
    | sK3(X0,X1,k2_tarski(X2,X0)) = X2
    | sK3(X0,X1,k2_tarski(X2,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u539,axiom,
    ( X0 != X2
    | sK3(X0,X1,k2_tarski(X0,X2)) = X1
    | sK3(X0,X1,k2_tarski(X0,X2)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u538,axiom,
    ( X1 != X2
    | sK3(X0,X1,k2_tarski(X0,X2)) = X1
    | sK3(X0,X1,k2_tarski(X0,X2)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u537,axiom,
    ( X0 != X2
    | sK3(X0,X1,k2_tarski(X0,X2)) = X1
    | sK3(X0,X1,k2_tarski(X0,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u536,axiom,
    ( X0 != X1
    | sK3(X0,X1,k2_tarski(X0,X2)) = X1
    | sK3(X0,X1,k2_tarski(X0,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u535,axiom,
    ( X1 != X2
    | sK3(X0,X1,k2_tarski(X0,X2)) = X0
    | sK3(X0,X1,k2_tarski(X0,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u534,axiom,
    ( X0 != X1
    | sK3(X0,X1,k2_tarski(X0,X2)) = X0
    | sK3(X0,X1,k2_tarski(X0,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u457,axiom,
    ( X1 != X2
    | sK3(X0,X1,k2_tarski(X2,X1)) = X0
    | sK3(X0,X1,k2_tarski(X2,X1)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u456,axiom,
    ( X0 != X1
    | sK3(X0,X1,k2_tarski(X2,X1)) = X0
    | sK3(X0,X1,k2_tarski(X2,X1)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u455,axiom,
    ( X1 != X2
    | sK3(X0,X1,k2_tarski(X2,X1)) = X0
    | sK3(X0,X1,k2_tarski(X2,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u454,axiom,
    ( X0 != X2
    | sK3(X0,X1,k2_tarski(X2,X1)) = X0
    | sK3(X0,X1,k2_tarski(X2,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u453,axiom,
    ( X0 != X1
    | sK3(X0,X1,k2_tarski(X2,X1)) = X2
    | sK3(X0,X1,k2_tarski(X2,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u452,axiom,
    ( X0 != X2
    | sK3(X0,X1,k2_tarski(X2,X1)) = X2
    | sK3(X0,X1,k2_tarski(X2,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u385,axiom,
    ( X1 != X2
    | sK3(X0,X1,k2_tarski(X1,X2)) = X0
    | sK3(X0,X1,k2_tarski(X1,X2)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u384,axiom,
    ( X0 != X2
    | sK3(X0,X1,k2_tarski(X1,X2)) = X0
    | sK3(X0,X1,k2_tarski(X1,X2)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u383,axiom,
    ( X1 != X2
    | sK3(X0,X1,k2_tarski(X1,X2)) = X0
    | sK3(X0,X1,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u382,axiom,
    ( X0 != X1
    | sK3(X0,X1,k2_tarski(X1,X2)) = X0
    | sK3(X0,X1,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u381,axiom,
    ( X0 != X2
    | sK3(X0,X1,k2_tarski(X1,X2)) = X1
    | sK3(X0,X1,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u380,axiom,
    ( X0 != X1
    | sK3(X0,X1,k2_tarski(X1,X2)) = X1
    | sK3(X0,X1,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u318,axiom,
    ( X0 != X1
    | sK3(X0,X0,k2_tarski(X1,X1)) = X0
    | k2_tarski(X0,X0) = k2_tarski(X1,X1) )).

cnf(u317,axiom,
    ( X0 != X1
    | sK3(X0,X0,k2_tarski(X1,X1)) = X1
    | k2_tarski(X0,X0) = k2_tarski(X1,X1) )).

cnf(u285,axiom,
    ( X12 != X13
    | k2_tarski(X12,X12) = k2_tarski(X13,X12)
    | ~ r2_hidden(X12,k2_tarski(X13,X12)) )).

cnf(u253,axiom,
    ( X0 != X1
    | sK3(X0,X0,k2_tarski(X1,X0)) = X1
    | k2_tarski(X0,X0) = k2_tarski(X1,X0) )).

cnf(u252,axiom,
    ( X0 != X1
    | sK3(X0,X0,k2_tarski(X1,X0)) = X0
    | k2_tarski(X0,X0) = k2_tarski(X1,X0) )).

cnf(u220,axiom,
    ( X12 != X13
    | k2_tarski(X12,X12) = k2_tarski(X12,X13)
    | ~ r2_hidden(X12,k2_tarski(X12,X13)) )).

cnf(u190,axiom,
    ( X0 != X1
    | sK3(X0,X0,k2_tarski(X0,X1)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X0,X0) )).

cnf(u189,axiom,
    ( X0 != X1
    | sK3(X0,X0,k2_tarski(X0,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X0,X0) )).

cnf(u154,axiom,
    ( X1 != X2
    | sK3(X0,X0,k2_tarski(X1,X2)) = X0
    | sK3(X0,X0,k2_tarski(X1,X2)) = X1
    | k2_tarski(X0,X0) = k2_tarski(X1,X2) )).

cnf(u153,axiom,
    ( X0 != X2
    | sK3(X0,X0,k2_tarski(X1,X2)) = X0
    | sK3(X0,X0,k2_tarski(X1,X2)) = X1
    | k2_tarski(X0,X0) = k2_tarski(X1,X2) )).

cnf(u152,axiom,
    ( X1 != X2
    | sK3(X0,X0,k2_tarski(X1,X2)) = X0
    | sK3(X0,X0,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X0) = k2_tarski(X1,X2) )).

cnf(u151,axiom,
    ( X0 != X1
    | sK3(X0,X0,k2_tarski(X1,X2)) = X0
    | sK3(X0,X0,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X0) = k2_tarski(X1,X2) )).

cnf(u150,axiom,
    ( X0 != X2
    | sK3(X0,X0,k2_tarski(X1,X2)) = X1
    | sK3(X0,X0,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X0) = k2_tarski(X1,X2) )).

cnf(u149,axiom,
    ( X0 != X1
    | sK3(X0,X0,k2_tarski(X1,X2)) = X1
    | sK3(X0,X0,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X0) = k2_tarski(X1,X2) )).

cnf(u102,axiom,
    ( X2 != X3
    | sK3(X0,X1,k2_tarski(X2,X3)) = X1
    | sK3(X0,X1,k2_tarski(X2,X3)) = X0
    | sK3(X0,X1,k2_tarski(X2,X3)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u101,axiom,
    ( X0 != X3
    | sK3(X0,X1,k2_tarski(X2,X3)) = X1
    | sK3(X0,X1,k2_tarski(X2,X3)) = X0
    | sK3(X0,X1,k2_tarski(X2,X3)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u100,axiom,
    ( X1 != X3
    | sK3(X0,X1,k2_tarski(X2,X3)) = X1
    | sK3(X0,X1,k2_tarski(X2,X3)) = X0
    | sK3(X0,X1,k2_tarski(X2,X3)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u99,axiom,
    ( X2 != X3
    | sK3(X0,X1,k2_tarski(X2,X3)) = X1
    | sK3(X0,X1,k2_tarski(X2,X3)) = X0
    | sK3(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u98,axiom,
    ( X0 != X2
    | sK3(X0,X1,k2_tarski(X2,X3)) = X1
    | sK3(X0,X1,k2_tarski(X2,X3)) = X0
    | sK3(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u97,axiom,
    ( X1 != X2
    | sK3(X0,X1,k2_tarski(X2,X3)) = X1
    | sK3(X0,X1,k2_tarski(X2,X3)) = X0
    | sK3(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u96,axiom,
    ( X0 != X3
    | sK3(X0,X1,k2_tarski(X2,X3)) = X1
    | sK3(X0,X1,k2_tarski(X2,X3)) = X2
    | sK3(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u95,axiom,
    ( X0 != X2
    | sK3(X0,X1,k2_tarski(X2,X3)) = X1
    | sK3(X0,X1,k2_tarski(X2,X3)) = X2
    | sK3(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u94,axiom,
    ( X0 != X1
    | sK3(X0,X1,k2_tarski(X2,X3)) = X1
    | sK3(X0,X1,k2_tarski(X2,X3)) = X2
    | sK3(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u93,axiom,
    ( X1 != X3
    | sK3(X0,X1,k2_tarski(X2,X3)) = X0
    | sK3(X0,X1,k2_tarski(X2,X3)) = X2
    | sK3(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u92,axiom,
    ( X1 != X2
    | sK3(X0,X1,k2_tarski(X2,X3)) = X0
    | sK3(X0,X1,k2_tarski(X2,X3)) = X2
    | sK3(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u91,axiom,
    ( X0 != X1
    | sK3(X0,X1,k2_tarski(X2,X3)) = X0
    | sK3(X0,X1,k2_tarski(X2,X3)) = X2
    | sK3(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u3399,axiom,
    ( sK3(X150,X151,k2_tarski(X152,X152)) != X153
    | k2_tarski(X152,X152) = k2_tarski(sK3(X150,X151,k2_tarski(X152,X152)),X153)
    | ~ r2_hidden(sK3(X150,X151,k2_tarski(X152,X152)),k2_tarski(X152,X152))
    | sK3(sK3(X150,X151,k2_tarski(X152,X152)),X153,k2_tarski(X152,X152)) = X152
    | sK3(X150,X151,k2_tarski(X152,X152)) = X151
    | sK3(X150,X151,k2_tarski(X152,X152)) = X150
    | k2_tarski(X150,X151) = k2_tarski(X152,X152) )).

cnf(u3683,axiom,
    ( sK3(X162,X163,k2_tarski(X164,X164)) != X161
    | k2_tarski(X164,X164) = k2_tarski(X161,sK3(X162,X163,k2_tarski(X164,X164)))
    | ~ r2_hidden(sK3(X162,X163,k2_tarski(X164,X164)),k2_tarski(X164,X164))
    | sK3(X161,sK3(X162,X163,k2_tarski(X164,X164)),k2_tarski(X164,X164)) = X164
    | sK3(X162,X163,k2_tarski(X164,X164)) = X163
    | sK3(X162,X163,k2_tarski(X164,X164)) = X162
    | k2_tarski(X162,X163) = k2_tarski(X164,X164) )).

cnf(u1144,axiom,
    ( sK3(X67,X68,k2_tarski(X69,X70)) != X71
    | k2_tarski(X69,X70) = k2_tarski(sK3(X67,X68,k2_tarski(X69,X70)),X71)
    | ~ r2_hidden(sK3(X67,X68,k2_tarski(X69,X70)),k2_tarski(X69,X70))
    | sK3(sK3(X67,X68,k2_tarski(X69,X70)),X71,k2_tarski(X69,X70)) = X69
    | sK3(sK3(X67,X68,k2_tarski(X69,X70)),X71,k2_tarski(X69,X70)) = X70
    | sK3(X67,X68,k2_tarski(X69,X70)) = X68
    | sK3(X67,X68,k2_tarski(X69,X70)) = X67
    | k2_tarski(X67,X68) = k2_tarski(X69,X70) )).

cnf(u1471,axiom,
    ( sK3(X85,X86,k2_tarski(X87,X88)) != X84
    | k2_tarski(X87,X88) = k2_tarski(X84,sK3(X85,X86,k2_tarski(X87,X88)))
    | ~ r2_hidden(sK3(X85,X86,k2_tarski(X87,X88)),k2_tarski(X87,X88))
    | sK3(X84,sK3(X85,X86,k2_tarski(X87,X88)),k2_tarski(X87,X88)) = X87
    | sK3(X84,sK3(X85,X86,k2_tarski(X87,X88)),k2_tarski(X87,X88)) = X88
    | sK3(X85,X86,k2_tarski(X87,X88)) = X86
    | sK3(X85,X86,k2_tarski(X87,X88)) = X85
    | k2_tarski(X85,X86) = k2_tarski(X87,X88) )).

cnf(u53,axiom,
    ( sK3(X0,X1,X2) != X0
    | k2_tarski(X0,X1) = X2
    | ~ r2_hidden(X0,X2) )).

cnf(u52,axiom,
    ( sK3(X0,X1,X2) != X1
    | k2_tarski(X0,X1) = X2
    | ~ r2_hidden(X1,X2) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:38:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (4930)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.51  % (4908)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (4914)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.52  % (4930)Refutation not found, incomplete strategy% (4930)------------------------------
% 0.22/0.52  % (4930)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (4908)Refutation not found, incomplete strategy% (4908)------------------------------
% 0.22/0.52  % (4908)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (4930)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (4930)Memory used [KB]: 6268
% 0.22/0.52  % (4930)Time elapsed: 0.096 s
% 0.22/0.52  % (4930)------------------------------
% 0.22/0.52  % (4930)------------------------------
% 0.22/0.52  % (4908)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (4908)Memory used [KB]: 1791
% 0.22/0.52  % (4908)Time elapsed: 0.102 s
% 0.22/0.52  % (4908)------------------------------
% 0.22/0.52  % (4908)------------------------------
% 0.22/0.52  % (4905)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (4914)Refutation not found, incomplete strategy% (4914)------------------------------
% 0.22/0.52  % (4914)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (4914)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (4914)Memory used [KB]: 10746
% 0.22/0.52  % (4914)Time elapsed: 0.106 s
% 0.22/0.52  % (4914)------------------------------
% 0.22/0.52  % (4914)------------------------------
% 0.22/0.52  % (4922)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.52  % (4905)Refutation not found, incomplete strategy% (4905)------------------------------
% 0.22/0.52  % (4905)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (4905)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (4905)Memory used [KB]: 1663
% 0.22/0.52  % (4905)Time elapsed: 0.109 s
% 0.22/0.52  % (4905)------------------------------
% 0.22/0.52  % (4905)------------------------------
% 0.22/0.52  % (4913)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.52  % (4917)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.53  % (4906)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.53  % (4916)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.53  % (4923)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.53  % (4931)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.53  % (4928)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.53  % (4904)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.53  % (4931)Refutation not found, incomplete strategy% (4931)------------------------------
% 0.22/0.53  % (4931)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (4907)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.53  % (4928)Refutation not found, incomplete strategy% (4928)------------------------------
% 0.22/0.53  % (4928)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (4928)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (4928)Memory used [KB]: 10618
% 0.22/0.53  % (4928)Time elapsed: 0.085 s
% 0.22/0.53  % (4928)------------------------------
% 0.22/0.53  % (4928)------------------------------
% 0.22/0.53  % (4931)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (4931)Memory used [KB]: 6140
% 0.22/0.53  % (4931)Time elapsed: 0.113 s
% 0.22/0.53  % (4931)------------------------------
% 0.22/0.53  % (4931)------------------------------
% 0.22/0.53  % (4915)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.53  % (4919)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.53  % (4916)Refutation not found, incomplete strategy% (4916)------------------------------
% 0.22/0.53  % (4916)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (4915)Refutation not found, incomplete strategy% (4915)------------------------------
% 0.22/0.54  % (4915)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (4915)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (4915)Memory used [KB]: 6268
% 0.22/0.54  % (4915)Time elapsed: 0.124 s
% 0.22/0.54  % (4915)------------------------------
% 0.22/0.54  % (4915)------------------------------
% 0.22/0.54  % (4916)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (4916)Memory used [KB]: 10618
% 0.22/0.54  % (4916)Time elapsed: 0.103 s
% 0.22/0.54  % (4916)------------------------------
% 0.22/0.54  % (4916)------------------------------
% 0.22/0.54  % (4933)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (4909)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.54  % (4933)Refutation not found, incomplete strategy% (4933)------------------------------
% 0.22/0.54  % (4933)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (4933)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (4933)Memory used [KB]: 1663
% 0.22/0.54  % (4933)Time elapsed: 0.002 s
% 0.22/0.54  % (4933)------------------------------
% 0.22/0.54  % (4933)------------------------------
% 0.22/0.54  % (4925)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.54  % (4929)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.54  % (4929)Refutation not found, incomplete strategy% (4929)------------------------------
% 0.22/0.54  % (4929)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (4929)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (4929)Memory used [KB]: 6140
% 0.22/0.54  % (4929)Time elapsed: 0.118 s
% 0.22/0.54  % (4929)------------------------------
% 0.22/0.54  % (4929)------------------------------
% 0.22/0.54  % (4922)Refutation not found, incomplete strategy% (4922)------------------------------
% 0.22/0.54  % (4922)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (4922)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (4922)Memory used [KB]: 1663
% 0.22/0.54  % (4922)Time elapsed: 0.135 s
% 0.22/0.54  % (4922)------------------------------
% 0.22/0.54  % (4922)------------------------------
% 0.22/0.54  % (4932)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.54  % (4932)Refutation not found, incomplete strategy% (4932)------------------------------
% 0.22/0.54  % (4932)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (4912)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.54  % (4932)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (4932)Memory used [KB]: 10618
% 0.22/0.54  % (4932)Time elapsed: 0.095 s
% 0.22/0.54  % (4932)------------------------------
% 0.22/0.54  % (4932)------------------------------
% 0.22/0.54  % (4921)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.54  % (4918)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.54  % (4921)Refutation not found, incomplete strategy% (4921)------------------------------
% 0.22/0.54  % (4921)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (4921)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (4921)Memory used [KB]: 1663
% 0.22/0.54  % (4921)Time elapsed: 0.119 s
% 0.22/0.54  % (4921)------------------------------
% 0.22/0.54  % (4921)------------------------------
% 0.22/0.55  % (4918)Refutation not found, incomplete strategy% (4918)------------------------------
% 0.22/0.55  % (4918)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (4918)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (4918)Memory used [KB]: 1791
% 0.22/0.55  % (4918)Time elapsed: 0.132 s
% 0.22/0.55  % (4918)------------------------------
% 0.22/0.55  % (4918)------------------------------
% 0.22/0.55  % (4910)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (4927)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.55  % (4924)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.55  % (4926)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.55  % (4911)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.56  % (4920)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.56  % (4920)Refutation not found, incomplete strategy% (4920)------------------------------
% 0.22/0.56  % (4920)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (4920)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (4920)Memory used [KB]: 10618
% 0.22/0.56  % (4920)Time elapsed: 0.152 s
% 0.22/0.56  % (4920)------------------------------
% 0.22/0.56  % (4920)------------------------------
% 2.12/0.63  % (4935)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.12/0.63  % (4934)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.12/0.67  % (4942)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.12/0.67  % (4907)Refutation not found, incomplete strategy% (4907)------------------------------
% 2.12/0.67  % (4907)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.67  % (4907)Termination reason: Refutation not found, incomplete strategy
% 2.12/0.67  
% 2.12/0.67  % (4907)Memory used [KB]: 6140
% 2.12/0.67  % (4907)Time elapsed: 0.259 s
% 2.12/0.67  % (4907)------------------------------
% 2.12/0.67  % (4907)------------------------------
% 2.12/0.68  % (4906)Refutation not found, incomplete strategy% (4906)------------------------------
% 2.12/0.68  % (4906)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.68  % (4906)Termination reason: Refutation not found, incomplete strategy
% 2.12/0.68  
% 2.12/0.68  % (4906)Memory used [KB]: 6268
% 2.12/0.68  % (4906)Time elapsed: 0.256 s
% 2.12/0.68  % (4906)------------------------------
% 2.12/0.68  % (4906)------------------------------
% 2.12/0.68  % (4940)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.12/0.68  % (4945)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 2.12/0.68  % (4946)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 2.12/0.68  % (4940)Refutation not found, incomplete strategy% (4940)------------------------------
% 2.12/0.68  % (4940)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.69  % (4939)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.12/0.69  % (4937)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.12/0.69  % (4940)Termination reason: Refutation not found, incomplete strategy
% 2.12/0.69  
% 2.12/0.69  % (4940)Memory used [KB]: 10746
% 2.12/0.69  % (4940)Time elapsed: 0.115 s
% 2.12/0.69  % (4940)------------------------------
% 2.12/0.69  % (4940)------------------------------
% 2.12/0.69  % (4937)Refutation not found, incomplete strategy% (4937)------------------------------
% 2.12/0.69  % (4937)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.69  % (4937)Termination reason: Refutation not found, incomplete strategy
% 2.12/0.69  
% 2.12/0.69  % (4937)Memory used [KB]: 10618
% 2.12/0.69  % (4937)Time elapsed: 0.132 s
% 2.12/0.69  % (4937)------------------------------
% 2.12/0.69  % (4937)------------------------------
% 2.12/0.69  % (4938)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.12/0.69  % (4938)Refutation not found, incomplete strategy% (4938)------------------------------
% 2.12/0.69  % (4938)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.70  % (4938)Termination reason: Refutation not found, incomplete strategy
% 2.12/0.70  
% 2.12/0.70  % (4938)Memory used [KB]: 10746
% 2.12/0.70  % (4938)Time elapsed: 0.120 s
% 2.12/0.70  % (4938)------------------------------
% 2.12/0.70  % (4938)------------------------------
% 2.12/0.70  % (4948)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 2.12/0.70  % (4945)Refutation not found, incomplete strategy% (4945)------------------------------
% 2.12/0.70  % (4945)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.70  % (4945)Termination reason: Refutation not found, incomplete strategy
% 2.12/0.70  
% 2.12/0.70  % (4945)Memory used [KB]: 10746
% 2.12/0.70  % (4945)Time elapsed: 0.129 s
% 2.12/0.70  % (4945)------------------------------
% 2.12/0.70  % (4945)------------------------------
% 2.12/0.70  % (4943)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 2.12/0.71  % (4943)Refutation not found, incomplete strategy% (4943)------------------------------
% 2.12/0.71  % (4943)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.71  % (4943)Termination reason: Refutation not found, incomplete strategy
% 2.12/0.71  
% 2.12/0.71  % (4943)Memory used [KB]: 10746
% 2.12/0.71  % (4943)Time elapsed: 0.063 s
% 2.12/0.71  % (4943)------------------------------
% 2.12/0.71  % (4943)------------------------------
% 2.12/0.71  % (4912)Refutation not found, incomplete strategy% (4912)------------------------------
% 2.12/0.71  % (4912)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.71  % (4919)Refutation not found, incomplete strategy% (4919)------------------------------
% 2.12/0.71  % (4919)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.71  % (4919)Termination reason: Refutation not found, incomplete strategy
% 2.12/0.71  
% 2.12/0.71  % (4919)Memory used [KB]: 6268
% 2.12/0.71  % (4919)Time elapsed: 0.292 s
% 2.12/0.71  % (4919)------------------------------
% 2.12/0.71  % (4919)------------------------------
% 2.12/0.71  % (4912)Termination reason: Refutation not found, incomplete strategy
% 2.12/0.71  
% 2.12/0.71  % (4912)Memory used [KB]: 6268
% 2.12/0.71  % (4912)Time elapsed: 0.295 s
% 2.12/0.71  % (4912)------------------------------
% 2.12/0.71  % (4912)------------------------------
% 2.12/0.71  % (4947)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 2.12/0.71  % (4947)Refutation not found, incomplete strategy% (4947)------------------------------
% 2.12/0.71  % (4947)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.71  % (4947)Termination reason: Refutation not found, incomplete strategy
% 2.12/0.71  
% 2.12/0.71  % (4947)Memory used [KB]: 10746
% 2.12/0.71  % (4947)Time elapsed: 0.131 s
% 2.12/0.71  % (4947)------------------------------
% 2.12/0.71  % (4947)------------------------------
% 2.12/0.72  % (4944)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 2.12/0.72  % (4936)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.94/0.73  % (4941)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.94/0.77  % (4949)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 2.94/0.80  % (4951)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 3.33/0.81  % (4952)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 3.33/0.82  % (4950)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 3.33/0.82  % (4942)Refutation not found, incomplete strategy% (4942)------------------------------
% 3.33/0.82  % (4942)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.33/0.82  % (4942)Termination reason: Refutation not found, incomplete strategy
% 3.33/0.82  
% 3.33/0.82  % (4942)Memory used [KB]: 6268
% 3.33/0.82  % (4942)Time elapsed: 0.240 s
% 3.33/0.82  % (4942)------------------------------
% 3.33/0.82  % (4942)------------------------------
% 3.33/0.83  % (4953)dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 3.33/0.84  % (4954)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 3.33/0.85  % (4948)Refutation not found, incomplete strategy% (4948)------------------------------
% 3.33/0.85  % (4948)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.33/0.85  % (4948)Termination reason: Refutation not found, incomplete strategy
% 3.33/0.85  
% 3.33/0.85  % (4948)Memory used [KB]: 6140
% 3.33/0.85  % (4948)Time elapsed: 0.247 s
% 3.33/0.85  % (4948)------------------------------
% 3.33/0.85  % (4948)------------------------------
% 3.74/0.86  % (4949)Refutation not found, incomplete strategy% (4949)------------------------------
% 3.74/0.86  % (4949)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.74/0.86  % (4949)Termination reason: Refutation not found, incomplete strategy
% 3.74/0.86  
% 3.74/0.86  % (4949)Memory used [KB]: 6268
% 3.74/0.86  % (4949)Time elapsed: 0.140 s
% 3.74/0.86  % (4949)------------------------------
% 3.74/0.86  % (4949)------------------------------
% 3.74/0.93  % (4910)Time limit reached!
% 3.74/0.93  % (4910)------------------------------
% 3.74/0.93  % (4910)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.74/0.93  % (4910)Termination reason: Time limit
% 3.74/0.93  
% 3.74/0.93  % (4910)Memory used [KB]: 12153
% 3.74/0.93  % (4910)Time elapsed: 0.524 s
% 3.74/0.93  % (4910)------------------------------
% 3.74/0.93  % (4910)------------------------------
% 4.94/1.07  % (4911)Time limit reached!
% 4.94/1.07  % (4911)------------------------------
% 4.94/1.07  % (4911)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.94/1.07  % (4911)Termination reason: Time limit
% 4.94/1.07  % (4911)Termination phase: Saturation
% 4.94/1.07  
% 4.94/1.07  % (4911)Memory used [KB]: 2942
% 4.94/1.07  % (4911)Time elapsed: 0.600 s
% 4.94/1.07  % (4911)------------------------------
% 4.94/1.07  % (4911)------------------------------
% 4.94/1.12  % (4951)Time limit reached!
% 4.94/1.12  % (4951)------------------------------
% 4.94/1.12  % (4951)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.94/1.12  % (4951)Termination reason: Time limit
% 4.94/1.12  % (4951)Termination phase: Saturation
% 4.94/1.12  
% 4.94/1.12  % (4951)Memory used [KB]: 6780
% 4.94/1.12  % (4951)Time elapsed: 0.400 s
% 4.94/1.12  % (4951)------------------------------
% 4.94/1.12  % (4951)------------------------------
% 5.72/1.15  % (4953)Time limit reached!
% 5.72/1.15  % (4953)------------------------------
% 5.72/1.15  % (4953)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.72/1.15  % (4953)Termination reason: Time limit
% 5.72/1.15  % (4953)Termination phase: Saturation
% 5.72/1.15  
% 5.72/1.15  % (4953)Memory used [KB]: 4477
% 5.72/1.15  % (4953)Time elapsed: 0.400 s
% 5.72/1.15  % (4953)------------------------------
% 5.72/1.15  % (4953)------------------------------
% 5.72/1.15  % (4954)Time limit reached!
% 5.72/1.15  % (4954)------------------------------
% 5.72/1.15  % (4954)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.72/1.15  % (4954)Termination reason: Time limit
% 5.72/1.15  
% 5.72/1.15  % (4954)Memory used [KB]: 7164
% 5.72/1.15  % (4954)Time elapsed: 0.425 s
% 5.72/1.15  % (4954)------------------------------
% 5.72/1.15  % (4954)------------------------------
% 6.44/1.25  % (4950)Time limit reached!
% 6.44/1.25  % (4950)------------------------------
% 6.44/1.25  % (4950)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.44/1.25  % (4950)Termination reason: Time limit
% 6.44/1.25  % (4950)Termination phase: Saturation
% 6.44/1.25  
% 6.44/1.25  % (4950)Memory used [KB]: 7931
% 6.44/1.25  % (4950)Time elapsed: 0.500 s
% 6.44/1.25  % (4950)------------------------------
% 6.44/1.25  % (4950)------------------------------
% 7.27/1.32  % SZS status CounterSatisfiable for theBenchmark
% 7.27/1.32  % (4909)# SZS output start Saturation.
% 7.27/1.32  cnf(u30,negated_conjecture,
% 7.27/1.32      l1_orders_2(sK0)).
% 7.27/1.32  
% 7.27/1.32  cnf(u115,negated_conjecture,
% 7.27/1.32      m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))).
% 7.27/1.32  
% 7.27/1.32  cnf(u64,negated_conjecture,
% 7.27/1.32      m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))).
% 7.27/1.32  
% 7.27/1.32  cnf(u41,axiom,
% 7.27/1.32      m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)).
% 7.27/1.32  
% 7.27/1.32  cnf(u32,negated_conjecture,
% 7.27/1.32      m1_subset_1(sK2,u1_struct_0(sK0))).
% 7.27/1.32  
% 7.27/1.32  cnf(u31,negated_conjecture,
% 7.27/1.32      m1_subset_1(sK1,u1_struct_0(sK0))).
% 7.27/1.32  
% 7.27/1.32  cnf(u58,negated_conjecture,
% 7.27/1.32      ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_tarski(X0,X0) = k6_domain_1(u1_struct_0(sK0),X0) | ~l1_struct_0(sK0)).
% 7.27/1.32  
% 7.27/1.32  cnf(u46,axiom,
% 7.27/1.32      v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1)).
% 7.27/1.32  
% 7.27/1.32  cnf(u55,negated_conjecture,
% 7.27/1.32      ~v1_xboole_0(u1_struct_0(sK0)) | ~l1_struct_0(sK0)).
% 7.27/1.32  
% 7.27/1.32  cnf(u44,axiom,
% 7.27/1.32      l1_struct_0(X0) | ~l1_orders_2(X0)).
% 7.27/1.32  
% 7.27/1.32  cnf(u43,axiom,
% 7.27/1.32      v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0))).
% 7.27/1.32  
% 7.27/1.32  cnf(u29,negated_conjecture,
% 7.27/1.32      ~v2_struct_0(sK0)).
% 7.27/1.32  
% 7.27/1.32  cnf(u38,axiom,
% 7.27/1.32      r2_hidden(sK3(X0,X1,X2),X2) | sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | k2_tarski(X0,X1) = X2).
% 7.27/1.32  
% 7.27/1.32  cnf(u50,axiom,
% 7.27/1.32      r2_hidden(X4,k2_tarski(X4,X1))).
% 7.27/1.32  
% 7.27/1.32  cnf(u48,axiom,
% 7.27/1.32      r2_hidden(X4,k2_tarski(X0,X4))).
% 7.27/1.32  
% 7.27/1.32  cnf(u33,negated_conjecture,
% 7.27/1.32      r2_hidden(sK2,k6_waybel_0(sK0,sK1)) | r1_orders_2(sK0,sK1,sK2)).
% 7.27/1.32  
% 7.27/1.32  cnf(u912,axiom,
% 7.27/1.32      ~r2_hidden(X40,k2_tarski(X40,X40)) | k2_tarski(X40,X40) = k2_tarski(X39,X40) | sK3(X39,X40,k2_tarski(X40,X40)) = X39).
% 7.27/1.32  
% 7.27/1.32  cnf(u1662,axiom,
% 7.27/1.32      ~r2_hidden(X58,k2_tarski(X58,X58)) | k2_tarski(X58,X59) = k2_tarski(X58,X58) | sK3(X58,X59,k2_tarski(X58,X58)) = X59).
% 7.27/1.32  
% 7.27/1.32  cnf(u195,axiom,
% 7.27/1.32      ~r2_hidden(X12,k2_tarski(X12,X13)) | k2_tarski(X12,X12) = k2_tarski(X12,X13) | sK3(X12,X12,k2_tarski(X12,X13)) = X13).
% 7.27/1.32  
% 7.27/1.32  cnf(u793,axiom,
% 7.27/1.32      ~r2_hidden(X38,k2_tarski(X38,X37)) | k2_tarski(X38,X37) = k2_tarski(X37,X38)).
% 7.27/1.32  
% 7.27/1.32  cnf(u390,axiom,
% 7.27/1.32      ~r2_hidden(X19,k2_tarski(X19,X20)) | k2_tarski(X19,X20) = k2_tarski(X18,X19) | sK3(X18,X19,k2_tarski(X19,X20)) = X18 | sK3(X18,X19,k2_tarski(X19,X20)) = X20).
% 7.27/1.32  
% 7.27/1.32  cnf(u545,axiom,
% 7.27/1.32      ~r2_hidden(X27,k2_tarski(X27,X29)) | k2_tarski(X27,X29) = k2_tarski(X27,X28) | sK3(X27,X28,k2_tarski(X27,X29)) = X28 | sK3(X27,X28,k2_tarski(X27,X29)) = X29).
% 7.27/1.32  
% 7.27/1.32  cnf(u2432,axiom,
% 7.27/1.32      ~r2_hidden(X260,k2_tarski(X259,X259)) | k2_tarski(X259,X259) = k2_tarski(sK3(X257,X258,k2_tarski(X259,X259)),X260) | sK3(sK3(X257,X258,k2_tarski(X259,X259)),X260,k2_tarski(X259,X259)) = X259 | sK3(X257,X258,k2_tarski(X259,X259)) = X258 | sK3(X257,X258,k2_tarski(X259,X259)) = X257 | k2_tarski(X259,X259) = k2_tarski(X257,X258)).
% 7.27/1.32  
% 7.27/1.32  cnf(u2424,axiom,
% 7.27/1.32      ~r2_hidden(X228,k2_tarski(X227,X227)) | k2_tarski(X227,X227) = k2_tarski(X228,sK3(X225,X226,k2_tarski(X227,X227))) | sK3(X228,sK3(X225,X226,k2_tarski(X227,X227)),k2_tarski(X227,X227)) = X227 | sK3(X225,X226,k2_tarski(X227,X227)) = X226 | sK3(X225,X226,k2_tarski(X227,X227)) = X225 | k2_tarski(X227,X227) = k2_tarski(X225,X226)).
% 7.27/1.32  
% 7.27/1.32  cnf(u2370,axiom,
% 7.27/1.32      ~r2_hidden(X9,k2_tarski(X8,X8)) | sK3(X6,X7,k2_tarski(X8,X8)) = X9 | X8 = X9 | sK3(X6,X7,k2_tarski(X8,X8)) = X7 | sK3(X6,X7,k2_tarski(X8,X8)) = X6 | k2_tarski(X6,X7) = k2_tarski(X8,X8)).
% 7.27/1.32  
% 7.27/1.32  cnf(u1715,axiom,
% 7.27/1.32      ~r2_hidden(X65,k2_tarski(X64,X64)) | k2_tarski(X64,X65) = k2_tarski(X64,X64)).
% 7.27/1.32  
% 7.27/1.32  cnf(u1589,axiom,
% 7.27/1.32      ~r2_hidden(X59,k2_tarski(X60,X60)) | k2_tarski(X60,X60) = k2_tarski(X59,X60)).
% 7.27/1.32  
% 7.27/1.32  cnf(u772,axiom,
% 7.27/1.32      ~r2_hidden(X45,k2_tarski(X46,X46)) | k2_tarski(X44,X45) = k2_tarski(X46,X46) | sK3(X44,X45,k2_tarski(X46,X46)) = X44 | sK3(X44,X45,k2_tarski(X46,X46)) = X46).
% 7.27/1.32  
% 7.27/1.32  cnf(u770,axiom,
% 7.27/1.32      ~r2_hidden(X41,k2_tarski(X43,X43)) | k2_tarski(X43,X43) = k2_tarski(X41,X42) | sK3(X41,X42,k2_tarski(X43,X43)) = X42 | sK3(X41,X42,k2_tarski(X43,X43)) = X43).
% 7.27/1.32  
% 7.27/1.32  cnf(u323,axiom,
% 7.27/1.32      ~r2_hidden(X12,k2_tarski(X13,X13)) | k2_tarski(X12,X12) = k2_tarski(X13,X13) | sK3(X12,X12,k2_tarski(X13,X13)) = X13).
% 7.27/1.32  
% 7.27/1.32  cnf(u255,axiom,
% 7.27/1.32      ~r2_hidden(X12,k2_tarski(X13,X12)) | k2_tarski(X12,X12) = k2_tarski(X13,X12) | sK3(X12,X12,k2_tarski(X13,X12)) = X13).
% 7.27/1.32  
% 7.27/1.32  cnf(u675,axiom,
% 7.27/1.32      ~r2_hidden(X28,k2_tarski(X29,X28)) | k2_tarski(X29,X28) = k2_tarski(X28,X29) | sK3(X28,X29,k2_tarski(X29,X28)) = X29).
% 7.27/1.32  
% 7.27/1.32  cnf(u459,axiom,
% 7.27/1.32      ~r2_hidden(X25,k2_tarski(X26,X25)) | k2_tarski(X26,X25) = k2_tarski(X24,X25) | sK3(X24,X25,k2_tarski(X26,X25)) = X24 | sK3(X24,X25,k2_tarski(X26,X25)) = X26).
% 7.27/1.32  
% 7.27/1.32  cnf(u633,axiom,
% 7.27/1.32      ~r2_hidden(X33,k2_tarski(X35,X33)) | k2_tarski(X33,X34) = k2_tarski(X35,X33) | sK3(X33,X34,k2_tarski(X35,X33)) = X34 | sK3(X33,X34,k2_tarski(X35,X33)) = X35).
% 7.27/1.32  
% 7.27/1.32  cnf(u2188,axiom,
% 7.27/1.32      ~r2_hidden(X2,k2_tarski(X1,X0)) | k2_tarski(X1,X0) = k2_tarski(X0,X2) | sK3(X0,X2,k2_tarski(X1,X0)) = X1).
% 7.27/1.32  
% 7.27/1.32  cnf(u2173,axiom,
% 7.27/1.32      ~r2_hidden(X96,k2_tarski(X95,X97)) | k2_tarski(X95,X96) = k2_tarski(X95,X97) | sK3(X95,X96,k2_tarski(X95,X97)) = X97).
% 7.27/1.32  
% 7.27/1.32  cnf(u1894,axiom,
% 7.27/1.32      ~r2_hidden(X2,k2_tarski(X1,X0)) | k2_tarski(X1,X0) = k2_tarski(X2,X0) | sK3(X2,X0,k2_tarski(X1,X0)) = X1).
% 7.27/1.32  
% 7.27/1.32  cnf(u1872,axiom,
% 7.27/1.32      ~r2_hidden(X87,k2_tarski(X88,X89)) | k2_tarski(X88,X89) = k2_tarski(X87,X88) | sK3(X87,X88,k2_tarski(X88,X89)) = X89).
% 7.27/1.32  
% 7.27/1.32  cnf(u1473,axiom,
% 7.27/1.32      ~r2_hidden(X79,k2_tarski(X82,X83)) | k2_tarski(X82,X83) = k2_tarski(X79,sK3(X80,X81,k2_tarski(X82,X83))) | sK3(X79,sK3(X80,X81,k2_tarski(X82,X83)),k2_tarski(X82,X83)) = X82 | sK3(X79,sK3(X80,X81,k2_tarski(X82,X83)),k2_tarski(X82,X83)) = X83 | sK3(X80,X81,k2_tarski(X82,X83)) = X81 | sK3(X80,X81,k2_tarski(X82,X83)) = X80 | k2_tarski(X82,X83) = k2_tarski(X80,X81)).
% 7.27/1.32  
% 7.27/1.32  cnf(u1143,axiom,
% 7.27/1.32      ~r2_hidden(X76,k2_tarski(X74,X75)) | k2_tarski(X74,X75) = k2_tarski(sK3(X72,X73,k2_tarski(X74,X75)),X76) | sK3(sK3(X72,X73,k2_tarski(X74,X75)),X76,k2_tarski(X74,X75)) = X74 | sK3(sK3(X72,X73,k2_tarski(X74,X75)),X76,k2_tarski(X74,X75)) = X75 | sK3(X72,X73,k2_tarski(X74,X75)) = X73 | sK3(X72,X73,k2_tarski(X74,X75)) = X72 | k2_tarski(X74,X75) = k2_tarski(X72,X73)).
% 7.27/1.32  
% 7.27/1.32  cnf(u638,axiom,
% 7.27/1.32      ~r2_hidden(X37,k2_tarski(X38,X36)) | k2_tarski(X36,X37) = k2_tarski(X38,X36) | sK3(X36,X37,k2_tarski(X38,X36)) = X38 | sK3(X36,X37,k2_tarski(X38,X36)) = X36).
% 7.27/1.32  
% 7.27/1.32  cnf(u547,axiom,
% 7.27/1.32      ~r2_hidden(X31,k2_tarski(X30,X32)) | k2_tarski(X30,X32) = k2_tarski(X30,X31) | sK3(X30,X31,k2_tarski(X30,X32)) = X30 | sK3(X30,X31,k2_tarski(X30,X32)) = X32).
% 7.27/1.32  
% 7.27/1.32  cnf(u466,axiom,
% 7.27/1.32      ~r2_hidden(X21,k2_tarski(X23,X22)) | k2_tarski(X23,X22) = k2_tarski(X21,X22) | sK3(X21,X22,k2_tarski(X23,X22)) = X23 | sK3(X21,X22,k2_tarski(X23,X22)) = X22).
% 7.27/1.32  
% 7.27/1.32  cnf(u394,axiom,
% 7.27/1.32      ~r2_hidden(X15,k2_tarski(X16,X17)) | k2_tarski(X16,X17) = k2_tarski(X15,X16) | sK3(X15,X16,k2_tarski(X16,X17)) = X16 | sK3(X15,X16,k2_tarski(X16,X17)) = X17).
% 7.27/1.32  
% 7.27/1.32  cnf(u162,axiom,
% 7.27/1.32      ~r2_hidden(X18,k2_tarski(X19,X20)) | k2_tarski(X19,X20) = k2_tarski(X18,X18) | sK3(X18,X18,k2_tarski(X19,X20)) = X19 | sK3(X18,X18,k2_tarski(X19,X20)) = X20).
% 7.27/1.32  
% 7.27/1.32  cnf(u113,axiom,
% 7.27/1.32      ~r2_hidden(X9,k2_tarski(X10,X11)) | k2_tarski(X10,X11) = k2_tarski(X8,X9) | sK3(X8,X9,k2_tarski(X10,X11)) = X8 | sK3(X8,X9,k2_tarski(X10,X11)) = X10 | sK3(X8,X9,k2_tarski(X10,X11)) = X11).
% 7.27/1.32  
% 7.27/1.32  cnf(u111,axiom,
% 7.27/1.32      ~r2_hidden(X4,k2_tarski(X6,X7)) | k2_tarski(X6,X7) = k2_tarski(X4,X5) | sK3(X4,X5,k2_tarski(X6,X7)) = X5 | sK3(X4,X5,k2_tarski(X6,X7)) = X6 | sK3(X4,X5,k2_tarski(X6,X7)) = X7).
% 7.27/1.32  
% 7.27/1.32  cnf(u51,axiom,
% 7.27/1.32      ~r2_hidden(X4,k2_tarski(X0,X1)) | X0 = X4 | X1 = X4).
% 7.27/1.32  
% 7.27/1.32  cnf(u34,negated_conjecture,
% 7.27/1.32      ~r2_hidden(sK2,k6_waybel_0(sK0,sK1)) | ~r1_orders_2(sK0,sK1,sK2)).
% 7.27/1.32  
% 7.27/1.32  cnf(u2180,axiom,
% 7.27/1.32      sK3(sK3(X5,X6,k2_tarski(X4,X4)),X7,k2_tarski(X4,X4)) = X7 | sK3(sK3(X5,X6,k2_tarski(X4,X4)),X7,k2_tarski(X4,X4)) = X4 | k2_tarski(X4,X4) = k2_tarski(sK3(X5,X6,k2_tarski(X4,X4)),X7) | sK3(X5,X6,k2_tarski(X4,X4)) = X6 | sK3(X5,X6,k2_tarski(X4,X4)) = X5 | k2_tarski(X4,X4) = k2_tarski(X5,X6)).
% 7.27/1.32  
% 7.27/1.32  cnf(u2180,axiom,
% 7.27/1.32      sK3(sK3(X5,X6,k2_tarski(X4,X4)),X7,k2_tarski(X4,X4)) = X7 | sK3(sK3(X5,X6,k2_tarski(X4,X4)),X7,k2_tarski(X4,X4)) = X4 | k2_tarski(X4,X4) = k2_tarski(sK3(X5,X6,k2_tarski(X4,X4)),X7) | sK3(X5,X6,k2_tarski(X4,X4)) = X6 | sK3(X5,X6,k2_tarski(X4,X4)) = X5 | k2_tarski(X4,X4) = k2_tarski(X5,X6)).
% 7.27/1.32  
% 7.27/1.32  cnf(u4999,axiom,
% 7.27/1.32      sK3(sK3(X0,X1,k2_tarski(X2,X2)),sK3(X3,X4,k2_tarski(X2,X2)),k2_tarski(X2,X2)) = X2 | k2_tarski(X2,X2) = k2_tarski(sK3(X0,X1,k2_tarski(X2,X2)),sK3(X3,X4,k2_tarski(X2,X2))) | sK3(X0,X1,k2_tarski(X2,X2)) = X1 | sK3(X0,X1,k2_tarski(X2,X2)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X2) | sK3(X3,X4,k2_tarski(X2,X2)) = X4 | sK3(X3,X4,k2_tarski(X2,X2)) = X3 | k2_tarski(X2,X2) = k2_tarski(X3,X4)).
% 7.27/1.32  
% 7.27/1.32  cnf(u2578,axiom,
% 7.27/1.32      sK3(sK3(X16,X17,k2_tarski(X15,X15)),sK3(X13,X14,k2_tarski(X15,X15)),k2_tarski(X15,X15)) = X15 | k2_tarski(X15,X15) = k2_tarski(sK3(X13,X14,k2_tarski(X15,X15)),sK3(X16,X17,k2_tarski(X15,X15))) | sK3(X16,X17,k2_tarski(X15,X15)) = X17 | sK3(X16,X17,k2_tarski(X15,X15)) = X16 | k2_tarski(X16,X17) = k2_tarski(X15,X15) | sK3(X13,X14,k2_tarski(X15,X15)) = X14 | sK3(X13,X14,k2_tarski(X15,X15)) = X13 | k2_tarski(X13,X14) = k2_tarski(X15,X15)).
% 7.27/1.32  
% 7.27/1.32  cnf(u330,axiom,
% 7.27/1.32      sK3(sK3(X2,X3,k2_tarski(X4,X4)),sK3(X2,X3,k2_tarski(X4,X4)),k2_tarski(X4,X4)) = X4 | k2_tarski(X4,X4) = k2_tarski(sK3(X2,X3,k2_tarski(X4,X4)),sK3(X2,X3,k2_tarski(X4,X4))) | sK3(X2,X3,k2_tarski(X4,X4)) = X3 | sK3(X2,X3,k2_tarski(X4,X4)) = X2 | k2_tarski(X2,X3) = k2_tarski(X4,X4)).
% 7.27/1.32  
% 7.27/1.32  cnf(u3149,axiom,
% 7.27/1.32      sK3(sK3(X10,X11,k2_tarski(X8,X9)),sK3(X12,X13,k2_tarski(X8,X9)),k2_tarski(X8,X9)) = X8 | sK3(sK3(X10,X11,k2_tarski(X8,X9)),sK3(X12,X13,k2_tarski(X8,X9)),k2_tarski(X8,X9)) = X9 | k2_tarski(X8,X9) = k2_tarski(sK3(X10,X11,k2_tarski(X8,X9)),sK3(X12,X13,k2_tarski(X8,X9))) | sK3(X10,X11,k2_tarski(X8,X9)) = X11 | sK3(X10,X11,k2_tarski(X8,X9)) = X10 | k2_tarski(X10,X11) = k2_tarski(X8,X9) | sK3(X12,X13,k2_tarski(X8,X9)) = X13 | sK3(X12,X13,k2_tarski(X8,X9)) = X12 | k2_tarski(X8,X9) = k2_tarski(X12,X13)).
% 7.27/1.32  
% 7.27/1.32  cnf(u3149,axiom,
% 7.27/1.32      sK3(sK3(X10,X11,k2_tarski(X8,X9)),sK3(X12,X13,k2_tarski(X8,X9)),k2_tarski(X8,X9)) = X8 | sK3(sK3(X10,X11,k2_tarski(X8,X9)),sK3(X12,X13,k2_tarski(X8,X9)),k2_tarski(X8,X9)) = X9 | k2_tarski(X8,X9) = k2_tarski(sK3(X10,X11,k2_tarski(X8,X9)),sK3(X12,X13,k2_tarski(X8,X9))) | sK3(X10,X11,k2_tarski(X8,X9)) = X11 | sK3(X10,X11,k2_tarski(X8,X9)) = X10 | k2_tarski(X10,X11) = k2_tarski(X8,X9) | sK3(X12,X13,k2_tarski(X8,X9)) = X13 | sK3(X12,X13,k2_tarski(X8,X9)) = X12 | k2_tarski(X8,X9) = k2_tarski(X12,X13)).
% 7.27/1.32  
% 7.27/1.32  cnf(u1735,axiom,
% 7.27/1.32      sK3(sK3(X6,X7,k2_tarski(X4,X5)),sK3(X6,X7,k2_tarski(X4,X5)),k2_tarski(X4,X5)) = X4 | sK3(sK3(X6,X7,k2_tarski(X4,X5)),sK3(X6,X7,k2_tarski(X4,X5)),k2_tarski(X4,X5)) = X5 | k2_tarski(X4,X5) = k2_tarski(sK3(X6,X7,k2_tarski(X4,X5)),sK3(X6,X7,k2_tarski(X4,X5))) | sK3(X6,X7,k2_tarski(X4,X5)) = X7 | sK3(X6,X7,k2_tarski(X4,X5)) = X6 | k2_tarski(X6,X7) = k2_tarski(X4,X5)).
% 7.27/1.32  
% 7.27/1.32  cnf(u1735,axiom,
% 7.27/1.32      sK3(sK3(X6,X7,k2_tarski(X4,X5)),sK3(X6,X7,k2_tarski(X4,X5)),k2_tarski(X4,X5)) = X4 | sK3(sK3(X6,X7,k2_tarski(X4,X5)),sK3(X6,X7,k2_tarski(X4,X5)),k2_tarski(X4,X5)) = X5 | k2_tarski(X4,X5) = k2_tarski(sK3(X6,X7,k2_tarski(X4,X5)),sK3(X6,X7,k2_tarski(X4,X5))) | sK3(X6,X7,k2_tarski(X4,X5)) = X7 | sK3(X6,X7,k2_tarski(X4,X5)) = X6 | k2_tarski(X6,X7) = k2_tarski(X4,X5)).
% 7.27/1.32  
% 7.27/1.32  cnf(u269,axiom,
% 7.27/1.32      sK3(sK3(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X10 | sK3(sK3(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X6 | sK3(sK3(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X7 | k2_tarski(X6,X7) = k2_tarski(sK3(X8,X9,k2_tarski(X6,X7)),X10) | sK3(X8,X9,k2_tarski(X6,X7)) = X9 | sK3(X8,X9,k2_tarski(X6,X7)) = X8 | k2_tarski(X6,X7) = k2_tarski(X8,X9)).
% 7.27/1.32  
% 7.27/1.32  cnf(u269,axiom,
% 7.27/1.32      sK3(sK3(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X10 | sK3(sK3(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X6 | sK3(sK3(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X7 | k2_tarski(X6,X7) = k2_tarski(sK3(X8,X9,k2_tarski(X6,X7)),X10) | sK3(X8,X9,k2_tarski(X6,X7)) = X9 | sK3(X8,X9,k2_tarski(X6,X7)) = X8 | k2_tarski(X6,X7) = k2_tarski(X8,X9)).
% 7.27/1.32  
% 7.27/1.32  cnf(u269,axiom,
% 7.27/1.32      sK3(sK3(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X10 | sK3(sK3(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X6 | sK3(sK3(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X7 | k2_tarski(X6,X7) = k2_tarski(sK3(X8,X9,k2_tarski(X6,X7)),X10) | sK3(X8,X9,k2_tarski(X6,X7)) = X9 | sK3(X8,X9,k2_tarski(X6,X7)) = X8 | k2_tarski(X6,X7) = k2_tarski(X8,X9)).
% 7.27/1.32  
% 7.27/1.32  cnf(u2575,axiom,
% 7.27/1.32      sK3(sK3(X2,X3,k2_tarski(X1,X0)),X0,k2_tarski(X1,X0)) = X1 | k2_tarski(X1,X0) = k2_tarski(X0,sK3(X2,X3,k2_tarski(X1,X0))) | sK3(X2,X3,k2_tarski(X1,X0)) = X3 | sK3(X2,X3,k2_tarski(X1,X0)) = X2 | k2_tarski(X1,X0) = k2_tarski(X2,X3)).
% 7.27/1.32  
% 7.27/1.32  cnf(u1896,axiom,
% 7.27/1.32      sK3(sK3(X6,X7,k2_tarski(X4,X5)),X4,k2_tarski(X4,X5)) = X5 | k2_tarski(X4,X5) = k2_tarski(X4,sK3(X6,X7,k2_tarski(X4,X5))) | sK3(X6,X7,k2_tarski(X4,X5)) = X7 | sK3(X6,X7,k2_tarski(X4,X5)) = X6 | k2_tarski(X6,X7) = k2_tarski(X4,X5)).
% 7.27/1.32  
% 7.27/1.32  cnf(u2187,axiom,
% 7.27/1.32      sK3(X4,sK3(X5,X6,k2_tarski(X4,X7)),k2_tarski(X4,X7)) = X7 | k2_tarski(X4,X7) = k2_tarski(X4,sK3(X5,X6,k2_tarski(X4,X7))) | sK3(X5,X6,k2_tarski(X4,X7)) = X6 | sK3(X5,X6,k2_tarski(X4,X7)) = X5 | k2_tarski(X5,X6) = k2_tarski(X4,X7)).
% 7.27/1.32  
% 7.27/1.32  cnf(u2184,axiom,
% 7.27/1.32      sK3(X4,sK3(X5,X6,k2_tarski(X7,X7)),k2_tarski(X7,X7)) = X4 | sK3(X4,sK3(X5,X6,k2_tarski(X7,X7)),k2_tarski(X7,X7)) = X7 | k2_tarski(X7,X7) = k2_tarski(X4,sK3(X5,X6,k2_tarski(X7,X7))) | sK3(X5,X6,k2_tarski(X7,X7)) = X6 | sK3(X5,X6,k2_tarski(X7,X7)) = X5 | k2_tarski(X7,X7) = k2_tarski(X5,X6)).
% 7.27/1.32  
% 7.27/1.32  cnf(u2184,axiom,
% 7.27/1.32      sK3(X4,sK3(X5,X6,k2_tarski(X7,X7)),k2_tarski(X7,X7)) = X4 | sK3(X4,sK3(X5,X6,k2_tarski(X7,X7)),k2_tarski(X7,X7)) = X7 | k2_tarski(X7,X7) = k2_tarski(X4,sK3(X5,X6,k2_tarski(X7,X7))) | sK3(X5,X6,k2_tarski(X7,X7)) = X6 | sK3(X5,X6,k2_tarski(X7,X7)) = X5 | k2_tarski(X7,X7) = k2_tarski(X5,X6)).
% 7.27/1.32  
% 7.27/1.32  cnf(u2691,axiom,
% 7.27/1.32      sK3(X0,sK3(X2,X3,k2_tarski(X1,X0)),k2_tarski(X1,X0)) = X1 | k2_tarski(X1,X0) = k2_tarski(X0,sK3(X2,X3,k2_tarski(X1,X0))) | sK3(X2,X3,k2_tarski(X1,X0)) = X3 | sK3(X2,X3,k2_tarski(X1,X0)) = X2 | k2_tarski(X1,X0) = k2_tarski(X2,X3)).
% 7.27/1.32  
% 7.27/1.32  cnf(u291,axiom,
% 7.27/1.32      sK3(X8,sK3(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X8 | sK3(X8,sK3(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X6 | sK3(X8,sK3(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X7 | k2_tarski(X6,X7) = k2_tarski(X8,sK3(X9,X10,k2_tarski(X6,X7))) | sK3(X9,X10,k2_tarski(X6,X7)) = X10 | sK3(X9,X10,k2_tarski(X6,X7)) = X9 | k2_tarski(X6,X7) = k2_tarski(X9,X10)).
% 7.27/1.32  
% 7.27/1.32  cnf(u291,axiom,
% 7.27/1.32      sK3(X8,sK3(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X8 | sK3(X8,sK3(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X6 | sK3(X8,sK3(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X7 | k2_tarski(X6,X7) = k2_tarski(X8,sK3(X9,X10,k2_tarski(X6,X7))) | sK3(X9,X10,k2_tarski(X6,X7)) = X10 | sK3(X9,X10,k2_tarski(X6,X7)) = X9 | k2_tarski(X6,X7) = k2_tarski(X9,X10)).
% 7.27/1.32  
% 7.27/1.32  cnf(u291,axiom,
% 7.27/1.32      sK3(X8,sK3(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X8 | sK3(X8,sK3(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X6 | sK3(X8,sK3(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X7 | k2_tarski(X6,X7) = k2_tarski(X8,sK3(X9,X10,k2_tarski(X6,X7))) | sK3(X9,X10,k2_tarski(X6,X7)) = X10 | sK3(X9,X10,k2_tarski(X6,X7)) = X9 | k2_tarski(X6,X7) = k2_tarski(X9,X10)).
% 7.27/1.32  
% 7.27/1.32  cnf(u165,axiom,
% 7.27/1.32      sK3(X0,X0,k2_tarski(X0,X1)) = X0 | sK3(X0,X0,k2_tarski(X0,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X0,X0)).
% 7.27/1.32  
% 7.27/1.32  cnf(u203,axiom,
% 7.27/1.32      sK3(X1,X1,k2_tarski(X1,X2)) = X2 | k2_tarski(X1,X1) = k2_tarski(X1,X2)).
% 7.27/1.32  
% 7.27/1.32  cnf(u165,axiom,
% 7.27/1.32      sK3(X0,X0,k2_tarski(X0,X1)) = X0 | sK3(X0,X0,k2_tarski(X0,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X0,X0)).
% 7.27/1.32  
% 7.27/1.32  cnf(u294,axiom,
% 7.27/1.32      sK3(X0,X0,k2_tarski(X1,X1)) = X0 | sK3(X0,X0,k2_tarski(X1,X1)) = X1 | k2_tarski(X0,X0) = k2_tarski(X1,X1)).
% 7.27/1.32  
% 7.27/1.32  cnf(u294,axiom,
% 7.27/1.32      sK3(X0,X0,k2_tarski(X1,X1)) = X0 | sK3(X0,X0,k2_tarski(X1,X1)) = X1 | k2_tarski(X0,X0) = k2_tarski(X1,X1)).
% 7.27/1.32  
% 7.27/1.32  cnf(u229,axiom,
% 7.27/1.32      sK3(X0,X0,k2_tarski(X1,X0)) = X1 | sK3(X0,X0,k2_tarski(X1,X0)) = X0 | k2_tarski(X0,X0) = k2_tarski(X1,X0)).
% 7.27/1.32  
% 7.27/1.32  cnf(u229,axiom,
% 7.27/1.32      sK3(X0,X0,k2_tarski(X1,X0)) = X1 | sK3(X0,X0,k2_tarski(X1,X0)) = X0 | k2_tarski(X0,X0) = k2_tarski(X1,X0)).
% 7.27/1.32  
% 7.27/1.32  cnf(u265,axiom,
% 7.27/1.32      sK3(X0,X0,k2_tarski(X1,X0)) = X1 | k2_tarski(X0,X0) = k2_tarski(X1,X0)).
% 7.27/1.32  
% 7.27/1.32  cnf(u116,axiom,
% 7.27/1.32      sK3(X0,X0,k2_tarski(X1,X2)) = X0 | sK3(X0,X0,k2_tarski(X1,X2)) = X1 | sK3(X0,X0,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X0) = k2_tarski(X1,X2)).
% 7.27/1.32  
% 7.27/1.32  cnf(u116,axiom,
% 7.27/1.32      sK3(X0,X0,k2_tarski(X1,X2)) = X0 | sK3(X0,X0,k2_tarski(X1,X2)) = X1 | sK3(X0,X0,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X0) = k2_tarski(X1,X2)).
% 7.27/1.32  
% 7.27/1.32  cnf(u116,axiom,
% 7.27/1.32      sK3(X0,X0,k2_tarski(X1,X2)) = X0 | sK3(X0,X0,k2_tarski(X1,X2)) = X1 | sK3(X0,X0,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X0) = k2_tarski(X1,X2)).
% 7.27/1.32  
% 7.27/1.32  cnf(u1605,axiom,
% 7.27/1.32      sK3(X0,X1,k2_tarski(X0,X0)) = X1 | sK3(X0,X1,k2_tarski(X0,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X0,X0)).
% 7.27/1.32  
% 7.27/1.32  cnf(u1605,axiom,
% 7.27/1.32      sK3(X0,X1,k2_tarski(X0,X0)) = X1 | sK3(X0,X1,k2_tarski(X0,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X0,X0)).
% 7.27/1.32  
% 7.27/1.32  cnf(u1673,axiom,
% 7.27/1.32      sK3(X0,X1,k2_tarski(X0,X0)) = X1 | k2_tarski(X0,X1) = k2_tarski(X0,X0)).
% 7.27/1.32  
% 7.27/1.32  cnf(u201,axiom,
% 7.27/1.32      sK3(X0,X1,k2_tarski(X0,X2)) = X1 | sK3(X0,X1,k2_tarski(X0,X2)) = X0 | sK3(X0,X1,k2_tarski(X0,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 7.27/1.32  
% 7.27/1.32  cnf(u1904,axiom,
% 7.27/1.32      sK3(X2,X4,k2_tarski(X2,X3)) = X4 | sK3(X2,X4,k2_tarski(X2,X3)) = X3 | k2_tarski(X2,X3) = k2_tarski(X2,X4)).
% 7.27/1.32  
% 7.27/1.32  cnf(u201,axiom,
% 7.27/1.32      sK3(X0,X1,k2_tarski(X0,X2)) = X1 | sK3(X0,X1,k2_tarski(X0,X2)) = X0 | sK3(X0,X1,k2_tarski(X0,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 7.27/1.32  
% 7.27/1.32  cnf(u201,axiom,
% 7.27/1.32      sK3(X0,X1,k2_tarski(X0,X2)) = X1 | sK3(X0,X1,k2_tarski(X0,X2)) = X0 | sK3(X0,X1,k2_tarski(X0,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 7.27/1.32  
% 7.27/1.32  cnf(u1904,axiom,
% 7.27/1.32      sK3(X2,X4,k2_tarski(X2,X3)) = X4 | sK3(X2,X4,k2_tarski(X2,X3)) = X3 | k2_tarski(X2,X3) = k2_tarski(X2,X4)).
% 7.27/1.32  
% 7.27/1.32  cnf(u874,axiom,
% 7.27/1.32      sK3(X0,X1,k2_tarski(X1,X1)) = X0 | sK3(X0,X1,k2_tarski(X1,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X1,X1)).
% 7.27/1.32  
% 7.27/1.32  cnf(u874,axiom,
% 7.27/1.32      sK3(X0,X1,k2_tarski(X1,X1)) = X0 | sK3(X0,X1,k2_tarski(X1,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X1,X1)).
% 7.27/1.32  
% 7.27/1.32  cnf(u1546,axiom,
% 7.27/1.32      sK3(X1,X0,k2_tarski(X0,X0)) = X1 | k2_tarski(X0,X0) = k2_tarski(X1,X0)).
% 7.27/1.32  
% 7.27/1.32  cnf(u642,axiom,
% 7.27/1.32      sK3(X0,X1,k2_tarski(X1,X0)) = X1 | sK3(X0,X1,k2_tarski(X1,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X1,X0)).
% 7.27/1.32  
% 7.27/1.32  cnf(u642,axiom,
% 7.27/1.32      sK3(X0,X1,k2_tarski(X1,X0)) = X1 | sK3(X0,X1,k2_tarski(X1,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X1,X0)).
% 7.27/1.32  
% 7.27/1.32  cnf(u775,axiom,
% 7.27/1.32      sK3(X1,X0,k2_tarski(X0,X1)) = X0 | k2_tarski(X0,X1) = k2_tarski(X1,X0)).
% 7.27/1.32  
% 7.27/1.32  cnf(u117,axiom,
% 7.27/1.32      sK3(X0,X1,k2_tarski(X1,X2)) = X0 | sK3(X0,X1,k2_tarski(X1,X2)) = X1 | sK3(X0,X1,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 7.27/1.32  
% 7.27/1.32  cnf(u1739,axiom,
% 7.27/1.32      sK3(X4,X2,k2_tarski(X2,X3)) = X4 | sK3(X4,X2,k2_tarski(X2,X3)) = X3 | k2_tarski(X2,X3) = k2_tarski(X4,X2)).
% 7.27/1.32  
% 7.27/1.32  cnf(u117,axiom,
% 7.27/1.32      sK3(X0,X1,k2_tarski(X1,X2)) = X0 | sK3(X0,X1,k2_tarski(X1,X2)) = X1 | sK3(X0,X1,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 7.27/1.32  
% 7.27/1.32  cnf(u117,axiom,
% 7.27/1.32      sK3(X0,X1,k2_tarski(X1,X2)) = X0 | sK3(X0,X1,k2_tarski(X1,X2)) = X1 | sK3(X0,X1,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 7.27/1.32  
% 7.27/1.32  cnf(u1739,axiom,
% 7.27/1.32      sK3(X4,X2,k2_tarski(X2,X3)) = X4 | sK3(X4,X2,k2_tarski(X2,X3)) = X3 | k2_tarski(X2,X3) = k2_tarski(X4,X2)).
% 7.27/1.32  
% 7.27/1.32  cnf(u65,axiom,
% 7.27/1.32      sK3(X0,X1,k2_tarski(X2,X3)) = X1 | sK3(X0,X1,k2_tarski(X2,X3)) = X0 | sK3(X0,X1,k2_tarski(X2,X3)) = X2 | sK3(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 7.27/1.32  
% 7.27/1.32  cnf(u65,axiom,
% 7.27/1.32      sK3(X0,X1,k2_tarski(X2,X3)) = X1 | sK3(X0,X1,k2_tarski(X2,X3)) = X0 | sK3(X0,X1,k2_tarski(X2,X3)) = X2 | sK3(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 7.27/1.32  
% 7.27/1.32  cnf(u65,axiom,
% 7.27/1.32      sK3(X0,X1,k2_tarski(X2,X3)) = X1 | sK3(X0,X1,k2_tarski(X2,X3)) = X0 | sK3(X0,X1,k2_tarski(X2,X3)) = X2 | sK3(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 7.27/1.32  
% 7.27/1.32  cnf(u65,axiom,
% 7.27/1.32      sK3(X0,X1,k2_tarski(X2,X3)) = X1 | sK3(X0,X1,k2_tarski(X2,X3)) = X0 | sK3(X0,X1,k2_tarski(X2,X3)) = X2 | sK3(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 7.27/1.32  
% 7.27/1.32  cnf(u227,axiom,
% 7.27/1.32      sK3(X0,X1,k2_tarski(X2,X2)) = X1 | sK3(X0,X1,k2_tarski(X2,X2)) = X0 | sK3(X0,X1,k2_tarski(X2,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 7.27/1.32  
% 7.27/1.32  cnf(u227,axiom,
% 7.27/1.32      sK3(X0,X1,k2_tarski(X2,X2)) = X1 | sK3(X0,X1,k2_tarski(X2,X2)) = X0 | sK3(X0,X1,k2_tarski(X2,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 7.27/1.32  
% 7.27/1.32  cnf(u227,axiom,
% 7.27/1.32      sK3(X0,X1,k2_tarski(X2,X2)) = X1 | sK3(X0,X1,k2_tarski(X2,X2)) = X0 | sK3(X0,X1,k2_tarski(X2,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 7.27/1.32  
% 7.27/1.32  cnf(u166,axiom,
% 7.27/1.32      sK3(X0,X1,k2_tarski(X2,X1)) = X0 | sK3(X0,X1,k2_tarski(X2,X1)) = X2 | sK3(X0,X1,k2_tarski(X2,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 7.27/1.32  
% 7.27/1.32  cnf(u166,axiom,
% 7.27/1.32      sK3(X0,X1,k2_tarski(X2,X1)) = X0 | sK3(X0,X1,k2_tarski(X2,X1)) = X2 | sK3(X0,X1,k2_tarski(X2,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 7.27/1.32  
% 7.27/1.32  cnf(u1880,axiom,
% 7.27/1.32      sK3(X2,X1,k2_tarski(X0,X1)) = X2 | sK3(X2,X1,k2_tarski(X0,X1)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 7.27/1.32  
% 7.27/1.32  cnf(u166,axiom,
% 7.27/1.32      sK3(X0,X1,k2_tarski(X2,X1)) = X0 | sK3(X0,X1,k2_tarski(X2,X1)) = X2 | sK3(X0,X1,k2_tarski(X2,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 7.27/1.32  
% 7.27/1.32  cnf(u1880,axiom,
% 7.27/1.32      sK3(X2,X1,k2_tarski(X0,X1)) = X2 | sK3(X2,X1,k2_tarski(X0,X1)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 7.27/1.32  
% 7.27/1.32  cnf(u204,axiom,
% 7.27/1.32      sK3(X0,X1,k2_tarski(X2,X0)) = X1 | sK3(X0,X1,k2_tarski(X2,X0)) = X2 | sK3(X0,X1,k2_tarski(X2,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 7.27/1.32  
% 7.27/1.32  cnf(u204,axiom,
% 7.27/1.32      sK3(X0,X1,k2_tarski(X2,X0)) = X1 | sK3(X0,X1,k2_tarski(X2,X0)) = X2 | sK3(X0,X1,k2_tarski(X2,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 7.27/1.32  
% 7.27/1.32  cnf(u2036,axiom,
% 7.27/1.32      sK3(X0,X1,k2_tarski(X2,X0)) = X1 | sK3(X0,X1,k2_tarski(X2,X0)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 7.27/1.32  
% 7.27/1.32  cnf(u204,axiom,
% 7.27/1.32      sK3(X0,X1,k2_tarski(X2,X0)) = X1 | sK3(X0,X1,k2_tarski(X2,X0)) = X2 | sK3(X0,X1,k2_tarski(X2,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 7.27/1.32  
% 7.27/1.32  cnf(u2036,axiom,
% 7.27/1.32      sK3(X0,X1,k2_tarski(X2,X0)) = X1 | sK3(X0,X1,k2_tarski(X2,X0)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 7.27/1.32  
% 7.27/1.32  cnf(u1721,axiom,
% 7.27/1.32      k2_tarski(X2,X2) = k2_tarski(X2,sK3(X3,X4,k2_tarski(X2,X2))) | sK3(X3,X4,k2_tarski(X2,X2)) = X4 | sK3(X3,X4,k2_tarski(X2,X2)) = X3 | k2_tarski(X2,X2) = k2_tarski(X3,X4)).
% 7.27/1.32  
% 7.27/1.32  cnf(u1594,axiom,
% 7.27/1.32      k2_tarski(X2,X2) = k2_tarski(sK3(X3,X4,k2_tarski(X2,X2)),X2) | sK3(X3,X4,k2_tarski(X2,X2)) = X4 | sK3(X3,X4,k2_tarski(X2,X2)) = X3 | k2_tarski(X2,X2) = k2_tarski(X3,X4)).
% 7.27/1.32  
% 7.27/1.32  cnf(u798,axiom,
% 7.27/1.32      k2_tarski(X1,X2) = k2_tarski(X2,X1)).
% 7.27/1.32  
% 7.27/1.32  cnf(u66,negated_conjecture,
% 7.27/1.32      k2_tarski(sK2,sK2) = k6_domain_1(u1_struct_0(sK0),sK2)).
% 7.27/1.32  
% 7.27/1.32  cnf(u63,negated_conjecture,
% 7.27/1.32      k2_tarski(sK1,sK1) = k6_domain_1(u1_struct_0(sK0),sK1)).
% 7.27/1.32  
% 7.27/1.32  cnf(u4615,axiom,
% 7.27/1.32      X2 != X3 | sK3(sK3(X0,X1,k2_tarski(X2,X3)),sK3(X4,X5,k2_tarski(X2,X3)),k2_tarski(X2,X3)) = X2 | k2_tarski(X2,X3) = k2_tarski(sK3(X0,X1,k2_tarski(X2,X3)),sK3(X4,X5,k2_tarski(X2,X3))) | sK3(X0,X1,k2_tarski(X2,X3)) = X1 | sK3(X0,X1,k2_tarski(X2,X3)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X3) | sK3(X4,X5,k2_tarski(X2,X3)) = X5 | sK3(X4,X5,k2_tarski(X2,X3)) = X4 | k2_tarski(X2,X3) = k2_tarski(X4,X5)).
% 7.27/1.32  
% 7.27/1.32  cnf(u4614,axiom,
% 7.27/1.32      X2 != X3 | sK3(sK3(X0,X1,k2_tarski(X2,X3)),sK3(X4,X5,k2_tarski(X2,X3)),k2_tarski(X2,X3)) = X3 | k2_tarski(X2,X3) = k2_tarski(sK3(X0,X1,k2_tarski(X2,X3)),sK3(X4,X5,k2_tarski(X2,X3))) | sK3(X0,X1,k2_tarski(X2,X3)) = X1 | sK3(X0,X1,k2_tarski(X2,X3)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X3) | sK3(X4,X5,k2_tarski(X2,X3)) = X5 | sK3(X4,X5,k2_tarski(X2,X3)) = X4 | k2_tarski(X2,X3) = k2_tarski(X4,X5)).
% 7.27/1.32  
% 7.27/1.32  cnf(u4142,axiom,
% 7.27/1.32      X2 != X3 | sK3(sK3(X0,X1,k2_tarski(X2,X3)),sK3(X0,X1,k2_tarski(X2,X3)),k2_tarski(X2,X3)) = X2 | k2_tarski(X2,X3) = k2_tarski(sK3(X0,X1,k2_tarski(X2,X3)),sK3(X0,X1,k2_tarski(X2,X3))) | sK3(X0,X1,k2_tarski(X2,X3)) = X1 | sK3(X0,X1,k2_tarski(X2,X3)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 7.27/1.32  
% 7.27/1.32  cnf(u4141,axiom,
% 7.27/1.32      X2 != X3 | sK3(sK3(X0,X1,k2_tarski(X2,X3)),sK3(X0,X1,k2_tarski(X2,X3)),k2_tarski(X2,X3)) = X3 | k2_tarski(X2,X3) = k2_tarski(sK3(X0,X1,k2_tarski(X2,X3)),sK3(X0,X1,k2_tarski(X2,X3))) | sK3(X0,X1,k2_tarski(X2,X3)) = X1 | sK3(X0,X1,k2_tarski(X2,X3)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 7.27/1.32  
% 7.27/1.32  cnf(u3665,axiom,
% 7.27/1.32      X0 != X3 | sK3(X0,sK3(X1,X2,k2_tarski(X3,X3)),k2_tarski(X3,X3)) = X0 | k2_tarski(X3,X3) = k2_tarski(X0,sK3(X1,X2,k2_tarski(X3,X3))) | sK3(X1,X2,k2_tarski(X3,X3)) = X2 | sK3(X1,X2,k2_tarski(X3,X3)) = X1 | k2_tarski(X1,X2) = k2_tarski(X3,X3)).
% 7.27/1.32  
% 7.27/1.32  cnf(u3664,axiom,
% 7.27/1.32      X0 != X3 | sK3(X0,sK3(X1,X2,k2_tarski(X3,X3)),k2_tarski(X3,X3)) = X3 | k2_tarski(X3,X3) = k2_tarski(X0,sK3(X1,X2,k2_tarski(X3,X3))) | sK3(X1,X2,k2_tarski(X3,X3)) = X2 | sK3(X1,X2,k2_tarski(X3,X3)) = X1 | k2_tarski(X1,X2) = k2_tarski(X3,X3)).
% 7.27/1.32  
% 7.27/1.32  cnf(u3384,axiom,
% 7.27/1.32      X2 != X3 | sK3(sK3(X0,X1,k2_tarski(X2,X2)),X3,k2_tarski(X2,X2)) = X3 | k2_tarski(X2,X2) = k2_tarski(sK3(X0,X1,k2_tarski(X2,X2)),X3) | sK3(X0,X1,k2_tarski(X2,X2)) = X1 | sK3(X0,X1,k2_tarski(X2,X2)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 7.27/1.32  
% 7.27/1.32  cnf(u3383,axiom,
% 7.27/1.32      X2 != X3 | sK3(sK3(X0,X1,k2_tarski(X2,X2)),X3,k2_tarski(X2,X2)) = X2 | k2_tarski(X2,X2) = k2_tarski(sK3(X0,X1,k2_tarski(X2,X2)),X3) | sK3(X0,X1,k2_tarski(X2,X2)) = X1 | sK3(X0,X1,k2_tarski(X2,X2)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 7.27/1.32  
% 7.27/1.32  cnf(u2884,axiom,
% 7.27/1.32      X138 != X139 | k2_tarski(X138,X139) = k2_tarski(X139,sK3(X136,X137,k2_tarski(X138,X139))) | ~r2_hidden(X139,k2_tarski(X138,X139)) | sK3(X136,X137,k2_tarski(X138,X139)) = X137 | sK3(X136,X137,k2_tarski(X138,X139)) = X136 | k2_tarski(X138,X139) = k2_tarski(X136,X137)).
% 7.27/1.32  
% 7.27/1.32  cnf(u2630,axiom,
% 7.27/1.32      X127 != X128 | k2_tarski(X127,X128) = k2_tarski(X127,sK3(X125,X126,k2_tarski(X127,X128))) | ~r2_hidden(X127,k2_tarski(X127,X128)) | sK3(X125,X126,k2_tarski(X127,X128)) = X126 | sK3(X125,X126,k2_tarski(X127,X128)) = X125 | k2_tarski(X125,X126) = k2_tarski(X127,X128)).
% 7.27/1.32  
% 7.27/1.32  cnf(u2331,axiom,
% 7.27/1.32      X99 != X100 | k2_tarski(X99,X100) = k2_tarski(X101,X99) | ~r2_hidden(X99,k2_tarski(X101,X99)) | sK3(X99,X100,k2_tarski(X101,X99)) = X101).
% 7.27/1.32  
% 7.27/1.32  cnf(u2316,axiom,
% 7.27/1.32      X99 != X101 | k2_tarski(X99,X100) = k2_tarski(X101,X99) | ~r2_hidden(X99,k2_tarski(X101,X99)) | sK3(X99,X100,k2_tarski(X101,X99)) = X100).
% 7.27/1.32  
% 7.27/1.32  cnf(u2314,axiom,
% 7.27/1.32      X1 != X2 | sK3(X0,X1,k2_tarski(X2,X0)) = X1 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 7.27/1.32  
% 7.27/1.32  cnf(u2313,axiom,
% 7.27/1.32      X1 != X2 | sK3(X0,X1,k2_tarski(X2,X0)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 7.27/1.32  
% 7.27/1.32  cnf(u2174,axiom,
% 7.27/1.32      X92 != X93 | k2_tarski(X92,X93) = k2_tarski(X92,X94) | ~r2_hidden(X92,k2_tarski(X92,X94)) | sK3(X92,X93,k2_tarski(X92,X94)) = X94).
% 7.27/1.32  
% 7.27/1.32  cnf(u2159,axiom,
% 7.27/1.32      X92 != X94 | k2_tarski(X92,X93) = k2_tarski(X92,X94) | ~r2_hidden(X92,k2_tarski(X92,X94)) | sK3(X92,X93,k2_tarski(X92,X94)) = X93).
% 7.27/1.32  
% 7.27/1.32  cnf(u2157,axiom,
% 7.27/1.32      X1 != X2 | sK3(X0,X1,k2_tarski(X0,X2)) = X1 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 7.27/1.32  
% 7.27/1.32  cnf(u2156,axiom,
% 7.27/1.32      X1 != X2 | sK3(X0,X1,k2_tarski(X0,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 7.27/1.32  
% 7.27/1.32  cnf(u2030,axiom,
% 7.27/1.32      X91 != X92 | k2_tarski(X93,X92) = k2_tarski(X91,X92) | ~r2_hidden(X92,k2_tarski(X93,X92)) | sK3(X91,X92,k2_tarski(X93,X92)) = X93).
% 7.27/1.32  
% 7.27/1.32  cnf(u2016,axiom,
% 7.27/1.32      X92 != X93 | k2_tarski(X93,X92) = k2_tarski(X91,X92) | ~r2_hidden(X92,k2_tarski(X93,X92)) | sK3(X91,X92,k2_tarski(X93,X92)) = X91).
% 7.27/1.32  
% 7.27/1.32  cnf(u2015,axiom,
% 7.27/1.32      X0 != X2 | sK3(X0,X1,k2_tarski(X2,X1)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 7.27/1.32  
% 7.27/1.32  cnf(u2014,axiom,
% 7.27/1.32      X0 != X2 | sK3(X0,X1,k2_tarski(X2,X1)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 7.27/1.32  
% 7.27/1.32  cnf(u1870,axiom,
% 7.27/1.32      X90 != X91 | k2_tarski(X90,X91) = k2_tarski(X91,X92) | ~r2_hidden(X91,k2_tarski(X91,X92)) | sK3(X90,X91,k2_tarski(X91,X92)) = X92).
% 7.27/1.32  
% 7.27/1.32  cnf(u1856,axiom,
% 7.27/1.32      X91 != X92 | k2_tarski(X90,X91) = k2_tarski(X91,X92) | ~r2_hidden(X91,k2_tarski(X91,X92)) | sK3(X90,X91,k2_tarski(X91,X92)) = X90).
% 7.27/1.32  
% 7.27/1.32  cnf(u1855,axiom,
% 7.27/1.32      X0 != X2 | sK3(X0,X1,k2_tarski(X1,X2)) = X0 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 7.27/1.32  
% 7.27/1.32  cnf(u1854,axiom,
% 7.27/1.32      X0 != X2 | sK3(X0,X1,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 7.27/1.32  
% 7.27/1.32  cnf(u1716,axiom,
% 7.27/1.32      X62 != X63 | k2_tarski(X62,X62) = k2_tarski(X62,X63) | ~r2_hidden(X62,k2_tarski(X62,X62))).
% 7.27/1.32  
% 7.27/1.32  cnf(u1659,axiom,
% 7.27/1.32      X0 != X1 | sK3(X0,X1,k2_tarski(X0,X0)) = X1 | k2_tarski(X0,X1) = k2_tarski(X0,X0)).
% 7.27/1.32  
% 7.27/1.32  cnf(u1658,axiom,
% 7.27/1.32      X0 != X1 | sK3(X0,X1,k2_tarski(X0,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X0,X0)).
% 7.27/1.32  
% 7.27/1.32  cnf(u1587,axiom,
% 7.27/1.32      X61 != X62 | k2_tarski(X62,X62) = k2_tarski(X61,X62) | ~r2_hidden(X62,k2_tarski(X62,X62))).
% 7.27/1.32  
% 7.27/1.32  cnf(u1455,axiom,
% 7.27/1.32      X3 != X4 | sK3(X0,sK3(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X0 | sK3(X0,sK3(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X3 | k2_tarski(X3,X4) = k2_tarski(X0,sK3(X1,X2,k2_tarski(X3,X4))) | sK3(X1,X2,k2_tarski(X3,X4)) = X2 | sK3(X1,X2,k2_tarski(X3,X4)) = X1 | k2_tarski(X1,X2) = k2_tarski(X3,X4)).
% 7.27/1.32  
% 7.27/1.32  cnf(u1454,axiom,
% 7.27/1.32      X0 != X4 | sK3(X0,sK3(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X0 | sK3(X0,sK3(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X3 | k2_tarski(X3,X4) = k2_tarski(X0,sK3(X1,X2,k2_tarski(X3,X4))) | sK3(X1,X2,k2_tarski(X3,X4)) = X2 | sK3(X1,X2,k2_tarski(X3,X4)) = X1 | k2_tarski(X1,X2) = k2_tarski(X3,X4)).
% 7.27/1.32  
% 7.27/1.32  cnf(u1453,axiom,
% 7.27/1.32      X3 != X4 | sK3(X0,sK3(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X0 | sK3(X0,sK3(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X4 | k2_tarski(X3,X4) = k2_tarski(X0,sK3(X1,X2,k2_tarski(X3,X4))) | sK3(X1,X2,k2_tarski(X3,X4)) = X2 | sK3(X1,X2,k2_tarski(X3,X4)) = X1 | k2_tarski(X1,X2) = k2_tarski(X3,X4)).
% 7.27/1.32  
% 7.27/1.32  cnf(u1452,axiom,
% 7.27/1.32      X0 != X3 | sK3(X0,sK3(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X0 | sK3(X0,sK3(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X4 | k2_tarski(X3,X4) = k2_tarski(X0,sK3(X1,X2,k2_tarski(X3,X4))) | sK3(X1,X2,k2_tarski(X3,X4)) = X2 | sK3(X1,X2,k2_tarski(X3,X4)) = X1 | k2_tarski(X1,X2) = k2_tarski(X3,X4)).
% 7.27/1.32  
% 7.27/1.32  cnf(u1451,axiom,
% 7.27/1.32      X0 != X4 | sK3(X0,sK3(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X3 | sK3(X0,sK3(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X4 | k2_tarski(X3,X4) = k2_tarski(X0,sK3(X1,X2,k2_tarski(X3,X4))) | sK3(X1,X2,k2_tarski(X3,X4)) = X2 | sK3(X1,X2,k2_tarski(X3,X4)) = X1 | k2_tarski(X1,X2) = k2_tarski(X3,X4)).
% 7.27/1.32  
% 7.27/1.32  cnf(u1450,axiom,
% 7.27/1.32      X0 != X3 | sK3(X0,sK3(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X3 | sK3(X0,sK3(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X4 | k2_tarski(X3,X4) = k2_tarski(X0,sK3(X1,X2,k2_tarski(X3,X4))) | sK3(X1,X2,k2_tarski(X3,X4)) = X2 | sK3(X1,X2,k2_tarski(X3,X4)) = X1 | k2_tarski(X1,X2) = k2_tarski(X3,X4)).
% 7.27/1.32  
% 7.27/1.32  cnf(u1135,axiom,
% 7.27/1.32      X2 != X3 | sK3(sK3(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X4 | sK3(sK3(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X2 | k2_tarski(X2,X3) = k2_tarski(sK3(X0,X1,k2_tarski(X2,X3)),X4) | sK3(X0,X1,k2_tarski(X2,X3)) = X1 | sK3(X0,X1,k2_tarski(X2,X3)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 7.27/1.32  
% 7.27/1.32  cnf(u1134,axiom,
% 7.27/1.32      X3 != X4 | sK3(sK3(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X4 | sK3(sK3(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X2 | k2_tarski(X2,X3) = k2_tarski(sK3(X0,X1,k2_tarski(X2,X3)),X4) | sK3(X0,X1,k2_tarski(X2,X3)) = X1 | sK3(X0,X1,k2_tarski(X2,X3)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 7.27/1.32  
% 7.27/1.32  cnf(u1133,axiom,
% 7.27/1.32      X2 != X3 | sK3(sK3(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X4 | sK3(sK3(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X3 | k2_tarski(X2,X3) = k2_tarski(sK3(X0,X1,k2_tarski(X2,X3)),X4) | sK3(X0,X1,k2_tarski(X2,X3)) = X1 | sK3(X0,X1,k2_tarski(X2,X3)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 7.27/1.32  
% 7.27/1.32  cnf(u1132,axiom,
% 7.27/1.32      X2 != X4 | sK3(sK3(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X4 | sK3(sK3(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X3 | k2_tarski(X2,X3) = k2_tarski(sK3(X0,X1,k2_tarski(X2,X3)),X4) | sK3(X0,X1,k2_tarski(X2,X3)) = X1 | sK3(X0,X1,k2_tarski(X2,X3)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 7.27/1.32  
% 7.27/1.32  cnf(u1131,axiom,
% 7.27/1.32      X3 != X4 | sK3(sK3(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X2 | sK3(sK3(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X3 | k2_tarski(X2,X3) = k2_tarski(sK3(X0,X1,k2_tarski(X2,X3)),X4) | sK3(X0,X1,k2_tarski(X2,X3)) = X1 | sK3(X0,X1,k2_tarski(X2,X3)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 7.27/1.32  
% 7.27/1.32  cnf(u1130,axiom,
% 7.27/1.32      X2 != X4 | sK3(sK3(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X2 | sK3(sK3(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X3 | k2_tarski(X2,X3) = k2_tarski(sK3(X0,X1,k2_tarski(X2,X3)),X4) | sK3(X0,X1,k2_tarski(X2,X3)) = X1 | sK3(X0,X1,k2_tarski(X2,X3)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 7.27/1.32  
% 7.27/1.32  cnf(u910,axiom,
% 7.27/1.32      X0 != X1 | sK3(X0,X1,k2_tarski(X1,X1)) = X0 | k2_tarski(X0,X1) = k2_tarski(X1,X1)).
% 7.27/1.32  
% 7.27/1.32  cnf(u909,axiom,
% 7.27/1.32      X0 != X1 | sK3(X0,X1,k2_tarski(X1,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X1,X1)).
% 7.27/1.32  
% 7.27/1.32  cnf(u764,axiom,
% 7.27/1.32      X0 != X2 | sK3(X0,X1,k2_tarski(X2,X2)) = X1 | sK3(X0,X1,k2_tarski(X2,X2)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 7.27/1.32  
% 7.27/1.32  cnf(u763,axiom,
% 7.27/1.32      X1 != X2 | sK3(X0,X1,k2_tarski(X2,X2)) = X1 | sK3(X0,X1,k2_tarski(X2,X2)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 7.27/1.32  
% 7.27/1.32  cnf(u762,axiom,
% 7.27/1.32      X0 != X2 | sK3(X0,X1,k2_tarski(X2,X2)) = X1 | sK3(X0,X1,k2_tarski(X2,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 7.27/1.32  
% 7.27/1.32  cnf(u761,axiom,
% 7.27/1.32      X0 != X1 | sK3(X0,X1,k2_tarski(X2,X2)) = X1 | sK3(X0,X1,k2_tarski(X2,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 7.27/1.32  
% 7.27/1.32  cnf(u760,axiom,
% 7.27/1.32      X1 != X2 | sK3(X0,X1,k2_tarski(X2,X2)) = X0 | sK3(X0,X1,k2_tarski(X2,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 7.27/1.32  
% 7.27/1.32  cnf(u759,axiom,
% 7.27/1.32      X0 != X1 | sK3(X0,X1,k2_tarski(X2,X2)) = X0 | sK3(X0,X1,k2_tarski(X2,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 7.27/1.32  
% 7.27/1.32  cnf(u672,axiom,
% 7.27/1.32      X0 != X1 | sK3(X0,X1,k2_tarski(X1,X0)) = X1 | k2_tarski(X0,X1) = k2_tarski(X1,X0)).
% 7.27/1.32  
% 7.27/1.32  cnf(u671,axiom,
% 7.27/1.32      X0 != X1 | sK3(X0,X1,k2_tarski(X1,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X1,X0)).
% 7.27/1.32  
% 7.27/1.32  cnf(u630,axiom,
% 7.27/1.32      X0 != X2 | sK3(X0,X1,k2_tarski(X2,X0)) = X1 | sK3(X0,X1,k2_tarski(X2,X0)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 7.27/1.32  
% 7.27/1.32  cnf(u629,axiom,
% 7.27/1.32      X0 != X1 | sK3(X0,X1,k2_tarski(X2,X0)) = X1 | sK3(X0,X1,k2_tarski(X2,X0)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 7.27/1.32  
% 7.27/1.32  cnf(u628,axiom,
% 7.27/1.32      X0 != X2 | sK3(X0,X1,k2_tarski(X2,X0)) = X1 | sK3(X0,X1,k2_tarski(X2,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 7.27/1.32  
% 7.27/1.32  cnf(u627,axiom,
% 7.27/1.32      X1 != X2 | sK3(X0,X1,k2_tarski(X2,X0)) = X1 | sK3(X0,X1,k2_tarski(X2,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 7.27/1.32  
% 7.27/1.32  cnf(u626,axiom,
% 7.27/1.32      X0 != X1 | sK3(X0,X1,k2_tarski(X2,X0)) = X2 | sK3(X0,X1,k2_tarski(X2,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 7.27/1.32  
% 7.27/1.32  cnf(u625,axiom,
% 7.27/1.32      X1 != X2 | sK3(X0,X1,k2_tarski(X2,X0)) = X2 | sK3(X0,X1,k2_tarski(X2,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 7.27/1.32  
% 7.27/1.32  cnf(u539,axiom,
% 7.27/1.32      X0 != X2 | sK3(X0,X1,k2_tarski(X0,X2)) = X1 | sK3(X0,X1,k2_tarski(X0,X2)) = X0 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 7.27/1.32  
% 7.27/1.32  cnf(u538,axiom,
% 7.27/1.32      X1 != X2 | sK3(X0,X1,k2_tarski(X0,X2)) = X1 | sK3(X0,X1,k2_tarski(X0,X2)) = X0 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 7.27/1.32  
% 7.27/1.32  cnf(u537,axiom,
% 7.27/1.32      X0 != X2 | sK3(X0,X1,k2_tarski(X0,X2)) = X1 | sK3(X0,X1,k2_tarski(X0,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 7.27/1.32  
% 7.27/1.32  cnf(u536,axiom,
% 7.27/1.32      X0 != X1 | sK3(X0,X1,k2_tarski(X0,X2)) = X1 | sK3(X0,X1,k2_tarski(X0,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 7.27/1.32  
% 7.27/1.32  cnf(u535,axiom,
% 7.27/1.32      X1 != X2 | sK3(X0,X1,k2_tarski(X0,X2)) = X0 | sK3(X0,X1,k2_tarski(X0,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 7.27/1.32  
% 7.27/1.32  cnf(u534,axiom,
% 7.27/1.32      X0 != X1 | sK3(X0,X1,k2_tarski(X0,X2)) = X0 | sK3(X0,X1,k2_tarski(X0,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 7.27/1.32  
% 7.27/1.32  cnf(u457,axiom,
% 7.27/1.32      X1 != X2 | sK3(X0,X1,k2_tarski(X2,X1)) = X0 | sK3(X0,X1,k2_tarski(X2,X1)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 7.27/1.32  
% 7.27/1.32  cnf(u456,axiom,
% 7.27/1.32      X0 != X1 | sK3(X0,X1,k2_tarski(X2,X1)) = X0 | sK3(X0,X1,k2_tarski(X2,X1)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 7.27/1.32  
% 7.27/1.32  cnf(u455,axiom,
% 7.27/1.32      X1 != X2 | sK3(X0,X1,k2_tarski(X2,X1)) = X0 | sK3(X0,X1,k2_tarski(X2,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 7.27/1.32  
% 7.27/1.32  cnf(u454,axiom,
% 7.27/1.32      X0 != X2 | sK3(X0,X1,k2_tarski(X2,X1)) = X0 | sK3(X0,X1,k2_tarski(X2,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 7.27/1.32  
% 7.27/1.32  cnf(u453,axiom,
% 7.27/1.32      X0 != X1 | sK3(X0,X1,k2_tarski(X2,X1)) = X2 | sK3(X0,X1,k2_tarski(X2,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 7.27/1.32  
% 7.27/1.32  cnf(u452,axiom,
% 7.27/1.32      X0 != X2 | sK3(X0,X1,k2_tarski(X2,X1)) = X2 | sK3(X0,X1,k2_tarski(X2,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 7.27/1.32  
% 7.27/1.32  cnf(u385,axiom,
% 7.27/1.32      X1 != X2 | sK3(X0,X1,k2_tarski(X1,X2)) = X0 | sK3(X0,X1,k2_tarski(X1,X2)) = X1 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 7.27/1.32  
% 7.27/1.32  cnf(u384,axiom,
% 7.27/1.32      X0 != X2 | sK3(X0,X1,k2_tarski(X1,X2)) = X0 | sK3(X0,X1,k2_tarski(X1,X2)) = X1 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 7.27/1.32  
% 7.27/1.32  cnf(u383,axiom,
% 7.27/1.32      X1 != X2 | sK3(X0,X1,k2_tarski(X1,X2)) = X0 | sK3(X0,X1,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 7.27/1.32  
% 7.27/1.32  cnf(u382,axiom,
% 7.27/1.32      X0 != X1 | sK3(X0,X1,k2_tarski(X1,X2)) = X0 | sK3(X0,X1,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 7.27/1.32  
% 7.27/1.32  cnf(u381,axiom,
% 7.27/1.32      X0 != X2 | sK3(X0,X1,k2_tarski(X1,X2)) = X1 | sK3(X0,X1,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 7.27/1.32  
% 7.27/1.32  cnf(u380,axiom,
% 7.27/1.32      X0 != X1 | sK3(X0,X1,k2_tarski(X1,X2)) = X1 | sK3(X0,X1,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 7.27/1.32  
% 7.27/1.32  cnf(u318,axiom,
% 7.27/1.32      X0 != X1 | sK3(X0,X0,k2_tarski(X1,X1)) = X0 | k2_tarski(X0,X0) = k2_tarski(X1,X1)).
% 7.27/1.32  
% 7.27/1.32  cnf(u317,axiom,
% 7.27/1.32      X0 != X1 | sK3(X0,X0,k2_tarski(X1,X1)) = X1 | k2_tarski(X0,X0) = k2_tarski(X1,X1)).
% 7.27/1.32  
% 7.27/1.32  cnf(u285,axiom,
% 7.27/1.32      X12 != X13 | k2_tarski(X12,X12) = k2_tarski(X13,X12) | ~r2_hidden(X12,k2_tarski(X13,X12))).
% 7.27/1.32  
% 7.27/1.32  cnf(u253,axiom,
% 7.27/1.32      X0 != X1 | sK3(X0,X0,k2_tarski(X1,X0)) = X1 | k2_tarski(X0,X0) = k2_tarski(X1,X0)).
% 7.27/1.32  
% 7.27/1.32  cnf(u252,axiom,
% 7.27/1.32      X0 != X1 | sK3(X0,X0,k2_tarski(X1,X0)) = X0 | k2_tarski(X0,X0) = k2_tarski(X1,X0)).
% 7.27/1.32  
% 7.27/1.32  cnf(u220,axiom,
% 7.27/1.32      X12 != X13 | k2_tarski(X12,X12) = k2_tarski(X12,X13) | ~r2_hidden(X12,k2_tarski(X12,X13))).
% 7.27/1.32  
% 7.27/1.32  cnf(u190,axiom,
% 7.27/1.32      X0 != X1 | sK3(X0,X0,k2_tarski(X0,X1)) = X0 | k2_tarski(X0,X1) = k2_tarski(X0,X0)).
% 7.27/1.32  
% 7.27/1.32  cnf(u189,axiom,
% 7.27/1.32      X0 != X1 | sK3(X0,X0,k2_tarski(X0,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X0,X0)).
% 7.27/1.32  
% 7.27/1.32  cnf(u154,axiom,
% 7.27/1.32      X1 != X2 | sK3(X0,X0,k2_tarski(X1,X2)) = X0 | sK3(X0,X0,k2_tarski(X1,X2)) = X1 | k2_tarski(X0,X0) = k2_tarski(X1,X2)).
% 7.27/1.32  
% 7.27/1.32  cnf(u153,axiom,
% 7.27/1.32      X0 != X2 | sK3(X0,X0,k2_tarski(X1,X2)) = X0 | sK3(X0,X0,k2_tarski(X1,X2)) = X1 | k2_tarski(X0,X0) = k2_tarski(X1,X2)).
% 7.27/1.32  
% 7.27/1.32  cnf(u152,axiom,
% 7.27/1.32      X1 != X2 | sK3(X0,X0,k2_tarski(X1,X2)) = X0 | sK3(X0,X0,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X0) = k2_tarski(X1,X2)).
% 7.27/1.32  
% 7.27/1.32  cnf(u151,axiom,
% 7.27/1.32      X0 != X1 | sK3(X0,X0,k2_tarski(X1,X2)) = X0 | sK3(X0,X0,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X0) = k2_tarski(X1,X2)).
% 7.27/1.32  
% 7.27/1.32  cnf(u150,axiom,
% 7.27/1.32      X0 != X2 | sK3(X0,X0,k2_tarski(X1,X2)) = X1 | sK3(X0,X0,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X0) = k2_tarski(X1,X2)).
% 7.27/1.32  
% 7.27/1.32  cnf(u149,axiom,
% 7.27/1.32      X0 != X1 | sK3(X0,X0,k2_tarski(X1,X2)) = X1 | sK3(X0,X0,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X0) = k2_tarski(X1,X2)).
% 7.27/1.32  
% 7.27/1.32  cnf(u102,axiom,
% 7.27/1.32      X2 != X3 | sK3(X0,X1,k2_tarski(X2,X3)) = X1 | sK3(X0,X1,k2_tarski(X2,X3)) = X0 | sK3(X0,X1,k2_tarski(X2,X3)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 7.27/1.32  
% 7.27/1.32  cnf(u101,axiom,
% 7.27/1.32      X0 != X3 | sK3(X0,X1,k2_tarski(X2,X3)) = X1 | sK3(X0,X1,k2_tarski(X2,X3)) = X0 | sK3(X0,X1,k2_tarski(X2,X3)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 7.27/1.32  
% 7.27/1.32  cnf(u100,axiom,
% 7.27/1.32      X1 != X3 | sK3(X0,X1,k2_tarski(X2,X3)) = X1 | sK3(X0,X1,k2_tarski(X2,X3)) = X0 | sK3(X0,X1,k2_tarski(X2,X3)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 7.27/1.32  
% 7.27/1.32  cnf(u99,axiom,
% 7.27/1.32      X2 != X3 | sK3(X0,X1,k2_tarski(X2,X3)) = X1 | sK3(X0,X1,k2_tarski(X2,X3)) = X0 | sK3(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 7.27/1.32  
% 7.27/1.32  cnf(u98,axiom,
% 7.27/1.32      X0 != X2 | sK3(X0,X1,k2_tarski(X2,X3)) = X1 | sK3(X0,X1,k2_tarski(X2,X3)) = X0 | sK3(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 7.27/1.32  
% 7.27/1.32  cnf(u97,axiom,
% 7.27/1.32      X1 != X2 | sK3(X0,X1,k2_tarski(X2,X3)) = X1 | sK3(X0,X1,k2_tarski(X2,X3)) = X0 | sK3(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 7.27/1.32  
% 7.27/1.32  cnf(u96,axiom,
% 7.27/1.32      X0 != X3 | sK3(X0,X1,k2_tarski(X2,X3)) = X1 | sK3(X0,X1,k2_tarski(X2,X3)) = X2 | sK3(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 7.27/1.32  
% 7.27/1.32  cnf(u95,axiom,
% 7.27/1.32      X0 != X2 | sK3(X0,X1,k2_tarski(X2,X3)) = X1 | sK3(X0,X1,k2_tarski(X2,X3)) = X2 | sK3(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 7.27/1.32  
% 7.27/1.32  cnf(u94,axiom,
% 7.27/1.32      X0 != X1 | sK3(X0,X1,k2_tarski(X2,X3)) = X1 | sK3(X0,X1,k2_tarski(X2,X3)) = X2 | sK3(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 7.27/1.32  
% 7.27/1.32  cnf(u93,axiom,
% 7.27/1.32      X1 != X3 | sK3(X0,X1,k2_tarski(X2,X3)) = X0 | sK3(X0,X1,k2_tarski(X2,X3)) = X2 | sK3(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 7.27/1.32  
% 7.27/1.32  cnf(u92,axiom,
% 7.27/1.32      X1 != X2 | sK3(X0,X1,k2_tarski(X2,X3)) = X0 | sK3(X0,X1,k2_tarski(X2,X3)) = X2 | sK3(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 7.27/1.32  
% 7.27/1.32  cnf(u91,axiom,
% 7.27/1.32      X0 != X1 | sK3(X0,X1,k2_tarski(X2,X3)) = X0 | sK3(X0,X1,k2_tarski(X2,X3)) = X2 | sK3(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 7.27/1.32  
% 7.27/1.32  cnf(u3399,axiom,
% 7.27/1.32      sK3(X150,X151,k2_tarski(X152,X152)) != X153 | k2_tarski(X152,X152) = k2_tarski(sK3(X150,X151,k2_tarski(X152,X152)),X153) | ~r2_hidden(sK3(X150,X151,k2_tarski(X152,X152)),k2_tarski(X152,X152)) | sK3(sK3(X150,X151,k2_tarski(X152,X152)),X153,k2_tarski(X152,X152)) = X152 | sK3(X150,X151,k2_tarski(X152,X152)) = X151 | sK3(X150,X151,k2_tarski(X152,X152)) = X150 | k2_tarski(X150,X151) = k2_tarski(X152,X152)).
% 7.27/1.32  
% 7.27/1.32  cnf(u3683,axiom,
% 7.27/1.32      sK3(X162,X163,k2_tarski(X164,X164)) != X161 | k2_tarski(X164,X164) = k2_tarski(X161,sK3(X162,X163,k2_tarski(X164,X164))) | ~r2_hidden(sK3(X162,X163,k2_tarski(X164,X164)),k2_tarski(X164,X164)) | sK3(X161,sK3(X162,X163,k2_tarski(X164,X164)),k2_tarski(X164,X164)) = X164 | sK3(X162,X163,k2_tarski(X164,X164)) = X163 | sK3(X162,X163,k2_tarski(X164,X164)) = X162 | k2_tarski(X162,X163) = k2_tarski(X164,X164)).
% 7.27/1.32  
% 7.27/1.32  cnf(u1144,axiom,
% 7.27/1.32      sK3(X67,X68,k2_tarski(X69,X70)) != X71 | k2_tarski(X69,X70) = k2_tarski(sK3(X67,X68,k2_tarski(X69,X70)),X71) | ~r2_hidden(sK3(X67,X68,k2_tarski(X69,X70)),k2_tarski(X69,X70)) | sK3(sK3(X67,X68,k2_tarski(X69,X70)),X71,k2_tarski(X69,X70)) = X69 | sK3(sK3(X67,X68,k2_tarski(X69,X70)),X71,k2_tarski(X69,X70)) = X70 | sK3(X67,X68,k2_tarski(X69,X70)) = X68 | sK3(X67,X68,k2_tarski(X69,X70)) = X67 | k2_tarski(X67,X68) = k2_tarski(X69,X70)).
% 7.27/1.32  
% 7.27/1.32  cnf(u1471,axiom,
% 7.27/1.32      sK3(X85,X86,k2_tarski(X87,X88)) != X84 | k2_tarski(X87,X88) = k2_tarski(X84,sK3(X85,X86,k2_tarski(X87,X88))) | ~r2_hidden(sK3(X85,X86,k2_tarski(X87,X88)),k2_tarski(X87,X88)) | sK3(X84,sK3(X85,X86,k2_tarski(X87,X88)),k2_tarski(X87,X88)) = X87 | sK3(X84,sK3(X85,X86,k2_tarski(X87,X88)),k2_tarski(X87,X88)) = X88 | sK3(X85,X86,k2_tarski(X87,X88)) = X86 | sK3(X85,X86,k2_tarski(X87,X88)) = X85 | k2_tarski(X85,X86) = k2_tarski(X87,X88)).
% 7.27/1.32  
% 7.27/1.32  cnf(u53,axiom,
% 7.27/1.32      sK3(X0,X1,X2) != X0 | k2_tarski(X0,X1) = X2 | ~r2_hidden(X0,X2)).
% 7.27/1.32  
% 7.27/1.32  cnf(u52,axiom,
% 7.27/1.32      sK3(X0,X1,X2) != X1 | k2_tarski(X0,X1) = X2 | ~r2_hidden(X1,X2)).
% 7.27/1.32  
% 7.27/1.32  % (4909)# SZS output end Saturation.
% 7.27/1.32  % (4909)------------------------------
% 7.27/1.32  % (4909)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.27/1.32  % (4909)Termination reason: Satisfiable
% 7.27/1.32  
% 7.27/1.32  % (4909)Memory used [KB]: 4605
% 7.27/1.32  % (4909)Time elapsed: 0.871 s
% 7.27/1.32  % (4909)------------------------------
% 7.27/1.32  % (4909)------------------------------
% 7.27/1.32  % (4903)Success in time 0.945 s
%------------------------------------------------------------------------------
