%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:55 EST 2020

% Result     : CounterSatisfiable 6.44s
% Output     : Saturation 6.44s
% Verified   : 
% Statistics : Number of clauses        :  230 ( 230 expanded)
%              Number of leaves         :  230 ( 230 expanded)
%              Depth                    :    0
%              Number of atoms          :  978 ( 978 expanded)
%              Number of equality atoms :  881 ( 881 expanded)
%              Maximal clause size      :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u63,negated_conjecture,
    ( ~ v2_waybel_0(k2_tarski(sK1,sK1),sK0)
    | ~ v1_waybel_0(k2_tarski(sK1,sK1),sK0) )).

cnf(u64,negated_conjecture,
    ( v6_orders_2(k2_tarski(sK1,sK1),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) )).

cnf(u35,axiom,
    ( v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u39,axiom,
    ( r1_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u30,negated_conjecture,
    ( v3_orders_2(sK0) )).

cnf(u65,negated_conjecture,
    ( m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) )).

cnf(u36,axiom,
    ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u32,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

cnf(u58,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k2_tarski(X0,X0) = k6_domain_1(u1_struct_0(sK0),X0)
    | ~ l1_struct_0(sK0) )).

cnf(u31,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u47,axiom,
    ( v1_xboole_0(X0)
    | ~ m1_subset_1(X1,X0)
    | k6_domain_1(X0,X1) = k2_tarski(X1,X1) )).

cnf(u55,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(sK0) )).

cnf(u38,axiom,
    ( l1_struct_0(X0)
    | ~ l1_orders_2(X0) )).

cnf(u37,axiom,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) )).

cnf(u29,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u43,axiom,
    ( r2_hidden(sK2(X0,X1,X2),X2)
    | sK2(X0,X1,X2) = X1
    | sK2(X0,X1,X2) = X0
    | k2_tarski(X0,X1) = X2 )).

cnf(u51,axiom,
    ( r2_hidden(X4,k2_tarski(X4,X1)) )).

cnf(u49,axiom,
    ( r2_hidden(X4,k2_tarski(X0,X4)) )).

cnf(u911,axiom,
    ( ~ r2_hidden(X40,k2_tarski(X40,X40))
    | k2_tarski(X40,X40) = k2_tarski(X39,X40)
    | sK2(X39,X40,k2_tarski(X40,X40)) = X39 )).

cnf(u1661,axiom,
    ( ~ r2_hidden(X58,k2_tarski(X58,X58))
    | k2_tarski(X58,X59) = k2_tarski(X58,X58)
    | sK2(X58,X59,k2_tarski(X58,X58)) = X59 )).

cnf(u193,axiom,
    ( ~ r2_hidden(X12,k2_tarski(X12,X13))
    | k2_tarski(X12,X12) = k2_tarski(X12,X13)
    | sK2(X12,X12,k2_tarski(X12,X13)) = X13 )).

cnf(u792,axiom,
    ( ~ r2_hidden(X38,k2_tarski(X38,X37))
    | k2_tarski(X38,X37) = k2_tarski(X37,X38) )).

cnf(u389,axiom,
    ( ~ r2_hidden(X19,k2_tarski(X19,X20))
    | k2_tarski(X19,X20) = k2_tarski(X18,X19)
    | sK2(X18,X19,k2_tarski(X19,X20)) = X18
    | sK2(X18,X19,k2_tarski(X19,X20)) = X20 )).

cnf(u545,axiom,
    ( ~ r2_hidden(X27,k2_tarski(X27,X29))
    | k2_tarski(X27,X29) = k2_tarski(X27,X28)
    | sK2(X27,X28,k2_tarski(X27,X29)) = X28
    | sK2(X27,X28,k2_tarski(X27,X29)) = X29 )).

cnf(u2431,axiom,
    ( ~ r2_hidden(X260,k2_tarski(X259,X259))
    | k2_tarski(X259,X259) = k2_tarski(sK2(X257,X258,k2_tarski(X259,X259)),X260)
    | sK2(sK2(X257,X258,k2_tarski(X259,X259)),X260,k2_tarski(X259,X259)) = X259
    | sK2(X257,X258,k2_tarski(X259,X259)) = X258
    | sK2(X257,X258,k2_tarski(X259,X259)) = X257
    | k2_tarski(X259,X259) = k2_tarski(X257,X258) )).

cnf(u2423,axiom,
    ( ~ r2_hidden(X228,k2_tarski(X227,X227))
    | k2_tarski(X227,X227) = k2_tarski(X228,sK2(X225,X226,k2_tarski(X227,X227)))
    | sK2(X228,sK2(X225,X226,k2_tarski(X227,X227)),k2_tarski(X227,X227)) = X227
    | sK2(X225,X226,k2_tarski(X227,X227)) = X226
    | sK2(X225,X226,k2_tarski(X227,X227)) = X225
    | k2_tarski(X227,X227) = k2_tarski(X225,X226) )).

cnf(u2369,axiom,
    ( ~ r2_hidden(X9,k2_tarski(X8,X8))
    | sK2(X6,X7,k2_tarski(X8,X8)) = X9
    | X8 = X9
    | sK2(X6,X7,k2_tarski(X8,X8)) = X7
    | sK2(X6,X7,k2_tarski(X8,X8)) = X6
    | k2_tarski(X6,X7) = k2_tarski(X8,X8) )).

cnf(u1713,axiom,
    ( ~ r2_hidden(X65,k2_tarski(X64,X64))
    | k2_tarski(X64,X65) = k2_tarski(X64,X64) )).

cnf(u1587,axiom,
    ( ~ r2_hidden(X59,k2_tarski(X60,X60))
    | k2_tarski(X60,X60) = k2_tarski(X59,X60) )).

cnf(u772,axiom,
    ( ~ r2_hidden(X45,k2_tarski(X46,X46))
    | k2_tarski(X44,X45) = k2_tarski(X46,X46)
    | sK2(X44,X45,k2_tarski(X46,X46)) = X44
    | sK2(X44,X45,k2_tarski(X46,X46)) = X46 )).

cnf(u770,axiom,
    ( ~ r2_hidden(X41,k2_tarski(X43,X43))
    | k2_tarski(X43,X43) = k2_tarski(X41,X42)
    | sK2(X41,X42,k2_tarski(X43,X43)) = X42
    | sK2(X41,X42,k2_tarski(X43,X43)) = X43 )).

cnf(u322,axiom,
    ( ~ r2_hidden(X12,k2_tarski(X13,X13))
    | k2_tarski(X12,X12) = k2_tarski(X13,X13)
    | sK2(X12,X12,k2_tarski(X13,X13)) = X13 )).

cnf(u254,axiom,
    ( ~ r2_hidden(X12,k2_tarski(X13,X12))
    | k2_tarski(X12,X12) = k2_tarski(X13,X12)
    | sK2(X12,X12,k2_tarski(X13,X12)) = X13 )).

cnf(u674,axiom,
    ( ~ r2_hidden(X28,k2_tarski(X29,X28))
    | k2_tarski(X29,X28) = k2_tarski(X28,X29)
    | sK2(X28,X29,k2_tarski(X29,X28)) = X29 )).

cnf(u458,axiom,
    ( ~ r2_hidden(X25,k2_tarski(X26,X25))
    | k2_tarski(X26,X25) = k2_tarski(X24,X25)
    | sK2(X24,X25,k2_tarski(X26,X25)) = X24
    | sK2(X24,X25,k2_tarski(X26,X25)) = X26 )).

cnf(u633,axiom,
    ( ~ r2_hidden(X33,k2_tarski(X35,X33))
    | k2_tarski(X33,X34) = k2_tarski(X35,X33)
    | sK2(X33,X34,k2_tarski(X35,X33)) = X34
    | sK2(X33,X34,k2_tarski(X35,X33)) = X35 )).

cnf(u2184,axiom,
    ( ~ r2_hidden(X2,k2_tarski(X1,X0))
    | k2_tarski(X1,X0) = k2_tarski(X0,X2)
    | sK2(X0,X2,k2_tarski(X1,X0)) = X1 )).

cnf(u2167,axiom,
    ( ~ r2_hidden(X96,k2_tarski(X95,X97))
    | k2_tarski(X95,X96) = k2_tarski(X95,X97)
    | sK2(X95,X96,k2_tarski(X95,X97)) = X97 )).

cnf(u1887,axiom,
    ( ~ r2_hidden(X2,k2_tarski(X1,X0))
    | k2_tarski(X1,X0) = k2_tarski(X2,X0)
    | sK2(X2,X0,k2_tarski(X1,X0)) = X1 )).

cnf(u1865,axiom,
    ( ~ r2_hidden(X87,k2_tarski(X88,X89))
    | k2_tarski(X88,X89) = k2_tarski(X87,X88)
    | sK2(X87,X88,k2_tarski(X88,X89)) = X89 )).

cnf(u1473,axiom,
    ( ~ r2_hidden(X79,k2_tarski(X82,X83))
    | k2_tarski(X82,X83) = k2_tarski(X79,sK2(X80,X81,k2_tarski(X82,X83)))
    | sK2(X79,sK2(X80,X81,k2_tarski(X82,X83)),k2_tarski(X82,X83)) = X82
    | sK2(X79,sK2(X80,X81,k2_tarski(X82,X83)),k2_tarski(X82,X83)) = X83
    | sK2(X80,X81,k2_tarski(X82,X83)) = X81
    | sK2(X80,X81,k2_tarski(X82,X83)) = X80
    | k2_tarski(X82,X83) = k2_tarski(X80,X81) )).

cnf(u1143,axiom,
    ( ~ r2_hidden(X76,k2_tarski(X74,X75))
    | k2_tarski(X74,X75) = k2_tarski(sK2(X72,X73,k2_tarski(X74,X75)),X76)
    | sK2(sK2(X72,X73,k2_tarski(X74,X75)),X76,k2_tarski(X74,X75)) = X74
    | sK2(sK2(X72,X73,k2_tarski(X74,X75)),X76,k2_tarski(X74,X75)) = X75
    | sK2(X72,X73,k2_tarski(X74,X75)) = X73
    | sK2(X72,X73,k2_tarski(X74,X75)) = X72
    | k2_tarski(X72,X73) = k2_tarski(X74,X75) )).

cnf(u638,axiom,
    ( ~ r2_hidden(X37,k2_tarski(X38,X36))
    | k2_tarski(X36,X37) = k2_tarski(X38,X36)
    | sK2(X36,X37,k2_tarski(X38,X36)) = X38
    | sK2(X36,X37,k2_tarski(X38,X36)) = X36 )).

cnf(u547,axiom,
    ( ~ r2_hidden(X31,k2_tarski(X30,X32))
    | k2_tarski(X30,X32) = k2_tarski(X30,X31)
    | sK2(X30,X31,k2_tarski(X30,X32)) = X30
    | sK2(X30,X31,k2_tarski(X30,X32)) = X32 )).

cnf(u465,axiom,
    ( ~ r2_hidden(X21,k2_tarski(X23,X22))
    | k2_tarski(X23,X22) = k2_tarski(X21,X22)
    | sK2(X21,X22,k2_tarski(X23,X22)) = X23
    | sK2(X21,X22,k2_tarski(X23,X22)) = X22 )).

cnf(u393,axiom,
    ( ~ r2_hidden(X15,k2_tarski(X16,X17))
    | k2_tarski(X16,X17) = k2_tarski(X15,X16)
    | sK2(X15,X16,k2_tarski(X16,X17)) = X16
    | sK2(X15,X16,k2_tarski(X16,X17)) = X17 )).

cnf(u160,axiom,
    ( ~ r2_hidden(X18,k2_tarski(X19,X20))
    | k2_tarski(X19,X20) = k2_tarski(X18,X18)
    | sK2(X18,X18,k2_tarski(X19,X20)) = X19
    | sK2(X18,X18,k2_tarski(X19,X20)) = X20 )).

cnf(u113,axiom,
    ( ~ r2_hidden(X9,k2_tarski(X10,X11))
    | k2_tarski(X10,X11) = k2_tarski(X8,X9)
    | sK2(X8,X9,k2_tarski(X10,X11)) = X8
    | sK2(X8,X9,k2_tarski(X10,X11)) = X10
    | sK2(X8,X9,k2_tarski(X10,X11)) = X11 )).

cnf(u111,axiom,
    ( ~ r2_hidden(X4,k2_tarski(X6,X7))
    | k2_tarski(X6,X7) = k2_tarski(X4,X5)
    | sK2(X4,X5,k2_tarski(X6,X7)) = X5
    | sK2(X4,X5,k2_tarski(X6,X7)) = X6
    | sK2(X4,X5,k2_tarski(X6,X7)) = X7 )).

cnf(u52,axiom,
    ( ~ r2_hidden(X4,k2_tarski(X0,X1))
    | X0 = X4
    | X1 = X4 )).

cnf(u1719,axiom,
    ( k2_tarski(X2,X2) = k2_tarski(X2,sK2(X3,X4,k2_tarski(X2,X2)))
    | sK2(X3,X4,k2_tarski(X2,X2)) = X4
    | sK2(X3,X4,k2_tarski(X2,X2)) = X3
    | k2_tarski(X2,X2) = k2_tarski(X3,X4) )).

cnf(u1592,axiom,
    ( k2_tarski(X2,X2) = k2_tarski(sK2(X3,X4,k2_tarski(X2,X2)),X2)
    | sK2(X3,X4,k2_tarski(X2,X2)) = X4
    | sK2(X3,X4,k2_tarski(X2,X2)) = X3
    | k2_tarski(X2,X2) = k2_tarski(X3,X4) )).

cnf(u797,axiom,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) )).

cnf(u2180,axiom,
    ( sK2(sK2(X5,X6,k2_tarski(X4,X4)),X7,k2_tarski(X4,X4)) = X7
    | sK2(sK2(X5,X6,k2_tarski(X4,X4)),X7,k2_tarski(X4,X4)) = X4
    | k2_tarski(X4,X4) = k2_tarski(sK2(X5,X6,k2_tarski(X4,X4)),X7)
    | sK2(X5,X6,k2_tarski(X4,X4)) = X6
    | sK2(X5,X6,k2_tarski(X4,X4)) = X5
    | k2_tarski(X4,X4) = k2_tarski(X5,X6) )).

cnf(u2180_001,axiom,
    ( sK2(sK2(X5,X6,k2_tarski(X4,X4)),X7,k2_tarski(X4,X4)) = X7
    | sK2(sK2(X5,X6,k2_tarski(X4,X4)),X7,k2_tarski(X4,X4)) = X4
    | k2_tarski(X4,X4) = k2_tarski(sK2(X5,X6,k2_tarski(X4,X4)),X7)
    | sK2(X5,X6,k2_tarski(X4,X4)) = X6
    | sK2(X5,X6,k2_tarski(X4,X4)) = X5
    | k2_tarski(X4,X4) = k2_tarski(X5,X6) )).

cnf(u4998,axiom,
    ( sK2(sK2(X0,X1,k2_tarski(X2,X2)),sK2(X3,X4,k2_tarski(X2,X2)),k2_tarski(X2,X2)) = X2
    | k2_tarski(X2,X2) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X2)),sK2(X3,X4,k2_tarski(X2,X2)))
    | sK2(X0,X1,k2_tarski(X2,X2)) = X1
    | sK2(X0,X1,k2_tarski(X2,X2)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X2)
    | sK2(X3,X4,k2_tarski(X2,X2)) = X4
    | sK2(X3,X4,k2_tarski(X2,X2)) = X3
    | k2_tarski(X2,X2) = k2_tarski(X3,X4) )).

cnf(u2579,axiom,
    ( sK2(sK2(X16,X17,k2_tarski(X15,X15)),sK2(X13,X14,k2_tarski(X15,X15)),k2_tarski(X15,X15)) = X15
    | k2_tarski(X15,X15) = k2_tarski(sK2(X13,X14,k2_tarski(X15,X15)),sK2(X16,X17,k2_tarski(X15,X15)))
    | sK2(X16,X17,k2_tarski(X15,X15)) = X17
    | sK2(X16,X17,k2_tarski(X15,X15)) = X16
    | k2_tarski(X16,X17) = k2_tarski(X15,X15)
    | sK2(X13,X14,k2_tarski(X15,X15)) = X14
    | sK2(X13,X14,k2_tarski(X15,X15)) = X13
    | k2_tarski(X13,X14) = k2_tarski(X15,X15) )).

cnf(u329,axiom,
    ( sK2(sK2(X2,X3,k2_tarski(X4,X4)),sK2(X2,X3,k2_tarski(X4,X4)),k2_tarski(X4,X4)) = X4
    | k2_tarski(X4,X4) = k2_tarski(sK2(X2,X3,k2_tarski(X4,X4)),sK2(X2,X3,k2_tarski(X4,X4)))
    | sK2(X2,X3,k2_tarski(X4,X4)) = X3
    | sK2(X2,X3,k2_tarski(X4,X4)) = X2
    | k2_tarski(X2,X3) = k2_tarski(X4,X4) )).

cnf(u3148,axiom,
    ( sK2(sK2(X10,X11,k2_tarski(X8,X9)),sK2(X12,X13,k2_tarski(X8,X9)),k2_tarski(X8,X9)) = X8
    | sK2(sK2(X10,X11,k2_tarski(X8,X9)),sK2(X12,X13,k2_tarski(X8,X9)),k2_tarski(X8,X9)) = X9
    | k2_tarski(X8,X9) = k2_tarski(sK2(X10,X11,k2_tarski(X8,X9)),sK2(X12,X13,k2_tarski(X8,X9)))
    | sK2(X10,X11,k2_tarski(X8,X9)) = X11
    | sK2(X10,X11,k2_tarski(X8,X9)) = X10
    | k2_tarski(X10,X11) = k2_tarski(X8,X9)
    | sK2(X12,X13,k2_tarski(X8,X9)) = X13
    | sK2(X12,X13,k2_tarski(X8,X9)) = X12
    | k2_tarski(X8,X9) = k2_tarski(X12,X13) )).

cnf(u3148_002,axiom,
    ( sK2(sK2(X10,X11,k2_tarski(X8,X9)),sK2(X12,X13,k2_tarski(X8,X9)),k2_tarski(X8,X9)) = X8
    | sK2(sK2(X10,X11,k2_tarski(X8,X9)),sK2(X12,X13,k2_tarski(X8,X9)),k2_tarski(X8,X9)) = X9
    | k2_tarski(X8,X9) = k2_tarski(sK2(X10,X11,k2_tarski(X8,X9)),sK2(X12,X13,k2_tarski(X8,X9)))
    | sK2(X10,X11,k2_tarski(X8,X9)) = X11
    | sK2(X10,X11,k2_tarski(X8,X9)) = X10
    | k2_tarski(X10,X11) = k2_tarski(X8,X9)
    | sK2(X12,X13,k2_tarski(X8,X9)) = X13
    | sK2(X12,X13,k2_tarski(X8,X9)) = X12
    | k2_tarski(X8,X9) = k2_tarski(X12,X13) )).

cnf(u1734,axiom,
    ( sK2(sK2(X6,X7,k2_tarski(X4,X5)),sK2(X6,X7,k2_tarski(X4,X5)),k2_tarski(X4,X5)) = X4
    | sK2(sK2(X6,X7,k2_tarski(X4,X5)),sK2(X6,X7,k2_tarski(X4,X5)),k2_tarski(X4,X5)) = X5
    | k2_tarski(X4,X5) = k2_tarski(sK2(X6,X7,k2_tarski(X4,X5)),sK2(X6,X7,k2_tarski(X4,X5)))
    | sK2(X6,X7,k2_tarski(X4,X5)) = X7
    | sK2(X6,X7,k2_tarski(X4,X5)) = X6
    | k2_tarski(X6,X7) = k2_tarski(X4,X5) )).

cnf(u1734_003,axiom,
    ( sK2(sK2(X6,X7,k2_tarski(X4,X5)),sK2(X6,X7,k2_tarski(X4,X5)),k2_tarski(X4,X5)) = X4
    | sK2(sK2(X6,X7,k2_tarski(X4,X5)),sK2(X6,X7,k2_tarski(X4,X5)),k2_tarski(X4,X5)) = X5
    | k2_tarski(X4,X5) = k2_tarski(sK2(X6,X7,k2_tarski(X4,X5)),sK2(X6,X7,k2_tarski(X4,X5)))
    | sK2(X6,X7,k2_tarski(X4,X5)) = X7
    | sK2(X6,X7,k2_tarski(X4,X5)) = X6
    | k2_tarski(X6,X7) = k2_tarski(X4,X5) )).

cnf(u287,axiom,
    ( sK2(sK2(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X10
    | sK2(sK2(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X6
    | sK2(sK2(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X7
    | k2_tarski(X6,X7) = k2_tarski(sK2(X8,X9,k2_tarski(X6,X7)),X10)
    | sK2(X8,X9,k2_tarski(X6,X7)) = X9
    | sK2(X8,X9,k2_tarski(X6,X7)) = X8
    | k2_tarski(X6,X7) = k2_tarski(X8,X9) )).

cnf(u287_004,axiom,
    ( sK2(sK2(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X10
    | sK2(sK2(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X6
    | sK2(sK2(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X7
    | k2_tarski(X6,X7) = k2_tarski(sK2(X8,X9,k2_tarski(X6,X7)),X10)
    | sK2(X8,X9,k2_tarski(X6,X7)) = X9
    | sK2(X8,X9,k2_tarski(X6,X7)) = X8
    | k2_tarski(X6,X7) = k2_tarski(X8,X9) )).

cnf(u287_005,axiom,
    ( sK2(sK2(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X10
    | sK2(sK2(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X6
    | sK2(sK2(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X7
    | k2_tarski(X6,X7) = k2_tarski(sK2(X8,X9,k2_tarski(X6,X7)),X10)
    | sK2(X8,X9,k2_tarski(X6,X7)) = X9
    | sK2(X8,X9,k2_tarski(X6,X7)) = X8
    | k2_tarski(X6,X7) = k2_tarski(X8,X9) )).

cnf(u2576,axiom,
    ( sK2(sK2(X2,X3,k2_tarski(X1,X0)),X0,k2_tarski(X1,X0)) = X1
    | k2_tarski(X1,X0) = k2_tarski(X0,sK2(X2,X3,k2_tarski(X1,X0)))
    | sK2(X2,X3,k2_tarski(X1,X0)) = X3
    | sK2(X2,X3,k2_tarski(X1,X0)) = X2
    | k2_tarski(X1,X0) = k2_tarski(X2,X3) )).

cnf(u1889,axiom,
    ( sK2(sK2(X6,X7,k2_tarski(X4,X5)),X4,k2_tarski(X4,X5)) = X5
    | k2_tarski(X4,X5) = k2_tarski(X4,sK2(X6,X7,k2_tarski(X4,X5)))
    | sK2(X6,X7,k2_tarski(X4,X5)) = X7
    | sK2(X6,X7,k2_tarski(X4,X5)) = X6
    | k2_tarski(X6,X7) = k2_tarski(X4,X5) )).

cnf(u2183,axiom,
    ( sK2(X4,sK2(X5,X6,k2_tarski(X4,X7)),k2_tarski(X4,X7)) = X7
    | k2_tarski(X4,X7) = k2_tarski(X4,sK2(X5,X6,k2_tarski(X4,X7)))
    | sK2(X5,X6,k2_tarski(X4,X7)) = X6
    | sK2(X5,X6,k2_tarski(X4,X7)) = X5
    | k2_tarski(X5,X6) = k2_tarski(X4,X7) )).

cnf(u2188,axiom,
    ( sK2(X4,sK2(X5,X6,k2_tarski(X7,X7)),k2_tarski(X7,X7)) = X4
    | sK2(X4,sK2(X5,X6,k2_tarski(X7,X7)),k2_tarski(X7,X7)) = X7
    | k2_tarski(X7,X7) = k2_tarski(X4,sK2(X5,X6,k2_tarski(X7,X7)))
    | sK2(X5,X6,k2_tarski(X7,X7)) = X6
    | sK2(X5,X6,k2_tarski(X7,X7)) = X5
    | k2_tarski(X7,X7) = k2_tarski(X5,X6) )).

cnf(u2188_006,axiom,
    ( sK2(X4,sK2(X5,X6,k2_tarski(X7,X7)),k2_tarski(X7,X7)) = X4
    | sK2(X4,sK2(X5,X6,k2_tarski(X7,X7)),k2_tarski(X7,X7)) = X7
    | k2_tarski(X7,X7) = k2_tarski(X4,sK2(X5,X6,k2_tarski(X7,X7)))
    | sK2(X5,X6,k2_tarski(X7,X7)) = X6
    | sK2(X5,X6,k2_tarski(X7,X7)) = X5
    | k2_tarski(X7,X7) = k2_tarski(X5,X6) )).

cnf(u2692,axiom,
    ( sK2(X0,sK2(X2,X3,k2_tarski(X1,X0)),k2_tarski(X1,X0)) = X1
    | k2_tarski(X1,X0) = k2_tarski(X0,sK2(X2,X3,k2_tarski(X1,X0)))
    | sK2(X2,X3,k2_tarski(X1,X0)) = X3
    | sK2(X2,X3,k2_tarski(X1,X0)) = X2
    | k2_tarski(X1,X0) = k2_tarski(X2,X3) )).

cnf(u291,axiom,
    ( sK2(X8,sK2(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X8
    | sK2(X8,sK2(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X6
    | sK2(X8,sK2(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X7
    | k2_tarski(X6,X7) = k2_tarski(X8,sK2(X9,X10,k2_tarski(X6,X7)))
    | sK2(X9,X10,k2_tarski(X6,X7)) = X10
    | sK2(X9,X10,k2_tarski(X6,X7)) = X9
    | k2_tarski(X6,X7) = k2_tarski(X9,X10) )).

cnf(u291_007,axiom,
    ( sK2(X8,sK2(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X8
    | sK2(X8,sK2(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X6
    | sK2(X8,sK2(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X7
    | k2_tarski(X6,X7) = k2_tarski(X8,sK2(X9,X10,k2_tarski(X6,X7)))
    | sK2(X9,X10,k2_tarski(X6,X7)) = X10
    | sK2(X9,X10,k2_tarski(X6,X7)) = X9
    | k2_tarski(X6,X7) = k2_tarski(X9,X10) )).

cnf(u291_008,axiom,
    ( sK2(X8,sK2(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X8
    | sK2(X8,sK2(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X6
    | sK2(X8,sK2(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X7
    | k2_tarski(X6,X7) = k2_tarski(X8,sK2(X9,X10,k2_tarski(X6,X7)))
    | sK2(X9,X10,k2_tarski(X6,X7)) = X10
    | sK2(X9,X10,k2_tarski(X6,X7)) = X9
    | k2_tarski(X6,X7) = k2_tarski(X9,X10) )).

cnf(u164,axiom,
    ( sK2(X0,X0,k2_tarski(X0,X1)) = X0
    | sK2(X0,X0,k2_tarski(X0,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X0,X0) )).

cnf(u201,axiom,
    ( sK2(X1,X1,k2_tarski(X1,X2)) = X2
    | k2_tarski(X1,X1) = k2_tarski(X1,X2) )).

cnf(u164_009,axiom,
    ( sK2(X0,X0,k2_tarski(X0,X1)) = X0
    | sK2(X0,X0,k2_tarski(X0,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X0,X0) )).

cnf(u293,axiom,
    ( sK2(X0,X0,k2_tarski(X1,X1)) = X0
    | sK2(X0,X0,k2_tarski(X1,X1)) = X1
    | k2_tarski(X0,X0) = k2_tarski(X1,X1) )).

cnf(u293_010,axiom,
    ( sK2(X0,X0,k2_tarski(X1,X1)) = X0
    | sK2(X0,X0,k2_tarski(X1,X1)) = X1
    | k2_tarski(X0,X0) = k2_tarski(X1,X1) )).

cnf(u227,axiom,
    ( sK2(X0,X0,k2_tarski(X1,X0)) = X1
    | sK2(X0,X0,k2_tarski(X1,X0)) = X0
    | k2_tarski(X0,X0) = k2_tarski(X1,X0) )).

cnf(u227_011,axiom,
    ( sK2(X0,X0,k2_tarski(X1,X0)) = X1
    | sK2(X0,X0,k2_tarski(X1,X0)) = X0
    | k2_tarski(X0,X0) = k2_tarski(X1,X0) )).

cnf(u264,axiom,
    ( sK2(X0,X0,k2_tarski(X1,X0)) = X1
    | k2_tarski(X0,X0) = k2_tarski(X1,X0) )).

cnf(u115,axiom,
    ( sK2(X0,X0,k2_tarski(X1,X2)) = X0
    | sK2(X0,X0,k2_tarski(X1,X2)) = X1
    | sK2(X0,X0,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X0) = k2_tarski(X1,X2) )).

cnf(u115_012,axiom,
    ( sK2(X0,X0,k2_tarski(X1,X2)) = X0
    | sK2(X0,X0,k2_tarski(X1,X2)) = X1
    | sK2(X0,X0,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X0) = k2_tarski(X1,X2) )).

cnf(u115_013,axiom,
    ( sK2(X0,X0,k2_tarski(X1,X2)) = X0
    | sK2(X0,X0,k2_tarski(X1,X2)) = X1
    | sK2(X0,X0,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X0) = k2_tarski(X1,X2) )).

cnf(u1604,axiom,
    ( sK2(X0,X1,k2_tarski(X0,X0)) = X1
    | sK2(X0,X1,k2_tarski(X0,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X0,X0) )).

cnf(u1604_014,axiom,
    ( sK2(X0,X1,k2_tarski(X0,X0)) = X1
    | sK2(X0,X1,k2_tarski(X0,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X0,X0) )).

cnf(u1672,axiom,
    ( sK2(X0,X1,k2_tarski(X0,X0)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X0,X0) )).

cnf(u202,axiom,
    ( sK2(X0,X1,k2_tarski(X0,X2)) = X1
    | sK2(X0,X1,k2_tarski(X0,X2)) = X0
    | sK2(X0,X1,k2_tarski(X0,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u1903,axiom,
    ( sK2(X2,X4,k2_tarski(X2,X3)) = X4
    | sK2(X2,X4,k2_tarski(X2,X3)) = X3
    | k2_tarski(X2,X3) = k2_tarski(X2,X4) )).

cnf(u202_015,axiom,
    ( sK2(X0,X1,k2_tarski(X0,X2)) = X1
    | sK2(X0,X1,k2_tarski(X0,X2)) = X0
    | sK2(X0,X1,k2_tarski(X0,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u202_016,axiom,
    ( sK2(X0,X1,k2_tarski(X0,X2)) = X1
    | sK2(X0,X1,k2_tarski(X0,X2)) = X0
    | sK2(X0,X1,k2_tarski(X0,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u1903_017,axiom,
    ( sK2(X2,X4,k2_tarski(X2,X3)) = X4
    | sK2(X2,X4,k2_tarski(X2,X3)) = X3
    | k2_tarski(X2,X3) = k2_tarski(X2,X4) )).

cnf(u873,axiom,
    ( sK2(X0,X1,k2_tarski(X1,X1)) = X0
    | sK2(X0,X1,k2_tarski(X1,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X1,X1) )).

cnf(u873_018,axiom,
    ( sK2(X0,X1,k2_tarski(X1,X1)) = X0
    | sK2(X0,X1,k2_tarski(X1,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X1,X1) )).

cnf(u1545,axiom,
    ( sK2(X1,X0,k2_tarski(X0,X0)) = X1
    | k2_tarski(X0,X0) = k2_tarski(X1,X0) )).

cnf(u641,axiom,
    ( sK2(X0,X1,k2_tarski(X1,X0)) = X1
    | sK2(X0,X1,k2_tarski(X1,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

cnf(u641_019,axiom,
    ( sK2(X0,X1,k2_tarski(X1,X0)) = X1
    | sK2(X0,X1,k2_tarski(X1,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

cnf(u774,axiom,
    ( sK2(X1,X0,k2_tarski(X0,X1)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

cnf(u163,axiom,
    ( sK2(X0,X1,k2_tarski(X1,X2)) = X0
    | sK2(X0,X1,k2_tarski(X1,X2)) = X1
    | sK2(X0,X1,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u1738,axiom,
    ( sK2(X4,X2,k2_tarski(X2,X3)) = X4
    | sK2(X4,X2,k2_tarski(X2,X3)) = X3
    | k2_tarski(X2,X3) = k2_tarski(X4,X2) )).

cnf(u163_020,axiom,
    ( sK2(X0,X1,k2_tarski(X1,X2)) = X0
    | sK2(X0,X1,k2_tarski(X1,X2)) = X1
    | sK2(X0,X1,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u163_021,axiom,
    ( sK2(X0,X1,k2_tarski(X1,X2)) = X0
    | sK2(X0,X1,k2_tarski(X1,X2)) = X1
    | sK2(X0,X1,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u1738_022,axiom,
    ( sK2(X4,X2,k2_tarski(X2,X3)) = X4
    | sK2(X4,X2,k2_tarski(X2,X3)) = X3
    | k2_tarski(X2,X3) = k2_tarski(X4,X2) )).

cnf(u66,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | sK2(X0,X1,k2_tarski(X2,X3)) = X2
    | sK2(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u66_023,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | sK2(X0,X1,k2_tarski(X2,X3)) = X2
    | sK2(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u66_024,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | sK2(X0,X1,k2_tarski(X2,X3)) = X2
    | sK2(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u66_025,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | sK2(X0,X1,k2_tarski(X2,X3)) = X2
    | sK2(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u226,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X2)) = X1
    | sK2(X0,X1,k2_tarski(X2,X2)) = X0
    | sK2(X0,X1,k2_tarski(X2,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u226_026,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X2)) = X1
    | sK2(X0,X1,k2_tarski(X2,X2)) = X0
    | sK2(X0,X1,k2_tarski(X2,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u226_027,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X2)) = X1
    | sK2(X0,X1,k2_tarski(X2,X2)) = X0
    | sK2(X0,X1,k2_tarski(X2,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u196,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X1)) = X0
    | sK2(X0,X1,k2_tarski(X2,X1)) = X2
    | sK2(X0,X1,k2_tarski(X2,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u196_028,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X1)) = X0
    | sK2(X0,X1,k2_tarski(X2,X1)) = X2
    | sK2(X0,X1,k2_tarski(X2,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u1880,axiom,
    ( sK2(X2,X1,k2_tarski(X0,X1)) = X2
    | sK2(X2,X1,k2_tarski(X0,X1)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u196_029,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X1)) = X0
    | sK2(X0,X1,k2_tarski(X2,X1)) = X2
    | sK2(X0,X1,k2_tarski(X2,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u1880_030,axiom,
    ( sK2(X2,X1,k2_tarski(X0,X1)) = X2
    | sK2(X2,X1,k2_tarski(X0,X1)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u222,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X0)) = X1
    | sK2(X0,X1,k2_tarski(X2,X0)) = X2
    | sK2(X0,X1,k2_tarski(X2,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u222_031,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X0)) = X1
    | sK2(X0,X1,k2_tarski(X2,X0)) = X2
    | sK2(X0,X1,k2_tarski(X2,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u2036,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X0)) = X1
    | sK2(X0,X1,k2_tarski(X2,X0)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u222_032,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X0)) = X1
    | sK2(X0,X1,k2_tarski(X2,X0)) = X2
    | sK2(X0,X1,k2_tarski(X2,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u2036_033,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X0)) = X1
    | sK2(X0,X1,k2_tarski(X2,X0)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u61,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) )).

cnf(u4614,axiom,
    ( X2 != X3
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X4,X5,k2_tarski(X2,X3)),k2_tarski(X2,X3)) = X2
    | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X4,X5,k2_tarski(X2,X3)))
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X3)
    | sK2(X4,X5,k2_tarski(X2,X3)) = X5
    | sK2(X4,X5,k2_tarski(X2,X3)) = X4
    | k2_tarski(X2,X3) = k2_tarski(X4,X5) )).

cnf(u4613,axiom,
    ( X2 != X3
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X4,X5,k2_tarski(X2,X3)),k2_tarski(X2,X3)) = X3
    | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X4,X5,k2_tarski(X2,X3)))
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X3)
    | sK2(X4,X5,k2_tarski(X2,X3)) = X5
    | sK2(X4,X5,k2_tarski(X2,X3)) = X4
    | k2_tarski(X2,X3) = k2_tarski(X4,X5) )).

cnf(u4141,axiom,
    ( X2 != X3
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X0,X1,k2_tarski(X2,X3)),k2_tarski(X2,X3)) = X2
    | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X0,X1,k2_tarski(X2,X3)))
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u4140,axiom,
    ( X2 != X3
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X0,X1,k2_tarski(X2,X3)),k2_tarski(X2,X3)) = X3
    | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X0,X1,k2_tarski(X2,X3)))
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u3664,axiom,
    ( X0 != X3
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X3)),k2_tarski(X3,X3)) = X0
    | k2_tarski(X3,X3) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X3)))
    | sK2(X1,X2,k2_tarski(X3,X3)) = X2
    | sK2(X1,X2,k2_tarski(X3,X3)) = X1
    | k2_tarski(X1,X2) = k2_tarski(X3,X3) )).

cnf(u3663,axiom,
    ( X0 != X3
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X3)),k2_tarski(X3,X3)) = X3
    | k2_tarski(X3,X3) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X3)))
    | sK2(X1,X2,k2_tarski(X3,X3)) = X2
    | sK2(X1,X2,k2_tarski(X3,X3)) = X1
    | k2_tarski(X1,X2) = k2_tarski(X3,X3) )).

cnf(u3383,axiom,
    ( X2 != X3
    | sK2(sK2(X0,X1,k2_tarski(X2,X2)),X3,k2_tarski(X2,X2)) = X3
    | k2_tarski(X2,X2) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X2)),X3)
    | sK2(X0,X1,k2_tarski(X2,X2)) = X1
    | sK2(X0,X1,k2_tarski(X2,X2)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u3382,axiom,
    ( X2 != X3
    | sK2(sK2(X0,X1,k2_tarski(X2,X2)),X3,k2_tarski(X2,X2)) = X2
    | k2_tarski(X2,X2) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X2)),X3)
    | sK2(X0,X1,k2_tarski(X2,X2)) = X1
    | sK2(X0,X1,k2_tarski(X2,X2)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u2885,axiom,
    ( X138 != X139
    | k2_tarski(X138,X139) = k2_tarski(X139,sK2(X136,X137,k2_tarski(X138,X139)))
    | ~ r2_hidden(X139,k2_tarski(X138,X139))
    | sK2(X136,X137,k2_tarski(X138,X139)) = X137
    | sK2(X136,X137,k2_tarski(X138,X139)) = X136
    | k2_tarski(X138,X139) = k2_tarski(X136,X137) )).

cnf(u2631,axiom,
    ( X127 != X128
    | k2_tarski(X127,X128) = k2_tarski(X127,sK2(X125,X126,k2_tarski(X127,X128)))
    | ~ r2_hidden(X127,k2_tarski(X127,X128))
    | sK2(X125,X126,k2_tarski(X127,X128)) = X126
    | sK2(X125,X126,k2_tarski(X127,X128)) = X125
    | k2_tarski(X125,X126) = k2_tarski(X127,X128) )).

cnf(u2330,axiom,
    ( X99 != X100
    | k2_tarski(X99,X100) = k2_tarski(X101,X99)
    | ~ r2_hidden(X99,k2_tarski(X101,X99))
    | sK2(X99,X100,k2_tarski(X101,X99)) = X101 )).

cnf(u2315,axiom,
    ( X99 != X101
    | k2_tarski(X99,X100) = k2_tarski(X101,X99)
    | ~ r2_hidden(X99,k2_tarski(X101,X99))
    | sK2(X99,X100,k2_tarski(X101,X99)) = X100 )).

cnf(u2313,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X2,X0)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u2312,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X2,X0)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u2168,axiom,
    ( X92 != X93
    | k2_tarski(X92,X93) = k2_tarski(X92,X94)
    | ~ r2_hidden(X92,k2_tarski(X92,X94))
    | sK2(X92,X93,k2_tarski(X92,X94)) = X94 )).

cnf(u2153,axiom,
    ( X92 != X94
    | k2_tarski(X92,X93) = k2_tarski(X92,X94)
    | ~ r2_hidden(X92,k2_tarski(X92,X94))
    | sK2(X92,X93,k2_tarski(X92,X94)) = X93 )).

cnf(u2151,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X0,X2)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u2150,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X0,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u2024,axiom,
    ( X91 != X92
    | k2_tarski(X93,X92) = k2_tarski(X91,X92)
    | ~ r2_hidden(X92,k2_tarski(X93,X92))
    | sK2(X91,X92,k2_tarski(X93,X92)) = X93 )).

cnf(u2010,axiom,
    ( X92 != X93
    | k2_tarski(X93,X92) = k2_tarski(X91,X92)
    | ~ r2_hidden(X92,k2_tarski(X93,X92))
    | sK2(X91,X92,k2_tarski(X93,X92)) = X91 )).

cnf(u2009,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X2,X1)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u2008,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X2,X1)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u1863,axiom,
    ( X90 != X91
    | k2_tarski(X90,X91) = k2_tarski(X91,X92)
    | ~ r2_hidden(X91,k2_tarski(X91,X92))
    | sK2(X90,X91,k2_tarski(X91,X92)) = X92 )).

cnf(u1849,axiom,
    ( X91 != X92
    | k2_tarski(X90,X91) = k2_tarski(X91,X92)
    | ~ r2_hidden(X91,k2_tarski(X91,X92))
    | sK2(X90,X91,k2_tarski(X91,X92)) = X90 )).

cnf(u1848,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X1,X2)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u1847,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u1714,axiom,
    ( X62 != X63
    | k2_tarski(X62,X62) = k2_tarski(X62,X63)
    | ~ r2_hidden(X62,k2_tarski(X62,X62)) )).

cnf(u1658,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X0,X0)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X0,X0) )).

cnf(u1657,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X0,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X0,X0) )).

cnf(u1585,axiom,
    ( X61 != X62
    | k2_tarski(X62,X62) = k2_tarski(X61,X62)
    | ~ r2_hidden(X62,k2_tarski(X62,X62)) )).

cnf(u1455,axiom,
    ( X3 != X4
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X0
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X3
    | k2_tarski(X3,X4) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X4)))
    | sK2(X1,X2,k2_tarski(X3,X4)) = X2
    | sK2(X1,X2,k2_tarski(X3,X4)) = X1
    | k2_tarski(X1,X2) = k2_tarski(X3,X4) )).

cnf(u1454,axiom,
    ( X0 != X4
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X0
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X3
    | k2_tarski(X3,X4) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X4)))
    | sK2(X1,X2,k2_tarski(X3,X4)) = X2
    | sK2(X1,X2,k2_tarski(X3,X4)) = X1
    | k2_tarski(X1,X2) = k2_tarski(X3,X4) )).

cnf(u1453,axiom,
    ( X3 != X4
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X0
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X4
    | k2_tarski(X3,X4) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X4)))
    | sK2(X1,X2,k2_tarski(X3,X4)) = X2
    | sK2(X1,X2,k2_tarski(X3,X4)) = X1
    | k2_tarski(X1,X2) = k2_tarski(X3,X4) )).

cnf(u1452,axiom,
    ( X0 != X3
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X0
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X4
    | k2_tarski(X3,X4) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X4)))
    | sK2(X1,X2,k2_tarski(X3,X4)) = X2
    | sK2(X1,X2,k2_tarski(X3,X4)) = X1
    | k2_tarski(X1,X2) = k2_tarski(X3,X4) )).

cnf(u1451,axiom,
    ( X0 != X4
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X3
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X4
    | k2_tarski(X3,X4) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X4)))
    | sK2(X1,X2,k2_tarski(X3,X4)) = X2
    | sK2(X1,X2,k2_tarski(X3,X4)) = X1
    | k2_tarski(X1,X2) = k2_tarski(X3,X4) )).

cnf(u1450,axiom,
    ( X0 != X3
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X3
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X4
    | k2_tarski(X3,X4) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X4)))
    | sK2(X1,X2,k2_tarski(X3,X4)) = X2
    | sK2(X1,X2,k2_tarski(X3,X4)) = X1
    | k2_tarski(X1,X2) = k2_tarski(X3,X4) )).

cnf(u1135,axiom,
    ( X2 != X3
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X4
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X2
    | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),X4)
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u1134,axiom,
    ( X3 != X4
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X4
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X2
    | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),X4)
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u1133,axiom,
    ( X2 != X3
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X4
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X3
    | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),X4)
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u1132,axiom,
    ( X2 != X4
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X4
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X3
    | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),X4)
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u1131,axiom,
    ( X3 != X4
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X2
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X3
    | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),X4)
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u1130,axiom,
    ( X2 != X4
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X2
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X3
    | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),X4)
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u909,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X1,X1)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X1,X1) )).

cnf(u908,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X1,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X1,X1) )).

cnf(u764,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X2,X2)) = X1
    | sK2(X0,X1,k2_tarski(X2,X2)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u763,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X2,X2)) = X1
    | sK2(X0,X1,k2_tarski(X2,X2)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u762,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X2,X2)) = X1
    | sK2(X0,X1,k2_tarski(X2,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u761,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X2,X2)) = X1
    | sK2(X0,X1,k2_tarski(X2,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u760,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X2,X2)) = X0
    | sK2(X0,X1,k2_tarski(X2,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u759,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X2,X2)) = X0
    | sK2(X0,X1,k2_tarski(X2,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u671,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X1,X0)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

cnf(u670,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X1,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

cnf(u630,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X2,X0)) = X1
    | sK2(X0,X1,k2_tarski(X2,X0)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u629,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X2,X0)) = X1
    | sK2(X0,X1,k2_tarski(X2,X0)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u628,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X2,X0)) = X1
    | sK2(X0,X1,k2_tarski(X2,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u627,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X2,X0)) = X1
    | sK2(X0,X1,k2_tarski(X2,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u626,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X2,X0)) = X2
    | sK2(X0,X1,k2_tarski(X2,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u625,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X2,X0)) = X2
    | sK2(X0,X1,k2_tarski(X2,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u539,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X0,X2)) = X1
    | sK2(X0,X1,k2_tarski(X0,X2)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u538,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X0,X2)) = X1
    | sK2(X0,X1,k2_tarski(X0,X2)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u537,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X0,X2)) = X1
    | sK2(X0,X1,k2_tarski(X0,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u536,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X0,X2)) = X1
    | sK2(X0,X1,k2_tarski(X0,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u535,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X0,X2)) = X0
    | sK2(X0,X1,k2_tarski(X0,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u534,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X0,X2)) = X0
    | sK2(X0,X1,k2_tarski(X0,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u456,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X2,X1)) = X0
    | sK2(X0,X1,k2_tarski(X2,X1)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u455,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X2,X1)) = X0
    | sK2(X0,X1,k2_tarski(X2,X1)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u454,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X2,X1)) = X0
    | sK2(X0,X1,k2_tarski(X2,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u453,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X2,X1)) = X0
    | sK2(X0,X1,k2_tarski(X2,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u452,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X2,X1)) = X2
    | sK2(X0,X1,k2_tarski(X2,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u451,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X2,X1)) = X2
    | sK2(X0,X1,k2_tarski(X2,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u384,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X1,X2)) = X0
    | sK2(X0,X1,k2_tarski(X1,X2)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u383,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X1,X2)) = X0
    | sK2(X0,X1,k2_tarski(X1,X2)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u382,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X1,X2)) = X0
    | sK2(X0,X1,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u381,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X1,X2)) = X0
    | sK2(X0,X1,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u380,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X1,X2)) = X1
    | sK2(X0,X1,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u379,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X1,X2)) = X1
    | sK2(X0,X1,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u317,axiom,
    ( X0 != X1
    | sK2(X0,X0,k2_tarski(X1,X1)) = X0
    | k2_tarski(X0,X0) = k2_tarski(X1,X1) )).

cnf(u316,axiom,
    ( X0 != X1
    | sK2(X0,X0,k2_tarski(X1,X1)) = X1
    | k2_tarski(X0,X0) = k2_tarski(X1,X1) )).

cnf(u281,axiom,
    ( X12 != X13
    | k2_tarski(X12,X12) = k2_tarski(X13,X12)
    | ~ r2_hidden(X12,k2_tarski(X13,X12)) )).

cnf(u252,axiom,
    ( X0 != X1
    | sK2(X0,X0,k2_tarski(X1,X0)) = X1
    | k2_tarski(X0,X0) = k2_tarski(X1,X0) )).

cnf(u251,axiom,
    ( X0 != X1
    | sK2(X0,X0,k2_tarski(X1,X0)) = X0
    | k2_tarski(X0,X0) = k2_tarski(X1,X0) )).

cnf(u218,axiom,
    ( X12 != X13
    | k2_tarski(X12,X12) = k2_tarski(X12,X13)
    | ~ r2_hidden(X12,k2_tarski(X12,X13)) )).

cnf(u188,axiom,
    ( X0 != X1
    | sK2(X0,X0,k2_tarski(X0,X1)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X0,X0) )).

cnf(u187,axiom,
    ( X0 != X1
    | sK2(X0,X0,k2_tarski(X0,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X0,X0) )).

cnf(u152,axiom,
    ( X1 != X2
    | sK2(X0,X0,k2_tarski(X1,X2)) = X0
    | sK2(X0,X0,k2_tarski(X1,X2)) = X1
    | k2_tarski(X0,X0) = k2_tarski(X1,X2) )).

cnf(u151,axiom,
    ( X0 != X2
    | sK2(X0,X0,k2_tarski(X1,X2)) = X0
    | sK2(X0,X0,k2_tarski(X1,X2)) = X1
    | k2_tarski(X0,X0) = k2_tarski(X1,X2) )).

cnf(u150,axiom,
    ( X1 != X2
    | sK2(X0,X0,k2_tarski(X1,X2)) = X0
    | sK2(X0,X0,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X0) = k2_tarski(X1,X2) )).

cnf(u149,axiom,
    ( X0 != X1
    | sK2(X0,X0,k2_tarski(X1,X2)) = X0
    | sK2(X0,X0,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X0) = k2_tarski(X1,X2) )).

cnf(u148,axiom,
    ( X0 != X2
    | sK2(X0,X0,k2_tarski(X1,X2)) = X1
    | sK2(X0,X0,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X0) = k2_tarski(X1,X2) )).

cnf(u147,axiom,
    ( X0 != X1
    | sK2(X0,X0,k2_tarski(X1,X2)) = X1
    | sK2(X0,X0,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X0) = k2_tarski(X1,X2) )).

cnf(u102,axiom,
    ( X2 != X3
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | sK2(X0,X1,k2_tarski(X2,X3)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u101,axiom,
    ( X0 != X3
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | sK2(X0,X1,k2_tarski(X2,X3)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u100,axiom,
    ( X1 != X3
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | sK2(X0,X1,k2_tarski(X2,X3)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u99,axiom,
    ( X2 != X3
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | sK2(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u98,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | sK2(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u97,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | sK2(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u96,axiom,
    ( X0 != X3
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X2
    | sK2(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u95,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X2
    | sK2(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u94,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X2
    | sK2(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u93,axiom,
    ( X1 != X3
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | sK2(X0,X1,k2_tarski(X2,X3)) = X2
    | sK2(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u92,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | sK2(X0,X1,k2_tarski(X2,X3)) = X2
    | sK2(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u91,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | sK2(X0,X1,k2_tarski(X2,X3)) = X2
    | sK2(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u3398,axiom,
    ( sK2(X150,X151,k2_tarski(X152,X152)) != X153
    | k2_tarski(X152,X152) = k2_tarski(sK2(X150,X151,k2_tarski(X152,X152)),X153)
    | ~ r2_hidden(sK2(X150,X151,k2_tarski(X152,X152)),k2_tarski(X152,X152))
    | sK2(sK2(X150,X151,k2_tarski(X152,X152)),X153,k2_tarski(X152,X152)) = X152
    | sK2(X150,X151,k2_tarski(X152,X152)) = X151
    | sK2(X150,X151,k2_tarski(X152,X152)) = X150
    | k2_tarski(X150,X151) = k2_tarski(X152,X152) )).

cnf(u3682,axiom,
    ( sK2(X162,X163,k2_tarski(X164,X164)) != X161
    | k2_tarski(X164,X164) = k2_tarski(X161,sK2(X162,X163,k2_tarski(X164,X164)))
    | ~ r2_hidden(sK2(X162,X163,k2_tarski(X164,X164)),k2_tarski(X164,X164))
    | sK2(X161,sK2(X162,X163,k2_tarski(X164,X164)),k2_tarski(X164,X164)) = X164
    | sK2(X162,X163,k2_tarski(X164,X164)) = X163
    | sK2(X162,X163,k2_tarski(X164,X164)) = X162
    | k2_tarski(X162,X163) = k2_tarski(X164,X164) )).

cnf(u1144,axiom,
    ( sK2(X67,X68,k2_tarski(X69,X70)) != X71
    | k2_tarski(X69,X70) = k2_tarski(sK2(X67,X68,k2_tarski(X69,X70)),X71)
    | ~ r2_hidden(sK2(X67,X68,k2_tarski(X69,X70)),k2_tarski(X69,X70))
    | sK2(sK2(X67,X68,k2_tarski(X69,X70)),X71,k2_tarski(X69,X70)) = X69
    | sK2(sK2(X67,X68,k2_tarski(X69,X70)),X71,k2_tarski(X69,X70)) = X70
    | sK2(X67,X68,k2_tarski(X69,X70)) = X68
    | sK2(X67,X68,k2_tarski(X69,X70)) = X67
    | k2_tarski(X69,X70) = k2_tarski(X67,X68) )).

cnf(u1471,axiom,
    ( sK2(X85,X86,k2_tarski(X87,X88)) != X84
    | k2_tarski(X87,X88) = k2_tarski(X84,sK2(X85,X86,k2_tarski(X87,X88)))
    | ~ r2_hidden(sK2(X85,X86,k2_tarski(X87,X88)),k2_tarski(X87,X88))
    | sK2(X84,sK2(X85,X86,k2_tarski(X87,X88)),k2_tarski(X87,X88)) = X87
    | sK2(X84,sK2(X85,X86,k2_tarski(X87,X88)),k2_tarski(X87,X88)) = X88
    | sK2(X85,X86,k2_tarski(X87,X88)) = X86
    | sK2(X85,X86,k2_tarski(X87,X88)) = X85
    | k2_tarski(X85,X86) = k2_tarski(X87,X88) )).

cnf(u54,axiom,
    ( sK2(X0,X1,X2) != X0
    | k2_tarski(X0,X1) = X2
    | ~ r2_hidden(X0,X2) )).

cnf(u53,axiom,
    ( sK2(X0,X1,X2) != X1
    | k2_tarski(X0,X1) = X2
    | ~ r2_hidden(X1,X2) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:36:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (30063)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.48  % (30047)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.51  % (30043)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (30050)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.51  % (30050)Refutation not found, incomplete strategy% (30050)------------------------------
% 0.21/0.51  % (30050)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (30050)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (30050)Memory used [KB]: 10618
% 0.21/0.51  % (30050)Time elapsed: 0.095 s
% 0.21/0.51  % (30050)------------------------------
% 0.21/0.51  % (30050)------------------------------
% 0.21/0.52  % (30057)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.52  % (30057)Refutation not found, incomplete strategy% (30057)------------------------------
% 0.21/0.52  % (30057)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (30057)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (30057)Memory used [KB]: 1663
% 0.21/0.52  % (30057)Time elapsed: 0.110 s
% 0.21/0.52  % (30057)------------------------------
% 0.21/0.52  % (30057)------------------------------
% 0.21/0.53  % (30042)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (30041)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (30041)Refutation not found, incomplete strategy% (30041)------------------------------
% 0.21/0.53  % (30041)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (30041)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (30041)Memory used [KB]: 1663
% 0.21/0.53  % (30041)Time elapsed: 0.125 s
% 0.21/0.53  % (30041)------------------------------
% 0.21/0.53  % (30041)------------------------------
% 0.21/0.54  % (30045)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (30044)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.41/0.54  % (30056)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.41/0.54  % (30044)Refutation not found, incomplete strategy% (30044)------------------------------
% 1.41/0.54  % (30044)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (30044)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.54  
% 1.41/0.54  % (30044)Memory used [KB]: 1791
% 1.41/0.54  % (30044)Time elapsed: 0.129 s
% 1.41/0.54  % (30044)------------------------------
% 1.41/0.54  % (30044)------------------------------
% 1.41/0.54  % (30051)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.41/0.54  % (30051)Refutation not found, incomplete strategy% (30051)------------------------------
% 1.41/0.54  % (30051)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (30051)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.54  
% 1.41/0.54  % (30051)Memory used [KB]: 6140
% 1.41/0.54  % (30051)Time elapsed: 0.125 s
% 1.41/0.54  % (30051)------------------------------
% 1.41/0.54  % (30051)------------------------------
% 1.41/0.54  % (30049)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.41/0.54  % (30053)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.41/0.54  % (30067)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.41/0.54  % (30065)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.41/0.54  % (30067)Refutation not found, incomplete strategy% (30067)------------------------------
% 1.41/0.54  % (30067)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (30067)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.54  
% 1.41/0.54  % (30067)Memory used [KB]: 6140
% 1.41/0.54  % (30067)Time elapsed: 0.140 s
% 1.41/0.54  % (30067)------------------------------
% 1.41/0.54  % (30067)------------------------------
% 1.41/0.54  % (30060)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.41/0.54  % (30069)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.41/0.54  % (30065)Refutation not found, incomplete strategy% (30065)------------------------------
% 1.41/0.54  % (30065)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (30069)Refutation not found, incomplete strategy% (30069)------------------------------
% 1.41/0.54  % (30069)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (30069)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.54  
% 1.41/0.54  % (30069)Memory used [KB]: 1663
% 1.41/0.54  % (30069)Time elapsed: 0.001 s
% 1.41/0.54  % (30069)------------------------------
% 1.41/0.54  % (30069)------------------------------
% 1.41/0.55  % (30059)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.41/0.55  % (30056)Refutation not found, incomplete strategy% (30056)------------------------------
% 1.41/0.55  % (30056)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (30056)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (30056)Memory used [KB]: 10618
% 1.41/0.55  % (30056)Time elapsed: 0.131 s
% 1.41/0.55  % (30056)------------------------------
% 1.41/0.55  % (30056)------------------------------
% 1.41/0.55  % (30054)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.41/0.55  % (30058)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.41/0.55  % (30054)Refutation not found, incomplete strategy% (30054)------------------------------
% 1.41/0.55  % (30054)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (30054)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (30054)Memory used [KB]: 1663
% 1.41/0.55  % (30054)Time elapsed: 0.123 s
% 1.41/0.55  % (30054)------------------------------
% 1.41/0.55  % (30054)------------------------------
% 1.41/0.55  % (30065)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (30065)Memory used [KB]: 6140
% 1.41/0.55  % (30065)Time elapsed: 0.138 s
% 1.41/0.55  % (30065)------------------------------
% 1.41/0.55  % (30065)------------------------------
% 1.41/0.55  % (30062)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.41/0.55  % (30068)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.57/0.56  % (30058)Refutation not found, incomplete strategy% (30058)------------------------------
% 1.57/0.56  % (30058)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.56  % (30058)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.56  
% 1.57/0.56  % (30058)Memory used [KB]: 1663
% 1.57/0.56  % (30058)Time elapsed: 0.139 s
% 1.57/0.56  % (30058)------------------------------
% 1.57/0.56  % (30058)------------------------------
% 1.57/0.56  % (30052)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.57/0.56  % (30046)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.57/0.56  % (30052)Refutation not found, incomplete strategy% (30052)------------------------------
% 1.57/0.56  % (30052)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.56  % (30052)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.56  
% 1.57/0.56  % (30052)Memory used [KB]: 10618
% 1.57/0.56  % (30052)Time elapsed: 0.001 s
% 1.57/0.56  % (30052)------------------------------
% 1.57/0.56  % (30052)------------------------------
% 1.57/0.56  % (30040)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.57/0.57  % (30066)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.57/0.57  % (30048)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.57/0.58  % (30068)Refutation not found, incomplete strategy% (30068)------------------------------
% 1.57/0.58  % (30068)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.58  % (30068)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.58  
% 1.57/0.58  % (30068)Memory used [KB]: 10746
% 1.57/0.58  % (30068)Time elapsed: 0.160 s
% 1.57/0.58  % (30068)------------------------------
% 1.57/0.58  % (30068)------------------------------
% 1.57/0.58  % (30055)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.57/0.58  % (30061)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.57/0.59  % (30064)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.57/0.59  % (30066)Refutation not found, incomplete strategy% (30066)------------------------------
% 1.57/0.59  % (30066)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.59  % (30066)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.59  
% 1.57/0.59  % (30066)Memory used [KB]: 6268
% 1.57/0.59  % (30066)Time elapsed: 0.176 s
% 1.57/0.59  % (30066)------------------------------
% 1.57/0.59  % (30066)------------------------------
% 1.57/0.61  % (30064)Refutation not found, incomplete strategy% (30064)------------------------------
% 1.57/0.61  % (30064)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.61  % (30064)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.61  
% 1.57/0.61  % (30064)Memory used [KB]: 10618
% 1.57/0.61  % (30064)Time elapsed: 0.206 s
% 1.57/0.61  % (30064)------------------------------
% 1.57/0.61  % (30064)------------------------------
% 1.96/0.64  % (30043)Refutation not found, incomplete strategy% (30043)------------------------------
% 1.96/0.64  % (30043)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.96/0.64  % (30043)Termination reason: Refutation not found, incomplete strategy
% 1.96/0.64  
% 1.96/0.64  % (30043)Memory used [KB]: 6140
% 1.96/0.64  % (30043)Time elapsed: 0.227 s
% 1.96/0.64  % (30043)------------------------------
% 1.96/0.64  % (30043)------------------------------
% 1.96/0.64  % (30070)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 1.96/0.66  % (30076)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 1.96/0.66  % (30071)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 1.96/0.66  % (30076)Refutation not found, incomplete strategy% (30076)------------------------------
% 1.96/0.66  % (30076)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.96/0.66  % (30076)Termination reason: Refutation not found, incomplete strategy
% 1.96/0.66  
% 1.96/0.66  % (30076)Memory used [KB]: 10746
% 1.96/0.66  % (30076)Time elapsed: 0.059 s
% 1.96/0.66  % (30076)------------------------------
% 1.96/0.66  % (30076)------------------------------
% 2.17/0.68  % (30074)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.17/0.68  % (30042)Refutation not found, incomplete strategy% (30042)------------------------------
% 2.17/0.68  % (30042)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.68  % (30082)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 2.17/0.68  % (30074)Refutation not found, incomplete strategy% (30074)------------------------------
% 2.17/0.68  % (30074)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.68  % (30074)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.68  
% 2.17/0.68  % (30074)Memory used [KB]: 10618
% 2.17/0.68  % (30074)Time elapsed: 0.106 s
% 2.17/0.68  % (30074)------------------------------
% 2.17/0.68  % (30074)------------------------------
% 2.17/0.68  % (30079)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 2.17/0.68  % (30042)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.68  
% 2.17/0.68  % (30042)Memory used [KB]: 6268
% 2.17/0.68  % (30042)Time elapsed: 0.252 s
% 2.17/0.68  % (30042)------------------------------
% 2.17/0.68  % (30042)------------------------------
% 2.17/0.68  % (30078)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.17/0.68  % (30082)Refutation not found, incomplete strategy% (30082)------------------------------
% 2.17/0.68  % (30082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.68  % (30082)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.68  
% 2.17/0.68  % (30082)Memory used [KB]: 1663
% 2.17/0.68  % (30082)Time elapsed: 0.045 s
% 2.17/0.68  % (30082)------------------------------
% 2.17/0.68  % (30082)------------------------------
% 2.17/0.68  % (30079)Refutation not found, incomplete strategy% (30079)------------------------------
% 2.17/0.68  % (30079)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.68  % (30077)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.17/0.68  % (30075)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.17/0.68  % (30079)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.68  
% 2.17/0.68  % (30079)Memory used [KB]: 10746
% 2.17/0.68  % (30079)Time elapsed: 0.093 s
% 2.17/0.68  % (30079)------------------------------
% 2.17/0.68  % (30079)------------------------------
% 2.17/0.69  % (30073)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.17/0.69  % (30073)Refutation not found, incomplete strategy% (30073)------------------------------
% 2.17/0.69  % (30073)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.69  % (30073)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.69  
% 2.17/0.69  % (30073)Memory used [KB]: 10618
% 2.17/0.69  % (30073)Time elapsed: 0.125 s
% 2.17/0.69  % (30073)------------------------------
% 2.17/0.69  % (30073)------------------------------
% 2.17/0.71  % (30080)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 2.17/0.71  % (30040)Refutation not found, incomplete strategy% (30040)------------------------------
% 2.17/0.71  % (30040)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.71  % (30040)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.71  
% 2.17/0.71  % (30040)Memory used [KB]: 1663
% 2.17/0.71  % (30040)Time elapsed: 0.294 s
% 2.17/0.71  % (30040)------------------------------
% 2.17/0.71  % (30040)------------------------------
% 2.17/0.71  % (30072)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.17/0.71  % (30072)Refutation not found, incomplete strategy% (30072)------------------------------
% 2.17/0.71  % (30072)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.71  % (30072)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.71  
% 2.17/0.71  % (30072)Memory used [KB]: 6140
% 2.17/0.71  % (30072)Time elapsed: 0.001 s
% 2.17/0.71  % (30072)------------------------------
% 2.17/0.71  % (30072)------------------------------
% 2.17/0.71  % (30081)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 2.17/0.73  % (30048)Refutation not found, incomplete strategy% (30048)------------------------------
% 2.17/0.73  % (30048)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.73  % (30048)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.73  
% 2.17/0.73  % (30048)Memory used [KB]: 6140
% 2.17/0.73  % (30048)Time elapsed: 0.320 s
% 2.17/0.73  % (30048)------------------------------
% 2.17/0.73  % (30048)------------------------------
% 2.17/0.73  % (30055)Refutation not found, incomplete strategy% (30055)------------------------------
% 2.17/0.73  % (30055)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.73  % (30055)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.73  
% 2.17/0.73  % (30055)Memory used [KB]: 6140
% 2.17/0.73  % (30055)Time elapsed: 0.300 s
% 2.17/0.73  % (30055)------------------------------
% 2.17/0.73  % (30055)------------------------------
% 2.17/0.74  % (30081)Refutation not found, incomplete strategy% (30081)------------------------------
% 2.17/0.74  % (30081)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.74  % (30081)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.74  
% 2.17/0.74  % (30081)Memory used [KB]: 10746
% 2.17/0.74  % (30081)Time elapsed: 0.125 s
% 2.17/0.74  % (30081)------------------------------
% 2.17/0.74  % (30081)------------------------------
% 2.70/0.74  % (30083)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 2.70/0.74  % (30083)Refutation not found, incomplete strategy% (30083)------------------------------
% 2.70/0.74  % (30083)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.70/0.74  % (30083)Termination reason: Refutation not found, incomplete strategy
% 2.70/0.74  
% 2.70/0.74  % (30083)Memory used [KB]: 10746
% 2.70/0.74  % (30083)Time elapsed: 0.128 s
% 2.70/0.74  % (30083)------------------------------
% 2.70/0.74  % (30083)------------------------------
% 2.70/0.75  % (30085)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 2.70/0.77  % (30086)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 2.89/0.77  % (30088)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 2.89/0.77  % (30084)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 2.89/0.80  % (30078)Refutation not found, incomplete strategy% (30078)------------------------------
% 2.89/0.80  % (30078)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.89/0.80  % (30090)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 2.89/0.81  % (30087)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 2.89/0.81  % (30078)Termination reason: Refutation not found, incomplete strategy
% 2.89/0.81  
% 2.89/0.81  % (30078)Memory used [KB]: 6268
% 2.89/0.81  % (30078)Time elapsed: 0.199 s
% 2.89/0.81  % (30078)------------------------------
% 2.89/0.81  % (30078)------------------------------
% 2.89/0.81  % (30089)dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 2.89/0.81  % (30089)Refutation not found, incomplete strategy% (30089)------------------------------
% 2.89/0.81  % (30089)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.89/0.81  % (30089)Termination reason: Refutation not found, incomplete strategy
% 2.89/0.81  
% 2.89/0.81  % (30089)Memory used [KB]: 1663
% 2.89/0.81  % (30089)Time elapsed: 0.105 s
% 2.89/0.81  % (30089)------------------------------
% 2.89/0.81  % (30089)------------------------------
% 3.29/0.84  % (30085)Refutation not found, incomplete strategy% (30085)------------------------------
% 3.29/0.84  % (30085)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.29/0.84  % (30085)Termination reason: Refutation not found, incomplete strategy
% 3.29/0.84  
% 3.29/0.84  % (30085)Memory used [KB]: 6140
% 3.29/0.84  % (30085)Time elapsed: 0.023 s
% 3.29/0.84  % (30085)------------------------------
% 3.29/0.84  % (30085)------------------------------
% 3.29/0.85  % (30088)Refutation not found, incomplete strategy% (30088)------------------------------
% 3.29/0.85  % (30088)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.29/0.85  % (30088)Termination reason: Refutation not found, incomplete strategy
% 3.29/0.85  
% 3.29/0.85  % (30088)Memory used [KB]: 6140
% 3.29/0.85  % (30088)Time elapsed: 0.106 s
% 3.29/0.85  % (30088)------------------------------
% 3.29/0.85  % (30088)------------------------------
% 3.56/0.89  % (30084)Refutation not found, incomplete strategy% (30084)------------------------------
% 3.56/0.89  % (30084)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.56/0.89  % (30084)Termination reason: Refutation not found, incomplete strategy
% 3.56/0.89  
% 3.56/0.89  % (30084)Memory used [KB]: 6140
% 3.56/0.89  % (30084)Time elapsed: 0.249 s
% 3.56/0.89  % (30084)------------------------------
% 3.56/0.89  % (30084)------------------------------
% 4.00/0.95  % (30046)Time limit reached!
% 4.00/0.95  % (30046)------------------------------
% 4.00/0.95  % (30046)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.00/0.95  % (30046)Termination reason: Time limit
% 4.00/0.95  % (30046)Termination phase: Saturation
% 4.00/0.95  
% 4.00/0.95  % (30046)Memory used [KB]: 12153
% 4.00/0.95  % (30046)Time elapsed: 0.500 s
% 4.00/0.95  % (30046)------------------------------
% 4.00/0.95  % (30046)------------------------------
% 4.65/1.07  % (30047)Time limit reached!
% 4.65/1.07  % (30047)------------------------------
% 4.65/1.07  % (30047)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.65/1.07  % (30047)Termination reason: Time limit
% 4.65/1.07  % (30047)Termination phase: Saturation
% 4.65/1.07  
% 4.65/1.07  % (30047)Memory used [KB]: 2942
% 4.65/1.07  % (30047)Time elapsed: 0.600 s
% 4.65/1.07  % (30047)------------------------------
% 4.65/1.07  % (30047)------------------------------
% 5.74/1.12  % (30087)Time limit reached!
% 5.74/1.12  % (30087)------------------------------
% 5.74/1.12  % (30087)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.74/1.12  % (30087)Termination reason: Time limit
% 5.74/1.12  
% 5.74/1.12  % (30087)Memory used [KB]: 6780
% 5.74/1.12  % (30087)Time elapsed: 0.415 s
% 5.74/1.12  % (30087)------------------------------
% 5.74/1.12  % (30087)------------------------------
% 5.74/1.13  % (30090)Time limit reached!
% 5.74/1.13  % (30090)------------------------------
% 5.74/1.13  % (30090)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.74/1.13  % (30090)Termination reason: Time limit
% 5.74/1.13  
% 5.74/1.13  % (30090)Memory used [KB]: 7419
% 5.74/1.13  % (30090)Time elapsed: 0.415 s
% 5.74/1.13  % (30090)------------------------------
% 5.74/1.13  % (30090)------------------------------
% 6.44/1.19  % SZS status CounterSatisfiable for theBenchmark
% 6.44/1.19  % (30045)# SZS output start Saturation.
% 6.44/1.19  cnf(u63,negated_conjecture,
% 6.44/1.19      ~v2_waybel_0(k2_tarski(sK1,sK1),sK0) | ~v1_waybel_0(k2_tarski(sK1,sK1),sK0)).
% 6.44/1.19  
% 6.44/1.19  cnf(u64,negated_conjecture,
% 6.44/1.19      v6_orders_2(k2_tarski(sK1,sK1),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)).
% 6.44/1.19  
% 6.44/1.19  cnf(u35,axiom,
% 6.44/1.19      v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)).
% 6.44/1.19  
% 6.44/1.19  cnf(u39,axiom,
% 6.44/1.19      r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)).
% 6.44/1.19  
% 6.44/1.19  cnf(u30,negated_conjecture,
% 6.44/1.19      v3_orders_2(sK0)).
% 6.44/1.19  
% 6.44/1.19  cnf(u65,negated_conjecture,
% 6.44/1.19      m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)).
% 6.44/1.19  
% 6.44/1.19  cnf(u36,axiom,
% 6.44/1.19      m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)).
% 6.44/1.19  
% 6.44/1.19  cnf(u32,negated_conjecture,
% 6.44/1.19      m1_subset_1(sK1,u1_struct_0(sK0))).
% 6.44/1.19  
% 6.44/1.19  cnf(u58,negated_conjecture,
% 6.44/1.19      ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_tarski(X0,X0) = k6_domain_1(u1_struct_0(sK0),X0) | ~l1_struct_0(sK0)).
% 6.44/1.19  
% 6.44/1.19  cnf(u31,negated_conjecture,
% 6.44/1.19      l1_orders_2(sK0)).
% 6.44/1.19  
% 6.44/1.19  cnf(u47,axiom,
% 6.44/1.19      v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1)).
% 6.44/1.19  
% 6.44/1.19  cnf(u55,negated_conjecture,
% 6.44/1.19      ~v1_xboole_0(u1_struct_0(sK0)) | ~l1_struct_0(sK0)).
% 6.44/1.19  
% 6.44/1.19  cnf(u38,axiom,
% 6.44/1.19      l1_struct_0(X0) | ~l1_orders_2(X0)).
% 6.44/1.19  
% 6.44/1.19  cnf(u37,axiom,
% 6.44/1.19      v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0))).
% 6.44/1.19  
% 6.44/1.19  cnf(u29,negated_conjecture,
% 6.44/1.19      ~v2_struct_0(sK0)).
% 6.44/1.19  
% 6.44/1.19  cnf(u43,axiom,
% 6.44/1.19      r2_hidden(sK2(X0,X1,X2),X2) | sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | k2_tarski(X0,X1) = X2).
% 6.44/1.19  
% 6.44/1.19  cnf(u51,axiom,
% 6.44/1.19      r2_hidden(X4,k2_tarski(X4,X1))).
% 6.44/1.19  
% 6.44/1.19  cnf(u49,axiom,
% 6.44/1.19      r2_hidden(X4,k2_tarski(X0,X4))).
% 6.44/1.19  
% 6.44/1.19  cnf(u911,axiom,
% 6.44/1.19      ~r2_hidden(X40,k2_tarski(X40,X40)) | k2_tarski(X40,X40) = k2_tarski(X39,X40) | sK2(X39,X40,k2_tarski(X40,X40)) = X39).
% 6.44/1.19  
% 6.44/1.19  cnf(u1661,axiom,
% 6.44/1.19      ~r2_hidden(X58,k2_tarski(X58,X58)) | k2_tarski(X58,X59) = k2_tarski(X58,X58) | sK2(X58,X59,k2_tarski(X58,X58)) = X59).
% 6.44/1.19  
% 6.44/1.19  cnf(u193,axiom,
% 6.44/1.19      ~r2_hidden(X12,k2_tarski(X12,X13)) | k2_tarski(X12,X12) = k2_tarski(X12,X13) | sK2(X12,X12,k2_tarski(X12,X13)) = X13).
% 6.44/1.19  
% 6.44/1.19  cnf(u792,axiom,
% 6.44/1.19      ~r2_hidden(X38,k2_tarski(X38,X37)) | k2_tarski(X38,X37) = k2_tarski(X37,X38)).
% 6.44/1.19  
% 6.44/1.19  cnf(u389,axiom,
% 6.44/1.19      ~r2_hidden(X19,k2_tarski(X19,X20)) | k2_tarski(X19,X20) = k2_tarski(X18,X19) | sK2(X18,X19,k2_tarski(X19,X20)) = X18 | sK2(X18,X19,k2_tarski(X19,X20)) = X20).
% 6.44/1.19  
% 6.44/1.19  cnf(u545,axiom,
% 6.44/1.19      ~r2_hidden(X27,k2_tarski(X27,X29)) | k2_tarski(X27,X29) = k2_tarski(X27,X28) | sK2(X27,X28,k2_tarski(X27,X29)) = X28 | sK2(X27,X28,k2_tarski(X27,X29)) = X29).
% 6.44/1.19  
% 6.44/1.19  cnf(u2431,axiom,
% 6.44/1.19      ~r2_hidden(X260,k2_tarski(X259,X259)) | k2_tarski(X259,X259) = k2_tarski(sK2(X257,X258,k2_tarski(X259,X259)),X260) | sK2(sK2(X257,X258,k2_tarski(X259,X259)),X260,k2_tarski(X259,X259)) = X259 | sK2(X257,X258,k2_tarski(X259,X259)) = X258 | sK2(X257,X258,k2_tarski(X259,X259)) = X257 | k2_tarski(X259,X259) = k2_tarski(X257,X258)).
% 6.44/1.19  
% 6.44/1.19  cnf(u2423,axiom,
% 6.44/1.19      ~r2_hidden(X228,k2_tarski(X227,X227)) | k2_tarski(X227,X227) = k2_tarski(X228,sK2(X225,X226,k2_tarski(X227,X227))) | sK2(X228,sK2(X225,X226,k2_tarski(X227,X227)),k2_tarski(X227,X227)) = X227 | sK2(X225,X226,k2_tarski(X227,X227)) = X226 | sK2(X225,X226,k2_tarski(X227,X227)) = X225 | k2_tarski(X227,X227) = k2_tarski(X225,X226)).
% 6.44/1.19  
% 6.44/1.19  cnf(u2369,axiom,
% 6.44/1.19      ~r2_hidden(X9,k2_tarski(X8,X8)) | sK2(X6,X7,k2_tarski(X8,X8)) = X9 | X8 = X9 | sK2(X6,X7,k2_tarski(X8,X8)) = X7 | sK2(X6,X7,k2_tarski(X8,X8)) = X6 | k2_tarski(X6,X7) = k2_tarski(X8,X8)).
% 6.44/1.19  
% 6.44/1.19  cnf(u1713,axiom,
% 6.44/1.19      ~r2_hidden(X65,k2_tarski(X64,X64)) | k2_tarski(X64,X65) = k2_tarski(X64,X64)).
% 6.44/1.19  
% 6.44/1.19  cnf(u1587,axiom,
% 6.44/1.19      ~r2_hidden(X59,k2_tarski(X60,X60)) | k2_tarski(X60,X60) = k2_tarski(X59,X60)).
% 6.44/1.19  
% 6.44/1.19  cnf(u772,axiom,
% 6.44/1.19      ~r2_hidden(X45,k2_tarski(X46,X46)) | k2_tarski(X44,X45) = k2_tarski(X46,X46) | sK2(X44,X45,k2_tarski(X46,X46)) = X44 | sK2(X44,X45,k2_tarski(X46,X46)) = X46).
% 6.44/1.19  
% 6.44/1.19  cnf(u770,axiom,
% 6.44/1.19      ~r2_hidden(X41,k2_tarski(X43,X43)) | k2_tarski(X43,X43) = k2_tarski(X41,X42) | sK2(X41,X42,k2_tarski(X43,X43)) = X42 | sK2(X41,X42,k2_tarski(X43,X43)) = X43).
% 6.44/1.19  
% 6.44/1.19  cnf(u322,axiom,
% 6.44/1.19      ~r2_hidden(X12,k2_tarski(X13,X13)) | k2_tarski(X12,X12) = k2_tarski(X13,X13) | sK2(X12,X12,k2_tarski(X13,X13)) = X13).
% 6.44/1.19  
% 6.44/1.19  cnf(u254,axiom,
% 6.44/1.19      ~r2_hidden(X12,k2_tarski(X13,X12)) | k2_tarski(X12,X12) = k2_tarski(X13,X12) | sK2(X12,X12,k2_tarski(X13,X12)) = X13).
% 6.44/1.19  
% 6.44/1.19  cnf(u674,axiom,
% 6.44/1.19      ~r2_hidden(X28,k2_tarski(X29,X28)) | k2_tarski(X29,X28) = k2_tarski(X28,X29) | sK2(X28,X29,k2_tarski(X29,X28)) = X29).
% 6.44/1.19  
% 6.44/1.19  cnf(u458,axiom,
% 6.44/1.19      ~r2_hidden(X25,k2_tarski(X26,X25)) | k2_tarski(X26,X25) = k2_tarski(X24,X25) | sK2(X24,X25,k2_tarski(X26,X25)) = X24 | sK2(X24,X25,k2_tarski(X26,X25)) = X26).
% 6.44/1.19  
% 6.44/1.19  cnf(u633,axiom,
% 6.44/1.19      ~r2_hidden(X33,k2_tarski(X35,X33)) | k2_tarski(X33,X34) = k2_tarski(X35,X33) | sK2(X33,X34,k2_tarski(X35,X33)) = X34 | sK2(X33,X34,k2_tarski(X35,X33)) = X35).
% 6.44/1.19  
% 6.44/1.19  cnf(u2184,axiom,
% 6.44/1.19      ~r2_hidden(X2,k2_tarski(X1,X0)) | k2_tarski(X1,X0) = k2_tarski(X0,X2) | sK2(X0,X2,k2_tarski(X1,X0)) = X1).
% 6.44/1.19  
% 6.44/1.19  cnf(u2167,axiom,
% 6.44/1.19      ~r2_hidden(X96,k2_tarski(X95,X97)) | k2_tarski(X95,X96) = k2_tarski(X95,X97) | sK2(X95,X96,k2_tarski(X95,X97)) = X97).
% 6.44/1.19  
% 6.44/1.19  cnf(u1887,axiom,
% 6.44/1.19      ~r2_hidden(X2,k2_tarski(X1,X0)) | k2_tarski(X1,X0) = k2_tarski(X2,X0) | sK2(X2,X0,k2_tarski(X1,X0)) = X1).
% 6.44/1.19  
% 6.44/1.19  cnf(u1865,axiom,
% 6.44/1.19      ~r2_hidden(X87,k2_tarski(X88,X89)) | k2_tarski(X88,X89) = k2_tarski(X87,X88) | sK2(X87,X88,k2_tarski(X88,X89)) = X89).
% 6.44/1.19  
% 6.44/1.19  cnf(u1473,axiom,
% 6.44/1.19      ~r2_hidden(X79,k2_tarski(X82,X83)) | k2_tarski(X82,X83) = k2_tarski(X79,sK2(X80,X81,k2_tarski(X82,X83))) | sK2(X79,sK2(X80,X81,k2_tarski(X82,X83)),k2_tarski(X82,X83)) = X82 | sK2(X79,sK2(X80,X81,k2_tarski(X82,X83)),k2_tarski(X82,X83)) = X83 | sK2(X80,X81,k2_tarski(X82,X83)) = X81 | sK2(X80,X81,k2_tarski(X82,X83)) = X80 | k2_tarski(X82,X83) = k2_tarski(X80,X81)).
% 6.44/1.19  
% 6.44/1.19  cnf(u1143,axiom,
% 6.44/1.19      ~r2_hidden(X76,k2_tarski(X74,X75)) | k2_tarski(X74,X75) = k2_tarski(sK2(X72,X73,k2_tarski(X74,X75)),X76) | sK2(sK2(X72,X73,k2_tarski(X74,X75)),X76,k2_tarski(X74,X75)) = X74 | sK2(sK2(X72,X73,k2_tarski(X74,X75)),X76,k2_tarski(X74,X75)) = X75 | sK2(X72,X73,k2_tarski(X74,X75)) = X73 | sK2(X72,X73,k2_tarski(X74,X75)) = X72 | k2_tarski(X72,X73) = k2_tarski(X74,X75)).
% 6.44/1.19  
% 6.44/1.19  cnf(u638,axiom,
% 6.44/1.19      ~r2_hidden(X37,k2_tarski(X38,X36)) | k2_tarski(X36,X37) = k2_tarski(X38,X36) | sK2(X36,X37,k2_tarski(X38,X36)) = X38 | sK2(X36,X37,k2_tarski(X38,X36)) = X36).
% 6.44/1.19  
% 6.44/1.19  cnf(u547,axiom,
% 6.44/1.19      ~r2_hidden(X31,k2_tarski(X30,X32)) | k2_tarski(X30,X32) = k2_tarski(X30,X31) | sK2(X30,X31,k2_tarski(X30,X32)) = X30 | sK2(X30,X31,k2_tarski(X30,X32)) = X32).
% 6.44/1.19  
% 6.44/1.19  cnf(u465,axiom,
% 6.44/1.19      ~r2_hidden(X21,k2_tarski(X23,X22)) | k2_tarski(X23,X22) = k2_tarski(X21,X22) | sK2(X21,X22,k2_tarski(X23,X22)) = X23 | sK2(X21,X22,k2_tarski(X23,X22)) = X22).
% 6.44/1.19  
% 6.44/1.19  cnf(u393,axiom,
% 6.44/1.19      ~r2_hidden(X15,k2_tarski(X16,X17)) | k2_tarski(X16,X17) = k2_tarski(X15,X16) | sK2(X15,X16,k2_tarski(X16,X17)) = X16 | sK2(X15,X16,k2_tarski(X16,X17)) = X17).
% 6.44/1.19  
% 6.44/1.19  cnf(u160,axiom,
% 6.44/1.19      ~r2_hidden(X18,k2_tarski(X19,X20)) | k2_tarski(X19,X20) = k2_tarski(X18,X18) | sK2(X18,X18,k2_tarski(X19,X20)) = X19 | sK2(X18,X18,k2_tarski(X19,X20)) = X20).
% 6.44/1.19  
% 6.44/1.19  cnf(u113,axiom,
% 6.44/1.19      ~r2_hidden(X9,k2_tarski(X10,X11)) | k2_tarski(X10,X11) = k2_tarski(X8,X9) | sK2(X8,X9,k2_tarski(X10,X11)) = X8 | sK2(X8,X9,k2_tarski(X10,X11)) = X10 | sK2(X8,X9,k2_tarski(X10,X11)) = X11).
% 6.44/1.19  
% 6.44/1.19  cnf(u111,axiom,
% 6.44/1.19      ~r2_hidden(X4,k2_tarski(X6,X7)) | k2_tarski(X6,X7) = k2_tarski(X4,X5) | sK2(X4,X5,k2_tarski(X6,X7)) = X5 | sK2(X4,X5,k2_tarski(X6,X7)) = X6 | sK2(X4,X5,k2_tarski(X6,X7)) = X7).
% 6.44/1.19  
% 6.44/1.19  cnf(u52,axiom,
% 6.44/1.19      ~r2_hidden(X4,k2_tarski(X0,X1)) | X0 = X4 | X1 = X4).
% 6.44/1.19  
% 6.44/1.19  cnf(u1719,axiom,
% 6.44/1.19      k2_tarski(X2,X2) = k2_tarski(X2,sK2(X3,X4,k2_tarski(X2,X2))) | sK2(X3,X4,k2_tarski(X2,X2)) = X4 | sK2(X3,X4,k2_tarski(X2,X2)) = X3 | k2_tarski(X2,X2) = k2_tarski(X3,X4)).
% 6.44/1.19  
% 6.44/1.19  cnf(u1592,axiom,
% 6.44/1.19      k2_tarski(X2,X2) = k2_tarski(sK2(X3,X4,k2_tarski(X2,X2)),X2) | sK2(X3,X4,k2_tarski(X2,X2)) = X4 | sK2(X3,X4,k2_tarski(X2,X2)) = X3 | k2_tarski(X2,X2) = k2_tarski(X3,X4)).
% 6.44/1.19  
% 6.44/1.19  cnf(u797,axiom,
% 6.44/1.19      k2_tarski(X1,X2) = k2_tarski(X2,X1)).
% 6.44/1.19  
% 6.44/1.19  cnf(u2180,axiom,
% 6.44/1.19      sK2(sK2(X5,X6,k2_tarski(X4,X4)),X7,k2_tarski(X4,X4)) = X7 | sK2(sK2(X5,X6,k2_tarski(X4,X4)),X7,k2_tarski(X4,X4)) = X4 | k2_tarski(X4,X4) = k2_tarski(sK2(X5,X6,k2_tarski(X4,X4)),X7) | sK2(X5,X6,k2_tarski(X4,X4)) = X6 | sK2(X5,X6,k2_tarski(X4,X4)) = X5 | k2_tarski(X4,X4) = k2_tarski(X5,X6)).
% 6.44/1.19  
% 6.44/1.19  cnf(u2180,axiom,
% 6.44/1.19      sK2(sK2(X5,X6,k2_tarski(X4,X4)),X7,k2_tarski(X4,X4)) = X7 | sK2(sK2(X5,X6,k2_tarski(X4,X4)),X7,k2_tarski(X4,X4)) = X4 | k2_tarski(X4,X4) = k2_tarski(sK2(X5,X6,k2_tarski(X4,X4)),X7) | sK2(X5,X6,k2_tarski(X4,X4)) = X6 | sK2(X5,X6,k2_tarski(X4,X4)) = X5 | k2_tarski(X4,X4) = k2_tarski(X5,X6)).
% 6.44/1.19  
% 6.44/1.19  cnf(u4998,axiom,
% 6.44/1.19      sK2(sK2(X0,X1,k2_tarski(X2,X2)),sK2(X3,X4,k2_tarski(X2,X2)),k2_tarski(X2,X2)) = X2 | k2_tarski(X2,X2) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X2)),sK2(X3,X4,k2_tarski(X2,X2))) | sK2(X0,X1,k2_tarski(X2,X2)) = X1 | sK2(X0,X1,k2_tarski(X2,X2)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X2) | sK2(X3,X4,k2_tarski(X2,X2)) = X4 | sK2(X3,X4,k2_tarski(X2,X2)) = X3 | k2_tarski(X2,X2) = k2_tarski(X3,X4)).
% 6.44/1.19  
% 6.44/1.19  cnf(u2579,axiom,
% 6.44/1.19      sK2(sK2(X16,X17,k2_tarski(X15,X15)),sK2(X13,X14,k2_tarski(X15,X15)),k2_tarski(X15,X15)) = X15 | k2_tarski(X15,X15) = k2_tarski(sK2(X13,X14,k2_tarski(X15,X15)),sK2(X16,X17,k2_tarski(X15,X15))) | sK2(X16,X17,k2_tarski(X15,X15)) = X17 | sK2(X16,X17,k2_tarski(X15,X15)) = X16 | k2_tarski(X16,X17) = k2_tarski(X15,X15) | sK2(X13,X14,k2_tarski(X15,X15)) = X14 | sK2(X13,X14,k2_tarski(X15,X15)) = X13 | k2_tarski(X13,X14) = k2_tarski(X15,X15)).
% 6.44/1.19  
% 6.44/1.19  cnf(u329,axiom,
% 6.44/1.19      sK2(sK2(X2,X3,k2_tarski(X4,X4)),sK2(X2,X3,k2_tarski(X4,X4)),k2_tarski(X4,X4)) = X4 | k2_tarski(X4,X4) = k2_tarski(sK2(X2,X3,k2_tarski(X4,X4)),sK2(X2,X3,k2_tarski(X4,X4))) | sK2(X2,X3,k2_tarski(X4,X4)) = X3 | sK2(X2,X3,k2_tarski(X4,X4)) = X2 | k2_tarski(X2,X3) = k2_tarski(X4,X4)).
% 6.44/1.19  
% 6.44/1.19  cnf(u3148,axiom,
% 6.44/1.19      sK2(sK2(X10,X11,k2_tarski(X8,X9)),sK2(X12,X13,k2_tarski(X8,X9)),k2_tarski(X8,X9)) = X8 | sK2(sK2(X10,X11,k2_tarski(X8,X9)),sK2(X12,X13,k2_tarski(X8,X9)),k2_tarski(X8,X9)) = X9 | k2_tarski(X8,X9) = k2_tarski(sK2(X10,X11,k2_tarski(X8,X9)),sK2(X12,X13,k2_tarski(X8,X9))) | sK2(X10,X11,k2_tarski(X8,X9)) = X11 | sK2(X10,X11,k2_tarski(X8,X9)) = X10 | k2_tarski(X10,X11) = k2_tarski(X8,X9) | sK2(X12,X13,k2_tarski(X8,X9)) = X13 | sK2(X12,X13,k2_tarski(X8,X9)) = X12 | k2_tarski(X8,X9) = k2_tarski(X12,X13)).
% 6.44/1.19  
% 6.44/1.19  cnf(u3148,axiom,
% 6.44/1.19      sK2(sK2(X10,X11,k2_tarski(X8,X9)),sK2(X12,X13,k2_tarski(X8,X9)),k2_tarski(X8,X9)) = X8 | sK2(sK2(X10,X11,k2_tarski(X8,X9)),sK2(X12,X13,k2_tarski(X8,X9)),k2_tarski(X8,X9)) = X9 | k2_tarski(X8,X9) = k2_tarski(sK2(X10,X11,k2_tarski(X8,X9)),sK2(X12,X13,k2_tarski(X8,X9))) | sK2(X10,X11,k2_tarski(X8,X9)) = X11 | sK2(X10,X11,k2_tarski(X8,X9)) = X10 | k2_tarski(X10,X11) = k2_tarski(X8,X9) | sK2(X12,X13,k2_tarski(X8,X9)) = X13 | sK2(X12,X13,k2_tarski(X8,X9)) = X12 | k2_tarski(X8,X9) = k2_tarski(X12,X13)).
% 6.44/1.19  
% 6.44/1.19  cnf(u1734,axiom,
% 6.44/1.19      sK2(sK2(X6,X7,k2_tarski(X4,X5)),sK2(X6,X7,k2_tarski(X4,X5)),k2_tarski(X4,X5)) = X4 | sK2(sK2(X6,X7,k2_tarski(X4,X5)),sK2(X6,X7,k2_tarski(X4,X5)),k2_tarski(X4,X5)) = X5 | k2_tarski(X4,X5) = k2_tarski(sK2(X6,X7,k2_tarski(X4,X5)),sK2(X6,X7,k2_tarski(X4,X5))) | sK2(X6,X7,k2_tarski(X4,X5)) = X7 | sK2(X6,X7,k2_tarski(X4,X5)) = X6 | k2_tarski(X6,X7) = k2_tarski(X4,X5)).
% 6.44/1.19  
% 6.44/1.19  cnf(u1734,axiom,
% 6.44/1.19      sK2(sK2(X6,X7,k2_tarski(X4,X5)),sK2(X6,X7,k2_tarski(X4,X5)),k2_tarski(X4,X5)) = X4 | sK2(sK2(X6,X7,k2_tarski(X4,X5)),sK2(X6,X7,k2_tarski(X4,X5)),k2_tarski(X4,X5)) = X5 | k2_tarski(X4,X5) = k2_tarski(sK2(X6,X7,k2_tarski(X4,X5)),sK2(X6,X7,k2_tarski(X4,X5))) | sK2(X6,X7,k2_tarski(X4,X5)) = X7 | sK2(X6,X7,k2_tarski(X4,X5)) = X6 | k2_tarski(X6,X7) = k2_tarski(X4,X5)).
% 6.44/1.19  
% 6.44/1.19  cnf(u287,axiom,
% 6.44/1.19      sK2(sK2(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X10 | sK2(sK2(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X6 | sK2(sK2(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X7 | k2_tarski(X6,X7) = k2_tarski(sK2(X8,X9,k2_tarski(X6,X7)),X10) | sK2(X8,X9,k2_tarski(X6,X7)) = X9 | sK2(X8,X9,k2_tarski(X6,X7)) = X8 | k2_tarski(X6,X7) = k2_tarski(X8,X9)).
% 6.44/1.19  
% 6.44/1.19  cnf(u287,axiom,
% 6.44/1.19      sK2(sK2(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X10 | sK2(sK2(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X6 | sK2(sK2(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X7 | k2_tarski(X6,X7) = k2_tarski(sK2(X8,X9,k2_tarski(X6,X7)),X10) | sK2(X8,X9,k2_tarski(X6,X7)) = X9 | sK2(X8,X9,k2_tarski(X6,X7)) = X8 | k2_tarski(X6,X7) = k2_tarski(X8,X9)).
% 6.44/1.19  
% 6.44/1.19  cnf(u287,axiom,
% 6.44/1.19      sK2(sK2(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X10 | sK2(sK2(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X6 | sK2(sK2(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X7 | k2_tarski(X6,X7) = k2_tarski(sK2(X8,X9,k2_tarski(X6,X7)),X10) | sK2(X8,X9,k2_tarski(X6,X7)) = X9 | sK2(X8,X9,k2_tarski(X6,X7)) = X8 | k2_tarski(X6,X7) = k2_tarski(X8,X9)).
% 6.44/1.19  
% 6.44/1.19  cnf(u2576,axiom,
% 6.44/1.19      sK2(sK2(X2,X3,k2_tarski(X1,X0)),X0,k2_tarski(X1,X0)) = X1 | k2_tarski(X1,X0) = k2_tarski(X0,sK2(X2,X3,k2_tarski(X1,X0))) | sK2(X2,X3,k2_tarski(X1,X0)) = X3 | sK2(X2,X3,k2_tarski(X1,X0)) = X2 | k2_tarski(X1,X0) = k2_tarski(X2,X3)).
% 6.44/1.19  
% 6.44/1.19  cnf(u1889,axiom,
% 6.44/1.19      sK2(sK2(X6,X7,k2_tarski(X4,X5)),X4,k2_tarski(X4,X5)) = X5 | k2_tarski(X4,X5) = k2_tarski(X4,sK2(X6,X7,k2_tarski(X4,X5))) | sK2(X6,X7,k2_tarski(X4,X5)) = X7 | sK2(X6,X7,k2_tarski(X4,X5)) = X6 | k2_tarski(X6,X7) = k2_tarski(X4,X5)).
% 6.44/1.19  
% 6.44/1.19  cnf(u2183,axiom,
% 6.44/1.19      sK2(X4,sK2(X5,X6,k2_tarski(X4,X7)),k2_tarski(X4,X7)) = X7 | k2_tarski(X4,X7) = k2_tarski(X4,sK2(X5,X6,k2_tarski(X4,X7))) | sK2(X5,X6,k2_tarski(X4,X7)) = X6 | sK2(X5,X6,k2_tarski(X4,X7)) = X5 | k2_tarski(X5,X6) = k2_tarski(X4,X7)).
% 6.44/1.19  
% 6.44/1.19  cnf(u2188,axiom,
% 6.44/1.19      sK2(X4,sK2(X5,X6,k2_tarski(X7,X7)),k2_tarski(X7,X7)) = X4 | sK2(X4,sK2(X5,X6,k2_tarski(X7,X7)),k2_tarski(X7,X7)) = X7 | k2_tarski(X7,X7) = k2_tarski(X4,sK2(X5,X6,k2_tarski(X7,X7))) | sK2(X5,X6,k2_tarski(X7,X7)) = X6 | sK2(X5,X6,k2_tarski(X7,X7)) = X5 | k2_tarski(X7,X7) = k2_tarski(X5,X6)).
% 6.44/1.19  
% 6.44/1.19  cnf(u2188,axiom,
% 6.44/1.19      sK2(X4,sK2(X5,X6,k2_tarski(X7,X7)),k2_tarski(X7,X7)) = X4 | sK2(X4,sK2(X5,X6,k2_tarski(X7,X7)),k2_tarski(X7,X7)) = X7 | k2_tarski(X7,X7) = k2_tarski(X4,sK2(X5,X6,k2_tarski(X7,X7))) | sK2(X5,X6,k2_tarski(X7,X7)) = X6 | sK2(X5,X6,k2_tarski(X7,X7)) = X5 | k2_tarski(X7,X7) = k2_tarski(X5,X6)).
% 6.44/1.19  
% 6.44/1.19  cnf(u2692,axiom,
% 6.44/1.19      sK2(X0,sK2(X2,X3,k2_tarski(X1,X0)),k2_tarski(X1,X0)) = X1 | k2_tarski(X1,X0) = k2_tarski(X0,sK2(X2,X3,k2_tarski(X1,X0))) | sK2(X2,X3,k2_tarski(X1,X0)) = X3 | sK2(X2,X3,k2_tarski(X1,X0)) = X2 | k2_tarski(X1,X0) = k2_tarski(X2,X3)).
% 6.44/1.19  
% 6.44/1.19  cnf(u291,axiom,
% 6.44/1.19      sK2(X8,sK2(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X8 | sK2(X8,sK2(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X6 | sK2(X8,sK2(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X7 | k2_tarski(X6,X7) = k2_tarski(X8,sK2(X9,X10,k2_tarski(X6,X7))) | sK2(X9,X10,k2_tarski(X6,X7)) = X10 | sK2(X9,X10,k2_tarski(X6,X7)) = X9 | k2_tarski(X6,X7) = k2_tarski(X9,X10)).
% 6.44/1.19  
% 6.44/1.19  cnf(u291,axiom,
% 6.44/1.19      sK2(X8,sK2(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X8 | sK2(X8,sK2(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X6 | sK2(X8,sK2(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X7 | k2_tarski(X6,X7) = k2_tarski(X8,sK2(X9,X10,k2_tarski(X6,X7))) | sK2(X9,X10,k2_tarski(X6,X7)) = X10 | sK2(X9,X10,k2_tarski(X6,X7)) = X9 | k2_tarski(X6,X7) = k2_tarski(X9,X10)).
% 6.44/1.19  
% 6.44/1.19  cnf(u291,axiom,
% 6.44/1.19      sK2(X8,sK2(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X8 | sK2(X8,sK2(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X6 | sK2(X8,sK2(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X7 | k2_tarski(X6,X7) = k2_tarski(X8,sK2(X9,X10,k2_tarski(X6,X7))) | sK2(X9,X10,k2_tarski(X6,X7)) = X10 | sK2(X9,X10,k2_tarski(X6,X7)) = X9 | k2_tarski(X6,X7) = k2_tarski(X9,X10)).
% 6.44/1.19  
% 6.44/1.19  cnf(u164,axiom,
% 6.44/1.19      sK2(X0,X0,k2_tarski(X0,X1)) = X0 | sK2(X0,X0,k2_tarski(X0,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X0,X0)).
% 6.44/1.19  
% 6.44/1.19  cnf(u201,axiom,
% 6.44/1.19      sK2(X1,X1,k2_tarski(X1,X2)) = X2 | k2_tarski(X1,X1) = k2_tarski(X1,X2)).
% 6.44/1.19  
% 6.44/1.19  cnf(u164,axiom,
% 6.44/1.19      sK2(X0,X0,k2_tarski(X0,X1)) = X0 | sK2(X0,X0,k2_tarski(X0,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X0,X0)).
% 6.44/1.19  
% 6.44/1.19  cnf(u293,axiom,
% 6.44/1.19      sK2(X0,X0,k2_tarski(X1,X1)) = X0 | sK2(X0,X0,k2_tarski(X1,X1)) = X1 | k2_tarski(X0,X0) = k2_tarski(X1,X1)).
% 6.44/1.19  
% 6.44/1.19  cnf(u293,axiom,
% 6.44/1.19      sK2(X0,X0,k2_tarski(X1,X1)) = X0 | sK2(X0,X0,k2_tarski(X1,X1)) = X1 | k2_tarski(X0,X0) = k2_tarski(X1,X1)).
% 6.44/1.19  
% 6.44/1.19  cnf(u227,axiom,
% 6.44/1.19      sK2(X0,X0,k2_tarski(X1,X0)) = X1 | sK2(X0,X0,k2_tarski(X1,X0)) = X0 | k2_tarski(X0,X0) = k2_tarski(X1,X0)).
% 6.44/1.19  
% 6.44/1.19  cnf(u227,axiom,
% 6.44/1.19      sK2(X0,X0,k2_tarski(X1,X0)) = X1 | sK2(X0,X0,k2_tarski(X1,X0)) = X0 | k2_tarski(X0,X0) = k2_tarski(X1,X0)).
% 6.44/1.19  
% 6.44/1.19  cnf(u264,axiom,
% 6.44/1.19      sK2(X0,X0,k2_tarski(X1,X0)) = X1 | k2_tarski(X0,X0) = k2_tarski(X1,X0)).
% 6.44/1.19  
% 6.44/1.19  cnf(u115,axiom,
% 6.44/1.19      sK2(X0,X0,k2_tarski(X1,X2)) = X0 | sK2(X0,X0,k2_tarski(X1,X2)) = X1 | sK2(X0,X0,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X0) = k2_tarski(X1,X2)).
% 6.44/1.19  
% 6.44/1.19  cnf(u115,axiom,
% 6.44/1.19      sK2(X0,X0,k2_tarski(X1,X2)) = X0 | sK2(X0,X0,k2_tarski(X1,X2)) = X1 | sK2(X0,X0,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X0) = k2_tarski(X1,X2)).
% 6.44/1.19  
% 6.44/1.19  cnf(u115,axiom,
% 6.44/1.19      sK2(X0,X0,k2_tarski(X1,X2)) = X0 | sK2(X0,X0,k2_tarski(X1,X2)) = X1 | sK2(X0,X0,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X0) = k2_tarski(X1,X2)).
% 6.44/1.19  
% 6.44/1.19  cnf(u1604,axiom,
% 6.44/1.19      sK2(X0,X1,k2_tarski(X0,X0)) = X1 | sK2(X0,X1,k2_tarski(X0,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X0,X0)).
% 6.44/1.19  
% 6.44/1.19  cnf(u1604,axiom,
% 6.44/1.19      sK2(X0,X1,k2_tarski(X0,X0)) = X1 | sK2(X0,X1,k2_tarski(X0,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X0,X0)).
% 6.44/1.19  
% 6.44/1.19  cnf(u1672,axiom,
% 6.44/1.19      sK2(X0,X1,k2_tarski(X0,X0)) = X1 | k2_tarski(X0,X1) = k2_tarski(X0,X0)).
% 6.44/1.19  
% 6.44/1.19  cnf(u202,axiom,
% 6.44/1.19      sK2(X0,X1,k2_tarski(X0,X2)) = X1 | sK2(X0,X1,k2_tarski(X0,X2)) = X0 | sK2(X0,X1,k2_tarski(X0,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 6.44/1.19  
% 6.44/1.19  cnf(u1903,axiom,
% 6.44/1.19      sK2(X2,X4,k2_tarski(X2,X3)) = X4 | sK2(X2,X4,k2_tarski(X2,X3)) = X3 | k2_tarski(X2,X3) = k2_tarski(X2,X4)).
% 6.44/1.19  
% 6.44/1.19  cnf(u202,axiom,
% 6.44/1.19      sK2(X0,X1,k2_tarski(X0,X2)) = X1 | sK2(X0,X1,k2_tarski(X0,X2)) = X0 | sK2(X0,X1,k2_tarski(X0,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 6.44/1.19  
% 6.44/1.19  cnf(u202,axiom,
% 6.44/1.19      sK2(X0,X1,k2_tarski(X0,X2)) = X1 | sK2(X0,X1,k2_tarski(X0,X2)) = X0 | sK2(X0,X1,k2_tarski(X0,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 6.44/1.19  
% 6.44/1.19  cnf(u1903,axiom,
% 6.44/1.19      sK2(X2,X4,k2_tarski(X2,X3)) = X4 | sK2(X2,X4,k2_tarski(X2,X3)) = X3 | k2_tarski(X2,X3) = k2_tarski(X2,X4)).
% 6.44/1.19  
% 6.44/1.19  cnf(u873,axiom,
% 6.44/1.19      sK2(X0,X1,k2_tarski(X1,X1)) = X0 | sK2(X0,X1,k2_tarski(X1,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X1,X1)).
% 6.44/1.19  
% 6.44/1.19  cnf(u873,axiom,
% 6.44/1.19      sK2(X0,X1,k2_tarski(X1,X1)) = X0 | sK2(X0,X1,k2_tarski(X1,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X1,X1)).
% 6.44/1.19  
% 6.44/1.19  cnf(u1545,axiom,
% 6.44/1.19      sK2(X1,X0,k2_tarski(X0,X0)) = X1 | k2_tarski(X0,X0) = k2_tarski(X1,X0)).
% 6.44/1.19  
% 6.44/1.19  cnf(u641,axiom,
% 6.44/1.19      sK2(X0,X1,k2_tarski(X1,X0)) = X1 | sK2(X0,X1,k2_tarski(X1,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X1,X0)).
% 6.44/1.19  
% 6.44/1.19  cnf(u641,axiom,
% 6.44/1.19      sK2(X0,X1,k2_tarski(X1,X0)) = X1 | sK2(X0,X1,k2_tarski(X1,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X1,X0)).
% 6.44/1.19  
% 6.44/1.19  cnf(u774,axiom,
% 6.44/1.19      sK2(X1,X0,k2_tarski(X0,X1)) = X0 | k2_tarski(X0,X1) = k2_tarski(X1,X0)).
% 6.44/1.19  
% 6.44/1.19  cnf(u163,axiom,
% 6.44/1.19      sK2(X0,X1,k2_tarski(X1,X2)) = X0 | sK2(X0,X1,k2_tarski(X1,X2)) = X1 | sK2(X0,X1,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 6.44/1.19  
% 6.44/1.19  cnf(u1738,axiom,
% 6.44/1.19      sK2(X4,X2,k2_tarski(X2,X3)) = X4 | sK2(X4,X2,k2_tarski(X2,X3)) = X3 | k2_tarski(X2,X3) = k2_tarski(X4,X2)).
% 6.44/1.19  
% 6.44/1.19  cnf(u163,axiom,
% 6.44/1.19      sK2(X0,X1,k2_tarski(X1,X2)) = X0 | sK2(X0,X1,k2_tarski(X1,X2)) = X1 | sK2(X0,X1,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 6.44/1.19  
% 6.44/1.19  cnf(u163,axiom,
% 6.44/1.19      sK2(X0,X1,k2_tarski(X1,X2)) = X0 | sK2(X0,X1,k2_tarski(X1,X2)) = X1 | sK2(X0,X1,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 6.44/1.19  
% 6.44/1.19  cnf(u1738,axiom,
% 6.44/1.19      sK2(X4,X2,k2_tarski(X2,X3)) = X4 | sK2(X4,X2,k2_tarski(X2,X3)) = X3 | k2_tarski(X2,X3) = k2_tarski(X4,X2)).
% 6.44/1.19  
% 6.44/1.19  cnf(u66,axiom,
% 6.44/1.19      sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | sK2(X0,X1,k2_tarski(X2,X3)) = X2 | sK2(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 6.44/1.19  
% 6.44/1.19  cnf(u66,axiom,
% 6.44/1.19      sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | sK2(X0,X1,k2_tarski(X2,X3)) = X2 | sK2(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 6.44/1.19  
% 6.44/1.19  cnf(u66,axiom,
% 6.44/1.19      sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | sK2(X0,X1,k2_tarski(X2,X3)) = X2 | sK2(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 6.44/1.19  
% 6.44/1.19  cnf(u66,axiom,
% 6.44/1.19      sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | sK2(X0,X1,k2_tarski(X2,X3)) = X2 | sK2(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 6.44/1.19  
% 6.44/1.19  cnf(u226,axiom,
% 6.44/1.19      sK2(X0,X1,k2_tarski(X2,X2)) = X1 | sK2(X0,X1,k2_tarski(X2,X2)) = X0 | sK2(X0,X1,k2_tarski(X2,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 6.44/1.19  
% 6.44/1.19  cnf(u226,axiom,
% 6.44/1.19      sK2(X0,X1,k2_tarski(X2,X2)) = X1 | sK2(X0,X1,k2_tarski(X2,X2)) = X0 | sK2(X0,X1,k2_tarski(X2,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 6.44/1.19  
% 6.44/1.19  cnf(u226,axiom,
% 6.44/1.19      sK2(X0,X1,k2_tarski(X2,X2)) = X1 | sK2(X0,X1,k2_tarski(X2,X2)) = X0 | sK2(X0,X1,k2_tarski(X2,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 6.44/1.19  
% 6.44/1.19  cnf(u196,axiom,
% 6.44/1.19      sK2(X0,X1,k2_tarski(X2,X1)) = X0 | sK2(X0,X1,k2_tarski(X2,X1)) = X2 | sK2(X0,X1,k2_tarski(X2,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 6.44/1.19  
% 6.44/1.19  cnf(u196,axiom,
% 6.44/1.19      sK2(X0,X1,k2_tarski(X2,X1)) = X0 | sK2(X0,X1,k2_tarski(X2,X1)) = X2 | sK2(X0,X1,k2_tarski(X2,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 6.44/1.19  
% 6.44/1.19  cnf(u1880,axiom,
% 6.44/1.19      sK2(X2,X1,k2_tarski(X0,X1)) = X2 | sK2(X2,X1,k2_tarski(X0,X1)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 6.44/1.19  
% 6.44/1.19  cnf(u196,axiom,
% 6.44/1.19      sK2(X0,X1,k2_tarski(X2,X1)) = X0 | sK2(X0,X1,k2_tarski(X2,X1)) = X2 | sK2(X0,X1,k2_tarski(X2,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 6.44/1.19  
% 6.44/1.19  cnf(u1880,axiom,
% 6.44/1.19      sK2(X2,X1,k2_tarski(X0,X1)) = X2 | sK2(X2,X1,k2_tarski(X0,X1)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 6.44/1.19  
% 6.44/1.19  cnf(u222,axiom,
% 6.44/1.19      sK2(X0,X1,k2_tarski(X2,X0)) = X1 | sK2(X0,X1,k2_tarski(X2,X0)) = X2 | sK2(X0,X1,k2_tarski(X2,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 6.44/1.19  
% 6.44/1.19  cnf(u222,axiom,
% 6.44/1.19      sK2(X0,X1,k2_tarski(X2,X0)) = X1 | sK2(X0,X1,k2_tarski(X2,X0)) = X2 | sK2(X0,X1,k2_tarski(X2,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 6.44/1.19  
% 6.44/1.19  cnf(u2036,axiom,
% 6.44/1.19      sK2(X0,X1,k2_tarski(X2,X0)) = X1 | sK2(X0,X1,k2_tarski(X2,X0)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 6.44/1.19  
% 6.44/1.19  cnf(u222,axiom,
% 6.44/1.19      sK2(X0,X1,k2_tarski(X2,X0)) = X1 | sK2(X0,X1,k2_tarski(X2,X0)) = X2 | sK2(X0,X1,k2_tarski(X2,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 6.44/1.19  
% 6.44/1.19  cnf(u2036,axiom,
% 6.44/1.19      sK2(X0,X1,k2_tarski(X2,X0)) = X1 | sK2(X0,X1,k2_tarski(X2,X0)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 6.44/1.19  
% 6.44/1.19  cnf(u61,negated_conjecture,
% 6.44/1.19      k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)).
% 6.44/1.19  
% 6.44/1.19  cnf(u4614,axiom,
% 6.44/1.19      X2 != X3 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X4,X5,k2_tarski(X2,X3)),k2_tarski(X2,X3)) = X2 | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X4,X5,k2_tarski(X2,X3))) | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X3) | sK2(X4,X5,k2_tarski(X2,X3)) = X5 | sK2(X4,X5,k2_tarski(X2,X3)) = X4 | k2_tarski(X2,X3) = k2_tarski(X4,X5)).
% 6.44/1.19  
% 6.44/1.19  cnf(u4613,axiom,
% 6.44/1.19      X2 != X3 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X4,X5,k2_tarski(X2,X3)),k2_tarski(X2,X3)) = X3 | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X4,X5,k2_tarski(X2,X3))) | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X3) | sK2(X4,X5,k2_tarski(X2,X3)) = X5 | sK2(X4,X5,k2_tarski(X2,X3)) = X4 | k2_tarski(X2,X3) = k2_tarski(X4,X5)).
% 6.44/1.19  
% 6.44/1.19  cnf(u4141,axiom,
% 6.44/1.19      X2 != X3 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X0,X1,k2_tarski(X2,X3)),k2_tarski(X2,X3)) = X2 | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X0,X1,k2_tarski(X2,X3))) | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 6.44/1.19  
% 6.44/1.19  cnf(u4140,axiom,
% 6.44/1.19      X2 != X3 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X0,X1,k2_tarski(X2,X3)),k2_tarski(X2,X3)) = X3 | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X0,X1,k2_tarski(X2,X3))) | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 6.44/1.19  
% 6.44/1.19  cnf(u3664,axiom,
% 6.44/1.19      X0 != X3 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X3)),k2_tarski(X3,X3)) = X0 | k2_tarski(X3,X3) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X3))) | sK2(X1,X2,k2_tarski(X3,X3)) = X2 | sK2(X1,X2,k2_tarski(X3,X3)) = X1 | k2_tarski(X1,X2) = k2_tarski(X3,X3)).
% 6.44/1.19  
% 6.44/1.19  cnf(u3663,axiom,
% 6.44/1.19      X0 != X3 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X3)),k2_tarski(X3,X3)) = X3 | k2_tarski(X3,X3) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X3))) | sK2(X1,X2,k2_tarski(X3,X3)) = X2 | sK2(X1,X2,k2_tarski(X3,X3)) = X1 | k2_tarski(X1,X2) = k2_tarski(X3,X3)).
% 6.44/1.19  
% 6.44/1.19  cnf(u3383,axiom,
% 6.44/1.19      X2 != X3 | sK2(sK2(X0,X1,k2_tarski(X2,X2)),X3,k2_tarski(X2,X2)) = X3 | k2_tarski(X2,X2) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X2)),X3) | sK2(X0,X1,k2_tarski(X2,X2)) = X1 | sK2(X0,X1,k2_tarski(X2,X2)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 6.44/1.19  
% 6.44/1.19  cnf(u3382,axiom,
% 6.44/1.19      X2 != X3 | sK2(sK2(X0,X1,k2_tarski(X2,X2)),X3,k2_tarski(X2,X2)) = X2 | k2_tarski(X2,X2) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X2)),X3) | sK2(X0,X1,k2_tarski(X2,X2)) = X1 | sK2(X0,X1,k2_tarski(X2,X2)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 6.44/1.19  
% 6.44/1.19  cnf(u2885,axiom,
% 6.44/1.19      X138 != X139 | k2_tarski(X138,X139) = k2_tarski(X139,sK2(X136,X137,k2_tarski(X138,X139))) | ~r2_hidden(X139,k2_tarski(X138,X139)) | sK2(X136,X137,k2_tarski(X138,X139)) = X137 | sK2(X136,X137,k2_tarski(X138,X139)) = X136 | k2_tarski(X138,X139) = k2_tarski(X136,X137)).
% 6.44/1.19  
% 6.44/1.19  cnf(u2631,axiom,
% 6.44/1.19      X127 != X128 | k2_tarski(X127,X128) = k2_tarski(X127,sK2(X125,X126,k2_tarski(X127,X128))) | ~r2_hidden(X127,k2_tarski(X127,X128)) | sK2(X125,X126,k2_tarski(X127,X128)) = X126 | sK2(X125,X126,k2_tarski(X127,X128)) = X125 | k2_tarski(X125,X126) = k2_tarski(X127,X128)).
% 6.44/1.19  
% 6.44/1.19  cnf(u2330,axiom,
% 6.44/1.19      X99 != X100 | k2_tarski(X99,X100) = k2_tarski(X101,X99) | ~r2_hidden(X99,k2_tarski(X101,X99)) | sK2(X99,X100,k2_tarski(X101,X99)) = X101).
% 6.44/1.19  
% 6.44/1.19  cnf(u2315,axiom,
% 6.44/1.19      X99 != X101 | k2_tarski(X99,X100) = k2_tarski(X101,X99) | ~r2_hidden(X99,k2_tarski(X101,X99)) | sK2(X99,X100,k2_tarski(X101,X99)) = X100).
% 6.44/1.19  
% 6.44/1.19  cnf(u2313,axiom,
% 6.44/1.19      X1 != X2 | sK2(X0,X1,k2_tarski(X2,X0)) = X1 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 6.44/1.19  
% 6.44/1.19  cnf(u2312,axiom,
% 6.44/1.19      X1 != X2 | sK2(X0,X1,k2_tarski(X2,X0)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 6.44/1.19  
% 6.44/1.19  cnf(u2168,axiom,
% 6.44/1.19      X92 != X93 | k2_tarski(X92,X93) = k2_tarski(X92,X94) | ~r2_hidden(X92,k2_tarski(X92,X94)) | sK2(X92,X93,k2_tarski(X92,X94)) = X94).
% 6.44/1.19  
% 6.44/1.19  cnf(u2153,axiom,
% 6.44/1.19      X92 != X94 | k2_tarski(X92,X93) = k2_tarski(X92,X94) | ~r2_hidden(X92,k2_tarski(X92,X94)) | sK2(X92,X93,k2_tarski(X92,X94)) = X93).
% 6.44/1.19  
% 6.44/1.19  cnf(u2151,axiom,
% 6.44/1.19      X1 != X2 | sK2(X0,X1,k2_tarski(X0,X2)) = X1 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 6.44/1.19  
% 6.44/1.19  cnf(u2150,axiom,
% 6.44/1.19      X1 != X2 | sK2(X0,X1,k2_tarski(X0,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 6.44/1.19  
% 6.44/1.19  cnf(u2024,axiom,
% 6.44/1.19      X91 != X92 | k2_tarski(X93,X92) = k2_tarski(X91,X92) | ~r2_hidden(X92,k2_tarski(X93,X92)) | sK2(X91,X92,k2_tarski(X93,X92)) = X93).
% 6.44/1.19  
% 6.44/1.19  cnf(u2010,axiom,
% 6.44/1.19      X92 != X93 | k2_tarski(X93,X92) = k2_tarski(X91,X92) | ~r2_hidden(X92,k2_tarski(X93,X92)) | sK2(X91,X92,k2_tarski(X93,X92)) = X91).
% 6.44/1.19  
% 6.44/1.19  cnf(u2009,axiom,
% 6.44/1.19      X0 != X2 | sK2(X0,X1,k2_tarski(X2,X1)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 6.44/1.19  
% 6.44/1.19  cnf(u2008,axiom,
% 6.44/1.19      X0 != X2 | sK2(X0,X1,k2_tarski(X2,X1)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 6.44/1.19  
% 6.44/1.19  cnf(u1863,axiom,
% 6.44/1.19      X90 != X91 | k2_tarski(X90,X91) = k2_tarski(X91,X92) | ~r2_hidden(X91,k2_tarski(X91,X92)) | sK2(X90,X91,k2_tarski(X91,X92)) = X92).
% 6.44/1.19  
% 6.44/1.19  cnf(u1849,axiom,
% 6.44/1.19      X91 != X92 | k2_tarski(X90,X91) = k2_tarski(X91,X92) | ~r2_hidden(X91,k2_tarski(X91,X92)) | sK2(X90,X91,k2_tarski(X91,X92)) = X90).
% 6.44/1.19  
% 6.44/1.19  cnf(u1848,axiom,
% 6.44/1.19      X0 != X2 | sK2(X0,X1,k2_tarski(X1,X2)) = X0 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 6.44/1.19  
% 6.44/1.19  cnf(u1847,axiom,
% 6.44/1.19      X0 != X2 | sK2(X0,X1,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 6.44/1.19  
% 6.44/1.19  cnf(u1714,axiom,
% 6.44/1.19      X62 != X63 | k2_tarski(X62,X62) = k2_tarski(X62,X63) | ~r2_hidden(X62,k2_tarski(X62,X62))).
% 6.44/1.19  
% 6.44/1.19  cnf(u1658,axiom,
% 6.44/1.19      X0 != X1 | sK2(X0,X1,k2_tarski(X0,X0)) = X1 | k2_tarski(X0,X1) = k2_tarski(X0,X0)).
% 6.44/1.19  
% 6.44/1.19  cnf(u1657,axiom,
% 6.44/1.19      X0 != X1 | sK2(X0,X1,k2_tarski(X0,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X0,X0)).
% 6.44/1.19  
% 6.44/1.19  cnf(u1585,axiom,
% 6.44/1.19      X61 != X62 | k2_tarski(X62,X62) = k2_tarski(X61,X62) | ~r2_hidden(X62,k2_tarski(X62,X62))).
% 6.44/1.19  
% 6.44/1.19  cnf(u1455,axiom,
% 6.44/1.19      X3 != X4 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X0 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X3 | k2_tarski(X3,X4) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X4))) | sK2(X1,X2,k2_tarski(X3,X4)) = X2 | sK2(X1,X2,k2_tarski(X3,X4)) = X1 | k2_tarski(X1,X2) = k2_tarski(X3,X4)).
% 6.44/1.19  
% 6.44/1.19  cnf(u1454,axiom,
% 6.44/1.19      X0 != X4 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X0 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X3 | k2_tarski(X3,X4) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X4))) | sK2(X1,X2,k2_tarski(X3,X4)) = X2 | sK2(X1,X2,k2_tarski(X3,X4)) = X1 | k2_tarski(X1,X2) = k2_tarski(X3,X4)).
% 6.44/1.19  
% 6.44/1.19  cnf(u1453,axiom,
% 6.44/1.19      X3 != X4 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X0 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X4 | k2_tarski(X3,X4) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X4))) | sK2(X1,X2,k2_tarski(X3,X4)) = X2 | sK2(X1,X2,k2_tarski(X3,X4)) = X1 | k2_tarski(X1,X2) = k2_tarski(X3,X4)).
% 6.44/1.19  
% 6.44/1.19  cnf(u1452,axiom,
% 6.44/1.19      X0 != X3 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X0 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X4 | k2_tarski(X3,X4) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X4))) | sK2(X1,X2,k2_tarski(X3,X4)) = X2 | sK2(X1,X2,k2_tarski(X3,X4)) = X1 | k2_tarski(X1,X2) = k2_tarski(X3,X4)).
% 6.44/1.19  
% 6.44/1.19  cnf(u1451,axiom,
% 6.44/1.19      X0 != X4 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X3 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X4 | k2_tarski(X3,X4) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X4))) | sK2(X1,X2,k2_tarski(X3,X4)) = X2 | sK2(X1,X2,k2_tarski(X3,X4)) = X1 | k2_tarski(X1,X2) = k2_tarski(X3,X4)).
% 6.44/1.19  
% 6.44/1.19  cnf(u1450,axiom,
% 6.44/1.19      X0 != X3 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X3 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X4 | k2_tarski(X3,X4) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X4))) | sK2(X1,X2,k2_tarski(X3,X4)) = X2 | sK2(X1,X2,k2_tarski(X3,X4)) = X1 | k2_tarski(X1,X2) = k2_tarski(X3,X4)).
% 6.44/1.19  
% 6.44/1.19  cnf(u1135,axiom,
% 6.44/1.19      X2 != X3 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X4 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X2 | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),X4) | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 6.44/1.19  
% 6.44/1.19  cnf(u1134,axiom,
% 6.44/1.19      X3 != X4 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X4 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X2 | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),X4) | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 6.44/1.19  
% 6.44/1.19  cnf(u1133,axiom,
% 6.44/1.19      X2 != X3 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X4 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X3 | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),X4) | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 6.44/1.19  
% 6.44/1.19  cnf(u1132,axiom,
% 6.44/1.19      X2 != X4 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X4 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X3 | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),X4) | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 6.44/1.19  
% 6.44/1.19  cnf(u1131,axiom,
% 6.44/1.19      X3 != X4 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X2 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X3 | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),X4) | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 6.44/1.19  
% 6.44/1.19  cnf(u1130,axiom,
% 6.44/1.19      X2 != X4 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X2 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X3 | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),X4) | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 6.44/1.19  
% 6.44/1.19  cnf(u909,axiom,
% 6.44/1.19      X0 != X1 | sK2(X0,X1,k2_tarski(X1,X1)) = X0 | k2_tarski(X0,X1) = k2_tarski(X1,X1)).
% 6.44/1.19  
% 6.44/1.19  cnf(u908,axiom,
% 6.44/1.19      X0 != X1 | sK2(X0,X1,k2_tarski(X1,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X1,X1)).
% 6.44/1.19  
% 6.44/1.19  cnf(u764,axiom,
% 6.44/1.19      X0 != X2 | sK2(X0,X1,k2_tarski(X2,X2)) = X1 | sK2(X0,X1,k2_tarski(X2,X2)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 6.44/1.19  
% 6.44/1.19  cnf(u763,axiom,
% 6.44/1.19      X1 != X2 | sK2(X0,X1,k2_tarski(X2,X2)) = X1 | sK2(X0,X1,k2_tarski(X2,X2)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 6.44/1.19  
% 6.44/1.19  cnf(u762,axiom,
% 6.44/1.19      X0 != X2 | sK2(X0,X1,k2_tarski(X2,X2)) = X1 | sK2(X0,X1,k2_tarski(X2,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 6.44/1.19  
% 6.44/1.19  cnf(u761,axiom,
% 6.44/1.19      X0 != X1 | sK2(X0,X1,k2_tarski(X2,X2)) = X1 | sK2(X0,X1,k2_tarski(X2,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 6.44/1.19  
% 6.44/1.19  cnf(u760,axiom,
% 6.44/1.19      X1 != X2 | sK2(X0,X1,k2_tarski(X2,X2)) = X0 | sK2(X0,X1,k2_tarski(X2,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 6.44/1.19  
% 6.44/1.19  cnf(u759,axiom,
% 6.44/1.19      X0 != X1 | sK2(X0,X1,k2_tarski(X2,X2)) = X0 | sK2(X0,X1,k2_tarski(X2,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 6.44/1.19  
% 6.44/1.19  cnf(u671,axiom,
% 6.44/1.19      X0 != X1 | sK2(X0,X1,k2_tarski(X1,X0)) = X1 | k2_tarski(X0,X1) = k2_tarski(X1,X0)).
% 6.44/1.19  
% 6.44/1.19  cnf(u670,axiom,
% 6.44/1.19      X0 != X1 | sK2(X0,X1,k2_tarski(X1,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X1,X0)).
% 6.44/1.19  
% 6.44/1.19  cnf(u630,axiom,
% 6.44/1.19      X0 != X2 | sK2(X0,X1,k2_tarski(X2,X0)) = X1 | sK2(X0,X1,k2_tarski(X2,X0)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 6.44/1.19  
% 6.44/1.19  cnf(u629,axiom,
% 6.44/1.19      X0 != X1 | sK2(X0,X1,k2_tarski(X2,X0)) = X1 | sK2(X0,X1,k2_tarski(X2,X0)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 6.44/1.19  
% 6.44/1.19  cnf(u628,axiom,
% 6.44/1.19      X0 != X2 | sK2(X0,X1,k2_tarski(X2,X0)) = X1 | sK2(X0,X1,k2_tarski(X2,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 6.44/1.19  
% 6.44/1.19  cnf(u627,axiom,
% 6.44/1.19      X1 != X2 | sK2(X0,X1,k2_tarski(X2,X0)) = X1 | sK2(X0,X1,k2_tarski(X2,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 6.44/1.19  
% 6.44/1.19  cnf(u626,axiom,
% 6.44/1.19      X0 != X1 | sK2(X0,X1,k2_tarski(X2,X0)) = X2 | sK2(X0,X1,k2_tarski(X2,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 6.44/1.19  
% 6.44/1.19  cnf(u625,axiom,
% 6.44/1.19      X1 != X2 | sK2(X0,X1,k2_tarski(X2,X0)) = X2 | sK2(X0,X1,k2_tarski(X2,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 6.44/1.19  
% 6.44/1.19  cnf(u539,axiom,
% 6.44/1.19      X0 != X2 | sK2(X0,X1,k2_tarski(X0,X2)) = X1 | sK2(X0,X1,k2_tarski(X0,X2)) = X0 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 6.44/1.19  
% 6.44/1.19  cnf(u538,axiom,
% 6.44/1.19      X1 != X2 | sK2(X0,X1,k2_tarski(X0,X2)) = X1 | sK2(X0,X1,k2_tarski(X0,X2)) = X0 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 6.44/1.19  
% 6.44/1.19  cnf(u537,axiom,
% 6.44/1.19      X0 != X2 | sK2(X0,X1,k2_tarski(X0,X2)) = X1 | sK2(X0,X1,k2_tarski(X0,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 6.44/1.19  
% 6.44/1.19  cnf(u536,axiom,
% 6.44/1.19      X0 != X1 | sK2(X0,X1,k2_tarski(X0,X2)) = X1 | sK2(X0,X1,k2_tarski(X0,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 6.44/1.19  
% 6.44/1.19  cnf(u535,axiom,
% 6.44/1.19      X1 != X2 | sK2(X0,X1,k2_tarski(X0,X2)) = X0 | sK2(X0,X1,k2_tarski(X0,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 6.44/1.19  
% 6.44/1.19  cnf(u534,axiom,
% 6.44/1.19      X0 != X1 | sK2(X0,X1,k2_tarski(X0,X2)) = X0 | sK2(X0,X1,k2_tarski(X0,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 6.44/1.19  
% 6.44/1.19  cnf(u456,axiom,
% 6.44/1.19      X1 != X2 | sK2(X0,X1,k2_tarski(X2,X1)) = X0 | sK2(X0,X1,k2_tarski(X2,X1)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 6.44/1.19  
% 6.44/1.19  cnf(u455,axiom,
% 6.44/1.19      X0 != X1 | sK2(X0,X1,k2_tarski(X2,X1)) = X0 | sK2(X0,X1,k2_tarski(X2,X1)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 6.44/1.19  
% 6.44/1.19  cnf(u454,axiom,
% 6.44/1.19      X1 != X2 | sK2(X0,X1,k2_tarski(X2,X1)) = X0 | sK2(X0,X1,k2_tarski(X2,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 6.44/1.19  
% 6.44/1.19  cnf(u453,axiom,
% 6.44/1.19      X0 != X2 | sK2(X0,X1,k2_tarski(X2,X1)) = X0 | sK2(X0,X1,k2_tarski(X2,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 6.44/1.19  
% 6.44/1.19  cnf(u452,axiom,
% 6.44/1.19      X0 != X1 | sK2(X0,X1,k2_tarski(X2,X1)) = X2 | sK2(X0,X1,k2_tarski(X2,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 6.44/1.19  
% 6.44/1.19  cnf(u451,axiom,
% 6.44/1.19      X0 != X2 | sK2(X0,X1,k2_tarski(X2,X1)) = X2 | sK2(X0,X1,k2_tarski(X2,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 6.44/1.19  
% 6.44/1.19  cnf(u384,axiom,
% 6.44/1.19      X1 != X2 | sK2(X0,X1,k2_tarski(X1,X2)) = X0 | sK2(X0,X1,k2_tarski(X1,X2)) = X1 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 6.44/1.19  
% 6.44/1.19  cnf(u383,axiom,
% 6.44/1.19      X0 != X2 | sK2(X0,X1,k2_tarski(X1,X2)) = X0 | sK2(X0,X1,k2_tarski(X1,X2)) = X1 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 6.44/1.19  
% 6.44/1.19  cnf(u382,axiom,
% 6.44/1.19      X1 != X2 | sK2(X0,X1,k2_tarski(X1,X2)) = X0 | sK2(X0,X1,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 6.44/1.19  
% 6.44/1.19  cnf(u381,axiom,
% 6.44/1.19      X0 != X1 | sK2(X0,X1,k2_tarski(X1,X2)) = X0 | sK2(X0,X1,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 6.44/1.19  
% 6.44/1.19  cnf(u380,axiom,
% 6.44/1.19      X0 != X2 | sK2(X0,X1,k2_tarski(X1,X2)) = X1 | sK2(X0,X1,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 6.44/1.19  
% 6.44/1.19  cnf(u379,axiom,
% 6.44/1.19      X0 != X1 | sK2(X0,X1,k2_tarski(X1,X2)) = X1 | sK2(X0,X1,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 6.44/1.19  
% 6.44/1.19  cnf(u317,axiom,
% 6.44/1.19      X0 != X1 | sK2(X0,X0,k2_tarski(X1,X1)) = X0 | k2_tarski(X0,X0) = k2_tarski(X1,X1)).
% 6.44/1.19  
% 6.44/1.19  cnf(u316,axiom,
% 6.44/1.19      X0 != X1 | sK2(X0,X0,k2_tarski(X1,X1)) = X1 | k2_tarski(X0,X0) = k2_tarski(X1,X1)).
% 6.44/1.19  
% 6.44/1.19  cnf(u281,axiom,
% 6.44/1.19      X12 != X13 | k2_tarski(X12,X12) = k2_tarski(X13,X12) | ~r2_hidden(X12,k2_tarski(X13,X12))).
% 6.44/1.19  
% 6.44/1.19  cnf(u252,axiom,
% 6.44/1.19      X0 != X1 | sK2(X0,X0,k2_tarski(X1,X0)) = X1 | k2_tarski(X0,X0) = k2_tarski(X1,X0)).
% 6.44/1.19  
% 6.44/1.19  cnf(u251,axiom,
% 6.44/1.19      X0 != X1 | sK2(X0,X0,k2_tarski(X1,X0)) = X0 | k2_tarski(X0,X0) = k2_tarski(X1,X0)).
% 6.44/1.19  
% 6.44/1.19  cnf(u218,axiom,
% 6.44/1.19      X12 != X13 | k2_tarski(X12,X12) = k2_tarski(X12,X13) | ~r2_hidden(X12,k2_tarski(X12,X13))).
% 6.44/1.19  
% 6.44/1.19  cnf(u188,axiom,
% 6.44/1.19      X0 != X1 | sK2(X0,X0,k2_tarski(X0,X1)) = X0 | k2_tarski(X0,X1) = k2_tarski(X0,X0)).
% 6.44/1.19  
% 6.44/1.19  cnf(u187,axiom,
% 6.44/1.19      X0 != X1 | sK2(X0,X0,k2_tarski(X0,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X0,X0)).
% 6.44/1.19  
% 6.44/1.19  cnf(u152,axiom,
% 6.44/1.19      X1 != X2 | sK2(X0,X0,k2_tarski(X1,X2)) = X0 | sK2(X0,X0,k2_tarski(X1,X2)) = X1 | k2_tarski(X0,X0) = k2_tarski(X1,X2)).
% 6.44/1.19  
% 6.44/1.19  cnf(u151,axiom,
% 6.44/1.19      X0 != X2 | sK2(X0,X0,k2_tarski(X1,X2)) = X0 | sK2(X0,X0,k2_tarski(X1,X2)) = X1 | k2_tarski(X0,X0) = k2_tarski(X1,X2)).
% 6.44/1.19  
% 6.44/1.19  cnf(u150,axiom,
% 6.44/1.19      X1 != X2 | sK2(X0,X0,k2_tarski(X1,X2)) = X0 | sK2(X0,X0,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X0) = k2_tarski(X1,X2)).
% 6.44/1.19  
% 6.44/1.19  cnf(u149,axiom,
% 6.44/1.19      X0 != X1 | sK2(X0,X0,k2_tarski(X1,X2)) = X0 | sK2(X0,X0,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X0) = k2_tarski(X1,X2)).
% 6.44/1.19  
% 6.44/1.19  cnf(u148,axiom,
% 6.44/1.19      X0 != X2 | sK2(X0,X0,k2_tarski(X1,X2)) = X1 | sK2(X0,X0,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X0) = k2_tarski(X1,X2)).
% 6.44/1.19  
% 6.44/1.19  cnf(u147,axiom,
% 6.44/1.19      X0 != X1 | sK2(X0,X0,k2_tarski(X1,X2)) = X1 | sK2(X0,X0,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X0) = k2_tarski(X1,X2)).
% 6.44/1.19  
% 6.44/1.19  cnf(u102,axiom,
% 6.44/1.19      X2 != X3 | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | sK2(X0,X1,k2_tarski(X2,X3)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 6.44/1.19  
% 6.44/1.19  cnf(u101,axiom,
% 6.44/1.19      X0 != X3 | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | sK2(X0,X1,k2_tarski(X2,X3)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 6.44/1.19  
% 6.44/1.19  cnf(u100,axiom,
% 6.44/1.19      X1 != X3 | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | sK2(X0,X1,k2_tarski(X2,X3)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 6.44/1.19  
% 6.44/1.19  cnf(u99,axiom,
% 6.44/1.19      X2 != X3 | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | sK2(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 6.44/1.19  
% 6.44/1.19  cnf(u98,axiom,
% 6.44/1.19      X0 != X2 | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | sK2(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 6.44/1.19  
% 6.44/1.19  cnf(u97,axiom,
% 6.44/1.19      X1 != X2 | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | sK2(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 6.44/1.19  
% 6.44/1.19  cnf(u96,axiom,
% 6.44/1.19      X0 != X3 | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X2 | sK2(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 6.44/1.19  
% 6.44/1.19  cnf(u95,axiom,
% 6.44/1.19      X0 != X2 | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X2 | sK2(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 6.44/1.19  
% 6.44/1.19  cnf(u94,axiom,
% 6.44/1.19      X0 != X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X2 | sK2(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 6.44/1.19  
% 6.44/1.19  cnf(u93,axiom,
% 6.44/1.19      X1 != X3 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | sK2(X0,X1,k2_tarski(X2,X3)) = X2 | sK2(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 6.44/1.19  
% 6.44/1.19  cnf(u92,axiom,
% 6.44/1.19      X1 != X2 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | sK2(X0,X1,k2_tarski(X2,X3)) = X2 | sK2(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 6.44/1.19  
% 6.44/1.19  cnf(u91,axiom,
% 6.44/1.19      X0 != X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | sK2(X0,X1,k2_tarski(X2,X3)) = X2 | sK2(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 6.44/1.19  
% 6.44/1.19  cnf(u3398,axiom,
% 6.44/1.19      sK2(X150,X151,k2_tarski(X152,X152)) != X153 | k2_tarski(X152,X152) = k2_tarski(sK2(X150,X151,k2_tarski(X152,X152)),X153) | ~r2_hidden(sK2(X150,X151,k2_tarski(X152,X152)),k2_tarski(X152,X152)) | sK2(sK2(X150,X151,k2_tarski(X152,X152)),X153,k2_tarski(X152,X152)) = X152 | sK2(X150,X151,k2_tarski(X152,X152)) = X151 | sK2(X150,X151,k2_tarski(X152,X152)) = X150 | k2_tarski(X150,X151) = k2_tarski(X152,X152)).
% 6.44/1.19  
% 6.44/1.19  cnf(u3682,axiom,
% 6.44/1.19      sK2(X162,X163,k2_tarski(X164,X164)) != X161 | k2_tarski(X164,X164) = k2_tarski(X161,sK2(X162,X163,k2_tarski(X164,X164))) | ~r2_hidden(sK2(X162,X163,k2_tarski(X164,X164)),k2_tarski(X164,X164)) | sK2(X161,sK2(X162,X163,k2_tarski(X164,X164)),k2_tarski(X164,X164)) = X164 | sK2(X162,X163,k2_tarski(X164,X164)) = X163 | sK2(X162,X163,k2_tarski(X164,X164)) = X162 | k2_tarski(X162,X163) = k2_tarski(X164,X164)).
% 6.44/1.19  
% 6.44/1.19  cnf(u1144,axiom,
% 6.44/1.19      sK2(X67,X68,k2_tarski(X69,X70)) != X71 | k2_tarski(X69,X70) = k2_tarski(sK2(X67,X68,k2_tarski(X69,X70)),X71) | ~r2_hidden(sK2(X67,X68,k2_tarski(X69,X70)),k2_tarski(X69,X70)) | sK2(sK2(X67,X68,k2_tarski(X69,X70)),X71,k2_tarski(X69,X70)) = X69 | sK2(sK2(X67,X68,k2_tarski(X69,X70)),X71,k2_tarski(X69,X70)) = X70 | sK2(X67,X68,k2_tarski(X69,X70)) = X68 | sK2(X67,X68,k2_tarski(X69,X70)) = X67 | k2_tarski(X69,X70) = k2_tarski(X67,X68)).
% 6.44/1.19  
% 6.44/1.19  cnf(u1471,axiom,
% 6.44/1.19      sK2(X85,X86,k2_tarski(X87,X88)) != X84 | k2_tarski(X87,X88) = k2_tarski(X84,sK2(X85,X86,k2_tarski(X87,X88))) | ~r2_hidden(sK2(X85,X86,k2_tarski(X87,X88)),k2_tarski(X87,X88)) | sK2(X84,sK2(X85,X86,k2_tarski(X87,X88)),k2_tarski(X87,X88)) = X87 | sK2(X84,sK2(X85,X86,k2_tarski(X87,X88)),k2_tarski(X87,X88)) = X88 | sK2(X85,X86,k2_tarski(X87,X88)) = X86 | sK2(X85,X86,k2_tarski(X87,X88)) = X85 | k2_tarski(X85,X86) = k2_tarski(X87,X88)).
% 6.44/1.19  
% 6.44/1.19  cnf(u54,axiom,
% 6.44/1.19      sK2(X0,X1,X2) != X0 | k2_tarski(X0,X1) = X2 | ~r2_hidden(X0,X2)).
% 6.44/1.19  
% 6.44/1.19  cnf(u53,axiom,
% 6.44/1.19      sK2(X0,X1,X2) != X1 | k2_tarski(X0,X1) = X2 | ~r2_hidden(X1,X2)).
% 6.44/1.19  
% 6.44/1.19  % (30045)# SZS output end Saturation.
% 6.44/1.19  % (30045)------------------------------
% 6.44/1.19  % (30045)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.44/1.19  % (30045)Termination reason: Satisfiable
% 6.44/1.19  
% 6.44/1.19  % (30045)Memory used [KB]: 4477
% 6.44/1.19  % (30045)Time elapsed: 0.776 s
% 6.44/1.19  % (30045)------------------------------
% 6.44/1.19  % (30045)------------------------------
% 6.44/1.19  % (30039)Success in time 0.817 s
%------------------------------------------------------------------------------
