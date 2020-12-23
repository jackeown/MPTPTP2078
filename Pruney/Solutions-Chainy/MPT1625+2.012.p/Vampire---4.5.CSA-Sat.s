%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:54 EST 2020

% Result     : CounterSatisfiable 7.99s
% Output     : Saturation 7.99s
% Verified   : 
% Statistics : Number of clauses        :  244 ( 244 expanded)
%              Number of leaves         :  244 ( 244 expanded)
%              Depth                    :    0
%              Number of atoms          : 1053 (1053 expanded)
%              Number of equality atoms :  930 ( 930 expanded)
%              Maximal clause size      :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u33,negated_conjecture,
    ( ~ v2_waybel_0(k6_domain_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v1_waybel_0(k6_domain_1(u1_struct_0(sK0),sK1),sK0) )).

cnf(u37,axiom,
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

cnf(u31,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u117,negated_conjecture,
    ( ~ l1_orders_2(sK0)
    | sK2(X0,X1,k6_domain_1(u1_struct_0(sK0),sK1)) = X1
    | sK2(X0,X1,k6_domain_1(u1_struct_0(sK0),sK1)) = X0
    | k2_tarski(X0,X1) = k6_domain_1(u1_struct_0(sK0),sK1)
    | ~ v3_orders_2(sK0)
    | k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) )).

cnf(u30,negated_conjecture,
    ( v3_orders_2(sK0) )).

cnf(u119,negated_conjecture,
    ( ~ v3_orders_2(sK0)
    | sK2(X0,X1,k6_domain_1(u1_struct_0(sK0),sK1)) = X0
    | k2_tarski(X0,X1) = k6_domain_1(u1_struct_0(sK0),sK1)
    | sK2(X0,X1,k6_domain_1(u1_struct_0(sK0),sK1)) = X1
    | k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) )).

cnf(u60,axiom,
    ( v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ r2_hidden(X2,k6_domain_1(u1_struct_0(X1),X0))
    | ~ v1_xboole_0(u1_struct_0(X1)) )).

cnf(u66,axiom,
    ( v2_struct_0(X6)
    | k2_tarski(X4,X5) = k6_domain_1(u1_struct_0(X6),X7)
    | sK2(X4,X5,k6_domain_1(u1_struct_0(X6),X7)) = X5
    | ~ v1_xboole_0(u1_struct_0(X6))
    | ~ m1_subset_1(X7,u1_struct_0(X6))
    | ~ l1_orders_2(X6)
    | ~ v3_orders_2(X6)
    | sK2(X4,X5,k6_domain_1(u1_struct_0(X6),X7)) = X4 )).

cnf(u29,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u47,axiom,
    ( v1_xboole_0(X0)
    | ~ m1_subset_1(X1,X0)
    | k6_domain_1(X0,X1) = k2_tarski(X1,X1) )).

cnf(u67,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | sK2(X0,X1,k6_domain_1(u1_struct_0(sK0),sK1)) = X1
    | sK2(X0,X1,k6_domain_1(u1_struct_0(sK0),sK1)) = X0
    | k2_tarski(X0,X1) = k6_domain_1(u1_struct_0(sK0),sK1) )).

cnf(u38,axiom,
    ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u34,axiom,
    ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
    | ~ m1_subset_1(X1,X0)
    | v1_xboole_0(X0) )).

cnf(u32,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

cnf(u64,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | sK2(X1,X2,k6_domain_1(u1_struct_0(sK0),X0)) = X2
    | sK2(X1,X2,k6_domain_1(u1_struct_0(sK0),X0)) = X1
    | k2_tarski(X1,X2) = k6_domain_1(u1_struct_0(sK0),X0) )).

cnf(u116,negated_conjecture,
    ( ~ m1_subset_1(X2,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | sK2(X0,X1,k6_domain_1(u1_struct_0(sK0),sK1)) = X1
    | sK2(X0,X1,k6_domain_1(u1_struct_0(sK0),sK1)) = X0
    | k2_tarski(X0,X1) = k6_domain_1(u1_struct_0(sK0),sK1)
    | ~ l1_orders_2(sK0)
    | k2_tarski(X2,X2) = k6_domain_1(u1_struct_0(sK0),X2) )).

cnf(u55,axiom,
    ( ~ m1_subset_1(k2_tarski(X1,X0),k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) )).

cnf(u36,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X2) )).

cnf(u61,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | sK2(X0,X1,X2) = X0
    | k2_tarski(X0,X1) = X2
    | sK2(X0,X1,X2) = X1
    | ~ v1_xboole_0(X3) )).

cnf(u43,axiom,
    ( r2_hidden(sK2(X0,X1,X2),X2)
    | sK2(X0,X1,X2) = X1
    | sK2(X0,X1,X2) = X0
    | k2_tarski(X0,X1) = X2 )).

cnf(u51,axiom,
    ( r2_hidden(X4,k2_tarski(X4,X1)) )).

cnf(u49,axiom,
    ( r2_hidden(X4,k2_tarski(X0,X4)) )).

cnf(u145,negated_conjecture,
    ( ~ r2_hidden(X4,k6_domain_1(u1_struct_0(sK0),sK1))
    | k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(X4,X4)
    | k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) )).

cnf(u133,negated_conjecture,
    ( ~ r2_hidden(X5,k6_domain_1(u1_struct_0(sK0),sK1))
    | k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(X4,X5)
    | sK2(X4,X5,k6_domain_1(u1_struct_0(sK0),sK1)) = X4
    | k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) )).

cnf(u137,negated_conjecture,
    ( ~ r2_hidden(X2,k6_domain_1(u1_struct_0(sK0),sK1))
    | k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(X2,X3)
    | sK2(X2,X3,k6_domain_1(u1_struct_0(sK0),sK1)) = X3
    | k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) )).

cnf(u63,negated_conjecture,
    ( ~ r2_hidden(X1,k6_domain_1(u1_struct_0(sK0),X0))
    | ~ v3_orders_2(sK0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0)) )).

cnf(u1571,axiom,
    ( ~ r2_hidden(X58,k2_tarski(X58,X58))
    | k2_tarski(X58,X58) = k2_tarski(X57,X58)
    | sK2(X57,X58,k2_tarski(X58,X58)) = X57 )).

cnf(u1698,axiom,
    ( ~ r2_hidden(X58,k2_tarski(X58,X58))
    | k2_tarski(X58,X58) = k2_tarski(X58,X59)
    | sK2(X58,X59,k2_tarski(X58,X58)) = X59 )).

cnf(u234,axiom,
    ( ~ r2_hidden(X12,k2_tarski(X12,X13))
    | k2_tarski(X12,X12) = k2_tarski(X12,X13)
    | sK2(X12,X12,k2_tarski(X12,X13)) = X13 )).

cnf(u826,axiom,
    ( ~ r2_hidden(X38,k2_tarski(X38,X37))
    | k2_tarski(X38,X37) = k2_tarski(X37,X38) )).

cnf(u385,axiom,
    ( ~ r2_hidden(X19,k2_tarski(X19,X20))
    | k2_tarski(X19,X20) = k2_tarski(X18,X19)
    | sK2(X18,X19,k2_tarski(X19,X20)) = X18
    | sK2(X18,X19,k2_tarski(X19,X20)) = X20 )).

cnf(u541,axiom,
    ( ~ r2_hidden(X27,k2_tarski(X27,X29))
    | k2_tarski(X27,X29) = k2_tarski(X27,X28)
    | sK2(X27,X28,k2_tarski(X27,X29)) = X28
    | sK2(X27,X28,k2_tarski(X27,X29)) = X29 )).

cnf(u2468,axiom,
    ( ~ r2_hidden(X264,k2_tarski(X263,X263))
    | k2_tarski(X263,X263) = k2_tarski(sK2(X261,X262,k2_tarski(X263,X263)),X264)
    | sK2(sK2(X261,X262,k2_tarski(X263,X263)),X264,k2_tarski(X263,X263)) = X263
    | sK2(X261,X262,k2_tarski(X263,X263)) = X262
    | sK2(X261,X262,k2_tarski(X263,X263)) = X261
    | k2_tarski(X263,X263) = k2_tarski(X261,X262) )).

cnf(u2460,axiom,
    ( ~ r2_hidden(X232,k2_tarski(X231,X231))
    | k2_tarski(X231,X231) = k2_tarski(X232,sK2(X229,X230,k2_tarski(X231,X231)))
    | sK2(X232,sK2(X229,X230,k2_tarski(X231,X231)),k2_tarski(X231,X231)) = X231
    | sK2(X229,X230,k2_tarski(X231,X231)) = X230
    | sK2(X229,X230,k2_tarski(X231,X231)) = X229
    | k2_tarski(X231,X231) = k2_tarski(X229,X230) )).

cnf(u2405,axiom,
    ( ~ r2_hidden(X9,k2_tarski(X8,X8))
    | sK2(X6,X7,k2_tarski(X8,X8)) = X9
    | X8 = X9
    | sK2(X6,X7,k2_tarski(X8,X8)) = X7
    | sK2(X6,X7,k2_tarski(X8,X8)) = X6
    | k2_tarski(X6,X7) = k2_tarski(X8,X8) )).

cnf(u1750,axiom,
    ( ~ r2_hidden(X65,k2_tarski(X64,X64))
    | k2_tarski(X64,X65) = k2_tarski(X64,X64) )).

cnf(u1625,axiom,
    ( ~ r2_hidden(X59,k2_tarski(X60,X60))
    | k2_tarski(X60,X60) = k2_tarski(X59,X60) )).

cnf(u764,axiom,
    ( ~ r2_hidden(X43,k2_tarski(X44,X44))
    | k2_tarski(X42,X43) = k2_tarski(X44,X44)
    | sK2(X42,X43,k2_tarski(X44,X44)) = X42
    | sK2(X42,X43,k2_tarski(X44,X44)) = X44 )).

cnf(u762,axiom,
    ( ~ r2_hidden(X39,k2_tarski(X41,X41))
    | k2_tarski(X41,X41) = k2_tarski(X39,X40)
    | sK2(X39,X40,k2_tarski(X41,X41)) = X40
    | sK2(X39,X40,k2_tarski(X41,X41)) = X41 )).

cnf(u664,axiom,
    ( ~ r2_hidden(X24,k2_tarski(X25,X25))
    | k2_tarski(X24,X24) = k2_tarski(X25,X25)
    | sK2(X24,X24,k2_tarski(X25,X25)) = X25 )).

cnf(u296,axiom,
    ( ~ r2_hidden(X12,k2_tarski(X13,X12))
    | k2_tarski(X12,X12) = k2_tarski(X13,X12)
    | sK2(X12,X12,k2_tarski(X13,X12)) = X13 )).

cnf(u802,axiom,
    ( ~ r2_hidden(X31,k2_tarski(X32,X31))
    | k2_tarski(X32,X31) = k2_tarski(X31,X32)
    | sK2(X31,X32,k2_tarski(X32,X31)) = X32 )).

cnf(u454,axiom,
    ( ~ r2_hidden(X25,k2_tarski(X26,X25))
    | k2_tarski(X26,X25) = k2_tarski(X24,X25)
    | sK2(X24,X25,k2_tarski(X26,X25)) = X24
    | sK2(X24,X25,k2_tarski(X26,X25)) = X26 )).

cnf(u629,axiom,
    ( ~ r2_hidden(X33,k2_tarski(X35,X33))
    | k2_tarski(X33,X34) = k2_tarski(X35,X33)
    | sK2(X33,X34,k2_tarski(X35,X33)) = X34
    | sK2(X33,X34,k2_tarski(X35,X33)) = X35 )).

cnf(u2223,axiom,
    ( ~ r2_hidden(X2,k2_tarski(X1,X0))
    | k2_tarski(X1,X0) = k2_tarski(X0,X2)
    | sK2(X0,X2,k2_tarski(X1,X0)) = X1 )).

cnf(u2208,axiom,
    ( ~ r2_hidden(X96,k2_tarski(X95,X97))
    | k2_tarski(X95,X96) = k2_tarski(X95,X97)
    | sK2(X95,X96,k2_tarski(X95,X97)) = X97 )).

cnf(u1929,axiom,
    ( ~ r2_hidden(X2,k2_tarski(X1,X0))
    | k2_tarski(X1,X0) = k2_tarski(X2,X0)
    | sK2(X2,X0,k2_tarski(X1,X0)) = X1 )).

cnf(u1907,axiom,
    ( ~ r2_hidden(X87,k2_tarski(X88,X89))
    | k2_tarski(X87,X88) = k2_tarski(X88,X89)
    | sK2(X87,X88,k2_tarski(X88,X89)) = X89 )).

cnf(u1442,axiom,
    ( ~ r2_hidden(X79,k2_tarski(X82,X83))
    | k2_tarski(X82,X83) = k2_tarski(X79,sK2(X80,X81,k2_tarski(X82,X83)))
    | sK2(X79,sK2(X80,X81,k2_tarski(X82,X83)),k2_tarski(X82,X83)) = X82
    | sK2(X79,sK2(X80,X81,k2_tarski(X82,X83)),k2_tarski(X82,X83)) = X83
    | sK2(X80,X81,k2_tarski(X82,X83)) = X81
    | sK2(X80,X81,k2_tarski(X82,X83)) = X80
    | k2_tarski(X82,X83) = k2_tarski(X80,X81) )).

cnf(u1040,axiom,
    ( ~ r2_hidden(X70,k2_tarski(X68,X69))
    | k2_tarski(X68,X69) = k2_tarski(sK2(X66,X67,k2_tarski(X68,X69)),X70)
    | sK2(sK2(X66,X67,k2_tarski(X68,X69)),X70,k2_tarski(X68,X69)) = X68
    | sK2(sK2(X66,X67,k2_tarski(X68,X69)),X70,k2_tarski(X68,X69)) = X69
    | sK2(X66,X67,k2_tarski(X68,X69)) = X67
    | sK2(X66,X67,k2_tarski(X68,X69)) = X66
    | k2_tarski(X68,X69) = k2_tarski(X66,X67) )).

cnf(u634,axiom,
    ( ~ r2_hidden(X37,k2_tarski(X38,X36))
    | k2_tarski(X38,X36) = k2_tarski(X36,X37)
    | sK2(X36,X37,k2_tarski(X38,X36)) = X38
    | sK2(X36,X37,k2_tarski(X38,X36)) = X36 )).

cnf(u543,axiom,
    ( ~ r2_hidden(X31,k2_tarski(X30,X32))
    | k2_tarski(X30,X31) = k2_tarski(X30,X32)
    | sK2(X30,X31,k2_tarski(X30,X32)) = X30
    | sK2(X30,X31,k2_tarski(X30,X32)) = X32 )).

cnf(u461,axiom,
    ( ~ r2_hidden(X21,k2_tarski(X23,X22))
    | k2_tarski(X23,X22) = k2_tarski(X21,X22)
    | sK2(X21,X22,k2_tarski(X23,X22)) = X23
    | sK2(X21,X22,k2_tarski(X23,X22)) = X22 )).

cnf(u389,axiom,
    ( ~ r2_hidden(X15,k2_tarski(X16,X17))
    | k2_tarski(X16,X17) = k2_tarski(X15,X16)
    | sK2(X15,X16,k2_tarski(X16,X17)) = X16
    | sK2(X15,X16,k2_tarski(X16,X17)) = X17 )).

cnf(u201,axiom,
    ( ~ r2_hidden(X18,k2_tarski(X19,X20))
    | k2_tarski(X19,X20) = k2_tarski(X18,X18)
    | sK2(X18,X18,k2_tarski(X19,X20)) = X19
    | sK2(X18,X18,k2_tarski(X19,X20)) = X20 )).

cnf(u114,axiom,
    ( ~ r2_hidden(X9,k2_tarski(X10,X11))
    | k2_tarski(X10,X11) = k2_tarski(X8,X9)
    | sK2(X8,X9,k2_tarski(X10,X11)) = X8
    | sK2(X8,X9,k2_tarski(X10,X11)) = X10
    | sK2(X8,X9,k2_tarski(X10,X11)) = X11 )).

cnf(u112,axiom,
    ( ~ r2_hidden(X4,k2_tarski(X6,X7))
    | k2_tarski(X6,X7) = k2_tarski(X4,X5)
    | sK2(X4,X5,k2_tarski(X6,X7)) = X5
    | sK2(X4,X5,k2_tarski(X6,X7)) = X6
    | sK2(X4,X5,k2_tarski(X6,X7)) = X7 )).

cnf(u52,axiom,
    ( ~ r2_hidden(X4,k2_tarski(X0,X1))
    | X0 = X4
    | X1 = X4 )).

cnf(u36_001,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X2) )).

cnf(u1756,axiom,
    ( k2_tarski(X2,X2) = k2_tarski(X2,sK2(X3,X4,k2_tarski(X2,X2)))
    | sK2(X3,X4,k2_tarski(X2,X2)) = X4
    | sK2(X3,X4,k2_tarski(X2,X2)) = X3
    | k2_tarski(X3,X4) = k2_tarski(X2,X2) )).

cnf(u1630,axiom,
    ( k2_tarski(X2,X2) = k2_tarski(sK2(X3,X4,k2_tarski(X2,X2)),X2)
    | sK2(X3,X4,k2_tarski(X2,X2)) = X4
    | sK2(X3,X4,k2_tarski(X2,X2)) = X3
    | k2_tarski(X3,X4) = k2_tarski(X2,X2) )).

cnf(u831,axiom,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) )).

cnf(u2214,axiom,
    ( sK2(sK2(X5,X6,k2_tarski(X4,X4)),X7,k2_tarski(X4,X4)) = X7
    | sK2(sK2(X5,X6,k2_tarski(X4,X4)),X7,k2_tarski(X4,X4)) = X4
    | k2_tarski(X4,X4) = k2_tarski(sK2(X5,X6,k2_tarski(X4,X4)),X7)
    | sK2(X5,X6,k2_tarski(X4,X4)) = X6
    | sK2(X5,X6,k2_tarski(X4,X4)) = X5
    | k2_tarski(X4,X4) = k2_tarski(X5,X6) )).

cnf(u2214_002,axiom,
    ( sK2(sK2(X5,X6,k2_tarski(X4,X4)),X7,k2_tarski(X4,X4)) = X7
    | sK2(sK2(X5,X6,k2_tarski(X4,X4)),X7,k2_tarski(X4,X4)) = X4
    | k2_tarski(X4,X4) = k2_tarski(sK2(X5,X6,k2_tarski(X4,X4)),X7)
    | sK2(X5,X6,k2_tarski(X4,X4)) = X6
    | sK2(X5,X6,k2_tarski(X4,X4)) = X5
    | k2_tarski(X4,X4) = k2_tarski(X5,X6) )).

cnf(u5036,axiom,
    ( sK2(sK2(X0,X1,k2_tarski(X2,X2)),sK2(X3,X4,k2_tarski(X2,X2)),k2_tarski(X2,X2)) = X2
    | k2_tarski(X2,X2) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X2)),sK2(X3,X4,k2_tarski(X2,X2)))
    | sK2(X0,X1,k2_tarski(X2,X2)) = X1
    | sK2(X0,X1,k2_tarski(X2,X2)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X2)
    | sK2(X3,X4,k2_tarski(X2,X2)) = X4
    | sK2(X3,X4,k2_tarski(X2,X2)) = X3
    | k2_tarski(X3,X4) = k2_tarski(X2,X2) )).

cnf(u2615,axiom,
    ( sK2(sK2(X16,X17,k2_tarski(X15,X15)),sK2(X13,X14,k2_tarski(X15,X15)),k2_tarski(X15,X15)) = X15
    | k2_tarski(X15,X15) = k2_tarski(sK2(X13,X14,k2_tarski(X15,X15)),sK2(X16,X17,k2_tarski(X15,X15)))
    | sK2(X16,X17,k2_tarski(X15,X15)) = X17
    | sK2(X16,X17,k2_tarski(X15,X15)) = X16
    | k2_tarski(X16,X17) = k2_tarski(X15,X15)
    | sK2(X13,X14,k2_tarski(X15,X15)) = X14
    | sK2(X13,X14,k2_tarski(X15,X15)) = X13
    | k2_tarski(X13,X14) = k2_tarski(X15,X15) )).

cnf(u671,axiom,
    ( sK2(sK2(X2,X3,k2_tarski(X4,X4)),sK2(X2,X3,k2_tarski(X4,X4)),k2_tarski(X4,X4)) = X4
    | k2_tarski(X4,X4) = k2_tarski(sK2(X2,X3,k2_tarski(X4,X4)),sK2(X2,X3,k2_tarski(X4,X4)))
    | sK2(X2,X3,k2_tarski(X4,X4)) = X3
    | sK2(X2,X3,k2_tarski(X4,X4)) = X2
    | k2_tarski(X2,X3) = k2_tarski(X4,X4) )).

cnf(u3186,axiom,
    ( sK2(sK2(X10,X11,k2_tarski(X8,X9)),sK2(X12,X13,k2_tarski(X8,X9)),k2_tarski(X8,X9)) = X8
    | sK2(sK2(X10,X11,k2_tarski(X8,X9)),sK2(X12,X13,k2_tarski(X8,X9)),k2_tarski(X8,X9)) = X9
    | k2_tarski(X8,X9) = k2_tarski(sK2(X10,X11,k2_tarski(X8,X9)),sK2(X12,X13,k2_tarski(X8,X9)))
    | sK2(X10,X11,k2_tarski(X8,X9)) = X11
    | sK2(X10,X11,k2_tarski(X8,X9)) = X10
    | k2_tarski(X10,X11) = k2_tarski(X8,X9)
    | sK2(X12,X13,k2_tarski(X8,X9)) = X13
    | sK2(X12,X13,k2_tarski(X8,X9)) = X12
    | k2_tarski(X8,X9) = k2_tarski(X12,X13) )).

cnf(u3186_003,axiom,
    ( sK2(sK2(X10,X11,k2_tarski(X8,X9)),sK2(X12,X13,k2_tarski(X8,X9)),k2_tarski(X8,X9)) = X8
    | sK2(sK2(X10,X11,k2_tarski(X8,X9)),sK2(X12,X13,k2_tarski(X8,X9)),k2_tarski(X8,X9)) = X9
    | k2_tarski(X8,X9) = k2_tarski(sK2(X10,X11,k2_tarski(X8,X9)),sK2(X12,X13,k2_tarski(X8,X9)))
    | sK2(X10,X11,k2_tarski(X8,X9)) = X11
    | sK2(X10,X11,k2_tarski(X8,X9)) = X10
    | k2_tarski(X10,X11) = k2_tarski(X8,X9)
    | sK2(X12,X13,k2_tarski(X8,X9)) = X13
    | sK2(X12,X13,k2_tarski(X8,X9)) = X12
    | k2_tarski(X8,X9) = k2_tarski(X12,X13) )).

cnf(u1770,axiom,
    ( sK2(sK2(X6,X7,k2_tarski(X4,X5)),sK2(X6,X7,k2_tarski(X4,X5)),k2_tarski(X4,X5)) = X4
    | sK2(sK2(X6,X7,k2_tarski(X4,X5)),sK2(X6,X7,k2_tarski(X4,X5)),k2_tarski(X4,X5)) = X5
    | k2_tarski(X4,X5) = k2_tarski(sK2(X6,X7,k2_tarski(X4,X5)),sK2(X6,X7,k2_tarski(X4,X5)))
    | sK2(X6,X7,k2_tarski(X4,X5)) = X7
    | sK2(X6,X7,k2_tarski(X4,X5)) = X6
    | k2_tarski(X6,X7) = k2_tarski(X4,X5) )).

cnf(u1770_004,axiom,
    ( sK2(sK2(X6,X7,k2_tarski(X4,X5)),sK2(X6,X7,k2_tarski(X4,X5)),k2_tarski(X4,X5)) = X4
    | sK2(sK2(X6,X7,k2_tarski(X4,X5)),sK2(X6,X7,k2_tarski(X4,X5)),k2_tarski(X4,X5)) = X5
    | k2_tarski(X4,X5) = k2_tarski(sK2(X6,X7,k2_tarski(X4,X5)),sK2(X6,X7,k2_tarski(X4,X5)))
    | sK2(X6,X7,k2_tarski(X4,X5)) = X7
    | sK2(X6,X7,k2_tarski(X4,X5)) = X6
    | k2_tarski(X6,X7) = k2_tarski(X4,X5) )).

cnf(u245,axiom,
    ( sK2(sK2(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X10
    | sK2(sK2(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X6
    | sK2(sK2(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X7
    | k2_tarski(X6,X7) = k2_tarski(sK2(X8,X9,k2_tarski(X6,X7)),X10)
    | sK2(X8,X9,k2_tarski(X6,X7)) = X9
    | sK2(X8,X9,k2_tarski(X6,X7)) = X8
    | k2_tarski(X6,X7) = k2_tarski(X8,X9) )).

cnf(u245_005,axiom,
    ( sK2(sK2(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X10
    | sK2(sK2(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X6
    | sK2(sK2(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X7
    | k2_tarski(X6,X7) = k2_tarski(sK2(X8,X9,k2_tarski(X6,X7)),X10)
    | sK2(X8,X9,k2_tarski(X6,X7)) = X9
    | sK2(X8,X9,k2_tarski(X6,X7)) = X8
    | k2_tarski(X6,X7) = k2_tarski(X8,X9) )).

cnf(u245_006,axiom,
    ( sK2(sK2(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X10
    | sK2(sK2(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X6
    | sK2(sK2(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X7
    | k2_tarski(X6,X7) = k2_tarski(sK2(X8,X9,k2_tarski(X6,X7)),X10)
    | sK2(X8,X9,k2_tarski(X6,X7)) = X9
    | sK2(X8,X9,k2_tarski(X6,X7)) = X8
    | k2_tarski(X6,X7) = k2_tarski(X8,X9) )).

cnf(u2612,axiom,
    ( sK2(sK2(X2,X3,k2_tarski(X1,X0)),X0,k2_tarski(X1,X0)) = X1
    | k2_tarski(X1,X0) = k2_tarski(X0,sK2(X2,X3,k2_tarski(X1,X0)))
    | sK2(X2,X3,k2_tarski(X1,X0)) = X3
    | sK2(X2,X3,k2_tarski(X1,X0)) = X2
    | k2_tarski(X1,X0) = k2_tarski(X2,X3) )).

cnf(u1931,axiom,
    ( sK2(sK2(X4,X5,k2_tarski(X6,X7)),X6,k2_tarski(X6,X7)) = X7
    | k2_tarski(X6,X7) = k2_tarski(X6,sK2(X4,X5,k2_tarski(X6,X7)))
    | sK2(X4,X5,k2_tarski(X6,X7)) = X5
    | sK2(X4,X5,k2_tarski(X6,X7)) = X4
    | k2_tarski(X6,X7) = k2_tarski(X4,X5) )).

cnf(u2222,axiom,
    ( sK2(X4,sK2(X5,X6,k2_tarski(X4,X7)),k2_tarski(X4,X7)) = X7
    | k2_tarski(X4,X7) = k2_tarski(X4,sK2(X5,X6,k2_tarski(X4,X7)))
    | sK2(X5,X6,k2_tarski(X4,X7)) = X6
    | sK2(X5,X6,k2_tarski(X4,X7)) = X5
    | k2_tarski(X5,X6) = k2_tarski(X4,X7) )).

cnf(u2219,axiom,
    ( sK2(X4,sK2(X5,X6,k2_tarski(X7,X7)),k2_tarski(X7,X7)) = X4
    | sK2(X4,sK2(X5,X6,k2_tarski(X7,X7)),k2_tarski(X7,X7)) = X7
    | k2_tarski(X7,X7) = k2_tarski(X4,sK2(X5,X6,k2_tarski(X7,X7)))
    | sK2(X5,X6,k2_tarski(X7,X7)) = X6
    | sK2(X5,X6,k2_tarski(X7,X7)) = X5
    | k2_tarski(X7,X7) = k2_tarski(X5,X6) )).

cnf(u2219_007,axiom,
    ( sK2(X4,sK2(X5,X6,k2_tarski(X7,X7)),k2_tarski(X7,X7)) = X4
    | sK2(X4,sK2(X5,X6,k2_tarski(X7,X7)),k2_tarski(X7,X7)) = X7
    | k2_tarski(X7,X7) = k2_tarski(X4,sK2(X5,X6,k2_tarski(X7,X7)))
    | sK2(X5,X6,k2_tarski(X7,X7)) = X6
    | sK2(X5,X6,k2_tarski(X7,X7)) = X5
    | k2_tarski(X7,X7) = k2_tarski(X5,X6) )).

cnf(u2726,axiom,
    ( sK2(X0,sK2(X2,X3,k2_tarski(X1,X0)),k2_tarski(X1,X0)) = X1
    | k2_tarski(X1,X0) = k2_tarski(X0,sK2(X2,X3,k2_tarski(X1,X0)))
    | sK2(X2,X3,k2_tarski(X1,X0)) = X3
    | sK2(X2,X3,k2_tarski(X1,X0)) = X2
    | k2_tarski(X1,X0) = k2_tarski(X2,X3) )).

cnf(u267,axiom,
    ( sK2(X8,sK2(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X8
    | sK2(X8,sK2(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X6
    | sK2(X8,sK2(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X7
    | k2_tarski(X6,X7) = k2_tarski(X8,sK2(X9,X10,k2_tarski(X6,X7)))
    | sK2(X9,X10,k2_tarski(X6,X7)) = X10
    | sK2(X9,X10,k2_tarski(X6,X7)) = X9
    | k2_tarski(X6,X7) = k2_tarski(X9,X10) )).

cnf(u267_008,axiom,
    ( sK2(X8,sK2(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X8
    | sK2(X8,sK2(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X6
    | sK2(X8,sK2(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X7
    | k2_tarski(X6,X7) = k2_tarski(X8,sK2(X9,X10,k2_tarski(X6,X7)))
    | sK2(X9,X10,k2_tarski(X6,X7)) = X10
    | sK2(X9,X10,k2_tarski(X6,X7)) = X9
    | k2_tarski(X6,X7) = k2_tarski(X9,X10) )).

cnf(u267_009,axiom,
    ( sK2(X8,sK2(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X8
    | sK2(X8,sK2(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X6
    | sK2(X8,sK2(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X7
    | k2_tarski(X6,X7) = k2_tarski(X8,sK2(X9,X10,k2_tarski(X6,X7)))
    | sK2(X9,X10,k2_tarski(X6,X7)) = X10
    | sK2(X9,X10,k2_tarski(X6,X7)) = X9
    | k2_tarski(X6,X7) = k2_tarski(X9,X10) )).

cnf(u118,axiom,
    ( sK2(X0,X0,k2_tarski(X1,X2)) = X0
    | sK2(X0,X0,k2_tarski(X1,X2)) = X1
    | sK2(X0,X0,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X0) = k2_tarski(X1,X2) )).

cnf(u205,axiom,
    ( sK2(X0,X0,k2_tarski(X0,X1)) = X0
    | sK2(X0,X0,k2_tarski(X0,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X0,X0) )).

cnf(u242,axiom,
    ( sK2(X1,X1,k2_tarski(X1,X2)) = X2
    | k2_tarski(X1,X1) = k2_tarski(X1,X2) )).

cnf(u545,axiom,
    ( sK2(X0,X0,k2_tarski(X1,X1)) = X0
    | sK2(X0,X0,k2_tarski(X1,X1)) = X1
    | k2_tarski(X0,X0) = k2_tarski(X1,X1) )).

cnf(u270,axiom,
    ( sK2(X0,X0,k2_tarski(X1,X0)) = X1
    | sK2(X0,X0,k2_tarski(X1,X0)) = X0
    | k2_tarski(X0,X0) = k2_tarski(X1,X0) )).

cnf(u304,axiom,
    ( sK2(X0,X0,k2_tarski(X1,X0)) = X1
    | k2_tarski(X0,X0) = k2_tarski(X1,X0) )).

cnf(u118_010,axiom,
    ( sK2(X0,X0,k2_tarski(X1,X2)) = X0
    | sK2(X0,X0,k2_tarski(X1,X2)) = X1
    | sK2(X0,X0,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X0) = k2_tarski(X1,X2) )).

cnf(u205_011,axiom,
    ( sK2(X0,X0,k2_tarski(X0,X1)) = X0
    | sK2(X0,X0,k2_tarski(X0,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X0,X0) )).

cnf(u545_012,axiom,
    ( sK2(X0,X0,k2_tarski(X1,X1)) = X0
    | sK2(X0,X0,k2_tarski(X1,X1)) = X1
    | k2_tarski(X0,X0) = k2_tarski(X1,X1) )).

cnf(u270_013,axiom,
    ( sK2(X0,X0,k2_tarski(X1,X0)) = X1
    | sK2(X0,X0,k2_tarski(X1,X0)) = X0
    | k2_tarski(X0,X0) = k2_tarski(X1,X0) )).

cnf(u118_014,axiom,
    ( sK2(X0,X0,k2_tarski(X1,X2)) = X0
    | sK2(X0,X0,k2_tarski(X1,X2)) = X1
    | sK2(X0,X0,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X0) = k2_tarski(X1,X2) )).

cnf(u139,negated_conjecture,
    ( sK2(X0,X0,k6_domain_1(u1_struct_0(sK0),sK1)) = X0
    | k2_tarski(X0,X0) = k6_domain_1(u1_struct_0(sK0),sK1)
    | k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) )).

cnf(u121,negated_conjecture,
    ( sK2(X0,X1,k6_domain_1(u1_struct_0(sK0),sK1)) = X0
    | sK2(X0,X1,k6_domain_1(u1_struct_0(sK0),sK1)) = X1
    | k2_tarski(X0,X1) = k6_domain_1(u1_struct_0(sK0),sK1)
    | k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) )).

cnf(u121_015,negated_conjecture,
    ( sK2(X0,X1,k6_domain_1(u1_struct_0(sK0),sK1)) = X0
    | sK2(X0,X1,k6_domain_1(u1_struct_0(sK0),sK1)) = X1
    | k2_tarski(X0,X1) = k6_domain_1(u1_struct_0(sK0),sK1)
    | k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) )).

cnf(u1640,axiom,
    ( sK2(X0,X1,k2_tarski(X0,X0)) = X1
    | sK2(X0,X1,k2_tarski(X0,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X0,X0) )).

cnf(u1640_016,axiom,
    ( sK2(X0,X1,k2_tarski(X0,X0)) = X1
    | sK2(X0,X1,k2_tarski(X0,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X0,X0) )).

cnf(u1709,axiom,
    ( sK2(X0,X1,k2_tarski(X0,X0)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X0,X0) )).

cnf(u149,axiom,
    ( sK2(X0,X1,k2_tarski(X0,X2)) = X1
    | sK2(X0,X1,k2_tarski(X0,X2)) = X0
    | sK2(X0,X1,k2_tarski(X0,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u1933,axiom,
    ( sK2(X2,X4,k2_tarski(X2,X3)) = X4
    | sK2(X2,X4,k2_tarski(X2,X3)) = X3
    | k2_tarski(X2,X3) = k2_tarski(X2,X4) )).

cnf(u149_017,axiom,
    ( sK2(X0,X1,k2_tarski(X0,X2)) = X1
    | sK2(X0,X1,k2_tarski(X0,X2)) = X0
    | sK2(X0,X1,k2_tarski(X0,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u149_018,axiom,
    ( sK2(X0,X1,k2_tarski(X0,X2)) = X1
    | sK2(X0,X1,k2_tarski(X0,X2)) = X0
    | sK2(X0,X1,k2_tarski(X0,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u1933_019,axiom,
    ( sK2(X2,X4,k2_tarski(X2,X3)) = X4
    | sK2(X2,X4,k2_tarski(X2,X3)) = X3
    | k2_tarski(X2,X3) = k2_tarski(X2,X4) )).

cnf(u1515,axiom,
    ( sK2(X0,X1,k2_tarski(X1,X1)) = X0
    | sK2(X0,X1,k2_tarski(X1,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X1,X1) )).

cnf(u1515_020,axiom,
    ( sK2(X0,X1,k2_tarski(X1,X1)) = X0
    | sK2(X0,X1,k2_tarski(X1,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X1,X1) )).

cnf(u1583,axiom,
    ( sK2(X1,X0,k2_tarski(X0,X0)) = X1
    | k2_tarski(X0,X0) = k2_tarski(X1,X0) )).

cnf(u769,axiom,
    ( sK2(X0,X1,k2_tarski(X1,X0)) = X1
    | sK2(X0,X1,k2_tarski(X1,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

cnf(u769_021,axiom,
    ( sK2(X0,X1,k2_tarski(X1,X0)) = X1
    | sK2(X0,X1,k2_tarski(X1,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

cnf(u808,axiom,
    ( sK2(X1,X0,k2_tarski(X0,X1)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

cnf(u120,axiom,
    ( sK2(X0,X1,k2_tarski(X1,X2)) = X0
    | sK2(X0,X1,k2_tarski(X1,X2)) = X1
    | sK2(X0,X1,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u1774,axiom,
    ( sK2(X4,X2,k2_tarski(X2,X3)) = X4
    | sK2(X4,X2,k2_tarski(X2,X3)) = X3
    | k2_tarski(X2,X3) = k2_tarski(X4,X2) )).

cnf(u120_022,axiom,
    ( sK2(X0,X1,k2_tarski(X1,X2)) = X0
    | sK2(X0,X1,k2_tarski(X1,X2)) = X1
    | sK2(X0,X1,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u120_023,axiom,
    ( sK2(X0,X1,k2_tarski(X1,X2)) = X0
    | sK2(X0,X1,k2_tarski(X1,X2)) = X1
    | sK2(X0,X1,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u1774_024,axiom,
    ( sK2(X4,X2,k2_tarski(X2,X3)) = X4
    | sK2(X4,X2,k2_tarski(X2,X3)) = X3
    | k2_tarski(X2,X3) = k2_tarski(X4,X2) )).

cnf(u62,axiom,
    ( sK2(X4,X5,k2_tarski(X6,X7)) = X5
    | sK2(X4,X5,k2_tarski(X6,X7)) = X4
    | sK2(X4,X5,k2_tarski(X6,X7)) = X6
    | sK2(X4,X5,k2_tarski(X6,X7)) = X7
    | k2_tarski(X6,X7) = k2_tarski(X4,X5) )).

cnf(u62_025,axiom,
    ( sK2(X4,X5,k2_tarski(X6,X7)) = X5
    | sK2(X4,X5,k2_tarski(X6,X7)) = X4
    | sK2(X4,X5,k2_tarski(X6,X7)) = X6
    | sK2(X4,X5,k2_tarski(X6,X7)) = X7
    | k2_tarski(X6,X7) = k2_tarski(X4,X5) )).

cnf(u62_026,axiom,
    ( sK2(X4,X5,k2_tarski(X6,X7)) = X5
    | sK2(X4,X5,k2_tarski(X6,X7)) = X4
    | sK2(X4,X5,k2_tarski(X6,X7)) = X6
    | sK2(X4,X5,k2_tarski(X6,X7)) = X7
    | k2_tarski(X6,X7) = k2_tarski(X4,X5) )).

cnf(u62_027,axiom,
    ( sK2(X4,X5,k2_tarski(X6,X7)) = X5
    | sK2(X4,X5,k2_tarski(X6,X7)) = X4
    | sK2(X4,X5,k2_tarski(X6,X7)) = X6
    | sK2(X4,X5,k2_tarski(X6,X7)) = X7
    | k2_tarski(X6,X7) = k2_tarski(X4,X5) )).

cnf(u156,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X2)) = X1
    | sK2(X0,X1,k2_tarski(X2,X2)) = X0
    | sK2(X0,X1,k2_tarski(X2,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u156_028,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X2)) = X1
    | sK2(X0,X1,k2_tarski(X2,X2)) = X0
    | sK2(X0,X1,k2_tarski(X2,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u156_029,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X2)) = X1
    | sK2(X0,X1,k2_tarski(X2,X2)) = X0
    | sK2(X0,X1,k2_tarski(X2,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u138,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X1)) = X0
    | sK2(X0,X1,k2_tarski(X2,X1)) = X2
    | sK2(X0,X1,k2_tarski(X2,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u138_030,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X1)) = X0
    | sK2(X0,X1,k2_tarski(X2,X1)) = X2
    | sK2(X0,X1,k2_tarski(X2,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u1914,axiom,
    ( sK2(X2,X1,k2_tarski(X0,X1)) = X2
    | sK2(X2,X1,k2_tarski(X0,X1)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u138_031,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X1)) = X0
    | sK2(X0,X1,k2_tarski(X2,X1)) = X2
    | sK2(X0,X1,k2_tarski(X2,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u1914_032,axiom,
    ( sK2(X2,X1,k2_tarski(X0,X1)) = X2
    | sK2(X2,X1,k2_tarski(X0,X1)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u150,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X0)) = X1
    | sK2(X0,X1,k2_tarski(X2,X0)) = X2
    | sK2(X0,X1,k2_tarski(X2,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u150_033,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X0)) = X1
    | sK2(X0,X1,k2_tarski(X2,X0)) = X2
    | sK2(X0,X1,k2_tarski(X2,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u2070,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X0)) = X1
    | sK2(X0,X1,k2_tarski(X2,X0)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u150_034,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X0)) = X1
    | sK2(X0,X1,k2_tarski(X2,X0)) = X2
    | sK2(X0,X1,k2_tarski(X2,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u2070_035,axiom,
    ( sK2(X0,X1,k2_tarski(X2,X0)) = X1
    | sK2(X0,X1,k2_tarski(X2,X0)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u4653,axiom,
    ( X2 != X3
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X4,X5,k2_tarski(X2,X3)),k2_tarski(X2,X3)) = X2
    | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X4,X5,k2_tarski(X2,X3)))
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X3)
    | sK2(X4,X5,k2_tarski(X2,X3)) = X5
    | sK2(X4,X5,k2_tarski(X2,X3)) = X4
    | k2_tarski(X4,X5) = k2_tarski(X2,X3) )).

cnf(u4652,axiom,
    ( X2 != X3
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X4,X5,k2_tarski(X2,X3)),k2_tarski(X2,X3)) = X3
    | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X4,X5,k2_tarski(X2,X3)))
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X3)
    | sK2(X4,X5,k2_tarski(X2,X3)) = X5
    | sK2(X4,X5,k2_tarski(X2,X3)) = X4
    | k2_tarski(X4,X5) = k2_tarski(X2,X3) )).

cnf(u4179,axiom,
    ( X2 != X3
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X0,X1,k2_tarski(X2,X3)),k2_tarski(X2,X3)) = X2
    | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X0,X1,k2_tarski(X2,X3)))
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u4178,axiom,
    ( X2 != X3
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X0,X1,k2_tarski(X2,X3)),k2_tarski(X2,X3)) = X3
    | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X0,X1,k2_tarski(X2,X3)))
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u3702,axiom,
    ( X0 != X3
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X3)),k2_tarski(X3,X3)) = X0
    | k2_tarski(X3,X3) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X3)))
    | sK2(X1,X2,k2_tarski(X3,X3)) = X2
    | sK2(X1,X2,k2_tarski(X3,X3)) = X1
    | k2_tarski(X1,X2) = k2_tarski(X3,X3) )).

cnf(u3701,axiom,
    ( X0 != X3
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X3)),k2_tarski(X3,X3)) = X3
    | k2_tarski(X3,X3) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X3)))
    | sK2(X1,X2,k2_tarski(X3,X3)) = X2
    | sK2(X1,X2,k2_tarski(X3,X3)) = X1
    | k2_tarski(X1,X2) = k2_tarski(X3,X3) )).

cnf(u3421,axiom,
    ( X2 != X3
    | sK2(sK2(X0,X1,k2_tarski(X2,X2)),X3,k2_tarski(X2,X2)) = X3
    | k2_tarski(X2,X2) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X2)),X3)
    | sK2(X0,X1,k2_tarski(X2,X2)) = X1
    | sK2(X0,X1,k2_tarski(X2,X2)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u3420,axiom,
    ( X2 != X3
    | sK2(sK2(X0,X1,k2_tarski(X2,X2)),X3,k2_tarski(X2,X2)) = X2
    | k2_tarski(X2,X2) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X2)),X3)
    | sK2(X0,X1,k2_tarski(X2,X2)) = X1
    | sK2(X0,X1,k2_tarski(X2,X2)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u2921,axiom,
    ( X138 != X139
    | k2_tarski(X138,X139) = k2_tarski(X139,sK2(X136,X137,k2_tarski(X138,X139)))
    | ~ r2_hidden(X139,k2_tarski(X138,X139))
    | sK2(X136,X137,k2_tarski(X138,X139)) = X137
    | sK2(X136,X137,k2_tarski(X138,X139)) = X136
    | k2_tarski(X138,X139) = k2_tarski(X136,X137) )).

cnf(u2667,axiom,
    ( X127 != X128
    | k2_tarski(X127,X128) = k2_tarski(X127,sK2(X125,X126,k2_tarski(X127,X128)))
    | ~ r2_hidden(X127,k2_tarski(X127,X128))
    | sK2(X125,X126,k2_tarski(X127,X128)) = X126
    | sK2(X125,X126,k2_tarski(X127,X128)) = X125
    | k2_tarski(X127,X128) = k2_tarski(X125,X126) )).

cnf(u2366,axiom,
    ( X99 != X100
    | k2_tarski(X99,X100) = k2_tarski(X101,X99)
    | ~ r2_hidden(X99,k2_tarski(X101,X99))
    | sK2(X99,X100,k2_tarski(X101,X99)) = X101 )).

cnf(u2351,axiom,
    ( X99 != X101
    | k2_tarski(X99,X100) = k2_tarski(X101,X99)
    | ~ r2_hidden(X99,k2_tarski(X101,X99))
    | sK2(X99,X100,k2_tarski(X101,X99)) = X100 )).

cnf(u2349,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X2,X0)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u2348,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X2,X0)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u2209,axiom,
    ( X92 != X93
    | k2_tarski(X92,X93) = k2_tarski(X92,X94)
    | ~ r2_hidden(X92,k2_tarski(X92,X94))
    | sK2(X92,X93,k2_tarski(X92,X94)) = X94 )).

cnf(u2194,axiom,
    ( X92 != X94
    | k2_tarski(X92,X93) = k2_tarski(X92,X94)
    | ~ r2_hidden(X92,k2_tarski(X92,X94))
    | sK2(X92,X93,k2_tarski(X92,X94)) = X93 )).

cnf(u2192,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X0,X2)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u2191,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X0,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u2065,axiom,
    ( X91 != X92
    | k2_tarski(X91,X92) = k2_tarski(X93,X92)
    | ~ r2_hidden(X92,k2_tarski(X93,X92))
    | sK2(X91,X92,k2_tarski(X93,X92)) = X93 )).

cnf(u2051,axiom,
    ( X92 != X93
    | k2_tarski(X91,X92) = k2_tarski(X93,X92)
    | ~ r2_hidden(X92,k2_tarski(X93,X92))
    | sK2(X91,X92,k2_tarski(X93,X92)) = X91 )).

cnf(u2050,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X2,X1)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u2049,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X2,X1)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u1905,axiom,
    ( X90 != X91
    | k2_tarski(X90,X91) = k2_tarski(X91,X92)
    | ~ r2_hidden(X91,k2_tarski(X91,X92))
    | sK2(X90,X91,k2_tarski(X91,X92)) = X92 )).

cnf(u1891,axiom,
    ( X91 != X92
    | k2_tarski(X90,X91) = k2_tarski(X91,X92)
    | ~ r2_hidden(X91,k2_tarski(X91,X92))
    | sK2(X90,X91,k2_tarski(X91,X92)) = X90 )).

cnf(u1890,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X1,X2)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u1889,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u1751,axiom,
    ( X62 != X63
    | k2_tarski(X62,X62) = k2_tarski(X62,X63)
    | ~ r2_hidden(X62,k2_tarski(X62,X62)) )).

cnf(u1695,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X0,X0)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X0,X0) )).

cnf(u1694,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X0,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X0,X0) )).

cnf(u1623,axiom,
    ( X61 != X62
    | k2_tarski(X61,X62) = k2_tarski(X62,X62)
    | ~ r2_hidden(X62,k2_tarski(X62,X62)) )).

cnf(u1569,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X1,X1)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X1,X1) )).

cnf(u1568,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X1,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X1,X1) )).

cnf(u1424,axiom,
    ( X3 != X4
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X0
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X3
    | k2_tarski(X3,X4) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X4)))
    | sK2(X1,X2,k2_tarski(X3,X4)) = X2
    | sK2(X1,X2,k2_tarski(X3,X4)) = X1
    | k2_tarski(X3,X4) = k2_tarski(X1,X2) )).

cnf(u1423,axiom,
    ( X0 != X4
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X0
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X3
    | k2_tarski(X3,X4) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X4)))
    | sK2(X1,X2,k2_tarski(X3,X4)) = X2
    | sK2(X1,X2,k2_tarski(X3,X4)) = X1
    | k2_tarski(X3,X4) = k2_tarski(X1,X2) )).

cnf(u1422,axiom,
    ( X3 != X4
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X0
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X4
    | k2_tarski(X3,X4) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X4)))
    | sK2(X1,X2,k2_tarski(X3,X4)) = X2
    | sK2(X1,X2,k2_tarski(X3,X4)) = X1
    | k2_tarski(X3,X4) = k2_tarski(X1,X2) )).

cnf(u1421,axiom,
    ( X0 != X3
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X0
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X4
    | k2_tarski(X3,X4) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X4)))
    | sK2(X1,X2,k2_tarski(X3,X4)) = X2
    | sK2(X1,X2,k2_tarski(X3,X4)) = X1
    | k2_tarski(X3,X4) = k2_tarski(X1,X2) )).

cnf(u1420,axiom,
    ( X0 != X4
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X3
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X4
    | k2_tarski(X3,X4) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X4)))
    | sK2(X1,X2,k2_tarski(X3,X4)) = X2
    | sK2(X1,X2,k2_tarski(X3,X4)) = X1
    | k2_tarski(X3,X4) = k2_tarski(X1,X2) )).

cnf(u1419,axiom,
    ( X0 != X3
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X3
    | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X4
    | k2_tarski(X3,X4) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X4)))
    | sK2(X1,X2,k2_tarski(X3,X4)) = X2
    | sK2(X1,X2,k2_tarski(X3,X4)) = X1
    | k2_tarski(X3,X4) = k2_tarski(X1,X2) )).

cnf(u1032,axiom,
    ( X2 != X3
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X4
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X2
    | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),X4)
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u1031,axiom,
    ( X3 != X4
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X4
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X2
    | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),X4)
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u1030,axiom,
    ( X2 != X3
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X4
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X3
    | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),X4)
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u1029,axiom,
    ( X2 != X4
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X4
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X3
    | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),X4)
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u1028,axiom,
    ( X3 != X4
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X2
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X3
    | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),X4)
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u1027,axiom,
    ( X2 != X4
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X2
    | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X3
    | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),X4)
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u799,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X1,X0)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

cnf(u798,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X1,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

cnf(u756,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X2,X2)) = X1
    | sK2(X0,X1,k2_tarski(X2,X2)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u755,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X2,X2)) = X1
    | sK2(X0,X1,k2_tarski(X2,X2)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u754,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X2,X2)) = X1
    | sK2(X0,X1,k2_tarski(X2,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u753,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X2,X2)) = X1
    | sK2(X0,X1,k2_tarski(X2,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u752,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X2,X2)) = X0
    | sK2(X0,X1,k2_tarski(X2,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u751,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X2,X2)) = X0
    | sK2(X0,X1,k2_tarski(X2,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X2) )).

cnf(u659,axiom,
    ( X0 != X1
    | sK2(X0,X0,k2_tarski(X1,X1)) = X0
    | k2_tarski(X0,X0) = k2_tarski(X1,X1) )).

cnf(u658,axiom,
    ( X0 != X1
    | sK2(X0,X0,k2_tarski(X1,X1)) = X1
    | k2_tarski(X0,X0) = k2_tarski(X1,X1) )).

cnf(u626,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X2,X0)) = X1
    | sK2(X0,X1,k2_tarski(X2,X0)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u625,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X2,X0)) = X1
    | sK2(X0,X1,k2_tarski(X2,X0)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u624,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X2,X0)) = X1
    | sK2(X0,X1,k2_tarski(X2,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u623,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X2,X0)) = X1
    | sK2(X0,X1,k2_tarski(X2,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u622,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X2,X0)) = X2
    | sK2(X0,X1,k2_tarski(X2,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u621,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X2,X0)) = X2
    | sK2(X0,X1,k2_tarski(X2,X0)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X2,X0) )).

cnf(u535,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X0,X2)) = X1
    | sK2(X0,X1,k2_tarski(X0,X2)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u534,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X0,X2)) = X1
    | sK2(X0,X1,k2_tarski(X0,X2)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u533,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X0,X2)) = X1
    | sK2(X0,X1,k2_tarski(X0,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u532,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X0,X2)) = X1
    | sK2(X0,X1,k2_tarski(X0,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u531,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X0,X2)) = X0
    | sK2(X0,X1,k2_tarski(X0,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u530,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X0,X2)) = X0
    | sK2(X0,X1,k2_tarski(X0,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X0,X2) )).

cnf(u452,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X2,X1)) = X0
    | sK2(X0,X1,k2_tarski(X2,X1)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u451,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X2,X1)) = X0
    | sK2(X0,X1,k2_tarski(X2,X1)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u450,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X2,X1)) = X0
    | sK2(X0,X1,k2_tarski(X2,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u449,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X2,X1)) = X0
    | sK2(X0,X1,k2_tarski(X2,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u448,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X2,X1)) = X2
    | sK2(X0,X1,k2_tarski(X2,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u447,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X2,X1)) = X2
    | sK2(X0,X1,k2_tarski(X2,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X2,X1) )).

cnf(u380,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X1,X2)) = X0
    | sK2(X0,X1,k2_tarski(X1,X2)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u379,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X1,X2)) = X0
    | sK2(X0,X1,k2_tarski(X1,X2)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u378,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X1,X2)) = X0
    | sK2(X0,X1,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u377,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X1,X2)) = X0
    | sK2(X0,X1,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u376,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X1,X2)) = X1
    | sK2(X0,X1,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u375,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X1,X2)) = X1
    | sK2(X0,X1,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X1,X2) )).

cnf(u321,axiom,
    ( X12 != X13
    | k2_tarski(X12,X12) = k2_tarski(X13,X12)
    | ~ r2_hidden(X12,k2_tarski(X13,X12)) )).

cnf(u294,axiom,
    ( X0 != X1
    | sK2(X0,X0,k2_tarski(X1,X0)) = X1
    | k2_tarski(X0,X0) = k2_tarski(X1,X0) )).

cnf(u293,axiom,
    ( X0 != X1
    | sK2(X0,X0,k2_tarski(X1,X0)) = X0
    | k2_tarski(X0,X0) = k2_tarski(X1,X0) )).

cnf(u261,axiom,
    ( X12 != X13
    | k2_tarski(X12,X12) = k2_tarski(X12,X13)
    | ~ r2_hidden(X12,k2_tarski(X12,X13)) )).

cnf(u229,axiom,
    ( X0 != X1
    | sK2(X0,X0,k2_tarski(X0,X1)) = X0
    | k2_tarski(X0,X1) = k2_tarski(X0,X0) )).

cnf(u228,axiom,
    ( X0 != X1
    | sK2(X0,X0,k2_tarski(X0,X1)) = X1
    | k2_tarski(X0,X1) = k2_tarski(X0,X0) )).

cnf(u193,axiom,
    ( X1 != X2
    | sK2(X0,X0,k2_tarski(X1,X2)) = X0
    | sK2(X0,X0,k2_tarski(X1,X2)) = X1
    | k2_tarski(X0,X0) = k2_tarski(X1,X2) )).

cnf(u192,axiom,
    ( X0 != X2
    | sK2(X0,X0,k2_tarski(X1,X2)) = X0
    | sK2(X0,X0,k2_tarski(X1,X2)) = X1
    | k2_tarski(X0,X0) = k2_tarski(X1,X2) )).

cnf(u191,axiom,
    ( X1 != X2
    | sK2(X0,X0,k2_tarski(X1,X2)) = X0
    | sK2(X0,X0,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X0) = k2_tarski(X1,X2) )).

cnf(u190,axiom,
    ( X0 != X1
    | sK2(X0,X0,k2_tarski(X1,X2)) = X0
    | sK2(X0,X0,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X0) = k2_tarski(X1,X2) )).

cnf(u189,axiom,
    ( X0 != X2
    | sK2(X0,X0,k2_tarski(X1,X2)) = X1
    | sK2(X0,X0,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X0) = k2_tarski(X1,X2) )).

cnf(u188,axiom,
    ( X0 != X1
    | sK2(X0,X0,k2_tarski(X1,X2)) = X1
    | sK2(X0,X0,k2_tarski(X1,X2)) = X2
    | k2_tarski(X0,X0) = k2_tarski(X1,X2) )).

cnf(u131,negated_conjecture,
    ( X0 != X1
    | sK2(X0,X1,k6_domain_1(u1_struct_0(sK0),sK1)) = X0
    | k2_tarski(X0,X1) = k6_domain_1(u1_struct_0(sK0),sK1)
    | k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) )).

cnf(u130,negated_conjecture,
    ( X0 != X1
    | sK2(X0,X1,k6_domain_1(u1_struct_0(sK0),sK1)) = X1
    | k2_tarski(X0,X1) = k6_domain_1(u1_struct_0(sK0),sK1)
    | k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) )).

cnf(u103,axiom,
    ( X2 != X3
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | sK2(X0,X1,k2_tarski(X2,X3)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u102,axiom,
    ( X0 != X3
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | sK2(X0,X1,k2_tarski(X2,X3)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u101,axiom,
    ( X1 != X3
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | sK2(X0,X1,k2_tarski(X2,X3)) = X2
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u100,axiom,
    ( X2 != X3
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | sK2(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u99,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | sK2(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u98,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | sK2(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u97,axiom,
    ( X0 != X3
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X2
    | sK2(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u96,axiom,
    ( X0 != X2
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X2
    | sK2(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u95,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X2
    | sK2(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u94,axiom,
    ( X1 != X3
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | sK2(X0,X1,k2_tarski(X2,X3)) = X2
    | sK2(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u93,axiom,
    ( X1 != X2
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | sK2(X0,X1,k2_tarski(X2,X3)) = X2
    | sK2(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u92,axiom,
    ( X0 != X1
    | sK2(X0,X1,k2_tarski(X2,X3)) = X0
    | sK2(X0,X1,k2_tarski(X2,X3)) = X2
    | sK2(X0,X1,k2_tarski(X2,X3)) = X3
    | k2_tarski(X0,X1) = k2_tarski(X2,X3) )).

cnf(u3436,axiom,
    ( sK2(X150,X151,k2_tarski(X152,X152)) != X153
    | k2_tarski(X152,X152) = k2_tarski(sK2(X150,X151,k2_tarski(X152,X152)),X153)
    | ~ r2_hidden(sK2(X150,X151,k2_tarski(X152,X152)),k2_tarski(X152,X152))
    | sK2(sK2(X150,X151,k2_tarski(X152,X152)),X153,k2_tarski(X152,X152)) = X152
    | sK2(X150,X151,k2_tarski(X152,X152)) = X151
    | sK2(X150,X151,k2_tarski(X152,X152)) = X150
    | k2_tarski(X152,X152) = k2_tarski(X150,X151) )).

cnf(u3720,axiom,
    ( sK2(X162,X163,k2_tarski(X164,X164)) != X161
    | k2_tarski(X164,X164) = k2_tarski(X161,sK2(X162,X163,k2_tarski(X164,X164)))
    | ~ r2_hidden(sK2(X162,X163,k2_tarski(X164,X164)),k2_tarski(X164,X164))
    | sK2(X161,sK2(X162,X163,k2_tarski(X164,X164)),k2_tarski(X164,X164)) = X164
    | sK2(X162,X163,k2_tarski(X164,X164)) = X163
    | sK2(X162,X163,k2_tarski(X164,X164)) = X162
    | k2_tarski(X164,X164) = k2_tarski(X162,X163) )).

cnf(u1041,axiom,
    ( sK2(X61,X62,k2_tarski(X63,X64)) != X65
    | k2_tarski(X63,X64) = k2_tarski(sK2(X61,X62,k2_tarski(X63,X64)),X65)
    | ~ r2_hidden(sK2(X61,X62,k2_tarski(X63,X64)),k2_tarski(X63,X64))
    | sK2(sK2(X61,X62,k2_tarski(X63,X64)),X65,k2_tarski(X63,X64)) = X63
    | sK2(sK2(X61,X62,k2_tarski(X63,X64)),X65,k2_tarski(X63,X64)) = X64
    | sK2(X61,X62,k2_tarski(X63,X64)) = X62
    | sK2(X61,X62,k2_tarski(X63,X64)) = X61
    | k2_tarski(X61,X62) = k2_tarski(X63,X64) )).

cnf(u1440,axiom,
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
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:38:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (22161)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.52  % (22153)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.52  % (22143)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (22148)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.52  % (22145)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.52  % (22138)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.53  % (22149)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.53  % (22159)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.53  % (22139)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.53  % (22139)Refutation not found, incomplete strategy% (22139)------------------------------
% 0.22/0.53  % (22139)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (22139)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (22139)Memory used [KB]: 1663
% 0.22/0.53  % (22139)Time elapsed: 0.123 s
% 0.22/0.53  % (22139)------------------------------
% 0.22/0.53  % (22139)------------------------------
% 0.22/0.54  % (22158)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.54  % (22142)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (22140)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (22142)Refutation not found, incomplete strategy% (22142)------------------------------
% 0.22/0.54  % (22142)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (22142)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (22142)Memory used [KB]: 1791
% 0.22/0.54  % (22142)Time elapsed: 0.127 s
% 0.22/0.54  % (22142)------------------------------
% 0.22/0.54  % (22142)------------------------------
% 0.22/0.54  % (22167)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (22164)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (22167)Refutation not found, incomplete strategy% (22167)------------------------------
% 0.22/0.54  % (22167)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (22167)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (22167)Memory used [KB]: 1663
% 0.22/0.54  % (22167)Time elapsed: 0.001 s
% 0.22/0.54  % (22167)------------------------------
% 0.22/0.54  % (22167)------------------------------
% 0.22/0.55  % (22151)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.55  % (22141)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.55  % (22150)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.55  % (22144)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (22146)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.55  % (22150)Refutation not found, incomplete strategy% (22150)------------------------------
% 0.22/0.55  % (22150)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (22150)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (22150)Memory used [KB]: 10618
% 0.22/0.55  % (22150)Time elapsed: 0.001 s
% 0.22/0.55  % (22150)------------------------------
% 0.22/0.55  % (22150)------------------------------
% 0.22/0.55  % (22149)Refutation not found, incomplete strategy% (22149)------------------------------
% 0.22/0.55  % (22149)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (22149)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (22149)Memory used [KB]: 6268
% 0.22/0.55  % (22149)Time elapsed: 0.117 s
% 0.22/0.55  % (22149)------------------------------
% 0.22/0.55  % (22149)------------------------------
% 0.22/0.55  % (22148)Refutation not found, incomplete strategy% (22148)------------------------------
% 0.22/0.55  % (22148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (22148)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (22148)Memory used [KB]: 10618
% 0.22/0.55  % (22148)Time elapsed: 0.144 s
% 0.22/0.55  % (22148)------------------------------
% 0.22/0.55  % (22148)------------------------------
% 0.22/0.55  % (22165)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.56  % (22156)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.56  % (22156)Refutation not found, incomplete strategy% (22156)------------------------------
% 0.22/0.56  % (22156)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (22156)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (22156)Memory used [KB]: 1663
% 0.22/0.56  % (22156)Time elapsed: 0.150 s
% 0.22/0.56  % (22156)------------------------------
% 0.22/0.56  % (22156)------------------------------
% 0.22/0.56  % (22154)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.56  % (22157)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.56  % (22165)Refutation not found, incomplete strategy% (22165)------------------------------
% 0.22/0.56  % (22165)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (22165)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (22165)Memory used [KB]: 6140
% 0.22/0.56  % (22165)Time elapsed: 0.149 s
% 0.22/0.56  % (22165)------------------------------
% 0.22/0.56  % (22165)------------------------------
% 0.22/0.56  % (22154)Refutation not found, incomplete strategy% (22154)------------------------------
% 0.22/0.56  % (22154)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (22154)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (22154)Memory used [KB]: 10618
% 0.22/0.56  % (22154)Time elapsed: 0.147 s
% 0.22/0.56  % (22154)------------------------------
% 0.22/0.56  % (22154)------------------------------
% 0.22/0.56  % (22162)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.56  % (22164)Refutation not found, incomplete strategy% (22164)------------------------------
% 0.22/0.56  % (22164)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (22164)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (22164)Memory used [KB]: 6140
% 0.22/0.56  % (22164)Time elapsed: 0.159 s
% 0.22/0.56  % (22164)------------------------------
% 0.22/0.56  % (22164)------------------------------
% 0.22/0.56  % (22147)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.56  % (22163)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.56  % (22155)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.56  % (22163)Refutation not found, incomplete strategy% (22163)------------------------------
% 0.22/0.56  % (22163)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (22163)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (22163)Memory used [KB]: 6140
% 0.22/0.56  % (22163)Time elapsed: 0.161 s
% 0.22/0.56  % (22163)------------------------------
% 0.22/0.56  % (22163)------------------------------
% 0.22/0.56  % (22160)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.61/0.57  % (22155)Refutation not found, incomplete strategy% (22155)------------------------------
% 1.61/0.57  % (22155)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.57  % (22155)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.57  
% 1.61/0.57  % (22155)Memory used [KB]: 1663
% 1.61/0.57  % (22155)Time elapsed: 0.157 s
% 1.61/0.57  % (22155)------------------------------
% 1.61/0.57  % (22155)------------------------------
% 1.61/0.57  % (22152)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.61/0.57  % (22152)Refutation not found, incomplete strategy% (22152)------------------------------
% 1.61/0.57  % (22152)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.57  % (22152)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.57  
% 1.61/0.57  % (22152)Memory used [KB]: 1791
% 1.61/0.57  % (22152)Time elapsed: 0.146 s
% 1.61/0.57  % (22152)------------------------------
% 1.61/0.57  % (22152)------------------------------
% 1.61/0.57  % (22166)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.61/0.58  % (22166)Refutation not found, incomplete strategy% (22166)------------------------------
% 1.61/0.58  % (22166)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.58  % (22166)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.58  
% 1.61/0.58  % (22166)Memory used [KB]: 10746
% 1.61/0.58  % (22166)Time elapsed: 0.170 s
% 1.61/0.58  % (22166)------------------------------
% 1.61/0.58  % (22166)------------------------------
% 1.61/0.58  % (22162)Refutation not found, incomplete strategy% (22162)------------------------------
% 1.61/0.58  % (22162)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.58  % (22162)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.58  
% 1.61/0.58  % (22162)Memory used [KB]: 10618
% 1.61/0.58  % (22162)Time elapsed: 0.169 s
% 1.61/0.58  % (22162)------------------------------
% 1.61/0.58  % (22162)------------------------------
% 2.04/0.66  % (22189)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.04/0.67  % (22198)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 2.04/0.67  % (22141)Refutation not found, incomplete strategy% (22141)------------------------------
% 2.04/0.67  % (22141)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.04/0.67  % (22141)Termination reason: Refutation not found, incomplete strategy
% 2.04/0.67  
% 2.04/0.67  % (22141)Memory used [KB]: 6140
% 2.04/0.67  % (22141)Time elapsed: 0.266 s
% 2.04/0.67  % (22141)------------------------------
% 2.04/0.67  % (22141)------------------------------
% 2.04/0.67  % (22190)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.04/0.68  % (22198)Refutation not found, incomplete strategy% (22198)------------------------------
% 2.04/0.68  % (22198)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.04/0.68  % (22200)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 2.04/0.68  % (22198)Termination reason: Refutation not found, incomplete strategy
% 2.04/0.68  
% 2.04/0.68  % (22198)Memory used [KB]: 10746
% 2.04/0.68  % (22198)Time elapsed: 0.063 s
% 2.04/0.68  % (22198)------------------------------
% 2.04/0.68  % (22198)------------------------------
% 2.04/0.68  % (22153)Refutation not found, incomplete strategy% (22153)------------------------------
% 2.04/0.68  % (22153)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.04/0.68  % (22153)Termination reason: Refutation not found, incomplete strategy
% 2.04/0.68  
% 2.04/0.68  % (22153)Memory used [KB]: 6140
% 2.04/0.68  % (22153)Time elapsed: 0.211 s
% 2.04/0.68  % (22153)------------------------------
% 2.04/0.68  % (22153)------------------------------
% 2.04/0.68  % (22193)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.04/0.68  % (22193)Refutation not found, incomplete strategy% (22193)------------------------------
% 2.04/0.68  % (22193)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.04/0.68  % (22193)Termination reason: Refutation not found, incomplete strategy
% 2.04/0.68  
% 2.04/0.68  % (22193)Memory used [KB]: 10618
% 2.04/0.68  % (22193)Time elapsed: 0.110 s
% 2.04/0.68  % (22193)------------------------------
% 2.04/0.68  % (22193)------------------------------
% 2.04/0.69  % (22192)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.04/0.69  % (22200)Refutation not found, incomplete strategy% (22200)------------------------------
% 2.04/0.69  % (22200)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.04/0.69  % (22200)Termination reason: Refutation not found, incomplete strategy
% 2.04/0.69  
% 2.04/0.69  % (22200)Memory used [KB]: 10746
% 2.04/0.69  % (22200)Time elapsed: 0.073 s
% 2.04/0.69  % (22200)------------------------------
% 2.04/0.69  % (22200)------------------------------
% 2.04/0.69  % (22192)Refutation not found, incomplete strategy% (22192)------------------------------
% 2.04/0.69  % (22192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.04/0.69  % (22192)Termination reason: Refutation not found, incomplete strategy
% 2.04/0.69  
% 2.04/0.69  % (22192)Memory used [KB]: 10618
% 2.04/0.69  % (22192)Time elapsed: 0.111 s
% 2.04/0.69  % (22192)------------------------------
% 2.04/0.69  % (22192)------------------------------
% 2.04/0.69  % (22195)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.04/0.69  % (22138)Refutation not found, incomplete strategy% (22138)------------------------------
% 2.04/0.69  % (22138)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.04/0.69  % (22138)Termination reason: Refutation not found, incomplete strategy
% 2.04/0.69  
% 2.04/0.69  % (22138)Memory used [KB]: 1663
% 2.04/0.69  % (22138)Time elapsed: 0.284 s
% 2.04/0.69  % (22138)------------------------------
% 2.04/0.69  % (22138)------------------------------
% 2.04/0.70  % (22146)Refutation not found, incomplete strategy% (22146)------------------------------
% 2.04/0.70  % (22146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.04/0.70  % (22146)Termination reason: Refutation not found, incomplete strategy
% 2.04/0.70  
% 2.04/0.70  % (22146)Memory used [KB]: 6268
% 2.04/0.70  % (22146)Time elapsed: 0.292 s
% 2.04/0.70  % (22146)------------------------------
% 2.04/0.70  % (22146)------------------------------
% 2.04/0.70  % (22191)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.04/0.70  % (22191)Refutation not found, incomplete strategy% (22191)------------------------------
% 2.04/0.70  % (22191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.04/0.70  % (22191)Termination reason: Refutation not found, incomplete strategy
% 2.04/0.70  
% 2.04/0.70  % (22191)Memory used [KB]: 6140
% 2.04/0.70  % (22191)Time elapsed: 0.001 s
% 2.04/0.70  % (22191)------------------------------
% 2.04/0.70  % (22191)------------------------------
% 2.04/0.70  % (22197)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.04/0.70  % (22195)Refutation not found, incomplete strategy% (22195)------------------------------
% 2.04/0.70  % (22195)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.52/0.71  % (22140)Refutation not found, incomplete strategy% (22140)------------------------------
% 2.52/0.71  % (22140)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.52/0.71  % (22196)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.52/0.71  % (22140)Termination reason: Refutation not found, incomplete strategy
% 2.52/0.71  
% 2.52/0.71  % (22140)Memory used [KB]: 6140
% 2.52/0.71  % (22140)Time elapsed: 0.279 s
% 2.52/0.71  % (22140)------------------------------
% 2.52/0.71  % (22140)------------------------------
% 2.52/0.71  % (22195)Termination reason: Refutation not found, incomplete strategy
% 2.52/0.71  
% 2.52/0.71  % (22195)Memory used [KB]: 10746
% 2.52/0.71  % (22195)Time elapsed: 0.128 s
% 2.52/0.71  % (22195)------------------------------
% 2.52/0.71  % (22195)------------------------------
% 2.52/0.71  % (22201)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 2.52/0.72  % (22201)Refutation not found, incomplete strategy% (22201)------------------------------
% 2.52/0.72  % (22201)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.52/0.72  % (22201)Termination reason: Refutation not found, incomplete strategy
% 2.52/0.72  
% 2.52/0.72  % (22201)Memory used [KB]: 1663
% 2.52/0.72  % (22201)Time elapsed: 0.120 s
% 2.52/0.72  % (22201)------------------------------
% 2.52/0.72  % (22201)------------------------------
% 2.52/0.72  % (22202)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 2.52/0.72  % (22202)Refutation not found, incomplete strategy% (22202)------------------------------
% 2.52/0.72  % (22202)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.52/0.72  % (22202)Termination reason: Refutation not found, incomplete strategy
% 2.52/0.72  
% 2.52/0.72  % (22202)Memory used [KB]: 10746
% 2.52/0.72  % (22202)Time elapsed: 0.128 s
% 2.52/0.72  % (22202)------------------------------
% 2.52/0.72  % (22202)------------------------------
% 2.52/0.72  % (22199)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 2.52/0.74  % (22203)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 2.52/0.75  % (22194)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.86/0.78  % (22206)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 2.86/0.79  % (22209)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 2.86/0.79  % (22205)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 2.86/0.79  % (22204)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 2.86/0.79  % (22197)Refutation not found, incomplete strategy% (22197)------------------------------
% 2.86/0.79  % (22197)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.86/0.79  % (22197)Termination reason: Refutation not found, incomplete strategy
% 2.86/0.79  
% 2.86/0.79  % (22197)Memory used [KB]: 6140
% 2.86/0.79  % (22197)Time elapsed: 0.215 s
% 2.86/0.79  % (22197)------------------------------
% 2.86/0.79  % (22197)------------------------------
% 2.86/0.81  % (22208)dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 2.86/0.82  % (22207)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 3.31/0.85  % (22203)Refutation not found, incomplete strategy% (22203)------------------------------
% 3.31/0.85  % (22203)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.31/0.85  % (22203)Termination reason: Refutation not found, incomplete strategy
% 3.31/0.85  
% 3.31/0.85  % (22203)Memory used [KB]: 6140
% 3.31/0.85  % (22203)Time elapsed: 0.228 s
% 3.31/0.85  % (22203)------------------------------
% 3.31/0.85  % (22203)------------------------------
% 3.31/0.85  % (22204)Refutation not found, incomplete strategy% (22204)------------------------------
% 3.31/0.85  % (22204)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.31/0.85  % (22204)Termination reason: Refutation not found, incomplete strategy
% 3.31/0.85  
% 3.31/0.85  % (22204)Memory used [KB]: 6140
% 3.31/0.85  % (22204)Time elapsed: 0.021 s
% 3.31/0.85  % (22204)------------------------------
% 3.31/0.85  % (22204)------------------------------
% 3.61/0.92  % (22207)Refutation not found, incomplete strategy% (22207)------------------------------
% 3.61/0.92  % (22207)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.61/0.92  % (22207)Termination reason: Refutation not found, incomplete strategy
% 3.61/0.92  
% 3.61/0.92  % (22207)Memory used [KB]: 6140
% 3.61/0.92  % (22207)Time elapsed: 0.180 s
% 3.61/0.92  % (22207)------------------------------
% 3.61/0.92  % (22207)------------------------------
% 3.85/0.94  % (22144)Time limit reached!
% 3.85/0.94  % (22144)------------------------------
% 3.85/0.94  % (22144)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.85/0.94  % (22144)Termination reason: Time limit
% 3.85/0.94  % (22144)Termination phase: Saturation
% 3.85/0.94  
% 3.85/0.94  % (22144)Memory used [KB]: 11897
% 3.85/0.94  % (22144)Time elapsed: 0.504 s
% 3.85/0.94  % (22144)------------------------------
% 3.85/0.94  % (22144)------------------------------
% 5.63/1.11  % (22206)Time limit reached!
% 5.63/1.11  % (22206)------------------------------
% 5.63/1.11  % (22206)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.63/1.11  % (22206)Termination reason: Time limit
% 5.63/1.11  % (22206)Termination phase: Saturation
% 5.63/1.11  
% 5.63/1.11  % (22206)Memory used [KB]: 7291
% 5.63/1.11  % (22206)Time elapsed: 0.400 s
% 5.63/1.11  % (22206)------------------------------
% 5.63/1.11  % (22206)------------------------------
% 5.63/1.13  % (22209)Time limit reached!
% 5.63/1.13  % (22209)------------------------------
% 5.63/1.13  % (22209)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.63/1.13  % (22209)Termination reason: Time limit
% 5.63/1.13  % (22209)Termination phase: Saturation
% 5.63/1.13  
% 5.63/1.13  % (22209)Memory used [KB]: 7547
% 5.63/1.13  % (22209)Time elapsed: 0.400 s
% 5.63/1.13  % (22209)------------------------------
% 5.63/1.13  % (22209)------------------------------
% 6.37/1.16  % (22145)Time limit reached!
% 6.37/1.16  % (22145)------------------------------
% 6.37/1.16  % (22145)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.37/1.16  % (22145)Termination reason: Time limit
% 6.37/1.16  % (22145)Termination phase: Saturation
% 6.37/1.16  
% 6.37/1.16  % (22145)Memory used [KB]: 2942
% 6.37/1.16  % (22145)Time elapsed: 0.600 s
% 6.37/1.16  % (22145)------------------------------
% 6.37/1.16  % (22145)------------------------------
% 6.37/1.17  % (22208)Time limit reached!
% 6.37/1.17  % (22208)------------------------------
% 6.37/1.17  % (22208)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.37/1.17  % (22208)Termination reason: Time limit
% 6.37/1.17  % (22208)Termination phase: Saturation
% 6.37/1.17  
% 6.37/1.17  % (22208)Memory used [KB]: 5373
% 6.37/1.17  % (22208)Time elapsed: 0.400 s
% 6.37/1.17  % (22208)------------------------------
% 6.37/1.17  % (22208)------------------------------
% 7.03/1.24  % (22205)Time limit reached!
% 7.03/1.24  % (22205)------------------------------
% 7.03/1.24  % (22205)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.03/1.24  % (22205)Termination reason: Time limit
% 7.03/1.24  % (22205)Termination phase: Saturation
% 7.03/1.24  
% 7.03/1.24  % (22205)Memory used [KB]: 8187
% 7.03/1.24  % (22205)Time elapsed: 0.500 s
% 7.03/1.24  % (22205)------------------------------
% 7.03/1.24  % (22205)------------------------------
% 7.99/1.40  % SZS status CounterSatisfiable for theBenchmark
% 7.99/1.40  % (22143)# SZS output start Saturation.
% 7.99/1.40  cnf(u33,negated_conjecture,
% 7.99/1.40      ~v2_waybel_0(k6_domain_1(u1_struct_0(sK0),sK1),sK0) | ~v1_waybel_0(k6_domain_1(u1_struct_0(sK0),sK1),sK0)).
% 7.99/1.40  
% 7.99/1.40  cnf(u37,axiom,
% 7.99/1.40      v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)).
% 7.99/1.40  
% 7.99/1.40  cnf(u39,axiom,
% 7.99/1.40      r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)).
% 7.99/1.40  
% 7.99/1.40  cnf(u31,negated_conjecture,
% 7.99/1.40      l1_orders_2(sK0)).
% 7.99/1.40  
% 7.99/1.40  cnf(u117,negated_conjecture,
% 7.99/1.40      ~l1_orders_2(sK0) | sK2(X0,X1,k6_domain_1(u1_struct_0(sK0),sK1)) = X1 | sK2(X0,X1,k6_domain_1(u1_struct_0(sK0),sK1)) = X0 | k2_tarski(X0,X1) = k6_domain_1(u1_struct_0(sK0),sK1) | ~v3_orders_2(sK0) | k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)).
% 7.99/1.40  
% 7.99/1.40  cnf(u30,negated_conjecture,
% 7.99/1.40      v3_orders_2(sK0)).
% 7.99/1.40  
% 7.99/1.40  cnf(u119,negated_conjecture,
% 7.99/1.40      ~v3_orders_2(sK0) | sK2(X0,X1,k6_domain_1(u1_struct_0(sK0),sK1)) = X0 | k2_tarski(X0,X1) = k6_domain_1(u1_struct_0(sK0),sK1) | sK2(X0,X1,k6_domain_1(u1_struct_0(sK0),sK1)) = X1 | k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)).
% 7.99/1.40  
% 7.99/1.40  cnf(u60,axiom,
% 7.99/1.40      v2_struct_0(X1) | ~l1_orders_2(X1) | ~v3_orders_2(X1) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~r2_hidden(X2,k6_domain_1(u1_struct_0(X1),X0)) | ~v1_xboole_0(u1_struct_0(X1))).
% 7.99/1.40  
% 7.99/1.40  cnf(u66,axiom,
% 7.99/1.40      v2_struct_0(X6) | k2_tarski(X4,X5) = k6_domain_1(u1_struct_0(X6),X7) | sK2(X4,X5,k6_domain_1(u1_struct_0(X6),X7)) = X5 | ~v1_xboole_0(u1_struct_0(X6)) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~l1_orders_2(X6) | ~v3_orders_2(X6) | sK2(X4,X5,k6_domain_1(u1_struct_0(X6),X7)) = X4).
% 7.99/1.40  
% 7.99/1.40  cnf(u29,negated_conjecture,
% 7.99/1.40      ~v2_struct_0(sK0)).
% 7.99/1.40  
% 7.99/1.40  cnf(u47,axiom,
% 7.99/1.40      v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1)).
% 7.99/1.40  
% 7.99/1.40  cnf(u67,negated_conjecture,
% 7.99/1.40      ~v1_xboole_0(u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | sK2(X0,X1,k6_domain_1(u1_struct_0(sK0),sK1)) = X1 | sK2(X0,X1,k6_domain_1(u1_struct_0(sK0),sK1)) = X0 | k2_tarski(X0,X1) = k6_domain_1(u1_struct_0(sK0),sK1)).
% 7.99/1.40  
% 7.99/1.40  cnf(u38,axiom,
% 7.99/1.40      m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)).
% 7.99/1.40  
% 7.99/1.40  cnf(u34,axiom,
% 7.99/1.40      m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)).
% 7.99/1.40  
% 7.99/1.40  cnf(u32,negated_conjecture,
% 7.99/1.40      m1_subset_1(sK1,u1_struct_0(sK0))).
% 7.99/1.40  
% 7.99/1.40  cnf(u64,negated_conjecture,
% 7.99/1.40      ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v3_orders_2(sK0) | ~l1_orders_2(sK0) | ~v1_xboole_0(u1_struct_0(sK0)) | sK2(X1,X2,k6_domain_1(u1_struct_0(sK0),X0)) = X2 | sK2(X1,X2,k6_domain_1(u1_struct_0(sK0),X0)) = X1 | k2_tarski(X1,X2) = k6_domain_1(u1_struct_0(sK0),X0)).
% 7.99/1.40  
% 7.99/1.40  cnf(u116,negated_conjecture,
% 7.99/1.40      ~m1_subset_1(X2,u1_struct_0(sK0)) | ~v3_orders_2(sK0) | sK2(X0,X1,k6_domain_1(u1_struct_0(sK0),sK1)) = X1 | sK2(X0,X1,k6_domain_1(u1_struct_0(sK0),sK1)) = X0 | k2_tarski(X0,X1) = k6_domain_1(u1_struct_0(sK0),sK1) | ~l1_orders_2(sK0) | k2_tarski(X2,X2) = k6_domain_1(u1_struct_0(sK0),X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u55,axiom,
% 7.99/1.40      ~m1_subset_1(k2_tarski(X1,X0),k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u36,axiom,
% 7.99/1.40      ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | ~v1_xboole_0(X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u61,axiom,
% 7.99/1.40      ~m1_subset_1(X2,k1_zfmisc_1(X3)) | sK2(X0,X1,X2) = X0 | k2_tarski(X0,X1) = X2 | sK2(X0,X1,X2) = X1 | ~v1_xboole_0(X3)).
% 7.99/1.40  
% 7.99/1.40  cnf(u43,axiom,
% 7.99/1.40      r2_hidden(sK2(X0,X1,X2),X2) | sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | k2_tarski(X0,X1) = X2).
% 7.99/1.40  
% 7.99/1.40  cnf(u51,axiom,
% 7.99/1.40      r2_hidden(X4,k2_tarski(X4,X1))).
% 7.99/1.40  
% 7.99/1.40  cnf(u49,axiom,
% 7.99/1.40      r2_hidden(X4,k2_tarski(X0,X4))).
% 7.99/1.40  
% 7.99/1.40  cnf(u145,negated_conjecture,
% 7.99/1.40      ~r2_hidden(X4,k6_domain_1(u1_struct_0(sK0),sK1)) | k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(X4,X4) | k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)).
% 7.99/1.40  
% 7.99/1.40  cnf(u133,negated_conjecture,
% 7.99/1.40      ~r2_hidden(X5,k6_domain_1(u1_struct_0(sK0),sK1)) | k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(X4,X5) | sK2(X4,X5,k6_domain_1(u1_struct_0(sK0),sK1)) = X4 | k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)).
% 7.99/1.40  
% 7.99/1.40  cnf(u137,negated_conjecture,
% 7.99/1.40      ~r2_hidden(X2,k6_domain_1(u1_struct_0(sK0),sK1)) | k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(X2,X3) | sK2(X2,X3,k6_domain_1(u1_struct_0(sK0),sK1)) = X3 | k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)).
% 7.99/1.40  
% 7.99/1.40  cnf(u63,negated_conjecture,
% 7.99/1.40      ~r2_hidden(X1,k6_domain_1(u1_struct_0(sK0),X0)) | ~v3_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v1_xboole_0(u1_struct_0(sK0))).
% 7.99/1.40  
% 7.99/1.40  cnf(u1571,axiom,
% 7.99/1.40      ~r2_hidden(X58,k2_tarski(X58,X58)) | k2_tarski(X58,X58) = k2_tarski(X57,X58) | sK2(X57,X58,k2_tarski(X58,X58)) = X57).
% 7.99/1.40  
% 7.99/1.40  cnf(u1698,axiom,
% 7.99/1.40      ~r2_hidden(X58,k2_tarski(X58,X58)) | k2_tarski(X58,X58) = k2_tarski(X58,X59) | sK2(X58,X59,k2_tarski(X58,X58)) = X59).
% 7.99/1.40  
% 7.99/1.40  cnf(u234,axiom,
% 7.99/1.40      ~r2_hidden(X12,k2_tarski(X12,X13)) | k2_tarski(X12,X12) = k2_tarski(X12,X13) | sK2(X12,X12,k2_tarski(X12,X13)) = X13).
% 7.99/1.40  
% 7.99/1.40  cnf(u826,axiom,
% 7.99/1.40      ~r2_hidden(X38,k2_tarski(X38,X37)) | k2_tarski(X38,X37) = k2_tarski(X37,X38)).
% 7.99/1.40  
% 7.99/1.40  cnf(u385,axiom,
% 7.99/1.40      ~r2_hidden(X19,k2_tarski(X19,X20)) | k2_tarski(X19,X20) = k2_tarski(X18,X19) | sK2(X18,X19,k2_tarski(X19,X20)) = X18 | sK2(X18,X19,k2_tarski(X19,X20)) = X20).
% 7.99/1.40  
% 7.99/1.40  cnf(u541,axiom,
% 7.99/1.40      ~r2_hidden(X27,k2_tarski(X27,X29)) | k2_tarski(X27,X29) = k2_tarski(X27,X28) | sK2(X27,X28,k2_tarski(X27,X29)) = X28 | sK2(X27,X28,k2_tarski(X27,X29)) = X29).
% 7.99/1.40  
% 7.99/1.40  cnf(u2468,axiom,
% 7.99/1.40      ~r2_hidden(X264,k2_tarski(X263,X263)) | k2_tarski(X263,X263) = k2_tarski(sK2(X261,X262,k2_tarski(X263,X263)),X264) | sK2(sK2(X261,X262,k2_tarski(X263,X263)),X264,k2_tarski(X263,X263)) = X263 | sK2(X261,X262,k2_tarski(X263,X263)) = X262 | sK2(X261,X262,k2_tarski(X263,X263)) = X261 | k2_tarski(X263,X263) = k2_tarski(X261,X262)).
% 7.99/1.40  
% 7.99/1.40  cnf(u2460,axiom,
% 7.99/1.40      ~r2_hidden(X232,k2_tarski(X231,X231)) | k2_tarski(X231,X231) = k2_tarski(X232,sK2(X229,X230,k2_tarski(X231,X231))) | sK2(X232,sK2(X229,X230,k2_tarski(X231,X231)),k2_tarski(X231,X231)) = X231 | sK2(X229,X230,k2_tarski(X231,X231)) = X230 | sK2(X229,X230,k2_tarski(X231,X231)) = X229 | k2_tarski(X231,X231) = k2_tarski(X229,X230)).
% 7.99/1.40  
% 7.99/1.40  cnf(u2405,axiom,
% 7.99/1.40      ~r2_hidden(X9,k2_tarski(X8,X8)) | sK2(X6,X7,k2_tarski(X8,X8)) = X9 | X8 = X9 | sK2(X6,X7,k2_tarski(X8,X8)) = X7 | sK2(X6,X7,k2_tarski(X8,X8)) = X6 | k2_tarski(X6,X7) = k2_tarski(X8,X8)).
% 7.99/1.40  
% 7.99/1.40  cnf(u1750,axiom,
% 7.99/1.40      ~r2_hidden(X65,k2_tarski(X64,X64)) | k2_tarski(X64,X65) = k2_tarski(X64,X64)).
% 7.99/1.40  
% 7.99/1.40  cnf(u1625,axiom,
% 7.99/1.40      ~r2_hidden(X59,k2_tarski(X60,X60)) | k2_tarski(X60,X60) = k2_tarski(X59,X60)).
% 7.99/1.40  
% 7.99/1.40  cnf(u764,axiom,
% 7.99/1.40      ~r2_hidden(X43,k2_tarski(X44,X44)) | k2_tarski(X42,X43) = k2_tarski(X44,X44) | sK2(X42,X43,k2_tarski(X44,X44)) = X42 | sK2(X42,X43,k2_tarski(X44,X44)) = X44).
% 7.99/1.40  
% 7.99/1.40  cnf(u762,axiom,
% 7.99/1.40      ~r2_hidden(X39,k2_tarski(X41,X41)) | k2_tarski(X41,X41) = k2_tarski(X39,X40) | sK2(X39,X40,k2_tarski(X41,X41)) = X40 | sK2(X39,X40,k2_tarski(X41,X41)) = X41).
% 7.99/1.40  
% 7.99/1.40  cnf(u664,axiom,
% 7.99/1.40      ~r2_hidden(X24,k2_tarski(X25,X25)) | k2_tarski(X24,X24) = k2_tarski(X25,X25) | sK2(X24,X24,k2_tarski(X25,X25)) = X25).
% 7.99/1.40  
% 7.99/1.40  cnf(u296,axiom,
% 7.99/1.40      ~r2_hidden(X12,k2_tarski(X13,X12)) | k2_tarski(X12,X12) = k2_tarski(X13,X12) | sK2(X12,X12,k2_tarski(X13,X12)) = X13).
% 7.99/1.40  
% 7.99/1.40  cnf(u802,axiom,
% 7.99/1.40      ~r2_hidden(X31,k2_tarski(X32,X31)) | k2_tarski(X32,X31) = k2_tarski(X31,X32) | sK2(X31,X32,k2_tarski(X32,X31)) = X32).
% 7.99/1.40  
% 7.99/1.40  cnf(u454,axiom,
% 7.99/1.40      ~r2_hidden(X25,k2_tarski(X26,X25)) | k2_tarski(X26,X25) = k2_tarski(X24,X25) | sK2(X24,X25,k2_tarski(X26,X25)) = X24 | sK2(X24,X25,k2_tarski(X26,X25)) = X26).
% 7.99/1.40  
% 7.99/1.40  cnf(u629,axiom,
% 7.99/1.40      ~r2_hidden(X33,k2_tarski(X35,X33)) | k2_tarski(X33,X34) = k2_tarski(X35,X33) | sK2(X33,X34,k2_tarski(X35,X33)) = X34 | sK2(X33,X34,k2_tarski(X35,X33)) = X35).
% 7.99/1.40  
% 7.99/1.40  cnf(u2223,axiom,
% 7.99/1.40      ~r2_hidden(X2,k2_tarski(X1,X0)) | k2_tarski(X1,X0) = k2_tarski(X0,X2) | sK2(X0,X2,k2_tarski(X1,X0)) = X1).
% 7.99/1.40  
% 7.99/1.40  cnf(u2208,axiom,
% 7.99/1.40      ~r2_hidden(X96,k2_tarski(X95,X97)) | k2_tarski(X95,X96) = k2_tarski(X95,X97) | sK2(X95,X96,k2_tarski(X95,X97)) = X97).
% 7.99/1.40  
% 7.99/1.40  cnf(u1929,axiom,
% 7.99/1.40      ~r2_hidden(X2,k2_tarski(X1,X0)) | k2_tarski(X1,X0) = k2_tarski(X2,X0) | sK2(X2,X0,k2_tarski(X1,X0)) = X1).
% 7.99/1.40  
% 7.99/1.40  cnf(u1907,axiom,
% 7.99/1.40      ~r2_hidden(X87,k2_tarski(X88,X89)) | k2_tarski(X87,X88) = k2_tarski(X88,X89) | sK2(X87,X88,k2_tarski(X88,X89)) = X89).
% 7.99/1.40  
% 7.99/1.40  cnf(u1442,axiom,
% 7.99/1.40      ~r2_hidden(X79,k2_tarski(X82,X83)) | k2_tarski(X82,X83) = k2_tarski(X79,sK2(X80,X81,k2_tarski(X82,X83))) | sK2(X79,sK2(X80,X81,k2_tarski(X82,X83)),k2_tarski(X82,X83)) = X82 | sK2(X79,sK2(X80,X81,k2_tarski(X82,X83)),k2_tarski(X82,X83)) = X83 | sK2(X80,X81,k2_tarski(X82,X83)) = X81 | sK2(X80,X81,k2_tarski(X82,X83)) = X80 | k2_tarski(X82,X83) = k2_tarski(X80,X81)).
% 7.99/1.40  
% 7.99/1.40  cnf(u1040,axiom,
% 7.99/1.40      ~r2_hidden(X70,k2_tarski(X68,X69)) | k2_tarski(X68,X69) = k2_tarski(sK2(X66,X67,k2_tarski(X68,X69)),X70) | sK2(sK2(X66,X67,k2_tarski(X68,X69)),X70,k2_tarski(X68,X69)) = X68 | sK2(sK2(X66,X67,k2_tarski(X68,X69)),X70,k2_tarski(X68,X69)) = X69 | sK2(X66,X67,k2_tarski(X68,X69)) = X67 | sK2(X66,X67,k2_tarski(X68,X69)) = X66 | k2_tarski(X68,X69) = k2_tarski(X66,X67)).
% 7.99/1.40  
% 7.99/1.40  cnf(u634,axiom,
% 7.99/1.40      ~r2_hidden(X37,k2_tarski(X38,X36)) | k2_tarski(X38,X36) = k2_tarski(X36,X37) | sK2(X36,X37,k2_tarski(X38,X36)) = X38 | sK2(X36,X37,k2_tarski(X38,X36)) = X36).
% 7.99/1.40  
% 7.99/1.40  cnf(u543,axiom,
% 7.99/1.40      ~r2_hidden(X31,k2_tarski(X30,X32)) | k2_tarski(X30,X31) = k2_tarski(X30,X32) | sK2(X30,X31,k2_tarski(X30,X32)) = X30 | sK2(X30,X31,k2_tarski(X30,X32)) = X32).
% 7.99/1.40  
% 7.99/1.40  cnf(u461,axiom,
% 7.99/1.40      ~r2_hidden(X21,k2_tarski(X23,X22)) | k2_tarski(X23,X22) = k2_tarski(X21,X22) | sK2(X21,X22,k2_tarski(X23,X22)) = X23 | sK2(X21,X22,k2_tarski(X23,X22)) = X22).
% 7.99/1.40  
% 7.99/1.40  cnf(u389,axiom,
% 7.99/1.40      ~r2_hidden(X15,k2_tarski(X16,X17)) | k2_tarski(X16,X17) = k2_tarski(X15,X16) | sK2(X15,X16,k2_tarski(X16,X17)) = X16 | sK2(X15,X16,k2_tarski(X16,X17)) = X17).
% 7.99/1.40  
% 7.99/1.40  cnf(u201,axiom,
% 7.99/1.40      ~r2_hidden(X18,k2_tarski(X19,X20)) | k2_tarski(X19,X20) = k2_tarski(X18,X18) | sK2(X18,X18,k2_tarski(X19,X20)) = X19 | sK2(X18,X18,k2_tarski(X19,X20)) = X20).
% 7.99/1.40  
% 7.99/1.40  cnf(u114,axiom,
% 7.99/1.40      ~r2_hidden(X9,k2_tarski(X10,X11)) | k2_tarski(X10,X11) = k2_tarski(X8,X9) | sK2(X8,X9,k2_tarski(X10,X11)) = X8 | sK2(X8,X9,k2_tarski(X10,X11)) = X10 | sK2(X8,X9,k2_tarski(X10,X11)) = X11).
% 7.99/1.40  
% 7.99/1.40  cnf(u112,axiom,
% 7.99/1.40      ~r2_hidden(X4,k2_tarski(X6,X7)) | k2_tarski(X6,X7) = k2_tarski(X4,X5) | sK2(X4,X5,k2_tarski(X6,X7)) = X5 | sK2(X4,X5,k2_tarski(X6,X7)) = X6 | sK2(X4,X5,k2_tarski(X6,X7)) = X7).
% 7.99/1.40  
% 7.99/1.40  cnf(u52,axiom,
% 7.99/1.40      ~r2_hidden(X4,k2_tarski(X0,X1)) | X0 = X4 | X1 = X4).
% 7.99/1.40  
% 7.99/1.40  cnf(u36,axiom,
% 7.99/1.40      ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | ~v1_xboole_0(X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u1756,axiom,
% 7.99/1.40      k2_tarski(X2,X2) = k2_tarski(X2,sK2(X3,X4,k2_tarski(X2,X2))) | sK2(X3,X4,k2_tarski(X2,X2)) = X4 | sK2(X3,X4,k2_tarski(X2,X2)) = X3 | k2_tarski(X3,X4) = k2_tarski(X2,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u1630,axiom,
% 7.99/1.40      k2_tarski(X2,X2) = k2_tarski(sK2(X3,X4,k2_tarski(X2,X2)),X2) | sK2(X3,X4,k2_tarski(X2,X2)) = X4 | sK2(X3,X4,k2_tarski(X2,X2)) = X3 | k2_tarski(X3,X4) = k2_tarski(X2,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u831,axiom,
% 7.99/1.40      k2_tarski(X1,X2) = k2_tarski(X2,X1)).
% 7.99/1.40  
% 7.99/1.40  cnf(u2214,axiom,
% 7.99/1.40      sK2(sK2(X5,X6,k2_tarski(X4,X4)),X7,k2_tarski(X4,X4)) = X7 | sK2(sK2(X5,X6,k2_tarski(X4,X4)),X7,k2_tarski(X4,X4)) = X4 | k2_tarski(X4,X4) = k2_tarski(sK2(X5,X6,k2_tarski(X4,X4)),X7) | sK2(X5,X6,k2_tarski(X4,X4)) = X6 | sK2(X5,X6,k2_tarski(X4,X4)) = X5 | k2_tarski(X4,X4) = k2_tarski(X5,X6)).
% 7.99/1.40  
% 7.99/1.40  cnf(u2214,axiom,
% 7.99/1.40      sK2(sK2(X5,X6,k2_tarski(X4,X4)),X7,k2_tarski(X4,X4)) = X7 | sK2(sK2(X5,X6,k2_tarski(X4,X4)),X7,k2_tarski(X4,X4)) = X4 | k2_tarski(X4,X4) = k2_tarski(sK2(X5,X6,k2_tarski(X4,X4)),X7) | sK2(X5,X6,k2_tarski(X4,X4)) = X6 | sK2(X5,X6,k2_tarski(X4,X4)) = X5 | k2_tarski(X4,X4) = k2_tarski(X5,X6)).
% 7.99/1.40  
% 7.99/1.40  cnf(u5036,axiom,
% 7.99/1.40      sK2(sK2(X0,X1,k2_tarski(X2,X2)),sK2(X3,X4,k2_tarski(X2,X2)),k2_tarski(X2,X2)) = X2 | k2_tarski(X2,X2) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X2)),sK2(X3,X4,k2_tarski(X2,X2))) | sK2(X0,X1,k2_tarski(X2,X2)) = X1 | sK2(X0,X1,k2_tarski(X2,X2)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X2) | sK2(X3,X4,k2_tarski(X2,X2)) = X4 | sK2(X3,X4,k2_tarski(X2,X2)) = X3 | k2_tarski(X3,X4) = k2_tarski(X2,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u2615,axiom,
% 7.99/1.40      sK2(sK2(X16,X17,k2_tarski(X15,X15)),sK2(X13,X14,k2_tarski(X15,X15)),k2_tarski(X15,X15)) = X15 | k2_tarski(X15,X15) = k2_tarski(sK2(X13,X14,k2_tarski(X15,X15)),sK2(X16,X17,k2_tarski(X15,X15))) | sK2(X16,X17,k2_tarski(X15,X15)) = X17 | sK2(X16,X17,k2_tarski(X15,X15)) = X16 | k2_tarski(X16,X17) = k2_tarski(X15,X15) | sK2(X13,X14,k2_tarski(X15,X15)) = X14 | sK2(X13,X14,k2_tarski(X15,X15)) = X13 | k2_tarski(X13,X14) = k2_tarski(X15,X15)).
% 7.99/1.40  
% 7.99/1.40  cnf(u671,axiom,
% 7.99/1.40      sK2(sK2(X2,X3,k2_tarski(X4,X4)),sK2(X2,X3,k2_tarski(X4,X4)),k2_tarski(X4,X4)) = X4 | k2_tarski(X4,X4) = k2_tarski(sK2(X2,X3,k2_tarski(X4,X4)),sK2(X2,X3,k2_tarski(X4,X4))) | sK2(X2,X3,k2_tarski(X4,X4)) = X3 | sK2(X2,X3,k2_tarski(X4,X4)) = X2 | k2_tarski(X2,X3) = k2_tarski(X4,X4)).
% 7.99/1.40  
% 7.99/1.40  cnf(u3186,axiom,
% 7.99/1.40      sK2(sK2(X10,X11,k2_tarski(X8,X9)),sK2(X12,X13,k2_tarski(X8,X9)),k2_tarski(X8,X9)) = X8 | sK2(sK2(X10,X11,k2_tarski(X8,X9)),sK2(X12,X13,k2_tarski(X8,X9)),k2_tarski(X8,X9)) = X9 | k2_tarski(X8,X9) = k2_tarski(sK2(X10,X11,k2_tarski(X8,X9)),sK2(X12,X13,k2_tarski(X8,X9))) | sK2(X10,X11,k2_tarski(X8,X9)) = X11 | sK2(X10,X11,k2_tarski(X8,X9)) = X10 | k2_tarski(X10,X11) = k2_tarski(X8,X9) | sK2(X12,X13,k2_tarski(X8,X9)) = X13 | sK2(X12,X13,k2_tarski(X8,X9)) = X12 | k2_tarski(X8,X9) = k2_tarski(X12,X13)).
% 7.99/1.40  
% 7.99/1.40  cnf(u3186,axiom,
% 7.99/1.40      sK2(sK2(X10,X11,k2_tarski(X8,X9)),sK2(X12,X13,k2_tarski(X8,X9)),k2_tarski(X8,X9)) = X8 | sK2(sK2(X10,X11,k2_tarski(X8,X9)),sK2(X12,X13,k2_tarski(X8,X9)),k2_tarski(X8,X9)) = X9 | k2_tarski(X8,X9) = k2_tarski(sK2(X10,X11,k2_tarski(X8,X9)),sK2(X12,X13,k2_tarski(X8,X9))) | sK2(X10,X11,k2_tarski(X8,X9)) = X11 | sK2(X10,X11,k2_tarski(X8,X9)) = X10 | k2_tarski(X10,X11) = k2_tarski(X8,X9) | sK2(X12,X13,k2_tarski(X8,X9)) = X13 | sK2(X12,X13,k2_tarski(X8,X9)) = X12 | k2_tarski(X8,X9) = k2_tarski(X12,X13)).
% 7.99/1.40  
% 7.99/1.40  cnf(u1770,axiom,
% 7.99/1.40      sK2(sK2(X6,X7,k2_tarski(X4,X5)),sK2(X6,X7,k2_tarski(X4,X5)),k2_tarski(X4,X5)) = X4 | sK2(sK2(X6,X7,k2_tarski(X4,X5)),sK2(X6,X7,k2_tarski(X4,X5)),k2_tarski(X4,X5)) = X5 | k2_tarski(X4,X5) = k2_tarski(sK2(X6,X7,k2_tarski(X4,X5)),sK2(X6,X7,k2_tarski(X4,X5))) | sK2(X6,X7,k2_tarski(X4,X5)) = X7 | sK2(X6,X7,k2_tarski(X4,X5)) = X6 | k2_tarski(X6,X7) = k2_tarski(X4,X5)).
% 7.99/1.40  
% 7.99/1.40  cnf(u1770,axiom,
% 7.99/1.40      sK2(sK2(X6,X7,k2_tarski(X4,X5)),sK2(X6,X7,k2_tarski(X4,X5)),k2_tarski(X4,X5)) = X4 | sK2(sK2(X6,X7,k2_tarski(X4,X5)),sK2(X6,X7,k2_tarski(X4,X5)),k2_tarski(X4,X5)) = X5 | k2_tarski(X4,X5) = k2_tarski(sK2(X6,X7,k2_tarski(X4,X5)),sK2(X6,X7,k2_tarski(X4,X5))) | sK2(X6,X7,k2_tarski(X4,X5)) = X7 | sK2(X6,X7,k2_tarski(X4,X5)) = X6 | k2_tarski(X6,X7) = k2_tarski(X4,X5)).
% 7.99/1.40  
% 7.99/1.40  cnf(u245,axiom,
% 7.99/1.40      sK2(sK2(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X10 | sK2(sK2(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X6 | sK2(sK2(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X7 | k2_tarski(X6,X7) = k2_tarski(sK2(X8,X9,k2_tarski(X6,X7)),X10) | sK2(X8,X9,k2_tarski(X6,X7)) = X9 | sK2(X8,X9,k2_tarski(X6,X7)) = X8 | k2_tarski(X6,X7) = k2_tarski(X8,X9)).
% 7.99/1.40  
% 7.99/1.40  cnf(u245,axiom,
% 7.99/1.40      sK2(sK2(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X10 | sK2(sK2(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X6 | sK2(sK2(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X7 | k2_tarski(X6,X7) = k2_tarski(sK2(X8,X9,k2_tarski(X6,X7)),X10) | sK2(X8,X9,k2_tarski(X6,X7)) = X9 | sK2(X8,X9,k2_tarski(X6,X7)) = X8 | k2_tarski(X6,X7) = k2_tarski(X8,X9)).
% 7.99/1.40  
% 7.99/1.40  cnf(u245,axiom,
% 7.99/1.40      sK2(sK2(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X10 | sK2(sK2(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X6 | sK2(sK2(X8,X9,k2_tarski(X6,X7)),X10,k2_tarski(X6,X7)) = X7 | k2_tarski(X6,X7) = k2_tarski(sK2(X8,X9,k2_tarski(X6,X7)),X10) | sK2(X8,X9,k2_tarski(X6,X7)) = X9 | sK2(X8,X9,k2_tarski(X6,X7)) = X8 | k2_tarski(X6,X7) = k2_tarski(X8,X9)).
% 7.99/1.40  
% 7.99/1.40  cnf(u2612,axiom,
% 7.99/1.40      sK2(sK2(X2,X3,k2_tarski(X1,X0)),X0,k2_tarski(X1,X0)) = X1 | k2_tarski(X1,X0) = k2_tarski(X0,sK2(X2,X3,k2_tarski(X1,X0))) | sK2(X2,X3,k2_tarski(X1,X0)) = X3 | sK2(X2,X3,k2_tarski(X1,X0)) = X2 | k2_tarski(X1,X0) = k2_tarski(X2,X3)).
% 7.99/1.40  
% 7.99/1.40  cnf(u1931,axiom,
% 7.99/1.40      sK2(sK2(X4,X5,k2_tarski(X6,X7)),X6,k2_tarski(X6,X7)) = X7 | k2_tarski(X6,X7) = k2_tarski(X6,sK2(X4,X5,k2_tarski(X6,X7))) | sK2(X4,X5,k2_tarski(X6,X7)) = X5 | sK2(X4,X5,k2_tarski(X6,X7)) = X4 | k2_tarski(X6,X7) = k2_tarski(X4,X5)).
% 7.99/1.40  
% 7.99/1.40  cnf(u2222,axiom,
% 7.99/1.40      sK2(X4,sK2(X5,X6,k2_tarski(X4,X7)),k2_tarski(X4,X7)) = X7 | k2_tarski(X4,X7) = k2_tarski(X4,sK2(X5,X6,k2_tarski(X4,X7))) | sK2(X5,X6,k2_tarski(X4,X7)) = X6 | sK2(X5,X6,k2_tarski(X4,X7)) = X5 | k2_tarski(X5,X6) = k2_tarski(X4,X7)).
% 7.99/1.40  
% 7.99/1.40  cnf(u2219,axiom,
% 7.99/1.40      sK2(X4,sK2(X5,X6,k2_tarski(X7,X7)),k2_tarski(X7,X7)) = X4 | sK2(X4,sK2(X5,X6,k2_tarski(X7,X7)),k2_tarski(X7,X7)) = X7 | k2_tarski(X7,X7) = k2_tarski(X4,sK2(X5,X6,k2_tarski(X7,X7))) | sK2(X5,X6,k2_tarski(X7,X7)) = X6 | sK2(X5,X6,k2_tarski(X7,X7)) = X5 | k2_tarski(X7,X7) = k2_tarski(X5,X6)).
% 7.99/1.40  
% 7.99/1.40  cnf(u2219,axiom,
% 7.99/1.40      sK2(X4,sK2(X5,X6,k2_tarski(X7,X7)),k2_tarski(X7,X7)) = X4 | sK2(X4,sK2(X5,X6,k2_tarski(X7,X7)),k2_tarski(X7,X7)) = X7 | k2_tarski(X7,X7) = k2_tarski(X4,sK2(X5,X6,k2_tarski(X7,X7))) | sK2(X5,X6,k2_tarski(X7,X7)) = X6 | sK2(X5,X6,k2_tarski(X7,X7)) = X5 | k2_tarski(X7,X7) = k2_tarski(X5,X6)).
% 7.99/1.40  
% 7.99/1.40  cnf(u2726,axiom,
% 7.99/1.40      sK2(X0,sK2(X2,X3,k2_tarski(X1,X0)),k2_tarski(X1,X0)) = X1 | k2_tarski(X1,X0) = k2_tarski(X0,sK2(X2,X3,k2_tarski(X1,X0))) | sK2(X2,X3,k2_tarski(X1,X0)) = X3 | sK2(X2,X3,k2_tarski(X1,X0)) = X2 | k2_tarski(X1,X0) = k2_tarski(X2,X3)).
% 7.99/1.40  
% 7.99/1.40  cnf(u267,axiom,
% 7.99/1.40      sK2(X8,sK2(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X8 | sK2(X8,sK2(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X6 | sK2(X8,sK2(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X7 | k2_tarski(X6,X7) = k2_tarski(X8,sK2(X9,X10,k2_tarski(X6,X7))) | sK2(X9,X10,k2_tarski(X6,X7)) = X10 | sK2(X9,X10,k2_tarski(X6,X7)) = X9 | k2_tarski(X6,X7) = k2_tarski(X9,X10)).
% 7.99/1.40  
% 7.99/1.40  cnf(u267,axiom,
% 7.99/1.40      sK2(X8,sK2(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X8 | sK2(X8,sK2(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X6 | sK2(X8,sK2(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X7 | k2_tarski(X6,X7) = k2_tarski(X8,sK2(X9,X10,k2_tarski(X6,X7))) | sK2(X9,X10,k2_tarski(X6,X7)) = X10 | sK2(X9,X10,k2_tarski(X6,X7)) = X9 | k2_tarski(X6,X7) = k2_tarski(X9,X10)).
% 7.99/1.40  
% 7.99/1.40  cnf(u267,axiom,
% 7.99/1.40      sK2(X8,sK2(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X8 | sK2(X8,sK2(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X6 | sK2(X8,sK2(X9,X10,k2_tarski(X6,X7)),k2_tarski(X6,X7)) = X7 | k2_tarski(X6,X7) = k2_tarski(X8,sK2(X9,X10,k2_tarski(X6,X7))) | sK2(X9,X10,k2_tarski(X6,X7)) = X10 | sK2(X9,X10,k2_tarski(X6,X7)) = X9 | k2_tarski(X6,X7) = k2_tarski(X9,X10)).
% 7.99/1.40  
% 7.99/1.40  cnf(u118,axiom,
% 7.99/1.40      sK2(X0,X0,k2_tarski(X1,X2)) = X0 | sK2(X0,X0,k2_tarski(X1,X2)) = X1 | sK2(X0,X0,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X0) = k2_tarski(X1,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u205,axiom,
% 7.99/1.40      sK2(X0,X0,k2_tarski(X0,X1)) = X0 | sK2(X0,X0,k2_tarski(X0,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X0,X0)).
% 7.99/1.40  
% 7.99/1.40  cnf(u242,axiom,
% 7.99/1.40      sK2(X1,X1,k2_tarski(X1,X2)) = X2 | k2_tarski(X1,X1) = k2_tarski(X1,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u545,axiom,
% 7.99/1.40      sK2(X0,X0,k2_tarski(X1,X1)) = X0 | sK2(X0,X0,k2_tarski(X1,X1)) = X1 | k2_tarski(X0,X0) = k2_tarski(X1,X1)).
% 7.99/1.40  
% 7.99/1.40  cnf(u270,axiom,
% 7.99/1.40      sK2(X0,X0,k2_tarski(X1,X0)) = X1 | sK2(X0,X0,k2_tarski(X1,X0)) = X0 | k2_tarski(X0,X0) = k2_tarski(X1,X0)).
% 7.99/1.40  
% 7.99/1.40  cnf(u304,axiom,
% 7.99/1.40      sK2(X0,X0,k2_tarski(X1,X0)) = X1 | k2_tarski(X0,X0) = k2_tarski(X1,X0)).
% 7.99/1.40  
% 7.99/1.40  cnf(u118,axiom,
% 7.99/1.40      sK2(X0,X0,k2_tarski(X1,X2)) = X0 | sK2(X0,X0,k2_tarski(X1,X2)) = X1 | sK2(X0,X0,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X0) = k2_tarski(X1,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u205,axiom,
% 7.99/1.40      sK2(X0,X0,k2_tarski(X0,X1)) = X0 | sK2(X0,X0,k2_tarski(X0,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X0,X0)).
% 7.99/1.40  
% 7.99/1.40  cnf(u545,axiom,
% 7.99/1.40      sK2(X0,X0,k2_tarski(X1,X1)) = X0 | sK2(X0,X0,k2_tarski(X1,X1)) = X1 | k2_tarski(X0,X0) = k2_tarski(X1,X1)).
% 7.99/1.40  
% 7.99/1.40  cnf(u270,axiom,
% 7.99/1.40      sK2(X0,X0,k2_tarski(X1,X0)) = X1 | sK2(X0,X0,k2_tarski(X1,X0)) = X0 | k2_tarski(X0,X0) = k2_tarski(X1,X0)).
% 7.99/1.40  
% 7.99/1.40  cnf(u118,axiom,
% 7.99/1.40      sK2(X0,X0,k2_tarski(X1,X2)) = X0 | sK2(X0,X0,k2_tarski(X1,X2)) = X1 | sK2(X0,X0,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X0) = k2_tarski(X1,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u139,negated_conjecture,
% 7.99/1.40      sK2(X0,X0,k6_domain_1(u1_struct_0(sK0),sK1)) = X0 | k2_tarski(X0,X0) = k6_domain_1(u1_struct_0(sK0),sK1) | k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)).
% 7.99/1.40  
% 7.99/1.40  cnf(u121,negated_conjecture,
% 7.99/1.40      sK2(X0,X1,k6_domain_1(u1_struct_0(sK0),sK1)) = X0 | sK2(X0,X1,k6_domain_1(u1_struct_0(sK0),sK1)) = X1 | k2_tarski(X0,X1) = k6_domain_1(u1_struct_0(sK0),sK1) | k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)).
% 7.99/1.40  
% 7.99/1.40  cnf(u121,negated_conjecture,
% 7.99/1.40      sK2(X0,X1,k6_domain_1(u1_struct_0(sK0),sK1)) = X0 | sK2(X0,X1,k6_domain_1(u1_struct_0(sK0),sK1)) = X1 | k2_tarski(X0,X1) = k6_domain_1(u1_struct_0(sK0),sK1) | k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)).
% 7.99/1.40  
% 7.99/1.40  cnf(u1640,axiom,
% 7.99/1.40      sK2(X0,X1,k2_tarski(X0,X0)) = X1 | sK2(X0,X1,k2_tarski(X0,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X0,X0)).
% 7.99/1.40  
% 7.99/1.40  cnf(u1640,axiom,
% 7.99/1.40      sK2(X0,X1,k2_tarski(X0,X0)) = X1 | sK2(X0,X1,k2_tarski(X0,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X0,X0)).
% 7.99/1.40  
% 7.99/1.40  cnf(u1709,axiom,
% 7.99/1.40      sK2(X0,X1,k2_tarski(X0,X0)) = X1 | k2_tarski(X0,X1) = k2_tarski(X0,X0)).
% 7.99/1.40  
% 7.99/1.40  cnf(u149,axiom,
% 7.99/1.40      sK2(X0,X1,k2_tarski(X0,X2)) = X1 | sK2(X0,X1,k2_tarski(X0,X2)) = X0 | sK2(X0,X1,k2_tarski(X0,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u1933,axiom,
% 7.99/1.40      sK2(X2,X4,k2_tarski(X2,X3)) = X4 | sK2(X2,X4,k2_tarski(X2,X3)) = X3 | k2_tarski(X2,X3) = k2_tarski(X2,X4)).
% 7.99/1.40  
% 7.99/1.40  cnf(u149,axiom,
% 7.99/1.40      sK2(X0,X1,k2_tarski(X0,X2)) = X1 | sK2(X0,X1,k2_tarski(X0,X2)) = X0 | sK2(X0,X1,k2_tarski(X0,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u149,axiom,
% 7.99/1.40      sK2(X0,X1,k2_tarski(X0,X2)) = X1 | sK2(X0,X1,k2_tarski(X0,X2)) = X0 | sK2(X0,X1,k2_tarski(X0,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u1933,axiom,
% 7.99/1.40      sK2(X2,X4,k2_tarski(X2,X3)) = X4 | sK2(X2,X4,k2_tarski(X2,X3)) = X3 | k2_tarski(X2,X3) = k2_tarski(X2,X4)).
% 7.99/1.40  
% 7.99/1.40  cnf(u1515,axiom,
% 7.99/1.40      sK2(X0,X1,k2_tarski(X1,X1)) = X0 | sK2(X0,X1,k2_tarski(X1,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X1,X1)).
% 7.99/1.40  
% 7.99/1.40  cnf(u1515,axiom,
% 7.99/1.40      sK2(X0,X1,k2_tarski(X1,X1)) = X0 | sK2(X0,X1,k2_tarski(X1,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X1,X1)).
% 7.99/1.40  
% 7.99/1.40  cnf(u1583,axiom,
% 7.99/1.40      sK2(X1,X0,k2_tarski(X0,X0)) = X1 | k2_tarski(X0,X0) = k2_tarski(X1,X0)).
% 7.99/1.40  
% 7.99/1.40  cnf(u769,axiom,
% 7.99/1.40      sK2(X0,X1,k2_tarski(X1,X0)) = X1 | sK2(X0,X1,k2_tarski(X1,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X1,X0)).
% 7.99/1.40  
% 7.99/1.40  cnf(u769,axiom,
% 7.99/1.40      sK2(X0,X1,k2_tarski(X1,X0)) = X1 | sK2(X0,X1,k2_tarski(X1,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X1,X0)).
% 7.99/1.40  
% 7.99/1.40  cnf(u808,axiom,
% 7.99/1.40      sK2(X1,X0,k2_tarski(X0,X1)) = X0 | k2_tarski(X0,X1) = k2_tarski(X1,X0)).
% 7.99/1.40  
% 7.99/1.40  cnf(u120,axiom,
% 7.99/1.40      sK2(X0,X1,k2_tarski(X1,X2)) = X0 | sK2(X0,X1,k2_tarski(X1,X2)) = X1 | sK2(X0,X1,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u1774,axiom,
% 7.99/1.40      sK2(X4,X2,k2_tarski(X2,X3)) = X4 | sK2(X4,X2,k2_tarski(X2,X3)) = X3 | k2_tarski(X2,X3) = k2_tarski(X4,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u120,axiom,
% 7.99/1.40      sK2(X0,X1,k2_tarski(X1,X2)) = X0 | sK2(X0,X1,k2_tarski(X1,X2)) = X1 | sK2(X0,X1,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u120,axiom,
% 7.99/1.40      sK2(X0,X1,k2_tarski(X1,X2)) = X0 | sK2(X0,X1,k2_tarski(X1,X2)) = X1 | sK2(X0,X1,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u1774,axiom,
% 7.99/1.40      sK2(X4,X2,k2_tarski(X2,X3)) = X4 | sK2(X4,X2,k2_tarski(X2,X3)) = X3 | k2_tarski(X2,X3) = k2_tarski(X4,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u62,axiom,
% 7.99/1.40      sK2(X4,X5,k2_tarski(X6,X7)) = X5 | sK2(X4,X5,k2_tarski(X6,X7)) = X4 | sK2(X4,X5,k2_tarski(X6,X7)) = X6 | sK2(X4,X5,k2_tarski(X6,X7)) = X7 | k2_tarski(X6,X7) = k2_tarski(X4,X5)).
% 7.99/1.40  
% 7.99/1.40  cnf(u62,axiom,
% 7.99/1.40      sK2(X4,X5,k2_tarski(X6,X7)) = X5 | sK2(X4,X5,k2_tarski(X6,X7)) = X4 | sK2(X4,X5,k2_tarski(X6,X7)) = X6 | sK2(X4,X5,k2_tarski(X6,X7)) = X7 | k2_tarski(X6,X7) = k2_tarski(X4,X5)).
% 7.99/1.40  
% 7.99/1.40  cnf(u62,axiom,
% 7.99/1.40      sK2(X4,X5,k2_tarski(X6,X7)) = X5 | sK2(X4,X5,k2_tarski(X6,X7)) = X4 | sK2(X4,X5,k2_tarski(X6,X7)) = X6 | sK2(X4,X5,k2_tarski(X6,X7)) = X7 | k2_tarski(X6,X7) = k2_tarski(X4,X5)).
% 7.99/1.40  
% 7.99/1.40  cnf(u62,axiom,
% 7.99/1.40      sK2(X4,X5,k2_tarski(X6,X7)) = X5 | sK2(X4,X5,k2_tarski(X6,X7)) = X4 | sK2(X4,X5,k2_tarski(X6,X7)) = X6 | sK2(X4,X5,k2_tarski(X6,X7)) = X7 | k2_tarski(X6,X7) = k2_tarski(X4,X5)).
% 7.99/1.40  
% 7.99/1.40  cnf(u156,axiom,
% 7.99/1.40      sK2(X0,X1,k2_tarski(X2,X2)) = X1 | sK2(X0,X1,k2_tarski(X2,X2)) = X0 | sK2(X0,X1,k2_tarski(X2,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u156,axiom,
% 7.99/1.40      sK2(X0,X1,k2_tarski(X2,X2)) = X1 | sK2(X0,X1,k2_tarski(X2,X2)) = X0 | sK2(X0,X1,k2_tarski(X2,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u156,axiom,
% 7.99/1.40      sK2(X0,X1,k2_tarski(X2,X2)) = X1 | sK2(X0,X1,k2_tarski(X2,X2)) = X0 | sK2(X0,X1,k2_tarski(X2,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u138,axiom,
% 7.99/1.40      sK2(X0,X1,k2_tarski(X2,X1)) = X0 | sK2(X0,X1,k2_tarski(X2,X1)) = X2 | sK2(X0,X1,k2_tarski(X2,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 7.99/1.40  
% 7.99/1.40  cnf(u138,axiom,
% 7.99/1.40      sK2(X0,X1,k2_tarski(X2,X1)) = X0 | sK2(X0,X1,k2_tarski(X2,X1)) = X2 | sK2(X0,X1,k2_tarski(X2,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 7.99/1.40  
% 7.99/1.40  cnf(u1914,axiom,
% 7.99/1.40      sK2(X2,X1,k2_tarski(X0,X1)) = X2 | sK2(X2,X1,k2_tarski(X0,X1)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 7.99/1.40  
% 7.99/1.40  cnf(u138,axiom,
% 7.99/1.40      sK2(X0,X1,k2_tarski(X2,X1)) = X0 | sK2(X0,X1,k2_tarski(X2,X1)) = X2 | sK2(X0,X1,k2_tarski(X2,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 7.99/1.40  
% 7.99/1.40  cnf(u1914,axiom,
% 7.99/1.40      sK2(X2,X1,k2_tarski(X0,X1)) = X2 | sK2(X2,X1,k2_tarski(X0,X1)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 7.99/1.40  
% 7.99/1.40  cnf(u150,axiom,
% 7.99/1.40      sK2(X0,X1,k2_tarski(X2,X0)) = X1 | sK2(X0,X1,k2_tarski(X2,X0)) = X2 | sK2(X0,X1,k2_tarski(X2,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 7.99/1.40  
% 7.99/1.40  cnf(u150,axiom,
% 7.99/1.40      sK2(X0,X1,k2_tarski(X2,X0)) = X1 | sK2(X0,X1,k2_tarski(X2,X0)) = X2 | sK2(X0,X1,k2_tarski(X2,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 7.99/1.40  
% 7.99/1.40  cnf(u2070,axiom,
% 7.99/1.40      sK2(X0,X1,k2_tarski(X2,X0)) = X1 | sK2(X0,X1,k2_tarski(X2,X0)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 7.99/1.40  
% 7.99/1.40  cnf(u150,axiom,
% 7.99/1.40      sK2(X0,X1,k2_tarski(X2,X0)) = X1 | sK2(X0,X1,k2_tarski(X2,X0)) = X2 | sK2(X0,X1,k2_tarski(X2,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 7.99/1.40  
% 7.99/1.40  cnf(u2070,axiom,
% 7.99/1.40      sK2(X0,X1,k2_tarski(X2,X0)) = X1 | sK2(X0,X1,k2_tarski(X2,X0)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 7.99/1.40  
% 7.99/1.40  cnf(u4653,axiom,
% 7.99/1.40      X2 != X3 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X4,X5,k2_tarski(X2,X3)),k2_tarski(X2,X3)) = X2 | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X4,X5,k2_tarski(X2,X3))) | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X3) | sK2(X4,X5,k2_tarski(X2,X3)) = X5 | sK2(X4,X5,k2_tarski(X2,X3)) = X4 | k2_tarski(X4,X5) = k2_tarski(X2,X3)).
% 7.99/1.40  
% 7.99/1.40  cnf(u4652,axiom,
% 7.99/1.40      X2 != X3 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X4,X5,k2_tarski(X2,X3)),k2_tarski(X2,X3)) = X3 | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X4,X5,k2_tarski(X2,X3))) | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X3) | sK2(X4,X5,k2_tarski(X2,X3)) = X5 | sK2(X4,X5,k2_tarski(X2,X3)) = X4 | k2_tarski(X4,X5) = k2_tarski(X2,X3)).
% 7.99/1.40  
% 7.99/1.40  cnf(u4179,axiom,
% 7.99/1.40      X2 != X3 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X0,X1,k2_tarski(X2,X3)),k2_tarski(X2,X3)) = X2 | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X0,X1,k2_tarski(X2,X3))) | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 7.99/1.40  
% 7.99/1.40  cnf(u4178,axiom,
% 7.99/1.40      X2 != X3 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X0,X1,k2_tarski(X2,X3)),k2_tarski(X2,X3)) = X3 | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),sK2(X0,X1,k2_tarski(X2,X3))) | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 7.99/1.40  
% 7.99/1.40  cnf(u3702,axiom,
% 7.99/1.40      X0 != X3 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X3)),k2_tarski(X3,X3)) = X0 | k2_tarski(X3,X3) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X3))) | sK2(X1,X2,k2_tarski(X3,X3)) = X2 | sK2(X1,X2,k2_tarski(X3,X3)) = X1 | k2_tarski(X1,X2) = k2_tarski(X3,X3)).
% 7.99/1.40  
% 7.99/1.40  cnf(u3701,axiom,
% 7.99/1.40      X0 != X3 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X3)),k2_tarski(X3,X3)) = X3 | k2_tarski(X3,X3) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X3))) | sK2(X1,X2,k2_tarski(X3,X3)) = X2 | sK2(X1,X2,k2_tarski(X3,X3)) = X1 | k2_tarski(X1,X2) = k2_tarski(X3,X3)).
% 7.99/1.40  
% 7.99/1.40  cnf(u3421,axiom,
% 7.99/1.40      X2 != X3 | sK2(sK2(X0,X1,k2_tarski(X2,X2)),X3,k2_tarski(X2,X2)) = X3 | k2_tarski(X2,X2) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X2)),X3) | sK2(X0,X1,k2_tarski(X2,X2)) = X1 | sK2(X0,X1,k2_tarski(X2,X2)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u3420,axiom,
% 7.99/1.40      X2 != X3 | sK2(sK2(X0,X1,k2_tarski(X2,X2)),X3,k2_tarski(X2,X2)) = X2 | k2_tarski(X2,X2) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X2)),X3) | sK2(X0,X1,k2_tarski(X2,X2)) = X1 | sK2(X0,X1,k2_tarski(X2,X2)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u2921,axiom,
% 7.99/1.40      X138 != X139 | k2_tarski(X138,X139) = k2_tarski(X139,sK2(X136,X137,k2_tarski(X138,X139))) | ~r2_hidden(X139,k2_tarski(X138,X139)) | sK2(X136,X137,k2_tarski(X138,X139)) = X137 | sK2(X136,X137,k2_tarski(X138,X139)) = X136 | k2_tarski(X138,X139) = k2_tarski(X136,X137)).
% 7.99/1.40  
% 7.99/1.40  cnf(u2667,axiom,
% 7.99/1.40      X127 != X128 | k2_tarski(X127,X128) = k2_tarski(X127,sK2(X125,X126,k2_tarski(X127,X128))) | ~r2_hidden(X127,k2_tarski(X127,X128)) | sK2(X125,X126,k2_tarski(X127,X128)) = X126 | sK2(X125,X126,k2_tarski(X127,X128)) = X125 | k2_tarski(X127,X128) = k2_tarski(X125,X126)).
% 7.99/1.40  
% 7.99/1.40  cnf(u2366,axiom,
% 7.99/1.40      X99 != X100 | k2_tarski(X99,X100) = k2_tarski(X101,X99) | ~r2_hidden(X99,k2_tarski(X101,X99)) | sK2(X99,X100,k2_tarski(X101,X99)) = X101).
% 7.99/1.40  
% 7.99/1.40  cnf(u2351,axiom,
% 7.99/1.40      X99 != X101 | k2_tarski(X99,X100) = k2_tarski(X101,X99) | ~r2_hidden(X99,k2_tarski(X101,X99)) | sK2(X99,X100,k2_tarski(X101,X99)) = X100).
% 7.99/1.40  
% 7.99/1.40  cnf(u2349,axiom,
% 7.99/1.40      X1 != X2 | sK2(X0,X1,k2_tarski(X2,X0)) = X1 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 7.99/1.40  
% 7.99/1.40  cnf(u2348,axiom,
% 7.99/1.40      X1 != X2 | sK2(X0,X1,k2_tarski(X2,X0)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 7.99/1.40  
% 7.99/1.40  cnf(u2209,axiom,
% 7.99/1.40      X92 != X93 | k2_tarski(X92,X93) = k2_tarski(X92,X94) | ~r2_hidden(X92,k2_tarski(X92,X94)) | sK2(X92,X93,k2_tarski(X92,X94)) = X94).
% 7.99/1.40  
% 7.99/1.40  cnf(u2194,axiom,
% 7.99/1.40      X92 != X94 | k2_tarski(X92,X93) = k2_tarski(X92,X94) | ~r2_hidden(X92,k2_tarski(X92,X94)) | sK2(X92,X93,k2_tarski(X92,X94)) = X93).
% 7.99/1.40  
% 7.99/1.40  cnf(u2192,axiom,
% 7.99/1.40      X1 != X2 | sK2(X0,X1,k2_tarski(X0,X2)) = X1 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u2191,axiom,
% 7.99/1.40      X1 != X2 | sK2(X0,X1,k2_tarski(X0,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u2065,axiom,
% 7.99/1.40      X91 != X92 | k2_tarski(X91,X92) = k2_tarski(X93,X92) | ~r2_hidden(X92,k2_tarski(X93,X92)) | sK2(X91,X92,k2_tarski(X93,X92)) = X93).
% 7.99/1.40  
% 7.99/1.40  cnf(u2051,axiom,
% 7.99/1.40      X92 != X93 | k2_tarski(X91,X92) = k2_tarski(X93,X92) | ~r2_hidden(X92,k2_tarski(X93,X92)) | sK2(X91,X92,k2_tarski(X93,X92)) = X91).
% 7.99/1.40  
% 7.99/1.40  cnf(u2050,axiom,
% 7.99/1.40      X0 != X2 | sK2(X0,X1,k2_tarski(X2,X1)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 7.99/1.40  
% 7.99/1.40  cnf(u2049,axiom,
% 7.99/1.40      X0 != X2 | sK2(X0,X1,k2_tarski(X2,X1)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 7.99/1.40  
% 7.99/1.40  cnf(u1905,axiom,
% 7.99/1.40      X90 != X91 | k2_tarski(X90,X91) = k2_tarski(X91,X92) | ~r2_hidden(X91,k2_tarski(X91,X92)) | sK2(X90,X91,k2_tarski(X91,X92)) = X92).
% 7.99/1.40  
% 7.99/1.40  cnf(u1891,axiom,
% 7.99/1.40      X91 != X92 | k2_tarski(X90,X91) = k2_tarski(X91,X92) | ~r2_hidden(X91,k2_tarski(X91,X92)) | sK2(X90,X91,k2_tarski(X91,X92)) = X90).
% 7.99/1.40  
% 7.99/1.40  cnf(u1890,axiom,
% 7.99/1.40      X0 != X2 | sK2(X0,X1,k2_tarski(X1,X2)) = X0 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u1889,axiom,
% 7.99/1.40      X0 != X2 | sK2(X0,X1,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u1751,axiom,
% 7.99/1.40      X62 != X63 | k2_tarski(X62,X62) = k2_tarski(X62,X63) | ~r2_hidden(X62,k2_tarski(X62,X62))).
% 7.99/1.40  
% 7.99/1.40  cnf(u1695,axiom,
% 7.99/1.40      X0 != X1 | sK2(X0,X1,k2_tarski(X0,X0)) = X1 | k2_tarski(X0,X1) = k2_tarski(X0,X0)).
% 7.99/1.40  
% 7.99/1.40  cnf(u1694,axiom,
% 7.99/1.40      X0 != X1 | sK2(X0,X1,k2_tarski(X0,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X0,X0)).
% 7.99/1.40  
% 7.99/1.40  cnf(u1623,axiom,
% 7.99/1.40      X61 != X62 | k2_tarski(X61,X62) = k2_tarski(X62,X62) | ~r2_hidden(X62,k2_tarski(X62,X62))).
% 7.99/1.40  
% 7.99/1.40  cnf(u1569,axiom,
% 7.99/1.40      X0 != X1 | sK2(X0,X1,k2_tarski(X1,X1)) = X0 | k2_tarski(X0,X1) = k2_tarski(X1,X1)).
% 7.99/1.40  
% 7.99/1.40  cnf(u1568,axiom,
% 7.99/1.40      X0 != X1 | sK2(X0,X1,k2_tarski(X1,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X1,X1)).
% 7.99/1.40  
% 7.99/1.40  cnf(u1424,axiom,
% 7.99/1.40      X3 != X4 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X0 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X3 | k2_tarski(X3,X4) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X4))) | sK2(X1,X2,k2_tarski(X3,X4)) = X2 | sK2(X1,X2,k2_tarski(X3,X4)) = X1 | k2_tarski(X3,X4) = k2_tarski(X1,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u1423,axiom,
% 7.99/1.40      X0 != X4 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X0 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X3 | k2_tarski(X3,X4) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X4))) | sK2(X1,X2,k2_tarski(X3,X4)) = X2 | sK2(X1,X2,k2_tarski(X3,X4)) = X1 | k2_tarski(X3,X4) = k2_tarski(X1,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u1422,axiom,
% 7.99/1.40      X3 != X4 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X0 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X4 | k2_tarski(X3,X4) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X4))) | sK2(X1,X2,k2_tarski(X3,X4)) = X2 | sK2(X1,X2,k2_tarski(X3,X4)) = X1 | k2_tarski(X3,X4) = k2_tarski(X1,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u1421,axiom,
% 7.99/1.40      X0 != X3 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X0 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X4 | k2_tarski(X3,X4) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X4))) | sK2(X1,X2,k2_tarski(X3,X4)) = X2 | sK2(X1,X2,k2_tarski(X3,X4)) = X1 | k2_tarski(X3,X4) = k2_tarski(X1,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u1420,axiom,
% 7.99/1.40      X0 != X4 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X3 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X4 | k2_tarski(X3,X4) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X4))) | sK2(X1,X2,k2_tarski(X3,X4)) = X2 | sK2(X1,X2,k2_tarski(X3,X4)) = X1 | k2_tarski(X3,X4) = k2_tarski(X1,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u1419,axiom,
% 7.99/1.40      X0 != X3 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X3 | sK2(X0,sK2(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X4 | k2_tarski(X3,X4) = k2_tarski(X0,sK2(X1,X2,k2_tarski(X3,X4))) | sK2(X1,X2,k2_tarski(X3,X4)) = X2 | sK2(X1,X2,k2_tarski(X3,X4)) = X1 | k2_tarski(X3,X4) = k2_tarski(X1,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u1032,axiom,
% 7.99/1.40      X2 != X3 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X4 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X2 | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),X4) | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 7.99/1.40  
% 7.99/1.40  cnf(u1031,axiom,
% 7.99/1.40      X3 != X4 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X4 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X2 | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),X4) | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 7.99/1.40  
% 7.99/1.40  cnf(u1030,axiom,
% 7.99/1.40      X2 != X3 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X4 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X3 | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),X4) | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 7.99/1.40  
% 7.99/1.40  cnf(u1029,axiom,
% 7.99/1.40      X2 != X4 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X4 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X3 | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),X4) | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 7.99/1.40  
% 7.99/1.40  cnf(u1028,axiom,
% 7.99/1.40      X3 != X4 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X2 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X3 | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),X4) | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 7.99/1.40  
% 7.99/1.40  cnf(u1027,axiom,
% 7.99/1.40      X2 != X4 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X2 | sK2(sK2(X0,X1,k2_tarski(X2,X3)),X4,k2_tarski(X2,X3)) = X3 | k2_tarski(X2,X3) = k2_tarski(sK2(X0,X1,k2_tarski(X2,X3)),X4) | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 7.99/1.40  
% 7.99/1.40  cnf(u799,axiom,
% 7.99/1.40      X0 != X1 | sK2(X0,X1,k2_tarski(X1,X0)) = X1 | k2_tarski(X0,X1) = k2_tarski(X1,X0)).
% 7.99/1.40  
% 7.99/1.40  cnf(u798,axiom,
% 7.99/1.40      X0 != X1 | sK2(X0,X1,k2_tarski(X1,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X1,X0)).
% 7.99/1.40  
% 7.99/1.40  cnf(u756,axiom,
% 7.99/1.40      X0 != X2 | sK2(X0,X1,k2_tarski(X2,X2)) = X1 | sK2(X0,X1,k2_tarski(X2,X2)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u755,axiom,
% 7.99/1.40      X1 != X2 | sK2(X0,X1,k2_tarski(X2,X2)) = X1 | sK2(X0,X1,k2_tarski(X2,X2)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u754,axiom,
% 7.99/1.40      X0 != X2 | sK2(X0,X1,k2_tarski(X2,X2)) = X1 | sK2(X0,X1,k2_tarski(X2,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u753,axiom,
% 7.99/1.40      X0 != X1 | sK2(X0,X1,k2_tarski(X2,X2)) = X1 | sK2(X0,X1,k2_tarski(X2,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u752,axiom,
% 7.99/1.40      X1 != X2 | sK2(X0,X1,k2_tarski(X2,X2)) = X0 | sK2(X0,X1,k2_tarski(X2,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u751,axiom,
% 7.99/1.40      X0 != X1 | sK2(X0,X1,k2_tarski(X2,X2)) = X0 | sK2(X0,X1,k2_tarski(X2,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u659,axiom,
% 7.99/1.40      X0 != X1 | sK2(X0,X0,k2_tarski(X1,X1)) = X0 | k2_tarski(X0,X0) = k2_tarski(X1,X1)).
% 7.99/1.40  
% 7.99/1.40  cnf(u658,axiom,
% 7.99/1.40      X0 != X1 | sK2(X0,X0,k2_tarski(X1,X1)) = X1 | k2_tarski(X0,X0) = k2_tarski(X1,X1)).
% 7.99/1.40  
% 7.99/1.40  cnf(u626,axiom,
% 7.99/1.40      X0 != X2 | sK2(X0,X1,k2_tarski(X2,X0)) = X1 | sK2(X0,X1,k2_tarski(X2,X0)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 7.99/1.40  
% 7.99/1.40  cnf(u625,axiom,
% 7.99/1.40      X0 != X1 | sK2(X0,X1,k2_tarski(X2,X0)) = X1 | sK2(X0,X1,k2_tarski(X2,X0)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 7.99/1.40  
% 7.99/1.40  cnf(u624,axiom,
% 7.99/1.40      X0 != X2 | sK2(X0,X1,k2_tarski(X2,X0)) = X1 | sK2(X0,X1,k2_tarski(X2,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 7.99/1.40  
% 7.99/1.40  cnf(u623,axiom,
% 7.99/1.40      X1 != X2 | sK2(X0,X1,k2_tarski(X2,X0)) = X1 | sK2(X0,X1,k2_tarski(X2,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 7.99/1.40  
% 7.99/1.40  cnf(u622,axiom,
% 7.99/1.40      X0 != X1 | sK2(X0,X1,k2_tarski(X2,X0)) = X2 | sK2(X0,X1,k2_tarski(X2,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 7.99/1.40  
% 7.99/1.40  cnf(u621,axiom,
% 7.99/1.40      X1 != X2 | sK2(X0,X1,k2_tarski(X2,X0)) = X2 | sK2(X0,X1,k2_tarski(X2,X0)) = X0 | k2_tarski(X0,X1) = k2_tarski(X2,X0)).
% 7.99/1.40  
% 7.99/1.40  cnf(u535,axiom,
% 7.99/1.40      X0 != X2 | sK2(X0,X1,k2_tarski(X0,X2)) = X1 | sK2(X0,X1,k2_tarski(X0,X2)) = X0 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u534,axiom,
% 7.99/1.40      X1 != X2 | sK2(X0,X1,k2_tarski(X0,X2)) = X1 | sK2(X0,X1,k2_tarski(X0,X2)) = X0 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u533,axiom,
% 7.99/1.40      X0 != X2 | sK2(X0,X1,k2_tarski(X0,X2)) = X1 | sK2(X0,X1,k2_tarski(X0,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u532,axiom,
% 7.99/1.40      X0 != X1 | sK2(X0,X1,k2_tarski(X0,X2)) = X1 | sK2(X0,X1,k2_tarski(X0,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u531,axiom,
% 7.99/1.40      X1 != X2 | sK2(X0,X1,k2_tarski(X0,X2)) = X0 | sK2(X0,X1,k2_tarski(X0,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u530,axiom,
% 7.99/1.40      X0 != X1 | sK2(X0,X1,k2_tarski(X0,X2)) = X0 | sK2(X0,X1,k2_tarski(X0,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X0,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u452,axiom,
% 7.99/1.40      X1 != X2 | sK2(X0,X1,k2_tarski(X2,X1)) = X0 | sK2(X0,X1,k2_tarski(X2,X1)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 7.99/1.40  
% 7.99/1.40  cnf(u451,axiom,
% 7.99/1.40      X0 != X1 | sK2(X0,X1,k2_tarski(X2,X1)) = X0 | sK2(X0,X1,k2_tarski(X2,X1)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 7.99/1.40  
% 7.99/1.40  cnf(u450,axiom,
% 7.99/1.40      X1 != X2 | sK2(X0,X1,k2_tarski(X2,X1)) = X0 | sK2(X0,X1,k2_tarski(X2,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 7.99/1.40  
% 7.99/1.40  cnf(u449,axiom,
% 7.99/1.40      X0 != X2 | sK2(X0,X1,k2_tarski(X2,X1)) = X0 | sK2(X0,X1,k2_tarski(X2,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 7.99/1.40  
% 7.99/1.40  cnf(u448,axiom,
% 7.99/1.40      X0 != X1 | sK2(X0,X1,k2_tarski(X2,X1)) = X2 | sK2(X0,X1,k2_tarski(X2,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 7.99/1.40  
% 7.99/1.40  cnf(u447,axiom,
% 7.99/1.40      X0 != X2 | sK2(X0,X1,k2_tarski(X2,X1)) = X2 | sK2(X0,X1,k2_tarski(X2,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X2,X1)).
% 7.99/1.40  
% 7.99/1.40  cnf(u380,axiom,
% 7.99/1.40      X1 != X2 | sK2(X0,X1,k2_tarski(X1,X2)) = X0 | sK2(X0,X1,k2_tarski(X1,X2)) = X1 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u379,axiom,
% 7.99/1.40      X0 != X2 | sK2(X0,X1,k2_tarski(X1,X2)) = X0 | sK2(X0,X1,k2_tarski(X1,X2)) = X1 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u378,axiom,
% 7.99/1.40      X1 != X2 | sK2(X0,X1,k2_tarski(X1,X2)) = X0 | sK2(X0,X1,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u377,axiom,
% 7.99/1.40      X0 != X1 | sK2(X0,X1,k2_tarski(X1,X2)) = X0 | sK2(X0,X1,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u376,axiom,
% 7.99/1.40      X0 != X2 | sK2(X0,X1,k2_tarski(X1,X2)) = X1 | sK2(X0,X1,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u375,axiom,
% 7.99/1.40      X0 != X1 | sK2(X0,X1,k2_tarski(X1,X2)) = X1 | sK2(X0,X1,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X1) = k2_tarski(X1,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u321,axiom,
% 7.99/1.40      X12 != X13 | k2_tarski(X12,X12) = k2_tarski(X13,X12) | ~r2_hidden(X12,k2_tarski(X13,X12))).
% 7.99/1.40  
% 7.99/1.40  cnf(u294,axiom,
% 7.99/1.40      X0 != X1 | sK2(X0,X0,k2_tarski(X1,X0)) = X1 | k2_tarski(X0,X0) = k2_tarski(X1,X0)).
% 7.99/1.40  
% 7.99/1.40  cnf(u293,axiom,
% 7.99/1.40      X0 != X1 | sK2(X0,X0,k2_tarski(X1,X0)) = X0 | k2_tarski(X0,X0) = k2_tarski(X1,X0)).
% 7.99/1.40  
% 7.99/1.40  cnf(u261,axiom,
% 7.99/1.40      X12 != X13 | k2_tarski(X12,X12) = k2_tarski(X12,X13) | ~r2_hidden(X12,k2_tarski(X12,X13))).
% 7.99/1.40  
% 7.99/1.40  cnf(u229,axiom,
% 7.99/1.40      X0 != X1 | sK2(X0,X0,k2_tarski(X0,X1)) = X0 | k2_tarski(X0,X1) = k2_tarski(X0,X0)).
% 7.99/1.40  
% 7.99/1.40  cnf(u228,axiom,
% 7.99/1.40      X0 != X1 | sK2(X0,X0,k2_tarski(X0,X1)) = X1 | k2_tarski(X0,X1) = k2_tarski(X0,X0)).
% 7.99/1.40  
% 7.99/1.40  cnf(u193,axiom,
% 7.99/1.40      X1 != X2 | sK2(X0,X0,k2_tarski(X1,X2)) = X0 | sK2(X0,X0,k2_tarski(X1,X2)) = X1 | k2_tarski(X0,X0) = k2_tarski(X1,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u192,axiom,
% 7.99/1.40      X0 != X2 | sK2(X0,X0,k2_tarski(X1,X2)) = X0 | sK2(X0,X0,k2_tarski(X1,X2)) = X1 | k2_tarski(X0,X0) = k2_tarski(X1,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u191,axiom,
% 7.99/1.40      X1 != X2 | sK2(X0,X0,k2_tarski(X1,X2)) = X0 | sK2(X0,X0,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X0) = k2_tarski(X1,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u190,axiom,
% 7.99/1.40      X0 != X1 | sK2(X0,X0,k2_tarski(X1,X2)) = X0 | sK2(X0,X0,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X0) = k2_tarski(X1,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u189,axiom,
% 7.99/1.40      X0 != X2 | sK2(X0,X0,k2_tarski(X1,X2)) = X1 | sK2(X0,X0,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X0) = k2_tarski(X1,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u188,axiom,
% 7.99/1.40      X0 != X1 | sK2(X0,X0,k2_tarski(X1,X2)) = X1 | sK2(X0,X0,k2_tarski(X1,X2)) = X2 | k2_tarski(X0,X0) = k2_tarski(X1,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u131,negated_conjecture,
% 7.99/1.40      X0 != X1 | sK2(X0,X1,k6_domain_1(u1_struct_0(sK0),sK1)) = X0 | k2_tarski(X0,X1) = k6_domain_1(u1_struct_0(sK0),sK1) | k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)).
% 7.99/1.40  
% 7.99/1.40  cnf(u130,negated_conjecture,
% 7.99/1.40      X0 != X1 | sK2(X0,X1,k6_domain_1(u1_struct_0(sK0),sK1)) = X1 | k2_tarski(X0,X1) = k6_domain_1(u1_struct_0(sK0),sK1) | k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)).
% 7.99/1.40  
% 7.99/1.40  cnf(u103,axiom,
% 7.99/1.40      X2 != X3 | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | sK2(X0,X1,k2_tarski(X2,X3)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 7.99/1.40  
% 7.99/1.40  cnf(u102,axiom,
% 7.99/1.40      X0 != X3 | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | sK2(X0,X1,k2_tarski(X2,X3)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 7.99/1.40  
% 7.99/1.40  cnf(u101,axiom,
% 7.99/1.40      X1 != X3 | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | sK2(X0,X1,k2_tarski(X2,X3)) = X2 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 7.99/1.40  
% 7.99/1.40  cnf(u100,axiom,
% 7.99/1.40      X2 != X3 | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | sK2(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 7.99/1.40  
% 7.99/1.40  cnf(u99,axiom,
% 7.99/1.40      X0 != X2 | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | sK2(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 7.99/1.40  
% 7.99/1.40  cnf(u98,axiom,
% 7.99/1.40      X1 != X2 | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | sK2(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 7.99/1.40  
% 7.99/1.40  cnf(u97,axiom,
% 7.99/1.40      X0 != X3 | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X2 | sK2(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 7.99/1.40  
% 7.99/1.40  cnf(u96,axiom,
% 7.99/1.40      X0 != X2 | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X2 | sK2(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 7.99/1.40  
% 7.99/1.40  cnf(u95,axiom,
% 7.99/1.40      X0 != X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X2 | sK2(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 7.99/1.40  
% 7.99/1.40  cnf(u94,axiom,
% 7.99/1.40      X1 != X3 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | sK2(X0,X1,k2_tarski(X2,X3)) = X2 | sK2(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 7.99/1.40  
% 7.99/1.40  cnf(u93,axiom,
% 7.99/1.40      X1 != X2 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | sK2(X0,X1,k2_tarski(X2,X3)) = X2 | sK2(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 7.99/1.40  
% 7.99/1.40  cnf(u92,axiom,
% 7.99/1.40      X0 != X1 | sK2(X0,X1,k2_tarski(X2,X3)) = X0 | sK2(X0,X1,k2_tarski(X2,X3)) = X2 | sK2(X0,X1,k2_tarski(X2,X3)) = X3 | k2_tarski(X0,X1) = k2_tarski(X2,X3)).
% 7.99/1.40  
% 7.99/1.40  cnf(u3436,axiom,
% 7.99/1.40      sK2(X150,X151,k2_tarski(X152,X152)) != X153 | k2_tarski(X152,X152) = k2_tarski(sK2(X150,X151,k2_tarski(X152,X152)),X153) | ~r2_hidden(sK2(X150,X151,k2_tarski(X152,X152)),k2_tarski(X152,X152)) | sK2(sK2(X150,X151,k2_tarski(X152,X152)),X153,k2_tarski(X152,X152)) = X152 | sK2(X150,X151,k2_tarski(X152,X152)) = X151 | sK2(X150,X151,k2_tarski(X152,X152)) = X150 | k2_tarski(X152,X152) = k2_tarski(X150,X151)).
% 7.99/1.40  
% 7.99/1.40  cnf(u3720,axiom,
% 7.99/1.40      sK2(X162,X163,k2_tarski(X164,X164)) != X161 | k2_tarski(X164,X164) = k2_tarski(X161,sK2(X162,X163,k2_tarski(X164,X164))) | ~r2_hidden(sK2(X162,X163,k2_tarski(X164,X164)),k2_tarski(X164,X164)) | sK2(X161,sK2(X162,X163,k2_tarski(X164,X164)),k2_tarski(X164,X164)) = X164 | sK2(X162,X163,k2_tarski(X164,X164)) = X163 | sK2(X162,X163,k2_tarski(X164,X164)) = X162 | k2_tarski(X164,X164) = k2_tarski(X162,X163)).
% 7.99/1.40  
% 7.99/1.40  cnf(u1041,axiom,
% 7.99/1.40      sK2(X61,X62,k2_tarski(X63,X64)) != X65 | k2_tarski(X63,X64) = k2_tarski(sK2(X61,X62,k2_tarski(X63,X64)),X65) | ~r2_hidden(sK2(X61,X62,k2_tarski(X63,X64)),k2_tarski(X63,X64)) | sK2(sK2(X61,X62,k2_tarski(X63,X64)),X65,k2_tarski(X63,X64)) = X63 | sK2(sK2(X61,X62,k2_tarski(X63,X64)),X65,k2_tarski(X63,X64)) = X64 | sK2(X61,X62,k2_tarski(X63,X64)) = X62 | sK2(X61,X62,k2_tarski(X63,X64)) = X61 | k2_tarski(X61,X62) = k2_tarski(X63,X64)).
% 7.99/1.40  
% 7.99/1.40  cnf(u1440,axiom,
% 7.99/1.40      sK2(X85,X86,k2_tarski(X87,X88)) != X84 | k2_tarski(X87,X88) = k2_tarski(X84,sK2(X85,X86,k2_tarski(X87,X88))) | ~r2_hidden(sK2(X85,X86,k2_tarski(X87,X88)),k2_tarski(X87,X88)) | sK2(X84,sK2(X85,X86,k2_tarski(X87,X88)),k2_tarski(X87,X88)) = X87 | sK2(X84,sK2(X85,X86,k2_tarski(X87,X88)),k2_tarski(X87,X88)) = X88 | sK2(X85,X86,k2_tarski(X87,X88)) = X86 | sK2(X85,X86,k2_tarski(X87,X88)) = X85 | k2_tarski(X85,X86) = k2_tarski(X87,X88)).
% 7.99/1.40  
% 7.99/1.40  cnf(u54,axiom,
% 7.99/1.40      sK2(X0,X1,X2) != X0 | k2_tarski(X0,X1) = X2 | ~r2_hidden(X0,X2)).
% 7.99/1.40  
% 7.99/1.40  cnf(u53,axiom,
% 7.99/1.40      sK2(X0,X1,X2) != X1 | k2_tarski(X0,X1) = X2 | ~r2_hidden(X1,X2)).
% 7.99/1.40  
% 7.99/1.40  % (22143)# SZS output end Saturation.
% 7.99/1.40  % (22143)------------------------------
% 7.99/1.40  % (22143)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.99/1.40  % (22143)Termination reason: Satisfiable
% 7.99/1.40  
% 7.99/1.40  % (22143)Memory used [KB]: 4605
% 7.99/1.40  % (22143)Time elapsed: 0.974 s
% 7.99/1.40  % (22143)------------------------------
% 7.99/1.40  % (22143)------------------------------
% 7.99/1.40  % (22137)Success in time 1.051 s
%------------------------------------------------------------------------------
