%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:20 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :  118 ( 118 expanded)
%              Number of leaves         :  118 ( 118 expanded)
%              Depth                    :    0
%              Number of atoms          :  287 ( 287 expanded)
%              Number of equality atoms :   97 (  97 expanded)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u73,axiom,
    ( m1_yellow_0(sK4(X0),X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u240,negated_conjecture,
    ( ~ m1_yellow_0(sK0,X1)
    | ~ l1_orders_2(X1)
    | r1_tarski(k1_relat_1(sK2),u1_struct_0(X1)) )).

cnf(u253,negated_conjecture,
    ( ~ m1_yellow_0(sK0,sK0)
    | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) )).

cnf(u71,axiom,
    ( ~ m1_yellow_0(X1,X0)
    | ~ l1_orders_2(X0)
    | l1_orders_2(X1) )).

cnf(u105,axiom,
    ( l1_orders_2(sK4(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) )).

cnf(u59,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u57,negated_conjecture,
    ( l1_orders_2(sK1) )).

cnf(u67,axiom,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) )).

cnf(u106,axiom,
    ( l1_struct_0(sK4(X0))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u97,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u96,negated_conjecture,
    ( l1_struct_0(sK1) )).

cnf(u74,axiom,
    ( ~ v2_struct_0(sK4(X0))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u58,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u56,negated_conjecture,
    ( ~ v2_struct_0(sK1) )).

cnf(u228,negated_conjecture,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) )).

cnf(u75,axiom,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) )).

cnf(u235,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k1_relat_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2))))
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
    | ~ v1_funct_1(k2_funct_1(sK2)) )).

cnf(u205,negated_conjecture,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_xboole_0 = X1
    | v1_partfun1(sK2,X0) )).

cnf(u95,axiom,
    ( ~ v1_funct_2(X2,k1_xboole_0,X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | v1_partfun1(X2,k1_xboole_0) )).

cnf(u211,negated_conjecture,
    ( v1_partfun1(sK2,k1_relat_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2) )).

cnf(u233,negated_conjecture,
    ( v1_partfun1(sK2,k1_relat_1(sK2))
    | k1_xboole_0 = u1_struct_0(sK1) )).

cnf(u92,axiom,
    ( v1_partfun1(X1,k1_relat_1(X1))
    | ~ v4_relat_1(X1,k1_relat_1(X1))
    | ~ v1_relat_1(X1) )).

cnf(u79,axiom,
    ( ~ v1_partfun1(X1,X0)
    | ~ v4_relat_1(X1,X0)
    | k1_relat_1(X1) = X0
    | ~ v1_relat_1(X1) )).

cnf(u266,axiom,
    ( v4_relat_1(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k2_zfmisc_1(X10,X11))),X10)
    | v1_relat_1(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k2_zfmisc_1(X10,X11))))
    | k1_zfmisc_1(k2_zfmisc_1(X10,X11)) = k1_zfmisc_1(k2_zfmisc_1(X12,X13)) )).

cnf(u282,axiom,
    ( v4_relat_1(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k2_zfmisc_1(X12,X13))),X10)
    | v4_relat_1(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k2_zfmisc_1(X12,X13))),X12)
    | k1_zfmisc_1(k2_zfmisc_1(X10,X11)) = k1_zfmisc_1(k2_zfmisc_1(X12,X13)) )).

cnf(u288,axiom,
    ( v4_relat_1(sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(k2_zfmisc_1(X9,X10))),X9)
    | k1_zfmisc_1(k2_zfmisc_1(X7,X8)) = k1_zfmisc_1(k2_zfmisc_1(X9,X10))
    | k2_relset_1(X7,X8,sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(k2_zfmisc_1(X9,X10)))) = k2_relat_1(sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(k2_zfmisc_1(X9,X10)))) )).

cnf(u166,axiom,
    ( r1_tarski(sK5(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8))),X6)
    | v4_relat_1(sK5(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8))),X7)
    | k1_zfmisc_1(X6) = k1_zfmisc_1(k2_zfmisc_1(X7,X8)) )).

cnf(u174,axiom,
    ( v4_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X2)
    | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))
    | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X2,X3)) )).

cnf(u201,axiom,
    ( v4_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X2)
    | k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X2,X3)) )).

cnf(u314,axiom,
    ( v4_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X2))),X0)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X0,X2)) )).

cnf(u282_001,axiom,
    ( v4_relat_1(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k2_zfmisc_1(X12,X13))),X10)
    | v4_relat_1(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k2_zfmisc_1(X12,X13))),X12)
    | k1_zfmisc_1(k2_zfmisc_1(X10,X11)) = k1_zfmisc_1(k2_zfmisc_1(X12,X13)) )).

cnf(u281,axiom,
    ( v4_relat_1(sK5(k2_zfmisc_1(X6,X7),k1_zfmisc_1(k2_zfmisc_1(X8,X9))),X6)
    | k1_zfmisc_1(k2_zfmisc_1(X8,X9)) = k1_zfmisc_1(k2_zfmisc_1(X6,X7))
    | k2_relset_1(X8,X9,sK5(k2_zfmisc_1(X6,X7),k1_zfmisc_1(k2_zfmisc_1(X8,X9)))) = k2_relat_1(sK5(k2_zfmisc_1(X6,X7),k1_zfmisc_1(k2_zfmisc_1(X8,X9)))) )).

cnf(u160,axiom,
    ( r1_tarski(sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(X9)),X9)
    | v4_relat_1(sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(X9)),X7)
    | k1_zfmisc_1(X9) = k1_zfmisc_1(k2_zfmisc_1(X7,X8)) )).

cnf(u182,axiom,
    ( v4_relat_1(sK5(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k1_xboole_0)),X3)
    | v1_xboole_0(sK5(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k1_xboole_0)))
    | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X3,X4)) )).

cnf(u190,axiom,
    ( v4_relat_1(sK5(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k1_xboole_0)),X3)
    | k1_xboole_0 = sK5(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k1_xboole_0))
    | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X3,X4)) )).

cnf(u148,axiom,
    ( r2_hidden(sK5(k2_zfmisc_1(X5,X6),X7),X7)
    | v4_relat_1(sK5(k2_zfmisc_1(X5,X6),X7),X5)
    | k1_zfmisc_1(k2_zfmisc_1(X5,X6)) = X7 )).

cnf(u121,axiom,
    ( v4_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | k1_xboole_0 = k2_zfmisc_1(X1,X2) )).

cnf(u130,negated_conjecture,
    ( v4_relat_1(sK2,k1_relat_1(sK2)) )).

cnf(u116,axiom,
    ( v4_relat_1(k1_xboole_0,X0) )).

cnf(u53,negated_conjecture,
    ( v1_funct_1(sK2) )).

cnf(u76,axiom,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) )).

cnf(u89,axiom,
    ( ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_xboole_0 = X1
    | v1_partfun1(X2,X0) )).

cnf(u268,axiom,
    ( v1_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X14,X15))))
    | k1_zfmisc_1(k2_zfmisc_1(X14,X15)) = k1_zfmisc_1(k2_zfmisc_1(X16,X17)) )).

cnf(u265,axiom,
    ( v1_relat_1(sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(k2_zfmisc_1(X6,X7))))
    | k1_zfmisc_1(k2_zfmisc_1(X8,X9)) = k1_zfmisc_1(k2_zfmisc_1(X6,X7))
    | k2_relset_1(X6,X7,sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) = k2_relat_1(sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) )).

cnf(u183,axiom,
    ( v1_relat_1(sK5(k2_zfmisc_1(X5,X6),k1_zfmisc_1(k1_xboole_0)))
    | v1_xboole_0(sK5(k2_zfmisc_1(X5,X6),k1_zfmisc_1(k1_xboole_0)))
    | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X5,X6)) )).

cnf(u191,axiom,
    ( v1_relat_1(sK5(k2_zfmisc_1(X5,X6),k1_zfmisc_1(k1_xboole_0)))
    | k1_xboole_0 = sK5(k2_zfmisc_1(X5,X6),k1_zfmisc_1(k1_xboole_0))
    | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X5,X6)) )).

cnf(u175,axiom,
    ( v1_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X4,X5))))
    | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X4,X5))))
    | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X4,X5)) )).

% (13048)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
cnf(u202,axiom,
    ( v1_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X4,X5))))
    | k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X4,X5)) )).

cnf(u115,axiom,
    ( v1_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1))))
    | k1_xboole_0 = k2_zfmisc_1(X0,X1) )).

cnf(u110,negated_conjecture,
    ( v1_relat_1(sK2) )).

cnf(u109,axiom,
    ( v1_relat_1(k1_xboole_0) )).

cnf(u84,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) )).

cnf(u229,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) )).

cnf(u129,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) )).

cnf(u91,axiom,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )).

cnf(u86,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(X2) )).

cnf(u88,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v4_relat_1(X2,X0) )).

cnf(u87,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) )).

cnf(u85,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) )).

cnf(u149,axiom,
    ( r2_hidden(sK5(k2_zfmisc_1(X8,X9),X10),X10)
    | k1_zfmisc_1(k2_zfmisc_1(X8,X9)) = X10
    | v1_relat_1(sK5(k2_zfmisc_1(X8,X9),X10)) )).

cnf(u148_002,axiom,
    ( r2_hidden(sK5(k2_zfmisc_1(X5,X6),X7),X7)
    | v4_relat_1(sK5(k2_zfmisc_1(X5,X6),X7),X5)
    | k1_zfmisc_1(k2_zfmisc_1(X5,X6)) = X7 )).

cnf(u147,axiom,
    ( r2_hidden(sK5(k2_zfmisc_1(X2,X3),X4),X4)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) = X4
    | k2_relset_1(X2,X3,sK5(k2_zfmisc_1(X2,X3),X4)) = k2_relat_1(sK5(k2_zfmisc_1(X2,X3),X4)) )).

cnf(u82,axiom,
    ( r1_tarski(sK5(X0,X1),X0)
    | r2_hidden(sK5(X0,X1),X1)
    | k1_zfmisc_1(X0) = X1 )).

cnf(u65,axiom,
    ( r2_hidden(sK3(X0),X0)
    | k1_xboole_0 = k3_tarski(X0) )).

cnf(u94,axiom,
    ( r2_hidden(X2,k1_zfmisc_1(X0))
    | ~ r1_tarski(X2,X0) )).

cnf(u277,axiom,
    ( ~ r2_hidden(sK5(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(sK5(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | k1_zfmisc_1(X0) = k1_zfmisc_1(k2_zfmisc_1(X1,X2)) )).

cnf(u291,axiom,
    ( ~ r2_hidden(sK5(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_zfmisc_1(X0) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | v4_relat_1(sK5(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1) )).

cnf(u328,axiom,
    ( ~ r2_hidden(sK5(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,sK5(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k2_relat_1(sK5(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | k1_zfmisc_1(X0) = k1_zfmisc_1(k2_zfmisc_1(X1,X2)) )).

cnf(u185,axiom,
    ( ~ r2_hidden(sK5(X0,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | v1_xboole_0(sK5(X0,k1_zfmisc_1(k1_xboole_0)))
    | k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0) )).

% (13045)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
cnf(u123,axiom,
    ( ~ r2_hidden(X0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = X0 )).

cnf(u93,axiom,
    ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
    | r1_tarski(X2,X0) )).

cnf(u161,axiom,
    ( r1_tarski(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(X12)),X12)
    | k1_zfmisc_1(X12) = k1_zfmisc_1(k2_zfmisc_1(X10,X11))
    | v1_relat_1(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(X12))) )).

cnf(u160_003,axiom,
    ( r1_tarski(sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(X9)),X9)
    | v4_relat_1(sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(X9)),X7)
    | k1_zfmisc_1(X9) = k1_zfmisc_1(k2_zfmisc_1(X7,X8)) )).

cnf(u159,axiom,
    ( r1_tarski(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(X6)),X6)
    | k1_zfmisc_1(X6) = k1_zfmisc_1(k2_zfmisc_1(X4,X5))
    | k2_relset_1(X4,X5,sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(X6))) = k2_relat_1(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(X6))) )).

cnf(u158,axiom,
    ( r1_tarski(sK5(k1_xboole_0,k1_zfmisc_1(X3)),X3)
    | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(X3)
    | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(X3))) )).

cnf(u157,axiom,
    ( r1_tarski(sK5(k1_xboole_0,k1_zfmisc_1(X2)),X2)
    | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(X2)
    | k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(X2)) )).

cnf(u150,axiom,
    ( r1_tarski(sK5(X0,k1_zfmisc_1(X1)),X0)
    | r1_tarski(sK5(X0,k1_zfmisc_1(X1)),X1)
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) )).

cnf(u167,axiom,
    ( r1_tarski(sK5(X9,k1_zfmisc_1(k2_zfmisc_1(X10,X11))),X9)
    | k1_zfmisc_1(X9) = k1_zfmisc_1(k2_zfmisc_1(X10,X11))
    | v1_relat_1(sK5(X9,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) )).

cnf(u166_004,axiom,
    ( r1_tarski(sK5(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8))),X6)
    | v4_relat_1(sK5(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8))),X7)
    | k1_zfmisc_1(X6) = k1_zfmisc_1(k2_zfmisc_1(X7,X8)) )).

cnf(u165,axiom,
    ( r1_tarski(sK5(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))),X3)
    | k1_zfmisc_1(X3) = k1_zfmisc_1(k2_zfmisc_1(X4,X5))
    | k2_relset_1(X4,X5,sK5(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) = k2_relat_1(sK5(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) )).

cnf(u164,axiom,
    ( r1_tarski(sK5(X2,k1_zfmisc_1(k1_xboole_0)),X2)
    | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(X2)
    | v1_xboole_0(sK5(X2,k1_zfmisc_1(k1_xboole_0))) )).

cnf(u151,axiom,
    ( r1_tarski(sK5(X2,k1_zfmisc_1(k1_xboole_0)),X2)
    | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(X2)
    | k1_xboole_0 = sK5(X2,k1_zfmisc_1(k1_xboole_0)) )).

cnf(u150_005,axiom,
    ( r1_tarski(sK5(X0,k1_zfmisc_1(X1)),X0)
    | r1_tarski(sK5(X0,k1_zfmisc_1(X1)),X1)
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) )).

cnf(u82_006,axiom,
    ( r1_tarski(sK5(X0,X1),X0)
    | r2_hidden(sK5(X0,X1),X1)
    | k1_zfmisc_1(X0) = X1 )).

cnf(u103,axiom,
    ( r1_tarski(sK3(k1_zfmisc_1(X0)),X0)
    | k1_xboole_0 = X0 )).

cnf(u230,negated_conjecture,
    ( r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))) )).

cnf(u132,negated_conjecture,
    ( r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) )).

cnf(u69,axiom,
    ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X0)
    | ~ m1_yellow_0(X1,X0) )).

cnf(u239,negated_conjecture,
    ( r1_tarski(u1_struct_0(X0),k1_relat_1(sK2))
    | ~ l1_orders_2(X0)
    | ~ m1_yellow_0(X0,sK0) )).

cnf(u68,axiom,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X0)
    | ~ m1_yellow_0(X1,X0) )).

cnf(u98,axiom,
    ( r1_tarski(k1_xboole_0,X0) )).

cnf(u70,axiom,
    ( ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
    | ~ l1_orders_2(X1)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | m1_yellow_0(X1,X0) )).

cnf(u83,axiom,
    ( ~ r1_tarski(sK5(X0,X1),X0)
    | ~ r2_hidden(sK5(X0,X1),X1)
    | k1_zfmisc_1(X0) = X1 )).

cnf(u111,axiom,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0) )).

cnf(u118,axiom,
    ( ~ r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | v4_relat_1(X1,X2) )).

cnf(u140,axiom,
    ( ~ r1_tarski(X4,k2_zfmisc_1(X2,X3))
    | k2_relset_1(X2,X3,X4) = k2_relat_1(X4) )).

cnf(u107,axiom,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | v1_xboole_0(X0) )).

cnf(u124,axiom,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 )).

cnf(u181,axiom,
    ( v1_xboole_0(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | k2_relset_1(X1,X2,sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) = k2_relat_1(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) )).

cnf(u173,axiom,
    ( v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k1_xboole_0)
    | k2_relset_1(X0,X1,sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) = k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )).

cnf(u108,axiom,
    ( v1_xboole_0(k1_xboole_0) )).

cnf(u242,negated_conjecture,
    ( ~ v1_xboole_0(k1_relat_1(sK2)) )).

cnf(u72,axiom,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) )).

cnf(u60,axiom,
    ( r1_xboole_0(X0,k1_xboole_0) )).

cnf(u77,axiom,
    ( ~ r1_xboole_0(X1,X0)
    | ~ r1_tarski(X1,X0)
    | v1_xboole_0(X1) )).

cnf(u226,negated_conjecture,
    ( u1_struct_0(sK0) = k1_relat_1(sK2) )).

cnf(u200,axiom,
    ( k2_relset_1(X0,X1,sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) = k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))
    | k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k1_xboole_0) )).

cnf(u318,axiom,
    ( k2_relat_1(sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) = k2_relset_1(X8,X9,sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(k2_zfmisc_1(X6,X7))))
    | k2_relset_1(X6,X7,sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) = k2_relat_1(sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(k2_zfmisc_1(X6,X7))))
    | k1_zfmisc_1(k2_zfmisc_1(X8,X9)) = k1_zfmisc_1(k2_zfmisc_1(X6,X7)) )).

cnf(u189,axiom,
    ( k2_relset_1(X1,X2,sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) = k2_relat_1(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))
    | k1_xboole_0 = sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0) )).

cnf(u144,axiom,
    ( k2_relset_1(X2,X3,sK3(k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) = k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X2,X3))))
    | k1_xboole_0 = k2_zfmisc_1(X2,X3) )).

cnf(u137,axiom,
    ( k2_relset_1(X0,X1,k1_xboole_0) = k2_relat_1(k1_xboole_0) )).

cnf(u318_007,axiom,
    ( k2_relat_1(sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) = k2_relset_1(X8,X9,sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(k2_zfmisc_1(X6,X7))))
    | k2_relset_1(X6,X7,sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) = k2_relat_1(sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(k2_zfmisc_1(X6,X7))))
    | k1_zfmisc_1(k2_zfmisc_1(X8,X9)) = k1_zfmisc_1(k2_zfmisc_1(X6,X7)) )).

cnf(u232,negated_conjecture,
    ( k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2) )).

cnf(u139,negated_conjecture,
    ( k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) )).

cnf(u62,axiom,
    ( k3_tarski(k1_zfmisc_1(X0)) = X0 )).

cnf(u122,axiom,
    ( k1_xboole_0 != X0
    | ~ r2_hidden(X1,k1_zfmisc_1(X0))
    | k1_xboole_0 = X1 )).

cnf(u66,axiom,
    ( k1_xboole_0 != k3_tarski(X0)
    | ~ r2_hidden(X2,X0)
    | k1_xboole_0 = X2 )).

cnf(u64,axiom,
    ( k1_xboole_0 != sK3(X0)
    | k1_xboole_0 = k3_tarski(X0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:57:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.52  % (13049)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (13057)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.53  % (13065)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (13044)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (13065)Refutation not found, incomplete strategy% (13065)------------------------------
% 0.22/0.53  % (13065)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (13046)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (13065)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (13065)Memory used [KB]: 10874
% 0.22/0.54  % (13065)Time elapsed: 0.114 s
% 0.22/0.54  % (13065)------------------------------
% 0.22/0.54  % (13065)------------------------------
% 0.22/0.54  % (13047)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (13049)# SZS output start Saturation.
% 0.22/0.54  cnf(u73,axiom,
% 0.22/0.54      m1_yellow_0(sK4(X0),X0) | ~l1_orders_2(X0) | v2_struct_0(X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u240,negated_conjecture,
% 0.22/0.54      ~m1_yellow_0(sK0,X1) | ~l1_orders_2(X1) | r1_tarski(k1_relat_1(sK2),u1_struct_0(X1))).
% 0.22/0.54  
% 0.22/0.54  cnf(u253,negated_conjecture,
% 0.22/0.54      ~m1_yellow_0(sK0,sK0) | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2))).
% 0.22/0.54  
% 0.22/0.54  cnf(u71,axiom,
% 0.22/0.54      ~m1_yellow_0(X1,X0) | ~l1_orders_2(X0) | l1_orders_2(X1)).
% 0.22/0.54  
% 0.22/0.54  cnf(u105,axiom,
% 0.22/0.54      l1_orders_2(sK4(X0)) | v2_struct_0(X0) | ~l1_orders_2(X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u59,negated_conjecture,
% 0.22/0.54      l1_orders_2(sK0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u57,negated_conjecture,
% 0.22/0.54      l1_orders_2(sK1)).
% 0.22/0.54  
% 0.22/0.54  cnf(u67,axiom,
% 0.22/0.54      ~l1_orders_2(X0) | l1_struct_0(X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u106,axiom,
% 0.22/0.54      l1_struct_0(sK4(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u97,negated_conjecture,
% 0.22/0.54      l1_struct_0(sK0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u96,negated_conjecture,
% 0.22/0.54      l1_struct_0(sK1)).
% 0.22/0.54  
% 0.22/0.54  cnf(u74,axiom,
% 0.22/0.54      ~v2_struct_0(sK4(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u58,negated_conjecture,
% 0.22/0.54      ~v2_struct_0(sK0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u56,negated_conjecture,
% 0.22/0.54      ~v2_struct_0(sK1)).
% 0.22/0.54  
% 0.22/0.54  cnf(u228,negated_conjecture,
% 0.22/0.54      v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))).
% 0.22/0.54  
% 0.22/0.54  cnf(u75,axiom,
% 0.22/0.54      v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u235,negated_conjecture,
% 0.22/0.54      ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k1_relat_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2)))) | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) | ~v1_funct_1(k2_funct_1(sK2))).
% 0.22/0.54  
% 0.22/0.54  cnf(u205,negated_conjecture,
% 0.22/0.54      ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | v1_partfun1(sK2,X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u95,axiom,
% 0.22/0.54      ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_partfun1(X2,k1_xboole_0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u211,negated_conjecture,
% 0.22/0.54      v1_partfun1(sK2,k1_relat_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2)).
% 0.22/0.54  
% 0.22/0.54  cnf(u233,negated_conjecture,
% 0.22/0.54      v1_partfun1(sK2,k1_relat_1(sK2)) | k1_xboole_0 = u1_struct_0(sK1)).
% 0.22/0.54  
% 0.22/0.54  cnf(u92,axiom,
% 0.22/0.54      v1_partfun1(X1,k1_relat_1(X1)) | ~v4_relat_1(X1,k1_relat_1(X1)) | ~v1_relat_1(X1)).
% 0.22/0.54  
% 0.22/0.54  cnf(u79,axiom,
% 0.22/0.54      ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)).
% 0.22/0.54  
% 0.22/0.54  cnf(u266,axiom,
% 0.22/0.54      v4_relat_1(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k2_zfmisc_1(X10,X11))),X10) | v1_relat_1(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) | k1_zfmisc_1(k2_zfmisc_1(X10,X11)) = k1_zfmisc_1(k2_zfmisc_1(X12,X13))).
% 0.22/0.54  
% 0.22/0.54  cnf(u282,axiom,
% 0.22/0.54      v4_relat_1(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k2_zfmisc_1(X12,X13))),X10) | v4_relat_1(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k2_zfmisc_1(X12,X13))),X12) | k1_zfmisc_1(k2_zfmisc_1(X10,X11)) = k1_zfmisc_1(k2_zfmisc_1(X12,X13))).
% 0.22/0.54  
% 0.22/0.54  cnf(u288,axiom,
% 0.22/0.54      v4_relat_1(sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(k2_zfmisc_1(X9,X10))),X9) | k1_zfmisc_1(k2_zfmisc_1(X7,X8)) = k1_zfmisc_1(k2_zfmisc_1(X9,X10)) | k2_relset_1(X7,X8,sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(k2_zfmisc_1(X9,X10)))) = k2_relat_1(sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(k2_zfmisc_1(X9,X10))))).
% 0.22/0.54  
% 0.22/0.54  cnf(u166,axiom,
% 0.22/0.54      r1_tarski(sK5(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8))),X6) | v4_relat_1(sK5(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8))),X7) | k1_zfmisc_1(X6) = k1_zfmisc_1(k2_zfmisc_1(X7,X8))).
% 0.22/0.54  
% 0.22/0.54  cnf(u174,axiom,
% 0.22/0.54      v4_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X2) | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))).
% 0.22/0.54  
% 0.22/0.54  cnf(u201,axiom,
% 0.22/0.54      v4_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X2) | k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))).
% 0.22/0.54  
% 0.22/0.54  cnf(u314,axiom,
% 0.22/0.54      v4_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X2))),X0) | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X0,X2))).
% 0.22/0.54  
% 0.22/0.54  cnf(u282,axiom,
% 0.22/0.54      v4_relat_1(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k2_zfmisc_1(X12,X13))),X10) | v4_relat_1(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k2_zfmisc_1(X12,X13))),X12) | k1_zfmisc_1(k2_zfmisc_1(X10,X11)) = k1_zfmisc_1(k2_zfmisc_1(X12,X13))).
% 0.22/0.54  
% 0.22/0.54  cnf(u281,axiom,
% 0.22/0.54      v4_relat_1(sK5(k2_zfmisc_1(X6,X7),k1_zfmisc_1(k2_zfmisc_1(X8,X9))),X6) | k1_zfmisc_1(k2_zfmisc_1(X8,X9)) = k1_zfmisc_1(k2_zfmisc_1(X6,X7)) | k2_relset_1(X8,X9,sK5(k2_zfmisc_1(X6,X7),k1_zfmisc_1(k2_zfmisc_1(X8,X9)))) = k2_relat_1(sK5(k2_zfmisc_1(X6,X7),k1_zfmisc_1(k2_zfmisc_1(X8,X9))))).
% 0.22/0.54  
% 0.22/0.54  cnf(u160,axiom,
% 0.22/0.54      r1_tarski(sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(X9)),X9) | v4_relat_1(sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(X9)),X7) | k1_zfmisc_1(X9) = k1_zfmisc_1(k2_zfmisc_1(X7,X8))).
% 0.22/0.54  
% 0.22/0.54  cnf(u182,axiom,
% 0.22/0.54      v4_relat_1(sK5(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k1_xboole_0)),X3) | v1_xboole_0(sK5(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k1_xboole_0))) | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))).
% 0.22/0.54  
% 0.22/0.54  cnf(u190,axiom,
% 0.22/0.54      v4_relat_1(sK5(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k1_xboole_0)),X3) | k1_xboole_0 = sK5(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k1_xboole_0)) | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))).
% 0.22/0.54  
% 0.22/0.54  cnf(u148,axiom,
% 0.22/0.54      r2_hidden(sK5(k2_zfmisc_1(X5,X6),X7),X7) | v4_relat_1(sK5(k2_zfmisc_1(X5,X6),X7),X5) | k1_zfmisc_1(k2_zfmisc_1(X5,X6)) = X7).
% 0.22/0.54  
% 0.22/0.54  cnf(u121,axiom,
% 0.22/0.54      v4_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1) | k1_xboole_0 = k2_zfmisc_1(X1,X2)).
% 0.22/0.54  
% 0.22/0.54  cnf(u130,negated_conjecture,
% 0.22/0.54      v4_relat_1(sK2,k1_relat_1(sK2))).
% 0.22/0.54  
% 0.22/0.54  cnf(u116,axiom,
% 0.22/0.54      v4_relat_1(k1_xboole_0,X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u53,negated_conjecture,
% 0.22/0.54      v1_funct_1(sK2)).
% 0.22/0.54  
% 0.22/0.54  cnf(u76,axiom,
% 0.22/0.54      ~v1_funct_1(X0) | ~v1_relat_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))).
% 0.22/0.54  
% 0.22/0.54  cnf(u89,axiom,
% 0.22/0.54      ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | v1_partfun1(X2,X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u268,axiom,
% 0.22/0.54      v1_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X14,X15)))) | k1_zfmisc_1(k2_zfmisc_1(X14,X15)) = k1_zfmisc_1(k2_zfmisc_1(X16,X17))).
% 0.22/0.54  
% 0.22/0.54  cnf(u265,axiom,
% 0.22/0.54      v1_relat_1(sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) | k1_zfmisc_1(k2_zfmisc_1(X8,X9)) = k1_zfmisc_1(k2_zfmisc_1(X6,X7)) | k2_relset_1(X6,X7,sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) = k2_relat_1(sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(k2_zfmisc_1(X6,X7))))).
% 0.22/0.54  
% 0.22/0.54  cnf(u183,axiom,
% 0.22/0.54      v1_relat_1(sK5(k2_zfmisc_1(X5,X6),k1_zfmisc_1(k1_xboole_0))) | v1_xboole_0(sK5(k2_zfmisc_1(X5,X6),k1_zfmisc_1(k1_xboole_0))) | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X5,X6))).
% 0.22/0.54  
% 0.22/0.54  cnf(u191,axiom,
% 0.22/0.54      v1_relat_1(sK5(k2_zfmisc_1(X5,X6),k1_zfmisc_1(k1_xboole_0))) | k1_xboole_0 = sK5(k2_zfmisc_1(X5,X6),k1_zfmisc_1(k1_xboole_0)) | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X5,X6))).
% 0.22/0.54  
% 0.22/0.54  cnf(u175,axiom,
% 0.22/0.54      v1_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X4,X5))).
% 0.22/0.54  
% 0.22/0.54  % (13048)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  cnf(u202,axiom,
% 0.22/0.54      v1_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) | k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X4,X5))).
% 0.22/0.54  
% 0.22/0.54  cnf(u115,axiom,
% 0.22/0.54      v1_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | k1_xboole_0 = k2_zfmisc_1(X0,X1)).
% 0.22/0.54  
% 0.22/0.54  cnf(u110,negated_conjecture,
% 0.22/0.54      v1_relat_1(sK2)).
% 0.22/0.54  
% 0.22/0.54  cnf(u109,axiom,
% 0.22/0.54      v1_relat_1(k1_xboole_0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u84,axiom,
% 0.22/0.54      m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)).
% 0.22/0.54  
% 0.22/0.54  cnf(u229,negated_conjecture,
% 0.22/0.54      m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))).
% 0.22/0.54  
% 0.22/0.54  cnf(u129,negated_conjecture,
% 0.22/0.54      m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))).
% 0.22/0.54  
% 0.22/0.54  cnf(u91,axiom,
% 0.22/0.54      m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))).
% 0.22/0.54  
% 0.22/0.54  cnf(u86,axiom,
% 0.22/0.54      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)).
% 0.22/0.54  
% 0.22/0.54  cnf(u88,axiom,
% 0.22/0.54      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u87,axiom,
% 0.22/0.54      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)).
% 0.22/0.54  
% 0.22/0.54  cnf(u85,axiom,
% 0.22/0.54      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)).
% 0.22/0.54  
% 0.22/0.54  cnf(u149,axiom,
% 0.22/0.54      r2_hidden(sK5(k2_zfmisc_1(X8,X9),X10),X10) | k1_zfmisc_1(k2_zfmisc_1(X8,X9)) = X10 | v1_relat_1(sK5(k2_zfmisc_1(X8,X9),X10))).
% 0.22/0.54  
% 0.22/0.54  cnf(u148,axiom,
% 0.22/0.54      r2_hidden(sK5(k2_zfmisc_1(X5,X6),X7),X7) | v4_relat_1(sK5(k2_zfmisc_1(X5,X6),X7),X5) | k1_zfmisc_1(k2_zfmisc_1(X5,X6)) = X7).
% 0.22/0.54  
% 0.22/0.54  cnf(u147,axiom,
% 0.22/0.54      r2_hidden(sK5(k2_zfmisc_1(X2,X3),X4),X4) | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) = X4 | k2_relset_1(X2,X3,sK5(k2_zfmisc_1(X2,X3),X4)) = k2_relat_1(sK5(k2_zfmisc_1(X2,X3),X4))).
% 0.22/0.54  
% 0.22/0.54  cnf(u82,axiom,
% 0.22/0.54      r1_tarski(sK5(X0,X1),X0) | r2_hidden(sK5(X0,X1),X1) | k1_zfmisc_1(X0) = X1).
% 0.22/0.54  
% 0.22/0.54  cnf(u65,axiom,
% 0.22/0.54      r2_hidden(sK3(X0),X0) | k1_xboole_0 = k3_tarski(X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u94,axiom,
% 0.22/0.54      r2_hidden(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X2,X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u277,axiom,
% 0.22/0.54      ~r2_hidden(sK5(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(sK5(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) | k1_zfmisc_1(X0) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))).
% 0.22/0.54  
% 0.22/0.54  cnf(u291,axiom,
% 0.22/0.54      ~r2_hidden(sK5(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_zfmisc_1(X0) = k1_zfmisc_1(k2_zfmisc_1(X1,X2)) | v4_relat_1(sK5(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)).
% 0.22/0.54  
% 0.22/0.54  cnf(u328,axiom,
% 0.22/0.54      ~r2_hidden(sK5(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k2_relset_1(X1,X2,sK5(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k2_relat_1(sK5(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) | k1_zfmisc_1(X0) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))).
% 0.22/0.54  
% 0.22/0.54  cnf(u185,axiom,
% 0.22/0.54      ~r2_hidden(sK5(X0,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(sK5(X0,k1_zfmisc_1(k1_xboole_0))) | k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0)).
% 0.22/0.54  
% 0.22/0.54  % (13045)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  cnf(u123,axiom,
% 0.22/0.54      ~r2_hidden(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0).
% 0.22/0.54  
% 0.22/0.54  cnf(u93,axiom,
% 0.22/0.54      ~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u161,axiom,
% 0.22/0.54      r1_tarski(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(X12)),X12) | k1_zfmisc_1(X12) = k1_zfmisc_1(k2_zfmisc_1(X10,X11)) | v1_relat_1(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(X12)))).
% 0.22/0.54  
% 0.22/0.54  cnf(u160,axiom,
% 0.22/0.54      r1_tarski(sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(X9)),X9) | v4_relat_1(sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(X9)),X7) | k1_zfmisc_1(X9) = k1_zfmisc_1(k2_zfmisc_1(X7,X8))).
% 0.22/0.54  
% 0.22/0.54  cnf(u159,axiom,
% 0.22/0.54      r1_tarski(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(X6)),X6) | k1_zfmisc_1(X6) = k1_zfmisc_1(k2_zfmisc_1(X4,X5)) | k2_relset_1(X4,X5,sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(X6))) = k2_relat_1(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(X6)))).
% 0.22/0.54  
% 0.22/0.54  cnf(u158,axiom,
% 0.22/0.54      r1_tarski(sK5(k1_xboole_0,k1_zfmisc_1(X3)),X3) | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(X3) | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(X3)))).
% 0.22/0.54  
% 0.22/0.54  cnf(u157,axiom,
% 0.22/0.54      r1_tarski(sK5(k1_xboole_0,k1_zfmisc_1(X2)),X2) | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(X2) | k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(X2))).
% 0.22/0.54  
% 0.22/0.54  cnf(u150,axiom,
% 0.22/0.54      r1_tarski(sK5(X0,k1_zfmisc_1(X1)),X0) | r1_tarski(sK5(X0,k1_zfmisc_1(X1)),X1) | k1_zfmisc_1(X0) = k1_zfmisc_1(X1)).
% 0.22/0.54  
% 0.22/0.54  cnf(u167,axiom,
% 0.22/0.54      r1_tarski(sK5(X9,k1_zfmisc_1(k2_zfmisc_1(X10,X11))),X9) | k1_zfmisc_1(X9) = k1_zfmisc_1(k2_zfmisc_1(X10,X11)) | v1_relat_1(sK5(X9,k1_zfmisc_1(k2_zfmisc_1(X10,X11))))).
% 0.22/0.54  
% 0.22/0.54  cnf(u166,axiom,
% 0.22/0.54      r1_tarski(sK5(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8))),X6) | v4_relat_1(sK5(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8))),X7) | k1_zfmisc_1(X6) = k1_zfmisc_1(k2_zfmisc_1(X7,X8))).
% 0.22/0.54  
% 0.22/0.54  cnf(u165,axiom,
% 0.22/0.54      r1_tarski(sK5(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))),X3) | k1_zfmisc_1(X3) = k1_zfmisc_1(k2_zfmisc_1(X4,X5)) | k2_relset_1(X4,X5,sK5(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) = k2_relat_1(sK5(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))))).
% 0.22/0.54  
% 0.22/0.54  cnf(u164,axiom,
% 0.22/0.54      r1_tarski(sK5(X2,k1_zfmisc_1(k1_xboole_0)),X2) | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(X2) | v1_xboole_0(sK5(X2,k1_zfmisc_1(k1_xboole_0)))).
% 0.22/0.54  
% 0.22/0.54  cnf(u151,axiom,
% 0.22/0.54      r1_tarski(sK5(X2,k1_zfmisc_1(k1_xboole_0)),X2) | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(X2) | k1_xboole_0 = sK5(X2,k1_zfmisc_1(k1_xboole_0))).
% 0.22/0.54  
% 0.22/0.54  cnf(u150,axiom,
% 0.22/0.54      r1_tarski(sK5(X0,k1_zfmisc_1(X1)),X0) | r1_tarski(sK5(X0,k1_zfmisc_1(X1)),X1) | k1_zfmisc_1(X0) = k1_zfmisc_1(X1)).
% 0.22/0.54  
% 0.22/0.54  cnf(u82,axiom,
% 0.22/0.54      r1_tarski(sK5(X0,X1),X0) | r2_hidden(sK5(X0,X1),X1) | k1_zfmisc_1(X0) = X1).
% 0.22/0.54  
% 0.22/0.54  cnf(u103,axiom,
% 0.22/0.54      r1_tarski(sK3(k1_zfmisc_1(X0)),X0) | k1_xboole_0 = X0).
% 0.22/0.54  
% 0.22/0.54  cnf(u230,negated_conjecture,
% 0.22/0.54      r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))).
% 0.22/0.54  
% 0.22/0.54  cnf(u132,negated_conjecture,
% 0.22/0.54      r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))).
% 0.22/0.54  
% 0.22/0.54  cnf(u69,axiom,
% 0.22/0.54      r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | ~l1_orders_2(X1) | ~l1_orders_2(X0) | ~m1_yellow_0(X1,X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u239,negated_conjecture,
% 0.22/0.54      r1_tarski(u1_struct_0(X0),k1_relat_1(sK2)) | ~l1_orders_2(X0) | ~m1_yellow_0(X0,sK0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u68,axiom,
% 0.22/0.54      r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~l1_orders_2(X1) | ~l1_orders_2(X0) | ~m1_yellow_0(X1,X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u98,axiom,
% 0.22/0.54      r1_tarski(k1_xboole_0,X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u70,axiom,
% 0.22/0.54      ~r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | ~l1_orders_2(X1) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~l1_orders_2(X0) | m1_yellow_0(X1,X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u83,axiom,
% 0.22/0.54      ~r1_tarski(sK5(X0,X1),X0) | ~r2_hidden(sK5(X0,X1),X1) | k1_zfmisc_1(X0) = X1).
% 0.22/0.54  
% 0.22/0.54  cnf(u111,axiom,
% 0.22/0.54      ~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | v1_relat_1(X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u118,axiom,
% 0.22/0.54      ~r1_tarski(X1,k2_zfmisc_1(X2,X3)) | v4_relat_1(X1,X2)).
% 0.22/0.54  
% 0.22/0.54  cnf(u140,axiom,
% 0.22/0.54      ~r1_tarski(X4,k2_zfmisc_1(X2,X3)) | k2_relset_1(X2,X3,X4) = k2_relat_1(X4)).
% 0.22/0.54  
% 0.22/0.54  cnf(u107,axiom,
% 0.22/0.54      ~r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u124,axiom,
% 0.22/0.54      ~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0).
% 0.22/0.54  
% 0.22/0.54  cnf(u181,axiom,
% 0.22/0.54      v1_xboole_0(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0) | k2_relset_1(X1,X2,sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) = k2_relat_1(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))).
% 0.22/0.54  
% 0.22/0.54  cnf(u173,axiom,
% 0.22/0.54      v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k1_xboole_0) | k2_relset_1(X0,X1,sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) = k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))).
% 0.22/0.54  
% 0.22/0.54  cnf(u108,axiom,
% 0.22/0.54      v1_xboole_0(k1_xboole_0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u242,negated_conjecture,
% 0.22/0.54      ~v1_xboole_0(k1_relat_1(sK2))).
% 0.22/0.54  
% 0.22/0.54  cnf(u72,axiom,
% 0.22/0.54      ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u60,axiom,
% 0.22/0.54      r1_xboole_0(X0,k1_xboole_0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u77,axiom,
% 0.22/0.54      ~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)).
% 0.22/0.54  
% 0.22/0.54  cnf(u226,negated_conjecture,
% 0.22/0.54      u1_struct_0(sK0) = k1_relat_1(sK2)).
% 0.22/0.54  
% 0.22/0.54  cnf(u200,axiom,
% 0.22/0.54      k2_relset_1(X0,X1,sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) = k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k1_xboole_0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u318,axiom,
% 0.22/0.54      k2_relat_1(sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) = k2_relset_1(X8,X9,sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) | k2_relset_1(X6,X7,sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) = k2_relat_1(sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) | k1_zfmisc_1(k2_zfmisc_1(X8,X9)) = k1_zfmisc_1(k2_zfmisc_1(X6,X7))).
% 0.22/0.54  
% 0.22/0.54  cnf(u189,axiom,
% 0.22/0.54      k2_relset_1(X1,X2,sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) = k2_relat_1(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) | k1_xboole_0 = sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)) | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u144,axiom,
% 0.22/0.54      k2_relset_1(X2,X3,sK3(k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) = k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) | k1_xboole_0 = k2_zfmisc_1(X2,X3)).
% 0.22/0.54  
% 0.22/0.54  cnf(u137,axiom,
% 0.22/0.54      k2_relset_1(X0,X1,k1_xboole_0) = k2_relat_1(k1_xboole_0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u318,axiom,
% 0.22/0.54      k2_relat_1(sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) = k2_relset_1(X8,X9,sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) | k2_relset_1(X6,X7,sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) = k2_relat_1(sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) | k1_zfmisc_1(k2_zfmisc_1(X8,X9)) = k1_zfmisc_1(k2_zfmisc_1(X6,X7))).
% 0.22/0.54  
% 0.22/0.54  cnf(u232,negated_conjecture,
% 0.22/0.54      k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2)).
% 0.22/0.54  
% 0.22/0.54  cnf(u139,negated_conjecture,
% 0.22/0.54      k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)).
% 0.22/0.54  
% 0.22/0.54  cnf(u62,axiom,
% 0.22/0.54      k3_tarski(k1_zfmisc_1(X0)) = X0).
% 0.22/0.54  
% 0.22/0.54  cnf(u122,axiom,
% 0.22/0.54      k1_xboole_0 != X0 | ~r2_hidden(X1,k1_zfmisc_1(X0)) | k1_xboole_0 = X1).
% 0.22/0.54  
% 0.22/0.54  cnf(u66,axiom,
% 0.22/0.54      k1_xboole_0 != k3_tarski(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X2).
% 0.22/0.54  
% 0.22/0.54  cnf(u64,axiom,
% 0.22/0.54      k1_xboole_0 != sK3(X0) | k1_xboole_0 = k3_tarski(X0)).
% 0.22/0.54  
% 0.22/0.54  % (13049)# SZS output end Saturation.
% 0.22/0.54  % (13049)------------------------------
% 0.22/0.54  % (13049)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (13049)Termination reason: Satisfiable
% 0.22/0.54  
% 0.22/0.54  % (13049)Memory used [KB]: 6396
% 0.22/0.54  % (13049)Time elapsed: 0.104 s
% 0.22/0.54  % (13049)------------------------------
% 0.22/0.54  % (13049)------------------------------
% 0.22/0.54  % (13042)Success in time 0.178 s
%------------------------------------------------------------------------------
