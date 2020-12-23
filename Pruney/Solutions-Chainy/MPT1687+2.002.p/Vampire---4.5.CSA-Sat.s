%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:20 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :  116 ( 116 expanded)
%              Number of leaves         :  116 ( 116 expanded)
%              Depth                    :    0
%              Number of atoms          :  285 ( 285 expanded)
%              Number of equality atoms :   90 (  90 expanded)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u76,negated_conjecture,
    ( v23_waybel_0(sK2,sK0,sK1) )).

cnf(u92,axiom,
    ( v4_yellow_0(sK4(X0),X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u91,axiom,
    ( v1_orders_2(sK4(X0))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u190,negated_conjecture,
    ( m1_yellow_0(sK1,sK1) )).

cnf(u189,negated_conjecture,
    ( m1_yellow_0(sK0,sK0) )).

cnf(u191,axiom,
    ( m1_yellow_0(sK4(X0),sK4(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) )).

cnf(u89,axiom,
    ( m1_yellow_0(sK4(X0),X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u87,axiom,
    ( ~ m1_yellow_0(X1,X0)
    | l1_orders_2(X1)
    | ~ l1_orders_2(X0) )).

cnf(u153,axiom,
    ( ~ m1_yellow_0(X1,X0)
    | r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u158,axiom,
    ( ~ m1_yellow_0(X1,X0)
    | r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
    | ~ l1_orders_2(X0) )).

cnf(u136,axiom,
    ( l1_orders_2(sK4(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) )).

cnf(u72,negated_conjecture,
    ( l1_orders_2(sK1) )).

cnf(u70,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u83,axiom,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) )).

cnf(u188,axiom,
    ( ~ l1_orders_2(X1)
    | m1_yellow_0(X1,X1) )).

cnf(u137,axiom,
    ( l1_struct_0(sK4(X0))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u127,negated_conjecture,
    ( l1_struct_0(sK1) )).

cnf(u126,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u90,axiom,
    ( ~ v2_struct_0(sK4(X0))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u71,negated_conjecture,
    ( ~ v2_struct_0(sK1) )).

cnf(u69,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u244,negated_conjecture,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_partfun1(sK2,k1_relat_1(sK2)) )).

cnf(u239,negated_conjecture,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) )).

cnf(u178,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_partfun1(sK2,u1_struct_0(sK0)) )).

cnf(u74,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) )).

cnf(u308,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k1_relat_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2))))
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
    | ~ v1_funct_1(k2_funct_1(sK2)) )).

cnf(u278,negated_conjecture,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | v1_partfun1(sK2,k1_relat_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2) )).

cnf(u125,axiom,
    ( ~ v1_funct_2(X2,k1_xboole_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | v1_partfun1(X2,k1_xboole_0)
    | ~ v1_funct_1(X2) )).

cnf(u246,negated_conjecture,
    ( v1_partfun1(sK2,k1_relat_1(sK2))
    | k1_xboole_0 = u1_struct_0(sK1) )).

cnf(u217,negated_conjecture,
    ( v1_partfun1(sK2,u1_struct_0(sK0))
    | k1_xboole_0 = u1_struct_0(sK1) )).

cnf(u118,axiom,
    ( v1_partfun1(X1,k1_relat_1(X1))
    | ~ v4_relat_1(X1,k1_relat_1(X1))
    | ~ v1_relat_1(X1) )).

cnf(u97,axiom,
    ( ~ v1_partfun1(X1,X0)
    | k1_relat_1(X1) = X0
    | ~ v4_relat_1(X1,X0)
    | ~ v1_relat_1(X1) )).

cnf(u181,negated_conjecture,
    ( v5_relat_1(sK2,k2_relat_1(sK2)) )).

cnf(u145,negated_conjecture,
    ( v5_relat_1(sK2,u1_struct_0(sK1)) )).

cnf(u144,axiom,
    ( v5_relat_1(k1_xboole_0,X0) )).

cnf(u241,negated_conjecture,
    ( v4_relat_1(sK2,k1_relat_1(sK2)) )).

cnf(u143,negated_conjecture,
    ( v4_relat_1(sK2,u1_struct_0(sK0)) )).

cnf(u142,axiom,
    ( v4_relat_1(k1_xboole_0,X0) )).

cnf(u93,axiom,
    ( ~ v2_funct_1(X0)
    | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) )).

cnf(u94,axiom,
    ( ~ v2_funct_1(X0)
    | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) )).

cnf(u112,axiom,
    ( ~ v2_funct_1(X2)
    | k2_relset_1(X0,X1,X2) != X1
    | v1_funct_1(k2_funct_1(X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_1(X2) )).

cnf(u113,axiom,
    ( ~ v2_funct_1(X2)
    | k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(k2_funct_1(X2),X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_1(X2) )).

cnf(u114,axiom,
    ( ~ v2_funct_1(X2)
    | k2_relset_1(X0,X1,X2) != X1
    | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_1(X2) )).

cnf(u73,negated_conjecture,
    ( v1_funct_1(sK2) )).

cnf(u111,axiom,
    ( ~ v1_funct_1(X2)
    | ~ v1_partfun1(X2,X0)
    | v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )).

cnf(u124,axiom,
    ( ~ v1_funct_1(X2)
    | k1_xboole_0 = X1
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(X2,X0,X1)
    | v1_partfun1(X2,X0) )).

cnf(u138,axiom,
    ( v1_relat_1(k1_xboole_0) )).

cnf(u139,negated_conjecture,
    ( v1_relat_1(sK2) )).

cnf(u243,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) )).

cnf(u240,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) )).

cnf(u177,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_relat_1(sK2)))) )).

cnf(u75,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) )).

cnf(u131,axiom,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )).

cnf(u173,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_2(sK2,X0,X1)
    | ~ v1_partfun1(sK2,X0) )).

cnf(u214,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | k1_xboole_0 = X0
    | ~ v1_funct_2(sK2,X1,X0)
    | v1_partfun1(sK2,X1) )).

cnf(u106,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(X2) )).

cnf(u108,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v4_relat_1(X2,X0) )).

cnf(u109,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v5_relat_1(X2,X1) )).

cnf(u107,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) )).

cnf(u175,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) )).

cnf(u104,axiom,
    ( r1_tarski(sK6(X0,X1),X0)
    | r2_hidden(sK6(X0,X1),X1)
    | k1_zfmisc_1(X0) = X1 )).

cnf(u167,axiom,
    ( r2_hidden(sK6(X0,X1),X1)
    | k1_zfmisc_1(X0) = X1
    | k1_xboole_0 = sK6(X0,X1)
    | k1_xboole_0 != X0 )).

cnf(u81,axiom,
    ( r2_hidden(sK3(X0),X0)
    | k1_xboole_0 = k3_tarski(X0) )).

cnf(u121,axiom,
    ( r2_hidden(X3,k1_zfmisc_1(X0))
    | ~ r1_tarski(X3,X0) )).

cnf(u285,axiom,
    ( ~ r2_hidden(sK6(X0,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK6(X0,k1_zfmisc_1(k1_xboole_0))
    | k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0) )).

cnf(u122,axiom,
    ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
    | r1_tarski(X3,X0) )).

cnf(u146,axiom,
    ( ~ r2_hidden(X1,k1_zfmisc_1(X0))
    | k1_xboole_0 != X0
    | k1_xboole_0 = X1 )).

cnf(u160,axiom,
    ( r1_tarski(u1_orders_2(sK4(X0)),u1_orders_2(X0))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u155,axiom,
    ( r1_tarski(u1_struct_0(sK4(X0)),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u256,negated_conjecture,
    ( r1_tarski(u1_struct_0(sK4(sK0)),k1_relat_1(sK2)) )).

cnf(u170,axiom,
    ( r1_tarski(sK6(X2,k1_zfmisc_1(X3)),X2)
    | r1_tarski(sK6(X2,k1_zfmisc_1(X3)),X3)
    | k1_zfmisc_1(X2) = k1_zfmisc_1(X3) )).

cnf(u297,axiom,
    ( r1_tarski(sK6(k1_xboole_0,k1_zfmisc_1(X0)),X0)
    | k1_xboole_0 = sK6(k1_xboole_0,k1_zfmisc_1(X0))
    | k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0) )).

cnf(u280,axiom,
    ( r1_tarski(sK6(X0,k1_zfmisc_1(k1_xboole_0)),X0)
    | k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0)
    | k1_xboole_0 = sK6(X0,k1_zfmisc_1(k1_xboole_0)) )).

cnf(u170_001,axiom,
    ( r1_tarski(sK6(X2,k1_zfmisc_1(X3)),X2)
    | r1_tarski(sK6(X2,k1_zfmisc_1(X3)),X3)
    | k1_zfmisc_1(X2) = k1_zfmisc_1(X3) )).

cnf(u104_002,axiom,
    ( r1_tarski(sK6(X0,X1),X0)
    | r2_hidden(sK6(X0,X1),X1)
    | k1_zfmisc_1(X0) = X1 )).

cnf(u134,axiom,
    ( r1_tarski(sK3(k1_zfmisc_1(X0)),X0)
    | k1_xboole_0 = X0 )).

cnf(u119,axiom,
    ( r1_tarski(X1,X1) )).

cnf(u288,axiom,
    ( ~ r1_tarski(sK6(X2,k1_zfmisc_1(k1_xboole_0)),k1_xboole_0)
    | k1_zfmisc_1(X2) = k1_zfmisc_1(k1_xboole_0)
    | k1_xboole_0 = sK6(X2,k1_zfmisc_1(k1_xboole_0)) )).

cnf(u105,axiom,
    ( ~ r1_tarski(sK6(X0,X1),X0)
    | k1_zfmisc_1(X0) = X1
    | ~ r2_hidden(sK6(X0,X1),X1) )).

cnf(u86,axiom,
    ( ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
    | m1_yellow_0(X1,X0)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X0) )).

cnf(u162,axiom,
    ( ~ r1_tarski(u1_orders_2(X1),u1_orders_2(sK4(X1)))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | u1_orders_2(X1) = u1_orders_2(sK4(X1)) )).

cnf(u157,axiom,
    ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(sK4(X1)))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | u1_struct_0(X1) = u1_struct_0(sK4(X1)) )).

cnf(u252,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(sK2),u1_struct_0(sK4(sK0)))
    | k1_relat_1(sK2) = u1_struct_0(sK4(sK0)) )).

cnf(u117,axiom,
    ( ~ r1_tarski(k2_relat_1(X3),X1)
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )).

cnf(u301,axiom,
    ( ~ r1_tarski(X1,sK6(k1_xboole_0,k1_zfmisc_1(X1)))
    | k1_zfmisc_1(X1) = k1_zfmisc_1(k1_xboole_0)
    | k1_xboole_0 = sK6(k1_xboole_0,k1_zfmisc_1(X1))
    | sK6(k1_xboole_0,k1_zfmisc_1(X1)) = X1 )).

cnf(u206,axiom,
    ( ~ r1_tarski(X4,sK6(X3,k1_zfmisc_1(X4)))
    | k1_zfmisc_1(X3) = k1_zfmisc_1(X4)
    | r1_tarski(sK6(X3,k1_zfmisc_1(X4)),X3)
    | sK6(X3,k1_zfmisc_1(X4)) = X4 )).

cnf(u283,axiom,
    ( ~ r1_tarski(X2,sK6(X2,k1_zfmisc_1(k1_xboole_0)))
    | k1_xboole_0 = sK6(X2,k1_zfmisc_1(k1_xboole_0))
    | k1_zfmisc_1(X2) = k1_zfmisc_1(k1_xboole_0)
    | sK6(X2,k1_zfmisc_1(k1_xboole_0)) = X2 )).

cnf(u203,axiom,
    ( ~ r1_tarski(X4,sK6(X4,k1_zfmisc_1(X5)))
    | k1_zfmisc_1(X5) = k1_zfmisc_1(X4)
    | r1_tarski(sK6(X4,k1_zfmisc_1(X5)),X5)
    | sK6(X4,k1_zfmisc_1(X5)) = X4 )).

cnf(u168,axiom,
    ( ~ r1_tarski(X2,sK6(X2,X3))
    | k1_zfmisc_1(X2) = X3
    | r2_hidden(sK6(X2,X3),X3)
    | sK6(X2,X3) = X2 )).

cnf(u141,axiom,
    ( ~ r1_tarski(X1,sK3(k1_zfmisc_1(X1)))
    | sK3(k1_zfmisc_1(X1)) = X1
    | k1_xboole_0 = X1 )).

cnf(u101,axiom,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 )).

cnf(u147,axiom,
    ( ~ r1_tarski(X1,X0)
    | k1_xboole_0 = X1
    | k1_xboole_0 != X0 )).

cnf(u129,axiom,
    ( v1_xboole_0(k1_xboole_0) )).

cnf(u96,axiom,
    ( v1_xboole_0(sK5(X0)) )).

cnf(u258,negated_conjecture,
    ( ~ v1_xboole_0(k1_relat_1(sK2)) )).

cnf(u88,axiom,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) )).

cnf(u82,axiom,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 )).

cnf(u238,negated_conjecture,
    ( u1_struct_0(sK0) = k1_relat_1(sK2) )).

cnf(u166,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2) )).

cnf(u165,axiom,
    ( k2_relset_1(X0,X1,k1_xboole_0) = k2_relat_1(k1_xboole_0) )).

cnf(u245,negated_conjecture,
    ( k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) )).

cnf(u242,negated_conjecture,
    ( k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2) )).

cnf(u180,negated_conjecture,
    ( k2_relat_1(sK2) = k2_relset_1(u1_struct_0(sK0),k2_relat_1(sK2),sK2) )).

cnf(u78,axiom,
    ( k3_tarski(k1_zfmisc_1(X0)) = X0 )).

cnf(u128,axiom,
    ( k1_xboole_0 = sK5(X0) )).

cnf(u80,axiom,
    ( k1_xboole_0 != sK3(X0)
    | k1_xboole_0 = k3_tarski(X0) )).

cnf(u161,axiom,
    ( k1_xboole_0 != u1_orders_2(X0)
    | v2_struct_0(X0)
    | k1_xboole_0 = u1_orders_2(sK4(X0))
    | ~ l1_orders_2(X0) )).

cnf(u156,axiom,
    ( k1_xboole_0 != u1_struct_0(X0)
    | v2_struct_0(X0)
    | k1_xboole_0 = u1_struct_0(sK4(X0))
    | ~ l1_orders_2(X0) )).

cnf(u254,negated_conjecture,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | k1_xboole_0 = u1_struct_0(sK4(sK0)) )).

cnf(u79,axiom,
    ( k1_xboole_0 != k3_tarski(X0)
    | ~ r2_hidden(X2,X0)
    | k1_xboole_0 = X2 )).

cnf(u149,axiom,
    ( k1_xboole_0 != X2
    | k1_xboole_0 = k3_tarski(k1_zfmisc_1(X2)) )).

cnf(u211,axiom,
    ( k1_xboole_0 != X1
    | k1_xboole_0 = sK6(X0,k1_zfmisc_1(X1))
    | k1_xboole_0 != X0
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) )).

cnf(u212,axiom,
    ( k1_xboole_0 != X0
    | k1_xboole_0 = sK6(X0,k1_zfmisc_1(k1_xboole_0))
    | k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0) )).

cnf(u169,axiom,
    ( k1_xboole_0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
    | r1_tarski(sK6(X0,k1_zfmisc_1(X1)),X0)
    | k1_xboole_0 = sK6(X0,k1_zfmisc_1(X1)) )).

cnf(u202,axiom,
    ( k1_xboole_0 != X2
    | k1_zfmisc_1(X2) = k1_zfmisc_1(X3)
    | k1_xboole_0 = sK6(X2,k1_zfmisc_1(X3))
    | r1_tarski(sK6(X2,k1_zfmisc_1(X3)),X3) )).

cnf(u302,axiom,
    ( k1_xboole_0 != X0
    | k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0)
    | k1_xboole_0 = sK6(k1_xboole_0,k1_zfmisc_1(X0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:11:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (25635)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.50  % (25629)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.50  % (25630)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.50  % (25630)Refutation not found, incomplete strategy% (25630)------------------------------
% 0.22/0.50  % (25630)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (25631)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.51  % (25631)Refutation not found, incomplete strategy% (25631)------------------------------
% 0.22/0.51  % (25631)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (25631)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (25631)Memory used [KB]: 10618
% 0.22/0.51  % (25631)Time elapsed: 0.096 s
% 0.22/0.51  % (25631)------------------------------
% 0.22/0.51  % (25631)------------------------------
% 0.22/0.51  % (25646)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.51  % (25641)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.51  % (25627)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (25640)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.51  % (25645)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.51  % (25625)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.51  % (25636)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.51  % (25625)Refutation not found, incomplete strategy% (25625)------------------------------
% 0.22/0.51  % (25625)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (25625)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (25625)Memory used [KB]: 10618
% 0.22/0.51  % (25625)Time elapsed: 0.078 s
% 0.22/0.51  % (25625)------------------------------
% 0.22/0.51  % (25625)------------------------------
% 0.22/0.52  % (25639)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.52  % (25626)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (25626)Refutation not found, incomplete strategy% (25626)------------------------------
% 0.22/0.52  % (25626)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (25626)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (25626)Memory used [KB]: 10618
% 0.22/0.52  % (25626)Time elapsed: 0.072 s
% 0.22/0.52  % (25626)------------------------------
% 0.22/0.52  % (25626)------------------------------
% 0.22/0.52  % (25638)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (25638)Refutation not found, incomplete strategy% (25638)------------------------------
% 0.22/0.52  % (25638)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (25638)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (25638)Memory used [KB]: 6140
% 0.22/0.52  % (25638)Time elapsed: 0.106 s
% 0.22/0.52  % (25638)------------------------------
% 0.22/0.52  % (25638)------------------------------
% 0.22/0.52  % (25630)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (25630)Memory used [KB]: 6140
% 0.22/0.52  % (25630)Time elapsed: 0.094 s
% 0.22/0.52  % (25630)------------------------------
% 0.22/0.52  % (25630)------------------------------
% 0.22/0.53  % (25643)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.53  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.53  % (25648)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.53  % (25628)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.53  % (25646)# SZS output start Saturation.
% 0.22/0.53  cnf(u76,negated_conjecture,
% 0.22/0.53      v23_waybel_0(sK2,sK0,sK1)).
% 0.22/0.53  
% 0.22/0.53  cnf(u92,axiom,
% 0.22/0.53      v4_yellow_0(sK4(X0),X0) | ~l1_orders_2(X0) | v2_struct_0(X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u91,axiom,
% 0.22/0.53      v1_orders_2(sK4(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u190,negated_conjecture,
% 0.22/0.53      m1_yellow_0(sK1,sK1)).
% 0.22/0.53  
% 0.22/0.53  cnf(u189,negated_conjecture,
% 0.22/0.53      m1_yellow_0(sK0,sK0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u191,axiom,
% 0.22/0.53      m1_yellow_0(sK4(X0),sK4(X0)) | v2_struct_0(X0) | ~l1_orders_2(X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u89,axiom,
% 0.22/0.53      m1_yellow_0(sK4(X0),X0) | ~l1_orders_2(X0) | v2_struct_0(X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u87,axiom,
% 0.22/0.53      ~m1_yellow_0(X1,X0) | l1_orders_2(X1) | ~l1_orders_2(X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u153,axiom,
% 0.22/0.53      ~m1_yellow_0(X1,X0) | r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u158,axiom,
% 0.22/0.53      ~m1_yellow_0(X1,X0) | r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | ~l1_orders_2(X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u136,axiom,
% 0.22/0.53      l1_orders_2(sK4(X0)) | v2_struct_0(X0) | ~l1_orders_2(X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u72,negated_conjecture,
% 0.22/0.53      l1_orders_2(sK1)).
% 0.22/0.53  
% 0.22/0.53  cnf(u70,negated_conjecture,
% 0.22/0.53      l1_orders_2(sK0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u83,axiom,
% 0.22/0.53      ~l1_orders_2(X0) | l1_struct_0(X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u188,axiom,
% 0.22/0.53      ~l1_orders_2(X1) | m1_yellow_0(X1,X1)).
% 0.22/0.53  
% 0.22/0.53  cnf(u137,axiom,
% 0.22/0.53      l1_struct_0(sK4(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u127,negated_conjecture,
% 0.22/0.53      l1_struct_0(sK1)).
% 0.22/0.53  
% 0.22/0.53  cnf(u126,negated_conjecture,
% 0.22/0.53      l1_struct_0(sK0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u90,axiom,
% 0.22/0.53      ~v2_struct_0(sK4(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u71,negated_conjecture,
% 0.22/0.53      ~v2_struct_0(sK1)).
% 0.22/0.53  
% 0.22/0.53  cnf(u69,negated_conjecture,
% 0.22/0.53      ~v2_struct_0(sK0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u244,negated_conjecture,
% 0.22/0.53      v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_partfun1(sK2,k1_relat_1(sK2))).
% 0.22/0.53  
% 0.22/0.53  cnf(u239,negated_conjecture,
% 0.22/0.53      v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))).
% 0.22/0.53  
% 0.22/0.53  cnf(u178,negated_conjecture,
% 0.22/0.53      v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2)) | ~v1_partfun1(sK2,u1_struct_0(sK0))).
% 0.22/0.53  
% 0.22/0.53  cnf(u74,negated_conjecture,
% 0.22/0.53      v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))).
% 0.22/0.53  
% 0.22/0.53  cnf(u308,negated_conjecture,
% 0.22/0.53      ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k1_relat_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2)))) | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) | ~v1_funct_1(k2_funct_1(sK2))).
% 0.22/0.53  
% 0.22/0.53  cnf(u278,negated_conjecture,
% 0.22/0.53      ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | v1_partfun1(sK2,k1_relat_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2)).
% 0.22/0.53  
% 0.22/0.53  cnf(u125,axiom,
% 0.22/0.53      ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_partfun1(X2,k1_xboole_0) | ~v1_funct_1(X2)).
% 0.22/0.53  
% 0.22/0.53  cnf(u246,negated_conjecture,
% 0.22/0.53      v1_partfun1(sK2,k1_relat_1(sK2)) | k1_xboole_0 = u1_struct_0(sK1)).
% 0.22/0.53  
% 0.22/0.53  cnf(u217,negated_conjecture,
% 0.22/0.53      v1_partfun1(sK2,u1_struct_0(sK0)) | k1_xboole_0 = u1_struct_0(sK1)).
% 0.22/0.53  
% 0.22/0.53  cnf(u118,axiom,
% 0.22/0.53      v1_partfun1(X1,k1_relat_1(X1)) | ~v4_relat_1(X1,k1_relat_1(X1)) | ~v1_relat_1(X1)).
% 0.22/0.53  
% 0.22/0.53  cnf(u97,axiom,
% 0.22/0.53      ~v1_partfun1(X1,X0) | k1_relat_1(X1) = X0 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)).
% 0.22/0.53  
% 0.22/0.53  cnf(u181,negated_conjecture,
% 0.22/0.53      v5_relat_1(sK2,k2_relat_1(sK2))).
% 0.22/0.53  
% 0.22/0.53  cnf(u145,negated_conjecture,
% 0.22/0.53      v5_relat_1(sK2,u1_struct_0(sK1))).
% 0.22/0.53  
% 0.22/0.53  cnf(u144,axiom,
% 0.22/0.53      v5_relat_1(k1_xboole_0,X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u241,negated_conjecture,
% 0.22/0.53      v4_relat_1(sK2,k1_relat_1(sK2))).
% 0.22/0.53  
% 0.22/0.53  cnf(u143,negated_conjecture,
% 0.22/0.53      v4_relat_1(sK2,u1_struct_0(sK0))).
% 0.22/0.53  
% 0.22/0.53  cnf(u142,axiom,
% 0.22/0.53      v4_relat_1(k1_xboole_0,X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u93,axiom,
% 0.22/0.53      ~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u94,axiom,
% 0.22/0.53      ~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u112,axiom,
% 0.22/0.53      ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | v1_funct_1(k2_funct_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)).
% 0.22/0.53  
% 0.22/0.53  cnf(u113,axiom,
% 0.22/0.53      ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | v1_funct_2(k2_funct_1(X2),X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)).
% 0.22/0.53  
% 0.22/0.53  cnf(u114,axiom,
% 0.22/0.53      ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)).
% 0.22/0.53  
% 0.22/0.53  cnf(u73,negated_conjecture,
% 0.22/0.53      v1_funct_1(sK2)).
% 0.22/0.53  
% 0.22/0.53  cnf(u111,axiom,
% 0.22/0.53      ~v1_funct_1(X2) | ~v1_partfun1(X2,X0) | v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))).
% 0.22/0.53  
% 0.22/0.53  cnf(u124,axiom,
% 0.22/0.53      ~v1_funct_1(X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u138,axiom,
% 0.22/0.53      v1_relat_1(k1_xboole_0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u139,negated_conjecture,
% 0.22/0.53      v1_relat_1(sK2)).
% 0.22/0.53  
% 0.22/0.53  cnf(u243,negated_conjecture,
% 0.22/0.53      m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))).
% 0.22/0.53  
% 0.22/0.53  cnf(u240,negated_conjecture,
% 0.22/0.53      m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))).
% 0.22/0.53  
% 0.22/0.53  cnf(u177,negated_conjecture,
% 0.22/0.53      m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_relat_1(sK2))))).
% 0.22/0.53  
% 0.22/0.53  cnf(u75,negated_conjecture,
% 0.22/0.53      m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))).
% 0.22/0.53  
% 0.22/0.53  cnf(u131,axiom,
% 0.22/0.53      m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))).
% 0.22/0.53  
% 0.22/0.53  cnf(u173,negated_conjecture,
% 0.22/0.53      ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_2(sK2,X0,X1) | ~v1_partfun1(sK2,X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u214,negated_conjecture,
% 0.22/0.53      ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_xboole_0 = X0 | ~v1_funct_2(sK2,X1,X0) | v1_partfun1(sK2,X1)).
% 0.22/0.53  
% 0.22/0.53  cnf(u106,axiom,
% 0.22/0.53      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)).
% 0.22/0.53  
% 0.22/0.53  cnf(u108,axiom,
% 0.22/0.53      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u109,axiom,
% 0.22/0.53      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)).
% 0.22/0.53  
% 0.22/0.53  cnf(u107,axiom,
% 0.22/0.53      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)).
% 0.22/0.53  
% 0.22/0.53  cnf(u175,axiom,
% 0.22/0.53      ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))).
% 0.22/0.53  
% 0.22/0.53  cnf(u104,axiom,
% 0.22/0.53      r1_tarski(sK6(X0,X1),X0) | r2_hidden(sK6(X0,X1),X1) | k1_zfmisc_1(X0) = X1).
% 0.22/0.53  
% 0.22/0.53  cnf(u167,axiom,
% 0.22/0.53      r2_hidden(sK6(X0,X1),X1) | k1_zfmisc_1(X0) = X1 | k1_xboole_0 = sK6(X0,X1) | k1_xboole_0 != X0).
% 0.22/0.53  
% 0.22/0.53  cnf(u81,axiom,
% 0.22/0.53      r2_hidden(sK3(X0),X0) | k1_xboole_0 = k3_tarski(X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u121,axiom,
% 0.22/0.53      r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u285,axiom,
% 0.22/0.53      ~r2_hidden(sK6(X0,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK6(X0,k1_zfmisc_1(k1_xboole_0)) | k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u122,axiom,
% 0.22/0.53      ~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u146,axiom,
% 0.22/0.53      ~r2_hidden(X1,k1_zfmisc_1(X0)) | k1_xboole_0 != X0 | k1_xboole_0 = X1).
% 0.22/0.53  
% 0.22/0.53  cnf(u160,axiom,
% 0.22/0.53      r1_tarski(u1_orders_2(sK4(X0)),u1_orders_2(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u155,axiom,
% 0.22/0.53      r1_tarski(u1_struct_0(sK4(X0)),u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u256,negated_conjecture,
% 0.22/0.53      r1_tarski(u1_struct_0(sK4(sK0)),k1_relat_1(sK2))).
% 0.22/0.53  
% 0.22/0.53  cnf(u170,axiom,
% 0.22/0.53      r1_tarski(sK6(X2,k1_zfmisc_1(X3)),X2) | r1_tarski(sK6(X2,k1_zfmisc_1(X3)),X3) | k1_zfmisc_1(X2) = k1_zfmisc_1(X3)).
% 0.22/0.53  
% 0.22/0.53  cnf(u297,axiom,
% 0.22/0.53      r1_tarski(sK6(k1_xboole_0,k1_zfmisc_1(X0)),X0) | k1_xboole_0 = sK6(k1_xboole_0,k1_zfmisc_1(X0)) | k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u280,axiom,
% 0.22/0.53      r1_tarski(sK6(X0,k1_zfmisc_1(k1_xboole_0)),X0) | k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0) | k1_xboole_0 = sK6(X0,k1_zfmisc_1(k1_xboole_0))).
% 0.22/0.53  
% 0.22/0.53  cnf(u170,axiom,
% 0.22/0.53      r1_tarski(sK6(X2,k1_zfmisc_1(X3)),X2) | r1_tarski(sK6(X2,k1_zfmisc_1(X3)),X3) | k1_zfmisc_1(X2) = k1_zfmisc_1(X3)).
% 0.22/0.53  
% 0.22/0.53  cnf(u104,axiom,
% 0.22/0.53      r1_tarski(sK6(X0,X1),X0) | r2_hidden(sK6(X0,X1),X1) | k1_zfmisc_1(X0) = X1).
% 0.22/0.53  
% 0.22/0.53  cnf(u134,axiom,
% 0.22/0.53      r1_tarski(sK3(k1_zfmisc_1(X0)),X0) | k1_xboole_0 = X0).
% 0.22/0.53  
% 0.22/0.53  cnf(u119,axiom,
% 0.22/0.53      r1_tarski(X1,X1)).
% 0.22/0.53  
% 0.22/0.53  cnf(u288,axiom,
% 0.22/0.53      ~r1_tarski(sK6(X2,k1_zfmisc_1(k1_xboole_0)),k1_xboole_0) | k1_zfmisc_1(X2) = k1_zfmisc_1(k1_xboole_0) | k1_xboole_0 = sK6(X2,k1_zfmisc_1(k1_xboole_0))).
% 0.22/0.53  
% 0.22/0.53  cnf(u105,axiom,
% 0.22/0.53      ~r1_tarski(sK6(X0,X1),X0) | k1_zfmisc_1(X0) = X1 | ~r2_hidden(sK6(X0,X1),X1)).
% 0.22/0.53  
% 0.22/0.53  cnf(u86,axiom,
% 0.22/0.53      ~r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | m1_yellow_0(X1,X0) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~l1_orders_2(X1) | ~l1_orders_2(X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u162,axiom,
% 0.22/0.53      ~r1_tarski(u1_orders_2(X1),u1_orders_2(sK4(X1))) | v2_struct_0(X1) | ~l1_orders_2(X1) | u1_orders_2(X1) = u1_orders_2(sK4(X1))).
% 0.22/0.53  
% 0.22/0.53  cnf(u157,axiom,
% 0.22/0.53      ~r1_tarski(u1_struct_0(X1),u1_struct_0(sK4(X1))) | v2_struct_0(X1) | ~l1_orders_2(X1) | u1_struct_0(X1) = u1_struct_0(sK4(X1))).
% 0.22/0.53  
% 0.22/0.53  cnf(u252,negated_conjecture,
% 0.22/0.53      ~r1_tarski(k1_relat_1(sK2),u1_struct_0(sK4(sK0))) | k1_relat_1(sK2) = u1_struct_0(sK4(sK0))).
% 0.22/0.53  
% 0.22/0.53  cnf(u117,axiom,
% 0.22/0.53      ~r1_tarski(k2_relat_1(X3),X1) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))).
% 0.22/0.53  
% 0.22/0.53  cnf(u301,axiom,
% 0.22/0.53      ~r1_tarski(X1,sK6(k1_xboole_0,k1_zfmisc_1(X1))) | k1_zfmisc_1(X1) = k1_zfmisc_1(k1_xboole_0) | k1_xboole_0 = sK6(k1_xboole_0,k1_zfmisc_1(X1)) | sK6(k1_xboole_0,k1_zfmisc_1(X1)) = X1).
% 0.22/0.53  
% 0.22/0.53  cnf(u206,axiom,
% 0.22/0.53      ~r1_tarski(X4,sK6(X3,k1_zfmisc_1(X4))) | k1_zfmisc_1(X3) = k1_zfmisc_1(X4) | r1_tarski(sK6(X3,k1_zfmisc_1(X4)),X3) | sK6(X3,k1_zfmisc_1(X4)) = X4).
% 0.22/0.53  
% 0.22/0.53  cnf(u283,axiom,
% 0.22/0.53      ~r1_tarski(X2,sK6(X2,k1_zfmisc_1(k1_xboole_0))) | k1_xboole_0 = sK6(X2,k1_zfmisc_1(k1_xboole_0)) | k1_zfmisc_1(X2) = k1_zfmisc_1(k1_xboole_0) | sK6(X2,k1_zfmisc_1(k1_xboole_0)) = X2).
% 0.22/0.53  
% 0.22/0.53  cnf(u203,axiom,
% 0.22/0.53      ~r1_tarski(X4,sK6(X4,k1_zfmisc_1(X5))) | k1_zfmisc_1(X5) = k1_zfmisc_1(X4) | r1_tarski(sK6(X4,k1_zfmisc_1(X5)),X5) | sK6(X4,k1_zfmisc_1(X5)) = X4).
% 0.22/0.53  
% 0.22/0.53  cnf(u168,axiom,
% 0.22/0.53      ~r1_tarski(X2,sK6(X2,X3)) | k1_zfmisc_1(X2) = X3 | r2_hidden(sK6(X2,X3),X3) | sK6(X2,X3) = X2).
% 0.22/0.53  
% 0.22/0.53  cnf(u141,axiom,
% 0.22/0.53      ~r1_tarski(X1,sK3(k1_zfmisc_1(X1))) | sK3(k1_zfmisc_1(X1)) = X1 | k1_xboole_0 = X1).
% 0.22/0.53  
% 0.22/0.53  cnf(u101,axiom,
% 0.22/0.53      ~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1).
% 0.22/0.53  
% 0.22/0.53  cnf(u147,axiom,
% 0.22/0.53      ~r1_tarski(X1,X0) | k1_xboole_0 = X1 | k1_xboole_0 != X0).
% 0.22/0.53  
% 0.22/0.53  cnf(u129,axiom,
% 0.22/0.53      v1_xboole_0(k1_xboole_0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u96,axiom,
% 0.22/0.53      v1_xboole_0(sK5(X0))).
% 0.22/0.53  
% 0.22/0.53  cnf(u258,negated_conjecture,
% 0.22/0.53      ~v1_xboole_0(k1_relat_1(sK2))).
% 0.22/0.53  
% 0.22/0.53  cnf(u88,axiom,
% 0.22/0.53      ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u82,axiom,
% 0.22/0.53      ~v1_xboole_0(X0) | k1_xboole_0 = X0).
% 0.22/0.53  
% 0.22/0.53  cnf(u238,negated_conjecture,
% 0.22/0.53      u1_struct_0(sK0) = k1_relat_1(sK2)).
% 0.22/0.53  
% 0.22/0.53  cnf(u166,negated_conjecture,
% 0.22/0.53      k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2)).
% 0.22/0.53  
% 0.22/0.53  cnf(u165,axiom,
% 0.22/0.53      k2_relset_1(X0,X1,k1_xboole_0) = k2_relat_1(k1_xboole_0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u245,negated_conjecture,
% 0.22/0.53      k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)).
% 0.22/0.53  
% 0.22/0.53  cnf(u242,negated_conjecture,
% 0.22/0.53      k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2)).
% 0.22/0.53  
% 0.22/0.53  cnf(u180,negated_conjecture,
% 0.22/0.53      k2_relat_1(sK2) = k2_relset_1(u1_struct_0(sK0),k2_relat_1(sK2),sK2)).
% 0.22/0.53  
% 0.22/0.53  cnf(u78,axiom,
% 0.22/0.53      k3_tarski(k1_zfmisc_1(X0)) = X0).
% 0.22/0.53  
% 0.22/0.53  cnf(u128,axiom,
% 0.22/0.53      k1_xboole_0 = sK5(X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u80,axiom,
% 0.22/0.53      k1_xboole_0 != sK3(X0) | k1_xboole_0 = k3_tarski(X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u161,axiom,
% 0.22/0.53      k1_xboole_0 != u1_orders_2(X0) | v2_struct_0(X0) | k1_xboole_0 = u1_orders_2(sK4(X0)) | ~l1_orders_2(X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u156,axiom,
% 0.22/0.53      k1_xboole_0 != u1_struct_0(X0) | v2_struct_0(X0) | k1_xboole_0 = u1_struct_0(sK4(X0)) | ~l1_orders_2(X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u254,negated_conjecture,
% 0.22/0.53      k1_xboole_0 != k1_relat_1(sK2) | k1_xboole_0 = u1_struct_0(sK4(sK0))).
% 0.22/0.53  
% 0.22/0.53  cnf(u79,axiom,
% 0.22/0.53      k1_xboole_0 != k3_tarski(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X2).
% 0.22/0.53  
% 0.22/0.53  cnf(u149,axiom,
% 0.22/0.53      k1_xboole_0 != X2 | k1_xboole_0 = k3_tarski(k1_zfmisc_1(X2))).
% 0.22/0.53  
% 0.22/0.53  cnf(u211,axiom,
% 0.22/0.53      k1_xboole_0 != X1 | k1_xboole_0 = sK6(X0,k1_zfmisc_1(X1)) | k1_xboole_0 != X0 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1)).
% 0.22/0.53  
% 0.22/0.53  cnf(u212,axiom,
% 0.22/0.53      k1_xboole_0 != X0 | k1_xboole_0 = sK6(X0,k1_zfmisc_1(k1_xboole_0)) | k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u169,axiom,
% 0.22/0.53      k1_xboole_0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) | r1_tarski(sK6(X0,k1_zfmisc_1(X1)),X0) | k1_xboole_0 = sK6(X0,k1_zfmisc_1(X1))).
% 0.22/0.53  
% 0.22/0.53  cnf(u202,axiom,
% 0.22/0.53      k1_xboole_0 != X2 | k1_zfmisc_1(X2) = k1_zfmisc_1(X3) | k1_xboole_0 = sK6(X2,k1_zfmisc_1(X3)) | r1_tarski(sK6(X2,k1_zfmisc_1(X3)),X3)).
% 0.22/0.53  
% 0.22/0.53  cnf(u302,axiom,
% 0.22/0.53      k1_xboole_0 != X0 | k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0) | k1_xboole_0 = sK6(k1_xboole_0,k1_zfmisc_1(X0))).
% 0.22/0.53  
% 0.22/0.53  % (25646)# SZS output end Saturation.
% 0.22/0.53  % (25646)------------------------------
% 0.22/0.53  % (25646)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (25646)Termination reason: Satisfiable
% 0.22/0.53  
% 0.22/0.53  % (25646)Memory used [KB]: 6396
% 0.22/0.53  % (25646)Time elapsed: 0.103 s
% 0.22/0.53  % (25646)------------------------------
% 0.22/0.53  % (25646)------------------------------
% 0.22/0.54  % (25624)Success in time 0.175 s
%------------------------------------------------------------------------------
