%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:35 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :  148 ( 148 expanded)
%              Number of leaves         :  148 ( 148 expanded)
%              Depth                    :    0
%              Number of atoms          :  579 ( 579 expanded)
%              Number of equality atoms :   78 (  78 expanded)
%              Maximal clause size      :   16 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u368,negated_conjecture,
    ( r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),X0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) )).

cnf(u63,negated_conjecture,
    ( ~ r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK3) )).

cnf(u64,axiom,
    ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
    | ~ r1_tsep_1(X0,X1)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0) )).

cnf(u362,negated_conjecture,
    ( ~ r1_xboole_0(u1_struct_0(sK2),X2)
    | ~ m1_subset_1(X3,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tmap_1(sK2,k6_tmap_1(sK0,X2),k2_tmap_1(sK0,k6_tmap_1(sK0,X2),k7_tmap_1(sK0,X2),sK2),X3) )).

cnf(u154,negated_conjecture,
    ( ~ r1_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))
    | r1_tsep_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1)) )).

cnf(u155,negated_conjecture,
    ( ~ r1_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))
    | r1_tsep_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK2))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK2)) )).

cnf(u165,negated_conjecture,
    ( ~ r1_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))
    | r1_tsep_1(k8_tmap_1(sK0,sK2),k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK2)) )).

cnf(u174,negated_conjecture,
    ( ~ r1_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))
    | r1_tsep_1(k8_tmap_1(sK0,sK2),k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1)) )).

cnf(u175,negated_conjecture,
    ( ~ r1_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))
    | r1_tsep_1(k8_tmap_1(sK0,sK2),k8_tmap_1(sK0,sK2))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK2)) )).

cnf(u184,negated_conjecture,
    ( ~ r1_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))
    | r1_tsep_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK2))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1)) )).

cnf(u152,negated_conjecture,
    ( ~ r1_xboole_0(u1_struct_0(sK0),u1_struct_0(X0))
    | r1_tsep_1(k8_tmap_1(sK0,sK1),X0)
    | ~ l1_pre_topc(X0) )).

cnf(u172,negated_conjecture,
    ( ~ r1_xboole_0(u1_struct_0(sK0),u1_struct_0(X0))
    | r1_tsep_1(k8_tmap_1(sK0,sK2),X0)
    | ~ l1_pre_topc(X0) )).

cnf(u162,negated_conjecture,
    ( ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK0))
    | r1_tsep_1(X0,k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(X0) )).

cnf(u182,negated_conjecture,
    ( ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK0))
    | r1_tsep_1(X0,k8_tmap_1(sK0,sK2))
    | ~ l1_pre_topc(X0) )).

cnf(u65,axiom,
    ( ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
    | r1_tsep_1(X0,X1)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0) )).

cnf(u104,negated_conjecture,
    ( r1_tsep_1(sK2,sK1) )).

cnf(u61,negated_conjecture,
    ( r1_tsep_1(sK1,sK2) )).

cnf(u365,negated_conjecture,
    ( ~ r1_tsep_1(sK2,X0)
    | r1_tmap_1(sK2,k6_tmap_1(sK0,u1_struct_0(X0)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(X0)),k7_tmap_1(sK0,u1_struct_0(X0)),sK2),X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) )).

cnf(u188,negated_conjecture,
    ( ~ r1_tsep_1(sK0,sK0)
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | r1_tsep_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1))
    | ~ l1_struct_0(sK0) )).

cnf(u190,negated_conjecture,
    ( ~ r1_tsep_1(sK0,sK0)
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK2))
    | r1_tsep_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK2))
    | ~ l1_struct_0(sK0) )).

cnf(u192,negated_conjecture,
    ( ~ r1_tsep_1(sK0,sK0)
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK2))
    | r1_tsep_1(k8_tmap_1(sK0,sK2),k8_tmap_1(sK0,sK1))
    | ~ l1_struct_0(sK0) )).

cnf(u194,negated_conjecture,
    ( ~ r1_tsep_1(sK0,sK0)
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | r1_tsep_1(k8_tmap_1(sK0,sK2),k8_tmap_1(sK0,sK1))
    | ~ l1_struct_0(sK0) )).

cnf(u196,negated_conjecture,
    ( ~ r1_tsep_1(sK0,sK0)
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK2))
    | r1_tsep_1(k8_tmap_1(sK0,sK2),k8_tmap_1(sK0,sK2))
    | ~ l1_struct_0(sK0) )).

cnf(u198,negated_conjecture,
    ( ~ r1_tsep_1(sK0,sK0)
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | r1_tsep_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK2))
    | ~ l1_struct_0(sK0) )).

cnf(u156,negated_conjecture,
    ( ~ r1_tsep_1(sK0,X0)
    | ~ l1_pre_topc(X0)
    | r1_tsep_1(k8_tmap_1(sK0,sK1),X0)
    | ~ l1_struct_0(sK0) )).

cnf(u176,negated_conjecture,
    ( ~ r1_tsep_1(sK0,X0)
    | ~ l1_pre_topc(X0)
    | r1_tsep_1(k8_tmap_1(sK0,sK2),X0)
    | ~ l1_struct_0(sK0) )).

cnf(u135,negated_conjecture,
    ( ~ r1_tsep_1(k8_tmap_1(sK0,sK2),X0)
    | r1_xboole_0(u1_struct_0(sK0),u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(k8_tmap_1(sK0,sK2)) )).

cnf(u127,negated_conjecture,
    ( ~ r1_tsep_1(k8_tmap_1(sK0,sK1),X0)
    | r1_xboole_0(u1_struct_0(sK0),u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(k8_tmap_1(sK0,sK1)) )).

cnf(u166,negated_conjecture,
    ( ~ r1_tsep_1(X0,sK0)
    | ~ l1_pre_topc(X0)
    | r1_tsep_1(X0,k8_tmap_1(sK0,sK1))
    | ~ l1_struct_0(sK0) )).

cnf(u186,negated_conjecture,
    ( ~ r1_tsep_1(X0,sK0)
    | ~ l1_pre_topc(X0)
    | r1_tsep_1(X0,k8_tmap_1(sK0,sK2))
    | ~ l1_struct_0(sK0) )).

cnf(u136,negated_conjecture,
    ( ~ r1_tsep_1(X1,k8_tmap_1(sK0,sK2))
    | r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK0))
    | ~ l1_struct_0(k8_tmap_1(sK0,sK2))
    | ~ l1_struct_0(X1) )).

cnf(u128,negated_conjecture,
    ( ~ r1_tsep_1(X1,k8_tmap_1(sK0,sK1))
    | r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK0))
    | ~ l1_struct_0(k8_tmap_1(sK0,sK1))
    | ~ l1_struct_0(X1) )).

cnf(u101,axiom,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X1,X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) )).

cnf(u79,axiom,
    ( v1_pre_topc(k8_tmap_1(X0,X1))
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0) )).

cnf(u72,axiom,
    ( ~ v1_pre_topc(X2)
    | u1_struct_0(X1) = sK4(X0,X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | k8_tmap_1(X0,X1) = X2
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0) )).

cnf(u71,axiom,
    ( ~ v1_pre_topc(X2)
    | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | k8_tmap_1(X0,X1) = X2
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0) )).

cnf(u80,axiom,
    ( v2_pre_topc(k8_tmap_1(X0,X1))
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0) )).

cnf(u55,negated_conjecture,
    ( v2_pre_topc(sK0) )).

cnf(u314,negated_conjecture,
    ( ~ v2_pre_topc(X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | k8_tmap_1(X0,X1) = k8_tmap_1(sK0,X2)
    | v2_struct_0(X0)
    | ~ m1_pre_topc(X2,sK0)
    | m1_subset_1(sK4(X0,X1,k8_tmap_1(sK0,X2)),k1_zfmisc_1(u1_struct_0(X0))) )).

cnf(u284,negated_conjecture,
    ( ~ v2_pre_topc(X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | k8_tmap_1(X0,X1) = k8_tmap_1(sK0,X2)
    | v2_struct_0(X0)
    | ~ m1_pre_topc(X2,sK0)
    | u1_struct_0(X1) = sK4(X0,X1,k8_tmap_1(sK0,X2)) )).

cnf(u273,axiom,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0) )).

cnf(u270,axiom,
    ( ~ v2_pre_topc(X2)
    | k8_tmap_1(X0,X1) = k8_tmap_1(X2,X3)
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2)
    | m1_subset_1(sK4(X0,X1,k8_tmap_1(X2,X3)),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X2) )).

cnf(u256,axiom,
    ( ~ v2_pre_topc(X2)
    | k8_tmap_1(X1,X0) = k8_tmap_1(X2,X3)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X0) = sK4(X1,X0,k8_tmap_1(X2,X3))
    | v2_struct_0(X2) )).

cnf(u110,axiom,
    ( ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,u1_struct_0(X1))
    | v2_struct_0(X0)
    | ~ m1_pre_topc(X1,X0) )).

cnf(u94,axiom,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ m1_pre_topc(X1,X0)
    | u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1)) )).

cnf(u84,axiom,
    ( ~ v2_pre_topc(X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | v2_struct_0(X0) )).

cnf(u83,axiom,
    ( ~ v2_pre_topc(X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | v2_struct_0(X0) )).

cnf(u77,axiom,
    ( ~ v2_pre_topc(X0)
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))
    | v2_struct_0(X0) )).

cnf(u76,axiom,
    ( ~ v2_pre_topc(X0)
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0))
    | v2_struct_0(X0) )).

cnf(u75,axiom,
    ( ~ v2_pre_topc(X0)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ r1_xboole_0(u1_struct_0(X2),X1)
    | ~ m1_pre_topc(X2,X0)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
    | v2_struct_0(X0) )).

cnf(u92,axiom,
    ( r1_funct_2(X0,X1,X2,X3,X5,X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_2(X5,X2,X3)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(X5,X0,X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X1) )).

cnf(u267,negated_conjecture,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK2),k3_struct_0(sK0)) )).

cnf(u265,negated_conjecture,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k3_struct_0(sK0)) )).

cnf(u260,negated_conjecture,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0)),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,X0),k3_struct_0(sK0))
    | v2_struct_0(X0)
    | ~ m1_pre_topc(X0,sK0) )).

cnf(u369,axiom,
    ( ~ r1_funct_2(X4,X5,X2,X3,k9_tmap_1(X6,X7),k9_tmap_1(X0,X1))
    | ~ v1_funct_2(k9_tmap_1(X0,X1),X2,X3)
    | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(k9_tmap_1(X6,X7),k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_2(k9_tmap_1(X6,X7),X4,X5)
    | k9_tmap_1(X0,X1) = k9_tmap_1(X6,X7)
    | v1_xboole_0(X3)
    | v1_xboole_0(X5)
    | ~ m1_pre_topc(X7,X6)
    | ~ l1_pre_topc(X6)
    | ~ v2_pre_topc(X6)
    | v2_struct_0(X6)
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0) )).

cnf(u338,negated_conjecture,
    ( m1_subset_1(sK4(sK0,sK1,k8_tmap_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | k8_tmap_1(sK0,sK1) = k8_tmap_1(sK0,sK2) )).

cnf(u324,negated_conjecture,
    ( m1_subset_1(sK4(sK0,sK2,k8_tmap_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | k8_tmap_1(sK0,sK1) = k8_tmap_1(sK0,sK2) )).

cnf(u62,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) )).

cnf(u225,negated_conjecture,
    ( m1_subset_1(k9_tmap_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )).

cnf(u224,negated_conjecture,
    ( m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )).

cnf(u220,negated_conjecture,
    ( m1_subset_1(k9_tmap_1(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0)))))
    | ~ m1_pre_topc(X0,sK0) )).

cnf(u344,negated_conjecture,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k8_tmap_1(sK0,sK1) = k8_tmap_1(sK0,sK2) )).

cnf(u329,negated_conjecture,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | k8_tmap_1(sK0,sK1) = k8_tmap_1(sK0,sK2) )).

cnf(u68,axiom,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0) )).

cnf(u361,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ r1_xboole_0(u1_struct_0(sK1),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tmap_1(sK1,k6_tmap_1(sK0,X0),k2_tmap_1(sK0,k6_tmap_1(sK0,X0),k7_tmap_1(sK0,X0),sK1),X1) )).

cnf(u235,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK1),X0)
    | v2_struct_0(k8_tmap_1(sK0,sK1)) )).

cnf(u249,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK2),X0)
    | v2_struct_0(k8_tmap_1(sK0,sK2)) )).

cnf(u74,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0) )).

cnf(u207,negated_conjecture,
    ( v1_funct_2(k9_tmap_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0)) )).

cnf(u206,negated_conjecture,
    ( v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) )).

cnf(u202,negated_conjecture,
    ( v1_funct_2(k9_tmap_1(sK0,X0),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0)))
    | ~ m1_pre_topc(X0,sK0) )).

cnf(u82,axiom,
    ( v1_funct_1(k9_tmap_1(X0,X1))
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0) )).

cnf(u86,axiom,
    ( ~ v1_funct_1(X4)
    | ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_2(X5,X2,X3)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(X4,X0,X1)
    | X4 = X5
    | v1_xboole_0(X3)
    | v1_xboole_0(X1) )).

cnf(u353,axiom,
    ( ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_2(X6,X2,X3)
    | ~ r1_funct_2(X0,X1,X2,X3,k9_tmap_1(X4,X5),X6)
    | ~ m1_subset_1(k9_tmap_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(k9_tmap_1(X4,X5),X0,X1)
    | k9_tmap_1(X4,X5) = X6
    | v1_xboole_0(X3)
    | v1_xboole_0(X1)
    | ~ m1_pre_topc(X5,X4)
    | ~ l1_pre_topc(X4)
    | ~ v2_pre_topc(X4)
    | v2_struct_0(X4) )).

cnf(u133,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(k8_tmap_1(sK0,sK1))
    | v2_struct_0(k8_tmap_1(sK0,sK1)) )).

cnf(u141,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(k8_tmap_1(sK0,sK2))
    | v2_struct_0(k8_tmap_1(sK0,sK2)) )).

cnf(u69,axiom,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) )).

cnf(u252,negated_conjecture,
    ( v2_struct_0(k8_tmap_1(sK0,sK2))
    | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK2),u1_struct_0(sK1)) )).

cnf(u253,negated_conjecture,
    ( v2_struct_0(k8_tmap_1(sK0,sK2))
    | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK2),u1_struct_0(sK2)) )).

cnf(u325,negated_conjecture,
    ( v2_struct_0(k8_tmap_1(sK0,sK2))
    | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK2),sK4(sK0,sK2,k8_tmap_1(sK0,sK1)))
    | k8_tmap_1(sK0,sK1) = k8_tmap_1(sK0,sK2) )).

cnf(u340,negated_conjecture,
    ( v2_struct_0(k8_tmap_1(sK0,sK2))
    | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK2),sK4(sK0,sK1,k8_tmap_1(sK0,sK2)))
    | k8_tmap_1(sK0,sK1) = k8_tmap_1(sK0,sK2) )).

cnf(u238,negated_conjecture,
    ( v2_struct_0(k8_tmap_1(sK0,sK1))
    | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(sK1)) )).

cnf(u239,negated_conjecture,
    ( v2_struct_0(k8_tmap_1(sK0,sK1))
    | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(sK2)) )).

cnf(u326,negated_conjecture,
    ( v2_struct_0(k8_tmap_1(sK0,sK1))
    | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK1),sK4(sK0,sK2,k8_tmap_1(sK0,sK1)))
    | k8_tmap_1(sK0,sK1) = k8_tmap_1(sK0,sK2) )).

cnf(u341,negated_conjecture,
    ( v2_struct_0(k8_tmap_1(sK0,sK1))
    | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK1),sK4(sK0,sK1,k8_tmap_1(sK0,sK2)))
    | k8_tmap_1(sK0,sK1) = k8_tmap_1(sK0,sK2) )).

cnf(u59,negated_conjecture,
    ( ~ v2_struct_0(sK2) )).

cnf(u57,negated_conjecture,
    ( ~ v2_struct_0(sK1) )).

cnf(u54,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u60,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) )).

cnf(u58,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) )).

cnf(u140,negated_conjecture,
    ( ~ m1_pre_topc(k8_tmap_1(sK0,sK2),X5)
    | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5)))
    | ~ l1_pre_topc(X5) )).

cnf(u132,negated_conjecture,
    ( ~ m1_pre_topc(k8_tmap_1(sK0,sK1),X5)
    | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5)))
    | ~ l1_pre_topc(X5) )).

cnf(u99,negated_conjecture,
    ( ~ m1_pre_topc(X0,sK2)
    | l1_pre_topc(X0) )).

cnf(u98,negated_conjecture,
    ( ~ m1_pre_topc(X0,sK1)
    | l1_pre_topc(X0) )).

cnf(u357,negated_conjecture,
    ( ~ m1_pre_topc(X1,sK0)
    | ~ r1_xboole_0(u1_struct_0(X1),X2)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tmap_1(X1,k6_tmap_1(sK0,X2),k2_tmap_1(sK0,k6_tmap_1(sK0,X2),k7_tmap_1(sK0,X2),X1),X0) )).

cnf(u322,negated_conjecture,
    ( ~ m1_pre_topc(X1,sK0)
    | k8_tmap_1(sK0,X1) = k8_tmap_1(sK0,sK2)
    | m1_subset_1(sK4(sK0,X1,k8_tmap_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u321,negated_conjecture,
    ( ~ m1_pre_topc(X0,sK0)
    | k8_tmap_1(sK0,sK1) = k8_tmap_1(sK0,X0)
    | m1_subset_1(sK4(sK0,X0,k8_tmap_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u319,negated_conjecture,
    ( ~ m1_pre_topc(X1,sK0)
    | k8_tmap_1(sK0,X1) = k8_tmap_1(sK0,X0)
    | ~ m1_pre_topc(X0,sK0)
    | m1_subset_1(sK4(sK0,X0,k8_tmap_1(sK0,X1)),k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u292,negated_conjecture,
    ( ~ m1_pre_topc(X1,sK0)
    | k8_tmap_1(sK0,X1) = k8_tmap_1(sK0,sK2)
    | u1_struct_0(X1) = sK4(sK0,X1,k8_tmap_1(sK0,sK2)) )).

cnf(u291,negated_conjecture,
    ( ~ m1_pre_topc(X0,sK0)
    | k8_tmap_1(sK0,sK1) = k8_tmap_1(sK0,X0)
    | u1_struct_0(X0) = sK4(sK0,X0,k8_tmap_1(sK0,sK1)) )).

cnf(u289,negated_conjecture,
    ( ~ m1_pre_topc(X1,sK0)
    | k8_tmap_1(sK0,X1) = k8_tmap_1(sK0,X0)
    | ~ m1_pre_topc(X0,sK0)
    | u1_struct_0(X0) = sK4(sK0,X0,k8_tmap_1(sK0,X1)) )).

cnf(u277,negated_conjecture,
    ( ~ m1_pre_topc(X0,sK0)
    | k8_tmap_1(sK0,X0) = k6_tmap_1(sK0,u1_struct_0(X0)) )).

cnf(u251,negated_conjecture,
    ( ~ m1_pre_topc(X0,sK0)
    | v2_struct_0(k8_tmap_1(sK0,sK2))
    | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK2),u1_struct_0(X0)) )).

cnf(u237,negated_conjecture,
    ( ~ m1_pre_topc(X0,sK0)
    | v2_struct_0(k8_tmap_1(sK0,sK1))
    | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(X0)) )).

cnf(u211,negated_conjecture,
    ( ~ m1_pre_topc(X0,sK0)
    | v2_struct_0(X0)
    | u1_pre_topc(k8_tmap_1(sK0,X0)) = k5_tmap_1(sK0,u1_struct_0(X0)) )).

cnf(u121,negated_conjecture,
    ( ~ m1_pre_topc(X0,sK0)
    | v2_struct_0(X0)
    | u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,X0)) )).

cnf(u114,negated_conjecture,
    ( ~ m1_pre_topc(X0,sK0)
    | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(X0)) )).

cnf(u95,negated_conjecture,
    ( ~ m1_pre_topc(X0,sK0)
    | l1_pre_topc(X0) )).

cnf(u139,negated_conjecture,
    ( ~ m1_pre_topc(X4,k8_tmap_1(sK0,sK2))
    | m1_subset_1(u1_struct_0(X4),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK2)) )).

cnf(u131,negated_conjecture,
    ( ~ m1_pre_topc(X4,k8_tmap_1(sK0,sK1))
    | m1_subset_1(u1_struct_0(X4),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1)) )).

cnf(u358,axiom,
    ( ~ m1_pre_topc(X4,k8_tmap_1(X6,X7))
    | ~ r1_xboole_0(u1_struct_0(X4),X5)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | v2_struct_0(X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k8_tmap_1(X6,X7))))
    | r1_tmap_1(X4,k6_tmap_1(k8_tmap_1(X6,X7),X5),k2_tmap_1(k8_tmap_1(X6,X7),k6_tmap_1(k8_tmap_1(X6,X7),X5),k7_tmap_1(k8_tmap_1(X6,X7),X5),X4),X3)
    | v2_struct_0(k8_tmap_1(X6,X7))
    | ~ m1_pre_topc(X7,X6)
    | ~ l1_pre_topc(X6)
    | ~ v2_pre_topc(X6)
    | v2_struct_0(X6) )).

cnf(u320,negated_conjecture,
    ( ~ m1_pre_topc(X2,k8_tmap_1(X3,X4))
    | k8_tmap_1(k8_tmap_1(X3,X4),X2) = k8_tmap_1(sK0,X5)
    | v2_struct_0(k8_tmap_1(X3,X4))
    | ~ m1_pre_topc(X5,sK0)
    | m1_subset_1(sK4(k8_tmap_1(X3,X4),X2,k8_tmap_1(sK0,X5)),k1_zfmisc_1(u1_struct_0(k8_tmap_1(X3,X4))))
    | ~ m1_pre_topc(X4,X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X3)
    | v2_struct_0(X3) )).

cnf(u315,axiom,
    ( ~ m1_pre_topc(X7,k8_tmap_1(X5,X6))
    | ~ m1_pre_topc(X4,X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X3)
    | v2_struct_0(X3)
    | k8_tmap_1(X3,X4) = k8_tmap_1(k8_tmap_1(X5,X6),X7)
    | m1_subset_1(sK4(X3,X4,k8_tmap_1(k8_tmap_1(X5,X6),X7)),k1_zfmisc_1(u1_struct_0(X3)))
    | v2_struct_0(k8_tmap_1(X5,X6))
    | ~ m1_pre_topc(X6,X5)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X5)
    | v2_struct_0(X5) )).

cnf(u290,negated_conjecture,
    ( ~ m1_pre_topc(X2,k8_tmap_1(X3,X4))
    | k8_tmap_1(k8_tmap_1(X3,X4),X2) = k8_tmap_1(sK0,X5)
    | v2_struct_0(k8_tmap_1(X3,X4))
    | ~ m1_pre_topc(X5,sK0)
    | u1_struct_0(X2) = sK4(k8_tmap_1(X3,X4),X2,k8_tmap_1(sK0,X5))
    | ~ m1_pre_topc(X4,X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X3)
    | v2_struct_0(X3) )).

cnf(u285,axiom,
    ( ~ m1_pre_topc(X7,k8_tmap_1(X5,X6))
    | ~ m1_pre_topc(X4,X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X3)
    | v2_struct_0(X3)
    | k8_tmap_1(X3,X4) = k8_tmap_1(k8_tmap_1(X5,X6),X7)
    | u1_struct_0(X4) = sK4(X3,X4,k8_tmap_1(k8_tmap_1(X5,X6),X7))
    | v2_struct_0(k8_tmap_1(X5,X6))
    | ~ m1_pre_topc(X6,X5)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X5)
    | v2_struct_0(X5) )).

cnf(u278,axiom,
    ( ~ m1_pre_topc(X3,k8_tmap_1(X1,X2))
    | k8_tmap_1(k8_tmap_1(X1,X2),X3) = k6_tmap_1(k8_tmap_1(X1,X2),u1_struct_0(X3))
    | v2_struct_0(k8_tmap_1(X1,X2))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1) )).

cnf(u261,axiom,
    ( ~ m1_pre_topc(X1,k8_tmap_1(X2,X3))
    | v2_struct_0(X1)
    | r1_funct_2(u1_struct_0(k8_tmap_1(X2,X3)),u1_struct_0(k8_tmap_1(k8_tmap_1(X2,X3),X1)),u1_struct_0(k8_tmap_1(X2,X3)),u1_struct_0(k8_tmap_1(X2,X3)),k9_tmap_1(k8_tmap_1(X2,X3),X1),k3_struct_0(k8_tmap_1(X2,X3)))
    | v2_struct_0(k8_tmap_1(X2,X3))
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X2) )).

cnf(u221,axiom,
    ( ~ m1_pre_topc(X1,k8_tmap_1(X2,X3))
    | m1_subset_1(k9_tmap_1(k8_tmap_1(X2,X3),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k8_tmap_1(X2,X3)),u1_struct_0(k8_tmap_1(k8_tmap_1(X2,X3),X1)))))
    | v2_struct_0(k8_tmap_1(X2,X3))
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X2) )).

cnf(u212,axiom,
    ( ~ m1_pre_topc(X1,k8_tmap_1(X2,X3))
    | v2_struct_0(k8_tmap_1(X2,X3))
    | v2_struct_0(X1)
    | u1_pre_topc(k8_tmap_1(k8_tmap_1(X2,X3),X1)) = k5_tmap_1(k8_tmap_1(X2,X3),u1_struct_0(X1))
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X2) )).

cnf(u203,axiom,
    ( ~ m1_pre_topc(X1,k8_tmap_1(X2,X3))
    | v1_funct_2(k9_tmap_1(k8_tmap_1(X2,X3),X1),u1_struct_0(k8_tmap_1(X2,X3)),u1_struct_0(k8_tmap_1(k8_tmap_1(X2,X3),X1)))
    | v2_struct_0(k8_tmap_1(X2,X3))
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X2) )).

cnf(u122,axiom,
    ( ~ m1_pre_topc(X1,k8_tmap_1(X2,X3))
    | v2_struct_0(X1)
    | u1_struct_0(k8_tmap_1(X2,X3)) = u1_struct_0(k8_tmap_1(k8_tmap_1(X2,X3),X1))
    | v2_struct_0(k8_tmap_1(X2,X3))
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X2) )).

cnf(u115,axiom,
    ( ~ m1_pre_topc(X3,k8_tmap_1(X1,X2))
    | v2_struct_0(k8_tmap_1(X1,X2))
    | k6_partfun1(u1_struct_0(k8_tmap_1(X1,X2))) = k7_tmap_1(k8_tmap_1(X1,X2),u1_struct_0(X3))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1) )).

cnf(u108,axiom,
    ( ~ m1_pre_topc(X2,k8_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X0,X1)
    | l1_pre_topc(X2) )).

cnf(u66,axiom,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) )).

cnf(u85,axiom,
    ( ~ l1_struct_0(X0)
    | ~ r1_tsep_1(X0,X1)
    | ~ l1_struct_0(X1)
    | r1_tsep_1(X1,X0) )).

cnf(u100,axiom,
    ( ~ l1_struct_0(X1)
    | ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X1,X0)
    | ~ l1_pre_topc(X0) )).

cnf(u151,negated_conjecture,
    ( ~ l1_struct_0(X0)
    | ~ r1_xboole_0(u1_struct_0(sK0),u1_struct_0(X0))
    | r1_tsep_1(k8_tmap_1(sK0,sK1),X0) )).

cnf(u161,negated_conjecture,
    ( ~ l1_struct_0(X0)
    | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK0))
    | r1_tsep_1(X0,k8_tmap_1(sK0,sK1)) )).

cnf(u171,negated_conjecture,
    ( ~ l1_struct_0(X0)
    | ~ r1_xboole_0(u1_struct_0(sK0),u1_struct_0(X0))
    | r1_tsep_1(k8_tmap_1(sK0,sK2),X0) )).

cnf(u181,negated_conjecture,
    ( ~ l1_struct_0(X0)
    | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK0))
    | r1_tsep_1(X0,k8_tmap_1(sK0,sK2)) )).

cnf(u97,negated_conjecture,
    ( l1_pre_topc(sK2) )).

cnf(u96,negated_conjecture,
    ( l1_pre_topc(sK1) )).

cnf(u56,negated_conjecture,
    ( l1_pre_topc(sK0) )).

cnf(u81,axiom,
    ( l1_pre_topc(k8_tmap_1(X0,X1))
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0) )).

cnf(u67,axiom,
    ( ~ l1_pre_topc(X0)
    | ~ m1_pre_topc(X1,X0)
    | l1_pre_topc(X1) )).

cnf(u302,negated_conjecture,
    ( u1_struct_0(sK1) = sK4(sK0,sK1,k8_tmap_1(sK0,sK2))
    | k8_tmap_1(sK0,sK1) = k8_tmap_1(sK0,sK2) )).

cnf(u294,negated_conjecture,
    ( u1_struct_0(sK2) = sK4(sK0,sK2,k8_tmap_1(sK0,sK1))
    | k8_tmap_1(sK0,sK1) = k8_tmap_1(sK0,sK2) )).

cnf(u216,negated_conjecture,
    ( u1_pre_topc(k8_tmap_1(sK0,sK2)) = k5_tmap_1(sK0,u1_struct_0(sK2)) )).

cnf(u215,negated_conjecture,
    ( u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1)) )).

cnf(u280,negated_conjecture,
    ( k8_tmap_1(sK0,sK2) = k6_tmap_1(sK0,u1_struct_0(sK2)) )).

cnf(u279,negated_conjecture,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) )).

cnf(u347,negated_conjecture,
    ( k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,sK4(sK0,sK1,k8_tmap_1(sK0,sK2)))
    | k8_tmap_1(sK0,sK1) = k8_tmap_1(sK0,sK2) )).

cnf(u332,negated_conjecture,
    ( k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,sK4(sK0,sK2,k8_tmap_1(sK0,sK1)))
    | k8_tmap_1(sK0,sK1) = k8_tmap_1(sK0,sK2) )).

cnf(u117,negated_conjecture,
    ( k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK2)) )).

cnf(u116,negated_conjecture,
    ( k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK1)) )).

cnf(u126,negated_conjecture,
    ( u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK2)) )).

cnf(u125,negated_conjecture,
    ( u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) )).

cnf(u73,axiom,
    ( k6_tmap_1(X0,sK4(X0,X1,X2)) != X2
    | k8_tmap_1(X0,X1) = X2
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ v1_pre_topc(X2)
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:32:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (2330)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.47  % (2320)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.48  % (2339)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.48  % (2323)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.49  % (2327)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.49  % (2336)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.49  % (2323)Refutation not found, incomplete strategy% (2323)------------------------------
% 0.21/0.49  % (2323)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (2323)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (2323)Memory used [KB]: 6268
% 0.21/0.49  % (2323)Time elapsed: 0.010 s
% 0.21/0.49  % (2323)------------------------------
% 0.21/0.49  % (2323)------------------------------
% 0.21/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.50  % (2339)# SZS output start Saturation.
% 0.21/0.50  cnf(u368,negated_conjecture,
% 0.21/0.50      r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),X0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(sK1) | ~m1_subset_1(X0,u1_struct_0(sK2))).
% 0.21/0.50  
% 0.21/0.50  cnf(u63,negated_conjecture,
% 0.21/0.50      ~r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK3)).
% 0.21/0.50  
% 0.21/0.50  cnf(u64,axiom,
% 0.21/0.50      r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u362,negated_conjecture,
% 0.21/0.50      ~r1_xboole_0(u1_struct_0(sK2),X2) | ~m1_subset_1(X3,u1_struct_0(sK2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tmap_1(sK2,k6_tmap_1(sK0,X2),k2_tmap_1(sK0,k6_tmap_1(sK0,X2),k7_tmap_1(sK0,X2),sK2),X3)).
% 0.21/0.50  
% 0.21/0.50  cnf(u154,negated_conjecture,
% 0.21/0.50      ~r1_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)) | r1_tsep_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(k8_tmap_1(sK0,sK1))).
% 0.21/0.50  
% 0.21/0.50  cnf(u155,negated_conjecture,
% 0.21/0.50      ~r1_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)) | r1_tsep_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK2)) | ~l1_pre_topc(k8_tmap_1(sK0,sK2))).
% 0.21/0.50  
% 0.21/0.50  cnf(u165,negated_conjecture,
% 0.21/0.50      ~r1_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)) | r1_tsep_1(k8_tmap_1(sK0,sK2),k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(k8_tmap_1(sK0,sK2))).
% 0.21/0.50  
% 0.21/0.50  cnf(u174,negated_conjecture,
% 0.21/0.50      ~r1_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)) | r1_tsep_1(k8_tmap_1(sK0,sK2),k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(k8_tmap_1(sK0,sK1))).
% 0.21/0.50  
% 0.21/0.50  cnf(u175,negated_conjecture,
% 0.21/0.50      ~r1_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)) | r1_tsep_1(k8_tmap_1(sK0,sK2),k8_tmap_1(sK0,sK2)) | ~l1_pre_topc(k8_tmap_1(sK0,sK2))).
% 0.21/0.50  
% 0.21/0.50  cnf(u184,negated_conjecture,
% 0.21/0.50      ~r1_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)) | r1_tsep_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK2)) | ~l1_pre_topc(k8_tmap_1(sK0,sK1))).
% 0.21/0.50  
% 0.21/0.50  cnf(u152,negated_conjecture,
% 0.21/0.50      ~r1_xboole_0(u1_struct_0(sK0),u1_struct_0(X0)) | r1_tsep_1(k8_tmap_1(sK0,sK1),X0) | ~l1_pre_topc(X0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u172,negated_conjecture,
% 0.21/0.50      ~r1_xboole_0(u1_struct_0(sK0),u1_struct_0(X0)) | r1_tsep_1(k8_tmap_1(sK0,sK2),X0) | ~l1_pre_topc(X0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u162,negated_conjecture,
% 0.21/0.50      ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK0)) | r1_tsep_1(X0,k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(X0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u182,negated_conjecture,
% 0.21/0.50      ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK0)) | r1_tsep_1(X0,k8_tmap_1(sK0,sK2)) | ~l1_pre_topc(X0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u65,axiom,
% 0.21/0.50      ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u104,negated_conjecture,
% 0.21/0.50      r1_tsep_1(sK2,sK1)).
% 0.21/0.50  
% 0.21/0.50  cnf(u61,negated_conjecture,
% 0.21/0.50      r1_tsep_1(sK1,sK2)).
% 0.21/0.50  
% 0.21/0.50  cnf(u365,negated_conjecture,
% 0.21/0.50      ~r1_tsep_1(sK2,X0) | r1_tmap_1(sK2,k6_tmap_1(sK0,u1_struct_0(X0)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(X0)),k7_tmap_1(sK0,u1_struct_0(X0)),sK2),X1) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK2))).
% 0.21/0.50  
% 0.21/0.50  cnf(u188,negated_conjecture,
% 0.21/0.50      ~r1_tsep_1(sK0,sK0) | ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | r1_tsep_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1)) | ~l1_struct_0(sK0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u190,negated_conjecture,
% 0.21/0.50      ~r1_tsep_1(sK0,sK0) | ~l1_pre_topc(k8_tmap_1(sK0,sK2)) | r1_tsep_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK2)) | ~l1_struct_0(sK0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u192,negated_conjecture,
% 0.21/0.50      ~r1_tsep_1(sK0,sK0) | ~l1_pre_topc(k8_tmap_1(sK0,sK2)) | r1_tsep_1(k8_tmap_1(sK0,sK2),k8_tmap_1(sK0,sK1)) | ~l1_struct_0(sK0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u194,negated_conjecture,
% 0.21/0.50      ~r1_tsep_1(sK0,sK0) | ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | r1_tsep_1(k8_tmap_1(sK0,sK2),k8_tmap_1(sK0,sK1)) | ~l1_struct_0(sK0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u196,negated_conjecture,
% 0.21/0.50      ~r1_tsep_1(sK0,sK0) | ~l1_pre_topc(k8_tmap_1(sK0,sK2)) | r1_tsep_1(k8_tmap_1(sK0,sK2),k8_tmap_1(sK0,sK2)) | ~l1_struct_0(sK0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u198,negated_conjecture,
% 0.21/0.50      ~r1_tsep_1(sK0,sK0) | ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | r1_tsep_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK2)) | ~l1_struct_0(sK0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u156,negated_conjecture,
% 0.21/0.50      ~r1_tsep_1(sK0,X0) | ~l1_pre_topc(X0) | r1_tsep_1(k8_tmap_1(sK0,sK1),X0) | ~l1_struct_0(sK0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u176,negated_conjecture,
% 0.21/0.50      ~r1_tsep_1(sK0,X0) | ~l1_pre_topc(X0) | r1_tsep_1(k8_tmap_1(sK0,sK2),X0) | ~l1_struct_0(sK0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u135,negated_conjecture,
% 0.21/0.50      ~r1_tsep_1(k8_tmap_1(sK0,sK2),X0) | r1_xboole_0(u1_struct_0(sK0),u1_struct_0(X0)) | ~l1_struct_0(X0) | ~l1_struct_0(k8_tmap_1(sK0,sK2))).
% 0.21/0.50  
% 0.21/0.50  cnf(u127,negated_conjecture,
% 0.21/0.50      ~r1_tsep_1(k8_tmap_1(sK0,sK1),X0) | r1_xboole_0(u1_struct_0(sK0),u1_struct_0(X0)) | ~l1_struct_0(X0) | ~l1_struct_0(k8_tmap_1(sK0,sK1))).
% 0.21/0.50  
% 0.21/0.50  cnf(u166,negated_conjecture,
% 0.21/0.50      ~r1_tsep_1(X0,sK0) | ~l1_pre_topc(X0) | r1_tsep_1(X0,k8_tmap_1(sK0,sK1)) | ~l1_struct_0(sK0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u186,negated_conjecture,
% 0.21/0.50      ~r1_tsep_1(X0,sK0) | ~l1_pre_topc(X0) | r1_tsep_1(X0,k8_tmap_1(sK0,sK2)) | ~l1_struct_0(sK0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u136,negated_conjecture,
% 0.21/0.50      ~r1_tsep_1(X1,k8_tmap_1(sK0,sK2)) | r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK0)) | ~l1_struct_0(k8_tmap_1(sK0,sK2)) | ~l1_struct_0(X1)).
% 0.21/0.50  
% 0.21/0.50  cnf(u128,negated_conjecture,
% 0.21/0.50      ~r1_tsep_1(X1,k8_tmap_1(sK0,sK1)) | r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK0)) | ~l1_struct_0(k8_tmap_1(sK0,sK1)) | ~l1_struct_0(X1)).
% 0.21/0.50  
% 0.21/0.50  cnf(u101,axiom,
% 0.21/0.50      ~r1_tsep_1(X0,X1) | r1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1)).
% 0.21/0.50  
% 0.21/0.50  cnf(u79,axiom,
% 0.21/0.50      v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u72,axiom,
% 0.21/0.50      ~v1_pre_topc(X2) | u1_struct_0(X1) = sK4(X0,X1,X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | k8_tmap_1(X0,X1) = X2 | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u71,axiom,
% 0.21/0.50      ~v1_pre_topc(X2) | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | k8_tmap_1(X0,X1) = X2 | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u80,axiom,
% 0.21/0.50      v2_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u55,negated_conjecture,
% 0.21/0.50      v2_pre_topc(sK0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u314,negated_conjecture,
% 0.21/0.50      ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | k8_tmap_1(X0,X1) = k8_tmap_1(sK0,X2) | v2_struct_0(X0) | ~m1_pre_topc(X2,sK0) | m1_subset_1(sK4(X0,X1,k8_tmap_1(sK0,X2)),k1_zfmisc_1(u1_struct_0(X0)))).
% 0.21/0.50  
% 0.21/0.50  cnf(u284,negated_conjecture,
% 0.21/0.50      ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | k8_tmap_1(X0,X1) = k8_tmap_1(sK0,X2) | v2_struct_0(X0) | ~m1_pre_topc(X2,sK0) | u1_struct_0(X1) = sK4(X0,X1,k8_tmap_1(sK0,X2))).
% 0.21/0.50  
% 0.21/0.50  cnf(u273,axiom,
% 0.21/0.50      ~v2_pre_topc(X0) | v2_struct_0(X0) | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u270,axiom,
% 0.21/0.50      ~v2_pre_topc(X2) | k8_tmap_1(X0,X1) = k8_tmap_1(X2,X3) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X3,X2) | ~l1_pre_topc(X2) | m1_subset_1(sK4(X0,X1,k8_tmap_1(X2,X3)),k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X2)).
% 0.21/0.50  
% 0.21/0.50  cnf(u256,axiom,
% 0.21/0.50      ~v2_pre_topc(X2) | k8_tmap_1(X1,X0) = k8_tmap_1(X2,X3) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~m1_pre_topc(X3,X2) | ~l1_pre_topc(X2) | u1_struct_0(X0) = sK4(X1,X0,k8_tmap_1(X2,X3)) | v2_struct_0(X2)).
% 0.21/0.50  
% 0.21/0.50  cnf(u110,axiom,
% 0.21/0.50      ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,u1_struct_0(X1)) | v2_struct_0(X0) | ~m1_pre_topc(X1,X0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u94,axiom,
% 0.21/0.50      ~v2_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1))).
% 0.21/0.50  
% 0.21/0.50  cnf(u84,axiom,
% 0.21/0.50      ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | v2_struct_0(X0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u83,axiom,
% 0.21/0.50      ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | v2_struct_0(X0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u77,axiom,
% 0.21/0.50      ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) | v2_struct_0(X0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u76,axiom,
% 0.21/0.50      ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0)) | v2_struct_0(X0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u75,axiom,
% 0.21/0.50      ~v2_pre_topc(X0) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~r1_xboole_0(u1_struct_0(X2),X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | v2_struct_0(X0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u92,axiom,
% 0.21/0.50      r1_funct_2(X0,X1,X2,X3,X5,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X5,X0,X1) | v1_xboole_0(X3) | v1_xboole_0(X1)).
% 0.21/0.50  
% 0.21/0.50  cnf(u267,negated_conjecture,
% 0.21/0.50      r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK2),k3_struct_0(sK0))).
% 0.21/0.50  
% 0.21/0.50  cnf(u265,negated_conjecture,
% 0.21/0.50      r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k3_struct_0(sK0))).
% 0.21/0.50  
% 0.21/0.50  cnf(u260,negated_conjecture,
% 0.21/0.50      r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0)),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,X0),k3_struct_0(sK0)) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u369,axiom,
% 0.21/0.50      ~r1_funct_2(X4,X5,X2,X3,k9_tmap_1(X6,X7),k9_tmap_1(X0,X1)) | ~v1_funct_2(k9_tmap_1(X0,X1),X2,X3) | ~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(k9_tmap_1(X6,X7),k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_2(k9_tmap_1(X6,X7),X4,X5) | k9_tmap_1(X0,X1) = k9_tmap_1(X6,X7) | v1_xboole_0(X3) | v1_xboole_0(X5) | ~m1_pre_topc(X7,X6) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u338,negated_conjecture,
% 0.21/0.50      m1_subset_1(sK4(sK0,sK1,k8_tmap_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | k8_tmap_1(sK0,sK1) = k8_tmap_1(sK0,sK2)).
% 0.21/0.50  
% 0.21/0.50  cnf(u324,negated_conjecture,
% 0.21/0.50      m1_subset_1(sK4(sK0,sK2,k8_tmap_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | k8_tmap_1(sK0,sK1) = k8_tmap_1(sK0,sK2)).
% 0.21/0.50  
% 0.21/0.50  cnf(u62,negated_conjecture,
% 0.21/0.50      m1_subset_1(sK3,u1_struct_0(sK2))).
% 0.21/0.50  
% 0.21/0.50  cnf(u225,negated_conjecture,
% 0.21/0.50      m1_subset_1(k9_tmap_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))).
% 0.21/0.50  
% 0.21/0.50  cnf(u224,negated_conjecture,
% 0.21/0.50      m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))).
% 0.21/0.50  
% 0.21/0.50  cnf(u220,negated_conjecture,
% 0.21/0.50      m1_subset_1(k9_tmap_1(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0))))) | ~m1_pre_topc(X0,sK0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u344,negated_conjecture,
% 0.21/0.50      m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | k8_tmap_1(sK0,sK1) = k8_tmap_1(sK0,sK2)).
% 0.21/0.50  
% 0.21/0.50  cnf(u329,negated_conjecture,
% 0.21/0.50      m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | k8_tmap_1(sK0,sK1) = k8_tmap_1(sK0,sK2)).
% 0.21/0.50  
% 0.21/0.50  cnf(u68,axiom,
% 0.21/0.50      m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u361,negated_conjecture,
% 0.21/0.50      ~m1_subset_1(X1,u1_struct_0(sK1)) | ~r1_xboole_0(u1_struct_0(sK1),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tmap_1(sK1,k6_tmap_1(sK0,X0),k2_tmap_1(sK0,k6_tmap_1(sK0,X0),k7_tmap_1(sK0,X0),sK1),X1)).
% 0.21/0.50  
% 0.21/0.50  cnf(u235,negated_conjecture,
% 0.21/0.50      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK1),X0) | v2_struct_0(k8_tmap_1(sK0,sK1))).
% 0.21/0.50  
% 0.21/0.50  cnf(u249,negated_conjecture,
% 0.21/0.50      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK2),X0) | v2_struct_0(k8_tmap_1(sK0,sK2))).
% 0.21/0.50  
% 0.21/0.50  cnf(u74,axiom,
% 0.21/0.50      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u207,negated_conjecture,
% 0.21/0.50      v1_funct_2(k9_tmap_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0))).
% 0.21/0.50  
% 0.21/0.50  cnf(u206,negated_conjecture,
% 0.21/0.50      v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))).
% 0.21/0.50  
% 0.21/0.50  cnf(u202,negated_conjecture,
% 0.21/0.50      v1_funct_2(k9_tmap_1(sK0,X0),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0))) | ~m1_pre_topc(X0,sK0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u82,axiom,
% 0.21/0.50      v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u86,axiom,
% 0.21/0.50      ~v1_funct_1(X4) | ~r1_funct_2(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | X4 = X5 | v1_xboole_0(X3) | v1_xboole_0(X1)).
% 0.21/0.50  
% 0.21/0.50  cnf(u353,axiom,
% 0.21/0.50      ~v1_funct_1(X6) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X6,X2,X3) | ~r1_funct_2(X0,X1,X2,X3,k9_tmap_1(X4,X5),X6) | ~m1_subset_1(k9_tmap_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(k9_tmap_1(X4,X5),X0,X1) | k9_tmap_1(X4,X5) = X6 | v1_xboole_0(X3) | v1_xboole_0(X1) | ~m1_pre_topc(X5,X4) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)).
% 0.21/0.50  
% 0.21/0.50  cnf(u133,negated_conjecture,
% 0.21/0.50      ~v1_xboole_0(u1_struct_0(sK0)) | ~l1_struct_0(k8_tmap_1(sK0,sK1)) | v2_struct_0(k8_tmap_1(sK0,sK1))).
% 0.21/0.50  
% 0.21/0.50  cnf(u141,negated_conjecture,
% 0.21/0.50      ~v1_xboole_0(u1_struct_0(sK0)) | ~l1_struct_0(k8_tmap_1(sK0,sK2)) | v2_struct_0(k8_tmap_1(sK0,sK2))).
% 0.21/0.50  
% 0.21/0.50  cnf(u69,axiom,
% 0.21/0.50      ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u252,negated_conjecture,
% 0.21/0.50      v2_struct_0(k8_tmap_1(sK0,sK2)) | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK2),u1_struct_0(sK1))).
% 0.21/0.50  
% 0.21/0.50  cnf(u253,negated_conjecture,
% 0.21/0.50      v2_struct_0(k8_tmap_1(sK0,sK2)) | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK2),u1_struct_0(sK2))).
% 0.21/0.50  
% 0.21/0.50  cnf(u325,negated_conjecture,
% 0.21/0.50      v2_struct_0(k8_tmap_1(sK0,sK2)) | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK2),sK4(sK0,sK2,k8_tmap_1(sK0,sK1))) | k8_tmap_1(sK0,sK1) = k8_tmap_1(sK0,sK2)).
% 0.21/0.50  
% 0.21/0.50  cnf(u340,negated_conjecture,
% 0.21/0.50      v2_struct_0(k8_tmap_1(sK0,sK2)) | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK2),sK4(sK0,sK1,k8_tmap_1(sK0,sK2))) | k8_tmap_1(sK0,sK1) = k8_tmap_1(sK0,sK2)).
% 0.21/0.50  
% 0.21/0.50  cnf(u238,negated_conjecture,
% 0.21/0.50      v2_struct_0(k8_tmap_1(sK0,sK1)) | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(sK1))).
% 0.21/0.50  
% 0.21/0.50  cnf(u239,negated_conjecture,
% 0.21/0.50      v2_struct_0(k8_tmap_1(sK0,sK1)) | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(sK2))).
% 0.21/0.50  
% 0.21/0.50  cnf(u326,negated_conjecture,
% 0.21/0.50      v2_struct_0(k8_tmap_1(sK0,sK1)) | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK1),sK4(sK0,sK2,k8_tmap_1(sK0,sK1))) | k8_tmap_1(sK0,sK1) = k8_tmap_1(sK0,sK2)).
% 0.21/0.50  
% 0.21/0.50  cnf(u341,negated_conjecture,
% 0.21/0.50      v2_struct_0(k8_tmap_1(sK0,sK1)) | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK1),sK4(sK0,sK1,k8_tmap_1(sK0,sK2))) | k8_tmap_1(sK0,sK1) = k8_tmap_1(sK0,sK2)).
% 0.21/0.50  
% 0.21/0.50  cnf(u59,negated_conjecture,
% 0.21/0.50      ~v2_struct_0(sK2)).
% 0.21/0.50  
% 0.21/0.50  cnf(u57,negated_conjecture,
% 0.21/0.50      ~v2_struct_0(sK1)).
% 0.21/0.50  
% 0.21/0.50  cnf(u54,negated_conjecture,
% 0.21/0.50      ~v2_struct_0(sK0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u60,negated_conjecture,
% 0.21/0.50      m1_pre_topc(sK2,sK0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u58,negated_conjecture,
% 0.21/0.50      m1_pre_topc(sK1,sK0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u140,negated_conjecture,
% 0.21/0.50      ~m1_pre_topc(k8_tmap_1(sK0,sK2),X5) | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5))) | ~l1_pre_topc(X5)).
% 0.21/0.50  
% 0.21/0.50  cnf(u132,negated_conjecture,
% 0.21/0.50      ~m1_pre_topc(k8_tmap_1(sK0,sK1),X5) | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5))) | ~l1_pre_topc(X5)).
% 0.21/0.50  
% 0.21/0.50  cnf(u99,negated_conjecture,
% 0.21/0.50      ~m1_pre_topc(X0,sK2) | l1_pre_topc(X0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u98,negated_conjecture,
% 0.21/0.50      ~m1_pre_topc(X0,sK1) | l1_pre_topc(X0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u357,negated_conjecture,
% 0.21/0.50      ~m1_pre_topc(X1,sK0) | ~r1_xboole_0(u1_struct_0(X1),X2) | ~m1_subset_1(X0,u1_struct_0(X1)) | v2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tmap_1(X1,k6_tmap_1(sK0,X2),k2_tmap_1(sK0,k6_tmap_1(sK0,X2),k7_tmap_1(sK0,X2),X1),X0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u322,negated_conjecture,
% 0.21/0.50      ~m1_pre_topc(X1,sK0) | k8_tmap_1(sK0,X1) = k8_tmap_1(sK0,sK2) | m1_subset_1(sK4(sK0,X1,k8_tmap_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.50  
% 0.21/0.50  cnf(u321,negated_conjecture,
% 0.21/0.50      ~m1_pre_topc(X0,sK0) | k8_tmap_1(sK0,sK1) = k8_tmap_1(sK0,X0) | m1_subset_1(sK4(sK0,X0,k8_tmap_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.50  
% 0.21/0.50  cnf(u319,negated_conjecture,
% 0.21/0.50      ~m1_pre_topc(X1,sK0) | k8_tmap_1(sK0,X1) = k8_tmap_1(sK0,X0) | ~m1_pre_topc(X0,sK0) | m1_subset_1(sK4(sK0,X0,k8_tmap_1(sK0,X1)),k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.50  
% 0.21/0.50  cnf(u292,negated_conjecture,
% 0.21/0.50      ~m1_pre_topc(X1,sK0) | k8_tmap_1(sK0,X1) = k8_tmap_1(sK0,sK2) | u1_struct_0(X1) = sK4(sK0,X1,k8_tmap_1(sK0,sK2))).
% 0.21/0.50  
% 0.21/0.50  cnf(u291,negated_conjecture,
% 0.21/0.50      ~m1_pre_topc(X0,sK0) | k8_tmap_1(sK0,sK1) = k8_tmap_1(sK0,X0) | u1_struct_0(X0) = sK4(sK0,X0,k8_tmap_1(sK0,sK1))).
% 0.21/0.50  
% 0.21/0.50  cnf(u289,negated_conjecture,
% 0.21/0.50      ~m1_pre_topc(X1,sK0) | k8_tmap_1(sK0,X1) = k8_tmap_1(sK0,X0) | ~m1_pre_topc(X0,sK0) | u1_struct_0(X0) = sK4(sK0,X0,k8_tmap_1(sK0,X1))).
% 0.21/0.50  
% 0.21/0.50  cnf(u277,negated_conjecture,
% 0.21/0.50      ~m1_pre_topc(X0,sK0) | k8_tmap_1(sK0,X0) = k6_tmap_1(sK0,u1_struct_0(X0))).
% 0.21/0.50  
% 0.21/0.50  cnf(u251,negated_conjecture,
% 0.21/0.50      ~m1_pre_topc(X0,sK0) | v2_struct_0(k8_tmap_1(sK0,sK2)) | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK2),u1_struct_0(X0))).
% 0.21/0.50  
% 0.21/0.50  cnf(u237,negated_conjecture,
% 0.21/0.50      ~m1_pre_topc(X0,sK0) | v2_struct_0(k8_tmap_1(sK0,sK1)) | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(X0))).
% 0.21/0.50  
% 0.21/0.50  cnf(u211,negated_conjecture,
% 0.21/0.50      ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | u1_pre_topc(k8_tmap_1(sK0,X0)) = k5_tmap_1(sK0,u1_struct_0(X0))).
% 0.21/0.50  
% 0.21/0.50  cnf(u121,negated_conjecture,
% 0.21/0.50      ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,X0))).
% 0.21/0.50  
% 0.21/0.50  cnf(u114,negated_conjecture,
% 0.21/0.50      ~m1_pre_topc(X0,sK0) | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(X0))).
% 0.21/0.50  
% 0.21/0.50  cnf(u95,negated_conjecture,
% 0.21/0.50      ~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u139,negated_conjecture,
% 0.21/0.50      ~m1_pre_topc(X4,k8_tmap_1(sK0,sK2)) | m1_subset_1(u1_struct_0(X4),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(k8_tmap_1(sK0,sK2))).
% 0.21/0.50  
% 0.21/0.50  cnf(u131,negated_conjecture,
% 0.21/0.50      ~m1_pre_topc(X4,k8_tmap_1(sK0,sK1)) | m1_subset_1(u1_struct_0(X4),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(k8_tmap_1(sK0,sK1))).
% 0.21/0.50  
% 0.21/0.50  cnf(u358,axiom,
% 0.21/0.50      ~m1_pre_topc(X4,k8_tmap_1(X6,X7)) | ~r1_xboole_0(u1_struct_0(X4),X5) | ~m1_subset_1(X3,u1_struct_0(X4)) | v2_struct_0(X4) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k8_tmap_1(X6,X7)))) | r1_tmap_1(X4,k6_tmap_1(k8_tmap_1(X6,X7),X5),k2_tmap_1(k8_tmap_1(X6,X7),k6_tmap_1(k8_tmap_1(X6,X7),X5),k7_tmap_1(k8_tmap_1(X6,X7),X5),X4),X3) | v2_struct_0(k8_tmap_1(X6,X7)) | ~m1_pre_topc(X7,X6) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)).
% 0.21/0.50  
% 0.21/0.50  cnf(u320,negated_conjecture,
% 0.21/0.50      ~m1_pre_topc(X2,k8_tmap_1(X3,X4)) | k8_tmap_1(k8_tmap_1(X3,X4),X2) = k8_tmap_1(sK0,X5) | v2_struct_0(k8_tmap_1(X3,X4)) | ~m1_pre_topc(X5,sK0) | m1_subset_1(sK4(k8_tmap_1(X3,X4),X2,k8_tmap_1(sK0,X5)),k1_zfmisc_1(u1_struct_0(k8_tmap_1(X3,X4)))) | ~m1_pre_topc(X4,X3) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)).
% 0.21/0.50  
% 0.21/0.50  cnf(u315,axiom,
% 0.21/0.50      ~m1_pre_topc(X7,k8_tmap_1(X5,X6)) | ~m1_pre_topc(X4,X3) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | k8_tmap_1(X3,X4) = k8_tmap_1(k8_tmap_1(X5,X6),X7) | m1_subset_1(sK4(X3,X4,k8_tmap_1(k8_tmap_1(X5,X6),X7)),k1_zfmisc_1(u1_struct_0(X3))) | v2_struct_0(k8_tmap_1(X5,X6)) | ~m1_pre_topc(X6,X5) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)).
% 0.21/0.50  
% 0.21/0.50  cnf(u290,negated_conjecture,
% 0.21/0.50      ~m1_pre_topc(X2,k8_tmap_1(X3,X4)) | k8_tmap_1(k8_tmap_1(X3,X4),X2) = k8_tmap_1(sK0,X5) | v2_struct_0(k8_tmap_1(X3,X4)) | ~m1_pre_topc(X5,sK0) | u1_struct_0(X2) = sK4(k8_tmap_1(X3,X4),X2,k8_tmap_1(sK0,X5)) | ~m1_pre_topc(X4,X3) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)).
% 0.21/0.50  
% 0.21/0.50  cnf(u285,axiom,
% 0.21/0.50      ~m1_pre_topc(X7,k8_tmap_1(X5,X6)) | ~m1_pre_topc(X4,X3) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | k8_tmap_1(X3,X4) = k8_tmap_1(k8_tmap_1(X5,X6),X7) | u1_struct_0(X4) = sK4(X3,X4,k8_tmap_1(k8_tmap_1(X5,X6),X7)) | v2_struct_0(k8_tmap_1(X5,X6)) | ~m1_pre_topc(X6,X5) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)).
% 0.21/0.50  
% 0.21/0.50  cnf(u278,axiom,
% 0.21/0.50      ~m1_pre_topc(X3,k8_tmap_1(X1,X2)) | k8_tmap_1(k8_tmap_1(X1,X2),X3) = k6_tmap_1(k8_tmap_1(X1,X2),u1_struct_0(X3)) | v2_struct_0(k8_tmap_1(X1,X2)) | ~m1_pre_topc(X2,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)).
% 0.21/0.50  
% 0.21/0.50  cnf(u261,axiom,
% 0.21/0.50      ~m1_pre_topc(X1,k8_tmap_1(X2,X3)) | v2_struct_0(X1) | r1_funct_2(u1_struct_0(k8_tmap_1(X2,X3)),u1_struct_0(k8_tmap_1(k8_tmap_1(X2,X3),X1)),u1_struct_0(k8_tmap_1(X2,X3)),u1_struct_0(k8_tmap_1(X2,X3)),k9_tmap_1(k8_tmap_1(X2,X3),X1),k3_struct_0(k8_tmap_1(X2,X3))) | v2_struct_0(k8_tmap_1(X2,X3)) | ~m1_pre_topc(X3,X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)).
% 0.21/0.50  
% 0.21/0.50  cnf(u221,axiom,
% 0.21/0.50      ~m1_pre_topc(X1,k8_tmap_1(X2,X3)) | m1_subset_1(k9_tmap_1(k8_tmap_1(X2,X3),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k8_tmap_1(X2,X3)),u1_struct_0(k8_tmap_1(k8_tmap_1(X2,X3),X1))))) | v2_struct_0(k8_tmap_1(X2,X3)) | ~m1_pre_topc(X3,X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)).
% 0.21/0.50  
% 0.21/0.50  cnf(u212,axiom,
% 0.21/0.50      ~m1_pre_topc(X1,k8_tmap_1(X2,X3)) | v2_struct_0(k8_tmap_1(X2,X3)) | v2_struct_0(X1) | u1_pre_topc(k8_tmap_1(k8_tmap_1(X2,X3),X1)) = k5_tmap_1(k8_tmap_1(X2,X3),u1_struct_0(X1)) | ~m1_pre_topc(X3,X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)).
% 0.21/0.50  
% 0.21/0.50  cnf(u203,axiom,
% 0.21/0.50      ~m1_pre_topc(X1,k8_tmap_1(X2,X3)) | v1_funct_2(k9_tmap_1(k8_tmap_1(X2,X3),X1),u1_struct_0(k8_tmap_1(X2,X3)),u1_struct_0(k8_tmap_1(k8_tmap_1(X2,X3),X1))) | v2_struct_0(k8_tmap_1(X2,X3)) | ~m1_pre_topc(X3,X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)).
% 0.21/0.50  
% 0.21/0.50  cnf(u122,axiom,
% 0.21/0.50      ~m1_pre_topc(X1,k8_tmap_1(X2,X3)) | v2_struct_0(X1) | u1_struct_0(k8_tmap_1(X2,X3)) = u1_struct_0(k8_tmap_1(k8_tmap_1(X2,X3),X1)) | v2_struct_0(k8_tmap_1(X2,X3)) | ~m1_pre_topc(X3,X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)).
% 0.21/0.50  
% 0.21/0.50  cnf(u115,axiom,
% 0.21/0.50      ~m1_pre_topc(X3,k8_tmap_1(X1,X2)) | v2_struct_0(k8_tmap_1(X1,X2)) | k6_partfun1(u1_struct_0(k8_tmap_1(X1,X2))) = k7_tmap_1(k8_tmap_1(X1,X2),u1_struct_0(X3)) | ~m1_pre_topc(X2,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)).
% 0.21/0.50  
% 0.21/0.50  cnf(u108,axiom,
% 0.21/0.50      ~m1_pre_topc(X2,k8_tmap_1(X1,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~m1_pre_topc(X0,X1) | l1_pre_topc(X2)).
% 0.21/0.50  
% 0.21/0.50  cnf(u66,axiom,
% 0.21/0.50      l1_struct_0(X0) | ~l1_pre_topc(X0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u85,axiom,
% 0.21/0.50      ~l1_struct_0(X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | r1_tsep_1(X1,X0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u100,axiom,
% 0.21/0.50      ~l1_struct_0(X1) | ~r1_tsep_1(X0,X1) | r1_tsep_1(X1,X0) | ~l1_pre_topc(X0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u151,negated_conjecture,
% 0.21/0.50      ~l1_struct_0(X0) | ~r1_xboole_0(u1_struct_0(sK0),u1_struct_0(X0)) | r1_tsep_1(k8_tmap_1(sK0,sK1),X0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u161,negated_conjecture,
% 0.21/0.50      ~l1_struct_0(X0) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK0)) | r1_tsep_1(X0,k8_tmap_1(sK0,sK1))).
% 0.21/0.50  
% 0.21/0.50  cnf(u171,negated_conjecture,
% 0.21/0.50      ~l1_struct_0(X0) | ~r1_xboole_0(u1_struct_0(sK0),u1_struct_0(X0)) | r1_tsep_1(k8_tmap_1(sK0,sK2),X0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u181,negated_conjecture,
% 0.21/0.50      ~l1_struct_0(X0) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK0)) | r1_tsep_1(X0,k8_tmap_1(sK0,sK2))).
% 0.21/0.50  
% 0.21/0.50  cnf(u97,negated_conjecture,
% 0.21/0.50      l1_pre_topc(sK2)).
% 0.21/0.50  
% 0.21/0.50  cnf(u96,negated_conjecture,
% 0.21/0.50      l1_pre_topc(sK1)).
% 0.21/0.50  
% 0.21/0.50  cnf(u56,negated_conjecture,
% 0.21/0.50      l1_pre_topc(sK0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u81,axiom,
% 0.21/0.50      l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u67,axiom,
% 0.21/0.50      ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)).
% 0.21/0.50  
% 0.21/0.50  cnf(u302,negated_conjecture,
% 0.21/0.50      u1_struct_0(sK1) = sK4(sK0,sK1,k8_tmap_1(sK0,sK2)) | k8_tmap_1(sK0,sK1) = k8_tmap_1(sK0,sK2)).
% 0.21/0.50  
% 0.21/0.50  cnf(u294,negated_conjecture,
% 0.21/0.50      u1_struct_0(sK2) = sK4(sK0,sK2,k8_tmap_1(sK0,sK1)) | k8_tmap_1(sK0,sK1) = k8_tmap_1(sK0,sK2)).
% 0.21/0.50  
% 0.21/0.50  cnf(u216,negated_conjecture,
% 0.21/0.50      u1_pre_topc(k8_tmap_1(sK0,sK2)) = k5_tmap_1(sK0,u1_struct_0(sK2))).
% 0.21/0.50  
% 0.21/0.50  cnf(u215,negated_conjecture,
% 0.21/0.50      u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1))).
% 0.21/0.50  
% 0.21/0.50  cnf(u280,negated_conjecture,
% 0.21/0.50      k8_tmap_1(sK0,sK2) = k6_tmap_1(sK0,u1_struct_0(sK2))).
% 0.21/0.50  
% 0.21/0.50  cnf(u279,negated_conjecture,
% 0.21/0.50      k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))).
% 0.21/0.50  
% 0.21/0.50  cnf(u347,negated_conjecture,
% 0.21/0.50      k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,sK4(sK0,sK1,k8_tmap_1(sK0,sK2))) | k8_tmap_1(sK0,sK1) = k8_tmap_1(sK0,sK2)).
% 0.21/0.50  
% 0.21/0.50  cnf(u332,negated_conjecture,
% 0.21/0.50      k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,sK4(sK0,sK2,k8_tmap_1(sK0,sK1))) | k8_tmap_1(sK0,sK1) = k8_tmap_1(sK0,sK2)).
% 0.21/0.50  
% 0.21/0.50  cnf(u117,negated_conjecture,
% 0.21/0.50      k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK2))).
% 0.21/0.50  
% 0.21/0.50  cnf(u116,negated_conjecture,
% 0.21/0.50      k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK1))).
% 0.21/0.50  
% 0.21/0.50  cnf(u126,negated_conjecture,
% 0.21/0.50      u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK2))).
% 0.21/0.50  
% 0.21/0.50  cnf(u125,negated_conjecture,
% 0.21/0.50      u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))).
% 0.21/0.50  
% 0.21/0.50  cnf(u73,axiom,
% 0.21/0.50      k6_tmap_1(X0,sK4(X0,X1,X2)) != X2 | k8_tmap_1(X0,X1) = X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)).
% 0.21/0.50  
% 0.21/0.50  % (2339)# SZS output end Saturation.
% 0.21/0.50  % (2339)------------------------------
% 0.21/0.50  % (2339)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (2339)Termination reason: Satisfiable
% 0.21/0.50  
% 0.21/0.50  % (2339)Memory used [KB]: 6524
% 0.21/0.50  % (2339)Time elapsed: 0.023 s
% 0.21/0.50  % (2339)------------------------------
% 0.21/0.50  % (2339)------------------------------
% 0.21/0.50  % (2317)Success in time 0.142 s
%------------------------------------------------------------------------------
