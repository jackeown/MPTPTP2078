%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:39 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :   91 (  91 expanded)
%              Number of leaves         :   91 (  91 expanded)
%              Depth                    :    0
%              Number of atoms          :  354 ( 354 expanded)
%              Number of equality atoms :   38 (  38 expanded)
%              Maximal clause size      :   10 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u247,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),sK1,k8_tmap_1(sK0,sK1)) )).

cnf(u313,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),sK1,k8_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1)) )).

cnf(u68,axiom,
    ( v1_pre_topc(k8_tmap_1(X0,X1))
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0) )).

cnf(u58,axiom,
    ( ~ v1_pre_topc(X2)
    | u1_struct_0(X1) = sK2(X0,X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | k8_tmap_1(X0,X1) = X2
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0) )).

cnf(u57,axiom,
    ( ~ v1_pre_topc(X2)
    | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | k8_tmap_1(X0,X1) = X2
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0) )).

cnf(u51,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) )).

cnf(u167,negated_conjecture,
    ( ~ m1_pre_topc(k8_tmap_1(sK0,sK1),X1)
    | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) )).

cnf(u169,negated_conjecture,
    ( ~ m1_pre_topc(k8_tmap_1(sK0,sK1),X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X3)
    | v2_struct_0(X3)
    | v1_funct_1(k7_tmap_1(X3,u1_struct_0(sK0))) )).

cnf(u108,negated_conjecture,
    ( ~ m1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)),X1)
    | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) )).

cnf(u113,negated_conjecture,
    ( ~ m1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)),X5)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X5)
    | v2_struct_0(X5)
    | v1_funct_1(k7_tmap_1(X5,u1_struct_0(sK0))) )).

cnf(u166,negated_conjecture,
    ( ~ m1_pre_topc(X0,k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u180,negated_conjecture,
    ( ~ m1_pre_topc(X4,k8_tmap_1(sK0,sK1))
    | r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X4)),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(k8_tmap_1(sK0,sK1),X4),k3_struct_0(k8_tmap_1(sK0,sK1)))
    | v2_struct_0(X4)
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | v2_struct_0(k8_tmap_1(sK0,sK1)) )).

cnf(u120,negated_conjecture,
    ( ~ m1_pre_topc(X0,sK0)
    | u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(X0))) = k5_tmap_1(sK0,u1_struct_0(X0)) )).

cnf(u130,negated_conjecture,
    ( ~ m1_pre_topc(X0,sK0)
    | v1_funct_2(k7_tmap_1(sK0,u1_struct_0(X0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0)))) )).

cnf(u140,negated_conjecture,
    ( ~ m1_pre_topc(X0,sK0)
    | m1_subset_1(k7_tmap_1(sK0,u1_struct_0(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0)))))) )).

cnf(u209,negated_conjecture,
    ( ~ m1_pre_topc(X0,sK0)
    | v2_struct_0(k8_tmap_1(sK0,sK1))
    | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(X0)) )).

cnf(u222,negated_conjecture,
    ( ~ m1_pre_topc(X0,sK0)
    | v2_struct_0(k8_tmap_1(sK0,sK1))
    | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(X0))) )).

cnf(u238,negated_conjecture,
    ( ~ m1_pre_topc(X0,sK0)
    | v2_struct_0(k8_tmap_1(sK0,sK1))
    | u1_pre_topc(k6_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(X0))) = k5_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(X0)) )).

cnf(u288,axiom,
    ( ~ m1_pre_topc(X2,X0)
    | m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X2))))))
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0) )).

cnf(u258,axiom,
    ( ~ m1_pre_topc(X2,X0)
    | v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X2))))
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0) )).

cnf(u256,negated_conjecture,
    ( ~ m1_pre_topc(X1,X0)
    | k8_tmap_1(X0,X1) = k8_tmap_1(sK0,sK1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | m1_subset_1(sK2(X0,X1,k8_tmap_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(X0))) )).

cnf(u251,negated_conjecture,
    ( ~ m1_pre_topc(X1,X0)
    | k8_tmap_1(X0,X1) = k8_tmap_1(sK0,sK1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | u1_struct_0(X1) = sK2(X0,X1,k8_tmap_1(sK0,sK1)) )).

cnf(u240,axiom,
    ( ~ m1_pre_topc(X2,X0)
    | v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),X2,k6_tmap_1(X0,u1_struct_0(X2)))
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0) )).

cnf(u160,axiom,
    ( ~ m1_pre_topc(X1,X0)
    | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) )).

cnf(u151,axiom,
    ( ~ m1_pre_topc(X2,X0)
    | v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2))
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0) )).

cnf(u150,axiom,
    ( ~ m1_pre_topc(X3,X2)
    | k8_tmap_1(X0,X1) = k8_tmap_1(X2,X3)
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | m1_subset_1(sK2(X0,X1,k8_tmap_1(X2,X3)),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X2) )).

cnf(u146,axiom,
    ( ~ m1_pre_topc(X3,X2)
    | k8_tmap_1(X2,X3) = k8_tmap_1(X1,X0)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | u1_struct_0(X0) = sK2(X1,X0,k8_tmap_1(X2,X3))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X2) )).

cnf(u118,axiom,
    ( ~ m1_pre_topc(X3,X2)
    | u1_pre_topc(k6_tmap_1(k8_tmap_1(X2,X3),X1)) = k5_tmap_1(k8_tmap_1(X2,X3),X1)
    | v2_struct_0(k8_tmap_1(X2,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k8_tmap_1(X2,X3))))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X2) )).

cnf(u102,axiom,
    ( ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))) )).

cnf(u91,axiom,
    ( ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,u1_struct_0(X1)) )).

cnf(u69,axiom,
    ( v2_pre_topc(k8_tmap_1(X0,X1))
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0) )).

cnf(u48,negated_conjecture,
    ( v2_pre_topc(sK0) )).

cnf(u112,negated_conjecture,
    ( ~ v2_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | v1_funct_1(k7_tmap_1(k6_tmap_1(sK0,u1_struct_0(sK1)),X4))
    | ~ l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) )).

cnf(u62,axiom,
    ( ~ v2_pre_topc(X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
    | v2_struct_0(X0) )).

cnf(u75,axiom,
    ( ~ v2_pre_topc(X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | v2_struct_0(X0) )).

cnf(u76,axiom,
    ( ~ v2_pre_topc(X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
    | v2_struct_0(X0) )).

cnf(u86,axiom,
    ( r1_funct_2(X0,X1,X2,X3,X5,X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_2(X5,X2,X3)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(X5,X0,X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X1) )).

cnf(u189,negated_conjecture,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k3_struct_0(sK0)) )).

cnf(u67,axiom,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0))
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0) )).

cnf(u77,axiom,
    ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
    | X4 = X5
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_2(X5,X2,X3)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(X4,X0,X1)
    | ~ v1_funct_1(X4)
    | v1_xboole_0(X3)
    | v1_xboole_0(X1) )).

cnf(u296,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) )).

cnf(u182,negated_conjecture,
    ( m1_subset_1(k9_tmap_1(k8_tmap_1(sK0,sK1),X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X6)))))
    | ~ m1_pre_topc(X6,k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | v2_struct_0(k8_tmap_1(sK0,sK1)) )).

cnf(u193,negated_conjecture,
    ( m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )).

cnf(u73,axiom,
    ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0) )).

cnf(u143,negated_conjecture,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )).

cnf(u301,negated_conjecture,
    ( m1_subset_1(k7_tmap_1(k8_tmap_1(sK0,sK1),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(k8_tmap_1(sK0,sK1),X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(k8_tmap_1(sK0,sK1)) )).

cnf(u138,axiom,
    ( m1_subset_1(k7_tmap_1(k8_tmap_1(X2,X3),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k8_tmap_1(X2,X3)),u1_struct_0(k6_tmap_1(k8_tmap_1(X2,X3),X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k8_tmap_1(X2,X3))))
    | v2_struct_0(k8_tmap_1(X2,X3))
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X2) )).

cnf(u54,axiom,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0) )).

cnf(u287,negated_conjecture,
    ( ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | k9_tmap_1(sK0,sK1) = k3_struct_0(sK0)
    | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k3_struct_0(sK0))
    | ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK0)) )).

cnf(u117,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_pre_topc(k6_tmap_1(sK0,X0)) = k5_tmap_1(sK0,X0) )).

cnf(u127,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_funct_2(k7_tmap_1(sK0,X0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X0))) )).

cnf(u137,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k7_tmap_1(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X0))))) )).

cnf(u207,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK1),X0)
    | v2_struct_0(k8_tmap_1(sK0,sK1)) )).

cnf(u220,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(k8_tmap_1(sK0,sK1),X0))
    | v2_struct_0(k8_tmap_1(sK0,sK1)) )).

cnf(u236,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_pre_topc(k6_tmap_1(k8_tmap_1(sK0,sK1),X0)) = k5_tmap_1(k8_tmap_1(sK0,sK1),X0)
    | v2_struct_0(k8_tmap_1(sK0,sK1)) )).

cnf(u74,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v1_funct_1(k7_tmap_1(X0,X1))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0) )).

cnf(u60,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0) )).

cnf(u61,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0) )).

cnf(u266,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),u1_struct_0(sK1),u1_struct_0(sK0)) )).

cnf(u197,negated_conjecture,
    ( v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) )).

cnf(u181,negated_conjecture,
    ( v1_funct_2(k9_tmap_1(k8_tmap_1(sK0,sK1),X5),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X5)))
    | ~ m1_pre_topc(X5,k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | v2_struct_0(k8_tmap_1(sK0,sK1)) )).

cnf(u72,axiom,
    ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0) )).

cnf(u133,negated_conjecture,
    ( v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) )).

cnf(u271,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(k8_tmap_1(sK0,sK1),X0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(k8_tmap_1(sK0,sK1),X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(k8_tmap_1(sK0,sK1)) )).

cnf(u128,axiom,
    ( v1_funct_2(k7_tmap_1(k8_tmap_1(X2,X3),X1),u1_struct_0(k8_tmap_1(X2,X3)),u1_struct_0(k6_tmap_1(k8_tmap_1(X2,X3),X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k8_tmap_1(X2,X3))))
    | v2_struct_0(k8_tmap_1(X2,X3))
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X2) )).

cnf(u171,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1)) )).

cnf(u157,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k6_partfun1(u1_struct_0(sK0)),sK1)) )).

cnf(u71,axiom,
    ( v1_funct_1(k9_tmap_1(X0,X1))
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0) )).

cnf(u100,negated_conjecture,
    ( v1_funct_1(k6_partfun1(u1_struct_0(sK0))) )).

cnf(u168,negated_conjecture,
    ( v1_funct_1(k7_tmap_1(k8_tmap_1(sK0,sK1),X2))
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(k8_tmap_1(sK0,sK1)) )).

cnf(u89,axiom,
    ( v1_funct_1(k7_tmap_1(X0,u1_struct_0(X1)))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ m1_pre_topc(X1,X0) )).

cnf(u285,axiom,
    ( ~ v1_funct_1(k3_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ v2_pre_topc(X0)
    | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | k9_tmap_1(X0,X1) = k3_struct_0(X0)
    | ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0)) )).

cnf(u109,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | v2_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) )).

cnf(u177,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(k8_tmap_1(sK0,sK1))
    | v2_struct_0(k8_tmap_1(sK0,sK1)) )).

cnf(u55,axiom,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) )).

cnf(u210,negated_conjecture,
    ( v2_struct_0(k8_tmap_1(sK0,sK1))
    | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(sK1)) )).

cnf(u223,negated_conjecture,
    ( v2_struct_0(k8_tmap_1(sK0,sK1))
    | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(sK1))) )).

cnf(u239,negated_conjecture,
    ( v2_struct_0(k8_tmap_1(sK0,sK1))
    | u1_pre_topc(k6_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(sK1))) = k5_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(sK1)) )).

cnf(u50,negated_conjecture,
    ( ~ v2_struct_0(sK1) )).

cnf(u47,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u53,axiom,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) )).

cnf(u70,axiom,
    ( l1_pre_topc(k8_tmap_1(X0,X1))
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0) )).

cnf(u49,negated_conjecture,
    ( l1_pre_topc(sK0) )).

cnf(u107,negated_conjecture,
    ( ~ l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ m1_pre_topc(X0,k6_tmap_1(sK0,u1_struct_0(sK1)))
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u170,negated_conjecture,
    ( k5_tmap_1(sK0,u1_struct_0(sK1)) = u1_pre_topc(k8_tmap_1(sK0,sK1)) )).

cnf(u121,negated_conjecture,
    ( u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) = k5_tmap_1(sK0,u1_struct_0(sK1)) )).

cnf(u164,negated_conjecture,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) )).

cnf(u95,negated_conjecture,
    ( k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK1)) )).

cnf(u165,negated_conjecture,
    ( u1_struct_0(k8_tmap_1(sK0,sK1)) = u1_struct_0(sK0) )).

cnf(u106,negated_conjecture,
    ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) )).

cnf(u59,axiom,
    ( k6_tmap_1(X0,sK2(X0,X1,X2)) != X2
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
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:07:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (13184)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.48  % (13200)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.49  % (13184)Refutation not found, incomplete strategy% (13184)------------------------------
% 0.22/0.49  % (13184)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (13184)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (13184)Memory used [KB]: 10746
% 0.22/0.49  % (13184)Time elapsed: 0.073 s
% 0.22/0.49  % (13184)------------------------------
% 0.22/0.49  % (13184)------------------------------
% 0.22/0.50  % (13192)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.51  % (13187)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (13197)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (13185)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (13188)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (13203)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.51  % (13188)Refutation not found, incomplete strategy% (13188)------------------------------
% 0.22/0.51  % (13188)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (13188)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (13188)Memory used [KB]: 6140
% 0.22/0.51  % (13188)Time elapsed: 0.105 s
% 0.22/0.51  % (13188)------------------------------
% 0.22/0.51  % (13188)------------------------------
% 0.22/0.52  % (13201)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.52  % (13186)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.52  % (13193)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.52  % (13205)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.52  % (13206)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.52  % (13186)Refutation not found, incomplete strategy% (13186)------------------------------
% 0.22/0.52  % (13186)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (13186)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (13186)Memory used [KB]: 6396
% 0.22/0.52  % (13186)Time elapsed: 0.105 s
% 0.22/0.52  % (13186)------------------------------
% 0.22/0.52  % (13186)------------------------------
% 0.22/0.52  % (13196)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (13195)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.53  % (13196)Refutation not found, incomplete strategy% (13196)------------------------------
% 0.22/0.53  % (13196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (13196)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (13196)Memory used [KB]: 6268
% 0.22/0.53  % (13196)Time elapsed: 0.114 s
% 0.22/0.53  % (13196)------------------------------
% 0.22/0.53  % (13196)------------------------------
% 0.22/0.53  % (13189)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.53  % (13189)Refutation not found, incomplete strategy% (13189)------------------------------
% 0.22/0.53  % (13189)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (13189)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (13189)Memory used [KB]: 10618
% 0.22/0.53  % (13189)Time elapsed: 0.112 s
% 0.22/0.53  % (13189)------------------------------
% 0.22/0.53  % (13189)------------------------------
% 0.22/0.53  % (13202)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.53  % (13183)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.53  % (13204)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.53  % (13183)Refutation not found, incomplete strategy% (13183)------------------------------
% 0.22/0.53  % (13183)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (13183)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (13183)Memory used [KB]: 10618
% 0.22/0.53  % (13183)Time elapsed: 0.099 s
% 0.22/0.53  % (13183)------------------------------
% 0.22/0.53  % (13183)------------------------------
% 0.22/0.54  % (13199)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.54  % (13194)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.54  % (13198)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.54  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.54  % (13204)# SZS output start Saturation.
% 0.22/0.54  cnf(u247,negated_conjecture,
% 0.22/0.54      v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),sK1,k8_tmap_1(sK0,sK1))).
% 0.22/0.54  
% 0.22/0.54  cnf(u313,negated_conjecture,
% 0.22/0.54      ~v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),sK1,k8_tmap_1(sK0,sK1)) | ~m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1))).
% 0.22/0.54  
% 0.22/0.54  cnf(u68,axiom,
% 0.22/0.54      v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u58,axiom,
% 0.22/0.54      ~v1_pre_topc(X2) | u1_struct_0(X1) = sK2(X0,X1,X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | k8_tmap_1(X0,X1) = X2 | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u57,axiom,
% 0.22/0.54      ~v1_pre_topc(X2) | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | k8_tmap_1(X0,X1) = X2 | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u51,negated_conjecture,
% 0.22/0.54      m1_pre_topc(sK1,sK0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u167,negated_conjecture,
% 0.22/0.54      ~m1_pre_topc(k8_tmap_1(sK0,sK1),X1) | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1)).
% 0.22/0.54  
% 0.22/0.54  cnf(u169,negated_conjecture,
% 0.22/0.54      ~m1_pre_topc(k8_tmap_1(sK0,sK1),X3) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | v1_funct_1(k7_tmap_1(X3,u1_struct_0(sK0)))).
% 0.22/0.54  
% 0.22/0.54  cnf(u108,negated_conjecture,
% 0.22/0.54      ~m1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)),X1) | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1)).
% 0.22/0.54  
% 0.22/0.54  cnf(u113,negated_conjecture,
% 0.22/0.54      ~m1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)),X5) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5) | v1_funct_1(k7_tmap_1(X5,u1_struct_0(sK0)))).
% 0.22/0.54  
% 0.22/0.54  cnf(u166,negated_conjecture,
% 0.22/0.54      ~m1_pre_topc(X0,k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.22/0.54  
% 0.22/0.54  cnf(u180,negated_conjecture,
% 0.22/0.54      ~m1_pre_topc(X4,k8_tmap_1(sK0,sK1)) | r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X4)),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(k8_tmap_1(sK0,sK1),X4),k3_struct_0(k8_tmap_1(sK0,sK1))) | v2_struct_0(X4) | ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~v2_pre_topc(k8_tmap_1(sK0,sK1)) | v2_struct_0(k8_tmap_1(sK0,sK1))).
% 0.22/0.54  
% 0.22/0.54  cnf(u120,negated_conjecture,
% 0.22/0.54      ~m1_pre_topc(X0,sK0) | u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(X0))) = k5_tmap_1(sK0,u1_struct_0(X0))).
% 0.22/0.54  
% 0.22/0.54  cnf(u130,negated_conjecture,
% 0.22/0.54      ~m1_pre_topc(X0,sK0) | v1_funct_2(k7_tmap_1(sK0,u1_struct_0(X0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0))))).
% 0.22/0.54  
% 0.22/0.54  cnf(u140,negated_conjecture,
% 0.22/0.54      ~m1_pre_topc(X0,sK0) | m1_subset_1(k7_tmap_1(sK0,u1_struct_0(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0))))))).
% 0.22/0.54  
% 0.22/0.54  cnf(u209,negated_conjecture,
% 0.22/0.54      ~m1_pre_topc(X0,sK0) | v2_struct_0(k8_tmap_1(sK0,sK1)) | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(X0))).
% 0.22/0.54  
% 0.22/0.54  cnf(u222,negated_conjecture,
% 0.22/0.54      ~m1_pre_topc(X0,sK0) | v2_struct_0(k8_tmap_1(sK0,sK1)) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(X0)))).
% 0.22/0.54  
% 0.22/0.54  cnf(u238,negated_conjecture,
% 0.22/0.54      ~m1_pre_topc(X0,sK0) | v2_struct_0(k8_tmap_1(sK0,sK1)) | u1_pre_topc(k6_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(X0))) = k5_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(X0))).
% 0.22/0.54  
% 0.22/0.54  cnf(u288,axiom,
% 0.22/0.54      ~m1_pre_topc(X2,X0) | m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X2)))))) | v2_struct_0(X2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u258,axiom,
% 0.22/0.54      ~m1_pre_topc(X2,X0) | v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X2)))) | v2_struct_0(X2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u256,negated_conjecture,
% 0.22/0.54      ~m1_pre_topc(X1,X0) | k8_tmap_1(X0,X1) = k8_tmap_1(sK0,sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | m1_subset_1(sK2(X0,X1,k8_tmap_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(X0)))).
% 0.22/0.54  
% 0.22/0.54  cnf(u251,negated_conjecture,
% 0.22/0.54      ~m1_pre_topc(X1,X0) | k8_tmap_1(X0,X1) = k8_tmap_1(sK0,sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | u1_struct_0(X1) = sK2(X0,X1,k8_tmap_1(sK0,sK1))).
% 0.22/0.54  
% 0.22/0.54  cnf(u240,axiom,
% 0.22/0.54      ~m1_pre_topc(X2,X0) | v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),X2,k6_tmap_1(X0,u1_struct_0(X2))) | v2_struct_0(X2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u160,axiom,
% 0.22/0.54      ~m1_pre_topc(X1,X0) | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u151,axiom,
% 0.22/0.54      ~m1_pre_topc(X2,X0) | v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2)) | v2_struct_0(X2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u150,axiom,
% 0.22/0.54      ~m1_pre_topc(X3,X2) | k8_tmap_1(X0,X1) = k8_tmap_1(X2,X3) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | m1_subset_1(sK2(X0,X1,k8_tmap_1(X2,X3)),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)).
% 0.22/0.54  
% 0.22/0.54  cnf(u146,axiom,
% 0.22/0.54      ~m1_pre_topc(X3,X2) | k8_tmap_1(X2,X3) = k8_tmap_1(X1,X0) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | u1_struct_0(X0) = sK2(X1,X0,k8_tmap_1(X2,X3)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)).
% 0.22/0.54  
% 0.22/0.54  cnf(u118,axiom,
% 0.22/0.54      ~m1_pre_topc(X3,X2) | u1_pre_topc(k6_tmap_1(k8_tmap_1(X2,X3),X1)) = k5_tmap_1(k8_tmap_1(X2,X3),X1) | v2_struct_0(k8_tmap_1(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k8_tmap_1(X2,X3)))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)).
% 0.22/0.54  
% 0.22/0.54  cnf(u102,axiom,
% 0.22/0.54      ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1)))).
% 0.22/0.54  
% 0.22/0.54  cnf(u91,axiom,
% 0.22/0.54      ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,u1_struct_0(X1))).
% 0.22/0.54  
% 0.22/0.54  cnf(u69,axiom,
% 0.22/0.54      v2_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u48,negated_conjecture,
% 0.22/0.54      v2_pre_topc(sK0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u112,negated_conjecture,
% 0.22/0.54      ~v2_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) | v1_funct_1(k7_tmap_1(k6_tmap_1(sK0,u1_struct_0(sK1)),X4)) | ~l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))).
% 0.22/0.54  
% 0.22/0.54  cnf(u62,axiom,
% 0.22/0.54      ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) | v2_struct_0(X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u75,axiom,
% 0.22/0.54      ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | v2_struct_0(X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u76,axiom,
% 0.22/0.54      ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | v2_struct_0(X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u86,axiom,
% 0.22/0.54      r1_funct_2(X0,X1,X2,X3,X5,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X5,X0,X1) | v1_xboole_0(X3) | v1_xboole_0(X1)).
% 0.22/0.54  
% 0.22/0.54  cnf(u189,negated_conjecture,
% 0.22/0.54      r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k3_struct_0(sK0))).
% 0.22/0.54  
% 0.22/0.54  cnf(u67,axiom,
% 0.22/0.54      r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u77,axiom,
% 0.22/0.54      ~r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 = X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)).
% 0.22/0.54  
% 0.22/0.54  cnf(u296,negated_conjecture,
% 0.22/0.54      m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))).
% 0.22/0.54  
% 0.22/0.54  cnf(u182,negated_conjecture,
% 0.22/0.54      m1_subset_1(k9_tmap_1(k8_tmap_1(sK0,sK1),X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X6))))) | ~m1_pre_topc(X6,k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~v2_pre_topc(k8_tmap_1(sK0,sK1)) | v2_struct_0(k8_tmap_1(sK0,sK1))).
% 0.22/0.54  
% 0.22/0.54  cnf(u193,negated_conjecture,
% 0.22/0.54      m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))).
% 0.22/0.54  
% 0.22/0.54  cnf(u73,axiom,
% 0.22/0.54      m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u143,negated_conjecture,
% 0.22/0.54      m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))).
% 0.22/0.54  
% 0.22/0.54  cnf(u301,negated_conjecture,
% 0.22/0.54      m1_subset_1(k7_tmap_1(k8_tmap_1(sK0,sK1),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(k8_tmap_1(sK0,sK1),X0))))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(k8_tmap_1(sK0,sK1))).
% 0.22/0.54  
% 0.22/0.54  cnf(u138,axiom,
% 0.22/0.54      m1_subset_1(k7_tmap_1(k8_tmap_1(X2,X3),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k8_tmap_1(X2,X3)),u1_struct_0(k6_tmap_1(k8_tmap_1(X2,X3),X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k8_tmap_1(X2,X3)))) | v2_struct_0(k8_tmap_1(X2,X3)) | ~m1_pre_topc(X3,X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)).
% 0.22/0.54  
% 0.22/0.54  cnf(u54,axiom,
% 0.22/0.54      m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u287,negated_conjecture,
% 0.22/0.54      ~m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | k9_tmap_1(sK0,sK1) = k3_struct_0(sK0) | ~v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k3_struct_0(sK0)) | ~v1_funct_1(k9_tmap_1(sK0,sK1)) | v1_xboole_0(u1_struct_0(sK0))).
% 0.22/0.54  
% 0.22/0.54  cnf(u117,negated_conjecture,
% 0.22/0.54      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_pre_topc(k6_tmap_1(sK0,X0)) = k5_tmap_1(sK0,X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u127,negated_conjecture,
% 0.22/0.54      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_funct_2(k7_tmap_1(sK0,X0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X0)))).
% 0.22/0.54  
% 0.22/0.54  cnf(u137,negated_conjecture,
% 0.22/0.54      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k7_tmap_1(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X0)))))).
% 0.22/0.54  
% 0.22/0.54  cnf(u207,negated_conjecture,
% 0.22/0.54      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK1),X0) | v2_struct_0(k8_tmap_1(sK0,sK1))).
% 0.22/0.54  
% 0.22/0.54  cnf(u220,negated_conjecture,
% 0.22/0.54      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(k8_tmap_1(sK0,sK1),X0)) | v2_struct_0(k8_tmap_1(sK0,sK1))).
% 0.22/0.54  
% 0.22/0.54  cnf(u236,negated_conjecture,
% 0.22/0.54      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_pre_topc(k6_tmap_1(k8_tmap_1(sK0,sK1),X0)) = k5_tmap_1(k8_tmap_1(sK0,sK1),X0) | v2_struct_0(k8_tmap_1(sK0,sK1))).
% 0.22/0.54  
% 0.22/0.54  cnf(u74,axiom,
% 0.22/0.54      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_funct_1(k7_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u60,axiom,
% 0.22/0.54      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u61,axiom,
% 0.22/0.54      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u266,negated_conjecture,
% 0.22/0.54      v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),u1_struct_0(sK1),u1_struct_0(sK0))).
% 0.22/0.54  
% 0.22/0.54  cnf(u197,negated_conjecture,
% 0.22/0.54      v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))).
% 0.22/0.54  
% 0.22/0.54  cnf(u181,negated_conjecture,
% 0.22/0.54      v1_funct_2(k9_tmap_1(k8_tmap_1(sK0,sK1),X5),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X5))) | ~m1_pre_topc(X5,k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~v2_pre_topc(k8_tmap_1(sK0,sK1)) | v2_struct_0(k8_tmap_1(sK0,sK1))).
% 0.22/0.54  
% 0.22/0.54  cnf(u72,axiom,
% 0.22/0.54      v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u133,negated_conjecture,
% 0.22/0.54      v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))).
% 0.22/0.54  
% 0.22/0.54  cnf(u271,negated_conjecture,
% 0.22/0.54      v1_funct_2(k7_tmap_1(k8_tmap_1(sK0,sK1),X0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(k8_tmap_1(sK0,sK1),X0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(k8_tmap_1(sK0,sK1))).
% 0.22/0.54  
% 0.22/0.54  cnf(u128,axiom,
% 0.22/0.54      v1_funct_2(k7_tmap_1(k8_tmap_1(X2,X3),X1),u1_struct_0(k8_tmap_1(X2,X3)),u1_struct_0(k6_tmap_1(k8_tmap_1(X2,X3),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k8_tmap_1(X2,X3)))) | v2_struct_0(k8_tmap_1(X2,X3)) | ~m1_pre_topc(X3,X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)).
% 0.22/0.54  
% 0.22/0.54  cnf(u171,negated_conjecture,
% 0.22/0.54      v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1))).
% 0.22/0.54  
% 0.22/0.54  cnf(u157,negated_conjecture,
% 0.22/0.54      v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k6_partfun1(u1_struct_0(sK0)),sK1))).
% 0.22/0.54  
% 0.22/0.54  cnf(u71,axiom,
% 0.22/0.54      v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u100,negated_conjecture,
% 0.22/0.54      v1_funct_1(k6_partfun1(u1_struct_0(sK0)))).
% 0.22/0.54  
% 0.22/0.54  cnf(u168,negated_conjecture,
% 0.22/0.54      v1_funct_1(k7_tmap_1(k8_tmap_1(sK0,sK1),X2)) | ~v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(k8_tmap_1(sK0,sK1))).
% 0.22/0.54  
% 0.22/0.54  cnf(u89,axiom,
% 0.22/0.54      v1_funct_1(k7_tmap_1(X0,u1_struct_0(X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u285,axiom,
% 0.22/0.54      ~v1_funct_1(k3_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1))) | ~v2_pre_topc(X0) | ~m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | k9_tmap_1(X0,X1) = k3_struct_0(X0) | ~v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))).
% 0.22/0.54  
% 0.22/0.54  cnf(u109,negated_conjecture,
% 0.22/0.54      ~v1_xboole_0(u1_struct_0(sK0)) | ~l1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) | v2_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))).
% 0.22/0.54  
% 0.22/0.54  cnf(u177,negated_conjecture,
% 0.22/0.54      ~v1_xboole_0(u1_struct_0(sK0)) | ~l1_struct_0(k8_tmap_1(sK0,sK1)) | v2_struct_0(k8_tmap_1(sK0,sK1))).
% 0.22/0.54  
% 0.22/0.54  cnf(u55,axiom,
% 0.22/0.54      ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u210,negated_conjecture,
% 0.22/0.54      v2_struct_0(k8_tmap_1(sK0,sK1)) | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(sK1))).
% 0.22/0.54  
% 0.22/0.54  cnf(u223,negated_conjecture,
% 0.22/0.54      v2_struct_0(k8_tmap_1(sK0,sK1)) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(sK1)))).
% 0.22/0.54  
% 0.22/0.54  cnf(u239,negated_conjecture,
% 0.22/0.54      v2_struct_0(k8_tmap_1(sK0,sK1)) | u1_pre_topc(k6_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(sK1))) = k5_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(sK1))).
% 0.22/0.54  
% 0.22/0.54  cnf(u50,negated_conjecture,
% 0.22/0.54      ~v2_struct_0(sK1)).
% 0.22/0.54  
% 0.22/0.54  cnf(u47,negated_conjecture,
% 0.22/0.54      ~v2_struct_0(sK0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u53,axiom,
% 0.22/0.54      l1_struct_0(X0) | ~l1_pre_topc(X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u70,axiom,
% 0.22/0.54      l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u49,negated_conjecture,
% 0.22/0.54      l1_pre_topc(sK0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u107,negated_conjecture,
% 0.22/0.54      ~l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) | ~m1_pre_topc(X0,k6_tmap_1(sK0,u1_struct_0(sK1))) | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.22/0.54  
% 0.22/0.54  cnf(u170,negated_conjecture,
% 0.22/0.54      k5_tmap_1(sK0,u1_struct_0(sK1)) = u1_pre_topc(k8_tmap_1(sK0,sK1))).
% 0.22/0.54  
% 0.22/0.54  cnf(u121,negated_conjecture,
% 0.22/0.54      u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) = k5_tmap_1(sK0,u1_struct_0(sK1))).
% 0.22/0.54  
% 0.22/0.54  cnf(u164,negated_conjecture,
% 0.22/0.54      k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))).
% 0.22/0.54  
% 0.22/0.54  cnf(u95,negated_conjecture,
% 0.22/0.54      k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK1))).
% 0.22/0.54  
% 0.22/0.54  cnf(u165,negated_conjecture,
% 0.22/0.54      u1_struct_0(k8_tmap_1(sK0,sK1)) = u1_struct_0(sK0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u106,negated_conjecture,
% 0.22/0.54      u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))).
% 0.22/0.54  
% 0.22/0.54  cnf(u59,axiom,
% 0.22/0.54      k6_tmap_1(X0,sK2(X0,X1,X2)) != X2 | k8_tmap_1(X0,X1) = X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)).
% 0.22/0.54  
% 0.22/0.54  % (13204)# SZS output end Saturation.
% 0.22/0.54  % (13204)------------------------------
% 0.22/0.54  % (13204)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (13204)Termination reason: Satisfiable
% 0.22/0.54  
% 0.22/0.54  % (13204)Memory used [KB]: 6396
% 0.22/0.54  % (13204)Time elapsed: 0.131 s
% 0.22/0.54  % (13204)------------------------------
% 0.22/0.54  % (13204)------------------------------
% 0.22/0.54  % (13182)Success in time 0.182 s
%------------------------------------------------------------------------------
