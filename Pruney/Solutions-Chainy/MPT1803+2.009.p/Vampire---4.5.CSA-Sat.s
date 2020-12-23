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
% DateTime   : Thu Dec  3 13:19:37 EST 2020

% Result     : CounterSatisfiable 1.19s
% Output     : Saturation 1.19s
% Verified   : 
% Statistics : Number of clauses        :   85 (  85 expanded)
%              Number of leaves         :   85 (  85 expanded)
%              Depth                    :    0
%              Number of atoms          :  332 ( 332 expanded)
%              Number of equality atoms :   38 (  38 expanded)
%              Maximal clause size      :   10 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u271,negated_conjecture,
    ( r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) )).

cnf(u54,negated_conjecture,
    ( ~ r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),sK2) )).

cnf(u67,axiom,
    ( v1_pre_topc(k8_tmap_1(X0,X1))
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0) )).

cnf(u60,axiom,
    ( ~ v1_pre_topc(X2)
    | u1_struct_0(X1) = sK3(X0,X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | k8_tmap_1(X0,X1) = X2
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0) )).

cnf(u59,axiom,
    ( ~ v1_pre_topc(X2)
    | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | k8_tmap_1(X0,X1) = X2
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0) )).

cnf(u52,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) )).

cnf(u156,negated_conjecture,
    ( ~ m1_pre_topc(k8_tmap_1(sK0,sK1),X1)
    | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) )).

cnf(u158,negated_conjecture,
    ( ~ m1_pre_topc(k8_tmap_1(sK0,sK1),X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X3)
    | v2_struct_0(X3)
    | v1_funct_1(k7_tmap_1(X3,u1_struct_0(sK0))) )).

cnf(u104,negated_conjecture,
    ( ~ m1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)),X1)
    | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) )).

cnf(u109,negated_conjecture,
    ( ~ m1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)),X5)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X5)
    | v2_struct_0(X5)
    | v1_funct_1(k7_tmap_1(X5,u1_struct_0(sK0))) )).

cnf(u155,negated_conjecture,
    ( ~ m1_pre_topc(X0,k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u168,negated_conjecture,
    ( ~ m1_pre_topc(X4,k8_tmap_1(sK0,sK1))
    | r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X4)),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(k8_tmap_1(sK0,sK1),X4),k3_struct_0(k8_tmap_1(sK0,sK1)))
    | v2_struct_0(X4)
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | v2_struct_0(k8_tmap_1(sK0,sK1)) )).

cnf(u116,negated_conjecture,
    ( ~ m1_pre_topc(X0,sK0)
    | u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(X0))) = k5_tmap_1(sK0,u1_struct_0(X0)) )).

cnf(u126,negated_conjecture,
    ( ~ m1_pre_topc(X0,sK0)
    | v1_funct_2(k7_tmap_1(sK0,u1_struct_0(X0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0)))) )).

cnf(u136,negated_conjecture,
    ( ~ m1_pre_topc(X0,sK0)
    | m1_subset_1(k7_tmap_1(sK0,u1_struct_0(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0)))))) )).

cnf(u197,negated_conjecture,
    ( ~ m1_pre_topc(X0,sK0)
    | v2_struct_0(k8_tmap_1(sK0,sK1))
    | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(X0)) )).

cnf(u210,negated_conjecture,
    ( ~ m1_pre_topc(X0,sK0)
    | v2_struct_0(k8_tmap_1(sK0,sK1))
    | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(X0))) )).

cnf(u226,negated_conjecture,
    ( ~ m1_pre_topc(X0,sK0)
    | v2_struct_0(k8_tmap_1(sK0,sK1))
    | u1_pre_topc(k6_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(X0))) = k5_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(X0)) )).

cnf(u264,axiom,
    ( ~ m1_pre_topc(X2,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | r1_tmap_1(X2,k6_tmap_1(X0,u1_struct_0(X2)),k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),X3)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0) )).

cnf(u236,negated_conjecture,
    ( ~ m1_pre_topc(X1,X0)
    | k8_tmap_1(X0,X1) = k8_tmap_1(sK0,sK1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | m1_subset_1(sK3(X0,X1,k8_tmap_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(X0))) )).

cnf(u231,negated_conjecture,
    ( ~ m1_pre_topc(X1,X0)
    | k8_tmap_1(X0,X1) = k8_tmap_1(sK0,sK1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | u1_struct_0(X1) = sK3(X0,X1,k8_tmap_1(sK0,sK1)) )).

cnf(u149,axiom,
    ( ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0) )).

cnf(u146,axiom,
    ( ~ m1_pre_topc(X3,X2)
    | k8_tmap_1(X0,X1) = k8_tmap_1(X2,X3)
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | m1_subset_1(sK3(X0,X1,k8_tmap_1(X2,X3)),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X2) )).

cnf(u142,axiom,
    ( ~ m1_pre_topc(X3,X2)
    | k8_tmap_1(X2,X3) = k8_tmap_1(X1,X0)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | u1_struct_0(X0) = sK3(X1,X0,k8_tmap_1(X2,X3))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X2) )).

cnf(u114,axiom,
    ( ~ m1_pre_topc(X3,X2)
    | u1_pre_topc(k6_tmap_1(k8_tmap_1(X2,X3),X1)) = k5_tmap_1(k8_tmap_1(X2,X3),X1)
    | v2_struct_0(k8_tmap_1(X2,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k8_tmap_1(X2,X3))))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X2) )).

cnf(u98,axiom,
    ( ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))) )).

cnf(u87,axiom,
    ( ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,u1_struct_0(X1)) )).

cnf(u68,axiom,
    ( v2_pre_topc(k8_tmap_1(X0,X1))
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0) )).

cnf(u49,negated_conjecture,
    ( v2_pre_topc(sK0) )).

cnf(u108,negated_conjecture,
    ( ~ v2_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | v1_funct_1(k7_tmap_1(k6_tmap_1(sK0,u1_struct_0(sK1)),X4))
    | ~ l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) )).

cnf(u64,axiom,
    ( ~ v2_pre_topc(X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
    | v2_struct_0(X0) )).

cnf(u74,axiom,
    ( ~ v2_pre_topc(X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | v2_struct_0(X0) )).

cnf(u75,axiom,
    ( ~ v2_pre_topc(X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
    | v2_struct_0(X0) )).

cnf(u82,axiom,
    ( r1_funct_2(X0,X1,X2,X3,X5,X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_2(X5,X2,X3)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(X5,X0,X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X1) )).

cnf(u177,negated_conjecture,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k3_struct_0(sK0)) )).

cnf(u66,axiom,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0))
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0) )).

cnf(u76,axiom,
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

cnf(u53,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) )).

cnf(u170,negated_conjecture,
    ( m1_subset_1(k9_tmap_1(k8_tmap_1(sK0,sK1),X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X6)))))
    | ~ m1_pre_topc(X6,k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | v2_struct_0(k8_tmap_1(sK0,sK1)) )).

cnf(u181,negated_conjecture,
    ( m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )).

cnf(u72,axiom,
    ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0) )).

cnf(u139,negated_conjecture,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )).

cnf(u263,negated_conjecture,
    ( m1_subset_1(k7_tmap_1(k8_tmap_1(sK0,sK1),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(k8_tmap_1(sK0,sK1),X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(k8_tmap_1(sK0,sK1)) )).

cnf(u134,axiom,
    ( m1_subset_1(k7_tmap_1(k8_tmap_1(X2,X3),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k8_tmap_1(X2,X3)),u1_struct_0(k6_tmap_1(k8_tmap_1(X2,X3),X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k8_tmap_1(X2,X3))))
    | v2_struct_0(k8_tmap_1(X2,X3))
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X2) )).

cnf(u56,axiom,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0) )).

cnf(u258,negated_conjecture,
    ( ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | k9_tmap_1(sK0,sK1) = k3_struct_0(sK0)
    | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k3_struct_0(sK0))
    | ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK0)) )).

cnf(u113,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_pre_topc(k6_tmap_1(sK0,X0)) = k5_tmap_1(sK0,X0) )).

cnf(u123,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_funct_2(k7_tmap_1(sK0,X0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X0))) )).

cnf(u133,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k7_tmap_1(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X0))))) )).

cnf(u195,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK1),X0)
    | v2_struct_0(k8_tmap_1(sK0,sK1)) )).

cnf(u208,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(k8_tmap_1(sK0,sK1),X0))
    | v2_struct_0(k8_tmap_1(sK0,sK1)) )).

cnf(u224,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_pre_topc(k6_tmap_1(k8_tmap_1(sK0,sK1),X0)) = k5_tmap_1(k8_tmap_1(sK0,sK1),X0)
    | v2_struct_0(k8_tmap_1(sK0,sK1)) )).

cnf(u73,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v1_funct_1(k7_tmap_1(X0,X1))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0) )).

cnf(u62,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0) )).

cnf(u63,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0) )).

cnf(u242,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(k8_tmap_1(sK0,sK1),X0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(k8_tmap_1(sK0,sK1),X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(k8_tmap_1(sK0,sK1)) )).

cnf(u124,axiom,
    ( v1_funct_2(k7_tmap_1(k8_tmap_1(X2,X3),X1),u1_struct_0(k8_tmap_1(X2,X3)),u1_struct_0(k6_tmap_1(k8_tmap_1(X2,X3),X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k8_tmap_1(X2,X3))))
    | v2_struct_0(k8_tmap_1(X2,X3))
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X2) )).

cnf(u129,negated_conjecture,
    ( v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) )).

cnf(u185,negated_conjecture,
    ( v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) )).

cnf(u169,negated_conjecture,
    ( v1_funct_2(k9_tmap_1(k8_tmap_1(sK0,sK1),X5),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X5)))
    | ~ m1_pre_topc(X5,k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | v2_struct_0(k8_tmap_1(sK0,sK1)) )).

cnf(u71,axiom,
    ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0) )).

cnf(u96,negated_conjecture,
    ( v1_funct_1(k6_partfun1(u1_struct_0(sK0))) )).

cnf(u157,negated_conjecture,
    ( v1_funct_1(k7_tmap_1(k8_tmap_1(sK0,sK1),X2))
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(k8_tmap_1(sK0,sK1)) )).

cnf(u85,axiom,
    ( v1_funct_1(k7_tmap_1(X0,u1_struct_0(X1)))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ m1_pre_topc(X1,X0) )).

cnf(u70,axiom,
    ( v1_funct_1(k9_tmap_1(X0,X1))
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0) )).

cnf(u256,axiom,
    ( ~ v1_funct_1(k3_struct_0(X0))
    | k9_tmap_1(X0,X1) = k3_struct_0(X0)
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1))) )).

cnf(u105,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | v2_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) )).

cnf(u165,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(k8_tmap_1(sK0,sK1))
    | v2_struct_0(k8_tmap_1(sK0,sK1)) )).

cnf(u57,axiom,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) )).

cnf(u198,negated_conjecture,
    ( v2_struct_0(k8_tmap_1(sK0,sK1))
    | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(sK1)) )).

cnf(u211,negated_conjecture,
    ( v2_struct_0(k8_tmap_1(sK0,sK1))
    | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(sK1))) )).

cnf(u227,negated_conjecture,
    ( v2_struct_0(k8_tmap_1(sK0,sK1))
    | u1_pre_topc(k6_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(sK1))) = k5_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(sK1)) )).

cnf(u51,negated_conjecture,
    ( ~ v2_struct_0(sK1) )).

cnf(u48,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u55,axiom,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) )).

cnf(u69,axiom,
    ( l1_pre_topc(k8_tmap_1(X0,X1))
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0) )).

cnf(u50,negated_conjecture,
    ( l1_pre_topc(sK0) )).

cnf(u103,negated_conjecture,
    ( ~ l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ m1_pre_topc(X0,k6_tmap_1(sK0,u1_struct_0(sK1)))
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u159,negated_conjecture,
    ( k5_tmap_1(sK0,u1_struct_0(sK1)) = u1_pre_topc(k8_tmap_1(sK0,sK1)) )).

cnf(u117,negated_conjecture,
    ( u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) = k5_tmap_1(sK0,u1_struct_0(sK1)) )).

cnf(u153,negated_conjecture,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) )).

cnf(u91,negated_conjecture,
    ( k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK1)) )).

cnf(u154,negated_conjecture,
    ( u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) )).

cnf(u102,negated_conjecture,
    ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) )).

cnf(u61,axiom,
    ( k6_tmap_1(X0,sK3(X0,X1,X2)) != X2
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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:37:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.45  % (4800)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.46  % (4800)Refutation not found, incomplete strategy% (4800)------------------------------
% 0.20/0.46  % (4800)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (4800)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (4800)Memory used [KB]: 6140
% 0.20/0.46  % (4800)Time elapsed: 0.062 s
% 0.20/0.46  % (4800)------------------------------
% 0.20/0.46  % (4800)------------------------------
% 0.20/0.46  % (4808)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.47  % (4808)Refutation not found, incomplete strategy% (4808)------------------------------
% 0.20/0.47  % (4808)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (4808)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (4808)Memory used [KB]: 6268
% 0.20/0.47  % (4808)Time elapsed: 0.074 s
% 0.20/0.47  % (4808)------------------------------
% 0.20/0.47  % (4808)------------------------------
% 0.20/0.47  % (4820)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.50  % (4795)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.50  % (4799)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.50  % (4817)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.50  % (4816)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.50  % (4813)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.50  % (4807)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.50  % (4795)Refutation not found, incomplete strategy% (4795)------------------------------
% 0.20/0.50  % (4795)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (4798)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.50  % (4795)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (4795)Memory used [KB]: 10618
% 0.20/0.50  % (4795)Time elapsed: 0.084 s
% 0.20/0.50  % (4795)------------------------------
% 0.20/0.50  % (4795)------------------------------
% 0.20/0.51  % (4796)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.19/0.51  % (4802)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.19/0.51  % (4806)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.19/0.51  % (4797)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.19/0.51  % (4798)Refutation not found, incomplete strategy% (4798)------------------------------
% 1.19/0.51  % (4798)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.51  % (4798)Termination reason: Refutation not found, incomplete strategy
% 1.19/0.51  
% 1.19/0.51  % (4798)Memory used [KB]: 6396
% 1.19/0.51  % (4798)Time elapsed: 0.097 s
% 1.19/0.51  % (4798)------------------------------
% 1.19/0.51  % (4798)------------------------------
% 1.19/0.51  % (4817)Refutation not found, incomplete strategy% (4817)------------------------------
% 1.19/0.51  % (4817)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.51  % (4817)Termination reason: Refutation not found, incomplete strategy
% 1.19/0.51  
% 1.19/0.51  % (4817)Memory used [KB]: 10874
% 1.19/0.51  % (4817)Time elapsed: 0.084 s
% 1.19/0.51  % (4817)------------------------------
% 1.19/0.51  % (4817)------------------------------
% 1.19/0.51  % (4811)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.19/0.51  % (4810)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.19/0.51  % (4815)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.19/0.51  % (4796)Refutation not found, incomplete strategy% (4796)------------------------------
% 1.19/0.51  % (4796)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.51  % (4796)Termination reason: Refutation not found, incomplete strategy
% 1.19/0.51  
% 1.19/0.51  % (4796)Memory used [KB]: 10874
% 1.19/0.51  % (4796)Time elapsed: 0.097 s
% 1.19/0.51  % (4796)------------------------------
% 1.19/0.51  % (4796)------------------------------
% 1.19/0.51  % (4802)Refutation not found, incomplete strategy% (4802)------------------------------
% 1.19/0.51  % (4802)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.51  % (4802)Termination reason: Refutation not found, incomplete strategy
% 1.19/0.51  
% 1.19/0.51  % (4802)Memory used [KB]: 1791
% 1.19/0.51  % (4802)Time elapsed: 0.097 s
% 1.19/0.51  % (4802)------------------------------
% 1.19/0.51  % (4802)------------------------------
% 1.19/0.52  % (4809)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.19/0.52  % SZS status CounterSatisfiable for theBenchmark
% 1.19/0.52  % (4816)# SZS output start Saturation.
% 1.19/0.52  cnf(u271,negated_conjecture,
% 1.19/0.52      r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),X0) | ~m1_subset_1(X0,u1_struct_0(sK1))).
% 1.19/0.52  
% 1.19/0.52  cnf(u54,negated_conjecture,
% 1.19/0.52      ~r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),sK2)).
% 1.19/0.52  
% 1.19/0.52  cnf(u67,axiom,
% 1.19/0.52      v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)).
% 1.19/0.52  
% 1.19/0.52  cnf(u60,axiom,
% 1.19/0.52      ~v1_pre_topc(X2) | u1_struct_0(X1) = sK3(X0,X1,X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | k8_tmap_1(X0,X1) = X2 | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)).
% 1.19/0.52  
% 1.19/0.52  cnf(u59,axiom,
% 1.19/0.52      ~v1_pre_topc(X2) | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | k8_tmap_1(X0,X1) = X2 | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)).
% 1.19/0.52  
% 1.19/0.52  cnf(u52,negated_conjecture,
% 1.19/0.52      m1_pre_topc(sK1,sK0)).
% 1.19/0.52  
% 1.19/0.52  cnf(u156,negated_conjecture,
% 1.19/0.52      ~m1_pre_topc(k8_tmap_1(sK0,sK1),X1) | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1)).
% 1.19/0.52  
% 1.19/0.52  cnf(u158,negated_conjecture,
% 1.19/0.52      ~m1_pre_topc(k8_tmap_1(sK0,sK1),X3) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | v1_funct_1(k7_tmap_1(X3,u1_struct_0(sK0)))).
% 1.19/0.52  
% 1.19/0.52  cnf(u104,negated_conjecture,
% 1.19/0.52      ~m1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)),X1) | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1)).
% 1.19/0.52  
% 1.19/0.52  cnf(u109,negated_conjecture,
% 1.19/0.52      ~m1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)),X5) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5) | v1_funct_1(k7_tmap_1(X5,u1_struct_0(sK0)))).
% 1.19/0.52  
% 1.19/0.52  cnf(u155,negated_conjecture,
% 1.19/0.52      ~m1_pre_topc(X0,k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.19/0.52  
% 1.19/0.52  cnf(u168,negated_conjecture,
% 1.19/0.52      ~m1_pre_topc(X4,k8_tmap_1(sK0,sK1)) | r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X4)),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(k8_tmap_1(sK0,sK1),X4),k3_struct_0(k8_tmap_1(sK0,sK1))) | v2_struct_0(X4) | ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~v2_pre_topc(k8_tmap_1(sK0,sK1)) | v2_struct_0(k8_tmap_1(sK0,sK1))).
% 1.19/0.52  
% 1.19/0.52  cnf(u116,negated_conjecture,
% 1.19/0.52      ~m1_pre_topc(X0,sK0) | u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(X0))) = k5_tmap_1(sK0,u1_struct_0(X0))).
% 1.19/0.52  
% 1.19/0.52  cnf(u126,negated_conjecture,
% 1.19/0.52      ~m1_pre_topc(X0,sK0) | v1_funct_2(k7_tmap_1(sK0,u1_struct_0(X0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0))))).
% 1.19/0.52  
% 1.19/0.52  cnf(u136,negated_conjecture,
% 1.19/0.52      ~m1_pre_topc(X0,sK0) | m1_subset_1(k7_tmap_1(sK0,u1_struct_0(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0))))))).
% 1.19/0.52  
% 1.19/0.52  cnf(u197,negated_conjecture,
% 1.19/0.52      ~m1_pre_topc(X0,sK0) | v2_struct_0(k8_tmap_1(sK0,sK1)) | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(X0))).
% 1.19/0.52  
% 1.19/0.52  cnf(u210,negated_conjecture,
% 1.19/0.52      ~m1_pre_topc(X0,sK0) | v2_struct_0(k8_tmap_1(sK0,sK1)) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(X0)))).
% 1.19/0.52  
% 1.19/0.52  cnf(u226,negated_conjecture,
% 1.19/0.52      ~m1_pre_topc(X0,sK0) | v2_struct_0(k8_tmap_1(sK0,sK1)) | u1_pre_topc(k6_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(X0))) = k5_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(X0))).
% 1.19/0.52  
% 1.19/0.52  cnf(u264,axiom,
% 1.19/0.52      ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,u1_struct_0(X2)) | r1_tmap_1(X2,k6_tmap_1(X0,u1_struct_0(X2)),k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),X3) | v2_struct_0(X2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)).
% 1.19/0.52  
% 1.19/0.52  cnf(u236,negated_conjecture,
% 1.19/0.52      ~m1_pre_topc(X1,X0) | k8_tmap_1(X0,X1) = k8_tmap_1(sK0,sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | m1_subset_1(sK3(X0,X1,k8_tmap_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(X0)))).
% 1.19/0.52  
% 1.19/0.52  cnf(u231,negated_conjecture,
% 1.19/0.52      ~m1_pre_topc(X1,X0) | k8_tmap_1(X0,X1) = k8_tmap_1(sK0,sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | u1_struct_0(X1) = sK3(X0,X1,k8_tmap_1(sK0,sK1))).
% 1.19/0.52  
% 1.19/0.52  cnf(u149,axiom,
% 1.19/0.52      ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | v2_struct_0(X0) | ~v2_pre_topc(X0)).
% 1.19/0.52  
% 1.19/0.52  cnf(u146,axiom,
% 1.19/0.52      ~m1_pre_topc(X3,X2) | k8_tmap_1(X0,X1) = k8_tmap_1(X2,X3) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | m1_subset_1(sK3(X0,X1,k8_tmap_1(X2,X3)),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)).
% 1.19/0.52  
% 1.19/0.52  cnf(u142,axiom,
% 1.19/0.52      ~m1_pre_topc(X3,X2) | k8_tmap_1(X2,X3) = k8_tmap_1(X1,X0) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | u1_struct_0(X0) = sK3(X1,X0,k8_tmap_1(X2,X3)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)).
% 1.19/0.52  
% 1.19/0.52  cnf(u114,axiom,
% 1.19/0.52      ~m1_pre_topc(X3,X2) | u1_pre_topc(k6_tmap_1(k8_tmap_1(X2,X3),X1)) = k5_tmap_1(k8_tmap_1(X2,X3),X1) | v2_struct_0(k8_tmap_1(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k8_tmap_1(X2,X3)))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)).
% 1.19/0.52  
% 1.19/0.52  cnf(u98,axiom,
% 1.19/0.52      ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1)))).
% 1.19/0.52  
% 1.19/0.52  cnf(u87,axiom,
% 1.19/0.52      ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,u1_struct_0(X1))).
% 1.19/0.52  
% 1.19/0.52  cnf(u68,axiom,
% 1.19/0.52      v2_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)).
% 1.19/0.52  
% 1.19/0.52  cnf(u49,negated_conjecture,
% 1.19/0.52      v2_pre_topc(sK0)).
% 1.19/0.52  
% 1.19/0.52  cnf(u108,negated_conjecture,
% 1.19/0.52      ~v2_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) | v1_funct_1(k7_tmap_1(k6_tmap_1(sK0,u1_struct_0(sK1)),X4)) | ~l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))).
% 1.19/0.52  
% 1.19/0.52  cnf(u64,axiom,
% 1.19/0.52      ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) | v2_struct_0(X0)).
% 1.19/0.52  
% 1.19/0.52  cnf(u74,axiom,
% 1.19/0.52      ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | v2_struct_0(X0)).
% 1.19/0.52  
% 1.19/0.52  cnf(u75,axiom,
% 1.19/0.52      ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | v2_struct_0(X0)).
% 1.19/0.52  
% 1.19/0.52  cnf(u82,axiom,
% 1.19/0.52      r1_funct_2(X0,X1,X2,X3,X5,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X5,X0,X1) | v1_xboole_0(X3) | v1_xboole_0(X1)).
% 1.19/0.52  
% 1.19/0.52  cnf(u177,negated_conjecture,
% 1.19/0.52      r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k3_struct_0(sK0))).
% 1.19/0.52  
% 1.19/0.52  cnf(u66,axiom,
% 1.19/0.52      r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)).
% 1.19/0.52  
% 1.19/0.52  cnf(u76,axiom,
% 1.19/0.52      ~r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 = X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)).
% 1.19/0.52  
% 1.19/0.52  cnf(u53,negated_conjecture,
% 1.19/0.52      m1_subset_1(sK2,u1_struct_0(sK1))).
% 1.19/0.52  
% 1.19/0.52  cnf(u170,negated_conjecture,
% 1.19/0.52      m1_subset_1(k9_tmap_1(k8_tmap_1(sK0,sK1),X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X6))))) | ~m1_pre_topc(X6,k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~v2_pre_topc(k8_tmap_1(sK0,sK1)) | v2_struct_0(k8_tmap_1(sK0,sK1))).
% 1.19/0.52  
% 1.19/0.52  cnf(u181,negated_conjecture,
% 1.19/0.52      m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))).
% 1.19/0.52  
% 1.19/0.52  cnf(u72,axiom,
% 1.19/0.52      m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)).
% 1.19/0.52  
% 1.19/0.52  cnf(u139,negated_conjecture,
% 1.19/0.52      m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))).
% 1.19/0.52  
% 1.19/0.52  cnf(u263,negated_conjecture,
% 1.19/0.52      m1_subset_1(k7_tmap_1(k8_tmap_1(sK0,sK1),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(k8_tmap_1(sK0,sK1),X0))))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(k8_tmap_1(sK0,sK1))).
% 1.19/0.52  
% 1.19/0.52  cnf(u134,axiom,
% 1.19/0.52      m1_subset_1(k7_tmap_1(k8_tmap_1(X2,X3),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k8_tmap_1(X2,X3)),u1_struct_0(k6_tmap_1(k8_tmap_1(X2,X3),X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k8_tmap_1(X2,X3)))) | v2_struct_0(k8_tmap_1(X2,X3)) | ~m1_pre_topc(X3,X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)).
% 1.19/0.52  
% 1.19/0.52  cnf(u56,axiom,
% 1.19/0.52      m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)).
% 1.19/0.52  
% 1.19/0.52  cnf(u258,negated_conjecture,
% 1.19/0.52      ~m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | k9_tmap_1(sK0,sK1) = k3_struct_0(sK0) | ~v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k3_struct_0(sK0)) | ~v1_funct_1(k9_tmap_1(sK0,sK1)) | v1_xboole_0(u1_struct_0(sK0))).
% 1.19/0.52  
% 1.19/0.52  cnf(u113,negated_conjecture,
% 1.19/0.52      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_pre_topc(k6_tmap_1(sK0,X0)) = k5_tmap_1(sK0,X0)).
% 1.19/0.52  
% 1.19/0.52  cnf(u123,negated_conjecture,
% 1.19/0.52      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_funct_2(k7_tmap_1(sK0,X0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X0)))).
% 1.19/0.52  
% 1.19/0.52  cnf(u133,negated_conjecture,
% 1.19/0.52      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k7_tmap_1(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X0)))))).
% 1.19/0.52  
% 1.19/0.52  cnf(u195,negated_conjecture,
% 1.19/0.52      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK1),X0) | v2_struct_0(k8_tmap_1(sK0,sK1))).
% 1.19/0.52  
% 1.19/0.52  cnf(u208,negated_conjecture,
% 1.19/0.52      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(k8_tmap_1(sK0,sK1),X0)) | v2_struct_0(k8_tmap_1(sK0,sK1))).
% 1.19/0.52  
% 1.19/0.52  cnf(u224,negated_conjecture,
% 1.19/0.52      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_pre_topc(k6_tmap_1(k8_tmap_1(sK0,sK1),X0)) = k5_tmap_1(k8_tmap_1(sK0,sK1),X0) | v2_struct_0(k8_tmap_1(sK0,sK1))).
% 1.19/0.52  
% 1.19/0.52  cnf(u73,axiom,
% 1.19/0.52      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_funct_1(k7_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)).
% 1.19/0.52  
% 1.19/0.52  cnf(u62,axiom,
% 1.19/0.52      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)).
% 1.19/0.52  
% 1.19/0.52  cnf(u63,axiom,
% 1.19/0.52      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)).
% 1.19/0.52  
% 1.19/0.52  cnf(u242,negated_conjecture,
% 1.19/0.52      v1_funct_2(k7_tmap_1(k8_tmap_1(sK0,sK1),X0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(k8_tmap_1(sK0,sK1),X0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(k8_tmap_1(sK0,sK1))).
% 1.19/0.52  
% 1.19/0.52  cnf(u124,axiom,
% 1.19/0.52      v1_funct_2(k7_tmap_1(k8_tmap_1(X2,X3),X1),u1_struct_0(k8_tmap_1(X2,X3)),u1_struct_0(k6_tmap_1(k8_tmap_1(X2,X3),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k8_tmap_1(X2,X3)))) | v2_struct_0(k8_tmap_1(X2,X3)) | ~m1_pre_topc(X3,X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)).
% 1.19/0.52  
% 1.19/0.52  cnf(u129,negated_conjecture,
% 1.19/0.52      v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))).
% 1.19/0.52  
% 1.19/0.52  cnf(u185,negated_conjecture,
% 1.19/0.52      v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))).
% 1.19/0.52  
% 1.19/0.52  cnf(u169,negated_conjecture,
% 1.19/0.52      v1_funct_2(k9_tmap_1(k8_tmap_1(sK0,sK1),X5),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X5))) | ~m1_pre_topc(X5,k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~v2_pre_topc(k8_tmap_1(sK0,sK1)) | v2_struct_0(k8_tmap_1(sK0,sK1))).
% 1.19/0.52  
% 1.19/0.52  cnf(u71,axiom,
% 1.19/0.52      v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)).
% 1.19/0.52  
% 1.19/0.52  cnf(u96,negated_conjecture,
% 1.19/0.52      v1_funct_1(k6_partfun1(u1_struct_0(sK0)))).
% 1.19/0.52  
% 1.19/0.52  cnf(u157,negated_conjecture,
% 1.19/0.52      v1_funct_1(k7_tmap_1(k8_tmap_1(sK0,sK1),X2)) | ~v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(k8_tmap_1(sK0,sK1))).
% 1.19/0.52  
% 1.19/0.52  cnf(u85,axiom,
% 1.19/0.52      v1_funct_1(k7_tmap_1(X0,u1_struct_0(X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,X0)).
% 1.19/0.52  
% 1.19/0.52  cnf(u70,axiom,
% 1.19/0.52      v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)).
% 1.19/0.52  
% 1.19/0.52  cnf(u256,axiom,
% 1.19/0.52      ~v1_funct_1(k3_struct_0(X0)) | k9_tmap_1(X0,X1) = k3_struct_0(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | ~m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X1) | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))).
% 1.19/0.52  
% 1.19/0.52  cnf(u105,negated_conjecture,
% 1.19/0.52      ~v1_xboole_0(u1_struct_0(sK0)) | ~l1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) | v2_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))).
% 1.19/0.52  
% 1.19/0.52  cnf(u165,negated_conjecture,
% 1.19/0.52      ~v1_xboole_0(u1_struct_0(sK0)) | ~l1_struct_0(k8_tmap_1(sK0,sK1)) | v2_struct_0(k8_tmap_1(sK0,sK1))).
% 1.19/0.52  
% 1.19/0.52  cnf(u57,axiom,
% 1.19/0.52      ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)).
% 1.19/0.52  
% 1.19/0.52  cnf(u198,negated_conjecture,
% 1.19/0.52      v2_struct_0(k8_tmap_1(sK0,sK1)) | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(sK1))).
% 1.19/0.52  
% 1.19/0.52  cnf(u211,negated_conjecture,
% 1.19/0.52      v2_struct_0(k8_tmap_1(sK0,sK1)) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(sK1)))).
% 1.19/0.52  
% 1.19/0.52  cnf(u227,negated_conjecture,
% 1.19/0.52      v2_struct_0(k8_tmap_1(sK0,sK1)) | u1_pre_topc(k6_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(sK1))) = k5_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(sK1))).
% 1.19/0.52  
% 1.19/0.52  cnf(u51,negated_conjecture,
% 1.19/0.52      ~v2_struct_0(sK1)).
% 1.19/0.52  
% 1.19/0.52  cnf(u48,negated_conjecture,
% 1.19/0.52      ~v2_struct_0(sK0)).
% 1.19/0.52  
% 1.19/0.52  cnf(u55,axiom,
% 1.19/0.52      l1_struct_0(X0) | ~l1_pre_topc(X0)).
% 1.19/0.52  
% 1.19/0.52  cnf(u69,axiom,
% 1.19/0.52      l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)).
% 1.19/0.52  
% 1.19/0.52  cnf(u50,negated_conjecture,
% 1.19/0.52      l1_pre_topc(sK0)).
% 1.19/0.52  
% 1.19/0.52  cnf(u103,negated_conjecture,
% 1.19/0.52      ~l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) | ~m1_pre_topc(X0,k6_tmap_1(sK0,u1_struct_0(sK1))) | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.19/0.52  
% 1.19/0.52  cnf(u159,negated_conjecture,
% 1.19/0.52      k5_tmap_1(sK0,u1_struct_0(sK1)) = u1_pre_topc(k8_tmap_1(sK0,sK1))).
% 1.19/0.52  
% 1.19/0.52  cnf(u117,negated_conjecture,
% 1.19/0.52      u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) = k5_tmap_1(sK0,u1_struct_0(sK1))).
% 1.19/0.52  
% 1.19/0.52  cnf(u153,negated_conjecture,
% 1.19/0.52      k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))).
% 1.19/0.52  
% 1.19/0.52  cnf(u91,negated_conjecture,
% 1.19/0.52      k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK1))).
% 1.19/0.52  
% 1.19/0.52  cnf(u154,negated_conjecture,
% 1.19/0.52      u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))).
% 1.19/0.52  
% 1.19/0.52  cnf(u102,negated_conjecture,
% 1.19/0.52      u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))).
% 1.19/0.52  
% 1.19/0.52  cnf(u61,axiom,
% 1.19/0.52      k6_tmap_1(X0,sK3(X0,X1,X2)) != X2 | k8_tmap_1(X0,X1) = X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)).
% 1.19/0.52  
% 1.19/0.52  % (4816)# SZS output end Saturation.
% 1.19/0.52  % (4816)------------------------------
% 1.19/0.52  % (4816)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.52  % (4816)Termination reason: Satisfiable
% 1.19/0.52  
% 1.19/0.52  % (4816)Memory used [KB]: 6396
% 1.19/0.52  % (4816)Time elapsed: 0.114 s
% 1.19/0.52  % (4816)------------------------------
% 1.19/0.52  % (4816)------------------------------
% 1.19/0.52  % (4794)Success in time 0.161 s
%------------------------------------------------------------------------------
