%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:20 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   76 (  76 expanded)
%              Number of leaves         :   76 (  76 expanded)
%              Depth                    :    0
%              Number of atoms          :  524 ( 524 expanded)
%              Number of equality atoms :   40 (  40 expanded)
%              Maximal clause size      :   16 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u48,axiom,
    ( v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v5_pre_topc(X4,X2,X1)
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
    | ~ v1_funct_1(X4)
    | ~ m1_pre_topc(X3,X0)
    | v2_struct_0(X3)
    | ~ m1_pre_topc(X2,X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0) )).

cnf(u43,axiom,
    ( v5_pre_topc(k3_struct_0(X0),X0,X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0) )).

cnf(u129,negated_conjecture,
    ( ~ v5_pre_topc(k4_tmap_1(sK0,sK0),sK0,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_subset_1(k4_tmap_1(sK0,sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | v5_pre_topc(k2_tmap_1(sK0,sK0,k4_tmap_1(sK0,sK0),sK0),sK0,sK0)
    | ~ v1_funct_2(k4_tmap_1(sK0,sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK0))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) )).

cnf(u130,negated_conjecture,
    ( ~ v5_pre_topc(k4_tmap_1(sK0,sK0),sK0,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_subset_1(k4_tmap_1(sK0,sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | v1_funct_2(k2_tmap_1(sK0,sK0,k4_tmap_1(sK0,sK0),sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_2(k4_tmap_1(sK0,sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK0))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) )).

cnf(u122,negated_conjecture,
    ( ~ v5_pre_topc(k4_tmap_1(sK0,sK0),sK0,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_subset_1(k4_tmap_1(sK0,sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | v5_pre_topc(k2_tmap_1(sK0,sK0,k4_tmap_1(sK0,sK0),sK1),sK1,sK0)
    | ~ v1_funct_2(k4_tmap_1(sK0,sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK0))
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) )).

cnf(u123,negated_conjecture,
    ( ~ v5_pre_topc(k4_tmap_1(sK0,sK0),sK0,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_subset_1(k4_tmap_1(sK0,sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | v1_funct_2(k2_tmap_1(sK0,sK0,k4_tmap_1(sK0,sK0),sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_2(k4_tmap_1(sK0,sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK0))
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) )).

cnf(u136,negated_conjecture,
    ( ~ v5_pre_topc(k4_tmap_1(sK0,X0),X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X0,sK0)
    | v2_struct_0(X0)
    | ~ v1_funct_1(k4_tmap_1(sK0,X0))
    | ~ v1_funct_2(k4_tmap_1(sK0,X0),u1_struct_0(X0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(X1,X0)
    | v1_funct_1(k3_tmap_1(sK0,sK0,X0,X1,k4_tmap_1(sK0,X0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) )).

cnf(u141,negated_conjecture,
    ( ~ v5_pre_topc(k4_tmap_1(sK0,X0),X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X0,sK0)
    | v2_struct_0(X0)
    | ~ v1_funct_1(k4_tmap_1(sK0,X0))
    | ~ v1_funct_2(k4_tmap_1(sK0,X0),u1_struct_0(X0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(X1,X0)
    | m1_subset_1(k3_tmap_1(sK0,sK0,X0,X1,k4_tmap_1(sK0,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) )).

cnf(u38,negated_conjecture,
    ( ~ v5_pre_topc(k4_tmap_1(sK0,sK1),sK1,sK0)
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1)) )).

cnf(u40,axiom,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) )).

cnf(u37,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) )).

cnf(u73,negated_conjecture,
    ( ~ m1_pre_topc(sK0,sK0)
    | ~ v1_funct_1(k4_tmap_1(sK0,sK0))
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(X0,sK0)
    | k2_tmap_1(sK0,sK0,k4_tmap_1(sK0,sK0),X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k4_tmap_1(sK0,sK0),u1_struct_0(X0))
    | ~ v1_funct_2(k4_tmap_1(sK0,sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) )).

cnf(u78,negated_conjecture,
    ( ~ m1_pre_topc(sK0,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | k2_tmap_1(sK0,sK0,k4_tmap_1(sK0,sK0),X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k4_tmap_1(sK0,sK0),u1_struct_0(X0))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) )).

cnf(u82,negated_conjecture,
    ( ~ m1_pre_topc(sK0,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k2_tmap_1(sK0,sK0,k4_tmap_1(sK0,sK0),X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k4_tmap_1(sK0,sK0),u1_struct_0(X0)) )).

cnf(u57,negated_conjecture,
    ( ~ m1_pre_topc(X0,sK1)
    | m1_pre_topc(X0,sK0) )).

cnf(u111,negated_conjecture,
    ( ~ m1_pre_topc(X0,sK1)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(X0,sK0)
    | k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X0)) )).

cnf(u56,negated_conjecture,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,X0)
    | m1_pre_topc(X1,sK0) )).

cnf(u61,negated_conjecture,
    ( ~ m1_pre_topc(X0,sK0)
    | k4_tmap_1(sK0,X0) = k2_tmap_1(sK0,sK0,k3_struct_0(sK0),X0)
    | v2_struct_0(sK0) )).

cnf(u87,negated_conjecture,
    ( ~ m1_pre_topc(X0,sK0)
    | v2_struct_0(sK0)
    | k2_tmap_1(sK0,sK0,k4_tmap_1(sK0,sK0),X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k4_tmap_1(sK0,sK0),u1_struct_0(X0)) )).

cnf(u109,negated_conjecture,
    ( ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | k3_tmap_1(sK0,sK0,X1,X0,k4_tmap_1(sK0,X1)) = k2_partfun1(u1_struct_0(X1),u1_struct_0(sK0),k4_tmap_1(sK0,X1),u1_struct_0(X0)) )).

cnf(u114,negated_conjecture,
    ( ~ m1_pre_topc(X0,sK0)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k4_tmap_1(sK0,sK0),u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK0,X0,k4_tmap_1(sK0,sK0))
    | v2_struct_0(sK0) )).

cnf(u54,axiom,
    ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0) )).

cnf(u96,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X2,sK0)
    | ~ v1_funct_2(X0,u1_struct_0(X2),u1_struct_0(sK0))
    | ~ v1_funct_1(X0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(X1,X2)
    | k3_tmap_1(sK0,sK0,X2,X1,X0) = k2_partfun1(u1_struct_0(X2),u1_struct_0(sK0),X0,u1_struct_0(X1)) )).

cnf(u134,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
    | ~ v1_funct_1(X0)
    | ~ m1_pre_topc(X2,sK0)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X1)
    | ~ v5_pre_topc(X0,X1,sK0)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(X2,X1)
    | v1_funct_1(k3_tmap_1(sK0,sK0,X1,X2,X0)) )).

cnf(u139,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
    | ~ v1_funct_1(X0)
    | ~ m1_pre_topc(X2,sK0)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X1)
    | ~ v5_pre_topc(X0,X1,sK0)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(X2,X1)
    | m1_subset_1(k3_tmap_1(sK0,sK0,X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) )).

cnf(u71,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(X0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(X1,sK0)
    | k2_tmap_1(sK0,sK0,X0,X1) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),X0,u1_struct_0(X1)) )).

cnf(u47,axiom,
    ( v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v5_pre_topc(X4,X2,X1)
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
    | ~ v1_funct_1(X4)
    | ~ m1_pre_topc(X3,X0)
    | v2_struct_0(X3)
    | ~ m1_pre_topc(X2,X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0) )).

cnf(u53,axiom,
    ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0) )).

cnf(u42,axiom,
    ( v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0) )).

cnf(u100,negated_conjecture,
    ( ~ v1_funct_2(k4_tmap_1(sK0,X0),u1_struct_0(X0),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_tmap_1(sK0,X0))
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(X1,X0)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(sK0),k4_tmap_1(sK0,X0),u1_struct_0(X1)) = k3_tmap_1(sK0,sK0,X0,X1,k4_tmap_1(sK0,X0))
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0) )).

cnf(u76,negated_conjecture,
    ( ~ v1_funct_2(k4_tmap_1(sK0,sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(X0,sK0)
    | k2_tmap_1(sK0,sK0,k4_tmap_1(sK0,sK0),X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k4_tmap_1(sK0,sK0),u1_struct_0(X0))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) )).

cnf(u52,axiom,
    ( v1_funct_1(k4_tmap_1(X0,X1))
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0) )).

cnf(u41,axiom,
    ( v1_funct_1(k3_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0) )).

cnf(u105,negated_conjecture,
    ( ~ v1_funct_1(k4_tmap_1(sK0,X1))
    | k3_tmap_1(sK0,sK0,X1,X0,k4_tmap_1(sK0,X1)) = k2_partfun1(u1_struct_0(X1),u1_struct_0(sK0),k4_tmap_1(sK0,X1),u1_struct_0(X0))
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(X0,X1) )).

cnf(u80,negated_conjecture,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK0))
    | k2_tmap_1(sK0,sK0,k4_tmap_1(sK0,sK0),X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k4_tmap_1(sK0,sK0),u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) )).

cnf(u34,negated_conjecture,
    ( v2_pre_topc(sK0) )).

cnf(u84,negated_conjecture,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(X0,sK0)
    | v2_struct_0(sK0)
    | k2_tmap_1(sK0,sK0,k4_tmap_1(sK0,sK0),X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k4_tmap_1(sK0,sK0),u1_struct_0(X0)) )).

cnf(u98,negated_conjecture,
    ( ~ v2_pre_topc(sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ v1_funct_2(k4_tmap_1(sK0,X1),u1_struct_0(X1),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_tmap_1(sK0,X1))
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(X0,X1)
    | k3_tmap_1(sK0,sK0,X1,X0,k4_tmap_1(sK0,X1)) = k2_partfun1(u1_struct_0(X1),u1_struct_0(sK0),k4_tmap_1(sK0,X1),u1_struct_0(X0))
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(X0,sK0) )).

cnf(u102,negated_conjecture,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(X1,X0)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(sK0),k4_tmap_1(sK0,X0),u1_struct_0(X1)) = k3_tmap_1(sK0,sK0,X0,X1,k4_tmap_1(sK0,X0))
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(k4_tmap_1(sK0,X0)) )).

cnf(u107,negated_conjecture,
    ( ~ v2_pre_topc(sK0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(sK0)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(sK0),k4_tmap_1(sK0,X0),u1_struct_0(X1)) = k3_tmap_1(sK0,sK0,X0,X1,k4_tmap_1(sK0,X0)) )).

cnf(u124,negated_conjecture,
    ( ~ v2_pre_topc(X2)
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X0)
    | ~ m1_pre_topc(X3,sK0)
    | v2_struct_0(X3)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X3,X1)
    | m1_subset_1(k3_tmap_1(sK0,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | v2_struct_0(sK0) )).

cnf(u110,negated_conjecture,
    ( ~ v2_pre_topc(X2)
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X0)
    | ~ m1_pre_topc(X3,sK0)
    | v2_struct_0(X3)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X3,X1)
    | v1_funct_1(k3_tmap_1(sK0,X2,X1,X3,X0))
    | v2_struct_0(sK0) )).

cnf(u93,negated_conjecture,
    ( ~ v2_pre_topc(X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X0)
    | ~ m1_pre_topc(X3,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X3,X1)
    | k3_tmap_1(sK0,X2,X1,X3,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3))
    | v2_struct_0(sK0) )).

cnf(u68,negated_conjecture,
    ( ~ v2_pre_topc(X1)
    | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,sK0)
    | k2_tmap_1(sK0,X1,X0,X2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(X2))
    | v2_struct_0(sK0) )).

cnf(u51,axiom,
    ( ~ v2_pre_topc(X0)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | m1_pre_topc(X2,X0) )).

cnf(u50,axiom,
    ( ~ v2_pre_topc(X0)
    | ~ m1_pre_topc(X3,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
    | v2_struct_0(X0) )).

cnf(u49,axiom,
    ( ~ v2_pre_topc(X0)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v5_pre_topc(X4,X2,X1)
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
    | ~ v1_funct_1(X4)
    | ~ m1_pre_topc(X3,X0)
    | v2_struct_0(X3)
    | ~ m1_pre_topc(X2,X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X0) )).

cnf(u46,axiom,
    ( ~ v2_pre_topc(X0)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v5_pre_topc(X4,X2,X1)
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
    | ~ v1_funct_1(X4)
    | ~ m1_pre_topc(X3,X0)
    | v2_struct_0(X3)
    | ~ m1_pre_topc(X2,X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))
    | v2_struct_0(X0) )).

cnf(u45,axiom,
    ( ~ v2_pre_topc(X0)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
    | ~ v1_funct_1(X4)
    | ~ m1_pre_topc(X3,X0)
    | ~ m1_pre_topc(X2,X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
    | v2_struct_0(X0) )).

cnf(u44,axiom,
    ( ~ v2_pre_topc(X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | k4_tmap_1(X0,X1) = k2_tmap_1(X0,X0,k3_struct_0(X0),X1)
    | v2_struct_0(X0) )).

cnf(u36,negated_conjecture,
    ( ~ v2_struct_0(sK1) )).

cnf(u33,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u39,axiom,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) )).

cnf(u35,negated_conjecture,
    ( l1_pre_topc(sK0) )).

cnf(u131,negated_conjecture,
    ( ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(sK1))
    | v2_struct_0(sK0) )).

cnf(u138,negated_conjecture,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
    | ~ v1_funct_1(X0)
    | ~ m1_pre_topc(X2,sK0)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X1)
    | ~ v5_pre_topc(X0,X1,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(X2,X1)
    | m1_subset_1(k3_tmap_1(sK0,sK0,X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) )).

cnf(u133,negated_conjecture,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
    | ~ v1_funct_1(X0)
    | ~ m1_pre_topc(X2,sK0)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X1)
    | ~ v5_pre_topc(X0,X1,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(X2,X1)
    | v1_funct_1(k3_tmap_1(sK0,sK0,X1,X2,X0)) )).

cnf(u113,negated_conjecture,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(X1,sK0)
    | k3_tmap_1(sK0,sK0,sK0,X1,k4_tmap_1(sK0,sK0)) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k4_tmap_1(sK0,sK0),u1_struct_0(X1))
    | v2_struct_0(sK0) )).

cnf(u108,negated_conjecture,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_pre_topc(X0,sK0)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(sK0),k4_tmap_1(sK0,X0),u1_struct_0(X1)) = k3_tmap_1(sK0,sK0,X0,X1,k4_tmap_1(sK0,X0)) )).

cnf(u104,negated_conjecture,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(X0,X1)
    | k3_tmap_1(sK0,sK0,X1,X0,k4_tmap_1(sK0,X1)) = k2_partfun1(u1_struct_0(X1),u1_struct_0(sK0),k4_tmap_1(sK0,X1),u1_struct_0(X0))
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(k4_tmap_1(sK0,X1)) )).

cnf(u103,negated_conjecture,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | ~ v5_pre_topc(X2,X1,X3)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X3))
    | ~ v1_funct_1(X2)
    | ~ m1_pre_topc(X0,sK0)
    | v2_struct_0(X0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X3)
    | v2_struct_0(X3)
    | ~ m1_pre_topc(X0,X1)
    | m1_subset_1(k3_tmap_1(sK0,X3,X1,X0,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
    | v2_struct_0(sK0) )).

cnf(u99,negated_conjecture,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_funct_2(k4_tmap_1(sK0,X0),u1_struct_0(X0),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_tmap_1(sK0,X0))
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(X1,X0)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(sK0),k4_tmap_1(sK0,X0),u1_struct_0(X1)) = k3_tmap_1(sK0,sK0,X0,X1,k4_tmap_1(sK0,X0))
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0) )).

cnf(u95,negated_conjecture,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(X0)
    | ~ m1_pre_topc(X2,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(X2,X1)
    | k3_tmap_1(sK0,sK0,X1,X2,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(sK0),X0,u1_struct_0(X2)) )).

cnf(u86,negated_conjecture,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(X0,sK0)
    | v2_struct_0(sK0)
    | k2_tmap_1(sK0,sK0,k4_tmap_1(sK0,sK0),X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k4_tmap_1(sK0,sK0),u1_struct_0(X0)) )).

cnf(u85,negated_conjecture,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | ~ v5_pre_topc(X2,X1,X3)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X3))
    | ~ v1_funct_1(X2)
    | ~ m1_pre_topc(X0,sK0)
    | v2_struct_0(X0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X3)
    | v2_struct_0(X3)
    | ~ m1_pre_topc(X0,X1)
    | v1_funct_1(k3_tmap_1(sK0,X3,X1,X0,X2))
    | v2_struct_0(sK0) )).

cnf(u74,negated_conjecture,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X3))
    | ~ v1_funct_1(X2)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X3)
    | v2_struct_0(X3)
    | ~ m1_pre_topc(X0,X1)
    | k3_tmap_1(sK0,X3,X1,X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),X2,u1_struct_0(X0))
    | v2_struct_0(sK0) )).

cnf(u70,negated_conjecture,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(X1,sK0)
    | k2_tmap_1(sK0,sK0,X0,X1) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),X0,u1_struct_0(X1)) )).

cnf(u67,negated_conjecture,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2))))
    | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X2))
    | ~ v1_funct_1(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X0,sK0)
    | k2_tmap_1(sK0,X2,X1,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X2),X1,u1_struct_0(X0))
    | v2_struct_0(sK0) )).

cnf(u60,negated_conjecture,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(X0,sK0)
    | k4_tmap_1(sK0,X0) = k2_tmap_1(sK0,sK0,k3_struct_0(sK0),X0)
    | v2_struct_0(sK0) )).

cnf(u55,negated_conjecture,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,sK0) )).

cnf(u126,negated_conjecture,
    ( k2_tmap_1(sK0,sK0,k4_tmap_1(sK0,sK0),sK0) = k3_tmap_1(sK0,sK0,sK0,sK0,k4_tmap_1(sK0,sK0)) )).

cnf(u119,negated_conjecture,
    ( k2_tmap_1(sK0,sK0,k4_tmap_1(sK0,sK0),sK1) = k3_tmap_1(sK0,sK0,sK0,sK1,k4_tmap_1(sK0,sK0)) )).

cnf(u92,negated_conjecture,
    ( k2_tmap_1(sK0,sK0,k4_tmap_1(sK0,sK0),sK0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k4_tmap_1(sK0,sK0),u1_struct_0(sK0)) )).

cnf(u90,negated_conjecture,
    ( k2_tmap_1(sK0,sK0,k4_tmap_1(sK0,sK0),sK1) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k4_tmap_1(sK0,sK0),u1_struct_0(sK1)) )).

cnf(u66,negated_conjecture,
    ( k4_tmap_1(sK0,sK0) = k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK0) )).

cnf(u64,negated_conjecture,
    ( k4_tmap_1(sK0,sK1) = k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:26:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.45  % (19161)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.45  % (19153)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.46  % (19161)Refutation not found, incomplete strategy% (19161)------------------------------
% 0.21/0.46  % (19161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (19161)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (19161)Memory used [KB]: 10618
% 0.21/0.46  % (19161)Time elapsed: 0.040 s
% 0.21/0.46  % (19161)------------------------------
% 0.21/0.46  % (19161)------------------------------
% 0.21/0.46  % (19145)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.46  % (19145)Refutation not found, incomplete strategy% (19145)------------------------------
% 0.21/0.46  % (19145)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (19145)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (19145)Memory used [KB]: 6012
% 0.21/0.46  % (19145)Time elapsed: 0.051 s
% 0.21/0.46  % (19145)------------------------------
% 0.21/0.46  % (19145)------------------------------
% 0.21/0.49  % (19158)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.49  % (19143)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.49  % (19159)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.50  % (19140)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.50  % (19154)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.50  % (19142)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.50  % (19141)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.50  % (19139)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.50  % (19141)Refutation not found, incomplete strategy% (19141)------------------------------
% 0.21/0.50  % (19141)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (19141)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (19141)Memory used [KB]: 10618
% 0.21/0.50  % (19141)Time elapsed: 0.094 s
% 0.21/0.50  % (19141)------------------------------
% 0.21/0.50  % (19141)------------------------------
% 0.21/0.50  % (19148)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.50  % (19148)Refutation not found, incomplete strategy% (19148)------------------------------
% 0.21/0.50  % (19148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (19148)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (19148)Memory used [KB]: 10490
% 0.21/0.50  % (19148)Time elapsed: 0.099 s
% 0.21/0.50  % (19148)------------------------------
% 0.21/0.50  % (19148)------------------------------
% 0.21/0.50  % (19150)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.51  % (19152)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.51  % (19138)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.51  % (19147)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.51  % (19146)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.51  % (19156)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.51  % (19160)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.51  % (19146)Refutation not found, incomplete strategy% (19146)------------------------------
% 0.21/0.51  % (19146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (19146)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (19146)Memory used [KB]: 10618
% 0.21/0.51  % (19146)Time elapsed: 0.110 s
% 0.21/0.51  % (19146)------------------------------
% 0.21/0.51  % (19146)------------------------------
% 0.21/0.51  % (19151)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.52  % (19154)Refutation not found, incomplete strategy% (19154)------------------------------
% 0.21/0.52  % (19154)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (19154)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (19154)Memory used [KB]: 1535
% 0.21/0.52  % (19154)Time elapsed: 0.108 s
% 0.21/0.52  % (19154)------------------------------
% 0.21/0.52  % (19154)------------------------------
% 0.21/0.52  % (19155)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.52  % (19157)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.52  % (19144)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.52  % (19158)Refutation not found, incomplete strategy% (19158)------------------------------
% 0.21/0.52  % (19158)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (19158)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (19158)Memory used [KB]: 6140
% 0.21/0.52  % (19158)Time elapsed: 0.112 s
% 0.21/0.52  % (19158)------------------------------
% 0.21/0.52  % (19158)------------------------------
% 0.21/0.52  % (19149)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.52  % (19157)Refutation not found, incomplete strategy% (19157)------------------------------
% 0.21/0.52  % (19157)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (19157)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (19157)Memory used [KB]: 6268
% 0.21/0.52  % (19157)Time elapsed: 0.119 s
% 0.21/0.52  % (19157)------------------------------
% 0.21/0.52  % (19157)------------------------------
% 0.21/0.53  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.53  % (19147)# SZS output start Saturation.
% 0.21/0.53  cnf(u48,axiom,
% 0.21/0.53      v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(X4,X2,X1) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u43,axiom,
% 0.21/0.53      v5_pre_topc(k3_struct_0(X0),X0,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u129,negated_conjecture,
% 0.21/0.53      ~v5_pre_topc(k4_tmap_1(sK0,sK0),sK0,sK0) | ~m1_pre_topc(sK0,sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | v5_pre_topc(k2_tmap_1(sK0,sK0,k4_tmap_1(sK0,sK0),sK0),sK0,sK0) | ~v1_funct_2(k4_tmap_1(sK0,sK0),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k4_tmap_1(sK0,sK0)) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u130,negated_conjecture,
% 0.21/0.53      ~v5_pre_topc(k4_tmap_1(sK0,sK0),sK0,sK0) | ~m1_pre_topc(sK0,sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | v1_funct_2(k2_tmap_1(sK0,sK0,k4_tmap_1(sK0,sK0),sK0),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_2(k4_tmap_1(sK0,sK0),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k4_tmap_1(sK0,sK0)) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u122,negated_conjecture,
% 0.21/0.53      ~v5_pre_topc(k4_tmap_1(sK0,sK0),sK0,sK0) | ~m1_pre_topc(sK1,sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | v5_pre_topc(k2_tmap_1(sK0,sK0,k4_tmap_1(sK0,sK0),sK1),sK1,sK0) | ~v1_funct_2(k4_tmap_1(sK0,sK0),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k4_tmap_1(sK0,sK0)) | v2_struct_0(sK1) | ~m1_pre_topc(sK0,sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u123,negated_conjecture,
% 0.21/0.53      ~v5_pre_topc(k4_tmap_1(sK0,sK0),sK0,sK0) | ~m1_pre_topc(sK1,sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | v1_funct_2(k2_tmap_1(sK0,sK0,k4_tmap_1(sK0,sK0),sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_2(k4_tmap_1(sK0,sK0),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k4_tmap_1(sK0,sK0)) | v2_struct_0(sK1) | ~m1_pre_topc(sK0,sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u136,negated_conjecture,
% 0.21/0.53      ~v5_pre_topc(k4_tmap_1(sK0,X0),X0,sK0) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~v1_funct_1(k4_tmap_1(sK0,X0)) | ~v1_funct_2(k4_tmap_1(sK0,X0),u1_struct_0(X0),u1_struct_0(sK0)) | v2_struct_0(sK0) | ~m1_pre_topc(X1,X0) | v1_funct_1(k3_tmap_1(sK0,sK0,X0,X1,k4_tmap_1(sK0,X0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u141,negated_conjecture,
% 0.21/0.53      ~v5_pre_topc(k4_tmap_1(sK0,X0),X0,sK0) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~v1_funct_1(k4_tmap_1(sK0,X0)) | ~v1_funct_2(k4_tmap_1(sK0,X0),u1_struct_0(X0),u1_struct_0(sK0)) | v2_struct_0(sK0) | ~m1_pre_topc(X1,X0) | m1_subset_1(k3_tmap_1(sK0,sK0,X0,X1,k4_tmap_1(sK0,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u38,negated_conjecture,
% 0.21/0.53      ~v5_pre_topc(k4_tmap_1(sK0,sK1),sK1,sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k4_tmap_1(sK0,sK1))).
% 0.21/0.53  
% 0.21/0.53  cnf(u40,axiom,
% 0.21/0.53      m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u37,negated_conjecture,
% 0.21/0.53      m1_pre_topc(sK1,sK0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u73,negated_conjecture,
% 0.21/0.53      ~m1_pre_topc(sK0,sK0) | ~v1_funct_1(k4_tmap_1(sK0,sK0)) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,sK0,k4_tmap_1(sK0,sK0),X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k4_tmap_1(sK0,sK0),u1_struct_0(X0)) | ~v1_funct_2(k4_tmap_1(sK0,sK0),u1_struct_0(sK0),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u78,negated_conjecture,
% 0.21/0.53      ~m1_pre_topc(sK0,sK0) | ~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,sK0,k4_tmap_1(sK0,sK0),X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k4_tmap_1(sK0,sK0),u1_struct_0(X0)) | ~v1_funct_1(k4_tmap_1(sK0,sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u82,negated_conjecture,
% 0.21/0.53      ~m1_pre_topc(sK0,sK0) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | k2_tmap_1(sK0,sK0,k4_tmap_1(sK0,sK0),X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k4_tmap_1(sK0,sK0),u1_struct_0(X0))).
% 0.21/0.53  
% 0.21/0.53  cnf(u57,negated_conjecture,
% 0.21/0.53      ~m1_pre_topc(X0,sK1) | m1_pre_topc(X0,sK0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u111,negated_conjecture,
% 0.21/0.53      ~m1_pre_topc(X0,sK1) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK0) | k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X0))).
% 0.21/0.53  
% 0.21/0.53  cnf(u56,negated_conjecture,
% 0.21/0.53      ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,X0) | m1_pre_topc(X1,sK0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u61,negated_conjecture,
% 0.21/0.53      ~m1_pre_topc(X0,sK0) | k4_tmap_1(sK0,X0) = k2_tmap_1(sK0,sK0,k3_struct_0(sK0),X0) | v2_struct_0(sK0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u87,negated_conjecture,
% 0.21/0.53      ~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | k2_tmap_1(sK0,sK0,k4_tmap_1(sK0,sK0),X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k4_tmap_1(sK0,sK0),u1_struct_0(X0))).
% 0.21/0.53  
% 0.21/0.53  cnf(u109,negated_conjecture,
% 0.21/0.53      ~m1_pre_topc(X1,sK0) | v2_struct_0(sK0) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,sK0) | k3_tmap_1(sK0,sK0,X1,X0,k4_tmap_1(sK0,X1)) = k2_partfun1(u1_struct_0(X1),u1_struct_0(sK0),k4_tmap_1(sK0,X1),u1_struct_0(X0))).
% 0.21/0.53  
% 0.21/0.53  cnf(u114,negated_conjecture,
% 0.21/0.53      ~m1_pre_topc(X0,sK0) | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k4_tmap_1(sK0,sK0),u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK0,X0,k4_tmap_1(sK0,sK0)) | v2_struct_0(sK0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u54,axiom,
% 0.21/0.53      m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u96,negated_conjecture,
% 0.21/0.53      ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X2,sK0) | ~v1_funct_2(X0,u1_struct_0(X2),u1_struct_0(sK0)) | ~v1_funct_1(X0) | v2_struct_0(sK0) | ~m1_pre_topc(X1,X2) | k3_tmap_1(sK0,sK0,X2,X1,X0) = k2_partfun1(u1_struct_0(X2),u1_struct_0(sK0),X0,u1_struct_0(X1))).
% 0.21/0.53  
% 0.21/0.53  cnf(u134,negated_conjecture,
% 0.21/0.53      ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) | ~v1_funct_1(X0) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~v5_pre_topc(X0,X1,sK0) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0)) | v2_struct_0(sK0) | ~m1_pre_topc(X2,X1) | v1_funct_1(k3_tmap_1(sK0,sK0,X1,X2,X0))).
% 0.21/0.53  
% 0.21/0.53  cnf(u139,negated_conjecture,
% 0.21/0.53      ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) | ~v1_funct_1(X0) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~v5_pre_topc(X0,X1,sK0) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0)) | v2_struct_0(sK0) | ~m1_pre_topc(X2,X1) | m1_subset_1(k3_tmap_1(sK0,sK0,X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))).
% 0.21/0.53  
% 0.21/0.53  cnf(u71,negated_conjecture,
% 0.21/0.53      ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(X0) | v2_struct_0(sK0) | ~m1_pre_topc(X1,sK0) | k2_tmap_1(sK0,sK0,X0,X1) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),X0,u1_struct_0(X1))).
% 0.21/0.53  
% 0.21/0.53  cnf(u47,axiom,
% 0.21/0.53      v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(X4,X2,X1) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u53,axiom,
% 0.21/0.53      v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u42,axiom,
% 0.21/0.53      v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u100,negated_conjecture,
% 0.21/0.53      ~v1_funct_2(k4_tmap_1(sK0,X0),u1_struct_0(X0),u1_struct_0(sK0)) | ~v1_funct_1(k4_tmap_1(sK0,X0)) | v2_struct_0(sK0) | ~m1_pre_topc(X1,X0) | k2_partfun1(u1_struct_0(X0),u1_struct_0(sK0),k4_tmap_1(sK0,X0),u1_struct_0(X1)) = k3_tmap_1(sK0,sK0,X0,X1,k4_tmap_1(sK0,X0)) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,sK0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u76,negated_conjecture,
% 0.21/0.53      ~v1_funct_2(k4_tmap_1(sK0,sK0),u1_struct_0(sK0),u1_struct_0(sK0)) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,sK0,k4_tmap_1(sK0,sK0),X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k4_tmap_1(sK0,sK0),u1_struct_0(X0)) | ~v1_funct_1(k4_tmap_1(sK0,sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u52,axiom,
% 0.21/0.53      v1_funct_1(k4_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u41,axiom,
% 0.21/0.53      v1_funct_1(k3_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u105,negated_conjecture,
% 0.21/0.53      ~v1_funct_1(k4_tmap_1(sK0,X1)) | k3_tmap_1(sK0,sK0,X1,X0,k4_tmap_1(sK0,X1)) = k2_partfun1(u1_struct_0(X1),u1_struct_0(sK0),k4_tmap_1(sK0,X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | ~m1_pre_topc(X0,X1)).
% 0.21/0.53  
% 0.21/0.53  cnf(u80,negated_conjecture,
% 0.21/0.53      ~v1_funct_1(k4_tmap_1(sK0,sK0)) | k2_tmap_1(sK0,sK0,k4_tmap_1(sK0,sK0),X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k4_tmap_1(sK0,sK0),u1_struct_0(X0)) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u34,negated_conjecture,
% 0.21/0.53      v2_pre_topc(sK0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u84,negated_conjecture,
% 0.21/0.53      ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | k2_tmap_1(sK0,sK0,k4_tmap_1(sK0,sK0),X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k4_tmap_1(sK0,sK0),u1_struct_0(X0))).
% 0.21/0.53  
% 0.21/0.53  cnf(u98,negated_conjecture,
% 0.21/0.53      ~v2_pre_topc(sK0) | ~m1_pre_topc(X1,sK0) | ~v1_funct_2(k4_tmap_1(sK0,X1),u1_struct_0(X1),u1_struct_0(sK0)) | ~v1_funct_1(k4_tmap_1(sK0,X1)) | v2_struct_0(sK0) | ~m1_pre_topc(X0,X1) | k3_tmap_1(sK0,sK0,X1,X0,k4_tmap_1(sK0,X1)) = k2_partfun1(u1_struct_0(X1),u1_struct_0(sK0),k4_tmap_1(sK0,X1),u1_struct_0(X0)) | ~l1_pre_topc(sK0) | ~m1_pre_topc(X0,sK0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u102,negated_conjecture,
% 0.21/0.53      ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_pre_topc(X1,X0) | k2_partfun1(u1_struct_0(X0),u1_struct_0(sK0),k4_tmap_1(sK0,X0),u1_struct_0(X1)) = k3_tmap_1(sK0,sK0,X0,X1,k4_tmap_1(sK0,X0)) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k4_tmap_1(sK0,X0))).
% 0.21/0.53  
% 0.21/0.53  cnf(u107,negated_conjecture,
% 0.21/0.53      ~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,sK0) | v2_struct_0(sK0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(sK0) | k2_partfun1(u1_struct_0(X0),u1_struct_0(sK0),k4_tmap_1(sK0,X0),u1_struct_0(X1)) = k3_tmap_1(sK0,sK0,X0,X1,k4_tmap_1(sK0,X0))).
% 0.21/0.53  
% 0.21/0.53  cnf(u124,negated_conjecture,
% 0.21/0.53      ~v2_pre_topc(X2) | ~v5_pre_topc(X0,X1,X2) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X0) | ~m1_pre_topc(X3,sK0) | v2_struct_0(X3) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~l1_pre_topc(X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | v2_struct_0(X2) | ~m1_pre_topc(X3,X1) | m1_subset_1(k3_tmap_1(sK0,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) | v2_struct_0(sK0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u110,negated_conjecture,
% 0.21/0.53      ~v2_pre_topc(X2) | ~v5_pre_topc(X0,X1,X2) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X0) | ~m1_pre_topc(X3,sK0) | v2_struct_0(X3) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~l1_pre_topc(X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | v2_struct_0(X2) | ~m1_pre_topc(X3,X1) | v1_funct_1(k3_tmap_1(sK0,X2,X1,X3,X0)) | v2_struct_0(sK0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u93,negated_conjecture,
% 0.21/0.53      ~v2_pre_topc(X2) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X0) | ~m1_pre_topc(X3,sK0) | ~m1_pre_topc(X1,sK0) | ~l1_pre_topc(X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | v2_struct_0(X2) | ~m1_pre_topc(X3,X1) | k3_tmap_1(sK0,X2,X1,X3,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) | v2_struct_0(sK0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u68,negated_conjecture,
% 0.21/0.53      ~v2_pre_topc(X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v2_struct_0(X1) | ~m1_pre_topc(X2,sK0) | k2_tmap_1(sK0,X1,X0,X2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(X2)) | v2_struct_0(sK0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u51,axiom,
% 0.21/0.53      ~v2_pre_topc(X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_pre_topc(X2,X0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u50,axiom,
% 0.21/0.53      ~v2_pre_topc(X0) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | v2_struct_0(X0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u49,axiom,
% 0.21/0.53      ~v2_pre_topc(X0) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(X4,X2,X1) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | v2_struct_0(X0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u46,axiom,
% 0.21/0.53      ~v2_pre_topc(X0) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(X4,X2,X1) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | v2_struct_0(X0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u45,axiom,
% 0.21/0.53      ~v2_pre_topc(X0) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | v2_struct_0(X0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u44,axiom,
% 0.21/0.53      ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | k4_tmap_1(X0,X1) = k2_tmap_1(X0,X0,k3_struct_0(X0),X1) | v2_struct_0(X0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u36,negated_conjecture,
% 0.21/0.53      ~v2_struct_0(sK1)).
% 0.21/0.53  
% 0.21/0.53  cnf(u33,negated_conjecture,
% 0.21/0.53      ~v2_struct_0(sK0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u39,axiom,
% 0.21/0.53      l1_struct_0(X0) | ~l1_pre_topc(X0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u35,negated_conjecture,
% 0.21/0.53      l1_pre_topc(sK0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u131,negated_conjecture,
% 0.21/0.53      ~l1_pre_topc(sK1) | ~m1_pre_topc(sK1,sK0) | k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(sK1)) | v2_struct_0(sK0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u138,negated_conjecture,
% 0.21/0.53      ~l1_pre_topc(sK0) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0)) | ~v1_funct_1(X0) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~v5_pre_topc(X0,X1,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) | v2_struct_0(sK0) | ~m1_pre_topc(X2,X1) | m1_subset_1(k3_tmap_1(sK0,sK0,X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))).
% 0.21/0.53  
% 0.21/0.53  cnf(u133,negated_conjecture,
% 0.21/0.53      ~l1_pre_topc(sK0) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0)) | ~v1_funct_1(X0) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~v5_pre_topc(X0,X1,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) | v2_struct_0(sK0) | ~m1_pre_topc(X2,X1) | v1_funct_1(k3_tmap_1(sK0,sK0,X1,X2,X0))).
% 0.21/0.53  
% 0.21/0.53  cnf(u113,negated_conjecture,
% 0.21/0.53      ~l1_pre_topc(sK0) | ~m1_pre_topc(X1,sK0) | k3_tmap_1(sK0,sK0,sK0,X1,k4_tmap_1(sK0,sK0)) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k4_tmap_1(sK0,sK0),u1_struct_0(X1)) | v2_struct_0(sK0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u108,negated_conjecture,
% 0.21/0.53      ~l1_pre_topc(sK0) | ~m1_pre_topc(X1,sK0) | v2_struct_0(sK0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X0,sK0) | k2_partfun1(u1_struct_0(X0),u1_struct_0(sK0),k4_tmap_1(sK0,X0),u1_struct_0(X1)) = k3_tmap_1(sK0,sK0,X0,X1,k4_tmap_1(sK0,X0))).
% 0.21/0.53  
% 0.21/0.53  cnf(u104,negated_conjecture,
% 0.21/0.53      ~l1_pre_topc(sK0) | ~m1_pre_topc(X0,X1) | k3_tmap_1(sK0,sK0,X1,X0,k4_tmap_1(sK0,X1)) = k2_partfun1(u1_struct_0(X1),u1_struct_0(sK0),k4_tmap_1(sK0,X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | ~v1_funct_1(k4_tmap_1(sK0,X1))).
% 0.21/0.53  
% 0.21/0.53  cnf(u103,negated_conjecture,
% 0.21/0.53      ~l1_pre_topc(sK0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v5_pre_topc(X2,X1,X3) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(X2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~m1_pre_topc(X0,X1) | m1_subset_1(k3_tmap_1(sK0,X3,X1,X0,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3)))) | v2_struct_0(sK0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u99,negated_conjecture,
% 0.21/0.53      ~l1_pre_topc(sK0) | ~v1_funct_2(k4_tmap_1(sK0,X0),u1_struct_0(X0),u1_struct_0(sK0)) | ~v1_funct_1(k4_tmap_1(sK0,X0)) | v2_struct_0(sK0) | ~m1_pre_topc(X1,X0) | k2_partfun1(u1_struct_0(X0),u1_struct_0(sK0),k4_tmap_1(sK0,X0),u1_struct_0(X1)) = k3_tmap_1(sK0,sK0,X0,X1,k4_tmap_1(sK0,X0)) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,sK0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u95,negated_conjecture,
% 0.21/0.53      ~l1_pre_topc(sK0) | ~v1_funct_1(X0) | ~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X1,sK0) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) | v2_struct_0(sK0) | ~m1_pre_topc(X2,X1) | k3_tmap_1(sK0,sK0,X1,X2,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(sK0),X0,u1_struct_0(X2))).
% 0.21/0.53  
% 0.21/0.53  cnf(u86,negated_conjecture,
% 0.21/0.53      ~l1_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | k2_tmap_1(sK0,sK0,k4_tmap_1(sK0,sK0),X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k4_tmap_1(sK0,sK0),u1_struct_0(X0))).
% 0.21/0.53  
% 0.21/0.53  cnf(u85,negated_conjecture,
% 0.21/0.53      ~l1_pre_topc(sK0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v5_pre_topc(X2,X1,X3) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(X2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~m1_pre_topc(X0,X1) | v1_funct_1(k3_tmap_1(sK0,X3,X1,X0,X2)) | v2_struct_0(sK0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u74,negated_conjecture,
% 0.21/0.53      ~l1_pre_topc(sK0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(X2) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,sK0) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~m1_pre_topc(X0,X1) | k3_tmap_1(sK0,X3,X1,X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),X2,u1_struct_0(X0)) | v2_struct_0(sK0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u70,negated_conjecture,
% 0.21/0.53      ~l1_pre_topc(sK0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | v2_struct_0(sK0) | ~m1_pre_topc(X1,sK0) | k2_tmap_1(sK0,sK0,X0,X1) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),X0,u1_struct_0(X1))).
% 0.21/0.53  
% 0.21/0.53  cnf(u67,negated_conjecture,
% 0.21/0.53      ~l1_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X2)) | ~v1_funct_1(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,X2,X1,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X2),X1,u1_struct_0(X0)) | v2_struct_0(sK0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u60,negated_conjecture,
% 0.21/0.53      ~l1_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | k4_tmap_1(sK0,X0) = k2_tmap_1(sK0,sK0,k3_struct_0(sK0),X0) | v2_struct_0(sK0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u55,negated_conjecture,
% 0.21/0.53      ~l1_pre_topc(sK0) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,X1) | m1_pre_topc(X0,sK0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u126,negated_conjecture,
% 0.21/0.53      k2_tmap_1(sK0,sK0,k4_tmap_1(sK0,sK0),sK0) = k3_tmap_1(sK0,sK0,sK0,sK0,k4_tmap_1(sK0,sK0))).
% 0.21/0.53  
% 0.21/0.53  cnf(u119,negated_conjecture,
% 0.21/0.53      k2_tmap_1(sK0,sK0,k4_tmap_1(sK0,sK0),sK1) = k3_tmap_1(sK0,sK0,sK0,sK1,k4_tmap_1(sK0,sK0))).
% 0.21/0.53  
% 0.21/0.53  cnf(u92,negated_conjecture,
% 0.21/0.53      k2_tmap_1(sK0,sK0,k4_tmap_1(sK0,sK0),sK0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k4_tmap_1(sK0,sK0),u1_struct_0(sK0))).
% 0.21/0.53  
% 0.21/0.53  cnf(u90,negated_conjecture,
% 0.21/0.53      k2_tmap_1(sK0,sK0,k4_tmap_1(sK0,sK0),sK1) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k4_tmap_1(sK0,sK0),u1_struct_0(sK1))).
% 0.21/0.53  
% 0.21/0.53  cnf(u66,negated_conjecture,
% 0.21/0.53      k4_tmap_1(sK0,sK0) = k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u64,negated_conjecture,
% 0.21/0.53      k4_tmap_1(sK0,sK1) = k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1)).
% 0.21/0.53  
% 0.21/0.53  % (19147)# SZS output end Saturation.
% 0.21/0.53  % (19147)------------------------------
% 0.21/0.53  % (19147)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (19147)Termination reason: Satisfiable
% 0.21/0.53  
% 0.21/0.53  % (19147)Memory used [KB]: 1791
% 0.21/0.53  % (19147)Time elapsed: 0.113 s
% 0.21/0.53  % (19147)------------------------------
% 0.21/0.53  % (19147)------------------------------
% 0.21/0.54  % (19137)Success in time 0.178 s
%------------------------------------------------------------------------------
