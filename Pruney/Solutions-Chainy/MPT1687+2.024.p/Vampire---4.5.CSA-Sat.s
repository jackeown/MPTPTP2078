%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:22 EST 2020

% Result     : CounterSatisfiable 1.24s
% Output     : Saturation 1.24s
% Verified   : 
% Statistics : Number of clauses        :   58 (  58 expanded)
%              Number of leaves         :   58 (  58 expanded)
%              Depth                    :    0
%              Number of atoms          :  231 ( 231 expanded)
%              Number of equality atoms :   67 (  67 expanded)
%              Maximal clause size      :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u35,negated_conjecture,
    ( v23_waybel_0(sK2,sK0,sK1) )).

cnf(u38,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u36,negated_conjecture,
    ( ~ v2_struct_0(sK1) )).

cnf(u39,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u37,negated_conjecture,
    ( l1_orders_2(sK1) )).

cnf(u45,axiom,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) )).

cnf(u57,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u56,negated_conjecture,
    ( l1_struct_0(sK1) )).

cnf(u42,axiom,
    ( ~ l1_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) )).

cnf(u65,negated_conjecture,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) )).

cnf(u64,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) )).

cnf(u47,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(X2) )).

cnf(u48,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k3_relset_1(X0,X1,X2) = k4_relat_1(X2) )).

cnf(u49,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) )).

cnf(u50,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2) )).

cnf(u51,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) )).

cnf(u46,axiom,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k4_relat_1(X0) = k2_funct_1(X0) )).

cnf(u32,negated_conjecture,
    ( v1_funct_1(sK2) )).

cnf(u69,negated_conjecture,
    ( v1_relat_1(sK2) )).

cnf(u40,axiom,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )).

cnf(u41,axiom,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) )).

cnf(u59,negated_conjecture,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) )).

cnf(u58,negated_conjecture,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) )).

cnf(u75,negated_conjecture,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k4_relat_1(sK2)) )).

cnf(u78,negated_conjecture,
    ( k1_relat_1(sK2) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k4_relat_1(sK2)) )).

cnf(u73,negated_conjecture,
    ( k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) )).

cnf(u70,negated_conjecture,
    ( k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2)) )).

cnf(u72,negated_conjecture,
    ( k4_relat_1(sK2) = k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) )).

cnf(u71,negated_conjecture,
    ( k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2)) )).

cnf(u92,negated_conjecture,
    ( k2_struct_0(X2) != k2_relset_1(k2_struct_0(sK0),u1_struct_0(X2),X3)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_struct_0(sK0),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X2))))
    | ~ v2_funct_1(X3)
    | k2_struct_0(X2) = k1_relset_1(u1_struct_0(X2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(X2),X3)) )).

cnf(u116,negated_conjecture,
    ( k2_struct_0(X2) != k2_relset_1(k2_struct_0(sK0),u1_struct_0(X2),X3)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_struct_0(sK0),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X2))))
    | ~ v2_funct_1(X3)
    | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(X2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(X2),X3)) )).

cnf(u91,negated_conjecture,
    ( k2_struct_0(X0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(X0),X1)
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,k2_struct_0(sK1),u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0))))
    | ~ v2_funct_1(X1)
    | k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(X0),X1)) )).

cnf(u115,negated_conjecture,
    ( k2_struct_0(X0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(X0),X1)
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,k2_struct_0(sK1),u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0))))
    | ~ v2_funct_1(X1)
    | k2_struct_0(sK1) = k2_relset_1(u1_struct_0(X0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(X0),X1)) )).

cnf(u104,negated_conjecture,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v2_funct_1(X1)
    | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK0),X1)) )).

cnf(u128,negated_conjecture,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v2_funct_1(X1)
    | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK0),X1)) )).

cnf(u103,negated_conjecture,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ v2_funct_1(X0)
    | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),X0)) )).

cnf(u127,negated_conjecture,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ v2_funct_1(X0)
    | k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),X0)) )).

cnf(u96,negated_conjecture,
    ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(X2),k2_struct_0(sK0),X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X2),k2_struct_0(sK0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),k2_struct_0(sK0))))
    | ~ l1_struct_0(X2)
    | ~ v2_funct_1(X3)
    | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),k2_struct_0(sK0),X3)) )).

cnf(u120,negated_conjecture,
    ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(X2),k2_struct_0(sK0),X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X2),k2_struct_0(sK0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),k2_struct_0(sK0))))
    | ~ l1_struct_0(X2)
    | ~ v2_funct_1(X3)
    | k2_struct_0(X2) = k2_relset_1(k2_struct_0(sK0),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),k2_struct_0(sK0),X3)) )).

cnf(u100,negated_conjecture,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v2_funct_1(X1)
    | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X1)) )).

cnf(u124,negated_conjecture,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v2_funct_1(X1)
    | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X1)) )).

cnf(u99,negated_conjecture,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1))))
    | ~ v2_funct_1(X0)
    | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK1),X0)) )).

cnf(u123,negated_conjecture,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1))))
    | ~ v2_funct_1(X0)
    | k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK1),X0)) )).

cnf(u94,negated_conjecture,
    ( k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X0),k2_struct_0(sK1),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X0),k2_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),k2_struct_0(sK1))))
    | ~ l1_struct_0(X0)
    | ~ v2_funct_1(X1)
    | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),k2_struct_0(sK1),X1)) )).

cnf(u118,negated_conjecture,
    ( k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X0),k2_struct_0(sK1),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X0),k2_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),k2_struct_0(sK1))))
    | ~ l1_struct_0(X0)
    | ~ v2_funct_1(X1)
    | k2_struct_0(X0) = k2_relset_1(k2_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),k2_struct_0(sK1),X1)) )).

cnf(u80,negated_conjecture,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | ~ v1_funct_2(k4_relat_1(sK2),k2_struct_0(sK1),k1_relat_1(sK2))
    | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2))))
    | ~ v2_funct_1(k4_relat_1(sK2))
    | ~ v1_funct_1(k4_relat_1(sK2))
    | v1_funct_1(k2_funct_1(k4_relat_1(sK2))) )).

cnf(u82,negated_conjecture,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | ~ v1_funct_2(k4_relat_1(sK2),k2_struct_0(sK1),k1_relat_1(sK2))
    | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2))))
    | ~ v2_funct_1(k4_relat_1(sK2))
    | ~ v1_funct_1(k4_relat_1(sK2))
    | v1_funct_2(k2_funct_1(k4_relat_1(sK2)),k1_relat_1(sK2),k2_struct_0(sK1)) )).

cnf(u84,negated_conjecture,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | ~ v1_funct_2(k4_relat_1(sK2),k2_struct_0(sK1),k1_relat_1(sK2))
    | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2))))
    | ~ v2_funct_1(k4_relat_1(sK2))
    | ~ v1_funct_1(k4_relat_1(sK2))
    | m1_subset_1(k2_funct_1(k4_relat_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) )).

cnf(u86,negated_conjecture,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | ~ v1_funct_2(k4_relat_1(sK2),k2_struct_0(sK1),k1_relat_1(sK2))
    | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2))))
    | ~ v1_funct_1(k4_relat_1(sK2))
    | ~ v2_funct_1(k4_relat_1(sK2))
    | k2_funct_1(k4_relat_1(sK2)) = k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k4_relat_1(sK2)) )).

cnf(u106,negated_conjecture,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | ~ v1_funct_1(k4_relat_1(sK2))
    | ~ v1_funct_2(k4_relat_1(sK2),k2_struct_0(sK1),k1_relat_1(sK2))
    | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2))))
    | ~ v2_funct_1(k4_relat_1(sK2))
    | k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k4_relat_1(sK2))) )).

cnf(u130,negated_conjecture,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | ~ v1_funct_1(k4_relat_1(sK2))
    | ~ v1_funct_2(k4_relat_1(sK2),k2_struct_0(sK1),k1_relat_1(sK2))
    | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2))))
    | ~ v2_funct_1(k4_relat_1(sK2))
    | k2_struct_0(sK1) = k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k4_relat_1(sK2))) )).

cnf(u68,negated_conjecture,
    ( k2_relat_1(k2_funct_1(sK2)) != k2_struct_0(sK0)
    | ~ v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ v1_funct_1(k2_funct_1(sK2)) )).

cnf(u43,axiom,
    ( k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_struct_0(X0)
    | ~ v2_funct_1(X2)
    | k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )).

cnf(u44,axiom,
    ( k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_struct_0(X0)
    | ~ v2_funct_1(X2)
    | k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )).

cnf(u52,axiom,
    ( k2_relset_1(X0,X1,X2) != X1
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | v1_funct_1(k2_funct_1(X2)) )).

cnf(u53,axiom,
    ( k2_relset_1(X0,X1,X2) != X1
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | v1_funct_2(k2_funct_1(X2),X1,X0) )).

cnf(u54,axiom,
    ( k2_relset_1(X0,X1,X2) != X1
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )).

cnf(u55,axiom,
    ( k2_relset_1(X0,X1,X2) != X1
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X2)
    | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:46:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  ipcrm: permission denied for id (822640641)
% 0.13/0.37  ipcrm: permission denied for id (825229314)
% 0.13/0.37  ipcrm: permission denied for id (828243971)
% 0.13/0.37  ipcrm: permission denied for id (828276740)
% 0.13/0.37  ipcrm: permission denied for id (828309509)
% 0.13/0.37  ipcrm: permission denied for id (828342278)
% 0.13/0.38  ipcrm: permission denied for id (828473354)
% 0.13/0.38  ipcrm: permission denied for id (822870027)
% 0.13/0.38  ipcrm: permission denied for id (825524236)
% 0.13/0.38  ipcrm: permission denied for id (822902798)
% 0.13/0.38  ipcrm: permission denied for id (822968336)
% 0.13/0.38  ipcrm: permission denied for id (823001105)
% 0.13/0.39  ipcrm: permission denied for id (825622546)
% 0.13/0.39  ipcrm: permission denied for id (825655315)
% 0.13/0.39  ipcrm: permission denied for id (823066644)
% 0.13/0.39  ipcrm: permission denied for id (828571669)
% 0.13/0.39  ipcrm: permission denied for id (825720854)
% 0.13/0.39  ipcrm: permission denied for id (823164952)
% 0.13/0.40  ipcrm: permission denied for id (823197722)
% 0.13/0.40  ipcrm: permission denied for id (825819163)
% 0.13/0.40  ipcrm: permission denied for id (825851932)
% 0.13/0.40  ipcrm: permission denied for id (823230493)
% 0.13/0.40  ipcrm: permission denied for id (825884702)
% 0.13/0.40  ipcrm: permission denied for id (823263263)
% 0.13/0.40  ipcrm: permission denied for id (825917472)
% 0.13/0.40  ipcrm: permission denied for id (823328801)
% 0.20/0.41  ipcrm: permission denied for id (825950242)
% 0.20/0.41  ipcrm: permission denied for id (825983011)
% 0.20/0.41  ipcrm: permission denied for id (828669988)
% 0.20/0.41  ipcrm: permission denied for id (828702757)
% 0.20/0.41  ipcrm: permission denied for id (823394342)
% 0.20/0.41  ipcrm: permission denied for id (826081319)
% 0.20/0.41  ipcrm: permission denied for id (826114088)
% 0.20/0.42  ipcrm: permission denied for id (826245163)
% 0.20/0.42  ipcrm: permission denied for id (826343469)
% 0.20/0.42  ipcrm: permission denied for id (828866606)
% 0.20/0.42  ipcrm: permission denied for id (828932143)
% 0.20/0.42  ipcrm: permission denied for id (826441776)
% 0.20/0.42  ipcrm: permission denied for id (823459889)
% 0.20/0.43  ipcrm: permission denied for id (823492658)
% 0.20/0.43  ipcrm: permission denied for id (826507315)
% 0.20/0.43  ipcrm: permission denied for id (828964916)
% 0.20/0.43  ipcrm: permission denied for id (826572853)
% 0.20/0.43  ipcrm: permission denied for id (826671160)
% 0.20/0.43  ipcrm: permission denied for id (823689273)
% 0.20/0.44  ipcrm: permission denied for id (826703930)
% 0.20/0.44  ipcrm: permission denied for id (826736699)
% 0.20/0.44  ipcrm: permission denied for id (823754812)
% 0.20/0.44  ipcrm: permission denied for id (829095997)
% 0.20/0.44  ipcrm: permission denied for id (823787582)
% 0.20/0.44  ipcrm: permission denied for id (829128767)
% 0.20/0.44  ipcrm: permission denied for id (826835008)
% 0.20/0.44  ipcrm: permission denied for id (829161537)
% 0.20/0.45  ipcrm: permission denied for id (826900546)
% 0.20/0.45  ipcrm: permission denied for id (823885891)
% 0.20/0.45  ipcrm: permission denied for id (826933316)
% 0.20/0.45  ipcrm: permission denied for id (823951429)
% 0.20/0.45  ipcrm: permission denied for id (823984198)
% 0.20/0.45  ipcrm: permission denied for id (826966087)
% 0.20/0.45  ipcrm: permission denied for id (829194312)
% 0.20/0.45  ipcrm: permission denied for id (824049737)
% 0.20/0.45  ipcrm: permission denied for id (824082506)
% 0.20/0.46  ipcrm: permission denied for id (827031627)
% 0.20/0.46  ipcrm: permission denied for id (824115276)
% 0.20/0.46  ipcrm: permission denied for id (827064397)
% 0.20/0.46  ipcrm: permission denied for id (824180814)
% 0.20/0.46  ipcrm: permission denied for id (824213583)
% 0.20/0.46  ipcrm: permission denied for id (827097168)
% 0.20/0.46  ipcrm: permission denied for id (824246353)
% 0.20/0.46  ipcrm: permission denied for id (824279122)
% 0.20/0.47  ipcrm: permission denied for id (824311891)
% 0.20/0.47  ipcrm: permission denied for id (827129940)
% 0.20/0.47  ipcrm: permission denied for id (824377429)
% 0.20/0.47  ipcrm: permission denied for id (824410198)
% 0.20/0.47  ipcrm: permission denied for id (827162711)
% 0.20/0.47  ipcrm: permission denied for id (827228249)
% 0.20/0.47  ipcrm: permission denied for id (827261018)
% 0.20/0.48  ipcrm: permission denied for id (824442971)
% 0.20/0.48  ipcrm: permission denied for id (824475740)
% 0.20/0.48  ipcrm: permission denied for id (829259869)
% 0.20/0.48  ipcrm: permission denied for id (824541278)
% 0.20/0.48  ipcrm: permission denied for id (827326559)
% 0.20/0.48  ipcrm: permission denied for id (827359328)
% 0.20/0.48  ipcrm: permission denied for id (829292641)
% 0.20/0.48  ipcrm: permission denied for id (824606818)
% 0.20/0.48  ipcrm: permission denied for id (827424867)
% 0.20/0.49  ipcrm: permission denied for id (829325412)
% 0.20/0.49  ipcrm: permission denied for id (829390950)
% 0.20/0.49  ipcrm: permission denied for id (824705127)
% 0.20/0.49  ipcrm: permission denied for id (829423720)
% 0.20/0.49  ipcrm: permission denied for id (827588713)
% 0.20/0.49  ipcrm: permission denied for id (827621482)
% 0.20/0.49  ipcrm: permission denied for id (827654251)
% 0.20/0.50  ipcrm: permission denied for id (827687020)
% 0.20/0.50  ipcrm: permission denied for id (829456493)
% 0.20/0.50  ipcrm: permission denied for id (824868974)
% 0.20/0.50  ipcrm: permission denied for id (824901743)
% 0.20/0.50  ipcrm: permission denied for id (827752560)
% 0.20/0.50  ipcrm: permission denied for id (827785329)
% 0.20/0.50  ipcrm: permission denied for id (827850867)
% 0.20/0.51  ipcrm: permission denied for id (827916405)
% 0.20/0.51  ipcrm: permission denied for id (824967286)
% 0.20/0.51  ipcrm: permission denied for id (825032824)
% 0.20/0.51  ipcrm: permission denied for id (827981945)
% 0.20/0.51  ipcrm: permission denied for id (828014714)
% 0.20/0.51  ipcrm: permission denied for id (828047483)
% 0.20/0.51  ipcrm: permission denied for id (828080252)
% 0.20/0.52  ipcrm: permission denied for id (825098365)
% 0.20/0.52  ipcrm: permission denied for id (828145790)
% 0.20/0.52  ipcrm: permission denied for id (828178559)
% 0.20/0.61  % (21309)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.61  % (21309)Refutation not found, incomplete strategy% (21309)------------------------------
% 0.20/0.61  % (21309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.61  % (21309)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.61  
% 0.20/0.61  % (21309)Memory used [KB]: 10618
% 0.20/0.61  % (21309)Time elapsed: 0.036 s
% 0.20/0.61  % (21309)------------------------------
% 0.20/0.61  % (21309)------------------------------
% 0.20/0.61  % (21317)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.62  % (21317)Refutation not found, incomplete strategy% (21317)------------------------------
% 0.20/0.62  % (21317)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.62  % (21317)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.62  
% 0.20/0.62  % (21317)Memory used [KB]: 1791
% 0.20/0.62  % (21317)Time elapsed: 0.045 s
% 0.20/0.62  % (21317)------------------------------
% 0.20/0.62  % (21317)------------------------------
% 0.95/0.64  % (21321)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 1.24/0.66  % (21307)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 1.24/0.67  % (21313)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.24/0.67  % (21313)Refutation not found, incomplete strategy% (21313)------------------------------
% 1.24/0.67  % (21313)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.67  % (21313)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.67  
% 1.24/0.67  % (21313)Memory used [KB]: 6140
% 1.24/0.67  % (21313)Time elapsed: 0.085 s
% 1.24/0.67  % (21313)------------------------------
% 1.24/0.67  % (21313)------------------------------
% 1.24/0.67  % (21328)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 1.24/0.67  % (21324)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 1.24/0.67  % (21311)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 1.24/0.67  % (21320)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 1.24/0.68  % (21308)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 1.24/0.68  % (21319)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 1.24/0.68  % (21310)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 1.24/0.68  % SZS status CounterSatisfiable for theBenchmark
% 1.24/0.68  % (21319)# SZS output start Saturation.
% 1.24/0.68  cnf(u35,negated_conjecture,
% 1.24/0.68      v23_waybel_0(sK2,sK0,sK1)).
% 1.24/0.68  
% 1.24/0.68  cnf(u38,negated_conjecture,
% 1.24/0.68      ~v2_struct_0(sK0)).
% 1.24/0.68  
% 1.24/0.68  cnf(u36,negated_conjecture,
% 1.24/0.68      ~v2_struct_0(sK1)).
% 1.24/0.68  
% 1.24/0.68  cnf(u39,negated_conjecture,
% 1.24/0.68      l1_orders_2(sK0)).
% 1.24/0.68  
% 1.24/0.68  cnf(u37,negated_conjecture,
% 1.24/0.68      l1_orders_2(sK1)).
% 1.24/0.68  
% 1.24/0.68  cnf(u45,axiom,
% 1.24/0.68      ~l1_orders_2(X0) | l1_struct_0(X0)).
% 1.24/0.68  
% 1.24/0.68  cnf(u57,negated_conjecture,
% 1.24/0.68      l1_struct_0(sK0)).
% 1.24/0.68  
% 1.24/0.68  cnf(u56,negated_conjecture,
% 1.24/0.68      l1_struct_0(sK1)).
% 1.24/0.68  
% 1.24/0.68  cnf(u42,axiom,
% 1.24/0.68      ~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)).
% 1.24/0.68  
% 1.24/0.68  cnf(u65,negated_conjecture,
% 1.24/0.68      v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))).
% 1.24/0.68  
% 1.24/0.68  cnf(u64,negated_conjecture,
% 1.24/0.68      m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))).
% 1.24/0.68  
% 1.24/0.68  cnf(u47,axiom,
% 1.24/0.68      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)).
% 1.24/0.68  
% 1.24/0.68  cnf(u48,axiom,
% 1.24/0.68      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k3_relset_1(X0,X1,X2) = k4_relat_1(X2)).
% 1.24/0.68  
% 1.24/0.68  cnf(u49,axiom,
% 1.24/0.68      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)).
% 1.24/0.68  
% 1.24/0.68  cnf(u50,axiom,
% 1.24/0.68      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2)).
% 1.24/0.68  
% 1.24/0.68  cnf(u51,axiom,
% 1.24/0.68      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))).
% 1.24/0.68  
% 1.24/0.68  cnf(u46,axiom,
% 1.24/0.68      ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k4_relat_1(X0) = k2_funct_1(X0)).
% 1.24/0.68  
% 1.24/0.68  cnf(u32,negated_conjecture,
% 1.24/0.68      v1_funct_1(sK2)).
% 1.24/0.68  
% 1.24/0.68  cnf(u69,negated_conjecture,
% 1.24/0.68      v1_relat_1(sK2)).
% 1.24/0.68  
% 1.24/0.68  cnf(u40,axiom,
% 1.24/0.68      ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))).
% 1.24/0.68  
% 1.24/0.68  cnf(u41,axiom,
% 1.24/0.68      ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))).
% 1.24/0.68  
% 1.24/0.68  cnf(u59,negated_conjecture,
% 1.24/0.68      u1_struct_0(sK0) = k2_struct_0(sK0)).
% 1.24/0.68  
% 1.24/0.68  cnf(u58,negated_conjecture,
% 1.24/0.68      u1_struct_0(sK1) = k2_struct_0(sK1)).
% 1.24/0.68  
% 1.24/0.68  cnf(u75,negated_conjecture,
% 1.24/0.68      k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k4_relat_1(sK2))).
% 1.24/0.68  
% 1.24/0.68  cnf(u78,negated_conjecture,
% 1.24/0.68      k1_relat_1(sK2) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k4_relat_1(sK2))).
% 1.24/0.68  
% 1.24/0.68  cnf(u73,negated_conjecture,
% 1.24/0.68      k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)).
% 1.24/0.68  
% 1.24/0.68  cnf(u70,negated_conjecture,
% 1.24/0.68      k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2))).
% 1.24/0.68  
% 1.24/0.68  cnf(u72,negated_conjecture,
% 1.24/0.68      k4_relat_1(sK2) = k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)).
% 1.24/0.68  
% 1.24/0.68  cnf(u71,negated_conjecture,
% 1.24/0.68      k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2))).
% 1.24/0.68  
% 1.24/0.68  cnf(u92,negated_conjecture,
% 1.24/0.68      k2_struct_0(X2) != k2_relset_1(k2_struct_0(sK0),u1_struct_0(X2),X3) | v2_struct_0(X2) | ~l1_struct_0(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,k2_struct_0(sK0),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X2)))) | ~v2_funct_1(X3) | k2_struct_0(X2) = k1_relset_1(u1_struct_0(X2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(X2),X3))).
% 1.24/0.68  
% 1.24/0.68  cnf(u116,negated_conjecture,
% 1.24/0.68      k2_struct_0(X2) != k2_relset_1(k2_struct_0(sK0),u1_struct_0(X2),X3) | v2_struct_0(X2) | ~l1_struct_0(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,k2_struct_0(sK0),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X2)))) | ~v2_funct_1(X3) | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(X2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(X2),X3))).
% 1.24/0.68  
% 1.24/0.68  cnf(u91,negated_conjecture,
% 1.24/0.68      k2_struct_0(X0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(X0),X1) | v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,k2_struct_0(sK1),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0)))) | ~v2_funct_1(X1) | k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(X0),X1))).
% 1.24/0.68  
% 1.24/0.68  cnf(u115,negated_conjecture,
% 1.24/0.68      k2_struct_0(X0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(X0),X1) | v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,k2_struct_0(sK1),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0)))) | ~v2_funct_1(X1) | k2_struct_0(sK1) = k2_relset_1(u1_struct_0(X0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(X0),X1))).
% 1.24/0.68  
% 1.24/0.68  cnf(u104,negated_conjecture,
% 1.24/0.68      k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v2_funct_1(X1) | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK0),X1))).
% 1.24/0.68  
% 1.24/0.68  cnf(u128,negated_conjecture,
% 1.24/0.68      k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v2_funct_1(X1) | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK0),X1))).
% 1.24/0.68  
% 1.24/0.68  cnf(u103,negated_conjecture,
% 1.24/0.68      k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),X0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | ~v2_funct_1(X0) | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),X0))).
% 1.24/0.68  
% 1.24/0.68  cnf(u127,negated_conjecture,
% 1.24/0.68      k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),X0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | ~v2_funct_1(X0) | k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),X0))).
% 1.24/0.68  
% 1.24/0.68  cnf(u96,negated_conjecture,
% 1.24/0.68      k2_struct_0(sK0) != k2_relset_1(u1_struct_0(X2),k2_struct_0(sK0),X3) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),k2_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),k2_struct_0(sK0)))) | ~l1_struct_0(X2) | ~v2_funct_1(X3) | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),k2_struct_0(sK0),X3))).
% 1.24/0.68  
% 1.24/0.68  cnf(u120,negated_conjecture,
% 1.24/0.68      k2_struct_0(sK0) != k2_relset_1(u1_struct_0(X2),k2_struct_0(sK0),X3) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),k2_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),k2_struct_0(sK0)))) | ~l1_struct_0(X2) | ~v2_funct_1(X3) | k2_struct_0(X2) = k2_relset_1(k2_struct_0(sK0),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),k2_struct_0(sK0),X3))).
% 1.24/0.68  
% 1.24/0.68  cnf(u100,negated_conjecture,
% 1.24/0.68      k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v2_funct_1(X1) | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X1))).
% 1.24/0.68  
% 1.24/0.68  cnf(u124,negated_conjecture,
% 1.24/0.68      k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v2_funct_1(X1) | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X1))).
% 1.24/0.68  
% 1.24/0.68  cnf(u99,negated_conjecture,
% 1.24/0.68      k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) | ~v2_funct_1(X0) | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK1),X0))).
% 1.24/0.68  
% 1.24/0.68  cnf(u123,negated_conjecture,
% 1.24/0.68      k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) | ~v2_funct_1(X0) | k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK1),X0))).
% 1.24/0.68  
% 1.24/0.68  cnf(u94,negated_conjecture,
% 1.24/0.68      k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X0),k2_struct_0(sK1),X1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),k2_struct_0(sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),k2_struct_0(sK1)))) | ~l1_struct_0(X0) | ~v2_funct_1(X1) | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),k2_struct_0(sK1),X1))).
% 1.24/0.68  
% 1.24/0.68  cnf(u118,negated_conjecture,
% 1.24/0.68      k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X0),k2_struct_0(sK1),X1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),k2_struct_0(sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),k2_struct_0(sK1)))) | ~l1_struct_0(X0) | ~v2_funct_1(X1) | k2_struct_0(X0) = k2_relset_1(k2_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),k2_struct_0(sK1),X1))).
% 1.24/0.68  
% 1.24/0.68  cnf(u80,negated_conjecture,
% 1.24/0.68      k2_struct_0(sK0) != k1_relat_1(sK2) | ~v1_funct_2(k4_relat_1(sK2),k2_struct_0(sK1),k1_relat_1(sK2)) | ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2)))) | ~v2_funct_1(k4_relat_1(sK2)) | ~v1_funct_1(k4_relat_1(sK2)) | v1_funct_1(k2_funct_1(k4_relat_1(sK2)))).
% 1.24/0.68  
% 1.24/0.68  cnf(u82,negated_conjecture,
% 1.24/0.68      k2_struct_0(sK0) != k1_relat_1(sK2) | ~v1_funct_2(k4_relat_1(sK2),k2_struct_0(sK1),k1_relat_1(sK2)) | ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2)))) | ~v2_funct_1(k4_relat_1(sK2)) | ~v1_funct_1(k4_relat_1(sK2)) | v1_funct_2(k2_funct_1(k4_relat_1(sK2)),k1_relat_1(sK2),k2_struct_0(sK1))).
% 1.24/0.68  
% 1.24/0.68  cnf(u84,negated_conjecture,
% 1.24/0.68      k2_struct_0(sK0) != k1_relat_1(sK2) | ~v1_funct_2(k4_relat_1(sK2),k2_struct_0(sK1),k1_relat_1(sK2)) | ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2)))) | ~v2_funct_1(k4_relat_1(sK2)) | ~v1_funct_1(k4_relat_1(sK2)) | m1_subset_1(k2_funct_1(k4_relat_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))))).
% 1.24/0.68  
% 1.24/0.68  cnf(u86,negated_conjecture,
% 1.24/0.68      k2_struct_0(sK0) != k1_relat_1(sK2) | ~v1_funct_2(k4_relat_1(sK2),k2_struct_0(sK1),k1_relat_1(sK2)) | ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2)))) | ~v1_funct_1(k4_relat_1(sK2)) | ~v2_funct_1(k4_relat_1(sK2)) | k2_funct_1(k4_relat_1(sK2)) = k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k4_relat_1(sK2))).
% 1.24/0.68  
% 1.24/0.68  cnf(u106,negated_conjecture,
% 1.24/0.68      k2_struct_0(sK0) != k1_relat_1(sK2) | ~v1_funct_1(k4_relat_1(sK2)) | ~v1_funct_2(k4_relat_1(sK2),k2_struct_0(sK1),k1_relat_1(sK2)) | ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2)))) | ~v2_funct_1(k4_relat_1(sK2)) | k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k4_relat_1(sK2)))).
% 1.24/0.68  
% 1.24/0.68  cnf(u130,negated_conjecture,
% 1.24/0.68      k2_struct_0(sK0) != k1_relat_1(sK2) | ~v1_funct_1(k4_relat_1(sK2)) | ~v1_funct_2(k4_relat_1(sK2),k2_struct_0(sK1),k1_relat_1(sK2)) | ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2)))) | ~v2_funct_1(k4_relat_1(sK2)) | k2_struct_0(sK1) = k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k4_relat_1(sK2)))).
% 1.24/0.68  
% 1.24/0.68  cnf(u68,negated_conjecture,
% 1.24/0.68      k2_relat_1(k2_funct_1(sK2)) != k2_struct_0(sK0) | ~v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | ~v1_funct_1(k2_funct_1(sK2))).
% 1.24/0.68  
% 1.24/0.68  cnf(u43,axiom,
% 1.24/0.68      k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_struct_0(X0) | ~v2_funct_1(X2) | k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))).
% 1.24/0.68  
% 1.24/0.68  cnf(u44,axiom,
% 1.24/0.68      k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_struct_0(X0) | ~v2_funct_1(X2) | k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))).
% 1.24/0.68  
% 1.24/0.68  cnf(u52,axiom,
% 1.24/0.68      k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | v1_funct_1(k2_funct_1(X2))).
% 1.24/0.68  
% 1.24/0.68  cnf(u53,axiom,
% 1.24/0.68      k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | v1_funct_2(k2_funct_1(X2),X1,X0)).
% 1.24/0.68  
% 1.24/0.68  cnf(u54,axiom,
% 1.24/0.68      k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))).
% 1.24/0.68  
% 1.24/0.68  cnf(u55,axiom,
% 1.24/0.68      k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)).
% 1.24/0.68  
% 1.24/0.68  % (21319)# SZS output end Saturation.
% 1.24/0.68  % (21319)------------------------------
% 1.24/0.68  % (21319)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.68  % (21319)Termination reason: Satisfiable
% 1.24/0.68  
% 1.24/0.68  % (21319)Memory used [KB]: 6268
% 1.24/0.68  % (21319)Time elapsed: 0.097 s
% 1.24/0.68  % (21319)------------------------------
% 1.24/0.68  % (21319)------------------------------
% 1.24/0.68  % (21171)Success in time 0.323 s
%------------------------------------------------------------------------------
