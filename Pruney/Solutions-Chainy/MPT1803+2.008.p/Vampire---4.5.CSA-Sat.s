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
% DateTime   : Thu Dec  3 13:19:37 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 103 expanded)
%              Number of leaves         :  103 ( 103 expanded)
%              Depth                    :    0
%              Number of atoms          :  281 ( 281 expanded)
%              Number of equality atoms :   42 (  42 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u678,negated_conjecture,
    ( ~ ( u1_struct_0(sK0) != u1_struct_0(k8_tmap_1(sK0,sK3(sK0))) )
    | u1_struct_0(sK0) != u1_struct_0(k8_tmap_1(sK0,sK3(sK0))) )).

tff(u677,negated_conjecture,
    ( ~ ( k8_tmap_1(sK0,sK1) != k8_tmap_1(sK0,sK3(sK0)) )
    | k8_tmap_1(sK0,sK1) != k8_tmap_1(sK0,sK3(sK0)) )).

tff(u676,negated_conjecture,
    ( u1_struct_0(sK3(sK0)) != sK4(sK0,sK3(sK0),k8_tmap_1(sK0,sK1))
    | ~ ( k8_tmap_1(sK0,sK1) != k8_tmap_1(sK0,sK3(sK0)) )
    | k8_tmap_1(sK0,sK1) != k6_tmap_1(sK0,u1_struct_0(sK3(sK0))) )).

tff(u675,negated_conjecture,
    ( ~ ( k9_tmap_1(sK0,sK1) != k3_struct_0(sK0) )
    | k9_tmap_1(sK0,sK1) != k3_struct_0(sK0) )).

tff(u674,negated_conjecture,
    ( ~ ( u1_pre_topc(k8_tmap_1(sK0,sK3(sK0))) != k5_tmap_1(sK0,u1_struct_0(sK3(sK0))) )
    | u1_pre_topc(k8_tmap_1(sK0,sK3(sK0))) != k5_tmap_1(sK0,u1_struct_0(sK3(sK0))) )).

tff(u673,negated_conjecture,(
    u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) )).

tff(u672,negated_conjecture,
    ( u1_struct_0(sK3(sK0)) != sK4(sK0,sK3(sK0),k8_tmap_1(sK0,sK1))
    | u1_struct_0(sK3(sK0)) = sK4(sK0,sK3(sK0),k8_tmap_1(sK0,sK1)) )).

tff(u671,negated_conjecture,
    ( ~ ( k8_tmap_1(sK0,sK1) != k8_tmap_1(sK0,sK3(sK0)) )
    | u1_struct_0(sK1) = sK4(sK0,sK1,k8_tmap_1(sK0,sK3(sK0))) )).

tff(u670,negated_conjecture,(
    k7_tmap_1(sK0,u1_struct_0(sK1)) = k6_partfun1(u1_struct_0(sK0)) )).

tff(u669,negated_conjecture,(
    k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK3(sK0))) )).

tff(u668,negated_conjecture,(
    k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK3(k8_tmap_1(sK0,sK1)))) )).

tff(u667,negated_conjecture,(
    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) )).

tff(u666,negated_conjecture,(
    k8_tmap_1(sK0,sK3(sK0)) = k6_tmap_1(sK0,u1_struct_0(sK3(sK0))) )).

tff(u665,negated_conjecture,(
    u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1)) )).

tff(u664,axiom,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(sK3(X0),X0) ) )).

tff(u663,axiom,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) )).

tff(u662,negated_conjecture,(
    l1_pre_topc(sK0) )).

tff(u661,negated_conjecture,(
    l1_pre_topc(k8_tmap_1(sK0,sK1)) )).

tff(u660,negated_conjecture,(
    l1_pre_topc(k8_tmap_1(sK0,sK3(sK0))) )).

tff(u659,negated_conjecture,
    ( ~ ~ l1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK3(k8_tmap_1(sK0,sK1)))))
    | ~ l1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK3(k8_tmap_1(sK0,sK1))))) )).

tff(u658,negated_conjecture,(
    l1_struct_0(sK0) )).

tff(u657,negated_conjecture,(
    l1_struct_0(k8_tmap_1(sK0,sK1)) )).

tff(u656,negated_conjecture,(
    l1_struct_0(k8_tmap_1(sK0,sK3(sK0))) )).

tff(u655,axiom,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) )).

tff(u654,axiom,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X1,X0)
      | r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0))
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u653,axiom,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X1,X0)
      | u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u652,axiom,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X1,X0)
      | v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u651,axiom,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u650,axiom,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u649,axiom,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X1,X0)
      | v1_funct_1(k9_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u648,axiom,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X1,X0)
      | v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u647,axiom,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u646,axiom,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X1,X0)
      | u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u645,negated_conjecture,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X0,X1)
      | k8_tmap_1(sK0,sK1) = k8_tmap_1(X1,X0)
      | u1_struct_0(X0) = sK4(X1,X0,k8_tmap_1(sK0,sK1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) )).

tff(u644,negated_conjecture,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X1,X0)
      | k8_tmap_1(X0,X1) = k8_tmap_1(sK0,sK1)
      | m1_subset_1(sK4(X0,X1,k8_tmap_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u643,negated_conjecture,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X1,X0)
      | k8_tmap_1(X0,X1) = k8_tmap_1(sK0,sK1)
      | k8_tmap_1(sK0,sK1) != k6_tmap_1(X0,sK4(X0,X1,k8_tmap_1(sK0,sK1)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u642,negated_conjecture,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X1,X0)
      | k8_tmap_1(X0,X1) = k8_tmap_1(sK0,sK3(sK0))
      | k8_tmap_1(sK0,sK3(sK0)) != k6_tmap_1(X0,sK4(X0,X1,k8_tmap_1(sK0,sK3(sK0))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u641,negated_conjecture,(
    ! [X3,X2] :
      ( ~ m1_pre_topc(X3,X2)
      | k8_tmap_1(sK0,sK3(sK0)) = k8_tmap_1(X2,X3)
      | m1_subset_1(sK4(X2,X3,k8_tmap_1(sK0,sK3(sK0))),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) )).

tff(u640,negated_conjecture,(
    ! [X5,X4] :
      ( ~ m1_pre_topc(X4,X5)
      | k8_tmap_1(sK0,sK3(sK0)) = k8_tmap_1(X5,X4)
      | u1_struct_0(X4) = sK4(X5,X4,k8_tmap_1(sK0,sK3(sK0)))
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5) ) )).

tff(u639,negated_conjecture,(
    ! [X0] :
      ( ~ m1_pre_topc(sK1,X0)
      | r1_tmap_1(sK1,k6_tmap_1(X0,u1_struct_0(sK1)),k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK1)),k7_tmap_1(X0,u1_struct_0(sK1)),sK1),sK2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u638,negated_conjecture,(
    m1_pre_topc(sK1,sK0) )).

tff(u637,negated_conjecture,(
    m1_pre_topc(sK3(sK0),sK0) )).

tff(u636,negated_conjecture,(
    m1_pre_topc(sK3(k8_tmap_1(sK0,sK1)),k8_tmap_1(sK0,sK1)) )).

tff(u635,negated_conjecture,(
    m1_pre_topc(sK3(k8_tmap_1(sK0,sK3(sK0))),k8_tmap_1(sK0,sK3(sK0))) )).

tff(u634,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u633,negated_conjecture,(
    ~ v2_struct_0(sK1) )).

tff(u632,negated_conjecture,
    ( ~ ~ v2_struct_0(k6_tmap_1(sK0,u1_struct_0(sK3(k8_tmap_1(sK0,sK1)))))
    | ~ v2_struct_0(k6_tmap_1(sK0,u1_struct_0(sK3(k8_tmap_1(sK0,sK1))))) )).

tff(u631,negated_conjecture,
    ( ~ v2_struct_0(k8_tmap_1(sK0,sK1))
    | v2_struct_0(k8_tmap_1(sK0,sK1)) )).

tff(u630,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK3(sK0))))
    | v2_struct_0(k8_tmap_1(sK0,sK3(sK0))) )).

tff(u629,negated_conjecture,
    ( ~ v2_struct_0(sK3(sK0))
    | v2_struct_0(sK3(sK0)) )).

tff(u628,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) )).

tff(u627,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_xboole_0(u1_struct_0(sK0)) )).

tff(u626,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK3(sK0))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK3(sK0)))) )).

tff(u625,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK3(k8_tmap_1(sK0,sK1))))))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK3(k8_tmap_1(sK0,sK1)))))) )).

tff(u624,negated_conjecture,
    ( ~ ~ v1_funct_1(k3_struct_0(sK0))
    | ~ v1_funct_1(k3_struct_0(sK0)) )).

tff(u623,negated_conjecture,(
    v1_funct_1(k9_tmap_1(sK0,sK1)) )).

tff(u622,negated_conjecture,(
    v1_funct_1(k9_tmap_1(sK0,sK3(sK0))) )).

tff(u621,negated_conjecture,(
    v1_funct_1(k6_partfun1(u1_struct_0(sK0))) )).

tff(u620,negated_conjecture,
    ( ~ ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0)) )).

tff(u619,negated_conjecture,(
    v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) )).

tff(u618,negated_conjecture,(
    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0)) )).

tff(u617,negated_conjecture,(
    v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) )).

tff(u616,negated_conjecture,(
    v1_funct_2(k9_tmap_1(sK0,sK3(sK0)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK3(sK0)))) )).

tff(u615,negated_conjecture,(
    v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK3(sK0)))) )).

tff(u614,negated_conjecture,(
    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK3(k8_tmap_1(sK0,sK1)))),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK3(k8_tmap_1(sK0,sK1)))))) )).

tff(u613,negated_conjecture,(
    v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK3(k8_tmap_1(sK0,sK1)))))) )).

tff(u612,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u611,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u610,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u609,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_funct_1(k7_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u608,axiom,(
    ! [X1,X3,X5,X0,X2] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | r1_funct_2(X0,X1,X2,X3,X5,X5)
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X5,X0,X1)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) )).

tff(u607,axiom,(
    ! [X3,X0,X2] :
      ( ~ m1_subset_1(X3,u1_struct_0(X2))
      | r1_tmap_1(X2,k6_tmap_1(X0,u1_struct_0(X2)),k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u606,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | ! [X1,X0] :
        ( ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),X0,X1)
        | r1_funct_2(X0,X1,u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0)))
        | v1_xboole_0(X1) ) )).

tff(u605,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | ! [X1,X0] :
        ( ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | r1_funct_2(X0,X1,u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1))
        | ~ v1_funct_2(k9_tmap_1(sK0,sK1),X0,X1)
        | v1_xboole_0(X1) ) )).

tff(u604,negated_conjecture,
    ( ~ ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )).

tff(u603,negated_conjecture,(
    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u602,negated_conjecture,(
    m1_subset_1(u1_struct_0(sK3(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u601,negated_conjecture,(
    m1_subset_1(u1_struct_0(sK3(k8_tmap_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u600,negated_conjecture,(
    m1_subset_1(u1_struct_0(sK3(k8_tmap_1(sK0,sK3(sK0)))),k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK0,sK3(sK0))))) )).

tff(u599,negated_conjecture,(
    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )).

tff(u598,negated_conjecture,(
    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK3(k8_tmap_1(sK0,sK1)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK3(k8_tmap_1(sK0,sK1)))))))) )).

tff(u597,negated_conjecture,(
    m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )).

tff(u596,negated_conjecture,(
    m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK3(sK0)))))) )).

tff(u595,negated_conjecture,(
    m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK3(k8_tmap_1(sK0,sK1)))))))) )).

tff(u594,negated_conjecture,(
    m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )).

tff(u593,negated_conjecture,(
    m1_subset_1(k9_tmap_1(sK0,sK3(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK3(sK0)))))) )).

tff(u592,negated_conjecture,(
    m1_subset_1(sK2,u1_struct_0(sK1)) )).

tff(u591,axiom,(
    ! [X1,X3,X5,X0,X2,X4] :
      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
      | X4 = X5
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) )).

tff(u590,negated_conjecture,
    ( ~ ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK3(sK0))),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK3(sK0)),k3_struct_0(sK0))
    | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK3(sK0))),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK3(sK0)),k3_struct_0(sK0)) )).

tff(u589,negated_conjecture,(
    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k3_struct_0(sK0)) )).

tff(u588,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1)) )).

tff(u587,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0))) )).

tff(u586,negated_conjecture,(
    v2_pre_topc(sK0) )).

tff(u585,negated_conjecture,(
    v2_pre_topc(k8_tmap_1(sK0,sK1)) )).

tff(u584,negated_conjecture,(
    v2_pre_topc(k8_tmap_1(sK0,sK3(sK0))) )).

tff(u583,axiom,(
    ! [X1,X0,X2] :
      ( ~ v1_pre_topc(X2)
      | k6_tmap_1(X0,sK4(X0,X1,X2)) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | k8_tmap_1(X0,X1) = X2
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u582,axiom,(
    ! [X1,X0,X2] :
      ( ~ v1_pre_topc(X2)
      | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | k8_tmap_1(X0,X1) = X2
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u581,axiom,(
    ! [X1,X0,X2] :
      ( ~ v1_pre_topc(X2)
      | u1_struct_0(X1) = sK4(X0,X1,X2)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | k8_tmap_1(X0,X1) = X2
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u580,axiom,(
    ! [X1,X0] :
      ( ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u579,negated_conjecture,(
    v1_pre_topc(k8_tmap_1(sK0,sK1)) )).

tff(u578,negated_conjecture,(
    v1_pre_topc(k8_tmap_1(sK0,sK3(sK0))) )).

tff(u577,negated_conjecture,(
    ~ r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),sK2) )).

tff(u576,negated_conjecture,(
    r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),sK2) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:18:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (29780)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.47  % (29767)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.47  % (29767)Refutation not found, incomplete strategy% (29767)------------------------------
% 0.22/0.47  % (29767)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (29767)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (29767)Memory used [KB]: 1791
% 0.22/0.47  % (29767)Time elapsed: 0.059 s
% 0.22/0.47  % (29767)------------------------------
% 0.22/0.47  % (29767)------------------------------
% 0.22/0.49  % (29765)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.49  % (29764)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.50  % (29773)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (29782)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.51  % (29761)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (29777)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.51  % (29785)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.51  % (29760)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.51  % (29765)Refutation not found, incomplete strategy% (29765)------------------------------
% 0.22/0.51  % (29765)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (29765)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (29765)Memory used [KB]: 6396
% 0.22/0.51  % (29765)Time elapsed: 0.097 s
% 0.22/0.51  % (29765)------------------------------
% 0.22/0.51  % (29765)------------------------------
% 0.22/0.51  % (29760)Refutation not found, incomplete strategy% (29760)------------------------------
% 0.22/0.51  % (29760)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (29760)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (29760)Memory used [KB]: 10618
% 0.22/0.51  % (29760)Time elapsed: 0.090 s
% 0.22/0.51  % (29760)------------------------------
% 0.22/0.51  % (29760)------------------------------
% 0.22/0.51  % (29773)Refutation not found, incomplete strategy% (29773)------------------------------
% 0.22/0.51  % (29773)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (29773)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (29773)Memory used [KB]: 6268
% 0.22/0.51  % (29773)Time elapsed: 0.116 s
% 0.22/0.51  % (29773)------------------------------
% 0.22/0.51  % (29773)------------------------------
% 0.22/0.51  % (29768)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.51  % (29762)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.52  % (29779)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.52  % (29769)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.52  % (29771)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  % (29776)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.52  % (29770)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.53  % (29771)Refutation not found, incomplete strategy% (29771)------------------------------
% 0.22/0.53  % (29771)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (29771)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (29771)Memory used [KB]: 10618
% 0.22/0.53  % (29771)Time elapsed: 0.106 s
% 0.22/0.53  % (29771)------------------------------
% 0.22/0.53  % (29771)------------------------------
% 0.22/0.53  % (29763)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.53  % (29783)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.53  % (29774)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.53  % (29775)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.53  % (29772)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.54  % (29761)Refutation not found, incomplete strategy% (29761)------------------------------
% 0.22/0.54  % (29761)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (29761)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (29761)Memory used [KB]: 11001
% 0.22/0.54  % (29761)Time elapsed: 0.099 s
% 0.22/0.54  % (29761)------------------------------
% 0.22/0.54  % (29761)------------------------------
% 0.22/0.54  % (29781)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.54  % (29766)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.54  % (29766)Refutation not found, incomplete strategy% (29766)------------------------------
% 0.22/0.54  % (29766)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (29766)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (29766)Memory used [KB]: 10618
% 0.22/0.54  % (29766)Time elapsed: 0.106 s
% 0.22/0.54  % (29766)------------------------------
% 0.22/0.54  % (29766)------------------------------
% 0.22/0.54  % (29778)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.54  % (29784)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.55  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.55  % (29770)# SZS output start Saturation.
% 0.22/0.55  tff(u678,negated_conjecture,
% 0.22/0.55      ((~(u1_struct_0(sK0) != u1_struct_0(k8_tmap_1(sK0,sK3(sK0))))) | (u1_struct_0(sK0) != u1_struct_0(k8_tmap_1(sK0,sK3(sK0)))))).
% 0.22/0.55  
% 0.22/0.55  tff(u677,negated_conjecture,
% 0.22/0.55      ((~(k8_tmap_1(sK0,sK1) != k8_tmap_1(sK0,sK3(sK0)))) | (k8_tmap_1(sK0,sK1) != k8_tmap_1(sK0,sK3(sK0))))).
% 0.22/0.55  
% 0.22/0.55  tff(u676,negated_conjecture,
% 0.22/0.55      ((~(u1_struct_0(sK3(sK0)) = sK4(sK0,sK3(sK0),k8_tmap_1(sK0,sK1)))) | (~(k8_tmap_1(sK0,sK1) != k8_tmap_1(sK0,sK3(sK0)))) | (k8_tmap_1(sK0,sK1) != k6_tmap_1(sK0,u1_struct_0(sK3(sK0)))))).
% 0.22/0.55  
% 0.22/0.55  tff(u675,negated_conjecture,
% 0.22/0.55      ((~(k9_tmap_1(sK0,sK1) != k3_struct_0(sK0))) | (k9_tmap_1(sK0,sK1) != k3_struct_0(sK0)))).
% 0.22/0.55  
% 0.22/0.55  tff(u674,negated_conjecture,
% 0.22/0.55      ((~(u1_pre_topc(k8_tmap_1(sK0,sK3(sK0))) != k5_tmap_1(sK0,u1_struct_0(sK3(sK0))))) | (u1_pre_topc(k8_tmap_1(sK0,sK3(sK0))) != k5_tmap_1(sK0,u1_struct_0(sK3(sK0)))))).
% 0.22/0.55  
% 0.22/0.55  tff(u673,negated_conjecture,
% 0.22/0.55      (u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)))).
% 0.22/0.55  
% 0.22/0.55  tff(u672,negated_conjecture,
% 0.22/0.55      ((~(u1_struct_0(sK3(sK0)) = sK4(sK0,sK3(sK0),k8_tmap_1(sK0,sK1)))) | (u1_struct_0(sK3(sK0)) = sK4(sK0,sK3(sK0),k8_tmap_1(sK0,sK1))))).
% 0.22/0.55  
% 0.22/0.55  tff(u671,negated_conjecture,
% 0.22/0.55      ((~(k8_tmap_1(sK0,sK1) != k8_tmap_1(sK0,sK3(sK0)))) | (u1_struct_0(sK1) = sK4(sK0,sK1,k8_tmap_1(sK0,sK3(sK0)))))).
% 0.22/0.55  
% 0.22/0.55  tff(u670,negated_conjecture,
% 0.22/0.55      (k7_tmap_1(sK0,u1_struct_0(sK1)) = k6_partfun1(u1_struct_0(sK0)))).
% 0.22/0.55  
% 0.22/0.55  tff(u669,negated_conjecture,
% 0.22/0.55      (k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK3(sK0))))).
% 0.22/0.55  
% 0.22/0.55  tff(u668,negated_conjecture,
% 0.22/0.55      (k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK3(k8_tmap_1(sK0,sK1)))))).
% 0.22/0.55  
% 0.22/0.55  tff(u667,negated_conjecture,
% 0.22/0.55      (k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)))).
% 0.22/0.55  
% 0.22/0.55  tff(u666,negated_conjecture,
% 0.22/0.55      (k8_tmap_1(sK0,sK3(sK0)) = k6_tmap_1(sK0,u1_struct_0(sK3(sK0))))).
% 0.22/0.55  
% 0.22/0.55  tff(u665,negated_conjecture,
% 0.22/0.55      (u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1)))).
% 0.22/0.55  
% 0.22/0.55  tff(u664,axiom,
% 0.22/0.55      (![X0] : ((~l1_pre_topc(X0) | m1_pre_topc(sK3(X0),X0))))).
% 0.22/0.55  
% 0.22/0.55  tff(u663,axiom,
% 0.22/0.55      (![X0] : ((~l1_pre_topc(X0) | l1_struct_0(X0))))).
% 0.22/0.55  
% 0.22/0.55  tff(u662,negated_conjecture,
% 0.22/0.55      l1_pre_topc(sK0)).
% 0.22/0.55  
% 0.22/0.55  tff(u661,negated_conjecture,
% 0.22/0.55      l1_pre_topc(k8_tmap_1(sK0,sK1))).
% 0.22/0.55  
% 0.22/0.55  tff(u660,negated_conjecture,
% 0.22/0.55      l1_pre_topc(k8_tmap_1(sK0,sK3(sK0)))).
% 0.22/0.55  
% 0.22/0.55  tff(u659,negated_conjecture,
% 0.22/0.55      ((~~l1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK3(k8_tmap_1(sK0,sK1)))))) | ~l1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK3(k8_tmap_1(sK0,sK1))))))).
% 0.22/0.55  
% 0.22/0.55  tff(u658,negated_conjecture,
% 0.22/0.55      l1_struct_0(sK0)).
% 0.22/0.55  
% 0.22/0.55  tff(u657,negated_conjecture,
% 0.22/0.55      l1_struct_0(k8_tmap_1(sK0,sK1))).
% 0.22/0.55  
% 0.22/0.55  tff(u656,negated_conjecture,
% 0.22/0.55      l1_struct_0(k8_tmap_1(sK0,sK3(sK0)))).
% 0.22/0.55  
% 0.22/0.55  tff(u655,axiom,
% 0.22/0.55      (![X1, X0] : ((~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))))).
% 0.22/0.55  
% 0.22/0.55  tff(u654,axiom,
% 0.22/0.55      (![X1, X0] : ((~m1_pre_topc(X1,X0) | r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0)) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 0.22/0.55  
% 0.22/0.55  tff(u653,axiom,
% 0.22/0.55      (![X1, X0] : ((~m1_pre_topc(X1,X0) | (u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 0.22/0.55  
% 0.22/0.55  tff(u652,axiom,
% 0.22/0.55      (![X1, X0] : ((~m1_pre_topc(X1,X0) | v1_pre_topc(k8_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 0.22/0.55  
% 0.22/0.55  tff(u651,axiom,
% 0.22/0.55      (![X1, X0] : ((~m1_pre_topc(X1,X0) | v2_pre_topc(k8_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 0.22/0.55  
% 0.22/0.55  tff(u650,axiom,
% 0.22/0.55      (![X1, X0] : ((~m1_pre_topc(X1,X0) | l1_pre_topc(k8_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 0.22/0.55  
% 0.22/0.55  tff(u649,axiom,
% 0.22/0.55      (![X1, X0] : ((~m1_pre_topc(X1,X0) | v1_funct_1(k9_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 0.22/0.55  
% 0.22/0.55  tff(u648,axiom,
% 0.22/0.55      (![X1, X0] : ((~m1_pre_topc(X1,X0) | v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 0.22/0.55  
% 0.22/0.55  tff(u647,axiom,
% 0.22/0.55      (![X1, X0] : ((~m1_pre_topc(X1,X0) | m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 0.22/0.55  
% 0.22/0.55  tff(u646,axiom,
% 0.22/0.55      (![X1, X0] : ((~m1_pre_topc(X1,X0) | (u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1))) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 0.22/0.55  
% 0.22/0.55  tff(u645,negated_conjecture,
% 0.22/0.55      (![X1, X0] : ((~m1_pre_topc(X0,X1) | (k8_tmap_1(sK0,sK1) = k8_tmap_1(X1,X0)) | (u1_struct_0(X0) = sK4(X1,X0,k8_tmap_1(sK0,sK1))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))))).
% 0.22/0.55  
% 0.22/0.55  tff(u644,negated_conjecture,
% 0.22/0.55      (![X1, X0] : ((~m1_pre_topc(X1,X0) | (k8_tmap_1(X0,X1) = k8_tmap_1(sK0,sK1)) | m1_subset_1(sK4(X0,X1,k8_tmap_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 0.22/0.55  
% 0.22/0.55  tff(u643,negated_conjecture,
% 0.22/0.55      (![X1, X0] : ((~m1_pre_topc(X1,X0) | (k8_tmap_1(X0,X1) = k8_tmap_1(sK0,sK1)) | (k8_tmap_1(sK0,sK1) != k6_tmap_1(X0,sK4(X0,X1,k8_tmap_1(sK0,sK1)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 0.22/0.55  
% 0.22/0.55  tff(u642,negated_conjecture,
% 0.22/0.55      (![X1, X0] : ((~m1_pre_topc(X1,X0) | (k8_tmap_1(X0,X1) = k8_tmap_1(sK0,sK3(sK0))) | (k8_tmap_1(sK0,sK3(sK0)) != k6_tmap_1(X0,sK4(X0,X1,k8_tmap_1(sK0,sK3(sK0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 0.22/0.55  
% 0.22/0.55  tff(u641,negated_conjecture,
% 0.22/0.55      (![X3, X2] : ((~m1_pre_topc(X3,X2) | (k8_tmap_1(sK0,sK3(sK0)) = k8_tmap_1(X2,X3)) | m1_subset_1(sK4(X2,X3,k8_tmap_1(sK0,sK3(sK0))),k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2))))).
% 0.22/0.55  
% 0.22/0.55  tff(u640,negated_conjecture,
% 0.22/0.55      (![X5, X4] : ((~m1_pre_topc(X4,X5) | (k8_tmap_1(sK0,sK3(sK0)) = k8_tmap_1(X5,X4)) | (u1_struct_0(X4) = sK4(X5,X4,k8_tmap_1(sK0,sK3(sK0)))) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5))))).
% 0.22/0.55  
% 0.22/0.55  tff(u639,negated_conjecture,
% 0.22/0.55      (![X0] : ((~m1_pre_topc(sK1,X0) | r1_tmap_1(sK1,k6_tmap_1(X0,u1_struct_0(sK1)),k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK1)),k7_tmap_1(X0,u1_struct_0(sK1)),sK1),sK2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 0.22/0.55  
% 0.22/0.55  tff(u638,negated_conjecture,
% 0.22/0.55      m1_pre_topc(sK1,sK0)).
% 0.22/0.55  
% 0.22/0.55  tff(u637,negated_conjecture,
% 0.22/0.55      m1_pre_topc(sK3(sK0),sK0)).
% 0.22/0.55  
% 0.22/0.55  tff(u636,negated_conjecture,
% 0.22/0.55      m1_pre_topc(sK3(k8_tmap_1(sK0,sK1)),k8_tmap_1(sK0,sK1))).
% 0.22/0.55  
% 0.22/0.55  tff(u635,negated_conjecture,
% 0.22/0.55      m1_pre_topc(sK3(k8_tmap_1(sK0,sK3(sK0))),k8_tmap_1(sK0,sK3(sK0)))).
% 0.22/0.55  
% 0.22/0.55  tff(u634,negated_conjecture,
% 0.22/0.55      ~v2_struct_0(sK0)).
% 0.22/0.55  
% 0.22/0.55  tff(u633,negated_conjecture,
% 0.22/0.55      ~v2_struct_0(sK1)).
% 0.22/0.55  
% 0.22/0.55  tff(u632,negated_conjecture,
% 0.22/0.55      ((~~v2_struct_0(k6_tmap_1(sK0,u1_struct_0(sK3(k8_tmap_1(sK0,sK1)))))) | ~v2_struct_0(k6_tmap_1(sK0,u1_struct_0(sK3(k8_tmap_1(sK0,sK1))))))).
% 0.22/0.55  
% 0.22/0.55  tff(u631,negated_conjecture,
% 0.22/0.55      ((~v2_struct_0(k8_tmap_1(sK0,sK1))) | v2_struct_0(k8_tmap_1(sK0,sK1)))).
% 0.22/0.55  
% 0.22/0.55  tff(u630,negated_conjecture,
% 0.22/0.55      ((~v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK3(sK0))))) | v2_struct_0(k8_tmap_1(sK0,sK3(sK0))))).
% 0.22/0.55  
% 0.22/0.55  tff(u629,negated_conjecture,
% 0.22/0.55      ((~v2_struct_0(sK3(sK0))) | v2_struct_0(sK3(sK0)))).
% 0.22/0.55  
% 0.22/0.55  tff(u628,axiom,
% 0.22/0.55      (![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))))).
% 0.22/0.55  
% 0.22/0.55  tff(u627,negated_conjecture,
% 0.22/0.55      ((~~v1_xboole_0(u1_struct_0(sK0))) | ~v1_xboole_0(u1_struct_0(sK0)))).
% 0.22/0.55  
% 0.22/0.55  tff(u626,negated_conjecture,
% 0.22/0.55      ((~v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK3(sK0))))) | v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK3(sK0)))))).
% 0.22/0.55  
% 0.22/0.55  tff(u625,negated_conjecture,
% 0.22/0.55      ((~v1_xboole_0(u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK3(k8_tmap_1(sK0,sK1))))))) | v1_xboole_0(u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK3(k8_tmap_1(sK0,sK1)))))))).
% 0.22/0.55  
% 0.22/0.55  tff(u624,negated_conjecture,
% 0.22/0.55      ((~~v1_funct_1(k3_struct_0(sK0))) | ~v1_funct_1(k3_struct_0(sK0)))).
% 0.22/0.55  
% 0.22/0.55  tff(u623,negated_conjecture,
% 0.22/0.55      v1_funct_1(k9_tmap_1(sK0,sK1))).
% 0.22/0.55  
% 0.22/0.55  tff(u622,negated_conjecture,
% 0.22/0.55      v1_funct_1(k9_tmap_1(sK0,sK3(sK0)))).
% 0.22/0.55  
% 0.22/0.55  tff(u621,negated_conjecture,
% 0.22/0.55      v1_funct_1(k6_partfun1(u1_struct_0(sK0)))).
% 0.22/0.55  
% 0.22/0.55  tff(u620,negated_conjecture,
% 0.22/0.55      ((~~v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))) | ~v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0)))).
% 0.22/0.55  
% 0.22/0.55  tff(u619,negated_conjecture,
% 0.22/0.55      v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))).
% 0.22/0.55  
% 0.22/0.55  tff(u618,negated_conjecture,
% 0.22/0.55      v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0))).
% 0.22/0.55  
% 0.22/0.55  tff(u617,negated_conjecture,
% 0.22/0.55      v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))).
% 0.22/0.55  
% 0.22/0.55  tff(u616,negated_conjecture,
% 0.22/0.55      v1_funct_2(k9_tmap_1(sK0,sK3(sK0)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK3(sK0))))).
% 0.22/0.55  
% 0.22/0.55  tff(u615,negated_conjecture,
% 0.22/0.55      v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK3(sK0))))).
% 0.22/0.55  
% 0.22/0.55  tff(u614,negated_conjecture,
% 0.22/0.55      v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK3(k8_tmap_1(sK0,sK1)))),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK3(k8_tmap_1(sK0,sK1))))))).
% 0.22/0.55  
% 0.22/0.55  tff(u613,negated_conjecture,
% 0.22/0.55      v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK3(k8_tmap_1(sK0,sK1))))))).
% 0.22/0.55  
% 0.22/0.55  tff(u612,axiom,
% 0.22/0.55      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 0.22/0.55  
% 0.22/0.55  tff(u611,axiom,
% 0.22/0.55      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 0.22/0.55  
% 0.22/0.55  tff(u610,axiom,
% 0.22/0.55      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 0.22/0.55  
% 0.22/0.55  tff(u609,axiom,
% 0.22/0.55      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_funct_1(k7_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 0.22/0.55  
% 0.22/0.55  tff(u608,axiom,
% 0.22/0.55      (![X1, X3, X5, X0, X2] : ((~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | r1_funct_2(X0,X1,X2,X3,X5,X5) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X5,X0,X1) | v1_xboole_0(X3) | v1_xboole_0(X1))))).
% 0.22/0.55  
% 0.22/0.55  tff(u607,axiom,
% 0.22/0.55      (![X3, X0, X2] : ((~m1_subset_1(X3,u1_struct_0(X2)) | r1_tmap_1(X2,k6_tmap_1(X0,u1_struct_0(X2)),k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 0.22/0.55  
% 0.22/0.55  tff(u606,negated_conjecture,
% 0.22/0.55      ((~~v1_xboole_0(u1_struct_0(sK0))) | (![X1, X0] : ((~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),X0,X1) | r1_funct_2(X0,X1,u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0))) | v1_xboole_0(X1)))))).
% 0.22/0.55  
% 0.22/0.55  tff(u605,negated_conjecture,
% 0.22/0.55      ((~~v1_xboole_0(u1_struct_0(sK0))) | (![X1, X0] : ((~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r1_funct_2(X0,X1,u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1)) | ~v1_funct_2(k9_tmap_1(sK0,sK1),X0,X1) | v1_xboole_0(X1)))))).
% 0.22/0.55  
% 0.22/0.55  tff(u604,negated_conjecture,
% 0.22/0.55      ((~~m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) | ~m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))).
% 0.22/0.55  
% 0.22/0.55  tff(u603,negated_conjecture,
% 0.22/0.55      m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.22/0.55  
% 0.22/0.55  tff(u602,negated_conjecture,
% 0.22/0.55      m1_subset_1(u1_struct_0(sK3(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.22/0.55  
% 0.22/0.55  tff(u601,negated_conjecture,
% 0.22/0.55      m1_subset_1(u1_struct_0(sK3(k8_tmap_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.22/0.55  
% 0.22/0.55  tff(u600,negated_conjecture,
% 0.22/0.55      m1_subset_1(u1_struct_0(sK3(k8_tmap_1(sK0,sK3(sK0)))),k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK0,sK3(sK0)))))).
% 0.22/0.55  
% 0.22/0.55  tff(u599,negated_conjecture,
% 0.22/0.55      m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))).
% 0.22/0.55  
% 0.22/0.55  tff(u598,negated_conjecture,
% 0.22/0.55      m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK3(k8_tmap_1(sK0,sK1)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK3(k8_tmap_1(sK0,sK1))))))))).
% 0.22/0.55  
% 0.22/0.55  tff(u597,negated_conjecture,
% 0.22/0.55      m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))).
% 0.22/0.55  
% 0.22/0.55  tff(u596,negated_conjecture,
% 0.22/0.55      m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK3(sK0))))))).
% 0.22/0.55  
% 0.22/0.55  tff(u595,negated_conjecture,
% 0.22/0.55      m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK3(k8_tmap_1(sK0,sK1))))))))).
% 0.22/0.55  
% 0.22/0.55  tff(u594,negated_conjecture,
% 0.22/0.55      m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))).
% 0.22/0.55  
% 0.22/0.55  tff(u593,negated_conjecture,
% 0.22/0.55      m1_subset_1(k9_tmap_1(sK0,sK3(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK3(sK0))))))).
% 0.22/0.55  
% 0.22/0.55  tff(u592,negated_conjecture,
% 0.22/0.55      m1_subset_1(sK2,u1_struct_0(sK1))).
% 0.22/0.55  
% 0.22/0.55  tff(u591,axiom,
% 0.22/0.55      (![X1, X3, X5, X0, X2, X4] : ((~r1_funct_2(X0,X1,X2,X3,X4,X5) | (X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))))).
% 0.22/0.55  
% 0.22/0.55  tff(u590,negated_conjecture,
% 0.22/0.55      ((~~r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK3(sK0))),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK3(sK0)),k3_struct_0(sK0))) | ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK3(sK0))),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK3(sK0)),k3_struct_0(sK0)))).
% 0.22/0.55  
% 0.22/0.55  tff(u589,negated_conjecture,
% 0.22/0.55      r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k3_struct_0(sK0))).
% 0.22/0.55  
% 0.22/0.55  tff(u588,negated_conjecture,
% 0.22/0.55      ((~~v1_xboole_0(u1_struct_0(sK0))) | r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1)))).
% 0.22/0.55  
% 0.22/0.55  tff(u587,negated_conjecture,
% 0.22/0.55      ((~~v1_xboole_0(u1_struct_0(sK0))) | r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0))))).
% 0.22/0.55  
% 0.22/0.55  tff(u586,negated_conjecture,
% 0.22/0.55      v2_pre_topc(sK0)).
% 0.22/0.55  
% 0.22/0.55  tff(u585,negated_conjecture,
% 0.22/0.55      v2_pre_topc(k8_tmap_1(sK0,sK1))).
% 0.22/0.55  
% 0.22/0.55  tff(u584,negated_conjecture,
% 0.22/0.55      v2_pre_topc(k8_tmap_1(sK0,sK3(sK0)))).
% 0.22/0.55  
% 0.22/0.55  tff(u583,axiom,
% 0.22/0.55      (![X1, X0, X2] : ((~v1_pre_topc(X2) | (k6_tmap_1(X0,sK4(X0,X1,X2)) != X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | (k8_tmap_1(X0,X1) = X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 0.22/0.55  
% 0.22/0.55  tff(u582,axiom,
% 0.22/0.55      (![X1, X0, X2] : ((~v1_pre_topc(X2) | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | (k8_tmap_1(X0,X1) = X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 0.22/0.55  
% 0.22/0.55  tff(u581,axiom,
% 0.22/0.55      (![X1, X0, X2] : ((~v1_pre_topc(X2) | (u1_struct_0(X1) = sK4(X0,X1,X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | (k8_tmap_1(X0,X1) = X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 0.22/0.55  
% 0.22/0.55  tff(u580,axiom,
% 0.22/0.55      (![X1, X0] : ((~v1_pre_topc(k8_tmap_1(X0,X1)) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 0.22/0.55  
% 0.22/0.55  tff(u579,negated_conjecture,
% 0.22/0.55      v1_pre_topc(k8_tmap_1(sK0,sK1))).
% 0.22/0.55  
% 0.22/0.55  tff(u578,negated_conjecture,
% 0.22/0.55      v1_pre_topc(k8_tmap_1(sK0,sK3(sK0)))).
% 0.22/0.55  
% 0.22/0.55  tff(u577,negated_conjecture,
% 0.22/0.55      ~r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),sK2)).
% 0.22/0.55  
% 0.22/0.55  tff(u576,negated_conjecture,
% 0.22/0.55      r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),sK2)).
% 0.22/0.55  
% 0.22/0.55  % (29770)# SZS output end Saturation.
% 0.22/0.55  % (29770)------------------------------
% 0.22/0.55  % (29770)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (29770)Termination reason: Satisfiable
% 0.22/0.55  
% 0.22/0.55  % (29770)Memory used [KB]: 10874
% 0.22/0.55  % (29770)Time elapsed: 0.121 s
% 0.22/0.55  % (29770)------------------------------
% 0.22/0.55  % (29770)------------------------------
% 0.22/0.55  % (29759)Success in time 0.189 s
%------------------------------------------------------------------------------
