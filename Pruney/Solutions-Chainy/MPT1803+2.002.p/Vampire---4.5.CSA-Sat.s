%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:36 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 111 expanded)
%              Number of leaves         :  111 ( 111 expanded)
%              Depth                    :    0
%              Number of atoms          :  393 ( 393 expanded)
%              Number of equality atoms :   81 (  81 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u742,negated_conjecture,
    ( ~ ( u1_struct_0(sK1) != sK4(sK0,sK1,k9_tmap_1(sK0,sK0)) )
    | u1_struct_0(sK1) != sK4(sK0,sK1,k9_tmap_1(sK0,sK0)) )).

tff(u741,negated_conjecture,
    ( ~ ( u1_struct_0(sK0) != u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1))) )
    | u1_struct_0(sK0) != u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1))) )).

tff(u740,negated_conjecture,
    ( ~ ( u1_struct_0(sK0) != sK3(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1)) )
    | u1_struct_0(sK0) != sK3(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1)) )).

tff(u739,negated_conjecture,
    ( ~ ( k8_tmap_1(sK0,sK1) != k8_tmap_1(sK0,sK0) )
    | k8_tmap_1(sK0,sK1) != k8_tmap_1(sK0,sK0) )).

tff(u738,negated_conjecture,
    ( ~ ( k8_tmap_1(sK0,sK1) != k8_tmap_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1)) )
    | k8_tmap_1(sK0,sK1) != k8_tmap_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1)) )).

tff(u737,negated_conjecture,
    ( ~ ( k8_tmap_1(sK0,sK1) != k8_tmap_1(sK0,sK0) )
    | k8_tmap_1(sK0,sK0) != k6_tmap_1(sK0,u1_struct_0(sK1)) )).

tff(u736,negated_conjecture,
    ( ~ ( k9_tmap_1(sK0,sK1) != k6_partfun1(u1_struct_0(sK0)) )
    | k9_tmap_1(sK0,sK1) != k6_partfun1(u1_struct_0(sK0)) )).

tff(u735,negated_conjecture,
    ( ~ ( k9_tmap_1(sK0,sK1) != k6_partfun1(u1_struct_0(sK0)) )
    | k9_tmap_1(sK0,sK1) != k9_tmap_1(sK0,sK0)
    | k9_tmap_1(sK0,sK0) != k6_partfun1(u1_struct_0(sK0)) )).

tff(u734,negated_conjecture,
    ( ~ ( u1_pre_topc(k8_tmap_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1))) != k5_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(sK0)) )
    | u1_pre_topc(k8_tmap_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1))) != k5_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(sK0)) )).

tff(u733,negated_conjecture,(
    u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) )).

tff(u732,negated_conjecture,(
    u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK0)) )).

tff(u731,negated_conjecture,
    ( u1_struct_0(sK0) != sK3(sK0,sK0,k8_tmap_1(sK0,sK1))
    | u1_struct_0(sK0) = sK3(sK0,sK0,k8_tmap_1(sK0,sK1)) )).

tff(u730,negated_conjecture,
    ( ~ ( k8_tmap_1(sK0,sK1) != k8_tmap_1(sK0,sK0) )
    | u1_struct_0(sK1) = sK3(sK0,sK1,k8_tmap_1(sK0,sK0)) )).

tff(u729,negated_conjecture,(
    k7_tmap_1(sK0,u1_struct_0(sK1)) = k6_partfun1(u1_struct_0(sK0)) )).

tff(u728,negated_conjecture,(
    k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK0)) )).

% (5631)Refutation not found, incomplete strategy% (5631)------------------------------
% (5631)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (5631)Termination reason: Refutation not found, incomplete strategy

% (5631)Memory used [KB]: 10618
% (5631)Time elapsed: 0.124 s
% (5631)------------------------------
% (5631)------------------------------
tff(u727,negated_conjecture,
    ( ~ ! [X9] :
          ( ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
          | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK1),X9) )
    | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(sK1)) )).

tff(u726,negated_conjecture,
    ( ~ ! [X9] :
          ( ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
          | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK1),X9) )
    | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(sK0)) )).

tff(u725,negated_conjecture,(
    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) )).

tff(u724,negated_conjecture,(
    k8_tmap_1(sK0,sK0) = k6_tmap_1(sK0,u1_struct_0(sK0)) )).

tff(u723,negated_conjecture,
    ( k9_tmap_1(sK0,sK1) != k9_tmap_1(sK0,sK0)
    | k9_tmap_1(sK0,sK1) = k9_tmap_1(sK0,sK0) )).

tff(u722,negated_conjecture,(
    u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1)) )).

tff(u721,negated_conjecture,(
    u1_pre_topc(k8_tmap_1(sK0,sK0)) = k5_tmap_1(sK0,u1_struct_0(sK0)) )).

tff(u720,axiom,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) )).

tff(u719,axiom,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) )).

tff(u718,negated_conjecture,
    ( ~ ~ l1_pre_topc(k8_tmap_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1)))
    | ~ l1_pre_topc(k8_tmap_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1))) )).

tff(u717,negated_conjecture,(
    l1_pre_topc(sK0) )).

tff(u716,negated_conjecture,(
    l1_pre_topc(k8_tmap_1(sK0,sK1)) )).

tff(u715,negated_conjecture,(
    l1_pre_topc(k8_tmap_1(sK0,sK0)) )).

tff(u714,negated_conjecture,(
    l1_struct_0(sK0) )).

tff(u713,negated_conjecture,(
    l1_struct_0(k8_tmap_1(sK0,sK1)) )).

tff(u712,negated_conjecture,(
    l1_struct_0(k8_tmap_1(sK0,sK0)) )).

tff(u711,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u710,negated_conjecture,(
    ~ v2_struct_0(sK1) )).

tff(u709,negated_conjecture,
    ( ~ v2_struct_0(k8_tmap_1(sK0,sK0))
    | v2_struct_0(k8_tmap_1(sK0,sK0)) )).

tff(u708,negated_conjecture,
    ( ~ v2_struct_0(k8_tmap_1(sK0,sK1))
    | v2_struct_0(k8_tmap_1(sK0,sK1)) )).

tff(u707,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) )).

tff(u706,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_xboole_0(u1_struct_0(sK0)) )).

tff(u705,negated_conjecture,
    ( ~ ~ v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
    | ~ v1_funct_1(k6_partfun1(u1_struct_0(sK0))) )).

tff(u704,negated_conjecture,
    ( ~ ~ v1_funct_1(k9_tmap_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k9_tmap_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1))) )).

tff(u703,negated_conjecture,(
    v1_funct_1(k9_tmap_1(sK0,sK1)) )).

tff(u702,negated_conjecture,(
    v1_funct_1(k9_tmap_1(sK0,sK0)) )).

tff(u701,negated_conjecture,
    ( ~ ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) )).

tff(u700,negated_conjecture,
    ( ~ ~ v1_funct_2(k9_tmap_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1))))
    | ~ v1_funct_2(k9_tmap_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1)))) )).

tff(u699,negated_conjecture,(
    v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) )).

tff(u698,negated_conjecture,(
    v1_funct_2(k9_tmap_1(sK0,sK0),u1_struct_0(sK0),u1_struct_0(sK0)) )).

tff(u697,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u696,negated_conjecture,
    ( ~ ! [X9] :
          ( ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
          | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK1),X9) )
    | ! [X9] :
        ( ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
        | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK1),X9) ) )).

tff(u695,axiom,(
    ! [X1,X3,X5,X0,X2] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | r1_funct_2(X0,X1,X2,X3,X5,X5)
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X5,X0,X1)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) )).

tff(u694,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | k9_tmap_1(X0,X1) = X2
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u693,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | u1_struct_0(X1) = sK4(X0,X1,X2)
      | k9_tmap_1(X0,X1) = X2
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u692,negated_conjecture,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | m1_subset_1(sK4(sK0,sK0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | k9_tmap_1(sK0,sK0) = X1
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ v1_funct_1(X1) ) )).

tff(u691,negated_conjecture,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | u1_struct_0(sK0) = sK4(sK0,sK0,X2)
      | k9_tmap_1(sK0,sK0) = X2
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ v1_funct_1(X2) ) )).

tff(u690,negated_conjecture,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | m1_subset_1(sK4(sK0,sK1,X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | k9_tmap_1(sK0,sK1) = X1
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ v1_funct_1(X1) ) )).

tff(u689,negated_conjecture,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | u1_struct_0(sK1) = sK4(sK0,sK1,X2)
      | k9_tmap_1(sK0,sK1) = X2
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ v1_funct_1(X2) ) )).

tff(u688,negated_conjecture,
    ( ~ ! [X3,X4] :
          ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X4)))))
          | ~ m1_pre_topc(X4,k8_tmap_1(sK0,sK1))
          | ~ v1_funct_1(X3)
          | ~ v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X4)))
          | k9_tmap_1(k8_tmap_1(sK0,sK1),X4) = X3
          | m1_subset_1(sK4(k8_tmap_1(sK0,sK1),X4,X3),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ! [X3,X4] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X4)))))
        | ~ m1_pre_topc(X4,k8_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X4)))
        | k9_tmap_1(k8_tmap_1(sK0,sK1),X4) = X3
        | m1_subset_1(sK4(k8_tmap_1(sK0,sK1),X4,X3),k1_zfmisc_1(u1_struct_0(sK0))) ) )).

tff(u687,negated_conjecture,
    ( ~ ! [X5,X6] :
          ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X6)))))
          | ~ m1_pre_topc(X6,k8_tmap_1(sK0,sK1))
          | ~ v1_funct_1(X5)
          | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X6)))
          | k9_tmap_1(k8_tmap_1(sK0,sK1),X6) = X5
          | u1_struct_0(X6) = sK4(k8_tmap_1(sK0,sK1),X6,X5) )
    | ! [X5,X6] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X6)))))
        | ~ m1_pre_topc(X6,k8_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X5)
        | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X6)))
        | k9_tmap_1(k8_tmap_1(sK0,sK1),X6) = X5
        | u1_struct_0(X6) = sK4(k8_tmap_1(sK0,sK1),X6,X5) ) )).

tff(u686,axiom,(
    ! [X3,X0,X2] :
      ( ~ m1_subset_1(X3,u1_struct_0(X2))
      | r1_tmap_1(X2,k6_tmap_1(X0,u1_struct_0(X2)),k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u685,negated_conjecture,
    ( ~ ! [X11,X12] :
          ( ~ m1_subset_1(X11,u1_struct_0(sK0))
          | v2_struct_0(X12)
          | ~ v2_pre_topc(X12)
          | ~ l1_pre_topc(X12)
          | ~ m1_pre_topc(k8_tmap_1(sK0,sK1),X12)
          | r1_tmap_1(k8_tmap_1(sK0,sK1),k6_tmap_1(X12,u1_struct_0(sK0)),k2_tmap_1(X12,k6_tmap_1(X12,u1_struct_0(sK0)),k7_tmap_1(X12,u1_struct_0(sK0)),k8_tmap_1(sK0,sK1)),X11) )
    | ! [X11,X12] :
        ( ~ m1_subset_1(X11,u1_struct_0(sK0))
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12)
        | ~ m1_pre_topc(k8_tmap_1(sK0,sK1),X12)
        | r1_tmap_1(k8_tmap_1(sK0,sK1),k6_tmap_1(X12,u1_struct_0(sK0)),k2_tmap_1(X12,k6_tmap_1(X12,u1_struct_0(sK0)),k7_tmap_1(X12,u1_struct_0(sK0)),k8_tmap_1(sK0,sK1)),X11) ) )).

tff(u684,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
      | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(k9_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u683,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | ! [X1,X0] :
        ( ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | r1_funct_2(X0,X1,u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1))
        | ~ v1_funct_2(k9_tmap_1(sK0,sK1),X0,X1)
        | v1_xboole_0(X1) ) )).

tff(u682,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | ! [X1,X0] :
        ( ~ m1_subset_1(k9_tmap_1(sK0,sK0),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | r1_funct_2(X0,X1,u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK0),k9_tmap_1(sK0,sK0))
        | ~ v1_funct_2(k9_tmap_1(sK0,sK0),X0,X1)
        | v1_xboole_0(X1) ) )).

tff(u681,negated_conjecture,
    ( ~ ! [X10] :
          ( ~ m1_subset_1(k9_tmap_1(k8_tmap_1(sK0,sK1),X10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X10)))))
          | ~ m1_pre_topc(X10,k8_tmap_1(sK0,sK1))
          | ~ v1_funct_1(k9_tmap_1(k8_tmap_1(sK0,sK1),X10))
          | ~ v1_funct_2(k9_tmap_1(k8_tmap_1(sK0,sK1),X10),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X10)))
          | r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X10)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(X10))),k9_tmap_1(k8_tmap_1(sK0,sK1),X10),k7_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(X10))) )
    | ! [X10] :
        ( ~ m1_subset_1(k9_tmap_1(k8_tmap_1(sK0,sK1),X10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X10)))))
        | ~ m1_pre_topc(X10,k8_tmap_1(sK0,sK1))
        | ~ v1_funct_1(k9_tmap_1(k8_tmap_1(sK0,sK1),X10))
        | ~ v1_funct_2(k9_tmap_1(k8_tmap_1(sK0,sK1),X10),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X10)))
        | r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X10)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(X10))),k9_tmap_1(k8_tmap_1(sK0,sK1),X10),k7_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(X10))) ) )).

tff(u680,negated_conjecture,
    ( ~ ~ m1_subset_1(k9_tmap_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1))))))
    | ~ m1_subset_1(k9_tmap_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1)))))) )).

tff(u679,negated_conjecture,
    ( ~ ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )).

tff(u678,negated_conjecture,(
    m1_subset_1(sK2,u1_struct_0(sK1)) )).

tff(u677,negated_conjecture,(
    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u676,negated_conjecture,(
    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u675,negated_conjecture,(
    m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )).

tff(u674,negated_conjecture,(
    m1_subset_1(k9_tmap_1(sK0,sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )).

tff(u673,axiom,(
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

tff(u672,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK4(X0,X1,X2))),X2,k7_tmap_1(X0,sK4(X0,X1,X2)))
      | k9_tmap_1(X0,X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u671,negated_conjecture,(
    ! [X0] :
      ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK4(sK0,sK1,X0))),X0,k7_tmap_1(sK0,sK4(sK0,sK1,X0)))
      | k9_tmap_1(sK0,sK1) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ v1_funct_1(X0) ) )).

tff(u670,negated_conjecture,(
    ! [X0] :
      ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK4(sK0,sK0,X0))),X0,k7_tmap_1(sK0,sK4(sK0,sK0,X0)))
      | k9_tmap_1(sK0,sK0) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ v1_funct_1(X0) ) )).

tff(u669,negated_conjecture,
    ( ~ ! [X7,X8] :
          ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X7)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(k8_tmap_1(sK0,sK1),sK4(k8_tmap_1(sK0,sK1),X7,X8))),X8,k7_tmap_1(k8_tmap_1(sK0,sK1),sK4(k8_tmap_1(sK0,sK1),X7,X8)))
          | ~ m1_pre_topc(X7,k8_tmap_1(sK0,sK1))
          | ~ v1_funct_1(X8)
          | ~ v1_funct_2(X8,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X7)))
          | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X7)))))
          | k9_tmap_1(k8_tmap_1(sK0,sK1),X7) = X8 )
    | ! [X7,X8] :
        ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X7)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(k8_tmap_1(sK0,sK1),sK4(k8_tmap_1(sK0,sK1),X7,X8))),X8,k7_tmap_1(k8_tmap_1(sK0,sK1),sK4(k8_tmap_1(sK0,sK1),X7,X8)))
        | ~ m1_pre_topc(X7,k8_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X7)))
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X7)))))
        | k9_tmap_1(k8_tmap_1(sK0,sK1),X7) = X8 ) )).

tff(u668,negated_conjecture,(
    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0))) )).

tff(u667,negated_conjecture,(
    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK0),k6_partfun1(u1_struct_0(sK0))) )).

tff(u666,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | k9_tmap_1(sK0,sK1) != k9_tmap_1(sK0,sK0)
    | r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK0),k9_tmap_1(sK0,sK0)) )).

tff(u665,negated_conjecture,
    ( ~ ~ v2_pre_topc(k8_tmap_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1)))
    | ~ v2_pre_topc(k8_tmap_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1))) )).

tff(u664,negated_conjecture,(
    v2_pre_topc(sK0) )).

tff(u663,negated_conjecture,(
    v2_pre_topc(k8_tmap_1(sK0,sK1)) )).

tff(u662,negated_conjecture,(
    v2_pre_topc(k8_tmap_1(sK0,sK0)) )).

tff(u661,axiom,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) )).

tff(u660,axiom,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X1,X0)
      | u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u659,axiom,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X1,X0)
      | v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u658,axiom,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u657,axiom,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u656,axiom,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X1,X0)
      | v1_funct_1(k9_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u655,axiom,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X1,X0)
      | v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u654,axiom,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u653,axiom,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X1,X0)
      | u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

% (5628)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
tff(u652,negated_conjecture,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X0,X1)
      | k8_tmap_1(sK0,sK1) = k8_tmap_1(X1,X0)
      | u1_struct_0(X0) = sK3(X1,X0,k8_tmap_1(sK0,sK1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) )).

tff(u651,negated_conjecture,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X1,X0)
      | k8_tmap_1(X0,X1) = k8_tmap_1(sK0,sK1)
      | m1_subset_1(sK3(X0,X1,k8_tmap_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u650,negated_conjecture,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X1,X0)
      | k8_tmap_1(X0,X1) = k8_tmap_1(sK0,sK1)
      | k8_tmap_1(sK0,sK1) != k6_tmap_1(X0,sK3(X0,X1,k8_tmap_1(sK0,sK1)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u649,negated_conjecture,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X1,X0)
      | k8_tmap_1(X0,X1) = k8_tmap_1(sK0,sK0)
      | k8_tmap_1(sK0,sK0) != k6_tmap_1(X0,sK3(X0,X1,k8_tmap_1(sK0,sK0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u648,negated_conjecture,(
    ! [X3,X2] :
      ( ~ m1_pre_topc(X3,X2)
      | k8_tmap_1(sK0,sK0) = k8_tmap_1(X2,X3)
      | m1_subset_1(sK3(X2,X3,k8_tmap_1(sK0,sK0)),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) )).

tff(u647,negated_conjecture,(
    ! [X5,X4] :
      ( ~ m1_pre_topc(X4,X5)
      | k8_tmap_1(sK0,sK0) = k8_tmap_1(X5,X4)
      | u1_struct_0(X4) = sK3(X5,X4,k8_tmap_1(sK0,sK0))
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5) ) )).

tff(u646,negated_conjecture,(
    ! [X0] :
      ( ~ m1_pre_topc(sK1,X0)
      | r1_tmap_1(sK1,k6_tmap_1(X0,u1_struct_0(sK1)),k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK1)),k7_tmap_1(X0,u1_struct_0(sK1)),sK1),sK2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u645,negated_conjecture,(
    m1_pre_topc(sK1,sK0) )).

tff(u644,negated_conjecture,(
    m1_pre_topc(sK0,sK0) )).

tff(u643,negated_conjecture,(
    m1_pre_topc(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1)) )).

tff(u642,negated_conjecture,(
    m1_pre_topc(k8_tmap_1(sK0,sK0),k8_tmap_1(sK0,sK0)) )).

tff(u641,axiom,(
    ! [X1,X0,X2] :
      ( ~ v1_pre_topc(X2)
      | k6_tmap_1(X0,sK3(X0,X1,X2)) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | k8_tmap_1(X0,X1) = X2
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u640,axiom,(
    ! [X1,X0,X2] :
      ( ~ v1_pre_topc(X2)
      | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | k8_tmap_1(X0,X1) = X2
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u639,axiom,(
    ! [X1,X0,X2] :
      ( ~ v1_pre_topc(X2)
      | u1_struct_0(X1) = sK3(X0,X1,X2)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | k8_tmap_1(X0,X1) = X2
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u638,axiom,(
    ! [X1,X0] :
      ( ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u637,negated_conjecture,
    ( ~ ~ v1_pre_topc(k8_tmap_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1)))
    | ~ v1_pre_topc(k8_tmap_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1))) )).

tff(u636,negated_conjecture,(
    v1_pre_topc(k8_tmap_1(sK0,sK1)) )).

tff(u635,negated_conjecture,(
    v1_pre_topc(k8_tmap_1(sK0,sK0)) )).

tff(u634,negated_conjecture,(
    ~ r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),sK2) )).

tff(u633,negated_conjecture,
    ( k9_tmap_1(sK0,sK1) != k9_tmap_1(sK0,sK0)
    | ~ r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK0),sK1),sK2) )).

tff(u632,negated_conjecture,(
    r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),sK2) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:01:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (5624)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.50  % (5620)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.50  % (5620)Refutation not found, incomplete strategy% (5620)------------------------------
% 0.20/0.50  % (5620)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (5620)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (5620)Memory used [KB]: 10618
% 0.20/0.50  % (5620)Time elapsed: 0.095 s
% 0.20/0.50  % (5620)------------------------------
% 0.20/0.50  % (5620)------------------------------
% 0.20/0.50  % (5639)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.50  % (5623)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.50  % (5645)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.50  % (5629)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.50  % (5622)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.51  % (5621)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (5642)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.51  % (5632)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.51  % (5631)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.51  % (5641)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.51  % (5643)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.51  % (5633)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (5627)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.52  % (5630)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.52  % (5640)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.52  % (5638)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.52  % (5621)Refutation not found, incomplete strategy% (5621)------------------------------
% 0.20/0.52  % (5621)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (5621)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (5621)Memory used [KB]: 10874
% 0.20/0.52  % (5621)Time elapsed: 0.104 s
% 0.20/0.52  % (5621)------------------------------
% 0.20/0.52  % (5621)------------------------------
% 0.20/0.52  % (5627)Refutation not found, incomplete strategy% (5627)------------------------------
% 0.20/0.52  % (5627)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (5627)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (5627)Memory used [KB]: 1791
% 0.20/0.52  % (5627)Time elapsed: 0.065 s
% 0.20/0.52  % (5627)------------------------------
% 0.20/0.52  % (5627)------------------------------
% 0.20/0.52  % (5634)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.52  % (5625)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.52  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.53  % (5633)Refutation not found, incomplete strategy% (5633)------------------------------
% 0.20/0.53  % (5633)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (5633)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (5633)Memory used [KB]: 6268
% 0.20/0.53  % (5633)Time elapsed: 0.123 s
% 0.20/0.53  % (5633)------------------------------
% 0.20/0.53  % (5633)------------------------------
% 0.20/0.53  % (5636)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.53  % (5626)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.53  % (5630)# SZS output start Saturation.
% 0.20/0.53  tff(u742,negated_conjecture,
% 0.20/0.53      ((~(u1_struct_0(sK1) != sK4(sK0,sK1,k9_tmap_1(sK0,sK0)))) | (u1_struct_0(sK1) != sK4(sK0,sK1,k9_tmap_1(sK0,sK0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u741,negated_conjecture,
% 0.20/0.53      ((~(u1_struct_0(sK0) != u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1))))) | (u1_struct_0(sK0) != u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1)))))).
% 0.20/0.53  
% 0.20/0.53  tff(u740,negated_conjecture,
% 0.20/0.53      ((~(u1_struct_0(sK0) != sK3(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1)))) | (u1_struct_0(sK0) != sK3(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1))))).
% 0.20/0.53  
% 0.20/0.53  tff(u739,negated_conjecture,
% 0.20/0.53      ((~(k8_tmap_1(sK0,sK1) != k8_tmap_1(sK0,sK0))) | (k8_tmap_1(sK0,sK1) != k8_tmap_1(sK0,sK0)))).
% 0.20/0.53  
% 0.20/0.53  tff(u738,negated_conjecture,
% 0.20/0.53      ((~(k8_tmap_1(sK0,sK1) != k8_tmap_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1)))) | (k8_tmap_1(sK0,sK1) != k8_tmap_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1))))).
% 0.20/0.53  
% 0.20/0.53  tff(u737,negated_conjecture,
% 0.20/0.53      ((~(k8_tmap_1(sK0,sK1) != k8_tmap_1(sK0,sK0))) | (k8_tmap_1(sK0,sK0) != k6_tmap_1(sK0,u1_struct_0(sK1))))).
% 0.20/0.53  
% 0.20/0.53  tff(u736,negated_conjecture,
% 0.20/0.53      ((~(k9_tmap_1(sK0,sK1) != k6_partfun1(u1_struct_0(sK0)))) | (k9_tmap_1(sK0,sK1) != k6_partfun1(u1_struct_0(sK0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u735,negated_conjecture,
% 0.20/0.53      ((~(k9_tmap_1(sK0,sK1) != k6_partfun1(u1_struct_0(sK0)))) | (~(k9_tmap_1(sK0,sK1) = k9_tmap_1(sK0,sK0))) | (k9_tmap_1(sK0,sK0) != k6_partfun1(u1_struct_0(sK0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u734,negated_conjecture,
% 0.20/0.53      ((~(u1_pre_topc(k8_tmap_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1))) != k5_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(sK0)))) | (u1_pre_topc(k8_tmap_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1))) != k5_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(sK0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u733,negated_conjecture,
% 0.20/0.53      (u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)))).
% 0.20/0.53  
% 0.20/0.53  tff(u732,negated_conjecture,
% 0.20/0.53      (u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK0)))).
% 0.20/0.53  
% 0.20/0.53  tff(u731,negated_conjecture,
% 0.20/0.53      ((~(u1_struct_0(sK0) = sK3(sK0,sK0,k8_tmap_1(sK0,sK1)))) | (u1_struct_0(sK0) = sK3(sK0,sK0,k8_tmap_1(sK0,sK1))))).
% 0.20/0.53  
% 0.20/0.53  tff(u730,negated_conjecture,
% 0.20/0.53      ((~(k8_tmap_1(sK0,sK1) != k8_tmap_1(sK0,sK0))) | (u1_struct_0(sK1) = sK3(sK0,sK1,k8_tmap_1(sK0,sK0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u729,negated_conjecture,
% 0.20/0.53      (k7_tmap_1(sK0,u1_struct_0(sK1)) = k6_partfun1(u1_struct_0(sK0)))).
% 0.20/0.53  
% 0.20/0.53  tff(u728,negated_conjecture,
% 0.20/0.53      (k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK0)))).
% 0.20/0.53  
% 0.20/0.53  % (5631)Refutation not found, incomplete strategy% (5631)------------------------------
% 0.20/0.53  % (5631)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (5631)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (5631)Memory used [KB]: 10618
% 0.20/0.53  % (5631)Time elapsed: 0.124 s
% 0.20/0.53  % (5631)------------------------------
% 0.20/0.53  % (5631)------------------------------
% 0.20/0.53  tff(u727,negated_conjecture,
% 0.20/0.53      ((~(![X9] : ((~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0))) | (k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK1),X9)))))) | (k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(sK1))))).
% 0.20/0.53  
% 0.20/0.53  tff(u726,negated_conjecture,
% 0.20/0.53      ((~(![X9] : ((~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0))) | (k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK1),X9)))))) | (k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(sK0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u725,negated_conjecture,
% 0.20/0.53      (k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)))).
% 0.20/0.53  
% 0.20/0.53  tff(u724,negated_conjecture,
% 0.20/0.53      (k8_tmap_1(sK0,sK0) = k6_tmap_1(sK0,u1_struct_0(sK0)))).
% 0.20/0.53  
% 0.20/0.53  tff(u723,negated_conjecture,
% 0.20/0.53      ((~(k9_tmap_1(sK0,sK1) = k9_tmap_1(sK0,sK0))) | (k9_tmap_1(sK0,sK1) = k9_tmap_1(sK0,sK0)))).
% 0.20/0.53  
% 0.20/0.53  tff(u722,negated_conjecture,
% 0.20/0.53      (u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1)))).
% 0.20/0.53  
% 0.20/0.53  tff(u721,negated_conjecture,
% 0.20/0.53      (u1_pre_topc(k8_tmap_1(sK0,sK0)) = k5_tmap_1(sK0,u1_struct_0(sK0)))).
% 0.20/0.53  
% 0.20/0.53  tff(u720,axiom,
% 0.20/0.53      (![X0] : ((~l1_pre_topc(X0) | m1_pre_topc(X0,X0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u719,axiom,
% 0.20/0.53      (![X0] : ((~l1_pre_topc(X0) | l1_struct_0(X0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u718,negated_conjecture,
% 0.20/0.53      ((~~l1_pre_topc(k8_tmap_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1)))) | ~l1_pre_topc(k8_tmap_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1))))).
% 0.20/0.53  
% 0.20/0.53  tff(u717,negated_conjecture,
% 0.20/0.53      l1_pre_topc(sK0)).
% 0.20/0.53  
% 0.20/0.53  tff(u716,negated_conjecture,
% 0.20/0.53      l1_pre_topc(k8_tmap_1(sK0,sK1))).
% 0.20/0.53  
% 0.20/0.53  tff(u715,negated_conjecture,
% 0.20/0.53      l1_pre_topc(k8_tmap_1(sK0,sK0))).
% 0.20/0.53  
% 0.20/0.53  tff(u714,negated_conjecture,
% 0.20/0.53      l1_struct_0(sK0)).
% 0.20/0.53  
% 0.20/0.53  tff(u713,negated_conjecture,
% 0.20/0.53      l1_struct_0(k8_tmap_1(sK0,sK1))).
% 0.20/0.53  
% 0.20/0.53  tff(u712,negated_conjecture,
% 0.20/0.53      l1_struct_0(k8_tmap_1(sK0,sK0))).
% 0.20/0.53  
% 0.20/0.53  tff(u711,negated_conjecture,
% 0.20/0.53      ~v2_struct_0(sK0)).
% 0.20/0.53  
% 0.20/0.53  tff(u710,negated_conjecture,
% 0.20/0.53      ~v2_struct_0(sK1)).
% 0.20/0.53  
% 0.20/0.53  tff(u709,negated_conjecture,
% 0.20/0.53      ((~v2_struct_0(k8_tmap_1(sK0,sK0))) | v2_struct_0(k8_tmap_1(sK0,sK0)))).
% 0.20/0.53  
% 0.20/0.53  tff(u708,negated_conjecture,
% 0.20/0.53      ((~v2_struct_0(k8_tmap_1(sK0,sK1))) | v2_struct_0(k8_tmap_1(sK0,sK1)))).
% 0.20/0.53  
% 0.20/0.53  tff(u707,axiom,
% 0.20/0.53      (![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u706,negated_conjecture,
% 0.20/0.53      ((~~v1_xboole_0(u1_struct_0(sK0))) | ~v1_xboole_0(u1_struct_0(sK0)))).
% 0.20/0.53  
% 0.20/0.53  tff(u705,negated_conjecture,
% 0.20/0.53      ((~~v1_funct_1(k6_partfun1(u1_struct_0(sK0)))) | ~v1_funct_1(k6_partfun1(u1_struct_0(sK0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u704,negated_conjecture,
% 0.20/0.53      ((~~v1_funct_1(k9_tmap_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1)))) | ~v1_funct_1(k9_tmap_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1))))).
% 0.20/0.53  
% 0.20/0.53  tff(u703,negated_conjecture,
% 0.20/0.53      v1_funct_1(k9_tmap_1(sK0,sK1))).
% 0.20/0.53  
% 0.20/0.53  tff(u702,negated_conjecture,
% 0.20/0.53      v1_funct_1(k9_tmap_1(sK0,sK0))).
% 0.20/0.53  
% 0.20/0.53  tff(u701,negated_conjecture,
% 0.20/0.53      ((~~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)))).
% 0.20/0.53  
% 0.20/0.53  tff(u700,negated_conjecture,
% 0.20/0.53      ((~~v1_funct_2(k9_tmap_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1))))) | ~v1_funct_2(k9_tmap_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1)))))).
% 0.20/0.53  
% 0.20/0.53  tff(u699,negated_conjecture,
% 0.20/0.53      v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))).
% 0.20/0.53  
% 0.20/0.53  tff(u698,negated_conjecture,
% 0.20/0.53      v1_funct_2(k9_tmap_1(sK0,sK0),u1_struct_0(sK0),u1_struct_0(sK0))).
% 0.20/0.53  
% 0.20/0.53  tff(u697,axiom,
% 0.20/0.53      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u696,negated_conjecture,
% 0.20/0.53      ((~(![X9] : ((~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0))) | (k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK1),X9)))))) | (![X9] : ((~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0))) | (k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK1),X9))))))).
% 0.20/0.53  
% 0.20/0.53  tff(u695,axiom,
% 0.20/0.53      (![X1, X3, X5, X0, X2] : ((~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | r1_funct_2(X0,X1,X2,X3,X5,X5) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X5,X0,X1) | v1_xboole_0(X3) | v1_xboole_0(X1))))).
% 0.20/0.53  
% 0.20/0.53  tff(u694,axiom,
% 0.20/0.53      (![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | (k9_tmap_1(X0,X1) = X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u693,axiom,
% 0.20/0.53      (![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | (u1_struct_0(X1) = sK4(X0,X1,X2)) | (k9_tmap_1(X0,X1) = X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u692,negated_conjecture,
% 0.20/0.53      (![X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | m1_subset_1(sK4(sK0,sK0,X1),k1_zfmisc_1(u1_struct_0(sK0))) | (k9_tmap_1(sK0,sK0) = X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(X1))))).
% 0.20/0.53  
% 0.20/0.53  tff(u691,negated_conjecture,
% 0.20/0.53      (![X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | (u1_struct_0(sK0) = sK4(sK0,sK0,X2)) | (k9_tmap_1(sK0,sK0) = X2) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(X2))))).
% 0.20/0.53  
% 0.20/0.53  tff(u690,negated_conjecture,
% 0.20/0.53      (![X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | m1_subset_1(sK4(sK0,sK1,X1),k1_zfmisc_1(u1_struct_0(sK0))) | (k9_tmap_1(sK0,sK1) = X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(X1))))).
% 0.20/0.53  
% 0.20/0.53  tff(u689,negated_conjecture,
% 0.20/0.53      (![X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | (u1_struct_0(sK1) = sK4(sK0,sK1,X2)) | (k9_tmap_1(sK0,sK1) = X2) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(X2))))).
% 0.20/0.53  
% 0.20/0.53  tff(u688,negated_conjecture,
% 0.20/0.53      ((~(![X3, X4] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X4))))) | ~m1_pre_topc(X4,k8_tmap_1(sK0,sK1)) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X4))) | (k9_tmap_1(k8_tmap_1(sK0,sK1),X4) = X3) | m1_subset_1(sK4(k8_tmap_1(sK0,sK1),X4,X3),k1_zfmisc_1(u1_struct_0(sK0))))))) | (![X3, X4] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X4))))) | ~m1_pre_topc(X4,k8_tmap_1(sK0,sK1)) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X4))) | (k9_tmap_1(k8_tmap_1(sK0,sK1),X4) = X3) | m1_subset_1(sK4(k8_tmap_1(sK0,sK1),X4,X3),k1_zfmisc_1(u1_struct_0(sK0)))))))).
% 0.20/0.53  
% 0.20/0.53  tff(u687,negated_conjecture,
% 0.20/0.53      ((~(![X5, X6] : ((~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X6))))) | ~m1_pre_topc(X6,k8_tmap_1(sK0,sK1)) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X6))) | (k9_tmap_1(k8_tmap_1(sK0,sK1),X6) = X5) | (u1_struct_0(X6) = sK4(k8_tmap_1(sK0,sK1),X6,X5)))))) | (![X5, X6] : ((~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X6))))) | ~m1_pre_topc(X6,k8_tmap_1(sK0,sK1)) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X6))) | (k9_tmap_1(k8_tmap_1(sK0,sK1),X6) = X5) | (u1_struct_0(X6) = sK4(k8_tmap_1(sK0,sK1),X6,X5))))))).
% 0.20/0.53  
% 0.20/0.53  tff(u686,axiom,
% 0.20/0.53      (![X3, X0, X2] : ((~m1_subset_1(X3,u1_struct_0(X2)) | r1_tmap_1(X2,k6_tmap_1(X0,u1_struct_0(X2)),k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u685,negated_conjecture,
% 0.20/0.53      ((~(![X11, X12] : ((~m1_subset_1(X11,u1_struct_0(sK0)) | v2_struct_0(X12) | ~v2_pre_topc(X12) | ~l1_pre_topc(X12) | ~m1_pre_topc(k8_tmap_1(sK0,sK1),X12) | r1_tmap_1(k8_tmap_1(sK0,sK1),k6_tmap_1(X12,u1_struct_0(sK0)),k2_tmap_1(X12,k6_tmap_1(X12,u1_struct_0(sK0)),k7_tmap_1(X12,u1_struct_0(sK0)),k8_tmap_1(sK0,sK1)),X11))))) | (![X11, X12] : ((~m1_subset_1(X11,u1_struct_0(sK0)) | v2_struct_0(X12) | ~v2_pre_topc(X12) | ~l1_pre_topc(X12) | ~m1_pre_topc(k8_tmap_1(sK0,sK1),X12) | r1_tmap_1(k8_tmap_1(sK0,sK1),k6_tmap_1(X12,u1_struct_0(sK0)),k2_tmap_1(X12,k6_tmap_1(X12,u1_struct_0(sK0)),k7_tmap_1(X12,u1_struct_0(sK0)),k8_tmap_1(sK0,sK1)),X11)))))).
% 0.20/0.53  
% 0.20/0.53  tff(u684,axiom,
% 0.20/0.53      (![X1, X0] : ((~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1))) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u683,negated_conjecture,
% 0.20/0.53      ((~~v1_xboole_0(u1_struct_0(sK0))) | (![X1, X0] : ((~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r1_funct_2(X0,X1,u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1)) | ~v1_funct_2(k9_tmap_1(sK0,sK1),X0,X1) | v1_xboole_0(X1)))))).
% 0.20/0.53  
% 0.20/0.53  tff(u682,negated_conjecture,
% 0.20/0.53      ((~~v1_xboole_0(u1_struct_0(sK0))) | (![X1, X0] : ((~m1_subset_1(k9_tmap_1(sK0,sK0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r1_funct_2(X0,X1,u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK0),k9_tmap_1(sK0,sK0)) | ~v1_funct_2(k9_tmap_1(sK0,sK0),X0,X1) | v1_xboole_0(X1)))))).
% 0.20/0.53  
% 0.20/0.53  tff(u681,negated_conjecture,
% 0.20/0.53      ((~(![X10] : ((~m1_subset_1(k9_tmap_1(k8_tmap_1(sK0,sK1),X10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X10))))) | ~m1_pre_topc(X10,k8_tmap_1(sK0,sK1)) | ~v1_funct_1(k9_tmap_1(k8_tmap_1(sK0,sK1),X10)) | ~v1_funct_2(k9_tmap_1(k8_tmap_1(sK0,sK1),X10),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X10))) | r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X10)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(X10))),k9_tmap_1(k8_tmap_1(sK0,sK1),X10),k7_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(X10))))))) | (![X10] : ((~m1_subset_1(k9_tmap_1(k8_tmap_1(sK0,sK1),X10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X10))))) | ~m1_pre_topc(X10,k8_tmap_1(sK0,sK1)) | ~v1_funct_1(k9_tmap_1(k8_tmap_1(sK0,sK1),X10)) | ~v1_funct_2(k9_tmap_1(k8_tmap_1(sK0,sK1),X10),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X10))) | r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X10)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(X10))),k9_tmap_1(k8_tmap_1(sK0,sK1),X10),k7_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(X10)))))))).
% 0.20/0.53  
% 0.20/0.53  tff(u680,negated_conjecture,
% 0.20/0.53      ((~~m1_subset_1(k9_tmap_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1))))))) | ~m1_subset_1(k9_tmap_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1)))))))).
% 0.20/0.53  
% 0.20/0.53  tff(u679,negated_conjecture,
% 0.20/0.53      ((~~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) | ~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))).
% 0.20/0.53  
% 0.20/0.53  tff(u678,negated_conjecture,
% 0.20/0.53      m1_subset_1(sK2,u1_struct_0(sK1))).
% 0.20/0.53  
% 0.20/0.53  tff(u677,negated_conjecture,
% 0.20/0.53      m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.53  
% 0.20/0.53  tff(u676,negated_conjecture,
% 0.20/0.53      m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.53  
% 0.20/0.53  tff(u675,negated_conjecture,
% 0.20/0.53      m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u674,negated_conjecture,
% 0.20/0.53      m1_subset_1(k9_tmap_1(sK0,sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u673,axiom,
% 0.20/0.53      (![X1, X3, X5, X0, X2, X4] : ((~r1_funct_2(X0,X1,X2,X3,X4,X5) | (X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))))).
% 0.20/0.53  
% 0.20/0.53  tff(u672,axiom,
% 0.20/0.53      (![X1, X0, X2] : ((~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK4(X0,X1,X2))),X2,k7_tmap_1(X0,sK4(X0,X1,X2))) | (k9_tmap_1(X0,X1) = X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u671,negated_conjecture,
% 0.20/0.53      (![X0] : ((~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK4(sK0,sK1,X0))),X0,k7_tmap_1(sK0,sK4(sK0,sK1,X0))) | (k9_tmap_1(sK0,sK1) = X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(X0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u670,negated_conjecture,
% 0.20/0.53      (![X0] : ((~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK4(sK0,sK0,X0))),X0,k7_tmap_1(sK0,sK4(sK0,sK0,X0))) | (k9_tmap_1(sK0,sK0) = X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(X0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u669,negated_conjecture,
% 0.20/0.53      ((~(![X7, X8] : ((~r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X7)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(k8_tmap_1(sK0,sK1),sK4(k8_tmap_1(sK0,sK1),X7,X8))),X8,k7_tmap_1(k8_tmap_1(sK0,sK1),sK4(k8_tmap_1(sK0,sK1),X7,X8))) | ~m1_pre_topc(X7,k8_tmap_1(sK0,sK1)) | ~v1_funct_1(X8) | ~v1_funct_2(X8,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X7))) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X7))))) | (k9_tmap_1(k8_tmap_1(sK0,sK1),X7) = X8))))) | (![X7, X8] : ((~r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X7)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(k8_tmap_1(sK0,sK1),sK4(k8_tmap_1(sK0,sK1),X7,X8))),X8,k7_tmap_1(k8_tmap_1(sK0,sK1),sK4(k8_tmap_1(sK0,sK1),X7,X8))) | ~m1_pre_topc(X7,k8_tmap_1(sK0,sK1)) | ~v1_funct_1(X8) | ~v1_funct_2(X8,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X7))) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X7))))) | (k9_tmap_1(k8_tmap_1(sK0,sK1),X7) = X8)))))).
% 0.20/0.53  
% 0.20/0.53  tff(u668,negated_conjecture,
% 0.20/0.53      r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)))).
% 0.20/0.53  
% 0.20/0.53  tff(u667,negated_conjecture,
% 0.20/0.53      r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK0),k6_partfun1(u1_struct_0(sK0)))).
% 0.20/0.53  
% 0.20/0.53  tff(u666,negated_conjecture,
% 0.20/0.53      ((~~v1_xboole_0(u1_struct_0(sK0))) | (~(k9_tmap_1(sK0,sK1) = k9_tmap_1(sK0,sK0))) | r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK0),k9_tmap_1(sK0,sK0)))).
% 0.20/0.53  
% 0.20/0.53  tff(u665,negated_conjecture,
% 0.20/0.53      ((~~v2_pre_topc(k8_tmap_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1)))) | ~v2_pre_topc(k8_tmap_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1))))).
% 0.20/0.53  
% 0.20/0.53  tff(u664,negated_conjecture,
% 0.20/0.53      v2_pre_topc(sK0)).
% 0.20/0.53  
% 0.20/0.53  tff(u663,negated_conjecture,
% 0.20/0.53      v2_pre_topc(k8_tmap_1(sK0,sK1))).
% 0.20/0.53  
% 0.20/0.53  tff(u662,negated_conjecture,
% 0.20/0.53      v2_pre_topc(k8_tmap_1(sK0,sK0))).
% 0.20/0.53  
% 0.20/0.53  tff(u661,axiom,
% 0.20/0.53      (![X1, X0] : ((~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u660,axiom,
% 0.20/0.53      (![X1, X0] : ((~m1_pre_topc(X1,X0) | (u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u659,axiom,
% 0.20/0.53      (![X1, X0] : ((~m1_pre_topc(X1,X0) | v1_pre_topc(k8_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u658,axiom,
% 0.20/0.53      (![X1, X0] : ((~m1_pre_topc(X1,X0) | v2_pre_topc(k8_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u657,axiom,
% 0.20/0.53      (![X1, X0] : ((~m1_pre_topc(X1,X0) | l1_pre_topc(k8_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u656,axiom,
% 0.20/0.53      (![X1, X0] : ((~m1_pre_topc(X1,X0) | v1_funct_1(k9_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u655,axiom,
% 0.20/0.53      (![X1, X0] : ((~m1_pre_topc(X1,X0) | v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u654,axiom,
% 0.20/0.53      (![X1, X0] : ((~m1_pre_topc(X1,X0) | m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u653,axiom,
% 0.20/0.53      (![X1, X0] : ((~m1_pre_topc(X1,X0) | (u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1))) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 0.20/0.53  
% 0.20/0.54  % (5628)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.54  tff(u652,negated_conjecture,
% 0.20/0.54      (![X1, X0] : ((~m1_pre_topc(X0,X1) | (k8_tmap_1(sK0,sK1) = k8_tmap_1(X1,X0)) | (u1_struct_0(X0) = sK3(X1,X0,k8_tmap_1(sK0,sK1))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))))).
% 0.20/0.54  
% 0.20/0.54  tff(u651,negated_conjecture,
% 0.20/0.54      (![X1, X0] : ((~m1_pre_topc(X1,X0) | (k8_tmap_1(X0,X1) = k8_tmap_1(sK0,sK1)) | m1_subset_1(sK3(X0,X1,k8_tmap_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 0.20/0.54  
% 0.20/0.54  tff(u650,negated_conjecture,
% 0.20/0.54      (![X1, X0] : ((~m1_pre_topc(X1,X0) | (k8_tmap_1(X0,X1) = k8_tmap_1(sK0,sK1)) | (k8_tmap_1(sK0,sK1) != k6_tmap_1(X0,sK3(X0,X1,k8_tmap_1(sK0,sK1)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 0.20/0.54  
% 0.20/0.54  tff(u649,negated_conjecture,
% 0.20/0.54      (![X1, X0] : ((~m1_pre_topc(X1,X0) | (k8_tmap_1(X0,X1) = k8_tmap_1(sK0,sK0)) | (k8_tmap_1(sK0,sK0) != k6_tmap_1(X0,sK3(X0,X1,k8_tmap_1(sK0,sK0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 0.20/0.54  
% 0.20/0.54  tff(u648,negated_conjecture,
% 0.20/0.54      (![X3, X2] : ((~m1_pre_topc(X3,X2) | (k8_tmap_1(sK0,sK0) = k8_tmap_1(X2,X3)) | m1_subset_1(sK3(X2,X3,k8_tmap_1(sK0,sK0)),k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2))))).
% 0.20/0.54  
% 0.20/0.54  tff(u647,negated_conjecture,
% 0.20/0.54      (![X5, X4] : ((~m1_pre_topc(X4,X5) | (k8_tmap_1(sK0,sK0) = k8_tmap_1(X5,X4)) | (u1_struct_0(X4) = sK3(X5,X4,k8_tmap_1(sK0,sK0))) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5))))).
% 0.20/0.54  
% 0.20/0.54  tff(u646,negated_conjecture,
% 0.20/0.54      (![X0] : ((~m1_pre_topc(sK1,X0) | r1_tmap_1(sK1,k6_tmap_1(X0,u1_struct_0(sK1)),k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK1)),k7_tmap_1(X0,u1_struct_0(sK1)),sK1),sK2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 0.20/0.54  
% 0.20/0.54  tff(u645,negated_conjecture,
% 0.20/0.54      m1_pre_topc(sK1,sK0)).
% 0.20/0.54  
% 0.20/0.54  tff(u644,negated_conjecture,
% 0.20/0.54      m1_pre_topc(sK0,sK0)).
% 0.20/0.54  
% 0.20/0.54  tff(u643,negated_conjecture,
% 0.20/0.54      m1_pre_topc(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1))).
% 0.20/0.54  
% 0.20/0.54  tff(u642,negated_conjecture,
% 0.20/0.54      m1_pre_topc(k8_tmap_1(sK0,sK0),k8_tmap_1(sK0,sK0))).
% 0.20/0.54  
% 0.20/0.54  tff(u641,axiom,
% 0.20/0.54      (![X1, X0, X2] : ((~v1_pre_topc(X2) | (k6_tmap_1(X0,sK3(X0,X1,X2)) != X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | (k8_tmap_1(X0,X1) = X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 0.20/0.54  
% 0.20/0.54  tff(u640,axiom,
% 0.20/0.54      (![X1, X0, X2] : ((~v1_pre_topc(X2) | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | (k8_tmap_1(X0,X1) = X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 0.20/0.54  
% 0.20/0.54  tff(u639,axiom,
% 0.20/0.54      (![X1, X0, X2] : ((~v1_pre_topc(X2) | (u1_struct_0(X1) = sK3(X0,X1,X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | (k8_tmap_1(X0,X1) = X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 0.20/0.54  
% 0.20/0.54  tff(u638,axiom,
% 0.20/0.54      (![X1, X0] : ((~v1_pre_topc(k8_tmap_1(X0,X1)) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 0.20/0.54  
% 0.20/0.54  tff(u637,negated_conjecture,
% 0.20/0.54      ((~~v1_pre_topc(k8_tmap_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1)))) | ~v1_pre_topc(k8_tmap_1(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1))))).
% 0.20/0.54  
% 0.20/0.54  tff(u636,negated_conjecture,
% 0.20/0.54      v1_pre_topc(k8_tmap_1(sK0,sK1))).
% 0.20/0.54  
% 0.20/0.54  tff(u635,negated_conjecture,
% 0.20/0.54      v1_pre_topc(k8_tmap_1(sK0,sK0))).
% 0.20/0.54  
% 0.20/0.54  tff(u634,negated_conjecture,
% 0.20/0.54      ~r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),sK2)).
% 0.20/0.54  
% 0.20/0.54  tff(u633,negated_conjecture,
% 0.20/0.54      ((~(k9_tmap_1(sK0,sK1) = k9_tmap_1(sK0,sK0))) | ~r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK0),sK1),sK2))).
% 0.20/0.54  
% 0.20/0.54  tff(u632,negated_conjecture,
% 0.20/0.54      r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),sK2)).
% 0.20/0.54  
% 0.20/0.54  % (5630)# SZS output end Saturation.
% 0.20/0.54  % (5630)------------------------------
% 0.20/0.54  % (5630)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (5630)Termination reason: Satisfiable
% 0.20/0.54  
% 0.20/0.54  % (5630)Memory used [KB]: 11001
% 0.20/0.54  % (5630)Time elapsed: 0.123 s
% 0.20/0.54  % (5630)------------------------------
% 0.20/0.54  % (5630)------------------------------
% 0.20/0.54  % (5618)Success in time 0.185 s
%------------------------------------------------------------------------------
