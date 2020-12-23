%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:36 EST 2020

% Result     : CounterSatisfiable 1.48s
% Output     : Saturation 1.48s
% Verified   : 
% Statistics : Number of formulae       :   76 (  76 expanded)
%              Number of leaves         :   76 (  76 expanded)
%              Depth                    :    0
%              Number of atoms          :  271 ( 271 expanded)
%              Number of equality atoms :   17 (  17 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u429,negated_conjecture,
    ( ~ ( k9_tmap_1(sK0,sK1) != k3_struct_0(sK0) )
    | k9_tmap_1(sK0,sK1) != k3_struct_0(sK0) )).

tff(u428,negated_conjecture,(
    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) )).

tff(u427,negated_conjecture,(
    k7_tmap_1(sK0,u1_struct_0(sK1)) = k6_partfun1(u1_struct_0(sK0)) )).

tff(u426,negated_conjecture,(
    v2_pre_topc(sK0) )).

tff(u425,negated_conjecture,(
    v2_pre_topc(sK1) )).

tff(u424,negated_conjecture,(
    v2_pre_topc(k8_tmap_1(sK0,sK1)) )).

tff(u423,axiom,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) )).

tff(u422,negated_conjecture,(
    l1_pre_topc(sK0) )).

tff(u421,negated_conjecture,(
    l1_pre_topc(sK1) )).

tff(u420,negated_conjecture,(
    l1_pre_topc(k8_tmap_1(sK0,sK1)) )).

tff(u419,axiom,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) )).

tff(u418,axiom,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) )).

tff(u417,axiom,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X1,X0)
      | r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0))
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u416,axiom,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) )).

tff(u415,axiom,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X1,X0)
      | v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u414,axiom,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u413,axiom,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u412,axiom,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X1,X0)
      | v1_funct_1(k9_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u411,axiom,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X1,X0)
      | v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u410,axiom,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u409,axiom,(
    ! [X0,X2] :
      ( ~ m1_pre_topc(X2,X0)
      | m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X2))))))
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u408,axiom,(
    ! [X0,X2] :
      ( ~ m1_pre_topc(X2,X0)
      | v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),X2,k6_tmap_1(X0,u1_struct_0(X2)))
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u407,axiom,(
    ! [X0,X2] :
      ( ~ m1_pre_topc(X2,X0)
      | v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X2))))
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u406,axiom,(
    ! [X0,X2] :
      ( ~ m1_pre_topc(X2,X0)
      | v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2))
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u405,negated_conjecture,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X1,X0)
      | k8_tmap_1(X0,X1) = k8_tmap_1(sK0,sK1)
      | k8_tmap_1(sK0,sK1) != k6_tmap_1(X0,sK3(X0,X1,k8_tmap_1(sK0,sK1)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u404,negated_conjecture,(
    ! [X3,X2] :
      ( ~ m1_pre_topc(X3,X2)
      | k8_tmap_1(sK0,sK1) = k8_tmap_1(X2,X3)
      | m1_subset_1(sK3(X2,X3,k8_tmap_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) )).

tff(u403,negated_conjecture,(
    ! [X5,X4] :
      ( ~ m1_pre_topc(X4,X5)
      | k8_tmap_1(sK0,sK1) = k8_tmap_1(X5,X4)
      | u1_struct_0(X4) = sK3(X5,X4,k8_tmap_1(sK0,sK1))
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5) ) )).

tff(u402,negated_conjecture,(
    m1_pre_topc(sK1,sK0) )).

tff(u401,negated_conjecture,(
    l1_struct_0(sK0) )).

tff(u400,negated_conjecture,(
    l1_struct_0(sK1) )).

tff(u399,negated_conjecture,(
    l1_struct_0(k8_tmap_1(sK0,sK1)) )).

tff(u398,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u397,negated_conjecture,(
    ~ v2_struct_0(sK1) )).

tff(u396,axiom,(
    ! [X1,X0] :
      ( ~ v2_struct_0(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u395,negated_conjecture,
    ( ~ ~ v2_struct_0(k8_tmap_1(sK0,sK1))
    | ~ v2_struct_0(k8_tmap_1(sK0,sK1)) )).

tff(u394,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) )).

tff(u393,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_xboole_0(u1_struct_0(sK0)) )).

tff(u392,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1))) )).

tff(u391,negated_conjecture,
    ( ~ ~ v1_funct_1(k3_struct_0(sK0))
    | ~ v1_funct_1(k3_struct_0(sK0)) )).

tff(u390,negated_conjecture,(
    v1_funct_1(k9_tmap_1(sK0,sK1)) )).

tff(u389,negated_conjecture,(
    v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1)) )).

tff(u388,negated_conjecture,(
    v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1)) )).

tff(u387,negated_conjecture,
    ( ~ ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0)) )).

tff(u386,negated_conjecture,(
    v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) )).

tff(u385,negated_conjecture,(
    v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK0,sK1))) )).

tff(u384,negated_conjecture,(
    v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK0,sK1))) )).

tff(u383,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u382,axiom,(
    ! [X1,X3,X5,X0,X2] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | r1_funct_2(X0,X1,X2,X3,X5,X5)
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X5,X0,X1)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) )).

tff(u381,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u380,negated_conjecture,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | r1_tmap_1(sK1,X0,X1,sK2)
      | ~ v5_pre_topc(X1,sK1,X0)
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u379,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_tmap_1(X0,X1,X2,X4)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u378,negated_conjecture,
    ( ~ ! [X1,X0] :
          ( ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | v1_xboole_0(X1)
          | ~ v1_funct_2(k9_tmap_1(sK0,sK1),X0,X1)
          | r1_funct_2(X0,X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k9_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1)) )
    | ! [X1,X0] :
        ( ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X1)
        | ~ v1_funct_2(k9_tmap_1(sK0,sK1),X0,X1)
        | r1_funct_2(X0,X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k9_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1)) ) )).

tff(u377,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ! [X1,X0] :
        ( ~ m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),X0,X1)
        | r1_funct_2(X0,X1,u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK0,sK1)),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1))
        | v1_xboole_0(X1) ) )).

tff(u376,negated_conjecture,
    ( ~ ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )).

tff(u375,negated_conjecture,
    ( ~ ~ m1_subset_1(sK4(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1)),u1_struct_0(sK0)) )).

tff(u374,negated_conjecture,
    ( ~ ~ m1_subset_1(sK4(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1)),u1_struct_0(sK1)) )).

tff(u373,negated_conjecture,(
    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u372,negated_conjecture,(
    m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) )).

tff(u371,negated_conjecture,(
    m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK0,sK1))))) )).

tff(u370,negated_conjecture,(
    m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK0,sK1))))) )).

tff(u369,negated_conjecture,(
    m1_subset_1(sK2,u1_struct_0(sK1)) )).

tff(u368,axiom,(
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

tff(u367,negated_conjecture,(
    r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k3_struct_0(sK0)) )).

tff(u366,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ ! [X1,X0] :
          ( ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | v1_xboole_0(X1)
          | ~ v1_funct_2(k9_tmap_1(sK0,sK1),X0,X1)
          | r1_funct_2(X0,X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k9_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1)) )
    | r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k9_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1)) )).

tff(u365,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1)))
    | r1_funct_2(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK0,sK1)),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1)) )).

tff(u364,axiom,(
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

tff(u363,axiom,(
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

tff(u362,axiom,(
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

tff(u361,axiom,(
    ! [X1,X0] :
      ( ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u360,negated_conjecture,(
    v1_pre_topc(k8_tmap_1(sK0,sK1)) )).

tff(u359,negated_conjecture,(
    v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),sK1,k6_tmap_1(sK0,u1_struct_0(sK1))) )).

tff(u358,negated_conjecture,(
    v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),sK1,k8_tmap_1(sK0,sK1)) )).

tff(u357,negated_conjecture,
    ( ~ v5_pre_topc(k9_tmap_1(sK0,sK1),sK0,k8_tmap_1(sK0,sK1))
    | v5_pre_topc(k9_tmap_1(sK0,sK1),sK0,k8_tmap_1(sK0,sK1)) )).

tff(u356,negated_conjecture,(
    ~ r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),sK2) )).

tff(u355,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_tmap_1(X0,X1,X2,sK4(X0,X1,X2))
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u354,negated_conjecture,
    ( ~ r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),sK2)
    | r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),sK2) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:36:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (8449)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.46  % (8457)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.48  % (8449)Refutation not found, incomplete strategy% (8449)------------------------------
% 0.20/0.48  % (8449)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (8449)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (8449)Memory used [KB]: 1791
% 0.20/0.48  % (8449)Time elapsed: 0.066 s
% 0.20/0.48  % (8449)------------------------------
% 0.20/0.48  % (8449)------------------------------
% 0.20/0.50  % (8459)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.50  % (8444)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.51  % (8451)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.51  % (8456)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (8453)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.51  % (8462)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.51  % (8443)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (8461)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.52  % (8443)Refutation not found, incomplete strategy% (8443)------------------------------
% 0.20/0.52  % (8443)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (8443)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (8443)Memory used [KB]: 10618
% 0.20/0.52  % (8443)Time elapsed: 0.112 s
% 0.20/0.52  % (8443)------------------------------
% 0.20/0.52  % (8443)------------------------------
% 0.20/0.52  % (8448)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.52  % (8448)Refutation not found, incomplete strategy% (8448)------------------------------
% 0.20/0.52  % (8448)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (8448)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (8448)Memory used [KB]: 10618
% 0.20/0.52  % (8448)Time elapsed: 0.115 s
% 0.20/0.52  % (8448)------------------------------
% 0.20/0.52  % (8448)------------------------------
% 0.20/0.52  % (8446)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.52  % (8464)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.26/0.53  % (8442)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.26/0.53  % (8455)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.26/0.53  % (8464)Refutation not found, incomplete strategy% (8464)------------------------------
% 1.26/0.53  % (8464)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.53  % (8464)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.53  
% 1.26/0.53  % (8464)Memory used [KB]: 11001
% 1.26/0.53  % (8464)Time elapsed: 0.115 s
% 1.26/0.53  % (8464)------------------------------
% 1.26/0.53  % (8464)------------------------------
% 1.26/0.53  % (8465)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.26/0.53  % (8445)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.26/0.53  % (8450)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.26/0.53  % (8460)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.26/0.53  % (8447)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.26/0.53  % (8467)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.26/0.53  % (8445)Refutation not found, incomplete strategy% (8445)------------------------------
% 1.26/0.53  % (8445)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.53  % (8445)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.53  
% 1.26/0.53  % (8445)Memory used [KB]: 6396
% 1.26/0.53  % (8445)Time elapsed: 0.125 s
% 1.26/0.53  % (8445)------------------------------
% 1.26/0.53  % (8445)------------------------------
% 1.26/0.54  % (8447)Refutation not found, incomplete strategy% (8447)------------------------------
% 1.26/0.54  % (8447)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.54  % (8447)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.54  
% 1.26/0.54  % (8447)Memory used [KB]: 6140
% 1.26/0.54  % (8447)Time elapsed: 0.102 s
% 1.26/0.54  % (8447)------------------------------
% 1.26/0.54  % (8447)------------------------------
% 1.26/0.54  % (8454)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.26/0.54  % (8463)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.26/0.54  % (8452)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.26/0.54  % (8458)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.48/0.54  % SZS status CounterSatisfiable for theBenchmark
% 1.48/0.54  % (8452)# SZS output start Saturation.
% 1.48/0.54  tff(u429,negated_conjecture,
% 1.48/0.54      ((~(k9_tmap_1(sK0,sK1) != k3_struct_0(sK0))) | (k9_tmap_1(sK0,sK1) != k3_struct_0(sK0)))).
% 1.48/0.54  
% 1.48/0.54  tff(u428,negated_conjecture,
% 1.48/0.54      (k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)))).
% 1.48/0.54  
% 1.48/0.54  tff(u427,negated_conjecture,
% 1.48/0.54      (k7_tmap_1(sK0,u1_struct_0(sK1)) = k6_partfun1(u1_struct_0(sK0)))).
% 1.48/0.54  
% 1.48/0.54  tff(u426,negated_conjecture,
% 1.48/0.54      v2_pre_topc(sK0)).
% 1.48/0.54  
% 1.48/0.54  tff(u425,negated_conjecture,
% 1.48/0.54      v2_pre_topc(sK1)).
% 1.48/0.54  
% 1.48/0.54  tff(u424,negated_conjecture,
% 1.48/0.54      v2_pre_topc(k8_tmap_1(sK0,sK1))).
% 1.48/0.54  
% 1.48/0.54  tff(u423,axiom,
% 1.48/0.54      (![X0] : ((~l1_pre_topc(X0) | l1_struct_0(X0))))).
% 1.48/0.54  
% 1.48/0.54  tff(u422,negated_conjecture,
% 1.48/0.54      l1_pre_topc(sK0)).
% 1.48/0.54  
% 1.48/0.54  tff(u421,negated_conjecture,
% 1.48/0.54      l1_pre_topc(sK1)).
% 1.48/0.54  
% 1.48/0.54  tff(u420,negated_conjecture,
% 1.48/0.54      l1_pre_topc(k8_tmap_1(sK0,sK1))).
% 1.48/0.54  
% 1.48/0.54  tff(u419,axiom,
% 1.48/0.54      (![X1, X0] : ((~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0))))).
% 1.48/0.54  
% 1.48/0.54  tff(u418,axiom,
% 1.48/0.54      (![X1, X0] : ((~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))))).
% 1.48/0.54  
% 1.48/0.54  tff(u417,axiom,
% 1.48/0.54      (![X1, X0] : ((~m1_pre_topc(X1,X0) | r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0)) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 1.48/0.54  
% 1.48/0.54  tff(u416,axiom,
% 1.48/0.54      (![X1, X0] : ((~m1_pre_topc(X1,X0) | v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))))).
% 1.48/0.54  
% 1.48/0.54  tff(u415,axiom,
% 1.48/0.54      (![X1, X0] : ((~m1_pre_topc(X1,X0) | v1_pre_topc(k8_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 1.48/0.54  
% 1.48/0.54  tff(u414,axiom,
% 1.48/0.54      (![X1, X0] : ((~m1_pre_topc(X1,X0) | v2_pre_topc(k8_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 1.48/0.54  
% 1.48/0.54  tff(u413,axiom,
% 1.48/0.54      (![X1, X0] : ((~m1_pre_topc(X1,X0) | l1_pre_topc(k8_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 1.48/0.54  
% 1.48/0.54  tff(u412,axiom,
% 1.48/0.54      (![X1, X0] : ((~m1_pre_topc(X1,X0) | v1_funct_1(k9_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 1.48/0.54  
% 1.48/0.54  tff(u411,axiom,
% 1.48/0.54      (![X1, X0] : ((~m1_pre_topc(X1,X0) | v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 1.48/0.54  
% 1.48/0.54  tff(u410,axiom,
% 1.48/0.54      (![X1, X0] : ((~m1_pre_topc(X1,X0) | m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 1.48/0.54  
% 1.48/0.54  tff(u409,axiom,
% 1.48/0.54      (![X0, X2] : ((~m1_pre_topc(X2,X0) | m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X2)))))) | v2_struct_0(X2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 1.48/0.54  
% 1.48/0.54  tff(u408,axiom,
% 1.48/0.54      (![X0, X2] : ((~m1_pre_topc(X2,X0) | v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),X2,k6_tmap_1(X0,u1_struct_0(X2))) | v2_struct_0(X2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 1.48/0.54  
% 1.48/0.54  tff(u407,axiom,
% 1.48/0.54      (![X0, X2] : ((~m1_pre_topc(X2,X0) | v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X2)))) | v2_struct_0(X2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 1.48/0.54  
% 1.48/0.54  tff(u406,axiom,
% 1.48/0.54      (![X0, X2] : ((~m1_pre_topc(X2,X0) | v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2)) | v2_struct_0(X2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 1.48/0.54  
% 1.48/0.54  tff(u405,negated_conjecture,
% 1.48/0.54      (![X1, X0] : ((~m1_pre_topc(X1,X0) | (k8_tmap_1(X0,X1) = k8_tmap_1(sK0,sK1)) | (k8_tmap_1(sK0,sK1) != k6_tmap_1(X0,sK3(X0,X1,k8_tmap_1(sK0,sK1)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 1.48/0.54  
% 1.48/0.54  tff(u404,negated_conjecture,
% 1.48/0.54      (![X3, X2] : ((~m1_pre_topc(X3,X2) | (k8_tmap_1(sK0,sK1) = k8_tmap_1(X2,X3)) | m1_subset_1(sK3(X2,X3,k8_tmap_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2))))).
% 1.48/0.54  
% 1.48/0.54  tff(u403,negated_conjecture,
% 1.48/0.54      (![X5, X4] : ((~m1_pre_topc(X4,X5) | (k8_tmap_1(sK0,sK1) = k8_tmap_1(X5,X4)) | (u1_struct_0(X4) = sK3(X5,X4,k8_tmap_1(sK0,sK1))) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5))))).
% 1.48/0.54  
% 1.48/0.54  tff(u402,negated_conjecture,
% 1.48/0.54      m1_pre_topc(sK1,sK0)).
% 1.48/0.54  
% 1.48/0.54  tff(u401,negated_conjecture,
% 1.48/0.54      l1_struct_0(sK0)).
% 1.48/0.54  
% 1.48/0.54  tff(u400,negated_conjecture,
% 1.48/0.54      l1_struct_0(sK1)).
% 1.48/0.54  
% 1.48/0.54  tff(u399,negated_conjecture,
% 1.48/0.54      l1_struct_0(k8_tmap_1(sK0,sK1))).
% 1.48/0.54  
% 1.48/0.54  tff(u398,negated_conjecture,
% 1.48/0.54      ~v2_struct_0(sK0)).
% 1.48/0.54  
% 1.48/0.54  tff(u397,negated_conjecture,
% 1.48/0.54      ~v2_struct_0(sK1)).
% 1.48/0.54  
% 1.48/0.54  tff(u396,axiom,
% 1.48/0.54      (![X1, X0] : ((~v2_struct_0(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 1.48/0.54  
% 1.48/0.54  tff(u395,negated_conjecture,
% 1.48/0.54      ((~~v2_struct_0(k8_tmap_1(sK0,sK1))) | ~v2_struct_0(k8_tmap_1(sK0,sK1)))).
% 1.48/0.54  
% 1.48/0.54  tff(u394,axiom,
% 1.48/0.54      (![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))))).
% 1.48/0.54  
% 1.48/0.54  tff(u393,negated_conjecture,
% 1.48/0.54      ((~~v1_xboole_0(u1_struct_0(sK0))) | ~v1_xboole_0(u1_struct_0(sK0)))).
% 1.48/0.54  
% 1.48/0.54  tff(u392,negated_conjecture,
% 1.48/0.54      ((~~v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1)))) | ~v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1))))).
% 1.48/0.54  
% 1.48/0.54  tff(u391,negated_conjecture,
% 1.48/0.54      ((~~v1_funct_1(k3_struct_0(sK0))) | ~v1_funct_1(k3_struct_0(sK0)))).
% 1.48/0.54  
% 1.48/0.54  tff(u390,negated_conjecture,
% 1.48/0.54      v1_funct_1(k9_tmap_1(sK0,sK1))).
% 1.48/0.54  
% 1.48/0.54  tff(u389,negated_conjecture,
% 1.48/0.54      v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1))).
% 1.48/0.54  
% 1.48/0.54  tff(u388,negated_conjecture,
% 1.48/0.54      v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1))).
% 1.48/0.54  
% 1.48/0.54  tff(u387,negated_conjecture,
% 1.48/0.54      ((~~v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))) | ~v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0)))).
% 1.48/0.54  
% 1.48/0.54  tff(u386,negated_conjecture,
% 1.48/0.54      v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))).
% 1.48/0.54  
% 1.48/0.54  tff(u385,negated_conjecture,
% 1.48/0.54      v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK0,sK1)))).
% 1.48/0.54  
% 1.48/0.54  tff(u384,negated_conjecture,
% 1.48/0.54      v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK0,sK1)))).
% 1.48/0.54  
% 1.48/0.54  tff(u383,axiom,
% 1.48/0.54      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 1.48/0.54  
% 1.48/0.54  tff(u382,axiom,
% 1.48/0.54      (![X1, X3, X5, X0, X2] : ((~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | r1_funct_2(X0,X1,X2,X3,X5,X5) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X5,X0,X1) | v1_xboole_0(X3) | v1_xboole_0(X1))))).
% 1.48/0.54  
% 1.48/0.54  tff(u381,axiom,
% 1.48/0.54      (![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) | v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 1.48/0.54  
% 1.48/0.54  tff(u380,negated_conjecture,
% 1.48/0.54      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | r1_tmap_1(sK1,X0,X1,sK2) | ~v5_pre_topc(X1,sK1,X0) | ~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 1.48/0.54  
% 1.48/0.54  tff(u379,axiom,
% 1.48/0.54      (![X1, X0, X2, X4] : ((~m1_subset_1(X4,u1_struct_0(X0)) | r1_tmap_1(X0,X1,X2,X4) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 1.48/0.54  
% 1.48/0.54  tff(u378,negated_conjecture,
% 1.48/0.54      ((~(![X1, X0] : ((~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_2(k9_tmap_1(sK0,sK1),X0,X1) | r1_funct_2(X0,X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k9_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1)))))) | (![X1, X0] : ((~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_2(k9_tmap_1(sK0,sK1),X0,X1) | r1_funct_2(X0,X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k9_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1))))))).
% 1.48/0.54  
% 1.48/0.54  tff(u377,negated_conjecture,
% 1.48/0.54      ((~~v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1)))) | (![X1, X0] : ((~m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),X0,X1) | r1_funct_2(X0,X1,u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK0,sK1)),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1)) | v1_xboole_0(X1)))))).
% 1.48/0.54  
% 1.48/0.54  tff(u376,negated_conjecture,
% 1.48/0.54      ((~~m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) | ~m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))).
% 1.48/0.54  
% 1.48/0.54  tff(u375,negated_conjecture,
% 1.48/0.54      ((~~m1_subset_1(sK4(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1)),u1_struct_0(sK0))) | ~m1_subset_1(sK4(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1)),u1_struct_0(sK0)))).
% 1.48/0.54  
% 1.48/0.54  tff(u374,negated_conjecture,
% 1.48/0.54      ((~~m1_subset_1(sK4(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1)),u1_struct_0(sK1))) | ~m1_subset_1(sK4(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1)),u1_struct_0(sK1)))).
% 1.48/0.54  
% 1.48/0.54  tff(u373,negated_conjecture,
% 1.48/0.54      m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.48/0.54  
% 1.48/0.54  tff(u372,negated_conjecture,
% 1.48/0.54      m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))).
% 1.48/0.54  
% 1.48/0.54  tff(u371,negated_conjecture,
% 1.48/0.54      m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK0,sK1)))))).
% 1.48/0.54  
% 1.48/0.54  tff(u370,negated_conjecture,
% 1.48/0.54      m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK0,sK1)))))).
% 1.48/0.54  
% 1.48/0.54  tff(u369,negated_conjecture,
% 1.48/0.54      m1_subset_1(sK2,u1_struct_0(sK1))).
% 1.48/0.54  
% 1.48/0.54  tff(u368,axiom,
% 1.48/0.54      (![X1, X3, X5, X0, X2, X4] : ((~r1_funct_2(X0,X1,X2,X3,X4,X5) | (X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))))).
% 1.48/0.54  
% 1.48/0.54  tff(u367,negated_conjecture,
% 1.48/0.54      r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k3_struct_0(sK0))).
% 1.48/0.54  
% 1.48/0.54  tff(u366,negated_conjecture,
% 1.48/0.54      ((~~v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1)))) | (~(![X1, X0] : ((~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_2(k9_tmap_1(sK0,sK1),X0,X1) | r1_funct_2(X0,X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k9_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1)))))) | r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k9_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1)))).
% 1.48/0.54  
% 1.48/0.54  tff(u365,negated_conjecture,
% 1.48/0.54      ((~~v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1)))) | r1_funct_2(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK0,sK1)),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1)))).
% 1.48/0.54  
% 1.48/0.54  tff(u364,axiom,
% 1.48/0.54      (![X1, X0, X2] : ((~v1_pre_topc(X2) | (k6_tmap_1(X0,sK3(X0,X1,X2)) != X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | (k8_tmap_1(X0,X1) = X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 1.48/0.54  
% 1.48/0.54  tff(u363,axiom,
% 1.48/0.54      (![X1, X0, X2] : ((~v1_pre_topc(X2) | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | (k8_tmap_1(X0,X1) = X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 1.48/0.54  
% 1.48/0.54  tff(u362,axiom,
% 1.48/0.54      (![X1, X0, X2] : ((~v1_pre_topc(X2) | (u1_struct_0(X1) = sK3(X0,X1,X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | (k8_tmap_1(X0,X1) = X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 1.48/0.54  
% 1.48/0.54  tff(u361,axiom,
% 1.48/0.54      (![X1, X0] : ((~v1_pre_topc(k8_tmap_1(X0,X1)) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 1.48/0.54  
% 1.48/0.54  tff(u360,negated_conjecture,
% 1.48/0.54      v1_pre_topc(k8_tmap_1(sK0,sK1))).
% 1.48/0.54  
% 1.48/0.54  tff(u359,negated_conjecture,
% 1.48/0.54      v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),sK1,k6_tmap_1(sK0,u1_struct_0(sK1)))).
% 1.48/0.54  
% 1.48/0.54  tff(u358,negated_conjecture,
% 1.48/0.54      v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),sK1,k8_tmap_1(sK0,sK1))).
% 1.48/0.54  
% 1.48/0.54  tff(u357,negated_conjecture,
% 1.48/0.54      ((~v5_pre_topc(k9_tmap_1(sK0,sK1),sK0,k8_tmap_1(sK0,sK1))) | v5_pre_topc(k9_tmap_1(sK0,sK1),sK0,k8_tmap_1(sK0,sK1)))).
% 1.48/0.54  
% 1.48/0.54  tff(u356,negated_conjecture,
% 1.48/0.54      ~r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),sK2)).
% 1.48/0.54  
% 1.48/0.54  tff(u355,axiom,
% 1.48/0.54      (![X1, X0, X2] : ((~r1_tmap_1(X0,X1,X2,sK4(X0,X1,X2)) | v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 1.48/0.54  
% 1.48/0.54  tff(u354,negated_conjecture,
% 1.48/0.54      ((~r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),sK2)) | r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),sK2))).
% 1.48/0.54  
% 1.48/0.54  % (8452)# SZS output end Saturation.
% 1.48/0.54  % (8452)------------------------------
% 1.48/0.54  % (8452)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.54  % (8452)Termination reason: Satisfiable
% 1.48/0.54  
% 1.48/0.54  % (8452)Memory used [KB]: 10746
% 1.48/0.54  % (8452)Time elapsed: 0.140 s
% 1.48/0.54  % (8452)------------------------------
% 1.48/0.54  % (8452)------------------------------
% 1.48/0.54  % (8466)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.48/0.54  % (8441)Success in time 0.189 s
%------------------------------------------------------------------------------
