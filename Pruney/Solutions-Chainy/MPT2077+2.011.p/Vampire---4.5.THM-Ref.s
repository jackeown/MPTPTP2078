%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:40 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  262 (5812 expanded)
%              Number of leaves         :   24 (1694 expanded)
%              Depth                    :   95
%              Number of atoms          : 2387 (69034 expanded)
%              Number of equality atoms :   49 ( 177 expanded)
%              Maximal formula depth    :   29 (  10 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f633,plain,(
    $false ),
    inference(subsumption_resolution,[],[f632,f69])).

fof(f69,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ( ( ! [X2] :
            ( ~ v3_yellow_6(X2,sK0)
            | ~ m2_yellow_6(X2,sK0,sK1) )
        & l1_waybel_0(sK1,sK0)
        & v7_waybel_0(sK1)
        & v4_orders_2(sK1)
        & ~ v2_struct_0(sK1) )
      | ~ v1_compts_1(sK0) )
    & ( ! [X3] :
          ( ( v3_yellow_6(sK2(X3),sK0)
            & m2_yellow_6(sK2(X3),sK0,X3) )
          | ~ l1_waybel_0(X3,sK0)
          | ~ v7_waybel_0(X3)
          | ~ v4_orders_2(X3)
          | v2_struct_0(X3) )
      | v1_compts_1(sK0) )
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f45,f48,f47,f46])).

fof(f46,plain,
    ( ? [X0] :
        ( ( ? [X1] :
              ( ! [X2] :
                  ( ~ v3_yellow_6(X2,X0)
                  | ~ m2_yellow_6(X2,X0,X1) )
              & l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
          | ~ v1_compts_1(X0) )
        & ( ! [X3] :
              ( ? [X4] :
                  ( v3_yellow_6(X4,X0)
                  & m2_yellow_6(X4,X0,X3) )
              | ~ l1_waybel_0(X3,X0)
              | ~ v7_waybel_0(X3)
              | ~ v4_orders_2(X3)
              | v2_struct_0(X3) )
          | v1_compts_1(X0) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ( ? [X1] :
            ( ! [X2] :
                ( ~ v3_yellow_6(X2,sK0)
                | ~ m2_yellow_6(X2,sK0,X1) )
            & l1_waybel_0(X1,sK0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        | ~ v1_compts_1(sK0) )
      & ( ! [X3] :
            ( ? [X4] :
                ( v3_yellow_6(X4,sK0)
                & m2_yellow_6(X4,sK0,X3) )
            | ~ l1_waybel_0(X3,sK0)
            | ~ v7_waybel_0(X3)
            | ~ v4_orders_2(X3)
            | v2_struct_0(X3) )
        | v1_compts_1(sK0) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X1] :
        ( ! [X2] :
            ( ~ v3_yellow_6(X2,sK0)
            | ~ m2_yellow_6(X2,sK0,X1) )
        & l1_waybel_0(X1,sK0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1) )
   => ( ! [X2] :
          ( ~ v3_yellow_6(X2,sK0)
          | ~ m2_yellow_6(X2,sK0,sK1) )
      & l1_waybel_0(sK1,sK0)
      & v7_waybel_0(sK1)
      & v4_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X3] :
      ( ? [X4] :
          ( v3_yellow_6(X4,sK0)
          & m2_yellow_6(X4,sK0,X3) )
     => ( v3_yellow_6(sK2(X3),sK0)
        & m2_yellow_6(sK2(X3),sK0,X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ! [X2] :
                ( ~ v3_yellow_6(X2,X0)
                | ~ m2_yellow_6(X2,X0,X1) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        | ~ v1_compts_1(X0) )
      & ( ! [X3] :
            ( ? [X4] :
                ( v3_yellow_6(X4,X0)
                & m2_yellow_6(X4,X0,X3) )
            | ~ l1_waybel_0(X3,X0)
            | ~ v7_waybel_0(X3)
            | ~ v4_orders_2(X3)
            | v2_struct_0(X3) )
        | v1_compts_1(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ! [X2] :
                ( ~ v3_yellow_6(X2,X0)
                | ~ m2_yellow_6(X2,X0,X1) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        | ~ v1_compts_1(X0) )
      & ( ! [X1] :
            ( ? [X2] :
                ( v3_yellow_6(X2,X0)
                & m2_yellow_6(X2,X0,X1) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) )
        | v1_compts_1(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ! [X2] :
                ( ~ v3_yellow_6(X2,X0)
                | ~ m2_yellow_6(X2,X0,X1) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        | ~ v1_compts_1(X0) )
      & ( ! [X1] :
            ( ? [X2] :
                ( v3_yellow_6(X2,X0)
                & m2_yellow_6(X2,X0,X1) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) )
        | v1_compts_1(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ( v1_compts_1(X0)
      <~> ! [X1] :
            ( ? [X2] :
                ( v3_yellow_6(X2,X0)
                & m2_yellow_6(X2,X0,X1) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ( v1_compts_1(X0)
      <~> ! [X1] :
            ( ? [X2] :
                ( v3_yellow_6(X2,X0)
                & m2_yellow_6(X2,X0,X1) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( v1_compts_1(X0)
        <=> ! [X1] :
              ( ( l1_waybel_0(X1,X0)
                & v7_waybel_0(X1)
                & v4_orders_2(X1)
                & ~ v2_struct_0(X1) )
             => ? [X2] :
                  ( v3_yellow_6(X2,X0)
                  & m2_yellow_6(X2,X0,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_compts_1(X0)
      <=> ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ? [X2] :
                ( v3_yellow_6(X2,X0)
                & m2_yellow_6(X2,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_yellow19)).

fof(f632,plain,(
    ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f631,f78])).

fof(f78,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f631,plain,(
    ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f630,f67])).

fof(f67,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f630,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f629,f68])).

fof(f68,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f629,plain,
    ( ~ l1_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f628,f69])).

fof(f628,plain,
    ( ~ l1_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f627,f351])).

fof(f351,plain,(
    ~ v1_compts_1(sK0) ),
    inference(subsumption_resolution,[],[f350,f72])).

fof(f72,plain,
    ( ~ v1_compts_1(sK0)
    | ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f350,plain,
    ( ~ v1_compts_1(sK0)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f349,f73])).

fof(f73,plain,
    ( ~ v1_compts_1(sK0)
    | v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f349,plain,
    ( ~ v1_compts_1(sK0)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f348,f74])).

fof(f74,plain,
    ( ~ v1_compts_1(sK0)
    | v7_waybel_0(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f348,plain,
    ( ~ v1_compts_1(sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f347,f75])).

fof(f75,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f347,plain,
    ( ~ v1_compts_1(sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f346,f67])).

fof(f346,plain,
    ( ~ v1_compts_1(sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f345,f68])).

fof(f345,plain,
    ( ~ v1_compts_1(sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f344,f69])).

fof(f344,plain,
    ( ~ v1_compts_1(sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f343])).

fof(f343,plain,
    ( ~ v1_compts_1(sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f320,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r3_waybel_9(X0,X1,sK3(X0,X1))
            & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f50])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r3_waybel_9(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X1,sK3(X0,X1))
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( r3_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( r3_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_compts_1(X0)
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l37_yellow19)).

fof(f320,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ v1_compts_1(sK0) ),
    inference(subsumption_resolution,[],[f319,f72])).

fof(f319,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ v1_compts_1(sK0)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f318,f73])).

fof(f318,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ v1_compts_1(sK0)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f317,f74])).

fof(f317,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ v1_compts_1(sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f316,f75])).

fof(f316,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ v1_compts_1(sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f315,f67])).

fof(f315,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ v1_compts_1(sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f314,f68])).

fof(f314,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ v1_compts_1(sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f313,f69])).

fof(f313,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ v1_compts_1(sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f307])).

fof(f307,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ v1_compts_1(sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f306,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r3_waybel_9(X0,X1,sK3(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f306,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f305,f72])).

fof(f305,plain,(
    ! [X0] :
      ( v2_struct_0(sK1)
      | ~ r3_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f304,f73])).

fof(f304,plain,(
    ! [X0] :
      ( ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ r3_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f303,f74])).

fof(f303,plain,(
    ! [X0] :
      ( ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ r3_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f302,f75])).

fof(f302,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ r3_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f301,f67])).

fof(f301,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ r3_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f300,f68])).

fof(f300,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r3_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f299,f69])).

fof(f299,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r3_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v1_compts_1(sK0) ) ),
    inference(duplicate_literal_removal,[],[f298])).

fof(f298,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r3_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK1,X0)
      | ~ v1_compts_1(sK0) ) ),
    inference(resolution,[],[f290,f201])).

fof(f201,plain,(
    ! [X0] :
      ( ~ v3_yellow_6(sK6(sK0,sK1,X0),sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK1,X0)
      | ~ v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f200,f72])).

fof(f200,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK1)
      | ~ v3_yellow_6(sK6(sK0,sK1,X0),sK0)
      | ~ v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f199,f73])).

fof(f199,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ v3_yellow_6(sK6(sK0,sK1,X0),sK0)
      | ~ v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f198,f74])).

fof(f198,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ v3_yellow_6(sK6(sK0,sK1,X0),sK0)
      | ~ v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f197,f75])).

fof(f197,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ v3_yellow_6(sK6(sK0,sK1,X0),sK0)
      | ~ v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f196,f67])).

fof(f196,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ v3_yellow_6(sK6(sK0,sK1,X0),sK0)
      | ~ v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f195,f68])).

fof(f195,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ v3_yellow_6(sK6(sK0,sK1,X0),sK0)
      | ~ v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f186,f69])).

fof(f186,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ v3_yellow_6(sK6(sK0,sK1,X0),sK0)
      | ~ v1_compts_1(sK0) ) ),
    inference(resolution,[],[f92,f76])).

fof(f76,plain,(
    ! [X2] :
      ( ~ m2_yellow_6(X2,sK0,sK1)
      | ~ v3_yellow_6(X2,sK0)
      | ~ v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( m2_yellow_6(sK6(X0,X1,X2),X0,X1)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,sK6(X0,X1,X2)))
                & m2_yellow_6(sK6(X0,X1,X2),X0,X1) )
              | ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f30,f58])).

fof(f58,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X2,k10_yellow_6(X0,X3))
          & m2_yellow_6(X3,X0,X1) )
     => ( r2_hidden(X2,k10_yellow_6(X0,sK6(X0,X1,X2)))
        & m2_yellow_6(sK6(X0,X1,X2),X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r2_hidden(X2,k10_yellow_6(X0,X3))
                  & m2_yellow_6(X3,X0,X1) )
              | ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r2_hidden(X2,k10_yellow_6(X0,X3))
                  & m2_yellow_6(X3,X0,X1) )
              | ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ~ ( ! [X3] :
                      ( m2_yellow_6(X3,X0,X1)
                     => ~ r2_hidden(X2,k10_yellow_6(X0,X3)) )
                  & r3_waybel_9(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_waybel_9)).

fof(f290,plain,(
    ! [X2,X0,X1] :
      ( v3_yellow_6(sK6(X0,X1,X2),X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f289,f205])).

fof(f205,plain,(
    ! [X12,X10,X11] :
      ( ~ v2_struct_0(sK6(X10,X11,X12))
      | ~ m1_subset_1(X12,u1_struct_0(X10))
      | ~ l1_waybel_0(X11,X10)
      | ~ v7_waybel_0(X11)
      | ~ v4_orders_2(X11)
      | v2_struct_0(X11)
      | ~ l1_pre_topc(X10)
      | ~ v2_pre_topc(X10)
      | v2_struct_0(X10)
      | ~ r3_waybel_9(X10,X11,X12) ) ),
    inference(subsumption_resolution,[],[f191,f78])).

fof(f191,plain,(
    ! [X12,X10,X11] :
      ( ~ r3_waybel_9(X10,X11,X12)
      | ~ m1_subset_1(X12,u1_struct_0(X10))
      | ~ l1_waybel_0(X11,X10)
      | ~ v7_waybel_0(X11)
      | ~ v4_orders_2(X11)
      | v2_struct_0(X11)
      | ~ l1_pre_topc(X10)
      | ~ v2_pre_topc(X10)
      | v2_struct_0(X10)
      | ~ v2_struct_0(sK6(X10,X11,X12))
      | ~ l1_struct_0(X10) ) ),
    inference(duplicate_literal_removal,[],[f190])).

fof(f190,plain,(
    ! [X12,X10,X11] :
      ( ~ r3_waybel_9(X10,X11,X12)
      | ~ m1_subset_1(X12,u1_struct_0(X10))
      | ~ l1_waybel_0(X11,X10)
      | ~ v7_waybel_0(X11)
      | ~ v4_orders_2(X11)
      | v2_struct_0(X11)
      | ~ l1_pre_topc(X10)
      | ~ v2_pre_topc(X10)
      | v2_struct_0(X10)
      | ~ v2_struct_0(sK6(X10,X11,X12))
      | ~ l1_waybel_0(X11,X10)
      | ~ v7_waybel_0(X11)
      | ~ v4_orders_2(X11)
      | v2_struct_0(X11)
      | ~ l1_struct_0(X10)
      | v2_struct_0(X10) ) ),
    inference(resolution,[],[f92,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_yellow_6(X2,X0,X1)
      | ~ v2_struct_0(X2)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
          | ~ m2_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
          | ~ m2_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_yellow_6(X2,X0,X1)
         => ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_yellow_6)).

fof(f289,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ r3_waybel_9(X0,X1,X2)
      | v3_yellow_6(sK6(X0,X1,X2),X0)
      | v2_struct_0(sK6(X0,X1,X2)) ) ),
    inference(subsumption_resolution,[],[f288,f204])).

fof(f204,plain,(
    ! [X8,X7,X9] :
      ( v4_orders_2(sK6(X7,X8,X9))
      | ~ m1_subset_1(X9,u1_struct_0(X7))
      | ~ l1_waybel_0(X8,X7)
      | ~ v7_waybel_0(X8)
      | ~ v4_orders_2(X8)
      | v2_struct_0(X8)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7)
      | ~ r3_waybel_9(X7,X8,X9) ) ),
    inference(subsumption_resolution,[],[f192,f78])).

fof(f192,plain,(
    ! [X8,X7,X9] :
      ( ~ r3_waybel_9(X7,X8,X9)
      | ~ m1_subset_1(X9,u1_struct_0(X7))
      | ~ l1_waybel_0(X8,X7)
      | ~ v7_waybel_0(X8)
      | ~ v4_orders_2(X8)
      | v2_struct_0(X8)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7)
      | v4_orders_2(sK6(X7,X8,X9))
      | ~ l1_struct_0(X7) ) ),
    inference(duplicate_literal_removal,[],[f189])).

fof(f189,plain,(
    ! [X8,X7,X9] :
      ( ~ r3_waybel_9(X7,X8,X9)
      | ~ m1_subset_1(X9,u1_struct_0(X7))
      | ~ l1_waybel_0(X8,X7)
      | ~ v7_waybel_0(X8)
      | ~ v4_orders_2(X8)
      | v2_struct_0(X8)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7)
      | v4_orders_2(sK6(X7,X8,X9))
      | ~ l1_waybel_0(X8,X7)
      | ~ v7_waybel_0(X8)
      | ~ v4_orders_2(X8)
      | v2_struct_0(X8)
      | ~ l1_struct_0(X7)
      | v2_struct_0(X7) ) ),
    inference(resolution,[],[f92,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_yellow_6(X2,X0,X1)
      | v4_orders_2(X2)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f288,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ r3_waybel_9(X0,X1,X2)
      | v3_yellow_6(sK6(X0,X1,X2),X0)
      | ~ v4_orders_2(sK6(X0,X1,X2))
      | v2_struct_0(sK6(X0,X1,X2)) ) ),
    inference(subsumption_resolution,[],[f287,f203])).

fof(f203,plain,(
    ! [X6,X4,X5] :
      ( v7_waybel_0(sK6(X4,X5,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ l1_waybel_0(X5,X4)
      | ~ v7_waybel_0(X5)
      | ~ v4_orders_2(X5)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | ~ r3_waybel_9(X4,X5,X6) ) ),
    inference(subsumption_resolution,[],[f193,f78])).

fof(f193,plain,(
    ! [X6,X4,X5] :
      ( ~ r3_waybel_9(X4,X5,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ l1_waybel_0(X5,X4)
      | ~ v7_waybel_0(X5)
      | ~ v4_orders_2(X5)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | v7_waybel_0(sK6(X4,X5,X6))
      | ~ l1_struct_0(X4) ) ),
    inference(duplicate_literal_removal,[],[f188])).

fof(f188,plain,(
    ! [X6,X4,X5] :
      ( ~ r3_waybel_9(X4,X5,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ l1_waybel_0(X5,X4)
      | ~ v7_waybel_0(X5)
      | ~ v4_orders_2(X5)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | v7_waybel_0(sK6(X4,X5,X6))
      | ~ l1_waybel_0(X5,X4)
      | ~ v7_waybel_0(X5)
      | ~ v4_orders_2(X5)
      | v2_struct_0(X5)
      | ~ l1_struct_0(X4)
      | v2_struct_0(X4) ) ),
    inference(resolution,[],[f92,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_yellow_6(X2,X0,X1)
      | v7_waybel_0(X2)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f287,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ r3_waybel_9(X0,X1,X2)
      | v3_yellow_6(sK6(X0,X1,X2),X0)
      | ~ v7_waybel_0(sK6(X0,X1,X2))
      | ~ v4_orders_2(sK6(X0,X1,X2))
      | v2_struct_0(sK6(X0,X1,X2)) ) ),
    inference(subsumption_resolution,[],[f286,f202])).

fof(f202,plain,(
    ! [X2,X3,X1] :
      ( l1_waybel_0(sK6(X1,X2,X3),X1)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_waybel_0(X2,X1)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ r3_waybel_9(X1,X2,X3) ) ),
    inference(subsumption_resolution,[],[f194,f78])).

fof(f194,plain,(
    ! [X2,X3,X1] :
      ( ~ r3_waybel_9(X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_waybel_0(X2,X1)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | l1_waybel_0(sK6(X1,X2,X3),X1)
      | ~ l1_struct_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f187])).

fof(f187,plain,(
    ! [X2,X3,X1] :
      ( ~ r3_waybel_9(X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_waybel_0(X2,X1)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | l1_waybel_0(sK6(X1,X2,X3),X1)
      | ~ l1_waybel_0(X2,X1)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f92,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_yellow_6(X2,X0,X1)
      | l1_waybel_0(X2,X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f286,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ r3_waybel_9(X0,X1,X2)
      | v3_yellow_6(sK6(X0,X1,X2),X0)
      | ~ l1_waybel_0(sK6(X0,X1,X2),X0)
      | ~ v7_waybel_0(sK6(X0,X1,X2))
      | ~ v4_orders_2(sK6(X0,X1,X2))
      | v2_struct_0(sK6(X0,X1,X2)) ) ),
    inference(subsumption_resolution,[],[f280,f114])).

fof(f114,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f107,f77])).

fof(f77,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f280,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_xboole_0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ r3_waybel_9(X0,X1,X2)
      | v3_yellow_6(sK6(X0,X1,X2),X0)
      | ~ l1_waybel_0(sK6(X0,X1,X2),X0)
      | ~ v7_waybel_0(sK6(X0,X1,X2))
      | ~ v4_orders_2(sK6(X0,X1,X2))
      | v2_struct_0(sK6(X0,X1,X2)) ) ),
    inference(duplicate_literal_removal,[],[f279])).

fof(f279,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_xboole_0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ r3_waybel_9(X0,X1,X2)
      | v3_yellow_6(sK6(X0,X1,X2),X0)
      | ~ l1_waybel_0(sK6(X0,X1,X2),X0)
      | ~ v7_waybel_0(sK6(X0,X1,X2))
      | ~ v4_orders_2(sK6(X0,X1,X2))
      | v2_struct_0(sK6(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f208,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k10_yellow_6(X0,X1)
      | v3_yellow_6(X1,X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_yellow_6(X1,X0)
              | k1_xboole_0 = k10_yellow_6(X0,X1) )
            & ( k1_xboole_0 != k10_yellow_6(X0,X1)
              | ~ v3_yellow_6(X1,X0) ) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_yellow_6(X1,X0)
          <=> k1_xboole_0 != k10_yellow_6(X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_yellow_6(X1,X0)
          <=> k1_xboole_0 != k10_yellow_6(X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ( v3_yellow_6(X1,X0)
          <=> k1_xboole_0 != k10_yellow_6(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_yellow_6)).

fof(f208,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_tarski(k10_yellow_6(X6,sK6(X6,X7,X8)),X8)
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ l1_waybel_0(X7,X6)
      | ~ v7_waybel_0(X7)
      | ~ v4_orders_2(X7)
      | v2_struct_0(X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | ~ r3_waybel_9(X6,X7,X8) ) ),
    inference(resolution,[],[f93,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k10_yellow_6(X0,sK6(X0,X1,X2)))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f627,plain,
    ( ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f626,f83])).

fof(f83,plain,(
    ! [X0] :
      ( ~ v2_struct_0(sK4(X0))
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ( ! [X2] :
                ( ~ r3_waybel_9(X0,sK4(X0),X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & r2_hidden(sK4(X0),k6_yellow_6(X0))
            & l1_waybel_0(sK4(X0),X0)
            & v7_waybel_0(sK4(X0))
            & v4_orders_2(sK4(X0))
            & ~ v2_struct_0(sK4(X0)) ) )
        & ( ! [X3] :
              ( ( r3_waybel_9(X0,X3,sK5(X0,X3))
                & m1_subset_1(sK5(X0,X3),u1_struct_0(X0)) )
              | ~ r2_hidden(X3,k6_yellow_6(X0))
              | ~ l1_waybel_0(X3,X0)
              | ~ v7_waybel_0(X3)
              | ~ v4_orders_2(X3)
              | v2_struct_0(X3) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f53,f55,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & r2_hidden(X1,k6_yellow_6(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
     => ( ! [X2] :
            ( ~ r3_waybel_9(X0,sK4(X0),X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & r2_hidden(sK4(X0),k6_yellow_6(X0))
        & l1_waybel_0(sK4(X0),X0)
        & v7_waybel_0(sK4(X0))
        & v4_orders_2(sK4(X0))
        & ~ v2_struct_0(sK4(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( r3_waybel_9(X0,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X3,sK5(X0,X3))
        & m1_subset_1(sK5(X0,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ? [X1] :
              ( ! [X2] :
                  ( ~ r3_waybel_9(X0,X1,X2)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              & r2_hidden(X1,k6_yellow_6(X0))
              & l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) ) )
        & ( ! [X3] :
              ( ? [X4] :
                  ( r3_waybel_9(X0,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_hidden(X3,k6_yellow_6(X0))
              | ~ l1_waybel_0(X3,X0)
              | ~ v7_waybel_0(X3)
              | ~ v4_orders_2(X3)
              | v2_struct_0(X3) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ? [X1] :
              ( ! [X2] :
                  ( ~ r3_waybel_9(X0,X1,X2)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              & r2_hidden(X1,k6_yellow_6(X0))
              & l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) ) )
        & ( ! [X1] :
              ( ? [X2] :
                  ( r3_waybel_9(X0,X1,X2)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ r2_hidden(X1,k6_yellow_6(X0))
              | ~ l1_waybel_0(X1,X0)
              | ~ v7_waybel_0(X1)
              | ~ v4_orders_2(X1)
              | v2_struct_0(X1) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> ! [X1] :
            ( ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r2_hidden(X1,k6_yellow_6(X0))
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> ! [X1] :
            ( ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r2_hidden(X1,k6_yellow_6(X0))
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_compts_1(X0)
      <=> ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ~ ( ! [X2] :
                    ( m1_subset_1(X2,u1_struct_0(X0))
                   => ~ r3_waybel_9(X0,X1,X2) )
                & r2_hidden(X1,k6_yellow_6(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_yellow19)).

fof(f626,plain,
    ( v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f625,f67])).

fof(f625,plain,
    ( v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f624,f68])).

fof(f624,plain,
    ( v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f623,f69])).

fof(f623,plain,
    ( v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f622,f351])).

fof(f622,plain,
    ( v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f621,f84])).

fof(f84,plain,(
    ! [X0] :
      ( v4_orders_2(sK4(X0))
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f621,plain,
    ( ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f620,f67])).

fof(f620,plain,
    ( ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f619,f68])).

fof(f619,plain,
    ( ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f618,f69])).

fof(f618,plain,
    ( ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f617,f351])).

fof(f617,plain,
    ( ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f616,f85])).

fof(f85,plain,(
    ! [X0] :
      ( v7_waybel_0(sK4(X0))
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f616,plain,
    ( ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f615,f351])).

fof(f615,plain,
    ( ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0) ),
    inference(duplicate_literal_removal,[],[f614])).

fof(f614,plain,
    ( ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0) ),
    inference(resolution,[],[f613,f125])).

fof(f125,plain,
    ( ~ v2_struct_0(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0) ),
    inference(subsumption_resolution,[],[f124,f67])).

fof(f124,plain,
    ( ~ v2_struct_0(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f123,f68])).

fof(f123,plain,
    ( ~ v2_struct_0(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f122,f69])).

fof(f122,plain,
    ( ~ v2_struct_0(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f121])).

fof(f121,plain,
    ( ~ v2_struct_0(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f119,f86])).

fof(f86,plain,(
    ! [X0] :
      ( l1_waybel_0(sK4(X0),X0)
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f119,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ v2_struct_0(sK2(X0))
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(sK0)
      | v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f118,f67])).

fof(f118,plain,(
    ! [X0] :
      ( ~ v2_struct_0(sK2(X0))
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0)
      | v1_compts_1(sK0) ) ),
    inference(duplicate_literal_removal,[],[f117])).

fof(f117,plain,(
    ! [X0] :
      ( ~ v2_struct_0(sK2(X0))
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | v1_compts_1(sK0) ) ),
    inference(resolution,[],[f102,f70])).

fof(f70,plain,(
    ! [X3] :
      ( m2_yellow_6(sK2(X3),sK0,X3)
      | ~ l1_waybel_0(X3,sK0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f613,plain,
    ( v2_struct_0(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f612,f351])).

fof(f612,plain,
    ( v2_struct_0(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0) ),
    inference(duplicate_literal_removal,[],[f611])).

fof(f611,plain,
    ( v2_struct_0(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0) ),
    inference(resolution,[],[f606,f134])).

fof(f134,plain,
    ( v4_orders_2(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0) ),
    inference(subsumption_resolution,[],[f133,f67])).

fof(f133,plain,
    ( v4_orders_2(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f132,f68])).

fof(f132,plain,
    ( v4_orders_2(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f131,f69])).

fof(f131,plain,
    ( v4_orders_2(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f130])).

fof(f130,plain,
    ( v4_orders_2(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f128,f86])).

fof(f128,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(X0,sK0)
      | v4_orders_2(sK2(X0))
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(sK0)
      | v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f127,f67])).

fof(f127,plain,(
    ! [X0] :
      ( v4_orders_2(sK2(X0))
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0)
      | v1_compts_1(sK0) ) ),
    inference(duplicate_literal_removal,[],[f126])).

fof(f126,plain,(
    ! [X0] :
      ( v4_orders_2(sK2(X0))
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | v1_compts_1(sK0) ) ),
    inference(resolution,[],[f103,f70])).

fof(f606,plain,
    ( ~ v4_orders_2(sK2(sK4(sK0)))
    | v2_struct_0(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f605,f351])).

fof(f605,plain,
    ( v2_struct_0(sK2(sK4(sK0)))
    | ~ v4_orders_2(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0) ),
    inference(duplicate_literal_removal,[],[f604])).

fof(f604,plain,
    ( v2_struct_0(sK2(sK4(sK0)))
    | ~ v4_orders_2(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0) ),
    inference(resolution,[],[f603,f143])).

fof(f143,plain,
    ( v7_waybel_0(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0) ),
    inference(subsumption_resolution,[],[f142,f67])).

fof(f142,plain,
    ( v7_waybel_0(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f141,f68])).

fof(f141,plain,
    ( v7_waybel_0(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f140,f69])).

fof(f140,plain,
    ( v7_waybel_0(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f139])).

fof(f139,plain,
    ( v7_waybel_0(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f137,f86])).

fof(f137,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(X0,sK0)
      | v7_waybel_0(sK2(X0))
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(sK0)
      | v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f136,f67])).

fof(f136,plain,(
    ! [X0] :
      ( v7_waybel_0(sK2(X0))
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0)
      | v1_compts_1(sK0) ) ),
    inference(duplicate_literal_removal,[],[f135])).

fof(f135,plain,(
    ! [X0] :
      ( v7_waybel_0(sK2(X0))
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | v1_compts_1(sK0) ) ),
    inference(resolution,[],[f104,f70])).

fof(f603,plain,
    ( ~ v7_waybel_0(sK2(sK4(sK0)))
    | v2_struct_0(sK2(sK4(sK0)))
    | ~ v4_orders_2(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f602,f67])).

fof(f602,plain,
    ( ~ v4_orders_2(sK2(sK4(sK0)))
    | v2_struct_0(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f601,f68])).

fof(f601,plain,
    ( ~ v4_orders_2(sK2(sK4(sK0)))
    | v2_struct_0(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f600,f69])).

fof(f600,plain,
    ( ~ v4_orders_2(sK2(sK4(sK0)))
    | v2_struct_0(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f599,f351])).

fof(f599,plain,
    ( ~ v4_orders_2(sK2(sK4(sK0)))
    | v2_struct_0(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f598,f86])).

fof(f598,plain,
    ( ~ l1_waybel_0(sK4(sK0),sK0)
    | ~ v4_orders_2(sK2(sK4(sK0)))
    | v2_struct_0(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f597,f351])).

fof(f597,plain,
    ( ~ v7_waybel_0(sK2(sK4(sK0)))
    | ~ v4_orders_2(sK2(sK4(sK0)))
    | v2_struct_0(sK2(sK4(sK0)))
    | ~ l1_waybel_0(sK4(sK0),sK0)
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0) ),
    inference(duplicate_literal_removal,[],[f596])).

fof(f596,plain,
    ( ~ v7_waybel_0(sK2(sK4(sK0)))
    | ~ v4_orders_2(sK2(sK4(sK0)))
    | v2_struct_0(sK2(sK4(sK0)))
    | ~ l1_waybel_0(sK4(sK0),sK0)
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_waybel_0(sK4(sK0),sK0)
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0) ),
    inference(resolution,[],[f595,f146])).

fof(f146,plain,(
    ! [X0] :
      ( l1_waybel_0(sK2(X0),sK0)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(sK0)
      | v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f145,f67])).

fof(f145,plain,(
    ! [X0] :
      ( l1_waybel_0(sK2(X0),sK0)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0)
      | v1_compts_1(sK0) ) ),
    inference(duplicate_literal_removal,[],[f144])).

fof(f144,plain,(
    ! [X0] :
      ( l1_waybel_0(sK2(X0),sK0)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | v1_compts_1(sK0) ) ),
    inference(resolution,[],[f105,f70])).

fof(f595,plain,
    ( ~ l1_waybel_0(sK2(sK4(sK0)),sK0)
    | ~ v7_waybel_0(sK2(sK4(sK0)))
    | ~ v4_orders_2(sK2(sK4(sK0)))
    | v2_struct_0(sK2(sK4(sK0)))
    | ~ l1_waybel_0(sK4(sK0),sK0)
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0)) ),
    inference(subsumption_resolution,[],[f594,f351])).

fof(f594,plain,
    ( ~ l1_waybel_0(sK2(sK4(sK0)),sK0)
    | ~ v7_waybel_0(sK2(sK4(sK0)))
    | ~ v4_orders_2(sK2(sK4(sK0)))
    | v2_struct_0(sK2(sK4(sK0)))
    | ~ l1_waybel_0(sK4(sK0),sK0)
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | v1_compts_1(sK0) ),
    inference(duplicate_literal_removal,[],[f593])).

fof(f593,plain,
    ( ~ l1_waybel_0(sK2(sK4(sK0)),sK0)
    | ~ v7_waybel_0(sK2(sK4(sK0)))
    | ~ v4_orders_2(sK2(sK4(sK0)))
    | v2_struct_0(sK2(sK4(sK0)))
    | ~ l1_waybel_0(sK4(sK0),sK0)
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_waybel_0(sK4(sK0),sK0)
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | v1_compts_1(sK0) ),
    inference(resolution,[],[f580,f71])).

fof(f71,plain,(
    ! [X3] :
      ( v3_yellow_6(sK2(X3),sK0)
      | ~ l1_waybel_0(X3,sK0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f580,plain,
    ( ~ v3_yellow_6(sK2(sK4(sK0)),sK0)
    | ~ l1_waybel_0(sK2(sK4(sK0)),sK0)
    | ~ v7_waybel_0(sK2(sK4(sK0)))
    | ~ v4_orders_2(sK2(sK4(sK0)))
    | v2_struct_0(sK2(sK4(sK0)))
    | ~ l1_waybel_0(sK4(sK0),sK0)
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0)) ),
    inference(subsumption_resolution,[],[f579,f67])).

fof(f579,plain,
    ( ~ v3_yellow_6(sK2(sK4(sK0)),sK0)
    | ~ l1_waybel_0(sK2(sK4(sK0)),sK0)
    | ~ v7_waybel_0(sK2(sK4(sK0)))
    | ~ v4_orders_2(sK2(sK4(sK0)))
    | v2_struct_0(sK2(sK4(sK0)))
    | v2_struct_0(sK0)
    | ~ l1_waybel_0(sK4(sK0),sK0)
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0)) ),
    inference(subsumption_resolution,[],[f578,f68])).

fof(f578,plain,
    ( ~ v3_yellow_6(sK2(sK4(sK0)),sK0)
    | ~ l1_waybel_0(sK2(sK4(sK0)),sK0)
    | ~ v7_waybel_0(sK2(sK4(sK0)))
    | ~ v4_orders_2(sK2(sK4(sK0)))
    | v2_struct_0(sK2(sK4(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_waybel_0(sK4(sK0),sK0)
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0)) ),
    inference(subsumption_resolution,[],[f577,f69])).

fof(f577,plain,
    ( ~ v3_yellow_6(sK2(sK4(sK0)),sK0)
    | ~ l1_waybel_0(sK2(sK4(sK0)),sK0)
    | ~ v7_waybel_0(sK2(sK4(sK0)))
    | ~ v4_orders_2(sK2(sK4(sK0)))
    | v2_struct_0(sK2(sK4(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_waybel_0(sK4(sK0),sK0)
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0)) ),
    inference(trivial_inequality_removal,[],[f576])).

fof(f576,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v3_yellow_6(sK2(sK4(sK0)),sK0)
    | ~ l1_waybel_0(sK2(sK4(sK0)),sK0)
    | ~ v7_waybel_0(sK2(sK4(sK0)))
    | ~ v4_orders_2(sK2(sK4(sK0)))
    | v2_struct_0(sK2(sK4(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_waybel_0(sK4(sK0),sK0)
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0)) ),
    inference(duplicate_literal_removal,[],[f557])).

fof(f557,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v3_yellow_6(sK2(sK4(sK0)),sK0)
    | ~ l1_waybel_0(sK2(sK4(sK0)),sK0)
    | ~ v7_waybel_0(sK2(sK4(sK0)))
    | ~ v4_orders_2(sK2(sK4(sK0)))
    | v2_struct_0(sK2(sK4(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK2(sK4(sK0)))
    | ~ v4_orders_2(sK2(sK4(sK0)))
    | ~ l1_waybel_0(sK2(sK4(sK0)),sK0)
    | ~ l1_waybel_0(sK4(sK0),sK0)
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ v7_waybel_0(sK2(sK4(sK0))) ),
    inference(superposition,[],[f89,f556])).

fof(f556,plain,
    ( k1_xboole_0 = k10_yellow_6(sK0,sK2(sK4(sK0)))
    | v2_struct_0(sK2(sK4(sK0)))
    | ~ v4_orders_2(sK2(sK4(sK0)))
    | ~ l1_waybel_0(sK2(sK4(sK0)),sK0)
    | ~ l1_waybel_0(sK4(sK0),sK0)
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ v7_waybel_0(sK2(sK4(sK0))) ),
    inference(subsumption_resolution,[],[f553,f77])).

fof(f553,plain,
    ( ~ v4_orders_2(sK2(sK4(sK0)))
    | v2_struct_0(sK2(sK4(sK0)))
    | k1_xboole_0 = k10_yellow_6(sK0,sK2(sK4(sK0)))
    | ~ l1_waybel_0(sK2(sK4(sK0)),sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_waybel_0(sK4(sK0),sK0)
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ v7_waybel_0(sK2(sK4(sK0))) ),
    inference(resolution,[],[f536,f114])).

fof(f536,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK7(sK0,sK2(sK4(sK0)),X0))
      | ~ v4_orders_2(sK2(sK4(sK0)))
      | v2_struct_0(sK2(sK4(sK0)))
      | k10_yellow_6(sK0,sK2(sK4(sK0))) = X0
      | ~ l1_waybel_0(sK2(sK4(sK0)),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_waybel_0(sK4(sK0),sK0)
      | ~ v7_waybel_0(sK4(sK0))
      | ~ v4_orders_2(sK4(sK0))
      | v2_struct_0(sK4(sK0))
      | ~ v7_waybel_0(sK2(sK4(sK0))) ) ),
    inference(resolution,[],[f534,f108])).

fof(f534,plain,(
    ! [X0] :
      ( r2_hidden(sK7(sK0,sK2(sK4(sK0)),X0),X0)
      | ~ v7_waybel_0(sK2(sK4(sK0)))
      | ~ v4_orders_2(sK2(sK4(sK0)))
      | v2_struct_0(sK2(sK4(sK0)))
      | k10_yellow_6(sK0,sK2(sK4(sK0))) = X0
      | ~ l1_waybel_0(sK2(sK4(sK0)),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_waybel_0(sK4(sK0),sK0)
      | ~ v7_waybel_0(sK4(sK0))
      | ~ v4_orders_2(sK4(sK0))
      | v2_struct_0(sK4(sK0)) ) ),
    inference(subsumption_resolution,[],[f533,f67])).

fof(f533,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(sK2(sK4(sK0)),sK0)
      | ~ v7_waybel_0(sK2(sK4(sK0)))
      | ~ v4_orders_2(sK2(sK4(sK0)))
      | v2_struct_0(sK2(sK4(sK0)))
      | k10_yellow_6(sK0,sK2(sK4(sK0))) = X0
      | r2_hidden(sK7(sK0,sK2(sK4(sK0)),X0),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_waybel_0(sK4(sK0),sK0)
      | ~ v7_waybel_0(sK4(sK0))
      | ~ v4_orders_2(sK4(sK0))
      | v2_struct_0(sK4(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f532,f68])).

fof(f532,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(sK2(sK4(sK0)),sK0)
      | ~ v7_waybel_0(sK2(sK4(sK0)))
      | ~ v4_orders_2(sK2(sK4(sK0)))
      | v2_struct_0(sK2(sK4(sK0)))
      | k10_yellow_6(sK0,sK2(sK4(sK0))) = X0
      | r2_hidden(sK7(sK0,sK2(sK4(sK0)),X0),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_waybel_0(sK4(sK0),sK0)
      | ~ v7_waybel_0(sK4(sK0))
      | ~ v4_orders_2(sK4(sK0))
      | v2_struct_0(sK4(sK0))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f531,f69])).

fof(f531,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(sK2(sK4(sK0)),sK0)
      | ~ v7_waybel_0(sK2(sK4(sK0)))
      | ~ v4_orders_2(sK2(sK4(sK0)))
      | v2_struct_0(sK2(sK4(sK0)))
      | k10_yellow_6(sK0,sK2(sK4(sK0))) = X0
      | r2_hidden(sK7(sK0,sK2(sK4(sK0)),X0),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_waybel_0(sK4(sK0),sK0)
      | ~ v7_waybel_0(sK4(sK0))
      | ~ v4_orders_2(sK4(sK0))
      | v2_struct_0(sK4(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f530])).

fof(f530,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(sK2(sK4(sK0)),sK0)
      | ~ v7_waybel_0(sK2(sK4(sK0)))
      | ~ v4_orders_2(sK2(sK4(sK0)))
      | v2_struct_0(sK2(sK4(sK0)))
      | k10_yellow_6(sK0,sK2(sK4(sK0))) = X0
      | r2_hidden(sK7(sK0,sK2(sK4(sK0)),X0),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_waybel_0(sK4(sK0),sK0)
      | ~ v7_waybel_0(sK4(sK0))
      | ~ v4_orders_2(sK4(sK0))
      | v2_struct_0(sK4(sK0))
      | k10_yellow_6(sK0,sK2(sK4(sK0))) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_waybel_0(sK2(sK4(sK0)),sK0)
      | ~ v7_waybel_0(sK2(sK4(sK0)))
      | ~ v4_orders_2(sK2(sK4(sK0)))
      | v2_struct_0(sK2(sK4(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f515,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))
      | k10_yellow_6(X0,X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ( ( ( ~ r1_waybel_0(X0,X1,sK8(X0,X1,X2))
                        & m1_connsp_2(sK8(X0,X1,X2),X0,sK7(X0,X1,X2)) )
                      | ~ r2_hidden(sK7(X0,X1,X2),X2) )
                    & ( ! [X5] :
                          ( r1_waybel_0(X0,X1,X5)
                          | ~ m1_connsp_2(X5,X0,sK7(X0,X1,X2)) )
                      | r2_hidden(sK7(X0,X1,X2),X2) )
                    & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ( ~ r1_waybel_0(X0,X1,sK9(X0,X1,X6))
                            & m1_connsp_2(sK9(X0,X1,X6),X0,X6) ) )
                        & ( ! [X8] :
                              ( r1_waybel_0(X0,X1,X8)
                              | ~ m1_connsp_2(X8,X0,X6) )
                          | ~ r2_hidden(X6,X2) ) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | k10_yellow_6(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f62,f65,f64,f63])).

fof(f63,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ? [X4] :
                ( ~ r1_waybel_0(X0,X1,X4)
                & m1_connsp_2(X4,X0,X3) )
            | ~ r2_hidden(X3,X2) )
          & ( ! [X5] :
                ( r1_waybel_0(X0,X1,X5)
                | ~ m1_connsp_2(X5,X0,X3) )
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ? [X4] :
              ( ~ r1_waybel_0(X0,X1,X4)
              & m1_connsp_2(X4,X0,sK7(X0,X1,X2)) )
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( ! [X5] :
              ( r1_waybel_0(X0,X1,X5)
              | ~ m1_connsp_2(X5,X0,sK7(X0,X1,X2)) )
          | r2_hidden(sK7(X0,X1,X2),X2) )
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_waybel_0(X0,X1,X4)
          & m1_connsp_2(X4,X0,sK7(X0,X1,X2)) )
     => ( ~ r1_waybel_0(X0,X1,sK8(X0,X1,X2))
        & m1_connsp_2(sK8(X0,X1,X2),X0,sK7(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X6,X1,X0] :
      ( ? [X7] :
          ( ~ r1_waybel_0(X0,X1,X7)
          & m1_connsp_2(X7,X0,X6) )
     => ( ~ r1_waybel_0(X0,X1,sK9(X0,X1,X6))
        & m1_connsp_2(sK9(X0,X1,X6),X0,X6) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ? [X3] :
                      ( ( ? [X4] :
                            ( ~ r1_waybel_0(X0,X1,X4)
                            & m1_connsp_2(X4,X0,X3) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ! [X5] :
                            ( r1_waybel_0(X0,X1,X5)
                            | ~ m1_connsp_2(X5,X0,X3) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ? [X7] :
                              ( ~ r1_waybel_0(X0,X1,X7)
                              & m1_connsp_2(X7,X0,X6) ) )
                        & ( ! [X8] :
                              ( r1_waybel_0(X0,X1,X8)
                              | ~ m1_connsp_2(X8,X0,X6) )
                          | ~ r2_hidden(X6,X2) ) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | k10_yellow_6(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ? [X3] :
                      ( ( ? [X4] :
                            ( ~ r1_waybel_0(X0,X1,X4)
                            & m1_connsp_2(X4,X0,X3) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ! [X4] :
                            ( r1_waybel_0(X0,X1,X4)
                            | ~ m1_connsp_2(X4,X0,X3) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( ( ( r2_hidden(X3,X2)
                          | ? [X4] :
                              ( ~ r1_waybel_0(X0,X1,X4)
                              & m1_connsp_2(X4,X0,X3) ) )
                        & ( ! [X4] :
                              ( r1_waybel_0(X0,X1,X4)
                              | ~ m1_connsp_2(X4,X0,X3) )
                          | ~ r2_hidden(X3,X2) ) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | k10_yellow_6(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ? [X3] :
                      ( ( ? [X4] :
                            ( ~ r1_waybel_0(X0,X1,X4)
                            & m1_connsp_2(X4,X0,X3) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ! [X4] :
                            ( r1_waybel_0(X0,X1,X4)
                            | ~ m1_connsp_2(X4,X0,X3) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( ( ( r2_hidden(X3,X2)
                          | ? [X4] :
                              ( ~ r1_waybel_0(X0,X1,X4)
                              & m1_connsp_2(X4,X0,X3) ) )
                        & ( ! [X4] :
                              ( r1_waybel_0(X0,X1,X4)
                              | ~ m1_connsp_2(X4,X0,X3) )
                          | ~ r2_hidden(X3,X2) ) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | k10_yellow_6(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k10_yellow_6(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( r1_waybel_0(X0,X1,X4)
                          | ~ m1_connsp_2(X4,X0,X3) ) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k10_yellow_6(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( r1_waybel_0(X0,X1,X4)
                          | ~ m1_connsp_2(X4,X0,X3) ) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k10_yellow_6(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( m1_connsp_2(X4,X0,X3)
                         => r1_waybel_0(X0,X1,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_yellow_6)).

fof(f515,plain,(
    ! [X2] :
      ( ~ m1_subset_1(sK7(sK0,sK2(sK4(sK0)),X2),u1_struct_0(sK0))
      | ~ l1_waybel_0(sK2(sK4(sK0)),sK0)
      | ~ v7_waybel_0(sK2(sK4(sK0)))
      | ~ v4_orders_2(sK2(sK4(sK0)))
      | v2_struct_0(sK2(sK4(sK0)))
      | k10_yellow_6(sK0,sK2(sK4(sK0))) = X2
      | r2_hidden(sK7(sK0,sK2(sK4(sK0)),X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_waybel_0(sK4(sK0),sK0)
      | ~ v7_waybel_0(sK4(sK0))
      | ~ v4_orders_2(sK4(sK0))
      | v2_struct_0(sK4(sK0)) ) ),
    inference(subsumption_resolution,[],[f514,f351])).

fof(f514,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_waybel_0(sK2(sK4(sK0)),sK0)
      | ~ v7_waybel_0(sK2(sK4(sK0)))
      | ~ v4_orders_2(sK2(sK4(sK0)))
      | v2_struct_0(sK2(sK4(sK0)))
      | k10_yellow_6(sK0,sK2(sK4(sK0))) = X2
      | r2_hidden(sK7(sK0,sK2(sK4(sK0)),X2),X2)
      | ~ m1_subset_1(sK7(sK0,sK2(sK4(sK0)),X2),u1_struct_0(sK0))
      | v1_compts_1(sK0)
      | ~ l1_waybel_0(sK4(sK0),sK0)
      | ~ v7_waybel_0(sK4(sK0))
      | ~ v4_orders_2(sK4(sK0))
      | v2_struct_0(sK4(sK0)) ) ),
    inference(subsumption_resolution,[],[f513,f67])).

fof(f513,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_waybel_0(sK2(sK4(sK0)),sK0)
      | ~ v7_waybel_0(sK2(sK4(sK0)))
      | ~ v4_orders_2(sK2(sK4(sK0)))
      | v2_struct_0(sK2(sK4(sK0)))
      | v2_struct_0(sK0)
      | k10_yellow_6(sK0,sK2(sK4(sK0))) = X2
      | r2_hidden(sK7(sK0,sK2(sK4(sK0)),X2),X2)
      | ~ m1_subset_1(sK7(sK0,sK2(sK4(sK0)),X2),u1_struct_0(sK0))
      | v1_compts_1(sK0)
      | ~ l1_waybel_0(sK4(sK0),sK0)
      | ~ v7_waybel_0(sK4(sK0))
      | ~ v4_orders_2(sK4(sK0))
      | v2_struct_0(sK4(sK0)) ) ),
    inference(subsumption_resolution,[],[f512,f68])).

fof(f512,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_waybel_0(sK2(sK4(sK0)),sK0)
      | ~ v7_waybel_0(sK2(sK4(sK0)))
      | ~ v4_orders_2(sK2(sK4(sK0)))
      | v2_struct_0(sK2(sK4(sK0)))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | k10_yellow_6(sK0,sK2(sK4(sK0))) = X2
      | r2_hidden(sK7(sK0,sK2(sK4(sK0)),X2),X2)
      | ~ m1_subset_1(sK7(sK0,sK2(sK4(sK0)),X2),u1_struct_0(sK0))
      | v1_compts_1(sK0)
      | ~ l1_waybel_0(sK4(sK0),sK0)
      | ~ v7_waybel_0(sK4(sK0))
      | ~ v4_orders_2(sK4(sK0))
      | v2_struct_0(sK4(sK0)) ) ),
    inference(subsumption_resolution,[],[f500,f69])).

fof(f500,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_waybel_0(sK2(sK4(sK0)),sK0)
      | ~ v7_waybel_0(sK2(sK4(sK0)))
      | ~ v4_orders_2(sK2(sK4(sK0)))
      | v2_struct_0(sK2(sK4(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | k10_yellow_6(sK0,sK2(sK4(sK0))) = X2
      | r2_hidden(sK7(sK0,sK2(sK4(sK0)),X2),X2)
      | ~ m1_subset_1(sK7(sK0,sK2(sK4(sK0)),X2),u1_struct_0(sK0))
      | v1_compts_1(sK0)
      | ~ l1_waybel_0(sK4(sK0),sK0)
      | ~ v7_waybel_0(sK4(sK0))
      | ~ v4_orders_2(sK4(sK0))
      | v2_struct_0(sK4(sK0)) ) ),
    inference(resolution,[],[f484,f245])).

fof(f245,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK2(sK4(sK0)),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v1_compts_1(sK0)
      | ~ l1_waybel_0(sK4(sK0),sK0)
      | ~ v7_waybel_0(sK4(sK0))
      | ~ v4_orders_2(sK4(sK0))
      | v2_struct_0(sK4(sK0)) ) ),
    inference(subsumption_resolution,[],[f244,f67])).

fof(f244,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK2(sK4(sK0)),X0)
      | v2_struct_0(sK0)
      | v1_compts_1(sK0)
      | ~ l1_waybel_0(sK4(sK0),sK0)
      | ~ v7_waybel_0(sK4(sK0))
      | ~ v4_orders_2(sK4(sK0))
      | v2_struct_0(sK4(sK0)) ) ),
    inference(subsumption_resolution,[],[f243,f68])).

fof(f243,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK2(sK4(sK0)),X0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | v1_compts_1(sK0)
      | ~ l1_waybel_0(sK4(sK0),sK0)
      | ~ v7_waybel_0(sK4(sK0))
      | ~ v4_orders_2(sK4(sK0))
      | v2_struct_0(sK4(sK0)) ) ),
    inference(subsumption_resolution,[],[f242,f69])).

fof(f242,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK2(sK4(sK0)),X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | v1_compts_1(sK0)
      | ~ l1_waybel_0(sK4(sK0),sK0)
      | ~ v7_waybel_0(sK4(sK0))
      | ~ v4_orders_2(sK4(sK0))
      | v2_struct_0(sK4(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f239])).

fof(f239,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK2(sK4(sK0)),X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | v1_compts_1(sK0)
      | ~ l1_waybel_0(sK4(sK0),sK0)
      | ~ v7_waybel_0(sK4(sK0))
      | ~ v4_orders_2(sK4(sK0))
      | v2_struct_0(sK4(sK0))
      | v1_compts_1(sK0) ) ),
    inference(resolution,[],[f238,f70])).

fof(f238,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_yellow_6(X1,X0,sK4(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_compts_1(X0) ) ),
    inference(subsumption_resolution,[],[f237,f83])).

fof(f237,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m2_yellow_6(X1,X0,sK4(X0))
      | v2_struct_0(sK4(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_compts_1(X0) ) ),
    inference(subsumption_resolution,[],[f236,f84])).

fof(f236,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m2_yellow_6(X1,X0,sK4(X0))
      | ~ v4_orders_2(sK4(X0))
      | v2_struct_0(sK4(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_compts_1(X0) ) ),
    inference(subsumption_resolution,[],[f235,f85])).

fof(f235,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m2_yellow_6(X1,X0,sK4(X0))
      | ~ v7_waybel_0(sK4(X0))
      | ~ v4_orders_2(sK4(X0))
      | v2_struct_0(sK4(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_compts_1(X0) ) ),
    inference(subsumption_resolution,[],[f234,f86])).

fof(f234,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m2_yellow_6(X1,X0,sK4(X0))
      | ~ l1_waybel_0(sK4(X0),X0)
      | ~ v7_waybel_0(sK4(X0))
      | ~ v4_orders_2(sK4(X0))
      | v2_struct_0(sK4(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_compts_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f233])).

fof(f233,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m2_yellow_6(X1,X0,sK4(X0))
      | ~ l1_waybel_0(sK4(X0),X0)
      | ~ v7_waybel_0(sK4(X0))
      | ~ v4_orders_2(sK4(X0))
      | v2_struct_0(sK4(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_compts_1(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f94,f88])).

fof(f88,plain,(
    ! [X2,X0] :
      ( ~ r3_waybel_9(X0,sK4(X0),X2)
      | v1_compts_1(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( r3_waybel_9(X0,X1,X3)
      | ~ r3_waybel_9(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r3_waybel_9(X0,X1,X3)
                  | ~ r3_waybel_9(X0,X2,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m2_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r3_waybel_9(X0,X1,X3)
                  | ~ r3_waybel_9(X0,X2,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m2_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m2_yellow_6(X2,X0,X1)
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r3_waybel_9(X0,X2,X3)
                   => r3_waybel_9(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_waybel_9)).

fof(f484,plain,(
    ! [X6,X4,X5] :
      ( r3_waybel_9(X4,X5,sK7(X4,X5,X6))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))
      | ~ l1_waybel_0(X5,X4)
      | ~ v7_waybel_0(X5)
      | ~ v4_orders_2(X5)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | k10_yellow_6(X4,X5) = X6
      | r2_hidden(sK7(X4,X5,X6),X6) ) ),
    inference(subsumption_resolution,[],[f482,f98])).

fof(f482,plain,(
    ! [X6,X4,X5] :
      ( r2_hidden(sK7(X4,X5,X6),X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))
      | ~ l1_waybel_0(X5,X4)
      | ~ v7_waybel_0(X5)
      | ~ v4_orders_2(X5)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | k10_yellow_6(X4,X5) = X6
      | r3_waybel_9(X4,X5,sK7(X4,X5,X6))
      | ~ m1_subset_1(sK7(X4,X5,X6),u1_struct_0(X4)) ) ),
    inference(duplicate_literal_removal,[],[f475])).

fof(f475,plain,(
    ! [X6,X4,X5] :
      ( r2_hidden(sK7(X4,X5,X6),X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))
      | ~ l1_waybel_0(X5,X4)
      | ~ v7_waybel_0(X5)
      | ~ v4_orders_2(X5)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | k10_yellow_6(X4,X5) = X6
      | r3_waybel_9(X4,X5,sK7(X4,X5,X6))
      | ~ m1_subset_1(sK7(X4,X5,X6),u1_struct_0(X4))
      | ~ l1_waybel_0(X5,X4)
      | ~ v7_waybel_0(X5)
      | ~ v4_orders_2(X5)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(resolution,[],[f473,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k10_yellow_6(X0,X1))
      | r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_waybel_9(X0,X1,X2)
              | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_waybel_9(X0,X1,X2)
              | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k10_yellow_6(X0,X1))
               => r3_waybel_9(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_waybel_9)).

fof(f473,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X2),k10_yellow_6(X0,X1))
      | r2_hidden(sK7(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | k10_yellow_6(X0,X1) = X2 ) ),
    inference(subsumption_resolution,[],[f472,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_yellow_6)).

fof(f472,plain,(
    ! [X2,X0,X1] :
      ( k10_yellow_6(X0,X1) = X2
      | r2_hidden(sK7(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | r2_hidden(sK7(X0,X1,X2),k10_yellow_6(X0,X1))
      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(subsumption_resolution,[],[f471,f98])).

fof(f471,plain,(
    ! [X2,X0,X1] :
      ( k10_yellow_6(X0,X1) = X2
      | r2_hidden(sK7(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | r2_hidden(sK7(X0,X1,X2),k10_yellow_6(X0,X1))
      | ~ m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(duplicate_literal_removal,[],[f470])).

fof(f470,plain,(
    ! [X2,X0,X1] :
      ( k10_yellow_6(X0,X1) = X2
      | r2_hidden(sK7(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | r2_hidden(sK7(X0,X1,X2),k10_yellow_6(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | r2_hidden(sK7(X0,X1,X2),k10_yellow_6(X0,X1))
      | ~ m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f460,f110])).

fof(f110,plain,(
    ! [X6,X0,X1] :
      ( ~ r1_waybel_0(X0,X1,sK9(X0,X1,X6))
      | r2_hidden(X6,k10_yellow_6(X0,X1))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | ~ r1_waybel_0(X0,X1,sK9(X0,X1,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | k10_yellow_6(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f460,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_waybel_0(X0,X1,sK9(X0,X2,sK7(X0,X1,X3)))
      | k10_yellow_6(X0,X1) = X3
      | r2_hidden(sK7(X0,X1,X3),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | r2_hidden(sK7(X0,X1,X3),k10_yellow_6(X0,X2))
      | ~ l1_waybel_0(X2,X0)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f459,f106])).

fof(f459,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_waybel_0(X0,X1,sK9(X0,X2,sK7(X0,X1,X3)))
      | k10_yellow_6(X0,X1) = X3
      | r2_hidden(sK7(X0,X1,X3),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | r2_hidden(sK7(X0,X1,X3),k10_yellow_6(X0,X2))
      | ~ m1_subset_1(k10_yellow_6(X0,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X2,X0)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f458,f98])).

fof(f458,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_waybel_0(X0,X1,sK9(X0,X2,sK7(X0,X1,X3)))
      | k10_yellow_6(X0,X1) = X3
      | r2_hidden(sK7(X0,X1,X3),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | r2_hidden(sK7(X0,X1,X3),k10_yellow_6(X0,X2))
      | ~ m1_subset_1(sK7(X0,X1,X3),u1_struct_0(X0))
      | ~ m1_subset_1(k10_yellow_6(X0,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X2,X0)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2) ) ),
    inference(duplicate_literal_removal,[],[f455])).

fof(f455,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_waybel_0(X0,X1,sK9(X0,X2,sK7(X0,X1,X3)))
      | k10_yellow_6(X0,X1) = X3
      | r2_hidden(sK7(X0,X1,X3),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | r2_hidden(sK7(X0,X1,X3),k10_yellow_6(X0,X2))
      | ~ m1_subset_1(sK7(X0,X1,X3),u1_struct_0(X0))
      | ~ m1_subset_1(k10_yellow_6(X0,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X2,X0)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f99,f111])).

fof(f111,plain,(
    ! [X6,X0,X1] :
      ( m1_connsp_2(sK9(X0,X1,X6),X0,X6)
      | r2_hidden(X6,k10_yellow_6(X0,X1))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | m1_connsp_2(sK9(X0,X1,X6),X0,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | k10_yellow_6(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f99,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ m1_connsp_2(X5,X0,sK7(X0,X1,X2))
      | r1_waybel_0(X0,X1,X5)
      | k10_yellow_6(X0,X1) = X2
      | r2_hidden(sK7(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_yellow_6(X0,X1)
      | ~ v3_yellow_6(X1,X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:27:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.45  % (15881)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.46  % (15879)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.46  % (15890)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.46  % (15882)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.46  % (15891)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.47  % (15876)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.47  % (15884)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.47  % (15876)Refutation not found, incomplete strategy% (15876)------------------------------
% 0.22/0.47  % (15876)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (15876)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (15876)Memory used [KB]: 10618
% 0.22/0.47  % (15876)Time elapsed: 0.060 s
% 0.22/0.47  % (15876)------------------------------
% 0.22/0.47  % (15876)------------------------------
% 0.22/0.47  % (15875)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.47  % (15875)Refutation not found, incomplete strategy% (15875)------------------------------
% 0.22/0.47  % (15875)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (15875)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (15875)Memory used [KB]: 6140
% 0.22/0.47  % (15875)Time elapsed: 0.065 s
% 0.22/0.47  % (15875)------------------------------
% 0.22/0.47  % (15875)------------------------------
% 0.22/0.47  % (15887)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (15894)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.48  % (15886)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.48  % (15893)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.48  % (15889)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.48  % (15890)Refutation not found, incomplete strategy% (15890)------------------------------
% 0.22/0.48  % (15890)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (15890)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (15890)Memory used [KB]: 6268
% 0.22/0.48  % (15890)Time elapsed: 0.073 s
% 0.22/0.48  % (15890)------------------------------
% 0.22/0.48  % (15890)------------------------------
% 0.22/0.48  % (15892)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.48  % (15878)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.48  % (15880)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.48  % (15877)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.49  % (15888)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.49  % (15885)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.49  % (15883)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.49  % (15885)Refutation not found, incomplete strategy% (15885)------------------------------
% 0.22/0.49  % (15885)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (15885)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (15885)Memory used [KB]: 6268
% 0.22/0.49  % (15885)Time elapsed: 0.050 s
% 0.22/0.49  % (15885)------------------------------
% 0.22/0.49  % (15885)------------------------------
% 0.22/0.49  % (15895)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (15895)Refutation not found, incomplete strategy% (15895)------------------------------
% 0.22/0.50  % (15895)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (15895)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (15895)Memory used [KB]: 10618
% 0.22/0.50  % (15895)Time elapsed: 0.092 s
% 0.22/0.50  % (15895)------------------------------
% 0.22/0.50  % (15895)------------------------------
% 0.22/0.51  % (15893)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f633,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(subsumption_resolution,[],[f632,f69])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    l1_pre_topc(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f49])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ((! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,sK1)) & l1_waybel_0(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1)) | ~v1_compts_1(sK0)) & (! [X3] : ((v3_yellow_6(sK2(X3),sK0) & m2_yellow_6(sK2(X3),sK0,X3)) | ~l1_waybel_0(X3,sK0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f45,f48,f47,f46])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ((? [X1] : (! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,X1)) & l1_waybel_0(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(sK0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,sK0) & m2_yellow_6(X4,sK0,X3)) | ~l1_waybel_0(X3,sK0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    ? [X1] : (! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,X1)) & l1_waybel_0(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,sK1)) & l1_waybel_0(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    ! [X3] : (? [X4] : (v3_yellow_6(X4,sK0) & m2_yellow_6(X4,sK0,X3)) => (v3_yellow_6(sK2(X3),sK0) & m2_yellow_6(sK2(X3),sK0,X3)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.51    inference(rectify,[],[f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f43])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ? [X0] : (((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | v1_compts_1(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,negated_conjecture,(
% 0.22/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)))))),
% 0.22/0.51    inference(negated_conjecture,[],[f15])).
% 0.22/0.51  fof(f15,conjecture,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_yellow19)).
% 0.22/0.51  fof(f632,plain,(
% 0.22/0.51    ~l1_pre_topc(sK0)),
% 0.22/0.51    inference(resolution,[],[f631,f78])).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.51  fof(f631,plain,(
% 0.22/0.51    ~l1_struct_0(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f630,f67])).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    ~v2_struct_0(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f49])).
% 0.22/0.51  fof(f630,plain,(
% 0.22/0.51    ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f629,f68])).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    v2_pre_topc(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f49])).
% 0.22/0.51  fof(f629,plain,(
% 0.22/0.51    ~l1_struct_0(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f628,f69])).
% 0.22/0.51  fof(f628,plain,(
% 0.22/0.51    ~l1_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f627,f351])).
% 0.22/0.51  fof(f351,plain,(
% 0.22/0.51    ~v1_compts_1(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f350,f72])).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    ~v1_compts_1(sK0) | ~v2_struct_0(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f49])).
% 0.22/0.51  fof(f350,plain,(
% 0.22/0.51    ~v1_compts_1(sK0) | v2_struct_0(sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f349,f73])).
% 0.22/0.51  fof(f73,plain,(
% 0.22/0.51    ~v1_compts_1(sK0) | v4_orders_2(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f49])).
% 0.22/0.51  fof(f349,plain,(
% 0.22/0.51    ~v1_compts_1(sK0) | ~v4_orders_2(sK1) | v2_struct_0(sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f348,f74])).
% 0.22/0.51  fof(f74,plain,(
% 0.22/0.51    ~v1_compts_1(sK0) | v7_waybel_0(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f49])).
% 0.22/0.51  fof(f348,plain,(
% 0.22/0.51    ~v1_compts_1(sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f347,f75])).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    l1_waybel_0(sK1,sK0) | ~v1_compts_1(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f49])).
% 0.22/0.51  fof(f347,plain,(
% 0.22/0.51    ~v1_compts_1(sK0) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f346,f67])).
% 0.22/0.51  fof(f346,plain,(
% 0.22/0.51    ~v1_compts_1(sK0) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | v2_struct_0(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f345,f68])).
% 0.22/0.51  fof(f345,plain,(
% 0.22/0.51    ~v1_compts_1(sK0) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f344,f69])).
% 0.22/0.51  fof(f344,plain,(
% 0.22/0.51    ~v1_compts_1(sK0) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f343])).
% 0.22/0.51  fof(f343,plain,(
% 0.22/0.51    ~v1_compts_1(sK0) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.51    inference(resolution,[],[f320,f79])).
% 0.22/0.51  fof(f79,plain,(
% 0.22/0.51    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f51])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((r3_waybel_9(X0,X1,sK3(X0,X1)) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f50])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    ! [X1,X0] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) => (r3_waybel_9(X0,X1,sK3(X0,X1)) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0] : ((! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | ~v1_compts_1(X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l37_yellow19)).
% 0.22/0.51  fof(f320,plain,(
% 0.22/0.51    ~m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) | ~v1_compts_1(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f319,f72])).
% 0.22/0.51  fof(f319,plain,(
% 0.22/0.51    ~m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) | ~v1_compts_1(sK0) | v2_struct_0(sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f318,f73])).
% 0.22/0.51  fof(f318,plain,(
% 0.22/0.51    ~m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) | ~v1_compts_1(sK0) | ~v4_orders_2(sK1) | v2_struct_0(sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f317,f74])).
% 0.22/0.51  fof(f317,plain,(
% 0.22/0.51    ~m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) | ~v1_compts_1(sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f316,f75])).
% 0.22/0.51  fof(f316,plain,(
% 0.22/0.51    ~m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) | ~v1_compts_1(sK0) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f315,f67])).
% 0.22/0.51  fof(f315,plain,(
% 0.22/0.51    ~m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) | ~v1_compts_1(sK0) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | v2_struct_0(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f314,f68])).
% 0.22/0.51  fof(f314,plain,(
% 0.22/0.51    ~m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) | ~v1_compts_1(sK0) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f313,f69])).
% 0.22/0.51  fof(f313,plain,(
% 0.22/0.51    ~m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) | ~v1_compts_1(sK0) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f307])).
% 0.22/0.51  fof(f307,plain,(
% 0.22/0.51    ~m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) | ~v1_compts_1(sK0) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.51    inference(resolution,[],[f306,f80])).
% 0.22/0.51  fof(f80,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r3_waybel_9(X0,X1,sK3(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f51])).
% 0.22/0.51  fof(f306,plain,(
% 0.22/0.51    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v1_compts_1(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f305,f72])).
% 0.22/0.51  fof(f305,plain,(
% 0.22/0.51    ( ! [X0] : (v2_struct_0(sK1) | ~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v1_compts_1(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f304,f73])).
% 0.22/0.51  fof(f304,plain,(
% 0.22/0.51    ( ! [X0] : (~v4_orders_2(sK1) | v2_struct_0(sK1) | ~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v1_compts_1(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f303,f74])).
% 0.22/0.51  fof(f303,plain,(
% 0.22/0.51    ( ! [X0] : (~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v1_compts_1(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f302,f75])).
% 0.22/0.51  fof(f302,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v1_compts_1(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f301,f67])).
% 0.22/0.51  fof(f301,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | v2_struct_0(sK0) | ~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v1_compts_1(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f300,f68])).
% 0.22/0.51  fof(f300,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v1_compts_1(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f299,f69])).
% 0.22/0.51  fof(f299,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v1_compts_1(sK0)) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f298])).
% 0.22/0.51  fof(f298,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X0) | ~v1_compts_1(sK0)) )),
% 0.22/0.51    inference(resolution,[],[f290,f201])).
% 0.22/0.51  fof(f201,plain,(
% 0.22/0.51    ( ! [X0] : (~v3_yellow_6(sK6(sK0,sK1,X0),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X0) | ~v1_compts_1(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f200,f72])).
% 0.22/0.51  fof(f200,plain,(
% 0.22/0.51    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK1) | ~v3_yellow_6(sK6(sK0,sK1,X0),sK0) | ~v1_compts_1(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f199,f73])).
% 0.22/0.51  fof(f199,plain,(
% 0.22/0.51    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v3_yellow_6(sK6(sK0,sK1,X0),sK0) | ~v1_compts_1(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f198,f74])).
% 0.22/0.51  fof(f198,plain,(
% 0.22/0.51    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v3_yellow_6(sK6(sK0,sK1,X0),sK0) | ~v1_compts_1(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f197,f75])).
% 0.22/0.51  fof(f197,plain,(
% 0.22/0.51    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v3_yellow_6(sK6(sK0,sK1,X0),sK0) | ~v1_compts_1(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f196,f67])).
% 0.22/0.51  fof(f196,plain,(
% 0.22/0.51    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | v2_struct_0(sK0) | ~v3_yellow_6(sK6(sK0,sK1,X0),sK0) | ~v1_compts_1(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f195,f68])).
% 0.22/0.51  fof(f195,plain,(
% 0.22/0.51    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~v3_yellow_6(sK6(sK0,sK1,X0),sK0) | ~v1_compts_1(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f186,f69])).
% 0.22/0.51  fof(f186,plain,(
% 0.22/0.51    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~v3_yellow_6(sK6(sK0,sK1,X0),sK0) | ~v1_compts_1(sK0)) )),
% 0.22/0.51    inference(resolution,[],[f92,f76])).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    ( ! [X2] : (~m2_yellow_6(X2,sK0,sK1) | ~v3_yellow_6(X2,sK0) | ~v1_compts_1(sK0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f49])).
% 0.22/0.51  fof(f92,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (m2_yellow_6(sK6(X0,X1,X2),X0,X1) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f59])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k10_yellow_6(X0,sK6(X0,X1,X2))) & m2_yellow_6(sK6(X0,X1,X2),X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f30,f58])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    ! [X2,X1,X0] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) => (r2_hidden(X2,k10_yellow_6(X0,sK6(X0,X1,X2))) & m2_yellow_6(sK6(X0,X1,X2),X0,X1)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : ((? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m2_yellow_6(X3,X0,X1) => ~r2_hidden(X2,k10_yellow_6(X0,X3))) & r3_waybel_9(X0,X1,X2)))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_waybel_9)).
% 0.22/0.51  fof(f290,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (v3_yellow_6(sK6(X0,X1,X2),X0) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f289,f205])).
% 0.22/0.51  fof(f205,plain,(
% 0.22/0.51    ( ! [X12,X10,X11] : (~v2_struct_0(sK6(X10,X11,X12)) | ~m1_subset_1(X12,u1_struct_0(X10)) | ~l1_waybel_0(X11,X10) | ~v7_waybel_0(X11) | ~v4_orders_2(X11) | v2_struct_0(X11) | ~l1_pre_topc(X10) | ~v2_pre_topc(X10) | v2_struct_0(X10) | ~r3_waybel_9(X10,X11,X12)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f191,f78])).
% 0.22/0.51  fof(f191,plain,(
% 0.22/0.51    ( ! [X12,X10,X11] : (~r3_waybel_9(X10,X11,X12) | ~m1_subset_1(X12,u1_struct_0(X10)) | ~l1_waybel_0(X11,X10) | ~v7_waybel_0(X11) | ~v4_orders_2(X11) | v2_struct_0(X11) | ~l1_pre_topc(X10) | ~v2_pre_topc(X10) | v2_struct_0(X10) | ~v2_struct_0(sK6(X10,X11,X12)) | ~l1_struct_0(X10)) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f190])).
% 0.22/0.51  fof(f190,plain,(
% 0.22/0.51    ( ! [X12,X10,X11] : (~r3_waybel_9(X10,X11,X12) | ~m1_subset_1(X12,u1_struct_0(X10)) | ~l1_waybel_0(X11,X10) | ~v7_waybel_0(X11) | ~v4_orders_2(X11) | v2_struct_0(X11) | ~l1_pre_topc(X10) | ~v2_pre_topc(X10) | v2_struct_0(X10) | ~v2_struct_0(sK6(X10,X11,X12)) | ~l1_waybel_0(X11,X10) | ~v7_waybel_0(X11) | ~v4_orders_2(X11) | v2_struct_0(X11) | ~l1_struct_0(X10) | v2_struct_0(X10)) )),
% 0.22/0.51    inference(resolution,[],[f92,f102])).
% 0.22/0.51  fof(f102,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m2_yellow_6(X2,X0,X1) | ~v2_struct_0(X2) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_yellow_6)).
% 0.22/0.51  fof(f289,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~r3_waybel_9(X0,X1,X2) | v3_yellow_6(sK6(X0,X1,X2),X0) | v2_struct_0(sK6(X0,X1,X2))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f288,f204])).
% 0.22/0.51  fof(f204,plain,(
% 0.22/0.51    ( ! [X8,X7,X9] : (v4_orders_2(sK6(X7,X8,X9)) | ~m1_subset_1(X9,u1_struct_0(X7)) | ~l1_waybel_0(X8,X7) | ~v7_waybel_0(X8) | ~v4_orders_2(X8) | v2_struct_0(X8) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7) | ~r3_waybel_9(X7,X8,X9)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f192,f78])).
% 0.22/0.51  fof(f192,plain,(
% 0.22/0.51    ( ! [X8,X7,X9] : (~r3_waybel_9(X7,X8,X9) | ~m1_subset_1(X9,u1_struct_0(X7)) | ~l1_waybel_0(X8,X7) | ~v7_waybel_0(X8) | ~v4_orders_2(X8) | v2_struct_0(X8) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7) | v4_orders_2(sK6(X7,X8,X9)) | ~l1_struct_0(X7)) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f189])).
% 0.22/0.51  fof(f189,plain,(
% 0.22/0.51    ( ! [X8,X7,X9] : (~r3_waybel_9(X7,X8,X9) | ~m1_subset_1(X9,u1_struct_0(X7)) | ~l1_waybel_0(X8,X7) | ~v7_waybel_0(X8) | ~v4_orders_2(X8) | v2_struct_0(X8) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7) | v4_orders_2(sK6(X7,X8,X9)) | ~l1_waybel_0(X8,X7) | ~v7_waybel_0(X8) | ~v4_orders_2(X8) | v2_struct_0(X8) | ~l1_struct_0(X7) | v2_struct_0(X7)) )),
% 0.22/0.51    inference(resolution,[],[f92,f103])).
% 0.22/0.51  fof(f103,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m2_yellow_6(X2,X0,X1) | v4_orders_2(X2) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f36])).
% 0.22/0.51  fof(f288,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~r3_waybel_9(X0,X1,X2) | v3_yellow_6(sK6(X0,X1,X2),X0) | ~v4_orders_2(sK6(X0,X1,X2)) | v2_struct_0(sK6(X0,X1,X2))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f287,f203])).
% 0.22/0.51  fof(f203,plain,(
% 0.22/0.51    ( ! [X6,X4,X5] : (v7_waybel_0(sK6(X4,X5,X6)) | ~m1_subset_1(X6,u1_struct_0(X4)) | ~l1_waybel_0(X5,X4) | ~v7_waybel_0(X5) | ~v4_orders_2(X5) | v2_struct_0(X5) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4) | ~r3_waybel_9(X4,X5,X6)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f193,f78])).
% 0.22/0.51  fof(f193,plain,(
% 0.22/0.51    ( ! [X6,X4,X5] : (~r3_waybel_9(X4,X5,X6) | ~m1_subset_1(X6,u1_struct_0(X4)) | ~l1_waybel_0(X5,X4) | ~v7_waybel_0(X5) | ~v4_orders_2(X5) | v2_struct_0(X5) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4) | v7_waybel_0(sK6(X4,X5,X6)) | ~l1_struct_0(X4)) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f188])).
% 0.22/0.52  fof(f188,plain,(
% 0.22/0.52    ( ! [X6,X4,X5] : (~r3_waybel_9(X4,X5,X6) | ~m1_subset_1(X6,u1_struct_0(X4)) | ~l1_waybel_0(X5,X4) | ~v7_waybel_0(X5) | ~v4_orders_2(X5) | v2_struct_0(X5) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4) | v7_waybel_0(sK6(X4,X5,X6)) | ~l1_waybel_0(X5,X4) | ~v7_waybel_0(X5) | ~v4_orders_2(X5) | v2_struct_0(X5) | ~l1_struct_0(X4) | v2_struct_0(X4)) )),
% 0.22/0.52    inference(resolution,[],[f92,f104])).
% 0.22/0.52  fof(f104,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m2_yellow_6(X2,X0,X1) | v7_waybel_0(X2) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f36])).
% 0.22/0.52  fof(f287,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~r3_waybel_9(X0,X1,X2) | v3_yellow_6(sK6(X0,X1,X2),X0) | ~v7_waybel_0(sK6(X0,X1,X2)) | ~v4_orders_2(sK6(X0,X1,X2)) | v2_struct_0(sK6(X0,X1,X2))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f286,f202])).
% 0.22/0.52  fof(f202,plain,(
% 0.22/0.52    ( ! [X2,X3,X1] : (l1_waybel_0(sK6(X1,X2,X3),X1) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l1_waybel_0(X2,X1) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~r3_waybel_9(X1,X2,X3)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f194,f78])).
% 0.22/0.52  fof(f194,plain,(
% 0.22/0.52    ( ! [X2,X3,X1] : (~r3_waybel_9(X1,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l1_waybel_0(X2,X1) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | l1_waybel_0(sK6(X1,X2,X3),X1) | ~l1_struct_0(X1)) )),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f187])).
% 0.22/0.52  fof(f187,plain,(
% 0.22/0.52    ( ! [X2,X3,X1] : (~r3_waybel_9(X1,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l1_waybel_0(X2,X1) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | l1_waybel_0(sK6(X1,X2,X3),X1) | ~l1_waybel_0(X2,X1) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 0.22/0.52    inference(resolution,[],[f92,f105])).
% 0.22/0.52  fof(f105,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m2_yellow_6(X2,X0,X1) | l1_waybel_0(X2,X0) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f36])).
% 0.22/0.52  fof(f286,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~r3_waybel_9(X0,X1,X2) | v3_yellow_6(sK6(X0,X1,X2),X0) | ~l1_waybel_0(sK6(X0,X1,X2),X0) | ~v7_waybel_0(sK6(X0,X1,X2)) | ~v4_orders_2(sK6(X0,X1,X2)) | v2_struct_0(sK6(X0,X1,X2))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f280,f114])).
% 0.22/0.52  fof(f114,plain,(
% 0.22/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.52    inference(resolution,[],[f107,f77])).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.53  fof(f107,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f39])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.22/0.53    inference(unused_predicate_definition_removal,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.53  fof(f280,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r1_tarski(k1_xboole_0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~r3_waybel_9(X0,X1,X2) | v3_yellow_6(sK6(X0,X1,X2),X0) | ~l1_waybel_0(sK6(X0,X1,X2),X0) | ~v7_waybel_0(sK6(X0,X1,X2)) | ~v4_orders_2(sK6(X0,X1,X2)) | v2_struct_0(sK6(X0,X1,X2))) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f279])).
% 0.22/0.53  fof(f279,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r1_tarski(k1_xboole_0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~r3_waybel_9(X0,X1,X2) | v3_yellow_6(sK6(X0,X1,X2),X0) | ~l1_waybel_0(sK6(X0,X1,X2),X0) | ~v7_waybel_0(sK6(X0,X1,X2)) | ~v4_orders_2(sK6(X0,X1,X2)) | v2_struct_0(sK6(X0,X1,X2)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(superposition,[],[f208,f90])).
% 0.22/0.53  fof(f90,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_xboole_0 = k10_yellow_6(X0,X1) | v3_yellow_6(X1,X0) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f57])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (((v3_yellow_6(X1,X0) | k1_xboole_0 = k10_yellow_6(X0,X1)) & (k1_xboole_0 != k10_yellow_6(X0,X1) | ~v3_yellow_6(X1,X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_yellow_6)).
% 0.22/0.53  fof(f208,plain,(
% 0.22/0.53    ( ! [X6,X8,X7] : (~r1_tarski(k10_yellow_6(X6,sK6(X6,X7,X8)),X8) | ~m1_subset_1(X8,u1_struct_0(X6)) | ~l1_waybel_0(X7,X6) | ~v7_waybel_0(X7) | ~v4_orders_2(X7) | v2_struct_0(X7) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6) | ~r3_waybel_9(X6,X7,X8)) )),
% 0.22/0.53    inference(resolution,[],[f93,f108])).
% 0.22/0.53  fof(f108,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,sK6(X0,X1,X2))) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f59])).
% 0.22/0.53  fof(f627,plain,(
% 0.22/0.53    ~l1_struct_0(sK0) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.53    inference(resolution,[],[f626,f83])).
% 0.22/0.53  fof(f83,plain,(
% 0.22/0.53    ( ! [X0] : (~v2_struct_0(sK4(X0)) | v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f56])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    ! [X0] : (((v1_compts_1(X0) | (! [X2] : (~r3_waybel_9(X0,sK4(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(sK4(X0),k6_yellow_6(X0)) & l1_waybel_0(sK4(X0),X0) & v7_waybel_0(sK4(X0)) & v4_orders_2(sK4(X0)) & ~v2_struct_0(sK4(X0)))) & (! [X3] : ((r3_waybel_9(X0,X3,sK5(X0,X3)) & m1_subset_1(sK5(X0,X3),u1_struct_0(X0))) | ~r2_hidden(X3,k6_yellow_6(X0)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f53,f55,f54])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    ! [X0] : (? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(X1,k6_yellow_6(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (~r3_waybel_9(X0,sK4(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(sK4(X0),k6_yellow_6(X0)) & l1_waybel_0(sK4(X0),X0) & v7_waybel_0(sK4(X0)) & v4_orders_2(sK4(X0)) & ~v2_struct_0(sK4(X0))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ! [X3,X0] : (? [X4] : (r3_waybel_9(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (r3_waybel_9(X0,X3,sK5(X0,X3)) & m1_subset_1(sK5(X0,X3),u1_struct_0(X0))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    ! [X0] : (((v1_compts_1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(X1,k6_yellow_6(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (! [X3] : (? [X4] : (r3_waybel_9(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r2_hidden(X3,k6_yellow_6(X0)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(rectify,[],[f52])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ! [X0] : (((v1_compts_1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(X1,k6_yellow_6(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~r2_hidden(X1,k6_yellow_6(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~r2_hidden(X1,k6_yellow_6(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : ((? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~r2_hidden(X1,k6_yellow_6(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,axiom,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ~(! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~r3_waybel_9(X0,X1,X2)) & r2_hidden(X1,k6_yellow_6(X0))))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_yellow19)).
% 0.22/0.53  fof(f626,plain,(
% 0.22/0.53    v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f625,f67])).
% 0.22/0.53  fof(f625,plain,(
% 0.22/0.53    v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f624,f68])).
% 0.22/0.53  fof(f624,plain,(
% 0.22/0.53    v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f623,f69])).
% 0.22/0.53  fof(f623,plain,(
% 0.22/0.53    v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f622,f351])).
% 0.22/0.53  fof(f622,plain,(
% 0.22/0.53    v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.53    inference(resolution,[],[f621,f84])).
% 0.22/0.53  fof(f84,plain,(
% 0.22/0.53    ( ! [X0] : (v4_orders_2(sK4(X0)) | v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f56])).
% 0.22/0.53  fof(f621,plain,(
% 0.22/0.53    ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f620,f67])).
% 0.22/0.53  fof(f620,plain,(
% 0.22/0.53    ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f619,f68])).
% 0.22/0.53  fof(f619,plain,(
% 0.22/0.53    ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f618,f69])).
% 0.22/0.53  fof(f618,plain,(
% 0.22/0.53    ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f617,f351])).
% 0.22/0.53  fof(f617,plain,(
% 0.22/0.53    ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.53    inference(resolution,[],[f616,f85])).
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    ( ! [X0] : (v7_waybel_0(sK4(X0)) | v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f56])).
% 0.22/0.53  fof(f616,plain,(
% 0.22/0.53    ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f615,f351])).
% 0.22/0.53  fof(f615,plain,(
% 0.22/0.53    ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0)),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f614])).
% 0.22/0.53  fof(f614,plain,(
% 0.22/0.53    ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0)),
% 0.22/0.53    inference(resolution,[],[f613,f125])).
% 0.22/0.53  fof(f125,plain,(
% 0.22/0.53    ~v2_struct_0(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f124,f67])).
% 0.22/0.53  fof(f124,plain,(
% 0.22/0.53    ~v2_struct_0(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | v2_struct_0(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f123,f68])).
% 0.22/0.53  fof(f123,plain,(
% 0.22/0.53    ~v2_struct_0(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f122,f69])).
% 0.22/0.53  fof(f122,plain,(
% 0.22/0.53    ~v2_struct_0(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f121])).
% 0.22/0.53  fof(f121,plain,(
% 0.22/0.53    ~v2_struct_0(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.53    inference(resolution,[],[f119,f86])).
% 0.22/0.53  fof(f86,plain,(
% 0.22/0.53    ( ! [X0] : (l1_waybel_0(sK4(X0),X0) | v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f56])).
% 0.22/0.53  fof(f119,plain,(
% 0.22/0.53    ( ! [X0] : (~l1_waybel_0(X0,sK0) | ~v2_struct_0(sK2(X0)) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v1_compts_1(sK0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f118,f67])).
% 0.22/0.53  fof(f118,plain,(
% 0.22/0.53    ( ! [X0] : (~v2_struct_0(sK2(X0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | v1_compts_1(sK0)) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f117])).
% 0.22/0.53  fof(f117,plain,(
% 0.22/0.53    ( ! [X0] : (~v2_struct_0(sK2(X0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | v1_compts_1(sK0)) )),
% 0.22/0.53    inference(resolution,[],[f102,f70])).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    ( ! [X3] : (m2_yellow_6(sK2(X3),sK0,X3) | ~l1_waybel_0(X3,sK0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | v1_compts_1(sK0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f49])).
% 0.22/0.53  fof(f613,plain,(
% 0.22/0.53    v2_struct_0(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f612,f351])).
% 0.22/0.53  fof(f612,plain,(
% 0.22/0.53    v2_struct_0(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0)),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f611])).
% 0.22/0.53  fof(f611,plain,(
% 0.22/0.53    v2_struct_0(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0)),
% 0.22/0.53    inference(resolution,[],[f606,f134])).
% 0.22/0.53  fof(f134,plain,(
% 0.22/0.53    v4_orders_2(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f133,f67])).
% 0.22/0.53  fof(f133,plain,(
% 0.22/0.53    v4_orders_2(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | v2_struct_0(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f132,f68])).
% 0.22/0.53  fof(f132,plain,(
% 0.22/0.53    v4_orders_2(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f131,f69])).
% 0.22/0.53  fof(f131,plain,(
% 0.22/0.53    v4_orders_2(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f130])).
% 0.22/0.53  fof(f130,plain,(
% 0.22/0.53    v4_orders_2(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.53    inference(resolution,[],[f128,f86])).
% 0.22/0.53  fof(f128,plain,(
% 0.22/0.53    ( ! [X0] : (~l1_waybel_0(X0,sK0) | v4_orders_2(sK2(X0)) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v1_compts_1(sK0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f127,f67])).
% 0.22/0.53  fof(f127,plain,(
% 0.22/0.53    ( ! [X0] : (v4_orders_2(sK2(X0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | v1_compts_1(sK0)) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f126])).
% 0.22/0.53  fof(f126,plain,(
% 0.22/0.53    ( ! [X0] : (v4_orders_2(sK2(X0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | v1_compts_1(sK0)) )),
% 0.22/0.53    inference(resolution,[],[f103,f70])).
% 0.22/0.53  fof(f606,plain,(
% 0.22/0.53    ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f605,f351])).
% 0.22/0.53  fof(f605,plain,(
% 0.22/0.53    v2_struct_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0)),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f604])).
% 0.22/0.53  fof(f604,plain,(
% 0.22/0.53    v2_struct_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0)),
% 0.22/0.53    inference(resolution,[],[f603,f143])).
% 0.22/0.53  fof(f143,plain,(
% 0.22/0.53    v7_waybel_0(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f142,f67])).
% 0.22/0.53  fof(f142,plain,(
% 0.22/0.53    v7_waybel_0(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | v2_struct_0(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f141,f68])).
% 0.22/0.53  fof(f141,plain,(
% 0.22/0.53    v7_waybel_0(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f140,f69])).
% 0.22/0.53  fof(f140,plain,(
% 0.22/0.53    v7_waybel_0(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f139])).
% 0.22/0.53  fof(f139,plain,(
% 0.22/0.53    v7_waybel_0(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.53    inference(resolution,[],[f137,f86])).
% 0.22/0.53  fof(f137,plain,(
% 0.22/0.53    ( ! [X0] : (~l1_waybel_0(X0,sK0) | v7_waybel_0(sK2(X0)) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v1_compts_1(sK0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f136,f67])).
% 0.22/0.53  fof(f136,plain,(
% 0.22/0.53    ( ! [X0] : (v7_waybel_0(sK2(X0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | v1_compts_1(sK0)) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f135])).
% 0.22/0.53  fof(f135,plain,(
% 0.22/0.53    ( ! [X0] : (v7_waybel_0(sK2(X0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | v1_compts_1(sK0)) )),
% 0.22/0.53    inference(resolution,[],[f104,f70])).
% 0.22/0.53  fof(f603,plain,(
% 0.22/0.53    ~v7_waybel_0(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f602,f67])).
% 0.22/0.53  fof(f602,plain,(
% 0.22/0.53    ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | ~v7_waybel_0(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f601,f68])).
% 0.22/0.53  fof(f601,plain,(
% 0.22/0.53    ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | ~v7_waybel_0(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f600,f69])).
% 0.22/0.53  fof(f600,plain,(
% 0.22/0.53    ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | ~v7_waybel_0(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f599,f351])).
% 0.22/0.53  fof(f599,plain,(
% 0.22/0.53    ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | ~v7_waybel_0(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.53    inference(resolution,[],[f598,f86])).
% 0.22/0.53  fof(f598,plain,(
% 0.22/0.53    ~l1_waybel_0(sK4(sK0),sK0) | ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | ~v7_waybel_0(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f597,f351])).
% 0.22/0.53  fof(f597,plain,(
% 0.22/0.53    ~v7_waybel_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0)),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f596])).
% 0.22/0.53  fof(f596,plain,(
% 0.22/0.53    ~v7_waybel_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0)),
% 0.22/0.53    inference(resolution,[],[f595,f146])).
% 0.22/0.53  fof(f146,plain,(
% 0.22/0.53    ( ! [X0] : (l1_waybel_0(sK2(X0),sK0) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v1_compts_1(sK0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f145,f67])).
% 0.22/0.53  fof(f145,plain,(
% 0.22/0.53    ( ! [X0] : (l1_waybel_0(sK2(X0),sK0) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | v1_compts_1(sK0)) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f144])).
% 0.22/0.53  fof(f144,plain,(
% 0.22/0.53    ( ! [X0] : (l1_waybel_0(sK2(X0),sK0) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | v1_compts_1(sK0)) )),
% 0.22/0.53    inference(resolution,[],[f105,f70])).
% 0.22/0.53  fof(f595,plain,(
% 0.22/0.53    ~l1_waybel_0(sK2(sK4(sK0)),sK0) | ~v7_waybel_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0))),
% 0.22/0.53    inference(subsumption_resolution,[],[f594,f351])).
% 0.22/0.53  fof(f594,plain,(
% 0.22/0.53    ~l1_waybel_0(sK2(sK4(sK0)),sK0) | ~v7_waybel_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | v1_compts_1(sK0)),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f593])).
% 0.22/0.53  fof(f593,plain,(
% 0.22/0.53    ~l1_waybel_0(sK2(sK4(sK0)),sK0) | ~v7_waybel_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | v1_compts_1(sK0)),
% 0.22/0.53    inference(resolution,[],[f580,f71])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    ( ! [X3] : (v3_yellow_6(sK2(X3),sK0) | ~l1_waybel_0(X3,sK0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | v1_compts_1(sK0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f49])).
% 0.22/0.53  fof(f580,plain,(
% 0.22/0.53    ~v3_yellow_6(sK2(sK4(sK0)),sK0) | ~l1_waybel_0(sK2(sK4(sK0)),sK0) | ~v7_waybel_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0))),
% 0.22/0.53    inference(subsumption_resolution,[],[f579,f67])).
% 0.22/0.53  fof(f579,plain,(
% 0.22/0.53    ~v3_yellow_6(sK2(sK4(sK0)),sK0) | ~l1_waybel_0(sK2(sK4(sK0)),sK0) | ~v7_waybel_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | v2_struct_0(sK0) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0))),
% 0.22/0.53    inference(subsumption_resolution,[],[f578,f68])).
% 0.22/0.53  fof(f578,plain,(
% 0.22/0.53    ~v3_yellow_6(sK2(sK4(sK0)),sK0) | ~l1_waybel_0(sK2(sK4(sK0)),sK0) | ~v7_waybel_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0))),
% 0.22/0.53    inference(subsumption_resolution,[],[f577,f69])).
% 0.22/0.53  fof(f577,plain,(
% 0.22/0.53    ~v3_yellow_6(sK2(sK4(sK0)),sK0) | ~l1_waybel_0(sK2(sK4(sK0)),sK0) | ~v7_waybel_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0))),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f576])).
% 0.22/0.53  fof(f576,plain,(
% 0.22/0.53    k1_xboole_0 != k1_xboole_0 | ~v3_yellow_6(sK2(sK4(sK0)),sK0) | ~l1_waybel_0(sK2(sK4(sK0)),sK0) | ~v7_waybel_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0))),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f557])).
% 0.22/0.53  fof(f557,plain,(
% 0.22/0.53    k1_xboole_0 != k1_xboole_0 | ~v3_yellow_6(sK2(sK4(sK0)),sK0) | ~l1_waybel_0(sK2(sK4(sK0)),sK0) | ~v7_waybel_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | v2_struct_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | ~l1_waybel_0(sK2(sK4(sK0)),sK0) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~v7_waybel_0(sK2(sK4(sK0)))),
% 0.22/0.53    inference(superposition,[],[f89,f556])).
% 0.22/0.53  fof(f556,plain,(
% 0.22/0.53    k1_xboole_0 = k10_yellow_6(sK0,sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | ~l1_waybel_0(sK2(sK4(sK0)),sK0) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~v7_waybel_0(sK2(sK4(sK0)))),
% 0.22/0.53    inference(subsumption_resolution,[],[f553,f77])).
% 0.22/0.53  fof(f553,plain,(
% 0.22/0.53    ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | k1_xboole_0 = k10_yellow_6(sK0,sK2(sK4(sK0))) | ~l1_waybel_0(sK2(sK4(sK0)),sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~v7_waybel_0(sK2(sK4(sK0)))),
% 0.22/0.53    inference(resolution,[],[f536,f114])).
% 0.22/0.53  fof(f536,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_tarski(X0,sK7(sK0,sK2(sK4(sK0)),X0)) | ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | k10_yellow_6(sK0,sK2(sK4(sK0))) = X0 | ~l1_waybel_0(sK2(sK4(sK0)),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~v7_waybel_0(sK2(sK4(sK0)))) )),
% 0.22/0.53    inference(resolution,[],[f534,f108])).
% 0.22/0.53  fof(f534,plain,(
% 0.22/0.53    ( ! [X0] : (r2_hidden(sK7(sK0,sK2(sK4(sK0)),X0),X0) | ~v7_waybel_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | k10_yellow_6(sK0,sK2(sK4(sK0))) = X0 | ~l1_waybel_0(sK2(sK4(sK0)),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f533,f67])).
% 0.22/0.53  fof(f533,plain,(
% 0.22/0.53    ( ! [X0] : (~l1_waybel_0(sK2(sK4(sK0)),sK0) | ~v7_waybel_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | k10_yellow_6(sK0,sK2(sK4(sK0))) = X0 | r2_hidden(sK7(sK0,sK2(sK4(sK0)),X0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | v2_struct_0(sK0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f532,f68])).
% 0.22/0.53  fof(f532,plain,(
% 0.22/0.53    ( ! [X0] : (~l1_waybel_0(sK2(sK4(sK0)),sK0) | ~v7_waybel_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | k10_yellow_6(sK0,sK2(sK4(sK0))) = X0 | r2_hidden(sK7(sK0,sK2(sK4(sK0)),X0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f531,f69])).
% 0.22/0.53  fof(f531,plain,(
% 0.22/0.53    ( ! [X0] : (~l1_waybel_0(sK2(sK4(sK0)),sK0) | ~v7_waybel_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | k10_yellow_6(sK0,sK2(sK4(sK0))) = X0 | r2_hidden(sK7(sK0,sK2(sK4(sK0)),X0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f530])).
% 0.22/0.53  fof(f530,plain,(
% 0.22/0.53    ( ! [X0] : (~l1_waybel_0(sK2(sK4(sK0)),sK0) | ~v7_waybel_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | k10_yellow_6(sK0,sK2(sK4(sK0))) = X0 | r2_hidden(sK7(sK0,sK2(sK4(sK0)),X0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | k10_yellow_6(sK0,sK2(sK4(sK0))) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK2(sK4(sK0)),sK0) | ~v7_waybel_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.53    inference(resolution,[],[f515,f98])).
% 0.22/0.53  fof(f98,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) | k10_yellow_6(X0,X1) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f66])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | (((~r1_waybel_0(X0,X1,sK8(X0,X1,X2)) & m1_connsp_2(sK8(X0,X1,X2),X0,sK7(X0,X1,X2))) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK7(X0,X1,X2))) | r2_hidden(sK7(X0,X1,X2),X2)) & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)))) & (! [X6] : (((r2_hidden(X6,X2) | (~r1_waybel_0(X0,X1,sK9(X0,X1,X6)) & m1_connsp_2(sK9(X0,X1,X6),X0,X6))) & (! [X8] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6)) | ~r2_hidden(X6,X2))) | ~m1_subset_1(X6,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f62,f65,f64,f63])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    ! [X2,X1,X0] : (? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0))) => ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,sK7(X0,X1,X2))) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK7(X0,X1,X2))) | r2_hidden(sK7(X0,X1,X2),X2)) & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    ! [X2,X1,X0] : (? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,sK7(X0,X1,X2))) => (~r1_waybel_0(X0,X1,sK8(X0,X1,X2)) & m1_connsp_2(sK8(X0,X1,X2),X0,sK7(X0,X1,X2))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    ! [X6,X1,X0] : (? [X7] : (~r1_waybel_0(X0,X1,X7) & m1_connsp_2(X7,X0,X6)) => (~r1_waybel_0(X0,X1,sK9(X0,X1,X6)) & m1_connsp_2(sK9(X0,X1,X6),X0,X6)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X6] : (((r2_hidden(X6,X2) | ? [X7] : (~r1_waybel_0(X0,X1,X7) & m1_connsp_2(X7,X0,X6))) & (! [X8] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6)) | ~r2_hidden(X6,X2))) | ~m1_subset_1(X6,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(rectify,[],[f61])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3))) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f60])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : (((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | r2_hidden(X3,X2))) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3))) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (k10_yellow_6(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) <=> ! [X4] : (m1_connsp_2(X4,X0,X3) => r1_waybel_0(X0,X1,X4))))))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_yellow_6)).
% 0.22/0.53  fof(f515,plain,(
% 0.22/0.53    ( ! [X2] : (~m1_subset_1(sK7(sK0,sK2(sK4(sK0)),X2),u1_struct_0(sK0)) | ~l1_waybel_0(sK2(sK4(sK0)),sK0) | ~v7_waybel_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | k10_yellow_6(sK0,sK2(sK4(sK0))) = X2 | r2_hidden(sK7(sK0,sK2(sK4(sK0)),X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f514,f351])).
% 0.22/0.53  fof(f514,plain,(
% 0.22/0.53    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK2(sK4(sK0)),sK0) | ~v7_waybel_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | k10_yellow_6(sK0,sK2(sK4(sK0))) = X2 | r2_hidden(sK7(sK0,sK2(sK4(sK0)),X2),X2) | ~m1_subset_1(sK7(sK0,sK2(sK4(sK0)),X2),u1_struct_0(sK0)) | v1_compts_1(sK0) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f513,f67])).
% 0.22/0.53  fof(f513,plain,(
% 0.22/0.53    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK2(sK4(sK0)),sK0) | ~v7_waybel_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | v2_struct_0(sK0) | k10_yellow_6(sK0,sK2(sK4(sK0))) = X2 | r2_hidden(sK7(sK0,sK2(sK4(sK0)),X2),X2) | ~m1_subset_1(sK7(sK0,sK2(sK4(sK0)),X2),u1_struct_0(sK0)) | v1_compts_1(sK0) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f512,f68])).
% 0.22/0.53  fof(f512,plain,(
% 0.22/0.53    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK2(sK4(sK0)),sK0) | ~v7_waybel_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | k10_yellow_6(sK0,sK2(sK4(sK0))) = X2 | r2_hidden(sK7(sK0,sK2(sK4(sK0)),X2),X2) | ~m1_subset_1(sK7(sK0,sK2(sK4(sK0)),X2),u1_struct_0(sK0)) | v1_compts_1(sK0) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f500,f69])).
% 0.22/0.53  fof(f500,plain,(
% 0.22/0.53    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK2(sK4(sK0)),sK0) | ~v7_waybel_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | k10_yellow_6(sK0,sK2(sK4(sK0))) = X2 | r2_hidden(sK7(sK0,sK2(sK4(sK0)),X2),X2) | ~m1_subset_1(sK7(sK0,sK2(sK4(sK0)),X2),u1_struct_0(sK0)) | v1_compts_1(sK0) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0))) )),
% 0.22/0.53    inference(resolution,[],[f484,f245])).
% 0.22/0.53  fof(f245,plain,(
% 0.22/0.53    ( ! [X0] : (~r3_waybel_9(sK0,sK2(sK4(sK0)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v1_compts_1(sK0) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f244,f67])).
% 0.22/0.53  fof(f244,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK2(sK4(sK0)),X0) | v2_struct_0(sK0) | v1_compts_1(sK0) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f243,f68])).
% 0.22/0.53  fof(f243,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK2(sK4(sK0)),X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | v1_compts_1(sK0) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f242,f69])).
% 0.22/0.53  fof(f242,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK2(sK4(sK0)),X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | v1_compts_1(sK0) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0))) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f239])).
% 0.22/0.53  fof(f239,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK2(sK4(sK0)),X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | v1_compts_1(sK0) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | v1_compts_1(sK0)) )),
% 0.22/0.53    inference(resolution,[],[f238,f70])).
% 0.22/0.53  fof(f238,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m2_yellow_6(X1,X0,sK4(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v1_compts_1(X0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f237,f83])).
% 0.22/0.53  fof(f237,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m2_yellow_6(X1,X0,sK4(X0)) | v2_struct_0(sK4(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v1_compts_1(X0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f236,f84])).
% 0.22/0.53  fof(f236,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m2_yellow_6(X1,X0,sK4(X0)) | ~v4_orders_2(sK4(X0)) | v2_struct_0(sK4(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v1_compts_1(X0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f235,f85])).
% 0.22/0.53  fof(f235,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m2_yellow_6(X1,X0,sK4(X0)) | ~v7_waybel_0(sK4(X0)) | ~v4_orders_2(sK4(X0)) | v2_struct_0(sK4(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v1_compts_1(X0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f234,f86])).
% 0.22/0.53  fof(f234,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m2_yellow_6(X1,X0,sK4(X0)) | ~l1_waybel_0(sK4(X0),X0) | ~v7_waybel_0(sK4(X0)) | ~v4_orders_2(sK4(X0)) | v2_struct_0(sK4(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v1_compts_1(X0)) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f233])).
% 0.22/0.53  fof(f233,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m2_yellow_6(X1,X0,sK4(X0)) | ~l1_waybel_0(sK4(X0),X0) | ~v7_waybel_0(sK4(X0)) | ~v4_orders_2(sK4(X0)) | v2_struct_0(sK4(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v1_compts_1(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(resolution,[],[f94,f88])).
% 0.22/0.53  fof(f88,plain,(
% 0.22/0.53    ( ! [X2,X0] : (~r3_waybel_9(X0,sK4(X0),X2) | v1_compts_1(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f56])).
% 0.22/0.53  fof(f94,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,axiom,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_waybel_9(X0,X2,X3) => r3_waybel_9(X0,X1,X3))))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_waybel_9)).
% 0.22/0.53  fof(f484,plain,(
% 0.22/0.53    ( ! [X6,X4,X5] : (r3_waybel_9(X4,X5,sK7(X4,X5,X6)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4))) | ~l1_waybel_0(X5,X4) | ~v7_waybel_0(X5) | ~v4_orders_2(X5) | v2_struct_0(X5) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4) | k10_yellow_6(X4,X5) = X6 | r2_hidden(sK7(X4,X5,X6),X6)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f482,f98])).
% 0.22/0.53  fof(f482,plain,(
% 0.22/0.53    ( ! [X6,X4,X5] : (r2_hidden(sK7(X4,X5,X6),X6) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4))) | ~l1_waybel_0(X5,X4) | ~v7_waybel_0(X5) | ~v4_orders_2(X5) | v2_struct_0(X5) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4) | k10_yellow_6(X4,X5) = X6 | r3_waybel_9(X4,X5,sK7(X4,X5,X6)) | ~m1_subset_1(sK7(X4,X5,X6),u1_struct_0(X4))) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f475])).
% 0.22/0.53  fof(f475,plain,(
% 0.22/0.53    ( ! [X6,X4,X5] : (r2_hidden(sK7(X4,X5,X6),X6) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4))) | ~l1_waybel_0(X5,X4) | ~v7_waybel_0(X5) | ~v4_orders_2(X5) | v2_struct_0(X5) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4) | k10_yellow_6(X4,X5) = X6 | r3_waybel_9(X4,X5,sK7(X4,X5,X6)) | ~m1_subset_1(sK7(X4,X5,X6),u1_struct_0(X4)) | ~l1_waybel_0(X5,X4) | ~v7_waybel_0(X5) | ~v4_orders_2(X5) | v2_struct_0(X5) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) )),
% 0.22/0.53    inference(resolution,[],[f473,f91])).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,k10_yellow_6(X0,X1)) | r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,X1)) => r3_waybel_9(X0,X1,X2)))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_waybel_9)).
% 0.22/0.53  fof(f473,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (r2_hidden(sK7(X0,X1,X2),k10_yellow_6(X0,X1)) | r2_hidden(sK7(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | k10_yellow_6(X0,X1) = X2) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f472,f106])).
% 0.22/0.53  fof(f106,plain,(
% 0.22/0.53    ( ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f38])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_yellow_6)).
% 0.22/0.53  fof(f472,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k10_yellow_6(X0,X1) = X2 | r2_hidden(sK7(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | r2_hidden(sK7(X0,X1,X2),k10_yellow_6(X0,X1)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f471,f98])).
% 0.22/0.53  fof(f471,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k10_yellow_6(X0,X1) = X2 | r2_hidden(sK7(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | r2_hidden(sK7(X0,X1,X2),k10_yellow_6(X0,X1)) | ~m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f470])).
% 0.22/0.53  fof(f470,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k10_yellow_6(X0,X1) = X2 | r2_hidden(sK7(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | r2_hidden(sK7(X0,X1,X2),k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | r2_hidden(sK7(X0,X1,X2),k10_yellow_6(X0,X1)) | ~m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(resolution,[],[f460,f110])).
% 0.22/0.53  fof(f110,plain,(
% 0.22/0.53    ( ! [X6,X0,X1] : (~r1_waybel_0(X0,X1,sK9(X0,X1,X6)) | r2_hidden(X6,k10_yellow_6(X0,X1)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(equality_resolution,[],[f97])).
% 0.22/0.53  fof(f97,plain,(
% 0.22/0.53    ( ! [X6,X2,X0,X1] : (r2_hidden(X6,X2) | ~r1_waybel_0(X0,X1,sK9(X0,X1,X6)) | ~m1_subset_1(X6,u1_struct_0(X0)) | k10_yellow_6(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f66])).
% 0.22/0.53  fof(f460,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (r1_waybel_0(X0,X1,sK9(X0,X2,sK7(X0,X1,X3))) | k10_yellow_6(X0,X1) = X3 | r2_hidden(sK7(X0,X1,X3),X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | r2_hidden(sK7(X0,X1,X3),k10_yellow_6(X0,X2)) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f459,f106])).
% 0.22/0.53  fof(f459,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (r1_waybel_0(X0,X1,sK9(X0,X2,sK7(X0,X1,X3))) | k10_yellow_6(X0,X1) = X3 | r2_hidden(sK7(X0,X1,X3),X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | r2_hidden(sK7(X0,X1,X3),k10_yellow_6(X0,X2)) | ~m1_subset_1(k10_yellow_6(X0,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f458,f98])).
% 0.22/0.53  fof(f458,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (r1_waybel_0(X0,X1,sK9(X0,X2,sK7(X0,X1,X3))) | k10_yellow_6(X0,X1) = X3 | r2_hidden(sK7(X0,X1,X3),X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | r2_hidden(sK7(X0,X1,X3),k10_yellow_6(X0,X2)) | ~m1_subset_1(sK7(X0,X1,X3),u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2)) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f455])).
% 0.22/0.53  fof(f455,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (r1_waybel_0(X0,X1,sK9(X0,X2,sK7(X0,X1,X3))) | k10_yellow_6(X0,X1) = X3 | r2_hidden(sK7(X0,X1,X3),X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | r2_hidden(sK7(X0,X1,X3),k10_yellow_6(X0,X2)) | ~m1_subset_1(sK7(X0,X1,X3),u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(resolution,[],[f99,f111])).
% 0.22/0.53  fof(f111,plain,(
% 0.22/0.53    ( ! [X6,X0,X1] : (m1_connsp_2(sK9(X0,X1,X6),X0,X6) | r2_hidden(X6,k10_yellow_6(X0,X1)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(equality_resolution,[],[f96])).
% 0.22/0.53  fof(f96,plain,(
% 0.22/0.53    ( ! [X6,X2,X0,X1] : (r2_hidden(X6,X2) | m1_connsp_2(sK9(X0,X1,X6),X0,X6) | ~m1_subset_1(X6,u1_struct_0(X0)) | k10_yellow_6(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f66])).
% 0.22/0.53  fof(f99,plain,(
% 0.22/0.53    ( ! [X2,X0,X5,X1] : (~m1_connsp_2(X5,X0,sK7(X0,X1,X2)) | r1_waybel_0(X0,X1,X5) | k10_yellow_6(X0,X1) = X2 | r2_hidden(sK7(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f66])).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_xboole_0 != k10_yellow_6(X0,X1) | ~v3_yellow_6(X1,X0) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f57])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (15893)------------------------------
% 0.22/0.53  % (15893)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (15893)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (15893)Memory used [KB]: 2046
% 0.22/0.53  % (15893)Time elapsed: 0.070 s
% 0.22/0.53  % (15893)------------------------------
% 0.22/0.53  % (15893)------------------------------
% 0.22/0.53  % (15874)Success in time 0.166 s
%------------------------------------------------------------------------------
