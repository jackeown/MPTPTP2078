%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:40 EST 2020

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :  257 (5872 expanded)
%              Number of leaves         :   22 (1714 expanded)
%              Depth                    :   95
%              Number of atoms          : 2332 (69962 expanded)
%              Number of equality atoms :   49 ( 177 expanded)
%              Maximal formula depth    :   29 (  10 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f608,plain,(
    $false ),
    inference(subsumption_resolution,[],[f607,f64])).

fof(f64,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f42,f45,f44,f43])).

fof(f43,plain,
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

fof(f44,plain,
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

fof(f45,plain,(
    ! [X3] :
      ( ? [X4] :
          ( v3_yellow_6(X4,sK0)
          & m2_yellow_6(X4,sK0,X3) )
     => ( v3_yellow_6(sK2(X3),sK0)
        & m2_yellow_6(sK2(X3),sK0,X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f18])).

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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_yellow19)).

fof(f607,plain,(
    ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f602,f73])).

fof(f73,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f602,plain,(
    ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f601,f62])).

fof(f62,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f601,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f600,f63])).

fof(f63,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f600,plain,
    ( ~ l1_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f599,f64])).

fof(f599,plain,
    ( ~ l1_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f598,f328])).

fof(f328,plain,(
    ~ v1_compts_1(sK0) ),
    inference(subsumption_resolution,[],[f327,f67])).

fof(f67,plain,
    ( ~ v1_compts_1(sK0)
    | ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f327,plain,
    ( ~ v1_compts_1(sK0)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f326,f68])).

fof(f68,plain,
    ( ~ v1_compts_1(sK0)
    | v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f326,plain,
    ( ~ v1_compts_1(sK0)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f325,f69])).

fof(f69,plain,
    ( ~ v1_compts_1(sK0)
    | v7_waybel_0(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f325,plain,
    ( ~ v1_compts_1(sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f324,f70])).

fof(f70,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f324,plain,
    ( ~ v1_compts_1(sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f323,f62])).

fof(f323,plain,
    ( ~ v1_compts_1(sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f322,f63])).

fof(f322,plain,
    ( ~ v1_compts_1(sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f321,f64])).

fof(f321,plain,
    ( ~ v1_compts_1(sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f320])).

fof(f320,plain,
    ( ~ v1_compts_1(sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f304,f74])).

fof(f74,plain,(
    ! [X0,X3] :
      ( m1_subset_1(sK4(X0,X3),u1_struct_0(X0))
      | ~ l1_waybel_0(X3,X0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ( ! [X2] :
                ( ~ r3_waybel_9(X0,sK3(X0),X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & l1_waybel_0(sK3(X0),X0)
            & v7_waybel_0(sK3(X0))
            & v4_orders_2(sK3(X0))
            & ~ v2_struct_0(sK3(X0)) ) )
        & ( ! [X3] :
              ( ( r3_waybel_9(X0,X3,sK4(X0,X3))
                & m1_subset_1(sK4(X0,X3),u1_struct_0(X0)) )
              | ~ l1_waybel_0(X3,X0)
              | ~ v7_waybel_0(X3)
              | ~ v4_orders_2(X3)
              | v2_struct_0(X3) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f48,f50,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
     => ( ! [X2] :
            ( ~ r3_waybel_9(X0,sK3(X0),X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & l1_waybel_0(sK3(X0),X0)
        & v7_waybel_0(sK3(X0))
        & v4_orders_2(sK3(X0))
        & ~ v2_struct_0(sK3(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( r3_waybel_9(X0,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X3,sK4(X0,X3))
        & m1_subset_1(sK4(X0,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ? [X1] :
              ( ! [X2] :
                  ( ~ r3_waybel_9(X0,X1,X2)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              & l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) ) )
        & ( ! [X3] :
              ( ? [X4] :
                  ( r3_waybel_9(X0,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ l1_waybel_0(X3,X0)
              | ~ v7_waybel_0(X3)
              | ~ v4_orders_2(X3)
              | v2_struct_0(X3) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ? [X1] :
              ( ! [X2] :
                  ( ~ r3_waybel_9(X0,X1,X2)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              & l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) ) )
        & ( ! [X1] :
              ( ? [X2] :
                  ( r3_waybel_9(X0,X1,X2)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ l1_waybel_0(X1,X0)
              | ~ v7_waybel_0(X1)
              | ~ v4_orders_2(X1)
              | v2_struct_0(X1) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> ! [X1] :
            ( ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> ! [X1] :
            ( ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) ) )
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
      <=> ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_yellow19)).

fof(f304,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ v1_compts_1(sK0) ),
    inference(subsumption_resolution,[],[f303,f67])).

fof(f303,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ v1_compts_1(sK0)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f302,f68])).

fof(f302,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ v1_compts_1(sK0)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f301,f69])).

fof(f301,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ v1_compts_1(sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f300,f70])).

fof(f300,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ v1_compts_1(sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f299,f62])).

fof(f299,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ v1_compts_1(sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f298,f63])).

fof(f298,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ v1_compts_1(sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f297,f64])).

fof(f297,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ v1_compts_1(sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f293])).

fof(f293,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ v1_compts_1(sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f292,f75])).

fof(f75,plain,(
    ! [X0,X3] :
      ( r3_waybel_9(X0,X3,sK4(X0,X3))
      | ~ l1_waybel_0(X3,X0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f292,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f291,f67])).

fof(f291,plain,(
    ! [X0] :
      ( v2_struct_0(sK1)
      | ~ r3_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f290,f68])).

fof(f290,plain,(
    ! [X0] :
      ( ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ r3_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f289,f69])).

fof(f289,plain,(
    ! [X0] :
      ( ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ r3_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f288,f70])).

fof(f288,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ r3_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f287,f62])).

fof(f287,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ r3_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f286,f63])).

fof(f286,plain,(
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
    inference(subsumption_resolution,[],[f285,f64])).

fof(f285,plain,(
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
    inference(duplicate_literal_removal,[],[f284])).

fof(f284,plain,(
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
    inference(resolution,[],[f276,f190])).

fof(f190,plain,(
    ! [X0] :
      ( ~ v3_yellow_6(sK5(sK0,sK1,X0),sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK1,X0)
      | ~ v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f189,f67])).

fof(f189,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK1)
      | ~ v3_yellow_6(sK5(sK0,sK1,X0),sK0)
      | ~ v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f188,f68])).

fof(f188,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ v3_yellow_6(sK5(sK0,sK1,X0),sK0)
      | ~ v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f187,f69])).

fof(f187,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ v3_yellow_6(sK5(sK0,sK1,X0),sK0)
      | ~ v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f186,f70])).

fof(f186,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ v3_yellow_6(sK5(sK0,sK1,X0),sK0)
      | ~ v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f185,f62])).

fof(f185,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ v3_yellow_6(sK5(sK0,sK1,X0),sK0)
      | ~ v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f184,f63])).

fof(f184,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ v3_yellow_6(sK5(sK0,sK1,X0),sK0)
      | ~ v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f175,f64])).

fof(f175,plain,(
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
      | ~ v3_yellow_6(sK5(sK0,sK1,X0),sK0)
      | ~ v1_compts_1(sK0) ) ),
    inference(resolution,[],[f84,f71])).

fof(f71,plain,(
    ! [X2] :
      ( ~ m2_yellow_6(X2,sK0,sK1)
      | ~ v3_yellow_6(X2,sK0)
      | ~ v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( m2_yellow_6(sK5(X0,X1,X2),X0,X1)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,sK5(X0,X1,X2)))
                & m2_yellow_6(sK5(X0,X1,X2),X0,X1) )
              | ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f27,f53])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X2,k10_yellow_6(X0,X3))
          & m2_yellow_6(X3,X0,X1) )
     => ( r2_hidden(X2,k10_yellow_6(X0,sK5(X0,X1,X2)))
        & m2_yellow_6(sK5(X0,X1,X2),X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_waybel_9)).

fof(f276,plain,(
    ! [X2,X0,X1] :
      ( v3_yellow_6(sK5(X0,X1,X2),X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f275,f194])).

fof(f194,plain,(
    ! [X12,X10,X11] :
      ( ~ v2_struct_0(sK5(X10,X11,X12))
      | ~ m1_subset_1(X12,u1_struct_0(X10))
      | ~ l1_waybel_0(X11,X10)
      | ~ v7_waybel_0(X11)
      | ~ v4_orders_2(X11)
      | v2_struct_0(X11)
      | ~ l1_pre_topc(X10)
      | ~ v2_pre_topc(X10)
      | v2_struct_0(X10)
      | ~ r3_waybel_9(X10,X11,X12) ) ),
    inference(subsumption_resolution,[],[f180,f73])).

fof(f180,plain,(
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
      | ~ v2_struct_0(sK5(X10,X11,X12))
      | ~ l1_struct_0(X10) ) ),
    inference(duplicate_literal_removal,[],[f179])).

fof(f179,plain,(
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
      | ~ v2_struct_0(sK5(X10,X11,X12))
      | ~ l1_waybel_0(X11,X10)
      | ~ v7_waybel_0(X11)
      | ~ v4_orders_2(X11)
      | v2_struct_0(X11)
      | ~ l1_struct_0(X10)
      | v2_struct_0(X10) ) ),
    inference(resolution,[],[f84,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_yellow_6(X2,X0,X1)
      | ~ v2_struct_0(X2)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_yellow_6)).

fof(f275,plain,(
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
      | v3_yellow_6(sK5(X0,X1,X2),X0)
      | v2_struct_0(sK5(X0,X1,X2)) ) ),
    inference(subsumption_resolution,[],[f274,f193])).

fof(f193,plain,(
    ! [X8,X7,X9] :
      ( v4_orders_2(sK5(X7,X8,X9))
      | ~ m1_subset_1(X9,u1_struct_0(X7))
      | ~ l1_waybel_0(X8,X7)
      | ~ v7_waybel_0(X8)
      | ~ v4_orders_2(X8)
      | v2_struct_0(X8)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7)
      | ~ r3_waybel_9(X7,X8,X9) ) ),
    inference(subsumption_resolution,[],[f181,f73])).

fof(f181,plain,(
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
      | v4_orders_2(sK5(X7,X8,X9))
      | ~ l1_struct_0(X7) ) ),
    inference(duplicate_literal_removal,[],[f178])).

fof(f178,plain,(
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
      | v4_orders_2(sK5(X7,X8,X9))
      | ~ l1_waybel_0(X8,X7)
      | ~ v7_waybel_0(X8)
      | ~ v4_orders_2(X8)
      | v2_struct_0(X8)
      | ~ l1_struct_0(X7)
      | v2_struct_0(X7) ) ),
    inference(resolution,[],[f84,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_yellow_6(X2,X0,X1)
      | v4_orders_2(X2)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f274,plain,(
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
      | v3_yellow_6(sK5(X0,X1,X2),X0)
      | ~ v4_orders_2(sK5(X0,X1,X2))
      | v2_struct_0(sK5(X0,X1,X2)) ) ),
    inference(subsumption_resolution,[],[f273,f192])).

fof(f192,plain,(
    ! [X6,X4,X5] :
      ( v7_waybel_0(sK5(X4,X5,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ l1_waybel_0(X5,X4)
      | ~ v7_waybel_0(X5)
      | ~ v4_orders_2(X5)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | ~ r3_waybel_9(X4,X5,X6) ) ),
    inference(subsumption_resolution,[],[f182,f73])).

fof(f182,plain,(
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
      | v7_waybel_0(sK5(X4,X5,X6))
      | ~ l1_struct_0(X4) ) ),
    inference(duplicate_literal_removal,[],[f177])).

fof(f177,plain,(
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
      | v7_waybel_0(sK5(X4,X5,X6))
      | ~ l1_waybel_0(X5,X4)
      | ~ v7_waybel_0(X5)
      | ~ v4_orders_2(X5)
      | v2_struct_0(X5)
      | ~ l1_struct_0(X4)
      | v2_struct_0(X4) ) ),
    inference(resolution,[],[f84,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_yellow_6(X2,X0,X1)
      | v7_waybel_0(X2)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f273,plain,(
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
      | v3_yellow_6(sK5(X0,X1,X2),X0)
      | ~ v7_waybel_0(sK5(X0,X1,X2))
      | ~ v4_orders_2(sK5(X0,X1,X2))
      | v2_struct_0(sK5(X0,X1,X2)) ) ),
    inference(subsumption_resolution,[],[f272,f191])).

fof(f191,plain,(
    ! [X2,X3,X1] :
      ( l1_waybel_0(sK5(X1,X2,X3),X1)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_waybel_0(X2,X1)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ r3_waybel_9(X1,X2,X3) ) ),
    inference(subsumption_resolution,[],[f183,f73])).

fof(f183,plain,(
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
      | l1_waybel_0(sK5(X1,X2,X3),X1)
      | ~ l1_struct_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f176])).

fof(f176,plain,(
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
      | l1_waybel_0(sK5(X1,X2,X3),X1)
      | ~ l1_waybel_0(X2,X1)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f84,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_yellow_6(X2,X0,X1)
      | l1_waybel_0(X2,X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f272,plain,(
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
      | v3_yellow_6(sK5(X0,X1,X2),X0)
      | ~ l1_waybel_0(sK5(X0,X1,X2),X0)
      | ~ v7_waybel_0(sK5(X0,X1,X2))
      | ~ v4_orders_2(sK5(X0,X1,X2))
      | v2_struct_0(sK5(X0,X1,X2)) ) ),
    inference(subsumption_resolution,[],[f266,f106])).

fof(f106,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f99,f72])).

fof(f72,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f266,plain,(
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
      | v3_yellow_6(sK5(X0,X1,X2),X0)
      | ~ l1_waybel_0(sK5(X0,X1,X2),X0)
      | ~ v7_waybel_0(sK5(X0,X1,X2))
      | ~ v4_orders_2(sK5(X0,X1,X2))
      | v2_struct_0(sK5(X0,X1,X2)) ) ),
    inference(duplicate_literal_removal,[],[f265])).

fof(f265,plain,(
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
      | v3_yellow_6(sK5(X0,X1,X2),X0)
      | ~ l1_waybel_0(sK5(X0,X1,X2),X0)
      | ~ v7_waybel_0(sK5(X0,X1,X2))
      | ~ v4_orders_2(sK5(X0,X1,X2))
      | v2_struct_0(sK5(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f209,f82])).

fof(f82,plain,(
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
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_yellow_6)).

fof(f209,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_tarski(k10_yellow_6(X6,sK5(X6,X7,X8)),X8)
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ l1_waybel_0(X7,X6)
      | ~ v7_waybel_0(X7)
      | ~ v4_orders_2(X7)
      | v2_struct_0(X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | ~ r3_waybel_9(X6,X7,X8) ) ),
    inference(resolution,[],[f85,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k10_yellow_6(X0,sK5(X0,X1,X2)))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f598,plain,
    ( ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f597,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v2_struct_0(sK3(X0))
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f597,plain,
    ( v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f596,f62])).

fof(f596,plain,
    ( v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f595,f63])).

fof(f595,plain,
    ( v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f594,f64])).

fof(f594,plain,
    ( v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f593,f328])).

fof(f593,plain,
    ( v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f592,f77])).

fof(f77,plain,(
    ! [X0] :
      ( v4_orders_2(sK3(X0))
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f592,plain,
    ( ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f591,f62])).

fof(f591,plain,
    ( ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f590,f63])).

fof(f590,plain,
    ( ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f589,f64])).

fof(f589,plain,
    ( ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f588,f328])).

fof(f588,plain,
    ( ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f587,f78])).

fof(f78,plain,(
    ! [X0] :
      ( v7_waybel_0(sK3(X0))
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f587,plain,
    ( ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f586,f328])).

fof(f586,plain,
    ( ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0) ),
    inference(duplicate_literal_removal,[],[f585])).

fof(f585,plain,
    ( ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0) ),
    inference(resolution,[],[f584,f116])).

fof(f116,plain,
    ( ~ v2_struct_0(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0) ),
    inference(subsumption_resolution,[],[f115,f62])).

fof(f115,plain,
    ( ~ v2_struct_0(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f114,f63])).

fof(f114,plain,
    ( ~ v2_struct_0(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f113,f64])).

fof(f113,plain,
    ( ~ v2_struct_0(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f112])).

fof(f112,plain,
    ( ~ v2_struct_0(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f110,f79])).

fof(f79,plain,(
    ! [X0] :
      ( l1_waybel_0(sK3(X0),X0)
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f110,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ v2_struct_0(sK2(X0))
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(sK0)
      | v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f109,f62])).

fof(f109,plain,(
    ! [X0] :
      ( ~ v2_struct_0(sK2(X0))
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0)
      | v1_compts_1(sK0) ) ),
    inference(duplicate_literal_removal,[],[f108])).

fof(f108,plain,(
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
    inference(resolution,[],[f94,f65])).

fof(f65,plain,(
    ! [X3] :
      ( m2_yellow_6(sK2(X3),sK0,X3)
      | ~ l1_waybel_0(X3,sK0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f584,plain,
    ( v2_struct_0(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f583,f328])).

fof(f583,plain,
    ( v2_struct_0(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0) ),
    inference(duplicate_literal_removal,[],[f582])).

fof(f582,plain,
    ( v2_struct_0(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0) ),
    inference(resolution,[],[f581,f125])).

fof(f125,plain,
    ( v4_orders_2(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0) ),
    inference(subsumption_resolution,[],[f124,f62])).

fof(f124,plain,
    ( v4_orders_2(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f123,f63])).

fof(f123,plain,
    ( v4_orders_2(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f122,f64])).

fof(f122,plain,
    ( v4_orders_2(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f121])).

fof(f121,plain,
    ( v4_orders_2(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f119,f79])).

fof(f119,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(X0,sK0)
      | v4_orders_2(sK2(X0))
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(sK0)
      | v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f118,f62])).

fof(f118,plain,(
    ! [X0] :
      ( v4_orders_2(sK2(X0))
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
    inference(resolution,[],[f95,f65])).

fof(f581,plain,
    ( ~ v4_orders_2(sK2(sK3(sK0)))
    | v2_struct_0(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f580,f328])).

fof(f580,plain,
    ( v2_struct_0(sK2(sK3(sK0)))
    | ~ v4_orders_2(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0) ),
    inference(duplicate_literal_removal,[],[f579])).

fof(f579,plain,
    ( v2_struct_0(sK2(sK3(sK0)))
    | ~ v4_orders_2(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0) ),
    inference(resolution,[],[f578,f134])).

fof(f134,plain,
    ( v7_waybel_0(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0) ),
    inference(subsumption_resolution,[],[f133,f62])).

fof(f133,plain,
    ( v7_waybel_0(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f132,f63])).

fof(f132,plain,
    ( v7_waybel_0(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f131,f64])).

fof(f131,plain,
    ( v7_waybel_0(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f130])).

fof(f130,plain,
    ( v7_waybel_0(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f128,f79])).

fof(f128,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(X0,sK0)
      | v7_waybel_0(sK2(X0))
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(sK0)
      | v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f127,f62])).

fof(f127,plain,(
    ! [X0] :
      ( v7_waybel_0(sK2(X0))
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
    inference(resolution,[],[f96,f65])).

fof(f578,plain,
    ( ~ v7_waybel_0(sK2(sK3(sK0)))
    | v2_struct_0(sK2(sK3(sK0)))
    | ~ v4_orders_2(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f577,f62])).

fof(f577,plain,
    ( ~ v4_orders_2(sK2(sK3(sK0)))
    | v2_struct_0(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f576,f63])).

fof(f576,plain,
    ( ~ v4_orders_2(sK2(sK3(sK0)))
    | v2_struct_0(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f575,f64])).

fof(f575,plain,
    ( ~ v4_orders_2(sK2(sK3(sK0)))
    | v2_struct_0(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f574,f328])).

fof(f574,plain,
    ( ~ v4_orders_2(sK2(sK3(sK0)))
    | v2_struct_0(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f573,f79])).

fof(f573,plain,
    ( ~ l1_waybel_0(sK3(sK0),sK0)
    | ~ v4_orders_2(sK2(sK3(sK0)))
    | v2_struct_0(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f572,f328])).

fof(f572,plain,
    ( ~ v7_waybel_0(sK2(sK3(sK0)))
    | ~ v4_orders_2(sK2(sK3(sK0)))
    | v2_struct_0(sK2(sK3(sK0)))
    | ~ l1_waybel_0(sK3(sK0),sK0)
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0) ),
    inference(duplicate_literal_removal,[],[f571])).

fof(f571,plain,
    ( ~ v7_waybel_0(sK2(sK3(sK0)))
    | ~ v4_orders_2(sK2(sK3(sK0)))
    | v2_struct_0(sK2(sK3(sK0)))
    | ~ l1_waybel_0(sK3(sK0),sK0)
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_waybel_0(sK3(sK0),sK0)
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0) ),
    inference(resolution,[],[f570,f137])).

fof(f137,plain,(
    ! [X0] :
      ( l1_waybel_0(sK2(X0),sK0)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(sK0)
      | v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f136,f62])).

fof(f136,plain,(
    ! [X0] :
      ( l1_waybel_0(sK2(X0),sK0)
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
    inference(resolution,[],[f97,f65])).

fof(f570,plain,
    ( ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
    | ~ v7_waybel_0(sK2(sK3(sK0)))
    | ~ v4_orders_2(sK2(sK3(sK0)))
    | v2_struct_0(sK2(sK3(sK0)))
    | ~ l1_waybel_0(sK3(sK0),sK0)
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0)) ),
    inference(subsumption_resolution,[],[f569,f328])).

fof(f569,plain,
    ( ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
    | ~ v7_waybel_0(sK2(sK3(sK0)))
    | ~ v4_orders_2(sK2(sK3(sK0)))
    | v2_struct_0(sK2(sK3(sK0)))
    | ~ l1_waybel_0(sK3(sK0),sK0)
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | v1_compts_1(sK0) ),
    inference(duplicate_literal_removal,[],[f568])).

fof(f568,plain,
    ( ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
    | ~ v7_waybel_0(sK2(sK3(sK0)))
    | ~ v4_orders_2(sK2(sK3(sK0)))
    | v2_struct_0(sK2(sK3(sK0)))
    | ~ l1_waybel_0(sK3(sK0),sK0)
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_waybel_0(sK3(sK0),sK0)
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | v1_compts_1(sK0) ),
    inference(resolution,[],[f555,f66])).

fof(f66,plain,(
    ! [X3] :
      ( v3_yellow_6(sK2(X3),sK0)
      | ~ l1_waybel_0(X3,sK0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f555,plain,
    ( ~ v3_yellow_6(sK2(sK3(sK0)),sK0)
    | ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
    | ~ v7_waybel_0(sK2(sK3(sK0)))
    | ~ v4_orders_2(sK2(sK3(sK0)))
    | v2_struct_0(sK2(sK3(sK0)))
    | ~ l1_waybel_0(sK3(sK0),sK0)
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0)) ),
    inference(subsumption_resolution,[],[f554,f62])).

fof(f554,plain,
    ( ~ v3_yellow_6(sK2(sK3(sK0)),sK0)
    | ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
    | ~ v7_waybel_0(sK2(sK3(sK0)))
    | ~ v4_orders_2(sK2(sK3(sK0)))
    | v2_struct_0(sK2(sK3(sK0)))
    | v2_struct_0(sK0)
    | ~ l1_waybel_0(sK3(sK0),sK0)
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0)) ),
    inference(subsumption_resolution,[],[f553,f63])).

fof(f553,plain,
    ( ~ v3_yellow_6(sK2(sK3(sK0)),sK0)
    | ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
    | ~ v7_waybel_0(sK2(sK3(sK0)))
    | ~ v4_orders_2(sK2(sK3(sK0)))
    | v2_struct_0(sK2(sK3(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_waybel_0(sK3(sK0),sK0)
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0)) ),
    inference(subsumption_resolution,[],[f552,f64])).

fof(f552,plain,
    ( ~ v3_yellow_6(sK2(sK3(sK0)),sK0)
    | ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
    | ~ v7_waybel_0(sK2(sK3(sK0)))
    | ~ v4_orders_2(sK2(sK3(sK0)))
    | v2_struct_0(sK2(sK3(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_waybel_0(sK3(sK0),sK0)
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0)) ),
    inference(trivial_inequality_removal,[],[f551])).

fof(f551,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v3_yellow_6(sK2(sK3(sK0)),sK0)
    | ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
    | ~ v7_waybel_0(sK2(sK3(sK0)))
    | ~ v4_orders_2(sK2(sK3(sK0)))
    | v2_struct_0(sK2(sK3(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_waybel_0(sK3(sK0),sK0)
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0)) ),
    inference(duplicate_literal_removal,[],[f532])).

fof(f532,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v3_yellow_6(sK2(sK3(sK0)),sK0)
    | ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
    | ~ v7_waybel_0(sK2(sK3(sK0)))
    | ~ v4_orders_2(sK2(sK3(sK0)))
    | v2_struct_0(sK2(sK3(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK2(sK3(sK0)))
    | ~ v4_orders_2(sK2(sK3(sK0)))
    | ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
    | ~ l1_waybel_0(sK3(sK0),sK0)
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ v7_waybel_0(sK2(sK3(sK0))) ),
    inference(superposition,[],[f81,f531])).

fof(f531,plain,
    ( k1_xboole_0 = k10_yellow_6(sK0,sK2(sK3(sK0)))
    | v2_struct_0(sK2(sK3(sK0)))
    | ~ v4_orders_2(sK2(sK3(sK0)))
    | ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
    | ~ l1_waybel_0(sK3(sK0),sK0)
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ v7_waybel_0(sK2(sK3(sK0))) ),
    inference(subsumption_resolution,[],[f528,f72])).

fof(f528,plain,
    ( ~ v4_orders_2(sK2(sK3(sK0)))
    | v2_struct_0(sK2(sK3(sK0)))
    | k1_xboole_0 = k10_yellow_6(sK0,sK2(sK3(sK0)))
    | ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_waybel_0(sK3(sK0),sK0)
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ v7_waybel_0(sK2(sK3(sK0))) ),
    inference(resolution,[],[f514,f106])).

fof(f514,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK6(sK0,sK2(sK3(sK0)),X0))
      | ~ v4_orders_2(sK2(sK3(sK0)))
      | v2_struct_0(sK2(sK3(sK0)))
      | k10_yellow_6(sK0,sK2(sK3(sK0))) = X0
      | ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_waybel_0(sK3(sK0),sK0)
      | ~ v7_waybel_0(sK3(sK0))
      | ~ v4_orders_2(sK3(sK0))
      | v2_struct_0(sK3(sK0))
      | ~ v7_waybel_0(sK2(sK3(sK0))) ) ),
    inference(resolution,[],[f512,f100])).

fof(f512,plain,(
    ! [X0] :
      ( r2_hidden(sK6(sK0,sK2(sK3(sK0)),X0),X0)
      | ~ v7_waybel_0(sK2(sK3(sK0)))
      | ~ v4_orders_2(sK2(sK3(sK0)))
      | v2_struct_0(sK2(sK3(sK0)))
      | k10_yellow_6(sK0,sK2(sK3(sK0))) = X0
      | ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_waybel_0(sK3(sK0),sK0)
      | ~ v7_waybel_0(sK3(sK0))
      | ~ v4_orders_2(sK3(sK0))
      | v2_struct_0(sK3(sK0)) ) ),
    inference(subsumption_resolution,[],[f511,f62])).

fof(f511,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
      | ~ v7_waybel_0(sK2(sK3(sK0)))
      | ~ v4_orders_2(sK2(sK3(sK0)))
      | v2_struct_0(sK2(sK3(sK0)))
      | k10_yellow_6(sK0,sK2(sK3(sK0))) = X0
      | r2_hidden(sK6(sK0,sK2(sK3(sK0)),X0),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_waybel_0(sK3(sK0),sK0)
      | ~ v7_waybel_0(sK3(sK0))
      | ~ v4_orders_2(sK3(sK0))
      | v2_struct_0(sK3(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f510,f63])).

fof(f510,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
      | ~ v7_waybel_0(sK2(sK3(sK0)))
      | ~ v4_orders_2(sK2(sK3(sK0)))
      | v2_struct_0(sK2(sK3(sK0)))
      | k10_yellow_6(sK0,sK2(sK3(sK0))) = X0
      | r2_hidden(sK6(sK0,sK2(sK3(sK0)),X0),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_waybel_0(sK3(sK0),sK0)
      | ~ v7_waybel_0(sK3(sK0))
      | ~ v4_orders_2(sK3(sK0))
      | v2_struct_0(sK3(sK0))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f509,f64])).

fof(f509,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
      | ~ v7_waybel_0(sK2(sK3(sK0)))
      | ~ v4_orders_2(sK2(sK3(sK0)))
      | v2_struct_0(sK2(sK3(sK0)))
      | k10_yellow_6(sK0,sK2(sK3(sK0))) = X0
      | r2_hidden(sK6(sK0,sK2(sK3(sK0)),X0),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_waybel_0(sK3(sK0),sK0)
      | ~ v7_waybel_0(sK3(sK0))
      | ~ v4_orders_2(sK3(sK0))
      | v2_struct_0(sK3(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f508])).

fof(f508,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
      | ~ v7_waybel_0(sK2(sK3(sK0)))
      | ~ v4_orders_2(sK2(sK3(sK0)))
      | v2_struct_0(sK2(sK3(sK0)))
      | k10_yellow_6(sK0,sK2(sK3(sK0))) = X0
      | r2_hidden(sK6(sK0,sK2(sK3(sK0)),X0),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_waybel_0(sK3(sK0),sK0)
      | ~ v7_waybel_0(sK3(sK0))
      | ~ v4_orders_2(sK3(sK0))
      | v2_struct_0(sK3(sK0))
      | k10_yellow_6(sK0,sK2(sK3(sK0))) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
      | ~ v7_waybel_0(sK2(sK3(sK0)))
      | ~ v4_orders_2(sK2(sK3(sK0)))
      | v2_struct_0(sK2(sK3(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f490,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | k10_yellow_6(X0,X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ( ( ( ~ r1_waybel_0(X0,X1,sK7(X0,X1,X2))
                        & m1_connsp_2(sK7(X0,X1,X2),X0,sK6(X0,X1,X2)) )
                      | ~ r2_hidden(sK6(X0,X1,X2),X2) )
                    & ( ! [X5] :
                          ( r1_waybel_0(X0,X1,X5)
                          | ~ m1_connsp_2(X5,X0,sK6(X0,X1,X2)) )
                      | r2_hidden(sK6(X0,X1,X2),X2) )
                    & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ( ~ r1_waybel_0(X0,X1,sK8(X0,X1,X6))
                            & m1_connsp_2(sK8(X0,X1,X6),X0,X6) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f57,f60,f59,f58])).

fof(f58,plain,(
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
              & m1_connsp_2(X4,X0,sK6(X0,X1,X2)) )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ! [X5] :
              ( r1_waybel_0(X0,X1,X5)
              | ~ m1_connsp_2(X5,X0,sK6(X0,X1,X2)) )
          | r2_hidden(sK6(X0,X1,X2),X2) )
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_waybel_0(X0,X1,X4)
          & m1_connsp_2(X4,X0,sK6(X0,X1,X2)) )
     => ( ~ r1_waybel_0(X0,X1,sK7(X0,X1,X2))
        & m1_connsp_2(sK7(X0,X1,X2),X0,sK6(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X6,X1,X0] :
      ( ? [X7] :
          ( ~ r1_waybel_0(X0,X1,X7)
          & m1_connsp_2(X7,X0,X6) )
     => ( ~ r1_waybel_0(X0,X1,sK8(X0,X1,X6))
        & m1_connsp_2(sK8(X0,X1,X6),X0,X6) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
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
    inference(rectify,[],[f56])).

fof(f56,plain,(
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
    inference(flattening,[],[f55])).

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_yellow_6)).

fof(f490,plain,(
    ! [X2] :
      ( ~ m1_subset_1(sK6(sK0,sK2(sK3(sK0)),X2),u1_struct_0(sK0))
      | ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
      | ~ v7_waybel_0(sK2(sK3(sK0)))
      | ~ v4_orders_2(sK2(sK3(sK0)))
      | v2_struct_0(sK2(sK3(sK0)))
      | k10_yellow_6(sK0,sK2(sK3(sK0))) = X2
      | r2_hidden(sK6(sK0,sK2(sK3(sK0)),X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_waybel_0(sK3(sK0),sK0)
      | ~ v7_waybel_0(sK3(sK0))
      | ~ v4_orders_2(sK3(sK0))
      | v2_struct_0(sK3(sK0)) ) ),
    inference(subsumption_resolution,[],[f489,f328])).

fof(f489,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
      | ~ v7_waybel_0(sK2(sK3(sK0)))
      | ~ v4_orders_2(sK2(sK3(sK0)))
      | v2_struct_0(sK2(sK3(sK0)))
      | k10_yellow_6(sK0,sK2(sK3(sK0))) = X2
      | r2_hidden(sK6(sK0,sK2(sK3(sK0)),X2),X2)
      | ~ m1_subset_1(sK6(sK0,sK2(sK3(sK0)),X2),u1_struct_0(sK0))
      | v1_compts_1(sK0)
      | ~ l1_waybel_0(sK3(sK0),sK0)
      | ~ v7_waybel_0(sK3(sK0))
      | ~ v4_orders_2(sK3(sK0))
      | v2_struct_0(sK3(sK0)) ) ),
    inference(subsumption_resolution,[],[f488,f62])).

fof(f488,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
      | ~ v7_waybel_0(sK2(sK3(sK0)))
      | ~ v4_orders_2(sK2(sK3(sK0)))
      | v2_struct_0(sK2(sK3(sK0)))
      | v2_struct_0(sK0)
      | k10_yellow_6(sK0,sK2(sK3(sK0))) = X2
      | r2_hidden(sK6(sK0,sK2(sK3(sK0)),X2),X2)
      | ~ m1_subset_1(sK6(sK0,sK2(sK3(sK0)),X2),u1_struct_0(sK0))
      | v1_compts_1(sK0)
      | ~ l1_waybel_0(sK3(sK0),sK0)
      | ~ v7_waybel_0(sK3(sK0))
      | ~ v4_orders_2(sK3(sK0))
      | v2_struct_0(sK3(sK0)) ) ),
    inference(subsumption_resolution,[],[f487,f63])).

fof(f487,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
      | ~ v7_waybel_0(sK2(sK3(sK0)))
      | ~ v4_orders_2(sK2(sK3(sK0)))
      | v2_struct_0(sK2(sK3(sK0)))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | k10_yellow_6(sK0,sK2(sK3(sK0))) = X2
      | r2_hidden(sK6(sK0,sK2(sK3(sK0)),X2),X2)
      | ~ m1_subset_1(sK6(sK0,sK2(sK3(sK0)),X2),u1_struct_0(sK0))
      | v1_compts_1(sK0)
      | ~ l1_waybel_0(sK3(sK0),sK0)
      | ~ v7_waybel_0(sK3(sK0))
      | ~ v4_orders_2(sK3(sK0))
      | v2_struct_0(sK3(sK0)) ) ),
    inference(subsumption_resolution,[],[f474,f64])).

fof(f474,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
      | ~ v7_waybel_0(sK2(sK3(sK0)))
      | ~ v4_orders_2(sK2(sK3(sK0)))
      | v2_struct_0(sK2(sK3(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | k10_yellow_6(sK0,sK2(sK3(sK0))) = X2
      | r2_hidden(sK6(sK0,sK2(sK3(sK0)),X2),X2)
      | ~ m1_subset_1(sK6(sK0,sK2(sK3(sK0)),X2),u1_struct_0(sK0))
      | v1_compts_1(sK0)
      | ~ l1_waybel_0(sK3(sK0),sK0)
      | ~ v7_waybel_0(sK3(sK0))
      | ~ v4_orders_2(sK3(sK0))
      | v2_struct_0(sK3(sK0)) ) ),
    inference(resolution,[],[f466,f234])).

fof(f234,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK2(sK3(sK0)),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v1_compts_1(sK0)
      | ~ l1_waybel_0(sK3(sK0),sK0)
      | ~ v7_waybel_0(sK3(sK0))
      | ~ v4_orders_2(sK3(sK0))
      | v2_struct_0(sK3(sK0)) ) ),
    inference(subsumption_resolution,[],[f233,f62])).

fof(f233,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK2(sK3(sK0)),X0)
      | v2_struct_0(sK0)
      | v1_compts_1(sK0)
      | ~ l1_waybel_0(sK3(sK0),sK0)
      | ~ v7_waybel_0(sK3(sK0))
      | ~ v4_orders_2(sK3(sK0))
      | v2_struct_0(sK3(sK0)) ) ),
    inference(subsumption_resolution,[],[f232,f63])).

fof(f232,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK2(sK3(sK0)),X0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | v1_compts_1(sK0)
      | ~ l1_waybel_0(sK3(sK0),sK0)
      | ~ v7_waybel_0(sK3(sK0))
      | ~ v4_orders_2(sK3(sK0))
      | v2_struct_0(sK3(sK0)) ) ),
    inference(subsumption_resolution,[],[f231,f64])).

fof(f231,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK2(sK3(sK0)),X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | v1_compts_1(sK0)
      | ~ l1_waybel_0(sK3(sK0),sK0)
      | ~ v7_waybel_0(sK3(sK0))
      | ~ v4_orders_2(sK3(sK0))
      | v2_struct_0(sK3(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f228])).

fof(f228,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK2(sK3(sK0)),X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | v1_compts_1(sK0)
      | ~ l1_waybel_0(sK3(sK0),sK0)
      | ~ v7_waybel_0(sK3(sK0))
      | ~ v4_orders_2(sK3(sK0))
      | v2_struct_0(sK3(sK0))
      | v1_compts_1(sK0) ) ),
    inference(resolution,[],[f227,f65])).

fof(f227,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_yellow_6(X1,X0,sK3(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_compts_1(X0) ) ),
    inference(subsumption_resolution,[],[f226,f76])).

fof(f226,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m2_yellow_6(X1,X0,sK3(X0))
      | v2_struct_0(sK3(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_compts_1(X0) ) ),
    inference(subsumption_resolution,[],[f225,f77])).

fof(f225,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m2_yellow_6(X1,X0,sK3(X0))
      | ~ v4_orders_2(sK3(X0))
      | v2_struct_0(sK3(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_compts_1(X0) ) ),
    inference(subsumption_resolution,[],[f224,f78])).

fof(f224,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m2_yellow_6(X1,X0,sK3(X0))
      | ~ v7_waybel_0(sK3(X0))
      | ~ v4_orders_2(sK3(X0))
      | v2_struct_0(sK3(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_compts_1(X0) ) ),
    inference(subsumption_resolution,[],[f223,f79])).

fof(f223,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m2_yellow_6(X1,X0,sK3(X0))
      | ~ l1_waybel_0(sK3(X0),X0)
      | ~ v7_waybel_0(sK3(X0))
      | ~ v4_orders_2(sK3(X0))
      | v2_struct_0(sK3(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_compts_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f222])).

fof(f222,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m2_yellow_6(X1,X0,sK3(X0))
      | ~ l1_waybel_0(sK3(X0),X0)
      | ~ v7_waybel_0(sK3(X0))
      | ~ v4_orders_2(sK3(X0))
      | v2_struct_0(sK3(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_compts_1(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f86,f80])).

fof(f80,plain,(
    ! [X2,X0] :
      ( ~ r3_waybel_9(X0,sK3(X0),X2)
      | v1_compts_1(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f86,plain,(
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
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_waybel_9)).

fof(f466,plain,(
    ! [X6,X4,X5] :
      ( r3_waybel_9(X4,X5,sK6(X4,X5,X6))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))
      | ~ l1_waybel_0(X5,X4)
      | ~ v7_waybel_0(X5)
      | ~ v4_orders_2(X5)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | k10_yellow_6(X4,X5) = X6
      | r2_hidden(sK6(X4,X5,X6),X6) ) ),
    inference(subsumption_resolution,[],[f464,f90])).

fof(f464,plain,(
    ! [X6,X4,X5] :
      ( r2_hidden(sK6(X4,X5,X6),X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))
      | ~ l1_waybel_0(X5,X4)
      | ~ v7_waybel_0(X5)
      | ~ v4_orders_2(X5)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | k10_yellow_6(X4,X5) = X6
      | r3_waybel_9(X4,X5,sK6(X4,X5,X6))
      | ~ m1_subset_1(sK6(X4,X5,X6),u1_struct_0(X4)) ) ),
    inference(duplicate_literal_removal,[],[f457])).

fof(f457,plain,(
    ! [X6,X4,X5] :
      ( r2_hidden(sK6(X4,X5,X6),X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))
      | ~ l1_waybel_0(X5,X4)
      | ~ v7_waybel_0(X5)
      | ~ v4_orders_2(X5)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | k10_yellow_6(X4,X5) = X6
      | r3_waybel_9(X4,X5,sK6(X4,X5,X6))
      | ~ m1_subset_1(sK6(X4,X5,X6),u1_struct_0(X4))
      | ~ l1_waybel_0(X5,X4)
      | ~ v7_waybel_0(X5)
      | ~ v4_orders_2(X5)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(resolution,[],[f455,f83])).

fof(f83,plain,(
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
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_waybel_9)).

fof(f455,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),k10_yellow_6(X0,X1))
      | r2_hidden(sK6(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | k10_yellow_6(X0,X1) = X2 ) ),
    inference(subsumption_resolution,[],[f454,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_yellow_6)).

fof(f454,plain,(
    ! [X2,X0,X1] :
      ( k10_yellow_6(X0,X1) = X2
      | r2_hidden(sK6(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | r2_hidden(sK6(X0,X1,X2),k10_yellow_6(X0,X1))
      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(subsumption_resolution,[],[f453,f90])).

fof(f453,plain,(
    ! [X2,X0,X1] :
      ( k10_yellow_6(X0,X1) = X2
      | r2_hidden(sK6(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | r2_hidden(sK6(X0,X1,X2),k10_yellow_6(X0,X1))
      | ~ m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(duplicate_literal_removal,[],[f452])).

fof(f452,plain,(
    ! [X2,X0,X1] :
      ( k10_yellow_6(X0,X1) = X2
      | r2_hidden(sK6(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | r2_hidden(sK6(X0,X1,X2),k10_yellow_6(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | r2_hidden(sK6(X0,X1,X2),k10_yellow_6(X0,X1))
      | ~ m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f431,f102])).

fof(f102,plain,(
    ! [X6,X0,X1] :
      ( ~ r1_waybel_0(X0,X1,sK8(X0,X1,X6))
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
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | ~ r1_waybel_0(X0,X1,sK8(X0,X1,X6))
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
    inference(cnf_transformation,[],[f61])).

fof(f431,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_waybel_0(X0,X1,sK8(X0,X2,sK6(X0,X1,X3)))
      | k10_yellow_6(X0,X1) = X3
      | r2_hidden(sK6(X0,X1,X3),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | r2_hidden(sK6(X0,X1,X3),k10_yellow_6(X0,X2))
      | ~ l1_waybel_0(X2,X0)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f430,f98])).

fof(f430,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_waybel_0(X0,X1,sK8(X0,X2,sK6(X0,X1,X3)))
      | k10_yellow_6(X0,X1) = X3
      | r2_hidden(sK6(X0,X1,X3),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | r2_hidden(sK6(X0,X1,X3),k10_yellow_6(X0,X2))
      | ~ m1_subset_1(k10_yellow_6(X0,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X2,X0)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f429,f90])).

fof(f429,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_waybel_0(X0,X1,sK8(X0,X2,sK6(X0,X1,X3)))
      | k10_yellow_6(X0,X1) = X3
      | r2_hidden(sK6(X0,X1,X3),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | r2_hidden(sK6(X0,X1,X3),k10_yellow_6(X0,X2))
      | ~ m1_subset_1(sK6(X0,X1,X3),u1_struct_0(X0))
      | ~ m1_subset_1(k10_yellow_6(X0,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X2,X0)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2) ) ),
    inference(duplicate_literal_removal,[],[f426])).

fof(f426,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_waybel_0(X0,X1,sK8(X0,X2,sK6(X0,X1,X3)))
      | k10_yellow_6(X0,X1) = X3
      | r2_hidden(sK6(X0,X1,X3),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | r2_hidden(sK6(X0,X1,X3),k10_yellow_6(X0,X2))
      | ~ m1_subset_1(sK6(X0,X1,X3),u1_struct_0(X0))
      | ~ m1_subset_1(k10_yellow_6(X0,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X2,X0)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f91,f103])).

fof(f103,plain,(
    ! [X6,X0,X1] :
      ( m1_connsp_2(sK8(X0,X1,X6),X0,X6)
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
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | m1_connsp_2(sK8(X0,X1,X6),X0,X6)
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
    inference(cnf_transformation,[],[f61])).

fof(f91,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ m1_connsp_2(X5,X0,sK6(X0,X1,X2))
      | r1_waybel_0(X0,X1,X5)
      | k10_yellow_6(X0,X1) = X2
      | r2_hidden(sK6(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f81,plain,(
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
    inference(cnf_transformation,[],[f52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:35:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (21314)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.46  % (21317)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.49  % (21311)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.49  % (21328)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.50  % (21321)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (21312)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  % (21313)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.51  % (21327)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.51  % (21320)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.51  % (21329)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.51  % (21315)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.51  % (21310)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (21329)Refutation not found, incomplete strategy% (21329)------------------------------
% 0.22/0.51  % (21329)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (21329)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (21329)Memory used [KB]: 10618
% 0.22/0.51  % (21329)Time elapsed: 0.096 s
% 0.22/0.51  % (21329)------------------------------
% 0.22/0.51  % (21329)------------------------------
% 0.22/0.51  % (21310)Refutation not found, incomplete strategy% (21310)------------------------------
% 0.22/0.51  % (21310)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (21310)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (21310)Memory used [KB]: 10618
% 0.22/0.51  % (21310)Time elapsed: 0.094 s
% 0.22/0.51  % (21310)------------------------------
% 0.22/0.51  % (21310)------------------------------
% 0.22/0.51  % (21322)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.51  % (21309)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (21323)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.51  % (21319)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.51  % (21318)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 1.30/0.52  % (21316)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 1.30/0.52  % (21326)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 1.30/0.52  % (21325)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 1.30/0.53  % (21324)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 1.30/0.53  % (21324)Refutation not found, incomplete strategy% (21324)------------------------------
% 1.30/0.53  % (21324)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.53  % (21324)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.53  
% 1.30/0.53  % (21324)Memory used [KB]: 6268
% 1.30/0.53  % (21324)Time elapsed: 0.116 s
% 1.30/0.53  % (21324)------------------------------
% 1.30/0.53  % (21324)------------------------------
% 1.30/0.53  % (21327)Refutation found. Thanks to Tanya!
% 1.30/0.53  % SZS status Theorem for theBenchmark
% 1.30/0.53  % SZS output start Proof for theBenchmark
% 1.30/0.53  fof(f608,plain,(
% 1.30/0.53    $false),
% 1.30/0.53    inference(subsumption_resolution,[],[f607,f64])).
% 1.30/0.53  fof(f64,plain,(
% 1.30/0.53    l1_pre_topc(sK0)),
% 1.30/0.53    inference(cnf_transformation,[],[f46])).
% 1.30/0.54  fof(f46,plain,(
% 1.30/0.54    ((! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,sK1)) & l1_waybel_0(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1)) | ~v1_compts_1(sK0)) & (! [X3] : ((v3_yellow_6(sK2(X3),sK0) & m2_yellow_6(sK2(X3),sK0,X3)) | ~l1_waybel_0(X3,sK0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.30/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f42,f45,f44,f43])).
% 1.30/0.54  fof(f43,plain,(
% 1.30/0.54    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ((? [X1] : (! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,X1)) & l1_waybel_0(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(sK0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,sK0) & m2_yellow_6(X4,sK0,X3)) | ~l1_waybel_0(X3,sK0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.30/0.54    introduced(choice_axiom,[])).
% 1.30/0.54  fof(f44,plain,(
% 1.30/0.54    ? [X1] : (! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,X1)) & l1_waybel_0(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,sK1)) & l1_waybel_0(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1))),
% 1.30/0.54    introduced(choice_axiom,[])).
% 1.30/0.54  fof(f45,plain,(
% 1.30/0.54    ! [X3] : (? [X4] : (v3_yellow_6(X4,sK0) & m2_yellow_6(X4,sK0,X3)) => (v3_yellow_6(sK2(X3),sK0) & m2_yellow_6(sK2(X3),sK0,X3)))),
% 1.30/0.54    introduced(choice_axiom,[])).
% 1.30/0.54  fof(f42,plain,(
% 1.30/0.54    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.30/0.54    inference(rectify,[],[f41])).
% 1.30/0.54  fof(f41,plain,(
% 1.30/0.54    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.30/0.54    inference(flattening,[],[f40])).
% 1.30/0.54  fof(f40,plain,(
% 1.30/0.54    ? [X0] : (((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | v1_compts_1(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.30/0.54    inference(nnf_transformation,[],[f18])).
% 1.30/0.54  fof(f18,plain,(
% 1.30/0.54    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.30/0.54    inference(flattening,[],[f17])).
% 1.30/0.54  fof(f17,plain,(
% 1.30/0.54    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.30/0.54    inference(ennf_transformation,[],[f15])).
% 1.30/0.54  fof(f15,negated_conjecture,(
% 1.30/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)))))),
% 1.30/0.54    inference(negated_conjecture,[],[f14])).
% 1.30/0.54  fof(f14,conjecture,(
% 1.30/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)))))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_yellow19)).
% 1.30/0.54  fof(f607,plain,(
% 1.30/0.54    ~l1_pre_topc(sK0)),
% 1.30/0.54    inference(resolution,[],[f602,f73])).
% 1.30/0.54  fof(f73,plain,(
% 1.30/0.54    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f19])).
% 1.30/0.54  fof(f19,plain,(
% 1.30/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.30/0.54    inference(ennf_transformation,[],[f5])).
% 1.30/0.54  fof(f5,axiom,(
% 1.30/0.54    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.30/0.54  fof(f602,plain,(
% 1.30/0.54    ~l1_struct_0(sK0)),
% 1.30/0.54    inference(subsumption_resolution,[],[f601,f62])).
% 1.30/0.54  fof(f62,plain,(
% 1.30/0.54    ~v2_struct_0(sK0)),
% 1.30/0.54    inference(cnf_transformation,[],[f46])).
% 1.30/0.54  fof(f601,plain,(
% 1.30/0.54    ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 1.30/0.54    inference(subsumption_resolution,[],[f600,f63])).
% 1.30/0.54  fof(f63,plain,(
% 1.30/0.54    v2_pre_topc(sK0)),
% 1.30/0.54    inference(cnf_transformation,[],[f46])).
% 1.30/0.54  fof(f600,plain,(
% 1.30/0.54    ~l1_struct_0(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.30/0.54    inference(subsumption_resolution,[],[f599,f64])).
% 1.30/0.54  fof(f599,plain,(
% 1.30/0.54    ~l1_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.30/0.54    inference(subsumption_resolution,[],[f598,f328])).
% 1.30/0.54  fof(f328,plain,(
% 1.30/0.54    ~v1_compts_1(sK0)),
% 1.30/0.54    inference(subsumption_resolution,[],[f327,f67])).
% 1.30/0.54  fof(f67,plain,(
% 1.30/0.54    ~v1_compts_1(sK0) | ~v2_struct_0(sK1)),
% 1.30/0.54    inference(cnf_transformation,[],[f46])).
% 1.30/0.54  fof(f327,plain,(
% 1.30/0.54    ~v1_compts_1(sK0) | v2_struct_0(sK1)),
% 1.30/0.54    inference(subsumption_resolution,[],[f326,f68])).
% 1.30/0.54  fof(f68,plain,(
% 1.30/0.54    ~v1_compts_1(sK0) | v4_orders_2(sK1)),
% 1.30/0.54    inference(cnf_transformation,[],[f46])).
% 1.30/0.54  fof(f326,plain,(
% 1.30/0.54    ~v1_compts_1(sK0) | ~v4_orders_2(sK1) | v2_struct_0(sK1)),
% 1.30/0.54    inference(subsumption_resolution,[],[f325,f69])).
% 1.30/0.54  fof(f69,plain,(
% 1.30/0.54    ~v1_compts_1(sK0) | v7_waybel_0(sK1)),
% 1.30/0.54    inference(cnf_transformation,[],[f46])).
% 1.30/0.54  fof(f325,plain,(
% 1.30/0.54    ~v1_compts_1(sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1)),
% 1.30/0.54    inference(subsumption_resolution,[],[f324,f70])).
% 1.30/0.54  fof(f70,plain,(
% 1.30/0.54    l1_waybel_0(sK1,sK0) | ~v1_compts_1(sK0)),
% 1.30/0.54    inference(cnf_transformation,[],[f46])).
% 1.30/0.54  fof(f324,plain,(
% 1.30/0.54    ~v1_compts_1(sK0) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1)),
% 1.30/0.54    inference(subsumption_resolution,[],[f323,f62])).
% 1.30/0.54  fof(f323,plain,(
% 1.30/0.54    ~v1_compts_1(sK0) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | v2_struct_0(sK0)),
% 1.30/0.54    inference(subsumption_resolution,[],[f322,f63])).
% 1.30/0.54  fof(f322,plain,(
% 1.30/0.54    ~v1_compts_1(sK0) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.30/0.54    inference(subsumption_resolution,[],[f321,f64])).
% 1.30/0.54  fof(f321,plain,(
% 1.30/0.54    ~v1_compts_1(sK0) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.30/0.54    inference(duplicate_literal_removal,[],[f320])).
% 1.30/0.54  fof(f320,plain,(
% 1.30/0.54    ~v1_compts_1(sK0) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.30/0.54    inference(resolution,[],[f304,f74])).
% 1.30/0.54  fof(f74,plain,(
% 1.30/0.54    ( ! [X0,X3] : (m1_subset_1(sK4(X0,X3),u1_struct_0(X0)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f51])).
% 1.30/0.54  fof(f51,plain,(
% 1.30/0.54    ! [X0] : (((v1_compts_1(X0) | (! [X2] : (~r3_waybel_9(X0,sK3(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(sK3(X0),X0) & v7_waybel_0(sK3(X0)) & v4_orders_2(sK3(X0)) & ~v2_struct_0(sK3(X0)))) & (! [X3] : ((r3_waybel_9(X0,X3,sK4(X0,X3)) & m1_subset_1(sK4(X0,X3),u1_struct_0(X0))) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.30/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f48,f50,f49])).
% 1.30/0.54  fof(f49,plain,(
% 1.30/0.54    ! [X0] : (? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (~r3_waybel_9(X0,sK3(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(sK3(X0),X0) & v7_waybel_0(sK3(X0)) & v4_orders_2(sK3(X0)) & ~v2_struct_0(sK3(X0))))),
% 1.30/0.54    introduced(choice_axiom,[])).
% 1.30/0.54  fof(f50,plain,(
% 1.30/0.54    ! [X3,X0] : (? [X4] : (r3_waybel_9(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (r3_waybel_9(X0,X3,sK4(X0,X3)) & m1_subset_1(sK4(X0,X3),u1_struct_0(X0))))),
% 1.30/0.54    introduced(choice_axiom,[])).
% 1.30/0.54  fof(f48,plain,(
% 1.30/0.54    ! [X0] : (((v1_compts_1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (! [X3] : (? [X4] : (r3_waybel_9(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.30/0.54    inference(rectify,[],[f47])).
% 1.30/0.54  fof(f47,plain,(
% 1.30/0.54    ! [X0] : (((v1_compts_1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.30/0.54    inference(nnf_transformation,[],[f21])).
% 1.30/0.54  fof(f21,plain,(
% 1.30/0.54    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.30/0.54    inference(flattening,[],[f20])).
% 1.30/0.54  fof(f20,plain,(
% 1.30/0.54    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.30/0.54    inference(ennf_transformation,[],[f13])).
% 1.30/0.54  fof(f13,axiom,(
% 1.30/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))))))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_yellow19)).
% 1.30/0.54  fof(f304,plain,(
% 1.30/0.54    ~m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | ~v1_compts_1(sK0)),
% 1.30/0.54    inference(subsumption_resolution,[],[f303,f67])).
% 1.30/0.54  fof(f303,plain,(
% 1.30/0.54    ~m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | ~v1_compts_1(sK0) | v2_struct_0(sK1)),
% 1.30/0.54    inference(subsumption_resolution,[],[f302,f68])).
% 1.30/0.54  fof(f302,plain,(
% 1.30/0.54    ~m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | ~v1_compts_1(sK0) | ~v4_orders_2(sK1) | v2_struct_0(sK1)),
% 1.30/0.54    inference(subsumption_resolution,[],[f301,f69])).
% 1.30/0.54  fof(f301,plain,(
% 1.30/0.54    ~m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | ~v1_compts_1(sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1)),
% 1.30/0.54    inference(subsumption_resolution,[],[f300,f70])).
% 1.30/0.54  fof(f300,plain,(
% 1.30/0.54    ~m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | ~v1_compts_1(sK0) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1)),
% 1.30/0.54    inference(subsumption_resolution,[],[f299,f62])).
% 1.30/0.54  fof(f299,plain,(
% 1.30/0.54    ~m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | ~v1_compts_1(sK0) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | v2_struct_0(sK0)),
% 1.30/0.54    inference(subsumption_resolution,[],[f298,f63])).
% 1.30/0.54  fof(f298,plain,(
% 1.30/0.54    ~m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | ~v1_compts_1(sK0) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.30/0.54    inference(subsumption_resolution,[],[f297,f64])).
% 1.30/0.54  fof(f297,plain,(
% 1.30/0.54    ~m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | ~v1_compts_1(sK0) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.30/0.54    inference(duplicate_literal_removal,[],[f293])).
% 1.30/0.54  fof(f293,plain,(
% 1.30/0.54    ~m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | ~v1_compts_1(sK0) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.30/0.54    inference(resolution,[],[f292,f75])).
% 1.30/0.54  fof(f75,plain,(
% 1.30/0.54    ( ! [X0,X3] : (r3_waybel_9(X0,X3,sK4(X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f51])).
% 1.30/0.54  fof(f292,plain,(
% 1.30/0.54    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v1_compts_1(sK0)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f291,f67])).
% 1.30/0.54  fof(f291,plain,(
% 1.30/0.54    ( ! [X0] : (v2_struct_0(sK1) | ~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v1_compts_1(sK0)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f290,f68])).
% 1.30/0.54  fof(f290,plain,(
% 1.30/0.54    ( ! [X0] : (~v4_orders_2(sK1) | v2_struct_0(sK1) | ~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v1_compts_1(sK0)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f289,f69])).
% 1.30/0.54  fof(f289,plain,(
% 1.30/0.54    ( ! [X0] : (~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v1_compts_1(sK0)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f288,f70])).
% 1.30/0.54  fof(f288,plain,(
% 1.30/0.54    ( ! [X0] : (~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v1_compts_1(sK0)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f287,f62])).
% 1.30/0.54  fof(f287,plain,(
% 1.30/0.54    ( ! [X0] : (~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | v2_struct_0(sK0) | ~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v1_compts_1(sK0)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f286,f63])).
% 1.30/0.54  fof(f286,plain,(
% 1.30/0.54    ( ! [X0] : (~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v1_compts_1(sK0)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f285,f64])).
% 1.30/0.54  fof(f285,plain,(
% 1.30/0.54    ( ! [X0] : (~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v1_compts_1(sK0)) )),
% 1.30/0.54    inference(duplicate_literal_removal,[],[f284])).
% 1.30/0.54  fof(f284,plain,(
% 1.30/0.54    ( ! [X0] : (~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X0) | ~v1_compts_1(sK0)) )),
% 1.30/0.54    inference(resolution,[],[f276,f190])).
% 1.30/0.54  fof(f190,plain,(
% 1.30/0.54    ( ! [X0] : (~v3_yellow_6(sK5(sK0,sK1,X0),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X0) | ~v1_compts_1(sK0)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f189,f67])).
% 1.30/0.54  fof(f189,plain,(
% 1.30/0.54    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK1) | ~v3_yellow_6(sK5(sK0,sK1,X0),sK0) | ~v1_compts_1(sK0)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f188,f68])).
% 1.30/0.54  fof(f188,plain,(
% 1.30/0.54    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v3_yellow_6(sK5(sK0,sK1,X0),sK0) | ~v1_compts_1(sK0)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f187,f69])).
% 1.30/0.54  fof(f187,plain,(
% 1.30/0.54    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v3_yellow_6(sK5(sK0,sK1,X0),sK0) | ~v1_compts_1(sK0)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f186,f70])).
% 1.30/0.54  fof(f186,plain,(
% 1.30/0.54    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v3_yellow_6(sK5(sK0,sK1,X0),sK0) | ~v1_compts_1(sK0)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f185,f62])).
% 1.30/0.54  fof(f185,plain,(
% 1.30/0.54    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | v2_struct_0(sK0) | ~v3_yellow_6(sK5(sK0,sK1,X0),sK0) | ~v1_compts_1(sK0)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f184,f63])).
% 1.30/0.54  fof(f184,plain,(
% 1.30/0.54    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~v3_yellow_6(sK5(sK0,sK1,X0),sK0) | ~v1_compts_1(sK0)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f175,f64])).
% 1.30/0.54  fof(f175,plain,(
% 1.30/0.54    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~v3_yellow_6(sK5(sK0,sK1,X0),sK0) | ~v1_compts_1(sK0)) )),
% 1.30/0.54    inference(resolution,[],[f84,f71])).
% 1.30/0.54  fof(f71,plain,(
% 1.30/0.54    ( ! [X2] : (~m2_yellow_6(X2,sK0,sK1) | ~v3_yellow_6(X2,sK0) | ~v1_compts_1(sK0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f46])).
% 1.30/0.54  fof(f84,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (m2_yellow_6(sK5(X0,X1,X2),X0,X1) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f54])).
% 1.30/0.54  fof(f54,plain,(
% 1.30/0.54    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k10_yellow_6(X0,sK5(X0,X1,X2))) & m2_yellow_6(sK5(X0,X1,X2),X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.30/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f27,f53])).
% 1.30/0.54  fof(f53,plain,(
% 1.30/0.54    ! [X2,X1,X0] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) => (r2_hidden(X2,k10_yellow_6(X0,sK5(X0,X1,X2))) & m2_yellow_6(sK5(X0,X1,X2),X0,X1)))),
% 1.30/0.54    introduced(choice_axiom,[])).
% 1.30/0.54  fof(f27,plain,(
% 1.30/0.54    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.30/0.54    inference(flattening,[],[f26])).
% 1.30/0.54  fof(f26,plain,(
% 1.30/0.54    ! [X0] : (! [X1] : (! [X2] : ((? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.30/0.54    inference(ennf_transformation,[],[f12])).
% 1.30/0.54  fof(f12,axiom,(
% 1.30/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m2_yellow_6(X3,X0,X1) => ~r2_hidden(X2,k10_yellow_6(X0,X3))) & r3_waybel_9(X0,X1,X2)))))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_waybel_9)).
% 1.30/0.54  fof(f276,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (v3_yellow_6(sK5(X0,X1,X2),X0) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f275,f194])).
% 1.30/0.54  fof(f194,plain,(
% 1.30/0.54    ( ! [X12,X10,X11] : (~v2_struct_0(sK5(X10,X11,X12)) | ~m1_subset_1(X12,u1_struct_0(X10)) | ~l1_waybel_0(X11,X10) | ~v7_waybel_0(X11) | ~v4_orders_2(X11) | v2_struct_0(X11) | ~l1_pre_topc(X10) | ~v2_pre_topc(X10) | v2_struct_0(X10) | ~r3_waybel_9(X10,X11,X12)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f180,f73])).
% 1.30/0.54  fof(f180,plain,(
% 1.30/0.54    ( ! [X12,X10,X11] : (~r3_waybel_9(X10,X11,X12) | ~m1_subset_1(X12,u1_struct_0(X10)) | ~l1_waybel_0(X11,X10) | ~v7_waybel_0(X11) | ~v4_orders_2(X11) | v2_struct_0(X11) | ~l1_pre_topc(X10) | ~v2_pre_topc(X10) | v2_struct_0(X10) | ~v2_struct_0(sK5(X10,X11,X12)) | ~l1_struct_0(X10)) )),
% 1.30/0.54    inference(duplicate_literal_removal,[],[f179])).
% 1.30/0.54  fof(f179,plain,(
% 1.30/0.54    ( ! [X12,X10,X11] : (~r3_waybel_9(X10,X11,X12) | ~m1_subset_1(X12,u1_struct_0(X10)) | ~l1_waybel_0(X11,X10) | ~v7_waybel_0(X11) | ~v4_orders_2(X11) | v2_struct_0(X11) | ~l1_pre_topc(X10) | ~v2_pre_topc(X10) | v2_struct_0(X10) | ~v2_struct_0(sK5(X10,X11,X12)) | ~l1_waybel_0(X11,X10) | ~v7_waybel_0(X11) | ~v4_orders_2(X11) | v2_struct_0(X11) | ~l1_struct_0(X10) | v2_struct_0(X10)) )),
% 1.30/0.54    inference(resolution,[],[f84,f94])).
% 1.30/0.54  fof(f94,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (~m2_yellow_6(X2,X0,X1) | ~v2_struct_0(X2) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f33])).
% 1.30/0.54  fof(f33,plain,(
% 1.30/0.54    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.30/0.54    inference(flattening,[],[f32])).
% 1.30/0.54  fof(f32,plain,(
% 1.30/0.54    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.30/0.54    inference(ennf_transformation,[],[f8])).
% 1.30/0.54  fof(f8,axiom,(
% 1.30/0.54    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_yellow_6)).
% 1.30/0.54  fof(f275,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~r3_waybel_9(X0,X1,X2) | v3_yellow_6(sK5(X0,X1,X2),X0) | v2_struct_0(sK5(X0,X1,X2))) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f274,f193])).
% 1.30/0.54  fof(f193,plain,(
% 1.30/0.54    ( ! [X8,X7,X9] : (v4_orders_2(sK5(X7,X8,X9)) | ~m1_subset_1(X9,u1_struct_0(X7)) | ~l1_waybel_0(X8,X7) | ~v7_waybel_0(X8) | ~v4_orders_2(X8) | v2_struct_0(X8) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7) | ~r3_waybel_9(X7,X8,X9)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f181,f73])).
% 1.30/0.54  fof(f181,plain,(
% 1.30/0.54    ( ! [X8,X7,X9] : (~r3_waybel_9(X7,X8,X9) | ~m1_subset_1(X9,u1_struct_0(X7)) | ~l1_waybel_0(X8,X7) | ~v7_waybel_0(X8) | ~v4_orders_2(X8) | v2_struct_0(X8) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7) | v4_orders_2(sK5(X7,X8,X9)) | ~l1_struct_0(X7)) )),
% 1.30/0.54    inference(duplicate_literal_removal,[],[f178])).
% 1.30/0.54  fof(f178,plain,(
% 1.30/0.54    ( ! [X8,X7,X9] : (~r3_waybel_9(X7,X8,X9) | ~m1_subset_1(X9,u1_struct_0(X7)) | ~l1_waybel_0(X8,X7) | ~v7_waybel_0(X8) | ~v4_orders_2(X8) | v2_struct_0(X8) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7) | v4_orders_2(sK5(X7,X8,X9)) | ~l1_waybel_0(X8,X7) | ~v7_waybel_0(X8) | ~v4_orders_2(X8) | v2_struct_0(X8) | ~l1_struct_0(X7) | v2_struct_0(X7)) )),
% 1.30/0.54    inference(resolution,[],[f84,f95])).
% 1.30/0.54  fof(f95,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (~m2_yellow_6(X2,X0,X1) | v4_orders_2(X2) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f33])).
% 1.30/0.54  fof(f274,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~r3_waybel_9(X0,X1,X2) | v3_yellow_6(sK5(X0,X1,X2),X0) | ~v4_orders_2(sK5(X0,X1,X2)) | v2_struct_0(sK5(X0,X1,X2))) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f273,f192])).
% 1.30/0.54  fof(f192,plain,(
% 1.30/0.54    ( ! [X6,X4,X5] : (v7_waybel_0(sK5(X4,X5,X6)) | ~m1_subset_1(X6,u1_struct_0(X4)) | ~l1_waybel_0(X5,X4) | ~v7_waybel_0(X5) | ~v4_orders_2(X5) | v2_struct_0(X5) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4) | ~r3_waybel_9(X4,X5,X6)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f182,f73])).
% 1.30/0.54  fof(f182,plain,(
% 1.30/0.54    ( ! [X6,X4,X5] : (~r3_waybel_9(X4,X5,X6) | ~m1_subset_1(X6,u1_struct_0(X4)) | ~l1_waybel_0(X5,X4) | ~v7_waybel_0(X5) | ~v4_orders_2(X5) | v2_struct_0(X5) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4) | v7_waybel_0(sK5(X4,X5,X6)) | ~l1_struct_0(X4)) )),
% 1.30/0.54    inference(duplicate_literal_removal,[],[f177])).
% 1.30/0.54  fof(f177,plain,(
% 1.30/0.54    ( ! [X6,X4,X5] : (~r3_waybel_9(X4,X5,X6) | ~m1_subset_1(X6,u1_struct_0(X4)) | ~l1_waybel_0(X5,X4) | ~v7_waybel_0(X5) | ~v4_orders_2(X5) | v2_struct_0(X5) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4) | v7_waybel_0(sK5(X4,X5,X6)) | ~l1_waybel_0(X5,X4) | ~v7_waybel_0(X5) | ~v4_orders_2(X5) | v2_struct_0(X5) | ~l1_struct_0(X4) | v2_struct_0(X4)) )),
% 1.30/0.54    inference(resolution,[],[f84,f96])).
% 1.30/0.54  fof(f96,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (~m2_yellow_6(X2,X0,X1) | v7_waybel_0(X2) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f33])).
% 1.30/0.54  fof(f273,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~r3_waybel_9(X0,X1,X2) | v3_yellow_6(sK5(X0,X1,X2),X0) | ~v7_waybel_0(sK5(X0,X1,X2)) | ~v4_orders_2(sK5(X0,X1,X2)) | v2_struct_0(sK5(X0,X1,X2))) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f272,f191])).
% 1.30/0.54  fof(f191,plain,(
% 1.30/0.54    ( ! [X2,X3,X1] : (l1_waybel_0(sK5(X1,X2,X3),X1) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l1_waybel_0(X2,X1) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~r3_waybel_9(X1,X2,X3)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f183,f73])).
% 1.30/0.54  fof(f183,plain,(
% 1.30/0.54    ( ! [X2,X3,X1] : (~r3_waybel_9(X1,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l1_waybel_0(X2,X1) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | l1_waybel_0(sK5(X1,X2,X3),X1) | ~l1_struct_0(X1)) )),
% 1.30/0.54    inference(duplicate_literal_removal,[],[f176])).
% 1.30/0.54  fof(f176,plain,(
% 1.30/0.54    ( ! [X2,X3,X1] : (~r3_waybel_9(X1,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l1_waybel_0(X2,X1) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | l1_waybel_0(sK5(X1,X2,X3),X1) | ~l1_waybel_0(X2,X1) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 1.30/0.54    inference(resolution,[],[f84,f97])).
% 1.30/0.54  fof(f97,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (~m2_yellow_6(X2,X0,X1) | l1_waybel_0(X2,X0) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f33])).
% 1.30/0.54  fof(f272,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~r3_waybel_9(X0,X1,X2) | v3_yellow_6(sK5(X0,X1,X2),X0) | ~l1_waybel_0(sK5(X0,X1,X2),X0) | ~v7_waybel_0(sK5(X0,X1,X2)) | ~v4_orders_2(sK5(X0,X1,X2)) | v2_struct_0(sK5(X0,X1,X2))) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f266,f106])).
% 1.30/0.54  fof(f106,plain,(
% 1.30/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.30/0.54    inference(resolution,[],[f99,f72])).
% 1.30/0.54  fof(f72,plain,(
% 1.30/0.54    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.30/0.54    inference(cnf_transformation,[],[f1])).
% 1.30/0.54  fof(f1,axiom,(
% 1.30/0.54    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.30/0.54  fof(f99,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f36])).
% 1.30/0.54  fof(f36,plain,(
% 1.30/0.54    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 1.30/0.54    inference(ennf_transformation,[],[f16])).
% 1.30/0.54  fof(f16,plain,(
% 1.30/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 1.30/0.54    inference(unused_predicate_definition_removal,[],[f2])).
% 1.30/0.54  fof(f2,axiom,(
% 1.30/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.30/0.54  fof(f266,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (~r1_tarski(k1_xboole_0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~r3_waybel_9(X0,X1,X2) | v3_yellow_6(sK5(X0,X1,X2),X0) | ~l1_waybel_0(sK5(X0,X1,X2),X0) | ~v7_waybel_0(sK5(X0,X1,X2)) | ~v4_orders_2(sK5(X0,X1,X2)) | v2_struct_0(sK5(X0,X1,X2))) )),
% 1.30/0.54    inference(duplicate_literal_removal,[],[f265])).
% 1.30/0.54  fof(f265,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (~r1_tarski(k1_xboole_0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~r3_waybel_9(X0,X1,X2) | v3_yellow_6(sK5(X0,X1,X2),X0) | ~l1_waybel_0(sK5(X0,X1,X2),X0) | ~v7_waybel_0(sK5(X0,X1,X2)) | ~v4_orders_2(sK5(X0,X1,X2)) | v2_struct_0(sK5(X0,X1,X2)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.30/0.54    inference(superposition,[],[f209,f82])).
% 1.30/0.54  fof(f82,plain,(
% 1.30/0.54    ( ! [X0,X1] : (k1_xboole_0 = k10_yellow_6(X0,X1) | v3_yellow_6(X1,X0) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f52])).
% 1.30/0.54  fof(f52,plain,(
% 1.30/0.54    ! [X0] : (! [X1] : (((v3_yellow_6(X1,X0) | k1_xboole_0 = k10_yellow_6(X0,X1)) & (k1_xboole_0 != k10_yellow_6(X0,X1) | ~v3_yellow_6(X1,X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.30/0.54    inference(nnf_transformation,[],[f23])).
% 1.30/0.54  fof(f23,plain,(
% 1.30/0.54    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.30/0.54    inference(flattening,[],[f22])).
% 1.30/0.54  fof(f22,plain,(
% 1.30/0.54    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.30/0.54    inference(ennf_transformation,[],[f9])).
% 1.30/0.54  fof(f9,axiom,(
% 1.30/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1))))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_yellow_6)).
% 1.30/0.54  fof(f209,plain,(
% 1.30/0.54    ( ! [X6,X8,X7] : (~r1_tarski(k10_yellow_6(X6,sK5(X6,X7,X8)),X8) | ~m1_subset_1(X8,u1_struct_0(X6)) | ~l1_waybel_0(X7,X6) | ~v7_waybel_0(X7) | ~v4_orders_2(X7) | v2_struct_0(X7) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6) | ~r3_waybel_9(X6,X7,X8)) )),
% 1.30/0.54    inference(resolution,[],[f85,f100])).
% 1.30/0.54  fof(f100,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f37])).
% 1.30/0.54  fof(f37,plain,(
% 1.30/0.54    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.30/0.54    inference(ennf_transformation,[],[f4])).
% 1.30/0.54  fof(f4,axiom,(
% 1.30/0.54    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.30/0.54  fof(f85,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,sK5(X0,X1,X2))) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f54])).
% 1.30/0.54  fof(f598,plain,(
% 1.30/0.54    ~l1_struct_0(sK0) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.30/0.54    inference(resolution,[],[f597,f76])).
% 1.30/0.54  fof(f76,plain,(
% 1.30/0.54    ( ! [X0] : (~v2_struct_0(sK3(X0)) | v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f51])).
% 1.30/0.54  fof(f597,plain,(
% 1.30/0.54    v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0)),
% 1.30/0.54    inference(subsumption_resolution,[],[f596,f62])).
% 1.30/0.54  fof(f596,plain,(
% 1.30/0.54    v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 1.30/0.54    inference(subsumption_resolution,[],[f595,f63])).
% 1.30/0.54  fof(f595,plain,(
% 1.30/0.54    v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.30/0.54    inference(subsumption_resolution,[],[f594,f64])).
% 1.30/0.54  fof(f594,plain,(
% 1.30/0.54    v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.30/0.54    inference(subsumption_resolution,[],[f593,f328])).
% 1.30/0.54  fof(f593,plain,(
% 1.30/0.54    v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.30/0.54    inference(resolution,[],[f592,f77])).
% 1.30/0.54  fof(f77,plain,(
% 1.30/0.54    ( ! [X0] : (v4_orders_2(sK3(X0)) | v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f51])).
% 1.30/0.54  fof(f592,plain,(
% 1.30/0.54    ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0)),
% 1.30/0.54    inference(subsumption_resolution,[],[f591,f62])).
% 1.30/0.54  fof(f591,plain,(
% 1.30/0.54    ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 1.30/0.54    inference(subsumption_resolution,[],[f590,f63])).
% 1.30/0.54  fof(f590,plain,(
% 1.30/0.54    ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.30/0.54    inference(subsumption_resolution,[],[f589,f64])).
% 1.30/0.54  fof(f589,plain,(
% 1.30/0.54    ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.30/0.54    inference(subsumption_resolution,[],[f588,f328])).
% 1.30/0.54  fof(f588,plain,(
% 1.30/0.54    ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.30/0.54    inference(resolution,[],[f587,f78])).
% 1.30/0.54  fof(f78,plain,(
% 1.30/0.54    ( ! [X0] : (v7_waybel_0(sK3(X0)) | v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f51])).
% 1.30/0.54  fof(f587,plain,(
% 1.30/0.54    ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0)),
% 1.30/0.54    inference(subsumption_resolution,[],[f586,f328])).
% 1.30/0.54  fof(f586,plain,(
% 1.30/0.54    ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0)),
% 1.30/0.54    inference(duplicate_literal_removal,[],[f585])).
% 1.30/0.54  fof(f585,plain,(
% 1.30/0.54    ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0)),
% 1.30/0.54    inference(resolution,[],[f584,f116])).
% 1.30/0.54  fof(f116,plain,(
% 1.30/0.54    ~v2_struct_0(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0)),
% 1.30/0.54    inference(subsumption_resolution,[],[f115,f62])).
% 1.30/0.54  fof(f115,plain,(
% 1.30/0.54    ~v2_struct_0(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | v2_struct_0(sK0)),
% 1.30/0.54    inference(subsumption_resolution,[],[f114,f63])).
% 1.30/0.54  fof(f114,plain,(
% 1.30/0.54    ~v2_struct_0(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.30/0.54    inference(subsumption_resolution,[],[f113,f64])).
% 1.30/0.54  fof(f113,plain,(
% 1.30/0.54    ~v2_struct_0(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.30/0.54    inference(duplicate_literal_removal,[],[f112])).
% 1.30/0.54  fof(f112,plain,(
% 1.30/0.54    ~v2_struct_0(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.30/0.54    inference(resolution,[],[f110,f79])).
% 1.30/0.54  fof(f79,plain,(
% 1.30/0.54    ( ! [X0] : (l1_waybel_0(sK3(X0),X0) | v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f51])).
% 1.30/0.54  fof(f110,plain,(
% 1.30/0.54    ( ! [X0] : (~l1_waybel_0(X0,sK0) | ~v2_struct_0(sK2(X0)) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v1_compts_1(sK0)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f109,f62])).
% 1.30/0.54  fof(f109,plain,(
% 1.30/0.54    ( ! [X0] : (~v2_struct_0(sK2(X0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | v1_compts_1(sK0)) )),
% 1.30/0.54    inference(duplicate_literal_removal,[],[f108])).
% 1.30/0.54  fof(f108,plain,(
% 1.30/0.54    ( ! [X0] : (~v2_struct_0(sK2(X0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | v1_compts_1(sK0)) )),
% 1.30/0.54    inference(resolution,[],[f94,f65])).
% 1.30/0.54  fof(f65,plain,(
% 1.30/0.54    ( ! [X3] : (m2_yellow_6(sK2(X3),sK0,X3) | ~l1_waybel_0(X3,sK0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | v1_compts_1(sK0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f46])).
% 1.30/0.54  fof(f584,plain,(
% 1.30/0.54    v2_struct_0(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0)),
% 1.30/0.54    inference(subsumption_resolution,[],[f583,f328])).
% 1.30/0.54  fof(f583,plain,(
% 1.30/0.54    v2_struct_0(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0)),
% 1.30/0.54    inference(duplicate_literal_removal,[],[f582])).
% 1.30/0.54  fof(f582,plain,(
% 1.30/0.54    v2_struct_0(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0)),
% 1.30/0.54    inference(resolution,[],[f581,f125])).
% 1.30/0.54  fof(f125,plain,(
% 1.30/0.54    v4_orders_2(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0)),
% 1.30/0.54    inference(subsumption_resolution,[],[f124,f62])).
% 1.30/0.54  fof(f124,plain,(
% 1.30/0.54    v4_orders_2(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | v2_struct_0(sK0)),
% 1.30/0.54    inference(subsumption_resolution,[],[f123,f63])).
% 1.30/0.54  fof(f123,plain,(
% 1.30/0.54    v4_orders_2(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.30/0.54    inference(subsumption_resolution,[],[f122,f64])).
% 1.30/0.54  fof(f122,plain,(
% 1.30/0.54    v4_orders_2(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.30/0.54    inference(duplicate_literal_removal,[],[f121])).
% 1.30/0.54  fof(f121,plain,(
% 1.30/0.54    v4_orders_2(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.30/0.54    inference(resolution,[],[f119,f79])).
% 1.30/0.54  fof(f119,plain,(
% 1.30/0.54    ( ! [X0] : (~l1_waybel_0(X0,sK0) | v4_orders_2(sK2(X0)) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v1_compts_1(sK0)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f118,f62])).
% 1.30/0.54  fof(f118,plain,(
% 1.30/0.54    ( ! [X0] : (v4_orders_2(sK2(X0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | v1_compts_1(sK0)) )),
% 1.30/0.54    inference(duplicate_literal_removal,[],[f117])).
% 1.30/0.54  fof(f117,plain,(
% 1.30/0.54    ( ! [X0] : (v4_orders_2(sK2(X0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | v1_compts_1(sK0)) )),
% 1.30/0.54    inference(resolution,[],[f95,f65])).
% 1.30/0.54  fof(f581,plain,(
% 1.30/0.54    ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0)),
% 1.30/0.54    inference(subsumption_resolution,[],[f580,f328])).
% 1.30/0.54  fof(f580,plain,(
% 1.30/0.54    v2_struct_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0)),
% 1.30/0.54    inference(duplicate_literal_removal,[],[f579])).
% 1.30/0.54  fof(f579,plain,(
% 1.30/0.54    v2_struct_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0)),
% 1.30/0.54    inference(resolution,[],[f578,f134])).
% 1.30/0.54  fof(f134,plain,(
% 1.30/0.54    v7_waybel_0(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0)),
% 1.30/0.54    inference(subsumption_resolution,[],[f133,f62])).
% 1.30/0.54  fof(f133,plain,(
% 1.30/0.54    v7_waybel_0(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | v2_struct_0(sK0)),
% 1.30/0.54    inference(subsumption_resolution,[],[f132,f63])).
% 1.30/0.54  fof(f132,plain,(
% 1.30/0.54    v7_waybel_0(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.30/0.54    inference(subsumption_resolution,[],[f131,f64])).
% 1.30/0.54  fof(f131,plain,(
% 1.30/0.54    v7_waybel_0(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.30/0.54    inference(duplicate_literal_removal,[],[f130])).
% 1.30/0.54  fof(f130,plain,(
% 1.30/0.54    v7_waybel_0(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.30/0.54    inference(resolution,[],[f128,f79])).
% 1.30/0.54  fof(f128,plain,(
% 1.30/0.54    ( ! [X0] : (~l1_waybel_0(X0,sK0) | v7_waybel_0(sK2(X0)) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v1_compts_1(sK0)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f127,f62])).
% 1.30/0.54  fof(f127,plain,(
% 1.30/0.54    ( ! [X0] : (v7_waybel_0(sK2(X0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | v1_compts_1(sK0)) )),
% 1.30/0.54    inference(duplicate_literal_removal,[],[f126])).
% 1.30/0.54  fof(f126,plain,(
% 1.30/0.54    ( ! [X0] : (v7_waybel_0(sK2(X0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | v1_compts_1(sK0)) )),
% 1.30/0.54    inference(resolution,[],[f96,f65])).
% 1.30/0.54  fof(f578,plain,(
% 1.30/0.54    ~v7_waybel_0(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0)),
% 1.30/0.54    inference(subsumption_resolution,[],[f577,f62])).
% 1.30/0.54  fof(f577,plain,(
% 1.30/0.54    ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | ~v7_waybel_0(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 1.30/0.54    inference(subsumption_resolution,[],[f576,f63])).
% 1.30/0.54  fof(f576,plain,(
% 1.30/0.54    ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | ~v7_waybel_0(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.30/0.54    inference(subsumption_resolution,[],[f575,f64])).
% 1.30/0.54  fof(f575,plain,(
% 1.30/0.54    ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | ~v7_waybel_0(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.30/0.54    inference(subsumption_resolution,[],[f574,f328])).
% 1.30/0.54  fof(f574,plain,(
% 1.30/0.54    ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | ~v7_waybel_0(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.30/0.54    inference(resolution,[],[f573,f79])).
% 1.30/0.54  fof(f573,plain,(
% 1.30/0.54    ~l1_waybel_0(sK3(sK0),sK0) | ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | ~v7_waybel_0(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0)),
% 1.30/0.54    inference(subsumption_resolution,[],[f572,f328])).
% 1.30/0.54  fof(f572,plain,(
% 1.30/0.54    ~v7_waybel_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0)),
% 1.30/0.54    inference(duplicate_literal_removal,[],[f571])).
% 1.30/0.54  fof(f571,plain,(
% 1.30/0.54    ~v7_waybel_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0)),
% 1.30/0.54    inference(resolution,[],[f570,f137])).
% 1.30/0.54  fof(f137,plain,(
% 1.30/0.54    ( ! [X0] : (l1_waybel_0(sK2(X0),sK0) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v1_compts_1(sK0)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f136,f62])).
% 1.30/0.54  fof(f136,plain,(
% 1.30/0.54    ( ! [X0] : (l1_waybel_0(sK2(X0),sK0) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | v1_compts_1(sK0)) )),
% 1.30/0.54    inference(duplicate_literal_removal,[],[f135])).
% 1.30/0.54  fof(f135,plain,(
% 1.30/0.54    ( ! [X0] : (l1_waybel_0(sK2(X0),sK0) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | v1_compts_1(sK0)) )),
% 1.30/0.54    inference(resolution,[],[f97,f65])).
% 1.30/0.54  fof(f570,plain,(
% 1.30/0.54    ~l1_waybel_0(sK2(sK3(sK0)),sK0) | ~v7_waybel_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0))),
% 1.30/0.54    inference(subsumption_resolution,[],[f569,f328])).
% 1.30/0.54  fof(f569,plain,(
% 1.30/0.54    ~l1_waybel_0(sK2(sK3(sK0)),sK0) | ~v7_waybel_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | v1_compts_1(sK0)),
% 1.30/0.54    inference(duplicate_literal_removal,[],[f568])).
% 1.30/0.54  fof(f568,plain,(
% 1.30/0.54    ~l1_waybel_0(sK2(sK3(sK0)),sK0) | ~v7_waybel_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | v1_compts_1(sK0)),
% 1.30/0.54    inference(resolution,[],[f555,f66])).
% 1.30/0.54  fof(f66,plain,(
% 1.30/0.54    ( ! [X3] : (v3_yellow_6(sK2(X3),sK0) | ~l1_waybel_0(X3,sK0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | v1_compts_1(sK0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f46])).
% 1.30/0.54  fof(f555,plain,(
% 1.30/0.54    ~v3_yellow_6(sK2(sK3(sK0)),sK0) | ~l1_waybel_0(sK2(sK3(sK0)),sK0) | ~v7_waybel_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0))),
% 1.30/0.54    inference(subsumption_resolution,[],[f554,f62])).
% 1.30/0.54  fof(f554,plain,(
% 1.30/0.54    ~v3_yellow_6(sK2(sK3(sK0)),sK0) | ~l1_waybel_0(sK2(sK3(sK0)),sK0) | ~v7_waybel_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | v2_struct_0(sK0) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0))),
% 1.30/0.54    inference(subsumption_resolution,[],[f553,f63])).
% 1.30/0.54  fof(f553,plain,(
% 1.30/0.54    ~v3_yellow_6(sK2(sK3(sK0)),sK0) | ~l1_waybel_0(sK2(sK3(sK0)),sK0) | ~v7_waybel_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0))),
% 1.30/0.54    inference(subsumption_resolution,[],[f552,f64])).
% 1.30/0.54  fof(f552,plain,(
% 1.30/0.54    ~v3_yellow_6(sK2(sK3(sK0)),sK0) | ~l1_waybel_0(sK2(sK3(sK0)),sK0) | ~v7_waybel_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0))),
% 1.30/0.54    inference(trivial_inequality_removal,[],[f551])).
% 1.30/0.54  fof(f551,plain,(
% 1.30/0.54    k1_xboole_0 != k1_xboole_0 | ~v3_yellow_6(sK2(sK3(sK0)),sK0) | ~l1_waybel_0(sK2(sK3(sK0)),sK0) | ~v7_waybel_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0))),
% 1.30/0.54    inference(duplicate_literal_removal,[],[f532])).
% 1.30/0.54  fof(f532,plain,(
% 1.30/0.54    k1_xboole_0 != k1_xboole_0 | ~v3_yellow_6(sK2(sK3(sK0)),sK0) | ~l1_waybel_0(sK2(sK3(sK0)),sK0) | ~v7_waybel_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | v2_struct_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | ~l1_waybel_0(sK2(sK3(sK0)),sK0) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~v7_waybel_0(sK2(sK3(sK0)))),
% 1.30/0.54    inference(superposition,[],[f81,f531])).
% 1.30/0.54  fof(f531,plain,(
% 1.30/0.54    k1_xboole_0 = k10_yellow_6(sK0,sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | ~l1_waybel_0(sK2(sK3(sK0)),sK0) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~v7_waybel_0(sK2(sK3(sK0)))),
% 1.30/0.54    inference(subsumption_resolution,[],[f528,f72])).
% 1.30/0.54  fof(f528,plain,(
% 1.30/0.54    ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | k1_xboole_0 = k10_yellow_6(sK0,sK2(sK3(sK0))) | ~l1_waybel_0(sK2(sK3(sK0)),sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~v7_waybel_0(sK2(sK3(sK0)))),
% 1.30/0.54    inference(resolution,[],[f514,f106])).
% 1.30/0.54  fof(f514,plain,(
% 1.30/0.54    ( ! [X0] : (~r1_tarski(X0,sK6(sK0,sK2(sK3(sK0)),X0)) | ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | k10_yellow_6(sK0,sK2(sK3(sK0))) = X0 | ~l1_waybel_0(sK2(sK3(sK0)),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~v7_waybel_0(sK2(sK3(sK0)))) )),
% 1.30/0.54    inference(resolution,[],[f512,f100])).
% 1.30/0.54  fof(f512,plain,(
% 1.30/0.54    ( ! [X0] : (r2_hidden(sK6(sK0,sK2(sK3(sK0)),X0),X0) | ~v7_waybel_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | k10_yellow_6(sK0,sK2(sK3(sK0))) = X0 | ~l1_waybel_0(sK2(sK3(sK0)),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0))) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f511,f62])).
% 1.30/0.54  fof(f511,plain,(
% 1.30/0.54    ( ! [X0] : (~l1_waybel_0(sK2(sK3(sK0)),sK0) | ~v7_waybel_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | k10_yellow_6(sK0,sK2(sK3(sK0))) = X0 | r2_hidden(sK6(sK0,sK2(sK3(sK0)),X0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | v2_struct_0(sK0)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f510,f63])).
% 1.30/0.54  fof(f510,plain,(
% 1.30/0.54    ( ! [X0] : (~l1_waybel_0(sK2(sK3(sK0)),sK0) | ~v7_waybel_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | k10_yellow_6(sK0,sK2(sK3(sK0))) = X0 | r2_hidden(sK6(sK0,sK2(sK3(sK0)),X0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f509,f64])).
% 1.30/0.54  fof(f509,plain,(
% 1.30/0.54    ( ! [X0] : (~l1_waybel_0(sK2(sK3(sK0)),sK0) | ~v7_waybel_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | k10_yellow_6(sK0,sK2(sK3(sK0))) = X0 | r2_hidden(sK6(sK0,sK2(sK3(sK0)),X0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.30/0.54    inference(duplicate_literal_removal,[],[f508])).
% 1.30/0.54  fof(f508,plain,(
% 1.30/0.54    ( ! [X0] : (~l1_waybel_0(sK2(sK3(sK0)),sK0) | ~v7_waybel_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | k10_yellow_6(sK0,sK2(sK3(sK0))) = X0 | r2_hidden(sK6(sK0,sK2(sK3(sK0)),X0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | k10_yellow_6(sK0,sK2(sK3(sK0))) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK2(sK3(sK0)),sK0) | ~v7_waybel_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.30/0.54    inference(resolution,[],[f490,f90])).
% 1.30/0.54  fof(f90,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) | k10_yellow_6(X0,X1) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f61])).
% 1.30/0.54  fof(f61,plain,(
% 1.30/0.54    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | (((~r1_waybel_0(X0,X1,sK7(X0,X1,X2)) & m1_connsp_2(sK7(X0,X1,X2),X0,sK6(X0,X1,X2))) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK6(X0,X1,X2))) | r2_hidden(sK6(X0,X1,X2),X2)) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)))) & (! [X6] : (((r2_hidden(X6,X2) | (~r1_waybel_0(X0,X1,sK8(X0,X1,X6)) & m1_connsp_2(sK8(X0,X1,X6),X0,X6))) & (! [X8] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6)) | ~r2_hidden(X6,X2))) | ~m1_subset_1(X6,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.30/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f57,f60,f59,f58])).
% 1.30/0.54  fof(f58,plain,(
% 1.30/0.54    ! [X2,X1,X0] : (? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0))) => ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,sK6(X0,X1,X2))) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK6(X0,X1,X2))) | r2_hidden(sK6(X0,X1,X2),X2)) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))))),
% 1.30/0.54    introduced(choice_axiom,[])).
% 1.30/0.54  fof(f59,plain,(
% 1.30/0.54    ! [X2,X1,X0] : (? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,sK6(X0,X1,X2))) => (~r1_waybel_0(X0,X1,sK7(X0,X1,X2)) & m1_connsp_2(sK7(X0,X1,X2),X0,sK6(X0,X1,X2))))),
% 1.30/0.54    introduced(choice_axiom,[])).
% 1.30/0.54  fof(f60,plain,(
% 1.30/0.54    ! [X6,X1,X0] : (? [X7] : (~r1_waybel_0(X0,X1,X7) & m1_connsp_2(X7,X0,X6)) => (~r1_waybel_0(X0,X1,sK8(X0,X1,X6)) & m1_connsp_2(sK8(X0,X1,X6),X0,X6)))),
% 1.30/0.54    introduced(choice_axiom,[])).
% 1.30/0.54  fof(f57,plain,(
% 1.30/0.54    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X6] : (((r2_hidden(X6,X2) | ? [X7] : (~r1_waybel_0(X0,X1,X7) & m1_connsp_2(X7,X0,X6))) & (! [X8] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6)) | ~r2_hidden(X6,X2))) | ~m1_subset_1(X6,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.30/0.54    inference(rectify,[],[f56])).
% 1.30/0.54  fof(f56,plain,(
% 1.30/0.54    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3))) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.30/0.54    inference(flattening,[],[f55])).
% 1.30/0.54  fof(f55,plain,(
% 1.30/0.54    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : (((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | r2_hidden(X3,X2))) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3))) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.30/0.54    inference(nnf_transformation,[],[f31])).
% 1.30/0.54  fof(f31,plain,(
% 1.30/0.54    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.30/0.54    inference(flattening,[],[f30])).
% 1.30/0.54  fof(f30,plain,(
% 1.30/0.54    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.30/0.54    inference(ennf_transformation,[],[f6])).
% 1.30/0.54  fof(f6,axiom,(
% 1.30/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (k10_yellow_6(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) <=> ! [X4] : (m1_connsp_2(X4,X0,X3) => r1_waybel_0(X0,X1,X4))))))))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_yellow_6)).
% 1.30/0.54  fof(f490,plain,(
% 1.30/0.54    ( ! [X2] : (~m1_subset_1(sK6(sK0,sK2(sK3(sK0)),X2),u1_struct_0(sK0)) | ~l1_waybel_0(sK2(sK3(sK0)),sK0) | ~v7_waybel_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | k10_yellow_6(sK0,sK2(sK3(sK0))) = X2 | r2_hidden(sK6(sK0,sK2(sK3(sK0)),X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0))) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f489,f328])).
% 1.30/0.54  fof(f489,plain,(
% 1.30/0.54    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK2(sK3(sK0)),sK0) | ~v7_waybel_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | k10_yellow_6(sK0,sK2(sK3(sK0))) = X2 | r2_hidden(sK6(sK0,sK2(sK3(sK0)),X2),X2) | ~m1_subset_1(sK6(sK0,sK2(sK3(sK0)),X2),u1_struct_0(sK0)) | v1_compts_1(sK0) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0))) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f488,f62])).
% 1.30/0.54  fof(f488,plain,(
% 1.30/0.54    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK2(sK3(sK0)),sK0) | ~v7_waybel_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | v2_struct_0(sK0) | k10_yellow_6(sK0,sK2(sK3(sK0))) = X2 | r2_hidden(sK6(sK0,sK2(sK3(sK0)),X2),X2) | ~m1_subset_1(sK6(sK0,sK2(sK3(sK0)),X2),u1_struct_0(sK0)) | v1_compts_1(sK0) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0))) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f487,f63])).
% 1.30/0.54  fof(f487,plain,(
% 1.30/0.54    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK2(sK3(sK0)),sK0) | ~v7_waybel_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | k10_yellow_6(sK0,sK2(sK3(sK0))) = X2 | r2_hidden(sK6(sK0,sK2(sK3(sK0)),X2),X2) | ~m1_subset_1(sK6(sK0,sK2(sK3(sK0)),X2),u1_struct_0(sK0)) | v1_compts_1(sK0) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0))) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f474,f64])).
% 1.30/0.54  fof(f474,plain,(
% 1.30/0.54    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK2(sK3(sK0)),sK0) | ~v7_waybel_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | k10_yellow_6(sK0,sK2(sK3(sK0))) = X2 | r2_hidden(sK6(sK0,sK2(sK3(sK0)),X2),X2) | ~m1_subset_1(sK6(sK0,sK2(sK3(sK0)),X2),u1_struct_0(sK0)) | v1_compts_1(sK0) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0))) )),
% 1.30/0.54    inference(resolution,[],[f466,f234])).
% 1.30/0.54  fof(f234,plain,(
% 1.30/0.54    ( ! [X0] : (~r3_waybel_9(sK0,sK2(sK3(sK0)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v1_compts_1(sK0) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0))) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f233,f62])).
% 1.30/0.54  fof(f233,plain,(
% 1.30/0.54    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK2(sK3(sK0)),X0) | v2_struct_0(sK0) | v1_compts_1(sK0) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0))) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f232,f63])).
% 1.30/0.54  fof(f232,plain,(
% 1.30/0.54    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK2(sK3(sK0)),X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | v1_compts_1(sK0) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0))) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f231,f64])).
% 1.30/0.54  fof(f231,plain,(
% 1.30/0.54    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK2(sK3(sK0)),X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | v1_compts_1(sK0) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0))) )),
% 1.30/0.54    inference(duplicate_literal_removal,[],[f228])).
% 1.30/0.54  fof(f228,plain,(
% 1.30/0.54    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK2(sK3(sK0)),X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | v1_compts_1(sK0) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | v1_compts_1(sK0)) )),
% 1.30/0.54    inference(resolution,[],[f227,f65])).
% 1.30/0.54  fof(f227,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (~m2_yellow_6(X1,X0,sK3(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v1_compts_1(X0)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f226,f76])).
% 1.30/0.54  fof(f226,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m2_yellow_6(X1,X0,sK3(X0)) | v2_struct_0(sK3(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v1_compts_1(X0)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f225,f77])).
% 1.30/0.54  fof(f225,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m2_yellow_6(X1,X0,sK3(X0)) | ~v4_orders_2(sK3(X0)) | v2_struct_0(sK3(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v1_compts_1(X0)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f224,f78])).
% 1.30/0.54  fof(f224,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m2_yellow_6(X1,X0,sK3(X0)) | ~v7_waybel_0(sK3(X0)) | ~v4_orders_2(sK3(X0)) | v2_struct_0(sK3(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v1_compts_1(X0)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f223,f79])).
% 1.30/0.54  fof(f223,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m2_yellow_6(X1,X0,sK3(X0)) | ~l1_waybel_0(sK3(X0),X0) | ~v7_waybel_0(sK3(X0)) | ~v4_orders_2(sK3(X0)) | v2_struct_0(sK3(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v1_compts_1(X0)) )),
% 1.30/0.54    inference(duplicate_literal_removal,[],[f222])).
% 1.30/0.54  fof(f222,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m2_yellow_6(X1,X0,sK3(X0)) | ~l1_waybel_0(sK3(X0),X0) | ~v7_waybel_0(sK3(X0)) | ~v4_orders_2(sK3(X0)) | v2_struct_0(sK3(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v1_compts_1(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.30/0.54    inference(resolution,[],[f86,f80])).
% 1.30/0.54  fof(f80,plain,(
% 1.30/0.54    ( ! [X2,X0] : (~r3_waybel_9(X0,sK3(X0),X2) | v1_compts_1(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f51])).
% 1.30/0.54  fof(f86,plain,(
% 1.30/0.54    ( ! [X2,X0,X3,X1] : (r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f29])).
% 1.30/0.54  fof(f29,plain,(
% 1.30/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.30/0.54    inference(flattening,[],[f28])).
% 1.30/0.54  fof(f28,plain,(
% 1.30/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.30/0.54    inference(ennf_transformation,[],[f11])).
% 1.30/0.54  fof(f11,axiom,(
% 1.30/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_waybel_9(X0,X2,X3) => r3_waybel_9(X0,X1,X3))))))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_waybel_9)).
% 1.30/0.54  fof(f466,plain,(
% 1.30/0.54    ( ! [X6,X4,X5] : (r3_waybel_9(X4,X5,sK6(X4,X5,X6)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4))) | ~l1_waybel_0(X5,X4) | ~v7_waybel_0(X5) | ~v4_orders_2(X5) | v2_struct_0(X5) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4) | k10_yellow_6(X4,X5) = X6 | r2_hidden(sK6(X4,X5,X6),X6)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f464,f90])).
% 1.30/0.54  fof(f464,plain,(
% 1.30/0.54    ( ! [X6,X4,X5] : (r2_hidden(sK6(X4,X5,X6),X6) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4))) | ~l1_waybel_0(X5,X4) | ~v7_waybel_0(X5) | ~v4_orders_2(X5) | v2_struct_0(X5) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4) | k10_yellow_6(X4,X5) = X6 | r3_waybel_9(X4,X5,sK6(X4,X5,X6)) | ~m1_subset_1(sK6(X4,X5,X6),u1_struct_0(X4))) )),
% 1.30/0.54    inference(duplicate_literal_removal,[],[f457])).
% 1.30/0.54  fof(f457,plain,(
% 1.30/0.54    ( ! [X6,X4,X5] : (r2_hidden(sK6(X4,X5,X6),X6) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4))) | ~l1_waybel_0(X5,X4) | ~v7_waybel_0(X5) | ~v4_orders_2(X5) | v2_struct_0(X5) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4) | k10_yellow_6(X4,X5) = X6 | r3_waybel_9(X4,X5,sK6(X4,X5,X6)) | ~m1_subset_1(sK6(X4,X5,X6),u1_struct_0(X4)) | ~l1_waybel_0(X5,X4) | ~v7_waybel_0(X5) | ~v4_orders_2(X5) | v2_struct_0(X5) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) )),
% 1.30/0.54    inference(resolution,[],[f455,f83])).
% 1.30/0.54  fof(f83,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,k10_yellow_6(X0,X1)) | r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f25])).
% 1.30/0.54  fof(f25,plain,(
% 1.30/0.54    ! [X0] : (! [X1] : (! [X2] : (r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.30/0.54    inference(flattening,[],[f24])).
% 1.30/0.54  fof(f24,plain,(
% 1.30/0.54    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.30/0.54    inference(ennf_transformation,[],[f10])).
% 1.30/0.54  fof(f10,axiom,(
% 1.30/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,X1)) => r3_waybel_9(X0,X1,X2)))))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_waybel_9)).
% 1.30/0.54  fof(f455,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),k10_yellow_6(X0,X1)) | r2_hidden(sK6(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | k10_yellow_6(X0,X1) = X2) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f454,f98])).
% 1.30/0.54  fof(f98,plain,(
% 1.30/0.54    ( ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f35])).
% 1.30/0.54  fof(f35,plain,(
% 1.30/0.54    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.30/0.54    inference(flattening,[],[f34])).
% 1.30/0.54  fof(f34,plain,(
% 1.30/0.54    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.30/0.54    inference(ennf_transformation,[],[f7])).
% 1.30/0.54  fof(f7,axiom,(
% 1.30/0.54    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_yellow_6)).
% 1.30/0.54  fof(f454,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (k10_yellow_6(X0,X1) = X2 | r2_hidden(sK6(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | r2_hidden(sK6(X0,X1,X2),k10_yellow_6(X0,X1)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f453,f90])).
% 1.30/0.54  fof(f453,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (k10_yellow_6(X0,X1) = X2 | r2_hidden(sK6(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | r2_hidden(sK6(X0,X1,X2),k10_yellow_6(X0,X1)) | ~m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.30/0.54    inference(duplicate_literal_removal,[],[f452])).
% 1.30/0.54  fof(f452,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (k10_yellow_6(X0,X1) = X2 | r2_hidden(sK6(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | r2_hidden(sK6(X0,X1,X2),k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | r2_hidden(sK6(X0,X1,X2),k10_yellow_6(X0,X1)) | ~m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.30/0.54    inference(resolution,[],[f431,f102])).
% 1.30/0.54  fof(f102,plain,(
% 1.30/0.54    ( ! [X6,X0,X1] : (~r1_waybel_0(X0,X1,sK8(X0,X1,X6)) | r2_hidden(X6,k10_yellow_6(X0,X1)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.30/0.54    inference(equality_resolution,[],[f89])).
% 1.30/0.54  fof(f89,plain,(
% 1.30/0.54    ( ! [X6,X2,X0,X1] : (r2_hidden(X6,X2) | ~r1_waybel_0(X0,X1,sK8(X0,X1,X6)) | ~m1_subset_1(X6,u1_struct_0(X0)) | k10_yellow_6(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f61])).
% 1.30/0.54  fof(f431,plain,(
% 1.30/0.54    ( ! [X2,X0,X3,X1] : (r1_waybel_0(X0,X1,sK8(X0,X2,sK6(X0,X1,X3))) | k10_yellow_6(X0,X1) = X3 | r2_hidden(sK6(X0,X1,X3),X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | r2_hidden(sK6(X0,X1,X3),k10_yellow_6(X0,X2)) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f430,f98])).
% 1.30/0.54  fof(f430,plain,(
% 1.30/0.54    ( ! [X2,X0,X3,X1] : (r1_waybel_0(X0,X1,sK8(X0,X2,sK6(X0,X1,X3))) | k10_yellow_6(X0,X1) = X3 | r2_hidden(sK6(X0,X1,X3),X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | r2_hidden(sK6(X0,X1,X3),k10_yellow_6(X0,X2)) | ~m1_subset_1(k10_yellow_6(X0,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f429,f90])).
% 1.30/0.54  fof(f429,plain,(
% 1.30/0.54    ( ! [X2,X0,X3,X1] : (r1_waybel_0(X0,X1,sK8(X0,X2,sK6(X0,X1,X3))) | k10_yellow_6(X0,X1) = X3 | r2_hidden(sK6(X0,X1,X3),X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | r2_hidden(sK6(X0,X1,X3),k10_yellow_6(X0,X2)) | ~m1_subset_1(sK6(X0,X1,X3),u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2)) )),
% 1.30/0.54    inference(duplicate_literal_removal,[],[f426])).
% 1.30/0.54  fof(f426,plain,(
% 1.30/0.54    ( ! [X2,X0,X3,X1] : (r1_waybel_0(X0,X1,sK8(X0,X2,sK6(X0,X1,X3))) | k10_yellow_6(X0,X1) = X3 | r2_hidden(sK6(X0,X1,X3),X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | r2_hidden(sK6(X0,X1,X3),k10_yellow_6(X0,X2)) | ~m1_subset_1(sK6(X0,X1,X3),u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.30/0.54    inference(resolution,[],[f91,f103])).
% 1.30/0.54  fof(f103,plain,(
% 1.30/0.54    ( ! [X6,X0,X1] : (m1_connsp_2(sK8(X0,X1,X6),X0,X6) | r2_hidden(X6,k10_yellow_6(X0,X1)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.30/0.54    inference(equality_resolution,[],[f88])).
% 1.30/0.54  fof(f88,plain,(
% 1.30/0.54    ( ! [X6,X2,X0,X1] : (r2_hidden(X6,X2) | m1_connsp_2(sK8(X0,X1,X6),X0,X6) | ~m1_subset_1(X6,u1_struct_0(X0)) | k10_yellow_6(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f61])).
% 1.30/0.54  fof(f91,plain,(
% 1.30/0.54    ( ! [X2,X0,X5,X1] : (~m1_connsp_2(X5,X0,sK6(X0,X1,X2)) | r1_waybel_0(X0,X1,X5) | k10_yellow_6(X0,X1) = X2 | r2_hidden(sK6(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f61])).
% 1.30/0.54  fof(f81,plain,(
% 1.30/0.54    ( ! [X0,X1] : (k1_xboole_0 != k10_yellow_6(X0,X1) | ~v3_yellow_6(X1,X0) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f52])).
% 1.30/0.54  % SZS output end Proof for theBenchmark
% 1.30/0.54  % (21327)------------------------------
% 1.30/0.54  % (21327)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (21327)Termination reason: Refutation
% 1.30/0.54  
% 1.30/0.54  % (21327)Memory used [KB]: 2046
% 1.30/0.54  % (21327)Time elapsed: 0.106 s
% 1.30/0.54  % (21327)------------------------------
% 1.30/0.54  % (21327)------------------------------
% 1.30/0.54  % (21308)Success in time 0.176 s
%------------------------------------------------------------------------------
