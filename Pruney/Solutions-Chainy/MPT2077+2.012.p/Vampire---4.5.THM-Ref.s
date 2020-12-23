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
% DateTime   : Thu Dec  3 13:23:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  256 (5821 expanded)
%              Number of leaves         :   22 (1704 expanded)
%              Depth                    :   96
%              Number of atoms          : 2351 (69891 expanded)
%              Number of equality atoms :   48 ( 176 expanded)
%              Maximal formula depth    :   29 (  10 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f587,plain,(
    $false ),
    inference(subsumption_resolution,[],[f586,f60])).

fof(f60,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f37,f40,f39,f38])).

fof(f38,plain,
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

fof(f39,plain,
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

fof(f40,plain,(
    ! [X3] :
      ( ? [X4] :
          ( v3_yellow_6(X4,sK0)
          & m2_yellow_6(X4,sK0,X3) )
     => ( v3_yellow_6(sK2(X3),sK0)
        & m2_yellow_6(sK2(X3),sK0,X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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

fof(f586,plain,(
    ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f585,f69])).

fof(f69,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f585,plain,(
    ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f584,f58])).

fof(f58,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f584,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f583,f59])).

fof(f59,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f583,plain,
    ( ~ l1_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f582,f60])).

fof(f582,plain,
    ( ~ l1_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f581,f319])).

fof(f319,plain,(
    ~ v1_compts_1(sK0) ),
    inference(subsumption_resolution,[],[f318,f63])).

fof(f63,plain,
    ( ~ v1_compts_1(sK0)
    | ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f318,plain,
    ( ~ v1_compts_1(sK0)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f317,f64])).

fof(f64,plain,
    ( ~ v1_compts_1(sK0)
    | v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f317,plain,
    ( ~ v1_compts_1(sK0)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f316,f65])).

fof(f65,plain,
    ( ~ v1_compts_1(sK0)
    | v7_waybel_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f316,plain,
    ( ~ v1_compts_1(sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f315,f66])).

fof(f66,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f315,plain,
    ( ~ v1_compts_1(sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f314,f58])).

fof(f314,plain,
    ( ~ v1_compts_1(sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f313,f59])).

fof(f313,plain,
    ( ~ v1_compts_1(sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f312,f60])).

fof(f312,plain,
    ( ~ v1_compts_1(sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f311])).

fof(f311,plain,
    ( ~ v1_compts_1(sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f296,f70])).

fof(f70,plain,(
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
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f43,f45,f44])).

fof(f44,plain,(
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

fof(f45,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( r3_waybel_9(X0,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X3,sK4(X0,X3))
        & m1_subset_1(sK4(X0,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_yellow19)).

fof(f296,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ v1_compts_1(sK0) ),
    inference(subsumption_resolution,[],[f295,f63])).

fof(f295,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ v1_compts_1(sK0)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f294,f64])).

fof(f294,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ v1_compts_1(sK0)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f293,f65])).

fof(f293,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ v1_compts_1(sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f292,f66])).

fof(f292,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ v1_compts_1(sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f291,f58])).

fof(f291,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ v1_compts_1(sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f290,f59])).

fof(f290,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ v1_compts_1(sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f289,f60])).

fof(f289,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ v1_compts_1(sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f284])).

fof(f284,plain,
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
    inference(resolution,[],[f283,f71])).

fof(f71,plain,(
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
    inference(cnf_transformation,[],[f46])).

fof(f283,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f282,f63])).

fof(f282,plain,(
    ! [X0] :
      ( v2_struct_0(sK1)
      | ~ r3_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f281,f64])).

fof(f281,plain,(
    ! [X0] :
      ( ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ r3_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f280,f65])).

fof(f280,plain,(
    ! [X0] :
      ( ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ r3_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f279,f66])).

fof(f279,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ r3_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f278,f58])).

fof(f278,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ r3_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f277,f59])).

fof(f277,plain,(
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
    inference(subsumption_resolution,[],[f276,f60])).

fof(f276,plain,(
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
    inference(duplicate_literal_removal,[],[f275])).

fof(f275,plain,(
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
    inference(resolution,[],[f268,f181])).

fof(f181,plain,(
    ! [X0] :
      ( ~ v3_yellow_6(sK5(sK0,sK1,X0),sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK1,X0)
      | ~ v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f180,f63])).

fof(f180,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK1)
      | ~ v3_yellow_6(sK5(sK0,sK1,X0),sK0)
      | ~ v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f179,f64])).

fof(f179,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ v3_yellow_6(sK5(sK0,sK1,X0),sK0)
      | ~ v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f178,f65])).

fof(f178,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ v3_yellow_6(sK5(sK0,sK1,X0),sK0)
      | ~ v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f177,f66])).

fof(f177,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ v3_yellow_6(sK5(sK0,sK1,X0),sK0)
      | ~ v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f176,f58])).

fof(f176,plain,(
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
    inference(subsumption_resolution,[],[f175,f59])).

fof(f175,plain,(
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
    inference(subsumption_resolution,[],[f166,f60])).

fof(f166,plain,(
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
    inference(resolution,[],[f80,f67])).

fof(f67,plain,(
    ! [X2] :
      ( ~ m2_yellow_6(X2,sK0,sK1)
      | ~ v3_yellow_6(X2,sK0)
      | ~ v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f80,plain,(
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
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f25,f48])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X2,k10_yellow_6(X0,X3))
          & m2_yellow_6(X3,X0,X1) )
     => ( r2_hidden(X2,k10_yellow_6(X0,sK5(X0,X1,X2)))
        & m2_yellow_6(sK5(X0,X1,X2),X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ~ ( ! [X3] :
                      ( m2_yellow_6(X3,X0,X1)
                     => ~ r2_hidden(X2,k10_yellow_6(X0,X3)) )
                  & r3_waybel_9(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_waybel_9)).

fof(f268,plain,(
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
    inference(subsumption_resolution,[],[f267,f185])).

fof(f185,plain,(
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
    inference(subsumption_resolution,[],[f171,f69])).

fof(f171,plain,(
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
    inference(duplicate_literal_removal,[],[f170])).

fof(f170,plain,(
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
    inference(resolution,[],[f80,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_yellow_6(X2,X0,X1)
      | ~ v2_struct_0(X2)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f267,plain,(
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
    inference(subsumption_resolution,[],[f266,f184])).

fof(f184,plain,(
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
    inference(subsumption_resolution,[],[f172,f69])).

fof(f172,plain,(
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
    inference(duplicate_literal_removal,[],[f169])).

fof(f169,plain,(
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
    inference(resolution,[],[f80,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_yellow_6(X2,X0,X1)
      | v4_orders_2(X2)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f266,plain,(
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
    inference(subsumption_resolution,[],[f265,f183])).

fof(f183,plain,(
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
    inference(subsumption_resolution,[],[f173,f69])).

% (20574)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f173,plain,(
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
    inference(duplicate_literal_removal,[],[f168])).

fof(f168,plain,(
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
    inference(resolution,[],[f80,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_yellow_6(X2,X0,X1)
      | v7_waybel_0(X2)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

% (20585)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f265,plain,(
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
    inference(subsumption_resolution,[],[f264,f182])).

fof(f182,plain,(
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
    inference(subsumption_resolution,[],[f174,f69])).

fof(f174,plain,(
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
    inference(duplicate_literal_removal,[],[f167])).

fof(f167,plain,(
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
    inference(resolution,[],[f80,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_yellow_6(X2,X0,X1)
      | l1_waybel_0(X2,X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f264,plain,(
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
    inference(subsumption_resolution,[],[f258,f68])).

fof(f68,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f258,plain,(
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
    inference(duplicate_literal_removal,[],[f257])).

fof(f257,plain,(
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
    inference(superposition,[],[f199,f78])).

fof(f78,plain,(
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
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f199,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(k10_yellow_6(X3,sK5(X3,X4,X5)),X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_waybel_0(X4,X3)
      | ~ v7_waybel_0(X4)
      | ~ v4_orders_2(X4)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ r3_waybel_9(X3,X4,X5) ) ),
    inference(resolution,[],[f81,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f81,plain,(
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
    inference(cnf_transformation,[],[f49])).

fof(f581,plain,
    ( ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f580,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v2_struct_0(sK3(X0))
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f580,plain,
    ( v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f579,f58])).

fof(f579,plain,
    ( v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f578,f59])).

fof(f578,plain,
    ( v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f577,f60])).

fof(f577,plain,
    ( v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f576,f319])).

fof(f576,plain,
    ( v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f575,f73])).

fof(f73,plain,(
    ! [X0] :
      ( v4_orders_2(sK3(X0))
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f575,plain,
    ( ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f574,f58])).

fof(f574,plain,
    ( ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f573,f59])).

% (20573)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f573,plain,
    ( ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f572,f60])).

fof(f572,plain,
    ( ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f571,f319])).

fof(f571,plain,
    ( ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f570,f74])).

fof(f74,plain,(
    ! [X0] :
      ( v7_waybel_0(sK3(X0))
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f570,plain,
    ( ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f569,f319])).

fof(f569,plain,
    ( ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0) ),
    inference(duplicate_literal_removal,[],[f568])).

fof(f568,plain,
    ( ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0) ),
    inference(resolution,[],[f567,f111])).

fof(f111,plain,
    ( ~ v2_struct_0(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0) ),
    inference(subsumption_resolution,[],[f110,f58])).

fof(f110,plain,
    ( ~ v2_struct_0(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f109,f59])).

fof(f109,plain,
    ( ~ v2_struct_0(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f108,f60])).

fof(f108,plain,
    ( ~ v2_struct_0(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f107])).

fof(f107,plain,
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
    inference(resolution,[],[f105,f75])).

fof(f75,plain,(
    ! [X0] :
      ( l1_waybel_0(sK3(X0),X0)
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f105,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ v2_struct_0(sK2(X0))
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(sK0)
      | v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f104,f58])).

fof(f104,plain,(
    ! [X0] :
      ( ~ v2_struct_0(sK2(X0))
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0)
      | v1_compts_1(sK0) ) ),
    inference(duplicate_literal_removal,[],[f103])).

fof(f103,plain,(
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
    inference(resolution,[],[f90,f61])).

fof(f61,plain,(
    ! [X3] :
      ( m2_yellow_6(sK2(X3),sK0,X3)
      | ~ l1_waybel_0(X3,sK0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f567,plain,
    ( v2_struct_0(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f566,f319])).

fof(f566,plain,
    ( v2_struct_0(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0) ),
    inference(duplicate_literal_removal,[],[f565])).

fof(f565,plain,
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
    inference(resolution,[],[f564,f120])).

fof(f120,plain,
    ( v4_orders_2(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0) ),
    inference(subsumption_resolution,[],[f119,f58])).

fof(f119,plain,
    ( v4_orders_2(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f118,f59])).

fof(f118,plain,
    ( v4_orders_2(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f117,f60])).

fof(f117,plain,
    ( v4_orders_2(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f116])).

fof(f116,plain,
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
    inference(resolution,[],[f114,f75])).

fof(f114,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(X0,sK0)
      | v4_orders_2(sK2(X0))
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(sK0)
      | v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f113,f58])).

fof(f113,plain,(
    ! [X0] :
      ( v4_orders_2(sK2(X0))
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0)
      | v1_compts_1(sK0) ) ),
    inference(duplicate_literal_removal,[],[f112])).

fof(f112,plain,(
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
    inference(resolution,[],[f91,f61])).

fof(f564,plain,
    ( ~ v4_orders_2(sK2(sK3(sK0)))
    | v2_struct_0(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f563,f319])).

fof(f563,plain,
    ( v2_struct_0(sK2(sK3(sK0)))
    | ~ v4_orders_2(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0) ),
    inference(duplicate_literal_removal,[],[f562])).

fof(f562,plain,
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
    inference(resolution,[],[f561,f129])).

fof(f129,plain,
    ( v7_waybel_0(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0) ),
    inference(subsumption_resolution,[],[f128,f58])).

fof(f128,plain,
    ( v7_waybel_0(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f127,f59])).

fof(f127,plain,
    ( v7_waybel_0(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f126,f60])).

fof(f126,plain,
    ( v7_waybel_0(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f125])).

fof(f125,plain,
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
    inference(resolution,[],[f123,f75])).

fof(f123,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(X0,sK0)
      | v7_waybel_0(sK2(X0))
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(sK0)
      | v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f122,f58])).

fof(f122,plain,(
    ! [X0] :
      ( v7_waybel_0(sK2(X0))
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0)
      | v1_compts_1(sK0) ) ),
    inference(duplicate_literal_removal,[],[f121])).

fof(f121,plain,(
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
    inference(resolution,[],[f92,f61])).

fof(f561,plain,
    ( ~ v7_waybel_0(sK2(sK3(sK0)))
    | v2_struct_0(sK2(sK3(sK0)))
    | ~ v4_orders_2(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f560,f58])).

fof(f560,plain,
    ( v2_struct_0(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK2(sK3(sK0)))
    | ~ v4_orders_2(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f559,f59])).

fof(f559,plain,
    ( v2_struct_0(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK2(sK3(sK0)))
    | ~ v4_orders_2(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f558,f60])).

fof(f558,plain,
    ( v2_struct_0(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK2(sK3(sK0)))
    | ~ v4_orders_2(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f557,f319])).

fof(f557,plain,
    ( v2_struct_0(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK2(sK3(sK0)))
    | ~ v4_orders_2(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f556,f75])).

fof(f556,plain,
    ( ~ l1_waybel_0(sK3(sK0),sK0)
    | v2_struct_0(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK2(sK3(sK0)))
    | ~ v4_orders_2(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f552,f68])).

fof(f552,plain,
    ( ~ v4_orders_2(sK2(sK3(sK0)))
    | v2_struct_0(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK2(sK3(sK0)))
    | ~ l1_waybel_0(sK3(sK0),sK0)
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | ~ r1_tarski(k1_xboole_0,u1_struct_0(sK0)) ),
    inference(resolution,[],[f550,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f550,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_orders_2(sK2(sK3(sK0)))
    | v2_struct_0(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK2(sK3(sK0)))
    | ~ l1_waybel_0(sK3(sK0),sK0)
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f549,f319])).

fof(f549,plain,
    ( ~ v7_waybel_0(sK2(sK3(sK0)))
    | ~ v4_orders_2(sK2(sK3(sK0)))
    | v2_struct_0(sK2(sK3(sK0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_waybel_0(sK3(sK0),sK0)
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0) ),
    inference(duplicate_literal_removal,[],[f548])).

fof(f548,plain,
    ( ~ v7_waybel_0(sK2(sK3(sK0)))
    | ~ v4_orders_2(sK2(sK3(sK0)))
    | v2_struct_0(sK2(sK3(sK0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
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
    inference(resolution,[],[f547,f132])).

fof(f132,plain,(
    ! [X0] :
      ( l1_waybel_0(sK2(X0),sK0)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(sK0)
      | v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f131,f58])).

fof(f131,plain,(
    ! [X0] :
      ( l1_waybel_0(sK2(X0),sK0)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0)
      | v1_compts_1(sK0) ) ),
    inference(duplicate_literal_removal,[],[f130])).

fof(f130,plain,(
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
    inference(resolution,[],[f93,f61])).

fof(f547,plain,
    ( ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
    | ~ v7_waybel_0(sK2(sK3(sK0)))
    | ~ v4_orders_2(sK2(sK3(sK0)))
    | v2_struct_0(sK2(sK3(sK0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_waybel_0(sK3(sK0),sK0)
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0)) ),
    inference(subsumption_resolution,[],[f546,f319])).

fof(f546,plain,
    ( ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
    | ~ v7_waybel_0(sK2(sK3(sK0)))
    | ~ v4_orders_2(sK2(sK3(sK0)))
    | v2_struct_0(sK2(sK3(sK0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_waybel_0(sK3(sK0),sK0)
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | v1_compts_1(sK0) ),
    inference(duplicate_literal_removal,[],[f545])).

% (20574)Refutation not found, incomplete strategy% (20574)------------------------------
% (20574)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f545,plain,
    ( ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
    | ~ v7_waybel_0(sK2(sK3(sK0)))
    | ~ v4_orders_2(sK2(sK3(sK0)))
    | v2_struct_0(sK2(sK3(sK0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_waybel_0(sK3(sK0),sK0)
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ l1_waybel_0(sK3(sK0),sK0)
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | v1_compts_1(sK0) ),
    inference(resolution,[],[f535,f62])).

% (20574)Termination reason: Refutation not found, incomplete strategy

% (20574)Memory used [KB]: 10618
% (20574)Time elapsed: 0.096 s
% (20574)------------------------------
% (20574)------------------------------
fof(f62,plain,(
    ! [X3] :
      ( v3_yellow_6(sK2(X3),sK0)
      | ~ l1_waybel_0(X3,sK0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f535,plain,
    ( ~ v3_yellow_6(sK2(sK3(sK0)),sK0)
    | ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
    | ~ v7_waybel_0(sK2(sK3(sK0)))
    | ~ v4_orders_2(sK2(sK3(sK0)))
    | v2_struct_0(sK2(sK3(sK0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_waybel_0(sK3(sK0),sK0)
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0)) ),
    inference(subsumption_resolution,[],[f534,f58])).

fof(f534,plain,
    ( ~ v3_yellow_6(sK2(sK3(sK0)),sK0)
    | ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
    | ~ v7_waybel_0(sK2(sK3(sK0)))
    | ~ v4_orders_2(sK2(sK3(sK0)))
    | v2_struct_0(sK2(sK3(sK0)))
    | v2_struct_0(sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_waybel_0(sK3(sK0),sK0)
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0)) ),
    inference(subsumption_resolution,[],[f533,f59])).

fof(f533,plain,
    ( ~ v3_yellow_6(sK2(sK3(sK0)),sK0)
    | ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
    | ~ v7_waybel_0(sK2(sK3(sK0)))
    | ~ v4_orders_2(sK2(sK3(sK0)))
    | v2_struct_0(sK2(sK3(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_waybel_0(sK3(sK0),sK0)
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0)) ),
    inference(subsumption_resolution,[],[f532,f60])).

fof(f532,plain,
    ( ~ v3_yellow_6(sK2(sK3(sK0)),sK0)
    | ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
    | ~ v7_waybel_0(sK2(sK3(sK0)))
    | ~ v4_orders_2(sK2(sK3(sK0)))
    | v2_struct_0(sK2(sK3(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_waybel_0(sK3(sK0),sK0)
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0)) ),
    inference(trivial_inequality_removal,[],[f531])).

fof(f531,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v3_yellow_6(sK2(sK3(sK0)),sK0)
    | ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
    | ~ v7_waybel_0(sK2(sK3(sK0)))
    | ~ v4_orders_2(sK2(sK3(sK0)))
    | v2_struct_0(sK2(sK3(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_waybel_0(sK3(sK0),sK0)
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0)) ),
    inference(duplicate_literal_removal,[],[f514])).

% (20593)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
fof(f514,plain,
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
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_waybel_0(sK3(sK0),sK0)
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ v7_waybel_0(sK2(sK3(sK0))) ),
    inference(superposition,[],[f77,f513])).

fof(f513,plain,
    ( k1_xboole_0 = k10_yellow_6(sK0,sK2(sK3(sK0)))
    | v2_struct_0(sK2(sK3(sK0)))
    | ~ v4_orders_2(sK2(sK3(sK0)))
    | ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_waybel_0(sK3(sK0),sK0)
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ v7_waybel_0(sK2(sK3(sK0))) ),
    inference(resolution,[],[f509,f68])).

fof(f509,plain,(
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
    inference(resolution,[],[f507,f97])).

fof(f507,plain,(
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
    inference(subsumption_resolution,[],[f506,f58])).

fof(f506,plain,(
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
    inference(subsumption_resolution,[],[f505,f59])).

fof(f505,plain,(
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
    inference(subsumption_resolution,[],[f504,f60])).

fof(f504,plain,(
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
    inference(duplicate_literal_removal,[],[f503])).

fof(f503,plain,(
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
    inference(resolution,[],[f485,f86])).

fof(f86,plain,(
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
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f52,f55,f54,f53])).

fof(f53,plain,(
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

fof(f54,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_waybel_0(X0,X1,X4)
          & m1_connsp_2(X4,X0,sK6(X0,X1,X2)) )
     => ( ~ r1_waybel_0(X0,X1,sK7(X0,X1,X2))
        & m1_connsp_2(sK7(X0,X1,X2),X0,sK6(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X6,X1,X0] :
      ( ? [X7] :
          ( ~ r1_waybel_0(X0,X1,X7)
          & m1_connsp_2(X7,X0,X6) )
     => ( ~ r1_waybel_0(X0,X1,sK8(X0,X1,X6))
        & m1_connsp_2(sK8(X0,X1,X6),X0,X6) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
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
    inference(rectify,[],[f51])).

fof(f51,plain,(
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
    inference(flattening,[],[f50])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f485,plain,(
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
    inference(subsumption_resolution,[],[f484,f319])).

fof(f484,plain,(
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
    inference(subsumption_resolution,[],[f483,f58])).

fof(f483,plain,(
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
    inference(subsumption_resolution,[],[f482,f59])).

fof(f482,plain,(
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
    inference(subsumption_resolution,[],[f469,f60])).

fof(f469,plain,(
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
    inference(resolution,[],[f456,f223])).

fof(f223,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK2(sK3(sK0)),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v1_compts_1(sK0)
      | ~ l1_waybel_0(sK3(sK0),sK0)
      | ~ v7_waybel_0(sK3(sK0))
      | ~ v4_orders_2(sK3(sK0))
      | v2_struct_0(sK3(sK0)) ) ),
    inference(subsumption_resolution,[],[f222,f58])).

fof(f222,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK2(sK3(sK0)),X0)
      | v2_struct_0(sK0)
      | v1_compts_1(sK0)
      | ~ l1_waybel_0(sK3(sK0),sK0)
      | ~ v7_waybel_0(sK3(sK0))
      | ~ v4_orders_2(sK3(sK0))
      | v2_struct_0(sK3(sK0)) ) ),
    inference(subsumption_resolution,[],[f221,f59])).

fof(f221,plain,(
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
    inference(subsumption_resolution,[],[f220,f60])).

fof(f220,plain,(
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
    inference(duplicate_literal_removal,[],[f217])).

fof(f217,plain,(
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
    inference(resolution,[],[f216,f61])).

fof(f216,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_yellow_6(X1,X0,sK3(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_compts_1(X0) ) ),
    inference(subsumption_resolution,[],[f215,f72])).

fof(f215,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m2_yellow_6(X1,X0,sK3(X0))
      | v2_struct_0(sK3(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_compts_1(X0) ) ),
    inference(subsumption_resolution,[],[f214,f73])).

fof(f214,plain,(
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
    inference(subsumption_resolution,[],[f213,f74])).

fof(f213,plain,(
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
    inference(subsumption_resolution,[],[f212,f75])).

fof(f212,plain,(
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
    inference(duplicate_literal_removal,[],[f211])).

fof(f211,plain,(
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
    inference(resolution,[],[f82,f76])).

fof(f76,plain,(
    ! [X2,X0] :
      ( ~ r3_waybel_9(X0,sK3(X0),X2)
      | v1_compts_1(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f82,plain,(
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
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
              ( m2_yellow_6(X2,X0,X1)
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r3_waybel_9(X0,X2,X3)
                   => r3_waybel_9(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_waybel_9)).

fof(f456,plain,(
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
    inference(subsumption_resolution,[],[f454,f86])).

fof(f454,plain,(
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
    inference(duplicate_literal_removal,[],[f449])).

fof(f449,plain,(
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
    inference(resolution,[],[f447,f79])).

fof(f79,plain,(
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
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k10_yellow_6(X0,X1))
               => r3_waybel_9(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_waybel_9)).

fof(f447,plain,(
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
    inference(subsumption_resolution,[],[f446,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f446,plain,(
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
    inference(subsumption_resolution,[],[f445,f86])).

fof(f445,plain,(
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
    inference(duplicate_literal_removal,[],[f444])).

fof(f444,plain,(
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
    inference(resolution,[],[f422,f98])).

% (20593)Refutation not found, incomplete strategy% (20593)------------------------------
% (20593)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (20593)Termination reason: Refutation not found, incomplete strategy

% (20593)Memory used [KB]: 10618
% (20593)Time elapsed: 0.100 s
% (20593)------------------------------
% (20593)------------------------------
fof(f98,plain,(
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
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
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
    inference(cnf_transformation,[],[f56])).

fof(f422,plain,(
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
    inference(subsumption_resolution,[],[f421,f94])).

fof(f421,plain,(
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
    inference(subsumption_resolution,[],[f420,f86])).

fof(f420,plain,(
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
    inference(duplicate_literal_removal,[],[f417])).

fof(f417,plain,(
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
    inference(resolution,[],[f87,f99])).

fof(f99,plain,(
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
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
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
    inference(cnf_transformation,[],[f56])).

fof(f87,plain,(
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
    inference(cnf_transformation,[],[f56])).

fof(f77,plain,(
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
    inference(cnf_transformation,[],[f47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:40:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.45  % (20583)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.45  % (20591)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.46  % (20578)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.46  % (20581)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.47  % (20575)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.48  % (20587)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (20577)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (20580)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (20579)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (20586)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (20576)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (20591)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % (20582)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (20583)Refutation not found, incomplete strategy% (20583)------------------------------
% 0.21/0.49  % (20583)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (20583)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (20583)Memory used [KB]: 6652
% 0.21/0.49  % (20583)Time elapsed: 0.076 s
% 0.21/0.49  % (20583)------------------------------
% 0.21/0.49  % (20583)------------------------------
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f587,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(subsumption_resolution,[],[f586,f60])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    l1_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ((! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,sK1)) & l1_waybel_0(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1)) | ~v1_compts_1(sK0)) & (! [X3] : ((v3_yellow_6(sK2(X3),sK0) & m2_yellow_6(sK2(X3),sK0,X3)) | ~l1_waybel_0(X3,sK0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f37,f40,f39,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ((? [X1] : (! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,X1)) & l1_waybel_0(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(sK0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,sK0) & m2_yellow_6(X4,sK0,X3)) | ~l1_waybel_0(X3,sK0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ? [X1] : (! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,X1)) & l1_waybel_0(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,sK1)) & l1_waybel_0(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ! [X3] : (? [X4] : (v3_yellow_6(X4,sK0) & m2_yellow_6(X4,sK0,X3)) => (v3_yellow_6(sK2(X3),sK0) & m2_yellow_6(sK2(X3),sK0,X3)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.49    inference(rectify,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ? [X0] : (((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | v1_compts_1(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)))))),
% 0.21/0.49    inference(negated_conjecture,[],[f13])).
% 0.21/0.49  fof(f13,conjecture,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_yellow19)).
% 0.21/0.49  fof(f586,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0)),
% 0.21/0.49    inference(resolution,[],[f585,f69])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.49  fof(f585,plain,(
% 0.21/0.49    ~l1_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f584,f58])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ~v2_struct_0(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f41])).
% 0.21/0.49  fof(f584,plain,(
% 0.21/0.49    ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f583,f59])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    v2_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f41])).
% 0.21/0.49  fof(f583,plain,(
% 0.21/0.49    ~l1_struct_0(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f582,f60])).
% 0.21/0.49  fof(f582,plain,(
% 0.21/0.49    ~l1_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f581,f319])).
% 0.21/0.49  fof(f319,plain,(
% 0.21/0.49    ~v1_compts_1(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f318,f63])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ~v1_compts_1(sK0) | ~v2_struct_0(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f41])).
% 0.21/0.49  fof(f318,plain,(
% 0.21/0.49    ~v1_compts_1(sK0) | v2_struct_0(sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f317,f64])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ~v1_compts_1(sK0) | v4_orders_2(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f41])).
% 0.21/0.49  fof(f317,plain,(
% 0.21/0.49    ~v1_compts_1(sK0) | ~v4_orders_2(sK1) | v2_struct_0(sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f316,f65])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    ~v1_compts_1(sK0) | v7_waybel_0(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f41])).
% 0.21/0.49  fof(f316,plain,(
% 0.21/0.49    ~v1_compts_1(sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f315,f66])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    l1_waybel_0(sK1,sK0) | ~v1_compts_1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f41])).
% 0.21/0.49  fof(f315,plain,(
% 0.21/0.49    ~v1_compts_1(sK0) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f314,f58])).
% 0.21/0.49  fof(f314,plain,(
% 0.21/0.49    ~v1_compts_1(sK0) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f313,f59])).
% 0.21/0.49  fof(f313,plain,(
% 0.21/0.49    ~v1_compts_1(sK0) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f312,f60])).
% 0.21/0.49  fof(f312,plain,(
% 0.21/0.49    ~v1_compts_1(sK0) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f311])).
% 0.21/0.49  fof(f311,plain,(
% 0.21/0.49    ~v1_compts_1(sK0) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(resolution,[],[f296,f70])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    ( ! [X0,X3] : (m1_subset_1(sK4(X0,X3),u1_struct_0(X0)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ! [X0] : (((v1_compts_1(X0) | (! [X2] : (~r3_waybel_9(X0,sK3(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(sK3(X0),X0) & v7_waybel_0(sK3(X0)) & v4_orders_2(sK3(X0)) & ~v2_struct_0(sK3(X0)))) & (! [X3] : ((r3_waybel_9(X0,X3,sK4(X0,X3)) & m1_subset_1(sK4(X0,X3),u1_struct_0(X0))) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f43,f45,f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ! [X0] : (? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (~r3_waybel_9(X0,sK3(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(sK3(X0),X0) & v7_waybel_0(sK3(X0)) & v4_orders_2(sK3(X0)) & ~v2_struct_0(sK3(X0))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ! [X3,X0] : (? [X4] : (r3_waybel_9(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (r3_waybel_9(X0,X3,sK4(X0,X3)) & m1_subset_1(sK4(X0,X3),u1_struct_0(X0))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ! [X0] : (((v1_compts_1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (! [X3] : (? [X4] : (r3_waybel_9(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(rectify,[],[f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ! [X0] : (((v1_compts_1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_yellow19)).
% 0.21/0.49  fof(f296,plain,(
% 0.21/0.49    ~m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | ~v1_compts_1(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f295,f63])).
% 0.21/0.49  fof(f295,plain,(
% 0.21/0.49    ~m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | ~v1_compts_1(sK0) | v2_struct_0(sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f294,f64])).
% 0.21/0.49  fof(f294,plain,(
% 0.21/0.49    ~m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | ~v1_compts_1(sK0) | ~v4_orders_2(sK1) | v2_struct_0(sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f293,f65])).
% 0.21/0.49  fof(f293,plain,(
% 0.21/0.49    ~m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | ~v1_compts_1(sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f292,f66])).
% 0.21/0.49  fof(f292,plain,(
% 0.21/0.49    ~m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | ~v1_compts_1(sK0) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f291,f58])).
% 0.21/0.49  fof(f291,plain,(
% 0.21/0.49    ~m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | ~v1_compts_1(sK0) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f290,f59])).
% 0.21/0.49  fof(f290,plain,(
% 0.21/0.49    ~m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | ~v1_compts_1(sK0) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f289,f60])).
% 0.21/0.49  fof(f289,plain,(
% 0.21/0.49    ~m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | ~v1_compts_1(sK0) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f284])).
% 0.21/0.49  fof(f284,plain,(
% 0.21/0.49    ~m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | ~v1_compts_1(sK0) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(resolution,[],[f283,f71])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    ( ! [X0,X3] : (r3_waybel_9(X0,X3,sK4(X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f46])).
% 0.21/0.49  fof(f283,plain,(
% 0.21/0.49    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v1_compts_1(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f282,f63])).
% 0.21/0.49  fof(f282,plain,(
% 0.21/0.49    ( ! [X0] : (v2_struct_0(sK1) | ~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v1_compts_1(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f281,f64])).
% 0.21/0.49  fof(f281,plain,(
% 0.21/0.49    ( ! [X0] : (~v4_orders_2(sK1) | v2_struct_0(sK1) | ~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v1_compts_1(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f280,f65])).
% 0.21/0.49  fof(f280,plain,(
% 0.21/0.49    ( ! [X0] : (~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v1_compts_1(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f279,f66])).
% 0.21/0.49  fof(f279,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v1_compts_1(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f278,f58])).
% 0.21/0.49  fof(f278,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | v2_struct_0(sK0) | ~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v1_compts_1(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f277,f59])).
% 0.21/0.49  fof(f277,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v1_compts_1(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f276,f60])).
% 0.21/0.49  fof(f276,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v1_compts_1(sK0)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f275])).
% 0.21/0.49  fof(f275,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X0) | ~v1_compts_1(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f268,f181])).
% 0.21/0.49  fof(f181,plain,(
% 0.21/0.49    ( ! [X0] : (~v3_yellow_6(sK5(sK0,sK1,X0),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X0) | ~v1_compts_1(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f180,f63])).
% 0.21/0.49  fof(f180,plain,(
% 0.21/0.49    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK1) | ~v3_yellow_6(sK5(sK0,sK1,X0),sK0) | ~v1_compts_1(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f179,f64])).
% 0.21/0.49  fof(f179,plain,(
% 0.21/0.49    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v3_yellow_6(sK5(sK0,sK1,X0),sK0) | ~v1_compts_1(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f178,f65])).
% 0.21/0.49  fof(f178,plain,(
% 0.21/0.49    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v3_yellow_6(sK5(sK0,sK1,X0),sK0) | ~v1_compts_1(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f177,f66])).
% 0.21/0.49  fof(f177,plain,(
% 0.21/0.49    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v3_yellow_6(sK5(sK0,sK1,X0),sK0) | ~v1_compts_1(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f176,f58])).
% 0.21/0.49  fof(f176,plain,(
% 0.21/0.49    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | v2_struct_0(sK0) | ~v3_yellow_6(sK5(sK0,sK1,X0),sK0) | ~v1_compts_1(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f175,f59])).
% 0.21/0.49  fof(f175,plain,(
% 0.21/0.49    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~v3_yellow_6(sK5(sK0,sK1,X0),sK0) | ~v1_compts_1(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f166,f60])).
% 0.21/0.49  fof(f166,plain,(
% 0.21/0.49    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~v3_yellow_6(sK5(sK0,sK1,X0),sK0) | ~v1_compts_1(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f80,f67])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    ( ! [X2] : (~m2_yellow_6(X2,sK0,sK1) | ~v3_yellow_6(X2,sK0) | ~v1_compts_1(sK0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f41])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m2_yellow_6(sK5(X0,X1,X2),X0,X1) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k10_yellow_6(X0,sK5(X0,X1,X2))) & m2_yellow_6(sK5(X0,X1,X2),X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f25,f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ! [X2,X1,X0] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) => (r2_hidden(X2,k10_yellow_6(X0,sK5(X0,X1,X2))) & m2_yellow_6(sK5(X0,X1,X2),X0,X1)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m2_yellow_6(X3,X0,X1) => ~r2_hidden(X2,k10_yellow_6(X0,X3))) & r3_waybel_9(X0,X1,X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_waybel_9)).
% 0.21/0.49  fof(f268,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v3_yellow_6(sK5(X0,X1,X2),X0) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f267,f185])).
% 0.21/0.49  fof(f185,plain,(
% 0.21/0.49    ( ! [X12,X10,X11] : (~v2_struct_0(sK5(X10,X11,X12)) | ~m1_subset_1(X12,u1_struct_0(X10)) | ~l1_waybel_0(X11,X10) | ~v7_waybel_0(X11) | ~v4_orders_2(X11) | v2_struct_0(X11) | ~l1_pre_topc(X10) | ~v2_pre_topc(X10) | v2_struct_0(X10) | ~r3_waybel_9(X10,X11,X12)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f171,f69])).
% 0.21/0.49  fof(f171,plain,(
% 0.21/0.49    ( ! [X12,X10,X11] : (~r3_waybel_9(X10,X11,X12) | ~m1_subset_1(X12,u1_struct_0(X10)) | ~l1_waybel_0(X11,X10) | ~v7_waybel_0(X11) | ~v4_orders_2(X11) | v2_struct_0(X11) | ~l1_pre_topc(X10) | ~v2_pre_topc(X10) | v2_struct_0(X10) | ~v2_struct_0(sK5(X10,X11,X12)) | ~l1_struct_0(X10)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f170])).
% 0.21/0.49  fof(f170,plain,(
% 0.21/0.49    ( ! [X12,X10,X11] : (~r3_waybel_9(X10,X11,X12) | ~m1_subset_1(X12,u1_struct_0(X10)) | ~l1_waybel_0(X11,X10) | ~v7_waybel_0(X11) | ~v4_orders_2(X11) | v2_struct_0(X11) | ~l1_pre_topc(X10) | ~v2_pre_topc(X10) | v2_struct_0(X10) | ~v2_struct_0(sK5(X10,X11,X12)) | ~l1_waybel_0(X11,X10) | ~v7_waybel_0(X11) | ~v4_orders_2(X11) | v2_struct_0(X11) | ~l1_struct_0(X10) | v2_struct_0(X10)) )),
% 0.21/0.49    inference(resolution,[],[f80,f90])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m2_yellow_6(X2,X0,X1) | ~v2_struct_0(X2) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_yellow_6)).
% 0.21/0.49  fof(f267,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~r3_waybel_9(X0,X1,X2) | v3_yellow_6(sK5(X0,X1,X2),X0) | v2_struct_0(sK5(X0,X1,X2))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f266,f184])).
% 0.21/0.49  fof(f184,plain,(
% 0.21/0.49    ( ! [X8,X7,X9] : (v4_orders_2(sK5(X7,X8,X9)) | ~m1_subset_1(X9,u1_struct_0(X7)) | ~l1_waybel_0(X8,X7) | ~v7_waybel_0(X8) | ~v4_orders_2(X8) | v2_struct_0(X8) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7) | ~r3_waybel_9(X7,X8,X9)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f172,f69])).
% 0.21/0.49  fof(f172,plain,(
% 0.21/0.49    ( ! [X8,X7,X9] : (~r3_waybel_9(X7,X8,X9) | ~m1_subset_1(X9,u1_struct_0(X7)) | ~l1_waybel_0(X8,X7) | ~v7_waybel_0(X8) | ~v4_orders_2(X8) | v2_struct_0(X8) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7) | v4_orders_2(sK5(X7,X8,X9)) | ~l1_struct_0(X7)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f169])).
% 0.21/0.49  fof(f169,plain,(
% 0.21/0.49    ( ! [X8,X7,X9] : (~r3_waybel_9(X7,X8,X9) | ~m1_subset_1(X9,u1_struct_0(X7)) | ~l1_waybel_0(X8,X7) | ~v7_waybel_0(X8) | ~v4_orders_2(X8) | v2_struct_0(X8) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7) | v4_orders_2(sK5(X7,X8,X9)) | ~l1_waybel_0(X8,X7) | ~v7_waybel_0(X8) | ~v4_orders_2(X8) | v2_struct_0(X8) | ~l1_struct_0(X7) | v2_struct_0(X7)) )),
% 0.21/0.49    inference(resolution,[],[f80,f91])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m2_yellow_6(X2,X0,X1) | v4_orders_2(X2) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f266,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~r3_waybel_9(X0,X1,X2) | v3_yellow_6(sK5(X0,X1,X2),X0) | ~v4_orders_2(sK5(X0,X1,X2)) | v2_struct_0(sK5(X0,X1,X2))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f265,f183])).
% 0.21/0.49  fof(f183,plain,(
% 0.21/0.49    ( ! [X6,X4,X5] : (v7_waybel_0(sK5(X4,X5,X6)) | ~m1_subset_1(X6,u1_struct_0(X4)) | ~l1_waybel_0(X5,X4) | ~v7_waybel_0(X5) | ~v4_orders_2(X5) | v2_struct_0(X5) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4) | ~r3_waybel_9(X4,X5,X6)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f173,f69])).
% 0.21/0.49  % (20574)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  fof(f173,plain,(
% 0.21/0.49    ( ! [X6,X4,X5] : (~r3_waybel_9(X4,X5,X6) | ~m1_subset_1(X6,u1_struct_0(X4)) | ~l1_waybel_0(X5,X4) | ~v7_waybel_0(X5) | ~v4_orders_2(X5) | v2_struct_0(X5) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4) | v7_waybel_0(sK5(X4,X5,X6)) | ~l1_struct_0(X4)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f168])).
% 0.21/0.49  fof(f168,plain,(
% 0.21/0.49    ( ! [X6,X4,X5] : (~r3_waybel_9(X4,X5,X6) | ~m1_subset_1(X6,u1_struct_0(X4)) | ~l1_waybel_0(X5,X4) | ~v7_waybel_0(X5) | ~v4_orders_2(X5) | v2_struct_0(X5) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4) | v7_waybel_0(sK5(X4,X5,X6)) | ~l1_waybel_0(X5,X4) | ~v7_waybel_0(X5) | ~v4_orders_2(X5) | v2_struct_0(X5) | ~l1_struct_0(X4) | v2_struct_0(X4)) )),
% 0.21/0.49    inference(resolution,[],[f80,f92])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m2_yellow_6(X2,X0,X1) | v7_waybel_0(X2) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  % (20585)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  fof(f265,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~r3_waybel_9(X0,X1,X2) | v3_yellow_6(sK5(X0,X1,X2),X0) | ~v7_waybel_0(sK5(X0,X1,X2)) | ~v4_orders_2(sK5(X0,X1,X2)) | v2_struct_0(sK5(X0,X1,X2))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f264,f182])).
% 0.21/0.49  fof(f182,plain,(
% 0.21/0.49    ( ! [X2,X3,X1] : (l1_waybel_0(sK5(X1,X2,X3),X1) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l1_waybel_0(X2,X1) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~r3_waybel_9(X1,X2,X3)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f174,f69])).
% 0.21/0.49  fof(f174,plain,(
% 0.21/0.49    ( ! [X2,X3,X1] : (~r3_waybel_9(X1,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l1_waybel_0(X2,X1) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | l1_waybel_0(sK5(X1,X2,X3),X1) | ~l1_struct_0(X1)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f167])).
% 0.21/0.49  fof(f167,plain,(
% 0.21/0.49    ( ! [X2,X3,X1] : (~r3_waybel_9(X1,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l1_waybel_0(X2,X1) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | l1_waybel_0(sK5(X1,X2,X3),X1) | ~l1_waybel_0(X2,X1) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 0.21/0.49    inference(resolution,[],[f80,f93])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m2_yellow_6(X2,X0,X1) | l1_waybel_0(X2,X0) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f264,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~r3_waybel_9(X0,X1,X2) | v3_yellow_6(sK5(X0,X1,X2),X0) | ~l1_waybel_0(sK5(X0,X1,X2),X0) | ~v7_waybel_0(sK5(X0,X1,X2)) | ~v4_orders_2(sK5(X0,X1,X2)) | v2_struct_0(sK5(X0,X1,X2))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f258,f68])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.49  fof(f258,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_tarski(k1_xboole_0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~r3_waybel_9(X0,X1,X2) | v3_yellow_6(sK5(X0,X1,X2),X0) | ~l1_waybel_0(sK5(X0,X1,X2),X0) | ~v7_waybel_0(sK5(X0,X1,X2)) | ~v4_orders_2(sK5(X0,X1,X2)) | v2_struct_0(sK5(X0,X1,X2))) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f257])).
% 0.21/0.49  fof(f257,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_tarski(k1_xboole_0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~r3_waybel_9(X0,X1,X2) | v3_yellow_6(sK5(X0,X1,X2),X0) | ~l1_waybel_0(sK5(X0,X1,X2),X0) | ~v7_waybel_0(sK5(X0,X1,X2)) | ~v4_orders_2(sK5(X0,X1,X2)) | v2_struct_0(sK5(X0,X1,X2)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(superposition,[],[f199,f78])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_xboole_0 = k10_yellow_6(X0,X1) | v3_yellow_6(X1,X0) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((v3_yellow_6(X1,X0) | k1_xboole_0 = k10_yellow_6(X0,X1)) & (k1_xboole_0 != k10_yellow_6(X0,X1) | ~v3_yellow_6(X1,X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_yellow_6)).
% 0.21/0.49  fof(f199,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (~r1_tarski(k10_yellow_6(X3,sK5(X3,X4,X5)),X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~l1_waybel_0(X4,X3) | ~v7_waybel_0(X4) | ~v4_orders_2(X4) | v2_struct_0(X4) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~r3_waybel_9(X3,X4,X5)) )),
% 0.21/0.49    inference(resolution,[],[f81,f97])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,sK5(X0,X1,X2))) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f49])).
% 0.21/0.49  fof(f581,plain,(
% 0.21/0.49    ~l1_struct_0(sK0) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(resolution,[],[f580,f72])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    ( ! [X0] : (~v2_struct_0(sK3(X0)) | v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f46])).
% 0.21/0.49  fof(f580,plain,(
% 0.21/0.49    v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f579,f58])).
% 0.21/0.49  fof(f579,plain,(
% 0.21/0.49    v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f578,f59])).
% 0.21/0.49  fof(f578,plain,(
% 0.21/0.49    v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f577,f60])).
% 0.21/0.49  fof(f577,plain,(
% 0.21/0.49    v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f576,f319])).
% 0.21/0.49  fof(f576,plain,(
% 0.21/0.49    v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(resolution,[],[f575,f73])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    ( ! [X0] : (v4_orders_2(sK3(X0)) | v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f46])).
% 0.21/0.49  fof(f575,plain,(
% 0.21/0.49    ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f574,f58])).
% 0.21/0.49  fof(f574,plain,(
% 0.21/0.49    ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f573,f59])).
% 0.21/0.49  % (20573)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  fof(f573,plain,(
% 0.21/0.49    ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f572,f60])).
% 0.21/0.49  fof(f572,plain,(
% 0.21/0.49    ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f571,f319])).
% 0.21/0.49  fof(f571,plain,(
% 0.21/0.49    ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(resolution,[],[f570,f74])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    ( ! [X0] : (v7_waybel_0(sK3(X0)) | v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f46])).
% 0.21/0.49  fof(f570,plain,(
% 0.21/0.49    ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f569,f319])).
% 0.21/0.49  fof(f569,plain,(
% 0.21/0.49    ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f568])).
% 0.21/0.49  fof(f568,plain,(
% 0.21/0.49    ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0)),
% 0.21/0.49    inference(resolution,[],[f567,f111])).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    ~v2_struct_0(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f110,f58])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    ~v2_struct_0(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f109,f59])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    ~v2_struct_0(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f108,f60])).
% 0.21/0.49  fof(f108,plain,(
% 0.21/0.49    ~v2_struct_0(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f107])).
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    ~v2_struct_0(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(resolution,[],[f105,f75])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    ( ! [X0] : (l1_waybel_0(sK3(X0),X0) | v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f46])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_waybel_0(X0,sK0) | ~v2_struct_0(sK2(X0)) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v1_compts_1(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f104,f58])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    ( ! [X0] : (~v2_struct_0(sK2(X0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | v1_compts_1(sK0)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f103])).
% 0.21/0.49  fof(f103,plain,(
% 0.21/0.49    ( ! [X0] : (~v2_struct_0(sK2(X0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | v1_compts_1(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f90,f61])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ( ! [X3] : (m2_yellow_6(sK2(X3),sK0,X3) | ~l1_waybel_0(X3,sK0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | v1_compts_1(sK0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f41])).
% 0.21/0.49  fof(f567,plain,(
% 0.21/0.49    v2_struct_0(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f566,f319])).
% 0.21/0.49  fof(f566,plain,(
% 0.21/0.49    v2_struct_0(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f565])).
% 0.21/0.49  fof(f565,plain,(
% 0.21/0.49    v2_struct_0(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0)),
% 0.21/0.49    inference(resolution,[],[f564,f120])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    v4_orders_2(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f119,f58])).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    v4_orders_2(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f118,f59])).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    v4_orders_2(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f117,f60])).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    v4_orders_2(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f116])).
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    v4_orders_2(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(resolution,[],[f114,f75])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_waybel_0(X0,sK0) | v4_orders_2(sK2(X0)) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v1_compts_1(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f113,f58])).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    ( ! [X0] : (v4_orders_2(sK2(X0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | v1_compts_1(sK0)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f112])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    ( ! [X0] : (v4_orders_2(sK2(X0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | v1_compts_1(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f91,f61])).
% 0.21/0.49  fof(f564,plain,(
% 0.21/0.49    ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f563,f319])).
% 0.21/0.49  fof(f563,plain,(
% 0.21/0.49    v2_struct_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f562])).
% 0.21/0.49  fof(f562,plain,(
% 0.21/0.49    v2_struct_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0)),
% 0.21/0.49    inference(resolution,[],[f561,f129])).
% 0.21/0.49  fof(f129,plain,(
% 0.21/0.49    v7_waybel_0(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f128,f58])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    v7_waybel_0(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f127,f59])).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    v7_waybel_0(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f126,f60])).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    v7_waybel_0(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f125])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    v7_waybel_0(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(resolution,[],[f123,f75])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_waybel_0(X0,sK0) | v7_waybel_0(sK2(X0)) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v1_compts_1(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f122,f58])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    ( ! [X0] : (v7_waybel_0(sK2(X0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | v1_compts_1(sK0)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f121])).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    ( ! [X0] : (v7_waybel_0(sK2(X0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | v1_compts_1(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f92,f61])).
% 0.21/0.49  fof(f561,plain,(
% 0.21/0.49    ~v7_waybel_0(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f560,f58])).
% 0.21/0.49  fof(f560,plain,(
% 0.21/0.49    v2_struct_0(sK2(sK3(sK0))) | ~v7_waybel_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f559,f59])).
% 0.21/0.49  fof(f559,plain,(
% 0.21/0.49    v2_struct_0(sK2(sK3(sK0))) | ~v7_waybel_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f558,f60])).
% 0.21/0.49  fof(f558,plain,(
% 0.21/0.49    v2_struct_0(sK2(sK3(sK0))) | ~v7_waybel_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f557,f319])).
% 0.21/0.49  fof(f557,plain,(
% 0.21/0.49    v2_struct_0(sK2(sK3(sK0))) | ~v7_waybel_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(resolution,[],[f556,f75])).
% 0.21/0.49  fof(f556,plain,(
% 0.21/0.49    ~l1_waybel_0(sK3(sK0),sK0) | v2_struct_0(sK2(sK3(sK0))) | ~v7_waybel_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f552,f68])).
% 0.21/0.49  fof(f552,plain,(
% 0.21/0.49    ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | ~v7_waybel_0(sK2(sK3(sK0))) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | ~r1_tarski(k1_xboole_0,u1_struct_0(sK0))),
% 0.21/0.49    inference(resolution,[],[f550,f96])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f57])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.49    inference(nnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.49  fof(f550,plain,(
% 0.21/0.49    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | ~v7_waybel_0(sK2(sK3(sK0))) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f549,f319])).
% 0.21/0.49  fof(f549,plain,(
% 0.21/0.49    ~v7_waybel_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f548])).
% 0.21/0.49  fof(f548,plain,(
% 0.21/0.49    ~v7_waybel_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0)),
% 0.21/0.49    inference(resolution,[],[f547,f132])).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    ( ! [X0] : (l1_waybel_0(sK2(X0),sK0) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v1_compts_1(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f131,f58])).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    ( ! [X0] : (l1_waybel_0(sK2(X0),sK0) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | v1_compts_1(sK0)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f130])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    ( ! [X0] : (l1_waybel_0(sK2(X0),sK0) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | v1_compts_1(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f93,f61])).
% 0.21/0.49  fof(f547,plain,(
% 0.21/0.49    ~l1_waybel_0(sK2(sK3(sK0)),sK0) | ~v7_waybel_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0))),
% 0.21/0.49    inference(subsumption_resolution,[],[f546,f319])).
% 0.21/0.49  fof(f546,plain,(
% 0.21/0.49    ~l1_waybel_0(sK2(sK3(sK0)),sK0) | ~v7_waybel_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | v1_compts_1(sK0)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f545])).
% 0.21/0.49  % (20574)Refutation not found, incomplete strategy% (20574)------------------------------
% 0.21/0.49  % (20574)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  fof(f545,plain,(
% 0.21/0.49    ~l1_waybel_0(sK2(sK3(sK0)),sK0) | ~v7_waybel_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | v1_compts_1(sK0)),
% 0.21/0.49    inference(resolution,[],[f535,f62])).
% 0.21/0.49  % (20574)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (20574)Memory used [KB]: 10618
% 0.21/0.49  % (20574)Time elapsed: 0.096 s
% 0.21/0.49  % (20574)------------------------------
% 0.21/0.49  % (20574)------------------------------
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ( ! [X3] : (v3_yellow_6(sK2(X3),sK0) | ~l1_waybel_0(X3,sK0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | v1_compts_1(sK0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f41])).
% 0.21/0.49  fof(f535,plain,(
% 0.21/0.49    ~v3_yellow_6(sK2(sK3(sK0)),sK0) | ~l1_waybel_0(sK2(sK3(sK0)),sK0) | ~v7_waybel_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0))),
% 0.21/0.49    inference(subsumption_resolution,[],[f534,f58])).
% 0.21/0.49  fof(f534,plain,(
% 0.21/0.49    ~v3_yellow_6(sK2(sK3(sK0)),sK0) | ~l1_waybel_0(sK2(sK3(sK0)),sK0) | ~v7_waybel_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | v2_struct_0(sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0))),
% 0.21/0.49    inference(subsumption_resolution,[],[f533,f59])).
% 0.21/0.49  fof(f533,plain,(
% 0.21/0.49    ~v3_yellow_6(sK2(sK3(sK0)),sK0) | ~l1_waybel_0(sK2(sK3(sK0)),sK0) | ~v7_waybel_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0))),
% 0.21/0.49    inference(subsumption_resolution,[],[f532,f60])).
% 0.21/0.49  fof(f532,plain,(
% 0.21/0.49    ~v3_yellow_6(sK2(sK3(sK0)),sK0) | ~l1_waybel_0(sK2(sK3(sK0)),sK0) | ~v7_waybel_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0))),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f531])).
% 0.21/0.49  fof(f531,plain,(
% 0.21/0.49    k1_xboole_0 != k1_xboole_0 | ~v3_yellow_6(sK2(sK3(sK0)),sK0) | ~l1_waybel_0(sK2(sK3(sK0)),sK0) | ~v7_waybel_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0))),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f514])).
% 0.21/0.49  % (20593)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.49  fof(f514,plain,(
% 0.21/0.49    k1_xboole_0 != k1_xboole_0 | ~v3_yellow_6(sK2(sK3(sK0)),sK0) | ~l1_waybel_0(sK2(sK3(sK0)),sK0) | ~v7_waybel_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | v2_struct_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | ~l1_waybel_0(sK2(sK3(sK0)),sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~v7_waybel_0(sK2(sK3(sK0)))),
% 0.21/0.49    inference(superposition,[],[f77,f513])).
% 0.21/0.49  fof(f513,plain,(
% 0.21/0.49    k1_xboole_0 = k10_yellow_6(sK0,sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | ~l1_waybel_0(sK2(sK3(sK0)),sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~v7_waybel_0(sK2(sK3(sK0)))),
% 0.21/0.49    inference(resolution,[],[f509,f68])).
% 0.21/0.49  fof(f509,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(X0,sK6(sK0,sK2(sK3(sK0)),X0)) | ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | k10_yellow_6(sK0,sK2(sK3(sK0))) = X0 | ~l1_waybel_0(sK2(sK3(sK0)),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~v7_waybel_0(sK2(sK3(sK0)))) )),
% 0.21/0.49    inference(resolution,[],[f507,f97])).
% 0.21/0.49  fof(f507,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(sK6(sK0,sK2(sK3(sK0)),X0),X0) | ~v7_waybel_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | k10_yellow_6(sK0,sK2(sK3(sK0))) = X0 | ~l1_waybel_0(sK2(sK3(sK0)),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f506,f58])).
% 0.21/0.49  fof(f506,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_waybel_0(sK2(sK3(sK0)),sK0) | ~v7_waybel_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | k10_yellow_6(sK0,sK2(sK3(sK0))) = X0 | r2_hidden(sK6(sK0,sK2(sK3(sK0)),X0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f505,f59])).
% 0.21/0.49  fof(f505,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_waybel_0(sK2(sK3(sK0)),sK0) | ~v7_waybel_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | k10_yellow_6(sK0,sK2(sK3(sK0))) = X0 | r2_hidden(sK6(sK0,sK2(sK3(sK0)),X0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f504,f60])).
% 0.21/0.49  fof(f504,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_waybel_0(sK2(sK3(sK0)),sK0) | ~v7_waybel_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | k10_yellow_6(sK0,sK2(sK3(sK0))) = X0 | r2_hidden(sK6(sK0,sK2(sK3(sK0)),X0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f503])).
% 0.21/0.49  fof(f503,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_waybel_0(sK2(sK3(sK0)),sK0) | ~v7_waybel_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | k10_yellow_6(sK0,sK2(sK3(sK0))) = X0 | r2_hidden(sK6(sK0,sK2(sK3(sK0)),X0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | k10_yellow_6(sK0,sK2(sK3(sK0))) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK2(sK3(sK0)),sK0) | ~v7_waybel_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f485,f86])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) | k10_yellow_6(X0,X1) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | (((~r1_waybel_0(X0,X1,sK7(X0,X1,X2)) & m1_connsp_2(sK7(X0,X1,X2),X0,sK6(X0,X1,X2))) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK6(X0,X1,X2))) | r2_hidden(sK6(X0,X1,X2),X2)) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)))) & (! [X6] : (((r2_hidden(X6,X2) | (~r1_waybel_0(X0,X1,sK8(X0,X1,X6)) & m1_connsp_2(sK8(X0,X1,X6),X0,X6))) & (! [X8] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6)) | ~r2_hidden(X6,X2))) | ~m1_subset_1(X6,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f52,f55,f54,f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ! [X2,X1,X0] : (? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0))) => ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,sK6(X0,X1,X2))) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK6(X0,X1,X2))) | r2_hidden(sK6(X0,X1,X2),X2)) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ! [X2,X1,X0] : (? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,sK6(X0,X1,X2))) => (~r1_waybel_0(X0,X1,sK7(X0,X1,X2)) & m1_connsp_2(sK7(X0,X1,X2),X0,sK6(X0,X1,X2))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ! [X6,X1,X0] : (? [X7] : (~r1_waybel_0(X0,X1,X7) & m1_connsp_2(X7,X0,X6)) => (~r1_waybel_0(X0,X1,sK8(X0,X1,X6)) & m1_connsp_2(sK8(X0,X1,X6),X0,X6)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X6] : (((r2_hidden(X6,X2) | ? [X7] : (~r1_waybel_0(X0,X1,X7) & m1_connsp_2(X7,X0,X6))) & (! [X8] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6)) | ~r2_hidden(X6,X2))) | ~m1_subset_1(X6,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(rectify,[],[f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3))) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f50])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : (((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | r2_hidden(X3,X2))) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3))) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (k10_yellow_6(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) <=> ! [X4] : (m1_connsp_2(X4,X0,X3) => r1_waybel_0(X0,X1,X4))))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_yellow_6)).
% 0.21/0.50  fof(f485,plain,(
% 0.21/0.50    ( ! [X2] : (~m1_subset_1(sK6(sK0,sK2(sK3(sK0)),X2),u1_struct_0(sK0)) | ~l1_waybel_0(sK2(sK3(sK0)),sK0) | ~v7_waybel_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | k10_yellow_6(sK0,sK2(sK3(sK0))) = X2 | r2_hidden(sK6(sK0,sK2(sK3(sK0)),X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0))) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f484,f319])).
% 0.21/0.50  fof(f484,plain,(
% 0.21/0.50    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK2(sK3(sK0)),sK0) | ~v7_waybel_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | k10_yellow_6(sK0,sK2(sK3(sK0))) = X2 | r2_hidden(sK6(sK0,sK2(sK3(sK0)),X2),X2) | ~m1_subset_1(sK6(sK0,sK2(sK3(sK0)),X2),u1_struct_0(sK0)) | v1_compts_1(sK0) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0))) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f483,f58])).
% 0.21/0.50  fof(f483,plain,(
% 0.21/0.50    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK2(sK3(sK0)),sK0) | ~v7_waybel_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | v2_struct_0(sK0) | k10_yellow_6(sK0,sK2(sK3(sK0))) = X2 | r2_hidden(sK6(sK0,sK2(sK3(sK0)),X2),X2) | ~m1_subset_1(sK6(sK0,sK2(sK3(sK0)),X2),u1_struct_0(sK0)) | v1_compts_1(sK0) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0))) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f482,f59])).
% 0.21/0.50  fof(f482,plain,(
% 0.21/0.50    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK2(sK3(sK0)),sK0) | ~v7_waybel_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | k10_yellow_6(sK0,sK2(sK3(sK0))) = X2 | r2_hidden(sK6(sK0,sK2(sK3(sK0)),X2),X2) | ~m1_subset_1(sK6(sK0,sK2(sK3(sK0)),X2),u1_struct_0(sK0)) | v1_compts_1(sK0) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0))) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f469,f60])).
% 0.21/0.50  fof(f469,plain,(
% 0.21/0.50    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK2(sK3(sK0)),sK0) | ~v7_waybel_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | k10_yellow_6(sK0,sK2(sK3(sK0))) = X2 | r2_hidden(sK6(sK0,sK2(sK3(sK0)),X2),X2) | ~m1_subset_1(sK6(sK0,sK2(sK3(sK0)),X2),u1_struct_0(sK0)) | v1_compts_1(sK0) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0))) )),
% 0.21/0.50    inference(resolution,[],[f456,f223])).
% 0.21/0.50  fof(f223,plain,(
% 0.21/0.50    ( ! [X0] : (~r3_waybel_9(sK0,sK2(sK3(sK0)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v1_compts_1(sK0) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0))) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f222,f58])).
% 0.21/0.50  fof(f222,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK2(sK3(sK0)),X0) | v2_struct_0(sK0) | v1_compts_1(sK0) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0))) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f221,f59])).
% 0.21/0.50  fof(f221,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK2(sK3(sK0)),X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | v1_compts_1(sK0) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0))) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f220,f60])).
% 0.21/0.50  fof(f220,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK2(sK3(sK0)),X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | v1_compts_1(sK0) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0))) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f217])).
% 0.21/0.50  fof(f217,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK2(sK3(sK0)),X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | v1_compts_1(sK0) | ~l1_waybel_0(sK3(sK0),sK0) | ~v7_waybel_0(sK3(sK0)) | ~v4_orders_2(sK3(sK0)) | v2_struct_0(sK3(sK0)) | v1_compts_1(sK0)) )),
% 0.21/0.50    inference(resolution,[],[f216,f61])).
% 0.21/0.50  fof(f216,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m2_yellow_6(X1,X0,sK3(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v1_compts_1(X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f215,f72])).
% 0.21/0.50  fof(f215,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m2_yellow_6(X1,X0,sK3(X0)) | v2_struct_0(sK3(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v1_compts_1(X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f214,f73])).
% 0.21/0.50  fof(f214,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m2_yellow_6(X1,X0,sK3(X0)) | ~v4_orders_2(sK3(X0)) | v2_struct_0(sK3(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v1_compts_1(X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f213,f74])).
% 0.21/0.50  fof(f213,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m2_yellow_6(X1,X0,sK3(X0)) | ~v7_waybel_0(sK3(X0)) | ~v4_orders_2(sK3(X0)) | v2_struct_0(sK3(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v1_compts_1(X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f212,f75])).
% 0.21/0.50  fof(f212,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m2_yellow_6(X1,X0,sK3(X0)) | ~l1_waybel_0(sK3(X0),X0) | ~v7_waybel_0(sK3(X0)) | ~v4_orders_2(sK3(X0)) | v2_struct_0(sK3(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v1_compts_1(X0)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f211])).
% 0.21/0.50  fof(f211,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m2_yellow_6(X1,X0,sK3(X0)) | ~l1_waybel_0(sK3(X0),X0) | ~v7_waybel_0(sK3(X0)) | ~v4_orders_2(sK3(X0)) | v2_struct_0(sK3(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v1_compts_1(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(resolution,[],[f82,f76])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    ( ! [X2,X0] : (~r3_waybel_9(X0,sK3(X0),X2) | v1_compts_1(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f46])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_waybel_9(X0,X2,X3) => r3_waybel_9(X0,X1,X3))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_waybel_9)).
% 0.21/0.50  fof(f456,plain,(
% 0.21/0.50    ( ! [X6,X4,X5] : (r3_waybel_9(X4,X5,sK6(X4,X5,X6)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4))) | ~l1_waybel_0(X5,X4) | ~v7_waybel_0(X5) | ~v4_orders_2(X5) | v2_struct_0(X5) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4) | k10_yellow_6(X4,X5) = X6 | r2_hidden(sK6(X4,X5,X6),X6)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f454,f86])).
% 0.21/0.50  fof(f454,plain,(
% 0.21/0.50    ( ! [X6,X4,X5] : (r2_hidden(sK6(X4,X5,X6),X6) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4))) | ~l1_waybel_0(X5,X4) | ~v7_waybel_0(X5) | ~v4_orders_2(X5) | v2_struct_0(X5) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4) | k10_yellow_6(X4,X5) = X6 | r3_waybel_9(X4,X5,sK6(X4,X5,X6)) | ~m1_subset_1(sK6(X4,X5,X6),u1_struct_0(X4))) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f449])).
% 0.21/0.50  fof(f449,plain,(
% 0.21/0.50    ( ! [X6,X4,X5] : (r2_hidden(sK6(X4,X5,X6),X6) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4))) | ~l1_waybel_0(X5,X4) | ~v7_waybel_0(X5) | ~v4_orders_2(X5) | v2_struct_0(X5) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4) | k10_yellow_6(X4,X5) = X6 | r3_waybel_9(X4,X5,sK6(X4,X5,X6)) | ~m1_subset_1(sK6(X4,X5,X6),u1_struct_0(X4)) | ~l1_waybel_0(X5,X4) | ~v7_waybel_0(X5) | ~v4_orders_2(X5) | v2_struct_0(X5) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) )),
% 0.21/0.50    inference(resolution,[],[f447,f79])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X2,k10_yellow_6(X0,X1)) | r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,X1)) => r3_waybel_9(X0,X1,X2)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_waybel_9)).
% 0.21/0.50  fof(f447,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),k10_yellow_6(X0,X1)) | r2_hidden(sK6(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | k10_yellow_6(X0,X1) = X2) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f446,f94])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_yellow_6)).
% 0.21/0.50  fof(f446,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k10_yellow_6(X0,X1) = X2 | r2_hidden(sK6(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | r2_hidden(sK6(X0,X1,X2),k10_yellow_6(X0,X1)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f445,f86])).
% 0.21/0.50  fof(f445,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k10_yellow_6(X0,X1) = X2 | r2_hidden(sK6(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | r2_hidden(sK6(X0,X1,X2),k10_yellow_6(X0,X1)) | ~m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f444])).
% 0.21/0.50  fof(f444,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k10_yellow_6(X0,X1) = X2 | r2_hidden(sK6(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | r2_hidden(sK6(X0,X1,X2),k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | r2_hidden(sK6(X0,X1,X2),k10_yellow_6(X0,X1)) | ~m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(resolution,[],[f422,f98])).
% 0.21/0.50  % (20593)Refutation not found, incomplete strategy% (20593)------------------------------
% 0.21/0.50  % (20593)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (20593)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (20593)Memory used [KB]: 10618
% 0.21/0.50  % (20593)Time elapsed: 0.100 s
% 0.21/0.50  % (20593)------------------------------
% 0.21/0.50  % (20593)------------------------------
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    ( ! [X6,X0,X1] : (~r1_waybel_0(X0,X1,sK8(X0,X1,X6)) | r2_hidden(X6,k10_yellow_6(X0,X1)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f85])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    ( ! [X6,X2,X0,X1] : (r2_hidden(X6,X2) | ~r1_waybel_0(X0,X1,sK8(X0,X1,X6)) | ~m1_subset_1(X6,u1_struct_0(X0)) | k10_yellow_6(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f56])).
% 0.21/0.50  fof(f422,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (r1_waybel_0(X0,X1,sK8(X0,X2,sK6(X0,X1,X3))) | k10_yellow_6(X0,X1) = X3 | r2_hidden(sK6(X0,X1,X3),X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | r2_hidden(sK6(X0,X1,X3),k10_yellow_6(X0,X2)) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f421,f94])).
% 0.21/0.50  fof(f421,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (r1_waybel_0(X0,X1,sK8(X0,X2,sK6(X0,X1,X3))) | k10_yellow_6(X0,X1) = X3 | r2_hidden(sK6(X0,X1,X3),X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | r2_hidden(sK6(X0,X1,X3),k10_yellow_6(X0,X2)) | ~m1_subset_1(k10_yellow_6(X0,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f420,f86])).
% 0.21/0.50  fof(f420,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (r1_waybel_0(X0,X1,sK8(X0,X2,sK6(X0,X1,X3))) | k10_yellow_6(X0,X1) = X3 | r2_hidden(sK6(X0,X1,X3),X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | r2_hidden(sK6(X0,X1,X3),k10_yellow_6(X0,X2)) | ~m1_subset_1(sK6(X0,X1,X3),u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f417])).
% 0.21/0.50  fof(f417,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (r1_waybel_0(X0,X1,sK8(X0,X2,sK6(X0,X1,X3))) | k10_yellow_6(X0,X1) = X3 | r2_hidden(sK6(X0,X1,X3),X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | r2_hidden(sK6(X0,X1,X3),k10_yellow_6(X0,X2)) | ~m1_subset_1(sK6(X0,X1,X3),u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(resolution,[],[f87,f99])).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    ( ! [X6,X0,X1] : (m1_connsp_2(sK8(X0,X1,X6),X0,X6) | r2_hidden(X6,k10_yellow_6(X0,X1)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f84])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    ( ! [X6,X2,X0,X1] : (r2_hidden(X6,X2) | m1_connsp_2(sK8(X0,X1,X6),X0,X6) | ~m1_subset_1(X6,u1_struct_0(X0)) | k10_yellow_6(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f56])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    ( ! [X2,X0,X5,X1] : (~m1_connsp_2(X5,X0,sK6(X0,X1,X2)) | r1_waybel_0(X0,X1,X5) | k10_yellow_6(X0,X1) = X2 | r2_hidden(sK6(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f56])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_xboole_0 != k10_yellow_6(X0,X1) | ~v3_yellow_6(X1,X0) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f47])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (20591)------------------------------
% 0.21/0.50  % (20591)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (20591)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (20591)Memory used [KB]: 2046
% 0.21/0.50  % (20591)Time elapsed: 0.083 s
% 0.21/0.50  % (20591)------------------------------
% 0.21/0.50  % (20591)------------------------------
% 0.21/0.50  % (20589)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.50  % (20572)Success in time 0.148 s
%------------------------------------------------------------------------------
