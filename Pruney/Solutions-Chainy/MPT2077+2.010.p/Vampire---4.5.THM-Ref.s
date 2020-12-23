%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:39 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  259 (5757 expanded)
%              Number of leaves         :   24 (1683 expanded)
%              Depth                    :   95
%              Number of atoms          : 2380 (68935 expanded)
%              Number of equality atoms :   49 ( 177 expanded)
%              Maximal formula depth    :   29 (  10 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f602,plain,(
    $false ),
    inference(subsumption_resolution,[],[f601,f67])).

fof(f67,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f43,f46,f45,f44])).

fof(f44,plain,
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

fof(f45,plain,
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

fof(f46,plain,(
    ! [X3] :
      ( ? [X4] :
          ( v3_yellow_6(X4,sK0)
          & m2_yellow_6(X4,sK0,X3) )
     => ( v3_yellow_6(sK2(X3),sK0)
        & m2_yellow_6(sK2(X3),sK0,X3) ) ) ),
    introduced(choice_axiom,[])).

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
    inference(rectify,[],[f42])).

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
    inference(flattening,[],[f41])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_yellow19)).

fof(f601,plain,(
    ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f600,f77])).

fof(f77,plain,(
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

fof(f600,plain,(
    ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f599,f65])).

fof(f65,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f599,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f598,f66])).

fof(f66,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f598,plain,
    ( ~ l1_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f597,f67])).

fof(f597,plain,
    ( ~ l1_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f596,f332])).

fof(f332,plain,(
    ~ v1_compts_1(sK0) ),
    inference(subsumption_resolution,[],[f331,f70])).

fof(f70,plain,
    ( ~ v1_compts_1(sK0)
    | ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f331,plain,
    ( ~ v1_compts_1(sK0)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f330,f71])).

fof(f71,plain,
    ( ~ v1_compts_1(sK0)
    | v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f330,plain,
    ( ~ v1_compts_1(sK0)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f329,f72])).

fof(f72,plain,
    ( ~ v1_compts_1(sK0)
    | v7_waybel_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f329,plain,
    ( ~ v1_compts_1(sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f328,f73])).

fof(f73,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f328,plain,
    ( ~ v1_compts_1(sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f327,f65])).

fof(f327,plain,
    ( ~ v1_compts_1(sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f326,f66])).

fof(f326,plain,
    ( ~ v1_compts_1(sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f325,f67])).

fof(f325,plain,
    ( ~ v1_compts_1(sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f324])).

fof(f324,plain,
    ( ~ v1_compts_1(sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f301,f78])).

fof(f78,plain,(
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
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f48])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r3_waybel_9(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X1,sK3(X0,X1))
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l37_yellow19)).

fof(f301,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ v1_compts_1(sK0) ),
    inference(subsumption_resolution,[],[f300,f70])).

fof(f300,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ v1_compts_1(sK0)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f299,f71])).

fof(f299,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ v1_compts_1(sK0)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f298,f72])).

fof(f298,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ v1_compts_1(sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f297,f73])).

fof(f297,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ v1_compts_1(sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f296,f65])).

fof(f296,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ v1_compts_1(sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f295,f66])).

fof(f295,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ v1_compts_1(sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f294,f67])).

fof(f294,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ v1_compts_1(sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f288])).

fof(f288,plain,
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
    inference(resolution,[],[f287,f79])).

fof(f79,plain,(
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
    inference(cnf_transformation,[],[f49])).

% (32637)Refutation not found, incomplete strategy% (32637)------------------------------
% (32637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (32637)Termination reason: Refutation not found, incomplete strategy

% (32637)Memory used [KB]: 10618
% (32637)Time elapsed: 0.089 s
% (32637)------------------------------
% (32637)------------------------------
fof(f287,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f286,f70])).

fof(f286,plain,(
    ! [X0] :
      ( v2_struct_0(sK1)
      | ~ r3_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f285,f71])).

fof(f285,plain,(
    ! [X0] :
      ( ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ r3_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f284,f72])).

fof(f284,plain,(
    ! [X0] :
      ( ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ r3_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f283,f73])).

fof(f283,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ r3_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f282,f65])).

fof(f282,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ r3_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f281,f66])).

fof(f281,plain,(
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
    inference(subsumption_resolution,[],[f280,f67])).

fof(f280,plain,(
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
    inference(duplicate_literal_removal,[],[f279])).

fof(f279,plain,(
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
    inference(resolution,[],[f278,f195])).

fof(f195,plain,(
    ! [X0] :
      ( ~ v3_yellow_6(sK6(sK0,sK1,X0),sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK1,X0)
      | ~ v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f194,f70])).

fof(f194,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK1)
      | ~ v3_yellow_6(sK6(sK0,sK1,X0),sK0)
      | ~ v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f193,f71])).

fof(f193,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ v3_yellow_6(sK6(sK0,sK1,X0),sK0)
      | ~ v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f192,f72])).

fof(f192,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ v3_yellow_6(sK6(sK0,sK1,X0),sK0)
      | ~ v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f191,f73])).

fof(f191,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ v3_yellow_6(sK6(sK0,sK1,X0),sK0)
      | ~ v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f190,f65])).

fof(f190,plain,(
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
    inference(subsumption_resolution,[],[f189,f66])).

fof(f189,plain,(
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
    inference(subsumption_resolution,[],[f180,f67])).

fof(f180,plain,(
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
    inference(resolution,[],[f91,f74])).

fof(f74,plain,(
    ! [X2] :
      ( ~ m2_yellow_6(X2,sK0,sK1)
      | ~ v3_yellow_6(X2,sK0)
      | ~ v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f91,plain,(
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
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f29,f56])).

fof(f56,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X2,k10_yellow_6(X0,X3))
          & m2_yellow_6(X3,X0,X1) )
     => ( r2_hidden(X2,k10_yellow_6(X0,sK6(X0,X1,X2)))
        & m2_yellow_6(sK6(X0,X1,X2),X0,X1) ) ) ),
    introduced(choice_axiom,[])).

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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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

fof(f278,plain,(
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
    inference(subsumption_resolution,[],[f277,f199])).

fof(f199,plain,(
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
    inference(subsumption_resolution,[],[f185,f77])).

fof(f185,plain,(
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
    inference(duplicate_literal_removal,[],[f184])).

fof(f184,plain,(
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
    inference(resolution,[],[f91,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_yellow_6(X2,X0,X1)
      | ~ v2_struct_0(X2)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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

fof(f277,plain,(
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
    inference(subsumption_resolution,[],[f276,f198])).

fof(f198,plain,(
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
    inference(subsumption_resolution,[],[f186,f77])).

fof(f186,plain,(
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
    inference(duplicate_literal_removal,[],[f183])).

fof(f183,plain,(
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
    inference(resolution,[],[f91,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_yellow_6(X2,X0,X1)
      | v4_orders_2(X2)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f276,plain,(
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
    inference(subsumption_resolution,[],[f275,f197])).

fof(f197,plain,(
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
    inference(subsumption_resolution,[],[f187,f77])).

fof(f187,plain,(
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
    inference(duplicate_literal_removal,[],[f182])).

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
      | v7_waybel_0(sK6(X4,X5,X6))
      | ~ l1_waybel_0(X5,X4)
      | ~ v7_waybel_0(X5)
      | ~ v4_orders_2(X5)
      | v2_struct_0(X5)
      | ~ l1_struct_0(X4)
      | v2_struct_0(X4) ) ),
    inference(resolution,[],[f91,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_yellow_6(X2,X0,X1)
      | v7_waybel_0(X2)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

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
      | v3_yellow_6(sK6(X0,X1,X2),X0)
      | ~ v7_waybel_0(sK6(X0,X1,X2))
      | ~ v4_orders_2(sK6(X0,X1,X2))
      | v2_struct_0(sK6(X0,X1,X2)) ) ),
    inference(subsumption_resolution,[],[f274,f196])).

fof(f196,plain,(
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
    inference(subsumption_resolution,[],[f188,f77])).

fof(f188,plain,(
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
    inference(duplicate_literal_removal,[],[f181])).

fof(f181,plain,(
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
    inference(resolution,[],[f91,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_yellow_6(X2,X0,X1)
      | l1_waybel_0(X2,X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

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
      | v3_yellow_6(sK6(X0,X1,X2),X0)
      | ~ l1_waybel_0(sK6(X0,X1,X2),X0)
      | ~ v7_waybel_0(sK6(X0,X1,X2))
      | ~ v4_orders_2(sK6(X0,X1,X2))
      | v2_struct_0(sK6(X0,X1,X2)) ) ),
    inference(subsumption_resolution,[],[f273,f75])).

fof(f75,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f273,plain,(
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
    inference(duplicate_literal_removal,[],[f272])).

fof(f272,plain,(
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
    inference(superposition,[],[f202,f89])).

fof(f89,plain,(
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
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f25])).

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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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

fof(f202,plain,(
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
    inference(resolution,[],[f92,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f92,plain,(
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
    inference(cnf_transformation,[],[f57])).

fof(f596,plain,
    ( ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f595,f82])).

fof(f82,plain,(
    ! [X0] :
      ( ~ v2_struct_0(sK4(X0))
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f51,f53,f52])).

fof(f52,plain,(
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

fof(f53,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( r3_waybel_9(X0,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X3,sK5(X0,X3))
        & m1_subset_1(sK5(X0,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
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
    inference(rectify,[],[f50])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f23])).

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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_yellow19)).

fof(f595,plain,
    ( v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f594,f65])).

fof(f594,plain,
    ( v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f593,f66])).

fof(f593,plain,
    ( v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f592,f67])).

fof(f592,plain,
    ( v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f591,f332])).

fof(f591,plain,
    ( v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f590,f83])).

fof(f83,plain,(
    ! [X0] :
      ( v4_orders_2(sK4(X0))
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f590,plain,
    ( ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f589,f65])).

fof(f589,plain,
    ( ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f588,f66])).

fof(f588,plain,
    ( ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f587,f67])).

fof(f587,plain,
    ( ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f586,f332])).

fof(f586,plain,
    ( ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f585,f84])).

fof(f84,plain,(
    ! [X0] :
      ( v7_waybel_0(sK4(X0))
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f585,plain,
    ( ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f584,f332])).

fof(f584,plain,
    ( ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0) ),
    inference(duplicate_literal_removal,[],[f583])).

% (32651)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f583,plain,
    ( ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0) ),
    inference(resolution,[],[f582,f122])).

fof(f122,plain,
    ( ~ v2_struct_0(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0) ),
    inference(subsumption_resolution,[],[f121,f65])).

fof(f121,plain,
    ( ~ v2_struct_0(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f120,f66])).

fof(f120,plain,
    ( ~ v2_struct_0(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f119,f67])).

fof(f119,plain,
    ( ~ v2_struct_0(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f118])).

fof(f118,plain,
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
    inference(resolution,[],[f116,f85])).

fof(f85,plain,(
    ! [X0] :
      ( l1_waybel_0(sK4(X0),X0)
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f116,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ v2_struct_0(sK2(X0))
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(sK0)
      | v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f115,f65])).

fof(f115,plain,(
    ! [X0] :
      ( ~ v2_struct_0(sK2(X0))
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0)
      | v1_compts_1(sK0) ) ),
    inference(duplicate_literal_removal,[],[f114])).

fof(f114,plain,(
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
    inference(resolution,[],[f101,f68])).

fof(f68,plain,(
    ! [X3] :
      ( m2_yellow_6(sK2(X3),sK0,X3)
      | ~ l1_waybel_0(X3,sK0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f582,plain,
    ( v2_struct_0(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f581,f332])).

fof(f581,plain,
    ( v2_struct_0(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0) ),
    inference(duplicate_literal_removal,[],[f580])).

fof(f580,plain,
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
    inference(resolution,[],[f579,f131])).

fof(f131,plain,
    ( v4_orders_2(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0) ),
    inference(subsumption_resolution,[],[f130,f65])).

fof(f130,plain,
    ( v4_orders_2(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f129,f66])).

fof(f129,plain,
    ( v4_orders_2(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f128,f67])).

fof(f128,plain,
    ( v4_orders_2(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f127])).

fof(f127,plain,
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
    inference(resolution,[],[f125,f85])).

fof(f125,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(X0,sK0)
      | v4_orders_2(sK2(X0))
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(sK0)
      | v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f124,f65])).

fof(f124,plain,(
    ! [X0] :
      ( v4_orders_2(sK2(X0))
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0)
      | v1_compts_1(sK0) ) ),
    inference(duplicate_literal_removal,[],[f123])).

fof(f123,plain,(
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
    inference(resolution,[],[f102,f68])).

fof(f579,plain,
    ( ~ v4_orders_2(sK2(sK4(sK0)))
    | v2_struct_0(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f578,f332])).

fof(f578,plain,
    ( v2_struct_0(sK2(sK4(sK0)))
    | ~ v4_orders_2(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0) ),
    inference(duplicate_literal_removal,[],[f577])).

fof(f577,plain,
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
    inference(resolution,[],[f576,f140])).

fof(f140,plain,
    ( v7_waybel_0(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0) ),
    inference(subsumption_resolution,[],[f139,f65])).

fof(f139,plain,
    ( v7_waybel_0(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f138,f66])).

fof(f138,plain,
    ( v7_waybel_0(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f137,f67])).

fof(f137,plain,
    ( v7_waybel_0(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f136])).

fof(f136,plain,
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
    inference(resolution,[],[f134,f85])).

fof(f134,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(X0,sK0)
      | v7_waybel_0(sK2(X0))
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(sK0)
      | v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f133,f65])).

fof(f133,plain,(
    ! [X0] :
      ( v7_waybel_0(sK2(X0))
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0)
      | v1_compts_1(sK0) ) ),
    inference(duplicate_literal_removal,[],[f132])).

fof(f132,plain,(
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
    inference(resolution,[],[f103,f68])).

fof(f576,plain,
    ( ~ v7_waybel_0(sK2(sK4(sK0)))
    | v2_struct_0(sK2(sK4(sK0)))
    | ~ v4_orders_2(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f575,f65])).

fof(f575,plain,
    ( ~ v4_orders_2(sK2(sK4(sK0)))
    | v2_struct_0(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f574,f66])).

fof(f574,plain,
    ( ~ v4_orders_2(sK2(sK4(sK0)))
    | v2_struct_0(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f573,f67])).

fof(f573,plain,
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
    inference(subsumption_resolution,[],[f572,f332])).

fof(f572,plain,
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
    inference(resolution,[],[f571,f85])).

fof(f571,plain,
    ( ~ l1_waybel_0(sK4(sK0),sK0)
    | ~ v4_orders_2(sK2(sK4(sK0)))
    | v2_struct_0(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK2(sK4(sK0)))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f570,f332])).

fof(f570,plain,
    ( ~ v7_waybel_0(sK2(sK4(sK0)))
    | ~ v4_orders_2(sK2(sK4(sK0)))
    | v2_struct_0(sK2(sK4(sK0)))
    | ~ l1_waybel_0(sK4(sK0),sK0)
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | v1_compts_1(sK0) ),
    inference(duplicate_literal_removal,[],[f569])).

fof(f569,plain,
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
    inference(resolution,[],[f568,f143])).

fof(f143,plain,(
    ! [X0] :
      ( l1_waybel_0(sK2(X0),sK0)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(sK0)
      | v1_compts_1(sK0) ) ),
    inference(subsumption_resolution,[],[f142,f65])).

fof(f142,plain,(
    ! [X0] :
      ( l1_waybel_0(sK2(X0),sK0)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0)
      | v1_compts_1(sK0) ) ),
    inference(duplicate_literal_removal,[],[f141])).

fof(f141,plain,(
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
    inference(resolution,[],[f104,f68])).

fof(f568,plain,
    ( ~ l1_waybel_0(sK2(sK4(sK0)),sK0)
    | ~ v7_waybel_0(sK2(sK4(sK0)))
    | ~ v4_orders_2(sK2(sK4(sK0)))
    | v2_struct_0(sK2(sK4(sK0)))
    | ~ l1_waybel_0(sK4(sK0),sK0)
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0)) ),
    inference(subsumption_resolution,[],[f567,f332])).

fof(f567,plain,
    ( ~ l1_waybel_0(sK2(sK4(sK0)),sK0)
    | ~ v7_waybel_0(sK2(sK4(sK0)))
    | ~ v4_orders_2(sK2(sK4(sK0)))
    | v2_struct_0(sK2(sK4(sK0)))
    | ~ l1_waybel_0(sK4(sK0),sK0)
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | v1_compts_1(sK0) ),
    inference(duplicate_literal_removal,[],[f566])).

fof(f566,plain,
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
    inference(resolution,[],[f553,f69])).

fof(f69,plain,(
    ! [X3] :
      ( v3_yellow_6(sK2(X3),sK0)
      | ~ l1_waybel_0(X3,sK0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f553,plain,
    ( ~ v3_yellow_6(sK2(sK4(sK0)),sK0)
    | ~ l1_waybel_0(sK2(sK4(sK0)),sK0)
    | ~ v7_waybel_0(sK2(sK4(sK0)))
    | ~ v4_orders_2(sK2(sK4(sK0)))
    | v2_struct_0(sK2(sK4(sK0)))
    | ~ l1_waybel_0(sK4(sK0),sK0)
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0)) ),
    inference(subsumption_resolution,[],[f552,f65])).

fof(f552,plain,
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
    inference(subsumption_resolution,[],[f551,f66])).

fof(f551,plain,
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
    inference(subsumption_resolution,[],[f550,f67])).

fof(f550,plain,
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
    inference(trivial_inequality_removal,[],[f549])).

fof(f549,plain,
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
    inference(duplicate_literal_removal,[],[f532])).

fof(f532,plain,
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
    inference(superposition,[],[f88,f531])).

fof(f531,plain,
    ( k1_xboole_0 = k10_yellow_6(sK0,sK2(sK4(sK0)))
    | v2_struct_0(sK2(sK4(sK0)))
    | ~ v4_orders_2(sK2(sK4(sK0)))
    | ~ l1_waybel_0(sK2(sK4(sK0)),sK0)
    | ~ l1_waybel_0(sK4(sK0),sK0)
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ v7_waybel_0(sK2(sK4(sK0))) ),
    inference(subsumption_resolution,[],[f530,f76])).

fof(f76,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f530,plain,
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
    inference(resolution,[],[f517,f75])).

fof(f517,plain,(
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
    inference(resolution,[],[f515,f106])).

fof(f515,plain,(
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
    inference(subsumption_resolution,[],[f514,f65])).

fof(f514,plain,(
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
    inference(subsumption_resolution,[],[f513,f66])).

fof(f513,plain,(
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
    inference(subsumption_resolution,[],[f512,f67])).

fof(f512,plain,(
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
    inference(duplicate_literal_removal,[],[f511])).

fof(f511,plain,(
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
    inference(resolution,[],[f493,f97])).

fof(f97,plain,(
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
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f60,f63,f62,f61])).

fof(f61,plain,(
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

fof(f62,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_waybel_0(X0,X1,X4)
          & m1_connsp_2(X4,X0,sK7(X0,X1,X2)) )
     => ( ~ r1_waybel_0(X0,X1,sK8(X0,X1,X2))
        & m1_connsp_2(sK8(X0,X1,X2),X0,sK7(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X6,X1,X0] :
      ( ? [X7] :
          ( ~ r1_waybel_0(X0,X1,X7)
          & m1_connsp_2(X7,X0,X6) )
     => ( ~ r1_waybel_0(X0,X1,sK9(X0,X1,X6))
        & m1_connsp_2(sK9(X0,X1,X6),X0,X6) ) ) ),
    introduced(choice_axiom,[])).

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
    inference(rectify,[],[f59])).

fof(f59,plain,(
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
    inference(flattening,[],[f58])).

fof(f58,plain,(
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
    inference(nnf_transformation,[],[f33])).

% (32639)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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

fof(f493,plain,(
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
    inference(subsumption_resolution,[],[f492,f332])).

fof(f492,plain,(
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
    inference(subsumption_resolution,[],[f491,f65])).

fof(f491,plain,(
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
    inference(subsumption_resolution,[],[f490,f66])).

fof(f490,plain,(
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
    inference(subsumption_resolution,[],[f477,f67])).

fof(f477,plain,(
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
    inference(resolution,[],[f469,f239])).

fof(f239,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK2(sK4(sK0)),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v1_compts_1(sK0)
      | ~ l1_waybel_0(sK4(sK0),sK0)
      | ~ v7_waybel_0(sK4(sK0))
      | ~ v4_orders_2(sK4(sK0))
      | v2_struct_0(sK4(sK0)) ) ),
    inference(subsumption_resolution,[],[f238,f65])).

fof(f238,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK2(sK4(sK0)),X0)
      | v2_struct_0(sK0)
      | v1_compts_1(sK0)
      | ~ l1_waybel_0(sK4(sK0),sK0)
      | ~ v7_waybel_0(sK4(sK0))
      | ~ v4_orders_2(sK4(sK0))
      | v2_struct_0(sK4(sK0)) ) ),
    inference(subsumption_resolution,[],[f237,f66])).

fof(f237,plain,(
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
    inference(subsumption_resolution,[],[f236,f67])).

fof(f236,plain,(
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
    inference(duplicate_literal_removal,[],[f233])).

fof(f233,plain,(
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
    inference(resolution,[],[f232,f68])).

fof(f232,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_yellow_6(X1,X0,sK4(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_compts_1(X0) ) ),
    inference(subsumption_resolution,[],[f231,f82])).

fof(f231,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m2_yellow_6(X1,X0,sK4(X0))
      | v2_struct_0(sK4(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_compts_1(X0) ) ),
    inference(subsumption_resolution,[],[f230,f83])).

fof(f230,plain,(
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
    inference(subsumption_resolution,[],[f229,f84])).

% (32644)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
fof(f229,plain,(
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
    inference(subsumption_resolution,[],[f228,f85])).

fof(f228,plain,(
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
    inference(duplicate_literal_removal,[],[f227])).

fof(f227,plain,(
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
    inference(resolution,[],[f93,f87])).

fof(f87,plain,(
    ! [X2,X0] :
      ( ~ r3_waybel_9(X0,sK4(X0),X2)
      | v1_compts_1(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f93,plain,(
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
    inference(cnf_transformation,[],[f31])).

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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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

fof(f469,plain,(
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
    inference(subsumption_resolution,[],[f467,f97])).

fof(f467,plain,(
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
    inference(duplicate_literal_removal,[],[f460])).

fof(f460,plain,(
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
    inference(resolution,[],[f458,f90])).

fof(f90,plain,(
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
    inference(cnf_transformation,[],[f27])).

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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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

fof(f458,plain,(
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
    inference(subsumption_resolution,[],[f457,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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

fof(f457,plain,(
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
    inference(subsumption_resolution,[],[f456,f97])).

fof(f456,plain,(
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
    inference(duplicate_literal_removal,[],[f455])).

fof(f455,plain,(
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
    inference(resolution,[],[f433,f108])).

fof(f108,plain,(
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
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
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
    inference(cnf_transformation,[],[f64])).

fof(f433,plain,(
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
    inference(subsumption_resolution,[],[f432,f105])).

fof(f432,plain,(
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
    inference(subsumption_resolution,[],[f431,f97])).

fof(f431,plain,(
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
    inference(duplicate_literal_removal,[],[f428])).

fof(f428,plain,(
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
    inference(resolution,[],[f98,f109])).

fof(f109,plain,(
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
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
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
    inference(cnf_transformation,[],[f64])).

fof(f98,plain,(
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
    inference(cnf_transformation,[],[f64])).

fof(f88,plain,(
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
    inference(cnf_transformation,[],[f55])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:45:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (32650)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.48  % (32638)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.48  % (32654)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.48  % (32642)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.49  % (32646)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.49  % (32641)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (32646)Refutation not found, incomplete strategy% (32646)------------------------------
% 0.20/0.49  % (32646)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (32646)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (32646)Memory used [KB]: 6268
% 0.20/0.50  % (32646)Time elapsed: 0.062 s
% 0.20/0.50  % (32646)------------------------------
% 0.20/0.50  % (32646)------------------------------
% 0.20/0.50  % (32648)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (32636)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (32645)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.50  % (32636)Refutation not found, incomplete strategy% (32636)------------------------------
% 0.20/0.50  % (32636)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (32636)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (32636)Memory used [KB]: 6140
% 0.20/0.50  % (32636)Time elapsed: 0.079 s
% 0.20/0.50  % (32636)------------------------------
% 0.20/0.50  % (32636)------------------------------
% 0.20/0.51  % (32655)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.51  % (32649)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.51  % (32637)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (32640)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.51  % (32654)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f602,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(subsumption_resolution,[],[f601,f67])).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    l1_pre_topc(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f47])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ((! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,sK1)) & l1_waybel_0(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1)) | ~v1_compts_1(sK0)) & (! [X3] : ((v3_yellow_6(sK2(X3),sK0) & m2_yellow_6(sK2(X3),sK0,X3)) | ~l1_waybel_0(X3,sK0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f43,f46,f45,f44])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ((? [X1] : (! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,X1)) & l1_waybel_0(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(sK0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,sK0) & m2_yellow_6(X4,sK0,X3)) | ~l1_waybel_0(X3,sK0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ? [X1] : (! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,X1)) & l1_waybel_0(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,sK1)) & l1_waybel_0(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ! [X3] : (? [X4] : (v3_yellow_6(X4,sK0) & m2_yellow_6(X4,sK0,X3)) => (v3_yellow_6(sK2(X3),sK0) & m2_yellow_6(sK2(X3),sK0,X3)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.51    inference(rectify,[],[f42])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f41])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ? [X0] : (((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | v1_compts_1(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,negated_conjecture,(
% 0.20/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)))))),
% 0.20/0.51    inference(negated_conjecture,[],[f15])).
% 0.20/0.51  fof(f15,conjecture,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_yellow19)).
% 0.20/0.51  fof(f601,plain,(
% 0.20/0.51    ~l1_pre_topc(sK0)),
% 0.20/0.51    inference(resolution,[],[f600,f77])).
% 0.20/0.51  fof(f77,plain,(
% 0.20/0.51    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.51  fof(f600,plain,(
% 0.20/0.51    ~l1_struct_0(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f599,f65])).
% 0.20/0.51  fof(f65,plain,(
% 0.20/0.51    ~v2_struct_0(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f47])).
% 0.20/0.51  fof(f599,plain,(
% 0.20/0.51    ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f598,f66])).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    v2_pre_topc(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f47])).
% 0.20/0.51  fof(f598,plain,(
% 0.20/0.51    ~l1_struct_0(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f597,f67])).
% 0.20/0.51  fof(f597,plain,(
% 0.20/0.51    ~l1_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f596,f332])).
% 0.20/0.51  fof(f332,plain,(
% 0.20/0.51    ~v1_compts_1(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f331,f70])).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    ~v1_compts_1(sK0) | ~v2_struct_0(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f47])).
% 0.20/0.51  fof(f331,plain,(
% 0.20/0.51    ~v1_compts_1(sK0) | v2_struct_0(sK1)),
% 0.20/0.51    inference(subsumption_resolution,[],[f330,f71])).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    ~v1_compts_1(sK0) | v4_orders_2(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f47])).
% 0.20/0.51  fof(f330,plain,(
% 0.20/0.51    ~v1_compts_1(sK0) | ~v4_orders_2(sK1) | v2_struct_0(sK1)),
% 0.20/0.51    inference(subsumption_resolution,[],[f329,f72])).
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    ~v1_compts_1(sK0) | v7_waybel_0(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f47])).
% 0.20/0.51  fof(f329,plain,(
% 0.20/0.51    ~v1_compts_1(sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1)),
% 0.20/0.51    inference(subsumption_resolution,[],[f328,f73])).
% 0.20/0.51  fof(f73,plain,(
% 0.20/0.51    l1_waybel_0(sK1,sK0) | ~v1_compts_1(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f47])).
% 0.20/0.51  fof(f328,plain,(
% 0.20/0.51    ~v1_compts_1(sK0) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1)),
% 0.20/0.51    inference(subsumption_resolution,[],[f327,f65])).
% 0.20/0.51  fof(f327,plain,(
% 0.20/0.51    ~v1_compts_1(sK0) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | v2_struct_0(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f326,f66])).
% 0.20/0.51  fof(f326,plain,(
% 0.20/0.51    ~v1_compts_1(sK0) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f325,f67])).
% 0.20/0.51  fof(f325,plain,(
% 0.20/0.51    ~v1_compts_1(sK0) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f324])).
% 0.20/0.51  fof(f324,plain,(
% 0.20/0.51    ~v1_compts_1(sK0) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.51    inference(resolution,[],[f301,f78])).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f49])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((r3_waybel_9(X0,X1,sK3(X0,X1)) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f48])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ! [X1,X0] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) => (r3_waybel_9(X0,X1,sK3(X0,X1)) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0] : ((! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | ~v1_compts_1(X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,axiom,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l37_yellow19)).
% 0.20/0.51  fof(f301,plain,(
% 0.20/0.51    ~m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) | ~v1_compts_1(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f300,f70])).
% 0.20/0.51  fof(f300,plain,(
% 0.20/0.51    ~m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) | ~v1_compts_1(sK0) | v2_struct_0(sK1)),
% 0.20/0.51    inference(subsumption_resolution,[],[f299,f71])).
% 0.20/0.51  fof(f299,plain,(
% 0.20/0.51    ~m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) | ~v1_compts_1(sK0) | ~v4_orders_2(sK1) | v2_struct_0(sK1)),
% 0.20/0.51    inference(subsumption_resolution,[],[f298,f72])).
% 0.20/0.51  fof(f298,plain,(
% 0.20/0.51    ~m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) | ~v1_compts_1(sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1)),
% 0.20/0.51    inference(subsumption_resolution,[],[f297,f73])).
% 0.20/0.51  fof(f297,plain,(
% 0.20/0.51    ~m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) | ~v1_compts_1(sK0) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1)),
% 0.20/0.51    inference(subsumption_resolution,[],[f296,f65])).
% 0.20/0.51  fof(f296,plain,(
% 0.20/0.51    ~m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) | ~v1_compts_1(sK0) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | v2_struct_0(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f295,f66])).
% 0.20/0.51  fof(f295,plain,(
% 0.20/0.51    ~m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) | ~v1_compts_1(sK0) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f294,f67])).
% 0.20/0.51  fof(f294,plain,(
% 0.20/0.51    ~m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) | ~v1_compts_1(sK0) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f288])).
% 0.20/0.51  fof(f288,plain,(
% 0.20/0.51    ~m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) | ~v1_compts_1(sK0) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.51    inference(resolution,[],[f287,f79])).
% 0.20/0.51  fof(f79,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r3_waybel_9(X0,X1,sK3(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f49])).
% 0.20/0.51  % (32637)Refutation not found, incomplete strategy% (32637)------------------------------
% 0.20/0.51  % (32637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (32637)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (32637)Memory used [KB]: 10618
% 0.20/0.51  % (32637)Time elapsed: 0.089 s
% 0.20/0.51  % (32637)------------------------------
% 0.20/0.51  % (32637)------------------------------
% 0.20/0.51  fof(f287,plain,(
% 0.20/0.51    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v1_compts_1(sK0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f286,f70])).
% 0.20/0.51  fof(f286,plain,(
% 0.20/0.51    ( ! [X0] : (v2_struct_0(sK1) | ~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v1_compts_1(sK0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f285,f71])).
% 0.20/0.51  fof(f285,plain,(
% 0.20/0.51    ( ! [X0] : (~v4_orders_2(sK1) | v2_struct_0(sK1) | ~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v1_compts_1(sK0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f284,f72])).
% 0.20/0.51  fof(f284,plain,(
% 0.20/0.51    ( ! [X0] : (~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v1_compts_1(sK0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f283,f73])).
% 0.20/0.51  fof(f283,plain,(
% 0.20/0.51    ( ! [X0] : (~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v1_compts_1(sK0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f282,f65])).
% 0.20/0.51  fof(f282,plain,(
% 0.20/0.51    ( ! [X0] : (~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | v2_struct_0(sK0) | ~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v1_compts_1(sK0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f281,f66])).
% 0.20/0.51  fof(f281,plain,(
% 0.20/0.51    ( ! [X0] : (~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v1_compts_1(sK0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f280,f67])).
% 0.20/0.51  fof(f280,plain,(
% 0.20/0.51    ( ! [X0] : (~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v1_compts_1(sK0)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f279])).
% 0.20/0.51  fof(f279,plain,(
% 0.20/0.51    ( ! [X0] : (~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X0) | ~v1_compts_1(sK0)) )),
% 0.20/0.51    inference(resolution,[],[f278,f195])).
% 0.20/0.51  fof(f195,plain,(
% 0.20/0.51    ( ! [X0] : (~v3_yellow_6(sK6(sK0,sK1,X0),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X0) | ~v1_compts_1(sK0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f194,f70])).
% 0.20/0.51  fof(f194,plain,(
% 0.20/0.51    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK1) | ~v3_yellow_6(sK6(sK0,sK1,X0),sK0) | ~v1_compts_1(sK0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f193,f71])).
% 0.20/0.51  fof(f193,plain,(
% 0.20/0.51    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v3_yellow_6(sK6(sK0,sK1,X0),sK0) | ~v1_compts_1(sK0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f192,f72])).
% 0.20/0.51  fof(f192,plain,(
% 0.20/0.51    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v3_yellow_6(sK6(sK0,sK1,X0),sK0) | ~v1_compts_1(sK0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f191,f73])).
% 0.20/0.51  fof(f191,plain,(
% 0.20/0.51    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v3_yellow_6(sK6(sK0,sK1,X0),sK0) | ~v1_compts_1(sK0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f190,f65])).
% 0.20/0.51  fof(f190,plain,(
% 0.20/0.51    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | v2_struct_0(sK0) | ~v3_yellow_6(sK6(sK0,sK1,X0),sK0) | ~v1_compts_1(sK0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f189,f66])).
% 0.20/0.51  fof(f189,plain,(
% 0.20/0.51    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~v3_yellow_6(sK6(sK0,sK1,X0),sK0) | ~v1_compts_1(sK0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f180,f67])).
% 0.20/0.51  fof(f180,plain,(
% 0.20/0.51    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~v3_yellow_6(sK6(sK0,sK1,X0),sK0) | ~v1_compts_1(sK0)) )),
% 0.20/0.51    inference(resolution,[],[f91,f74])).
% 0.20/0.51  fof(f74,plain,(
% 0.20/0.51    ( ! [X2] : (~m2_yellow_6(X2,sK0,sK1) | ~v3_yellow_6(X2,sK0) | ~v1_compts_1(sK0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f47])).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (m2_yellow_6(sK6(X0,X1,X2),X0,X1) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f57])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k10_yellow_6(X0,sK6(X0,X1,X2))) & m2_yellow_6(sK6(X0,X1,X2),X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f29,f56])).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    ! [X2,X1,X0] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) => (r2_hidden(X2,k10_yellow_6(X0,sK6(X0,X1,X2))) & m2_yellow_6(sK6(X0,X1,X2),X0,X1)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : ((? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,axiom,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m2_yellow_6(X3,X0,X1) => ~r2_hidden(X2,k10_yellow_6(X0,X3))) & r3_waybel_9(X0,X1,X2)))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_waybel_9)).
% 0.20/0.51  fof(f278,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (v3_yellow_6(sK6(X0,X1,X2),X0) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f277,f199])).
% 0.20/0.51  fof(f199,plain,(
% 0.20/0.51    ( ! [X12,X10,X11] : (~v2_struct_0(sK6(X10,X11,X12)) | ~m1_subset_1(X12,u1_struct_0(X10)) | ~l1_waybel_0(X11,X10) | ~v7_waybel_0(X11) | ~v4_orders_2(X11) | v2_struct_0(X11) | ~l1_pre_topc(X10) | ~v2_pre_topc(X10) | v2_struct_0(X10) | ~r3_waybel_9(X10,X11,X12)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f185,f77])).
% 0.20/0.51  fof(f185,plain,(
% 0.20/0.51    ( ! [X12,X10,X11] : (~r3_waybel_9(X10,X11,X12) | ~m1_subset_1(X12,u1_struct_0(X10)) | ~l1_waybel_0(X11,X10) | ~v7_waybel_0(X11) | ~v4_orders_2(X11) | v2_struct_0(X11) | ~l1_pre_topc(X10) | ~v2_pre_topc(X10) | v2_struct_0(X10) | ~v2_struct_0(sK6(X10,X11,X12)) | ~l1_struct_0(X10)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f184])).
% 0.20/0.51  fof(f184,plain,(
% 0.20/0.51    ( ! [X12,X10,X11] : (~r3_waybel_9(X10,X11,X12) | ~m1_subset_1(X12,u1_struct_0(X10)) | ~l1_waybel_0(X11,X10) | ~v7_waybel_0(X11) | ~v4_orders_2(X11) | v2_struct_0(X11) | ~l1_pre_topc(X10) | ~v2_pre_topc(X10) | v2_struct_0(X10) | ~v2_struct_0(sK6(X10,X11,X12)) | ~l1_waybel_0(X11,X10) | ~v7_waybel_0(X11) | ~v4_orders_2(X11) | v2_struct_0(X11) | ~l1_struct_0(X10) | v2_struct_0(X10)) )),
% 0.20/0.51    inference(resolution,[],[f91,f101])).
% 0.20/0.51  fof(f101,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m2_yellow_6(X2,X0,X1) | ~v2_struct_0(X2) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_yellow_6)).
% 0.20/0.51  fof(f277,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~r3_waybel_9(X0,X1,X2) | v3_yellow_6(sK6(X0,X1,X2),X0) | v2_struct_0(sK6(X0,X1,X2))) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f276,f198])).
% 0.20/0.51  fof(f198,plain,(
% 0.20/0.51    ( ! [X8,X7,X9] : (v4_orders_2(sK6(X7,X8,X9)) | ~m1_subset_1(X9,u1_struct_0(X7)) | ~l1_waybel_0(X8,X7) | ~v7_waybel_0(X8) | ~v4_orders_2(X8) | v2_struct_0(X8) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7) | ~r3_waybel_9(X7,X8,X9)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f186,f77])).
% 0.20/0.51  fof(f186,plain,(
% 0.20/0.51    ( ! [X8,X7,X9] : (~r3_waybel_9(X7,X8,X9) | ~m1_subset_1(X9,u1_struct_0(X7)) | ~l1_waybel_0(X8,X7) | ~v7_waybel_0(X8) | ~v4_orders_2(X8) | v2_struct_0(X8) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7) | v4_orders_2(sK6(X7,X8,X9)) | ~l1_struct_0(X7)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f183])).
% 0.20/0.51  fof(f183,plain,(
% 0.20/0.51    ( ! [X8,X7,X9] : (~r3_waybel_9(X7,X8,X9) | ~m1_subset_1(X9,u1_struct_0(X7)) | ~l1_waybel_0(X8,X7) | ~v7_waybel_0(X8) | ~v4_orders_2(X8) | v2_struct_0(X8) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7) | v4_orders_2(sK6(X7,X8,X9)) | ~l1_waybel_0(X8,X7) | ~v7_waybel_0(X8) | ~v4_orders_2(X8) | v2_struct_0(X8) | ~l1_struct_0(X7) | v2_struct_0(X7)) )),
% 0.20/0.51    inference(resolution,[],[f91,f102])).
% 0.20/0.51  fof(f102,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m2_yellow_6(X2,X0,X1) | v4_orders_2(X2) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f35])).
% 0.20/0.51  fof(f276,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~r3_waybel_9(X0,X1,X2) | v3_yellow_6(sK6(X0,X1,X2),X0) | ~v4_orders_2(sK6(X0,X1,X2)) | v2_struct_0(sK6(X0,X1,X2))) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f275,f197])).
% 0.20/0.51  fof(f197,plain,(
% 0.20/0.51    ( ! [X6,X4,X5] : (v7_waybel_0(sK6(X4,X5,X6)) | ~m1_subset_1(X6,u1_struct_0(X4)) | ~l1_waybel_0(X5,X4) | ~v7_waybel_0(X5) | ~v4_orders_2(X5) | v2_struct_0(X5) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4) | ~r3_waybel_9(X4,X5,X6)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f187,f77])).
% 0.20/0.51  fof(f187,plain,(
% 0.20/0.51    ( ! [X6,X4,X5] : (~r3_waybel_9(X4,X5,X6) | ~m1_subset_1(X6,u1_struct_0(X4)) | ~l1_waybel_0(X5,X4) | ~v7_waybel_0(X5) | ~v4_orders_2(X5) | v2_struct_0(X5) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4) | v7_waybel_0(sK6(X4,X5,X6)) | ~l1_struct_0(X4)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f182])).
% 0.20/0.51  fof(f182,plain,(
% 0.20/0.51    ( ! [X6,X4,X5] : (~r3_waybel_9(X4,X5,X6) | ~m1_subset_1(X6,u1_struct_0(X4)) | ~l1_waybel_0(X5,X4) | ~v7_waybel_0(X5) | ~v4_orders_2(X5) | v2_struct_0(X5) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4) | v7_waybel_0(sK6(X4,X5,X6)) | ~l1_waybel_0(X5,X4) | ~v7_waybel_0(X5) | ~v4_orders_2(X5) | v2_struct_0(X5) | ~l1_struct_0(X4) | v2_struct_0(X4)) )),
% 0.20/0.51    inference(resolution,[],[f91,f103])).
% 0.20/0.51  fof(f103,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m2_yellow_6(X2,X0,X1) | v7_waybel_0(X2) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f35])).
% 0.20/0.51  fof(f275,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~r3_waybel_9(X0,X1,X2) | v3_yellow_6(sK6(X0,X1,X2),X0) | ~v7_waybel_0(sK6(X0,X1,X2)) | ~v4_orders_2(sK6(X0,X1,X2)) | v2_struct_0(sK6(X0,X1,X2))) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f274,f196])).
% 0.20/0.51  fof(f196,plain,(
% 0.20/0.51    ( ! [X2,X3,X1] : (l1_waybel_0(sK6(X1,X2,X3),X1) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l1_waybel_0(X2,X1) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~r3_waybel_9(X1,X2,X3)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f188,f77])).
% 0.20/0.51  fof(f188,plain,(
% 0.20/0.51    ( ! [X2,X3,X1] : (~r3_waybel_9(X1,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l1_waybel_0(X2,X1) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | l1_waybel_0(sK6(X1,X2,X3),X1) | ~l1_struct_0(X1)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f181])).
% 0.20/0.51  fof(f181,plain,(
% 0.20/0.51    ( ! [X2,X3,X1] : (~r3_waybel_9(X1,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l1_waybel_0(X2,X1) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | l1_waybel_0(sK6(X1,X2,X3),X1) | ~l1_waybel_0(X2,X1) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 0.20/0.51    inference(resolution,[],[f91,f104])).
% 0.20/0.51  fof(f104,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m2_yellow_6(X2,X0,X1) | l1_waybel_0(X2,X0) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f35])).
% 0.20/0.51  fof(f274,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~r3_waybel_9(X0,X1,X2) | v3_yellow_6(sK6(X0,X1,X2),X0) | ~l1_waybel_0(sK6(X0,X1,X2),X0) | ~v7_waybel_0(sK6(X0,X1,X2)) | ~v4_orders_2(sK6(X0,X1,X2)) | v2_struct_0(sK6(X0,X1,X2))) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f273,f75])).
% 0.20/0.51  fof(f75,plain,(
% 0.20/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.51  fof(f273,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r1_tarski(k1_xboole_0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~r3_waybel_9(X0,X1,X2) | v3_yellow_6(sK6(X0,X1,X2),X0) | ~l1_waybel_0(sK6(X0,X1,X2),X0) | ~v7_waybel_0(sK6(X0,X1,X2)) | ~v4_orders_2(sK6(X0,X1,X2)) | v2_struct_0(sK6(X0,X1,X2))) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f272])).
% 0.20/0.51  fof(f272,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r1_tarski(k1_xboole_0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~r3_waybel_9(X0,X1,X2) | v3_yellow_6(sK6(X0,X1,X2),X0) | ~l1_waybel_0(sK6(X0,X1,X2),X0) | ~v7_waybel_0(sK6(X0,X1,X2)) | ~v4_orders_2(sK6(X0,X1,X2)) | v2_struct_0(sK6(X0,X1,X2)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(superposition,[],[f202,f89])).
% 0.20/0.51  fof(f89,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_xboole_0 = k10_yellow_6(X0,X1) | v3_yellow_6(X1,X0) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f55])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (((v3_yellow_6(X1,X0) | k1_xboole_0 = k10_yellow_6(X0,X1)) & (k1_xboole_0 != k10_yellow_6(X0,X1) | ~v3_yellow_6(X1,X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_yellow_6)).
% 0.20/0.51  fof(f202,plain,(
% 0.20/0.51    ( ! [X6,X8,X7] : (~r1_tarski(k10_yellow_6(X6,sK6(X6,X7,X8)),X8) | ~m1_subset_1(X8,u1_struct_0(X6)) | ~l1_waybel_0(X7,X6) | ~v7_waybel_0(X7) | ~v4_orders_2(X7) | v2_struct_0(X7) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6) | ~r3_waybel_9(X6,X7,X8)) )),
% 0.20/0.51    inference(resolution,[],[f92,f106])).
% 0.20/0.51  fof(f106,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f38])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.51  fof(f92,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,sK6(X0,X1,X2))) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f57])).
% 0.20/0.51  fof(f596,plain,(
% 0.20/0.51    ~l1_struct_0(sK0) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.51    inference(resolution,[],[f595,f82])).
% 0.20/0.51  fof(f82,plain,(
% 0.20/0.51    ( ! [X0] : (~v2_struct_0(sK4(X0)) | v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f54])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    ! [X0] : (((v1_compts_1(X0) | (! [X2] : (~r3_waybel_9(X0,sK4(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(sK4(X0),k6_yellow_6(X0)) & l1_waybel_0(sK4(X0),X0) & v7_waybel_0(sK4(X0)) & v4_orders_2(sK4(X0)) & ~v2_struct_0(sK4(X0)))) & (! [X3] : ((r3_waybel_9(X0,X3,sK5(X0,X3)) & m1_subset_1(sK5(X0,X3),u1_struct_0(X0))) | ~r2_hidden(X3,k6_yellow_6(X0)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f51,f53,f52])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    ! [X0] : (? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(X1,k6_yellow_6(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (~r3_waybel_9(X0,sK4(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(sK4(X0),k6_yellow_6(X0)) & l1_waybel_0(sK4(X0),X0) & v7_waybel_0(sK4(X0)) & v4_orders_2(sK4(X0)) & ~v2_struct_0(sK4(X0))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    ! [X3,X0] : (? [X4] : (r3_waybel_9(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (r3_waybel_9(X0,X3,sK5(X0,X3)) & m1_subset_1(sK5(X0,X3),u1_struct_0(X0))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ! [X0] : (((v1_compts_1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(X1,k6_yellow_6(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (! [X3] : (? [X4] : (r3_waybel_9(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r2_hidden(X3,k6_yellow_6(X0)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(rectify,[],[f50])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ! [X0] : (((v1_compts_1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(X1,k6_yellow_6(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~r2_hidden(X1,k6_yellow_6(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~r2_hidden(X1,k6_yellow_6(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : ((? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~r2_hidden(X1,k6_yellow_6(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,axiom,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ~(! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~r3_waybel_9(X0,X1,X2)) & r2_hidden(X1,k6_yellow_6(X0))))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_yellow19)).
% 0.20/0.51  fof(f595,plain,(
% 0.20/0.51    v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f594,f65])).
% 0.20/0.51  fof(f594,plain,(
% 0.20/0.51    v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f593,f66])).
% 0.20/0.51  fof(f593,plain,(
% 0.20/0.51    v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f592,f67])).
% 0.20/0.51  fof(f592,plain,(
% 0.20/0.51    v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f591,f332])).
% 0.20/0.51  fof(f591,plain,(
% 0.20/0.51    v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.51    inference(resolution,[],[f590,f83])).
% 0.20/0.51  fof(f83,plain,(
% 0.20/0.51    ( ! [X0] : (v4_orders_2(sK4(X0)) | v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f54])).
% 0.20/0.51  fof(f590,plain,(
% 0.20/0.51    ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f589,f65])).
% 0.20/0.51  fof(f589,plain,(
% 0.20/0.51    ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f588,f66])).
% 0.20/0.51  fof(f588,plain,(
% 0.20/0.51    ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f587,f67])).
% 0.20/0.51  fof(f587,plain,(
% 0.20/0.51    ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f586,f332])).
% 0.20/0.51  fof(f586,plain,(
% 0.20/0.51    ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.51    inference(resolution,[],[f585,f84])).
% 0.20/0.51  fof(f84,plain,(
% 0.20/0.51    ( ! [X0] : (v7_waybel_0(sK4(X0)) | v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f54])).
% 0.20/0.51  fof(f585,plain,(
% 0.20/0.51    ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f584,f332])).
% 0.20/0.51  fof(f584,plain,(
% 0.20/0.51    ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0)),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f583])).
% 0.20/0.51  % (32651)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.51  fof(f583,plain,(
% 0.20/0.51    ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0)),
% 0.20/0.51    inference(resolution,[],[f582,f122])).
% 0.20/0.51  fof(f122,plain,(
% 0.20/0.51    ~v2_struct_0(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f121,f65])).
% 0.20/0.51  fof(f121,plain,(
% 0.20/0.51    ~v2_struct_0(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | v2_struct_0(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f120,f66])).
% 0.20/0.51  fof(f120,plain,(
% 0.20/0.51    ~v2_struct_0(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f119,f67])).
% 0.20/0.51  fof(f119,plain,(
% 0.20/0.51    ~v2_struct_0(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f118])).
% 0.20/0.51  fof(f118,plain,(
% 0.20/0.51    ~v2_struct_0(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.51    inference(resolution,[],[f116,f85])).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    ( ! [X0] : (l1_waybel_0(sK4(X0),X0) | v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f54])).
% 0.20/0.51  fof(f116,plain,(
% 0.20/0.51    ( ! [X0] : (~l1_waybel_0(X0,sK0) | ~v2_struct_0(sK2(X0)) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v1_compts_1(sK0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f115,f65])).
% 0.20/0.51  fof(f115,plain,(
% 0.20/0.51    ( ! [X0] : (~v2_struct_0(sK2(X0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | v1_compts_1(sK0)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f114])).
% 0.20/0.51  fof(f114,plain,(
% 0.20/0.51    ( ! [X0] : (~v2_struct_0(sK2(X0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | v1_compts_1(sK0)) )),
% 0.20/0.51    inference(resolution,[],[f101,f68])).
% 0.20/0.51  fof(f68,plain,(
% 0.20/0.51    ( ! [X3] : (m2_yellow_6(sK2(X3),sK0,X3) | ~l1_waybel_0(X3,sK0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | v1_compts_1(sK0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f47])).
% 0.20/0.51  fof(f582,plain,(
% 0.20/0.51    v2_struct_0(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f581,f332])).
% 0.20/0.51  fof(f581,plain,(
% 0.20/0.51    v2_struct_0(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0)),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f580])).
% 0.20/0.51  fof(f580,plain,(
% 0.20/0.51    v2_struct_0(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0)),
% 0.20/0.51    inference(resolution,[],[f579,f131])).
% 0.20/0.51  fof(f131,plain,(
% 0.20/0.51    v4_orders_2(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f130,f65])).
% 0.20/0.51  fof(f130,plain,(
% 0.20/0.51    v4_orders_2(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | v2_struct_0(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f129,f66])).
% 0.20/0.51  fof(f129,plain,(
% 0.20/0.51    v4_orders_2(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f128,f67])).
% 0.20/0.51  fof(f128,plain,(
% 0.20/0.51    v4_orders_2(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f127])).
% 0.20/0.51  fof(f127,plain,(
% 0.20/0.51    v4_orders_2(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.51    inference(resolution,[],[f125,f85])).
% 0.20/0.51  fof(f125,plain,(
% 0.20/0.51    ( ! [X0] : (~l1_waybel_0(X0,sK0) | v4_orders_2(sK2(X0)) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v1_compts_1(sK0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f124,f65])).
% 0.20/0.51  fof(f124,plain,(
% 0.20/0.51    ( ! [X0] : (v4_orders_2(sK2(X0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | v1_compts_1(sK0)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f123])).
% 0.20/0.51  fof(f123,plain,(
% 0.20/0.51    ( ! [X0] : (v4_orders_2(sK2(X0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | v1_compts_1(sK0)) )),
% 0.20/0.51    inference(resolution,[],[f102,f68])).
% 0.20/0.51  fof(f579,plain,(
% 0.20/0.51    ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f578,f332])).
% 0.20/0.51  fof(f578,plain,(
% 0.20/0.51    v2_struct_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0)),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f577])).
% 0.20/0.51  fof(f577,plain,(
% 0.20/0.51    v2_struct_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0)),
% 0.20/0.51    inference(resolution,[],[f576,f140])).
% 0.20/0.51  fof(f140,plain,(
% 0.20/0.51    v7_waybel_0(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f139,f65])).
% 0.20/0.51  fof(f139,plain,(
% 0.20/0.51    v7_waybel_0(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | v2_struct_0(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f138,f66])).
% 0.20/0.51  fof(f138,plain,(
% 0.20/0.51    v7_waybel_0(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f137,f67])).
% 0.20/0.51  fof(f137,plain,(
% 0.20/0.51    v7_waybel_0(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f136])).
% 0.20/0.51  fof(f136,plain,(
% 0.20/0.51    v7_waybel_0(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.51    inference(resolution,[],[f134,f85])).
% 0.20/0.51  fof(f134,plain,(
% 0.20/0.51    ( ! [X0] : (~l1_waybel_0(X0,sK0) | v7_waybel_0(sK2(X0)) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v1_compts_1(sK0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f133,f65])).
% 0.20/0.52  fof(f133,plain,(
% 0.20/0.52    ( ! [X0] : (v7_waybel_0(sK2(X0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | v1_compts_1(sK0)) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f132])).
% 0.20/0.52  fof(f132,plain,(
% 0.20/0.52    ( ! [X0] : (v7_waybel_0(sK2(X0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | v1_compts_1(sK0)) )),
% 0.20/0.52    inference(resolution,[],[f103,f68])).
% 0.20/0.52  fof(f576,plain,(
% 0.20/0.52    ~v7_waybel_0(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f575,f65])).
% 0.20/0.52  fof(f575,plain,(
% 0.20/0.52    ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | ~v7_waybel_0(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f574,f66])).
% 0.20/0.52  fof(f574,plain,(
% 0.20/0.52    ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | ~v7_waybel_0(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f573,f67])).
% 0.20/0.52  fof(f573,plain,(
% 0.20/0.52    ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | ~v7_waybel_0(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f572,f332])).
% 0.20/0.52  fof(f572,plain,(
% 0.20/0.52    ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | ~v7_waybel_0(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.52    inference(resolution,[],[f571,f85])).
% 0.20/0.52  fof(f571,plain,(
% 0.20/0.52    ~l1_waybel_0(sK4(sK0),sK0) | ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | ~v7_waybel_0(sK2(sK4(sK0))) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f570,f332])).
% 0.20/0.52  fof(f570,plain,(
% 0.20/0.52    ~v7_waybel_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0)),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f569])).
% 0.20/0.52  fof(f569,plain,(
% 0.20/0.52    ~v7_waybel_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_struct_0(sK0) | v1_compts_1(sK0)),
% 0.20/0.52    inference(resolution,[],[f568,f143])).
% 0.20/0.52  fof(f143,plain,(
% 0.20/0.52    ( ! [X0] : (l1_waybel_0(sK2(X0),sK0) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v1_compts_1(sK0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f142,f65])).
% 0.20/0.52  fof(f142,plain,(
% 0.20/0.52    ( ! [X0] : (l1_waybel_0(sK2(X0),sK0) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | v1_compts_1(sK0)) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f141])).
% 0.20/0.52  fof(f141,plain,(
% 0.20/0.52    ( ! [X0] : (l1_waybel_0(sK2(X0),sK0) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | v1_compts_1(sK0)) )),
% 0.20/0.52    inference(resolution,[],[f104,f68])).
% 0.20/0.52  fof(f568,plain,(
% 0.20/0.52    ~l1_waybel_0(sK2(sK4(sK0)),sK0) | ~v7_waybel_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0))),
% 0.20/0.52    inference(subsumption_resolution,[],[f567,f332])).
% 0.20/0.52  fof(f567,plain,(
% 0.20/0.52    ~l1_waybel_0(sK2(sK4(sK0)),sK0) | ~v7_waybel_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | v1_compts_1(sK0)),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f566])).
% 0.20/0.52  fof(f566,plain,(
% 0.20/0.52    ~l1_waybel_0(sK2(sK4(sK0)),sK0) | ~v7_waybel_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | v1_compts_1(sK0)),
% 0.20/0.52    inference(resolution,[],[f553,f69])).
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    ( ! [X3] : (v3_yellow_6(sK2(X3),sK0) | ~l1_waybel_0(X3,sK0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | v1_compts_1(sK0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f47])).
% 0.20/0.52  fof(f553,plain,(
% 0.20/0.52    ~v3_yellow_6(sK2(sK4(sK0)),sK0) | ~l1_waybel_0(sK2(sK4(sK0)),sK0) | ~v7_waybel_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0))),
% 0.20/0.52    inference(subsumption_resolution,[],[f552,f65])).
% 0.20/0.52  fof(f552,plain,(
% 0.20/0.52    ~v3_yellow_6(sK2(sK4(sK0)),sK0) | ~l1_waybel_0(sK2(sK4(sK0)),sK0) | ~v7_waybel_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | v2_struct_0(sK0) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0))),
% 0.20/0.52    inference(subsumption_resolution,[],[f551,f66])).
% 0.20/0.52  fof(f551,plain,(
% 0.20/0.52    ~v3_yellow_6(sK2(sK4(sK0)),sK0) | ~l1_waybel_0(sK2(sK4(sK0)),sK0) | ~v7_waybel_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0))),
% 0.20/0.52    inference(subsumption_resolution,[],[f550,f67])).
% 0.20/0.52  fof(f550,plain,(
% 0.20/0.52    ~v3_yellow_6(sK2(sK4(sK0)),sK0) | ~l1_waybel_0(sK2(sK4(sK0)),sK0) | ~v7_waybel_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0))),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f549])).
% 0.20/0.52  fof(f549,plain,(
% 0.20/0.52    k1_xboole_0 != k1_xboole_0 | ~v3_yellow_6(sK2(sK4(sK0)),sK0) | ~l1_waybel_0(sK2(sK4(sK0)),sK0) | ~v7_waybel_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0))),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f532])).
% 0.20/0.52  fof(f532,plain,(
% 0.20/0.52    k1_xboole_0 != k1_xboole_0 | ~v3_yellow_6(sK2(sK4(sK0)),sK0) | ~l1_waybel_0(sK2(sK4(sK0)),sK0) | ~v7_waybel_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | v2_struct_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | ~l1_waybel_0(sK2(sK4(sK0)),sK0) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~v7_waybel_0(sK2(sK4(sK0)))),
% 0.20/0.52    inference(superposition,[],[f88,f531])).
% 0.20/0.52  fof(f531,plain,(
% 0.20/0.52    k1_xboole_0 = k10_yellow_6(sK0,sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | ~l1_waybel_0(sK2(sK4(sK0)),sK0) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~v7_waybel_0(sK2(sK4(sK0)))),
% 0.20/0.52    inference(subsumption_resolution,[],[f530,f76])).
% 0.20/0.52  fof(f76,plain,(
% 0.20/0.52    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.52  fof(f530,plain,(
% 0.20/0.52    ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | k1_xboole_0 = k10_yellow_6(sK0,sK2(sK4(sK0))) | ~l1_waybel_0(sK2(sK4(sK0)),sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~v7_waybel_0(sK2(sK4(sK0)))),
% 0.20/0.52    inference(resolution,[],[f517,f75])).
% 0.20/0.52  fof(f517,plain,(
% 0.20/0.52    ( ! [X0] : (~r1_tarski(X0,sK7(sK0,sK2(sK4(sK0)),X0)) | ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | k10_yellow_6(sK0,sK2(sK4(sK0))) = X0 | ~l1_waybel_0(sK2(sK4(sK0)),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~v7_waybel_0(sK2(sK4(sK0)))) )),
% 0.20/0.52    inference(resolution,[],[f515,f106])).
% 0.20/0.52  fof(f515,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(sK7(sK0,sK2(sK4(sK0)),X0),X0) | ~v7_waybel_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | k10_yellow_6(sK0,sK2(sK4(sK0))) = X0 | ~l1_waybel_0(sK2(sK4(sK0)),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f514,f65])).
% 0.20/0.52  fof(f514,plain,(
% 0.20/0.52    ( ! [X0] : (~l1_waybel_0(sK2(sK4(sK0)),sK0) | ~v7_waybel_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | k10_yellow_6(sK0,sK2(sK4(sK0))) = X0 | r2_hidden(sK7(sK0,sK2(sK4(sK0)),X0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | v2_struct_0(sK0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f513,f66])).
% 0.20/0.52  fof(f513,plain,(
% 0.20/0.52    ( ! [X0] : (~l1_waybel_0(sK2(sK4(sK0)),sK0) | ~v7_waybel_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | k10_yellow_6(sK0,sK2(sK4(sK0))) = X0 | r2_hidden(sK7(sK0,sK2(sK4(sK0)),X0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f512,f67])).
% 0.20/0.52  fof(f512,plain,(
% 0.20/0.52    ( ! [X0] : (~l1_waybel_0(sK2(sK4(sK0)),sK0) | ~v7_waybel_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | k10_yellow_6(sK0,sK2(sK4(sK0))) = X0 | r2_hidden(sK7(sK0,sK2(sK4(sK0)),X0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f511])).
% 0.20/0.52  fof(f511,plain,(
% 0.20/0.52    ( ! [X0] : (~l1_waybel_0(sK2(sK4(sK0)),sK0) | ~v7_waybel_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | k10_yellow_6(sK0,sK2(sK4(sK0))) = X0 | r2_hidden(sK7(sK0,sK2(sK4(sK0)),X0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | k10_yellow_6(sK0,sK2(sK4(sK0))) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK2(sK4(sK0)),sK0) | ~v7_waybel_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.52    inference(resolution,[],[f493,f97])).
% 0.20/0.52  fof(f97,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) | k10_yellow_6(X0,X1) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f64])).
% 0.20/0.52  fof(f64,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | (((~r1_waybel_0(X0,X1,sK8(X0,X1,X2)) & m1_connsp_2(sK8(X0,X1,X2),X0,sK7(X0,X1,X2))) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK7(X0,X1,X2))) | r2_hidden(sK7(X0,X1,X2),X2)) & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)))) & (! [X6] : (((r2_hidden(X6,X2) | (~r1_waybel_0(X0,X1,sK9(X0,X1,X6)) & m1_connsp_2(sK9(X0,X1,X6),X0,X6))) & (! [X8] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6)) | ~r2_hidden(X6,X2))) | ~m1_subset_1(X6,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f60,f63,f62,f61])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    ! [X2,X1,X0] : (? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0))) => ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,sK7(X0,X1,X2))) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK7(X0,X1,X2))) | r2_hidden(sK7(X0,X1,X2),X2)) & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    ! [X2,X1,X0] : (? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,sK7(X0,X1,X2))) => (~r1_waybel_0(X0,X1,sK8(X0,X1,X2)) & m1_connsp_2(sK8(X0,X1,X2),X0,sK7(X0,X1,X2))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    ! [X6,X1,X0] : (? [X7] : (~r1_waybel_0(X0,X1,X7) & m1_connsp_2(X7,X0,X6)) => (~r1_waybel_0(X0,X1,sK9(X0,X1,X6)) & m1_connsp_2(sK9(X0,X1,X6),X0,X6)))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f60,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X6] : (((r2_hidden(X6,X2) | ? [X7] : (~r1_waybel_0(X0,X1,X7) & m1_connsp_2(X7,X0,X6))) & (! [X8] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6)) | ~r2_hidden(X6,X2))) | ~m1_subset_1(X6,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(rectify,[],[f59])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3))) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f58])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : (((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | r2_hidden(X3,X2))) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3))) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(nnf_transformation,[],[f33])).
% 0.20/0.52  % (32639)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (k10_yellow_6(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) <=> ! [X4] : (m1_connsp_2(X4,X0,X3) => r1_waybel_0(X0,X1,X4))))))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_yellow_6)).
% 0.20/0.52  fof(f493,plain,(
% 0.20/0.52    ( ! [X2] : (~m1_subset_1(sK7(sK0,sK2(sK4(sK0)),X2),u1_struct_0(sK0)) | ~l1_waybel_0(sK2(sK4(sK0)),sK0) | ~v7_waybel_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | k10_yellow_6(sK0,sK2(sK4(sK0))) = X2 | r2_hidden(sK7(sK0,sK2(sK4(sK0)),X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f492,f332])).
% 0.20/0.52  fof(f492,plain,(
% 0.20/0.52    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK2(sK4(sK0)),sK0) | ~v7_waybel_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | k10_yellow_6(sK0,sK2(sK4(sK0))) = X2 | r2_hidden(sK7(sK0,sK2(sK4(sK0)),X2),X2) | ~m1_subset_1(sK7(sK0,sK2(sK4(sK0)),X2),u1_struct_0(sK0)) | v1_compts_1(sK0) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f491,f65])).
% 0.20/0.52  fof(f491,plain,(
% 0.20/0.52    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK2(sK4(sK0)),sK0) | ~v7_waybel_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | v2_struct_0(sK0) | k10_yellow_6(sK0,sK2(sK4(sK0))) = X2 | r2_hidden(sK7(sK0,sK2(sK4(sK0)),X2),X2) | ~m1_subset_1(sK7(sK0,sK2(sK4(sK0)),X2),u1_struct_0(sK0)) | v1_compts_1(sK0) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f490,f66])).
% 0.20/0.52  fof(f490,plain,(
% 0.20/0.52    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK2(sK4(sK0)),sK0) | ~v7_waybel_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | k10_yellow_6(sK0,sK2(sK4(sK0))) = X2 | r2_hidden(sK7(sK0,sK2(sK4(sK0)),X2),X2) | ~m1_subset_1(sK7(sK0,sK2(sK4(sK0)),X2),u1_struct_0(sK0)) | v1_compts_1(sK0) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f477,f67])).
% 0.20/0.52  fof(f477,plain,(
% 0.20/0.52    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK2(sK4(sK0)),sK0) | ~v7_waybel_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | k10_yellow_6(sK0,sK2(sK4(sK0))) = X2 | r2_hidden(sK7(sK0,sK2(sK4(sK0)),X2),X2) | ~m1_subset_1(sK7(sK0,sK2(sK4(sK0)),X2),u1_struct_0(sK0)) | v1_compts_1(sK0) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0))) )),
% 0.20/0.52    inference(resolution,[],[f469,f239])).
% 0.20/0.52  fof(f239,plain,(
% 0.20/0.52    ( ! [X0] : (~r3_waybel_9(sK0,sK2(sK4(sK0)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v1_compts_1(sK0) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f238,f65])).
% 0.20/0.52  fof(f238,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK2(sK4(sK0)),X0) | v2_struct_0(sK0) | v1_compts_1(sK0) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f237,f66])).
% 0.20/0.52  fof(f237,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK2(sK4(sK0)),X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | v1_compts_1(sK0) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f236,f67])).
% 0.20/0.52  fof(f236,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK2(sK4(sK0)),X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | v1_compts_1(sK0) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0))) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f233])).
% 0.20/0.52  fof(f233,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK2(sK4(sK0)),X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | v1_compts_1(sK0) | ~l1_waybel_0(sK4(sK0),sK0) | ~v7_waybel_0(sK4(sK0)) | ~v4_orders_2(sK4(sK0)) | v2_struct_0(sK4(sK0)) | v1_compts_1(sK0)) )),
% 0.20/0.52    inference(resolution,[],[f232,f68])).
% 0.20/0.52  fof(f232,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m2_yellow_6(X1,X0,sK4(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v1_compts_1(X0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f231,f82])).
% 0.20/0.52  fof(f231,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m2_yellow_6(X1,X0,sK4(X0)) | v2_struct_0(sK4(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v1_compts_1(X0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f230,f83])).
% 0.20/0.52  fof(f230,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m2_yellow_6(X1,X0,sK4(X0)) | ~v4_orders_2(sK4(X0)) | v2_struct_0(sK4(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v1_compts_1(X0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f229,f84])).
% 0.20/0.52  % (32644)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.52  fof(f229,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m2_yellow_6(X1,X0,sK4(X0)) | ~v7_waybel_0(sK4(X0)) | ~v4_orders_2(sK4(X0)) | v2_struct_0(sK4(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v1_compts_1(X0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f228,f85])).
% 0.20/0.52  fof(f228,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m2_yellow_6(X1,X0,sK4(X0)) | ~l1_waybel_0(sK4(X0),X0) | ~v7_waybel_0(sK4(X0)) | ~v4_orders_2(sK4(X0)) | v2_struct_0(sK4(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v1_compts_1(X0)) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f227])).
% 0.20/0.52  fof(f227,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m2_yellow_6(X1,X0,sK4(X0)) | ~l1_waybel_0(sK4(X0),X0) | ~v7_waybel_0(sK4(X0)) | ~v4_orders_2(sK4(X0)) | v2_struct_0(sK4(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v1_compts_1(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(resolution,[],[f93,f87])).
% 0.20/0.52  fof(f87,plain,(
% 0.20/0.52    ( ! [X2,X0] : (~r3_waybel_9(X0,sK4(X0),X2) | v1_compts_1(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f54])).
% 0.20/0.52  fof(f93,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,axiom,(
% 0.20/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_waybel_9(X0,X2,X3) => r3_waybel_9(X0,X1,X3))))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_waybel_9)).
% 0.20/0.52  fof(f469,plain,(
% 0.20/0.52    ( ! [X6,X4,X5] : (r3_waybel_9(X4,X5,sK7(X4,X5,X6)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4))) | ~l1_waybel_0(X5,X4) | ~v7_waybel_0(X5) | ~v4_orders_2(X5) | v2_struct_0(X5) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4) | k10_yellow_6(X4,X5) = X6 | r2_hidden(sK7(X4,X5,X6),X6)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f467,f97])).
% 0.20/0.52  fof(f467,plain,(
% 0.20/0.52    ( ! [X6,X4,X5] : (r2_hidden(sK7(X4,X5,X6),X6) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4))) | ~l1_waybel_0(X5,X4) | ~v7_waybel_0(X5) | ~v4_orders_2(X5) | v2_struct_0(X5) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4) | k10_yellow_6(X4,X5) = X6 | r3_waybel_9(X4,X5,sK7(X4,X5,X6)) | ~m1_subset_1(sK7(X4,X5,X6),u1_struct_0(X4))) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f460])).
% 0.20/0.52  fof(f460,plain,(
% 0.20/0.52    ( ! [X6,X4,X5] : (r2_hidden(sK7(X4,X5,X6),X6) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4))) | ~l1_waybel_0(X5,X4) | ~v7_waybel_0(X5) | ~v4_orders_2(X5) | v2_struct_0(X5) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4) | k10_yellow_6(X4,X5) = X6 | r3_waybel_9(X4,X5,sK7(X4,X5,X6)) | ~m1_subset_1(sK7(X4,X5,X6),u1_struct_0(X4)) | ~l1_waybel_0(X5,X4) | ~v7_waybel_0(X5) | ~v4_orders_2(X5) | v2_struct_0(X5) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) )),
% 0.20/0.52    inference(resolution,[],[f458,f90])).
% 0.20/0.52  fof(f90,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X2,k10_yellow_6(X0,X1)) | r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,axiom,(
% 0.20/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,X1)) => r3_waybel_9(X0,X1,X2)))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_waybel_9)).
% 0.20/0.52  fof(f458,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r2_hidden(sK7(X0,X1,X2),k10_yellow_6(X0,X1)) | r2_hidden(sK7(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | k10_yellow_6(X0,X1) = X2) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f457,f105])).
% 0.20/0.52  fof(f105,plain,(
% 0.20/0.52    ( ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_yellow_6)).
% 0.20/0.52  fof(f457,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k10_yellow_6(X0,X1) = X2 | r2_hidden(sK7(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | r2_hidden(sK7(X0,X1,X2),k10_yellow_6(X0,X1)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f456,f97])).
% 0.20/0.52  fof(f456,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k10_yellow_6(X0,X1) = X2 | r2_hidden(sK7(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | r2_hidden(sK7(X0,X1,X2),k10_yellow_6(X0,X1)) | ~m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f455])).
% 0.20/0.52  fof(f455,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k10_yellow_6(X0,X1) = X2 | r2_hidden(sK7(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | r2_hidden(sK7(X0,X1,X2),k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | r2_hidden(sK7(X0,X1,X2),k10_yellow_6(X0,X1)) | ~m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(resolution,[],[f433,f108])).
% 0.20/0.52  fof(f108,plain,(
% 0.20/0.52    ( ! [X6,X0,X1] : (~r1_waybel_0(X0,X1,sK9(X0,X1,X6)) | r2_hidden(X6,k10_yellow_6(X0,X1)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(equality_resolution,[],[f96])).
% 0.20/0.52  fof(f96,plain,(
% 0.20/0.52    ( ! [X6,X2,X0,X1] : (r2_hidden(X6,X2) | ~r1_waybel_0(X0,X1,sK9(X0,X1,X6)) | ~m1_subset_1(X6,u1_struct_0(X0)) | k10_yellow_6(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f64])).
% 0.20/0.52  fof(f433,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (r1_waybel_0(X0,X1,sK9(X0,X2,sK7(X0,X1,X3))) | k10_yellow_6(X0,X1) = X3 | r2_hidden(sK7(X0,X1,X3),X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | r2_hidden(sK7(X0,X1,X3),k10_yellow_6(X0,X2)) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f432,f105])).
% 0.20/0.52  fof(f432,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (r1_waybel_0(X0,X1,sK9(X0,X2,sK7(X0,X1,X3))) | k10_yellow_6(X0,X1) = X3 | r2_hidden(sK7(X0,X1,X3),X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | r2_hidden(sK7(X0,X1,X3),k10_yellow_6(X0,X2)) | ~m1_subset_1(k10_yellow_6(X0,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f431,f97])).
% 0.20/0.52  fof(f431,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (r1_waybel_0(X0,X1,sK9(X0,X2,sK7(X0,X1,X3))) | k10_yellow_6(X0,X1) = X3 | r2_hidden(sK7(X0,X1,X3),X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | r2_hidden(sK7(X0,X1,X3),k10_yellow_6(X0,X2)) | ~m1_subset_1(sK7(X0,X1,X3),u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2)) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f428])).
% 0.20/0.52  fof(f428,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (r1_waybel_0(X0,X1,sK9(X0,X2,sK7(X0,X1,X3))) | k10_yellow_6(X0,X1) = X3 | r2_hidden(sK7(X0,X1,X3),X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | r2_hidden(sK7(X0,X1,X3),k10_yellow_6(X0,X2)) | ~m1_subset_1(sK7(X0,X1,X3),u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(resolution,[],[f98,f109])).
% 0.20/0.52  fof(f109,plain,(
% 0.20/0.52    ( ! [X6,X0,X1] : (m1_connsp_2(sK9(X0,X1,X6),X0,X6) | r2_hidden(X6,k10_yellow_6(X0,X1)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(equality_resolution,[],[f95])).
% 0.20/0.52  fof(f95,plain,(
% 0.20/0.52    ( ! [X6,X2,X0,X1] : (r2_hidden(X6,X2) | m1_connsp_2(sK9(X0,X1,X6),X0,X6) | ~m1_subset_1(X6,u1_struct_0(X0)) | k10_yellow_6(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f64])).
% 0.20/0.52  fof(f98,plain,(
% 0.20/0.52    ( ! [X2,X0,X5,X1] : (~m1_connsp_2(X5,X0,sK7(X0,X1,X2)) | r1_waybel_0(X0,X1,X5) | k10_yellow_6(X0,X1) = X2 | r2_hidden(sK7(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f64])).
% 0.20/0.52  fof(f88,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_xboole_0 != k10_yellow_6(X0,X1) | ~v3_yellow_6(X1,X0) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f55])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (32654)------------------------------
% 0.20/0.52  % (32654)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (32654)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (32654)Memory used [KB]: 2046
% 0.20/0.52  % (32654)Time elapsed: 0.092 s
% 0.20/0.52  % (32654)------------------------------
% 0.20/0.52  % (32654)------------------------------
% 1.20/0.52  % (32635)Success in time 0.159 s
%------------------------------------------------------------------------------
