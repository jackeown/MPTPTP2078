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
% DateTime   : Thu Dec  3 13:23:38 EST 2020

% Result     : Theorem 2.14s
% Output     : Refutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :  163 (16378 expanded)
%              Number of leaves         :   31 (5439 expanded)
%              Depth                    :   23
%              Number of atoms          : 1064 (198233 expanded)
%              Number of equality atoms :   14 (  58 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f381,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f113,f118,f123,f128,f133,f137,f141,f332,f380])).

fof(f380,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6 ),
    inference(avatar_contradiction_clause,[],[f379])).

fof(f379,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6 ),
    inference(subsumption_resolution,[],[f373,f73])).

fof(f73,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f373,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3(sK0,sK1))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6 ),
    inference(unit_resulting_resolution,[],[f371,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f371,plain,
    ( r2_hidden(sK3(sK0,sK1),k1_xboole_0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6 ),
    inference(subsumption_resolution,[],[f370,f63])).

fof(f63,plain,(
    ~ v2_struct_0(sK0) ),
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

fof(f370,plain,
    ( r2_hidden(sK3(sK0,sK1),k1_xboole_0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6 ),
    inference(subsumption_resolution,[],[f369,f64])).

fof(f64,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f369,plain,
    ( r2_hidden(sK3(sK0,sK1),k1_xboole_0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6 ),
    inference(subsumption_resolution,[],[f368,f65])).

fof(f65,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f368,plain,
    ( r2_hidden(sK3(sK0,sK1),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6 ),
    inference(subsumption_resolution,[],[f367,f356])).

fof(f356,plain,
    ( ~ v2_struct_0(sK6(sK0,sK1,sK3(sK0,sK1)))
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6 ),
    inference(unit_resulting_resolution,[],[f63,f142,f132,f127,f122,f117,f346,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(X2)
      | ~ m2_yellow_6(X2,X0,X1)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_yellow_6)).

fof(f346,plain,
    ( m2_yellow_6(sK6(sK0,sK1,sK3(sK0,sK1)),sK0,sK1)
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6 ),
    inference(unit_resulting_resolution,[],[f63,f64,f65,f132,f127,f122,f117,f335,f336,f88])).

fof(f88,plain,(
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
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f29,f55])).

fof(f55,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_waybel_9)).

fof(f336,plain,
    ( r3_waybel_9(sK0,sK1,sK3(sK0,sK1))
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6 ),
    inference(unit_resulting_resolution,[],[f63,f64,f65,f108,f132,f127,f122,f117,f76])).

fof(f76,plain,(
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
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f47])).

fof(f47,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l37_yellow19)).

fof(f108,plain,
    ( v1_compts_1(sK0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl8_1
  <=> v1_compts_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f335,plain,
    ( m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6 ),
    inference(unit_resulting_resolution,[],[f63,f64,f65,f108,f132,f127,f122,f117,f75])).

fof(f75,plain,(
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
    inference(cnf_transformation,[],[f48])).

fof(f117,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl8_3
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f122,plain,
    ( v7_waybel_0(sK1)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl8_4
  <=> v7_waybel_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f127,plain,
    ( v4_orders_2(sK1)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl8_5
  <=> v4_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f132,plain,
    ( ~ v2_struct_0(sK1)
    | spl8_6 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl8_6
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f142,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f65,f74])).

fof(f74,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f367,plain,
    ( r2_hidden(sK3(sK0,sK1),k1_xboole_0)
    | v2_struct_0(sK6(sK0,sK1,sK3(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6 ),
    inference(subsumption_resolution,[],[f366,f357])).

fof(f357,plain,
    ( v4_orders_2(sK6(sK0,sK1,sK3(sK0,sK1)))
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6 ),
    inference(unit_resulting_resolution,[],[f63,f142,f132,f127,f122,f117,f346,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f366,plain,
    ( r2_hidden(sK3(sK0,sK1),k1_xboole_0)
    | ~ v4_orders_2(sK6(sK0,sK1,sK3(sK0,sK1)))
    | v2_struct_0(sK6(sK0,sK1,sK3(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6 ),
    inference(subsumption_resolution,[],[f365,f358])).

fof(f358,plain,
    ( v7_waybel_0(sK6(sK0,sK1,sK3(sK0,sK1)))
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6 ),
    inference(unit_resulting_resolution,[],[f63,f142,f132,f127,f122,f117,f346,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f365,plain,
    ( r2_hidden(sK3(sK0,sK1),k1_xboole_0)
    | ~ v7_waybel_0(sK6(sK0,sK1,sK3(sK0,sK1)))
    | ~ v4_orders_2(sK6(sK0,sK1,sK3(sK0,sK1)))
    | v2_struct_0(sK6(sK0,sK1,sK3(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6 ),
    inference(subsumption_resolution,[],[f364,f359])).

fof(f359,plain,
    ( l1_waybel_0(sK6(sK0,sK1,sK3(sK0,sK1)),sK0)
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6 ),
    inference(unit_resulting_resolution,[],[f63,f142,f132,f127,f122,f117,f346,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(X2,X0)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f364,plain,
    ( r2_hidden(sK3(sK0,sK1),k1_xboole_0)
    | ~ l1_waybel_0(sK6(sK0,sK1,sK3(sK0,sK1)),sK0)
    | ~ v7_waybel_0(sK6(sK0,sK1,sK3(sK0,sK1)))
    | ~ v4_orders_2(sK6(sK0,sK1,sK3(sK0,sK1)))
    | v2_struct_0(sK6(sK0,sK1,sK3(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6 ),
    inference(subsumption_resolution,[],[f363,f355])).

fof(f355,plain,
    ( ~ v3_yellow_6(sK6(sK0,sK1,sK3(sK0,sK1)),sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6 ),
    inference(unit_resulting_resolution,[],[f346,f112])).

fof(f112,plain,
    ( ! [X2] :
        ( ~ v3_yellow_6(X2,sK0)
        | ~ m2_yellow_6(X2,sK0,sK1) )
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl8_2
  <=> ! [X2] :
        ( ~ v3_yellow_6(X2,sK0)
        | ~ m2_yellow_6(X2,sK0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f363,plain,
    ( r2_hidden(sK3(sK0,sK1),k1_xboole_0)
    | v3_yellow_6(sK6(sK0,sK1,sK3(sK0,sK1)),sK0)
    | ~ l1_waybel_0(sK6(sK0,sK1,sK3(sK0,sK1)),sK0)
    | ~ v7_waybel_0(sK6(sK0,sK1,sK3(sK0,sK1)))
    | ~ v4_orders_2(sK6(sK0,sK1,sK3(sK0,sK1)))
    | v2_struct_0(sK6(sK0,sK1,sK3(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6 ),
    inference(superposition,[],[f347,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( v3_yellow_6(X1,X0)
      | k1_xboole_0 = k10_yellow_6(X0,X1)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_yellow_6)).

fof(f347,plain,
    ( r2_hidden(sK3(sK0,sK1),k10_yellow_6(sK0,sK6(sK0,sK1,sK3(sK0,sK1))))
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6 ),
    inference(unit_resulting_resolution,[],[f63,f64,f65,f132,f127,f122,f117,f335,f336,f89])).

fof(f89,plain,(
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
    inference(cnf_transformation,[],[f56])).

fof(f332,plain,
    ( spl8_1
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(avatar_contradiction_clause,[],[f331])).

fof(f331,plain,
    ( $false
    | spl8_1
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f327,f300])).

fof(f300,plain,
    ( r3_waybel_9(sK0,sK2(sK4(sK0)),sK7(k10_yellow_6(sK0,sK2(sK4(sK0))),k1_xboole_0))
    | spl8_1
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f63,f64,f65,f156,f157,f158,f159,f219,f268,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r3_waybel_9(X0,X1,X2)
      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_waybel_9)).

fof(f268,plain,
    ( m1_subset_1(sK7(k10_yellow_6(sK0,sK2(sK4(sK0))),k1_xboole_0),u1_struct_0(sK0))
    | spl8_1
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f181,f219,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f181,plain,
    ( m1_subset_1(k10_yellow_6(sK0,sK2(sK4(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl8_1
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f63,f64,f65,f156,f157,f158,f159,f95])).

fof(f95,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_yellow_6)).

fof(f219,plain,
    ( r2_hidden(sK7(k10_yellow_6(sK0,sK2(sK4(sK0))),k1_xboole_0),k10_yellow_6(sK0,sK2(sK4(sK0))))
    | spl8_1
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f196,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK7(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f60,f61])).

fof(f61,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f196,plain,
    ( ~ r1_tarski(k10_yellow_6(sK0,sK2(sK4(sK0))),k1_xboole_0)
    | spl8_1
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f73,f180,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f180,plain,
    ( k1_xboole_0 != k10_yellow_6(sK0,sK2(sK4(sK0)))
    | spl8_1
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f63,f64,f65,f156,f157,f158,f149,f159,f85])).

fof(f85,plain,(
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
    inference(cnf_transformation,[],[f54])).

fof(f149,plain,
    ( v3_yellow_6(sK2(sK4(sK0)),sK0)
    | spl8_1
    | ~ spl8_7 ),
    inference(unit_resulting_resolution,[],[f145,f143,f144,f146,f136])).

fof(f136,plain,
    ( ! [X3] :
        ( ~ v7_waybel_0(X3)
        | v2_struct_0(X3)
        | ~ v4_orders_2(X3)
        | v3_yellow_6(sK2(X3),sK0)
        | ~ l1_waybel_0(X3,sK0) )
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl8_7
  <=> ! [X3] :
        ( v3_yellow_6(sK2(X3),sK0)
        | v2_struct_0(X3)
        | ~ v4_orders_2(X3)
        | ~ v7_waybel_0(X3)
        | ~ l1_waybel_0(X3,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f146,plain,
    ( l1_waybel_0(sK4(sK0),sK0)
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f63,f64,f65,f109,f82])).

fof(f82,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | l1_waybel_0(sK4(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f50,f52,f51])).

fof(f51,plain,(
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

fof(f52,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( r3_waybel_9(X0,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X3,sK5(X0,X3))
        & m1_subset_1(sK5(X0,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

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
    inference(rectify,[],[f49])).

fof(f49,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_yellow19)).

fof(f109,plain,
    ( ~ v1_compts_1(sK0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f107])).

fof(f144,plain,
    ( v4_orders_2(sK4(sK0))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f63,f64,f65,f109,f80])).

fof(f80,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | v4_orders_2(sK4(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f143,plain,
    ( ~ v2_struct_0(sK4(sK0))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f63,f64,f65,f109,f79])).

fof(f79,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ~ v2_struct_0(sK4(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f145,plain,
    ( v7_waybel_0(sK4(sK0))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f63,f64,f65,f109,f81])).

fof(f81,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | v7_waybel_0(sK4(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f159,plain,
    ( l1_waybel_0(sK2(sK4(sK0)),sK0)
    | spl8_1
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f63,f142,f143,f144,f145,f146,f148,f94])).

fof(f148,plain,
    ( m2_yellow_6(sK2(sK4(sK0)),sK0,sK4(sK0))
    | spl8_1
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f145,f143,f144,f146,f140])).

fof(f140,plain,
    ( ! [X3] :
        ( ~ v7_waybel_0(X3)
        | v2_struct_0(X3)
        | ~ v4_orders_2(X3)
        | m2_yellow_6(sK2(X3),sK0,X3)
        | ~ l1_waybel_0(X3,sK0) )
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl8_8
  <=> ! [X3] :
        ( m2_yellow_6(sK2(X3),sK0,X3)
        | v2_struct_0(X3)
        | ~ v4_orders_2(X3)
        | ~ v7_waybel_0(X3)
        | ~ l1_waybel_0(X3,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f158,plain,
    ( v7_waybel_0(sK2(sK4(sK0)))
    | spl8_1
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f63,f142,f143,f144,f145,f146,f148,f93])).

fof(f157,plain,
    ( v4_orders_2(sK2(sK4(sK0)))
    | spl8_1
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f63,f142,f143,f144,f145,f146,f148,f92])).

fof(f156,plain,
    ( ~ v2_struct_0(sK2(sK4(sK0)))
    | spl8_1
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f63,f142,f143,f144,f145,f146,f148,f91])).

fof(f327,plain,
    ( ~ r3_waybel_9(sK0,sK2(sK4(sK0)),sK7(k10_yellow_6(sK0,sK2(sK4(sK0))),k1_xboole_0))
    | spl8_1
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f63,f64,f65,f143,f144,f145,f146,f148,f268,f301,f90])).

fof(f90,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_waybel_9)).

fof(f301,plain,
    ( ~ r3_waybel_9(sK0,sK4(sK0),sK7(k10_yellow_6(sK0,sK2(sK4(sK0))),k1_xboole_0))
    | spl8_1
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f63,f64,f65,f109,f268,f84])).

fof(f84,plain,(
    ! [X2,X0] :
      ( v1_compts_1(X0)
      | ~ r3_waybel_9(X0,sK4(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f141,plain,
    ( spl8_1
    | spl8_8 ),
    inference(avatar_split_clause,[],[f66,f139,f107])).

fof(f66,plain,(
    ! [X3] :
      ( m2_yellow_6(sK2(X3),sK0,X3)
      | ~ l1_waybel_0(X3,sK0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f137,plain,
    ( spl8_1
    | spl8_7 ),
    inference(avatar_split_clause,[],[f67,f135,f107])).

fof(f67,plain,(
    ! [X3] :
      ( v3_yellow_6(sK2(X3),sK0)
      | ~ l1_waybel_0(X3,sK0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f133,plain,
    ( ~ spl8_1
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f68,f130,f107])).

fof(f68,plain,
    ( ~ v2_struct_0(sK1)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f128,plain,
    ( ~ spl8_1
    | spl8_5 ),
    inference(avatar_split_clause,[],[f69,f125,f107])).

fof(f69,plain,
    ( v4_orders_2(sK1)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f123,plain,
    ( ~ spl8_1
    | spl8_4 ),
    inference(avatar_split_clause,[],[f70,f120,f107])).

fof(f70,plain,
    ( v7_waybel_0(sK1)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f118,plain,
    ( ~ spl8_1
    | spl8_3 ),
    inference(avatar_split_clause,[],[f71,f115,f107])).

fof(f71,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f113,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f72,f111,f107])).

fof(f72,plain,(
    ! [X2] :
      ( ~ v3_yellow_6(X2,sK0)
      | ~ m2_yellow_6(X2,sK0,sK1)
      | ~ v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:14:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (24275)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (24293)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.55  % (24263)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.55  % (24262)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.56  % (24265)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.56  % (24268)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.56  % (24286)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.57  % (24269)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.57  % (24288)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.57  % (24292)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.57  % (24270)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.57  % (24281)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.57  % (24278)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.58  % (24264)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.58  % (24273)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.70/0.58  % (24273)Refutation not found, incomplete strategy% (24273)------------------------------
% 1.70/0.58  % (24273)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.58  % (24273)Termination reason: Refutation not found, incomplete strategy
% 1.70/0.58  
% 1.70/0.58  % (24273)Memory used [KB]: 10746
% 1.70/0.58  % (24273)Time elapsed: 0.170 s
% 1.70/0.58  % (24273)------------------------------
% 1.70/0.58  % (24273)------------------------------
% 1.70/0.58  % (24279)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.70/0.58  % (24283)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.70/0.58  % (24277)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.70/0.58  % (24291)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.70/0.58  % (24285)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.70/0.59  % (24276)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.70/0.59  % (24284)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.70/0.59  % (24287)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.70/0.59  % (24285)Refutation not found, incomplete strategy% (24285)------------------------------
% 1.70/0.59  % (24285)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.59  % (24285)Termination reason: Refutation not found, incomplete strategy
% 1.70/0.59  
% 1.70/0.59  % (24285)Memory used [KB]: 10874
% 1.70/0.59  % (24285)Time elapsed: 0.183 s
% 1.70/0.59  % (24285)------------------------------
% 1.70/0.59  % (24285)------------------------------
% 1.82/0.59  % (24266)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.82/0.59  % (24267)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.82/0.59  % (24266)Refutation not found, incomplete strategy% (24266)------------------------------
% 1.82/0.59  % (24266)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.82/0.59  % (24266)Termination reason: Refutation not found, incomplete strategy
% 1.82/0.59  
% 1.82/0.59  % (24266)Memory used [KB]: 6268
% 1.82/0.59  % (24266)Time elapsed: 0.174 s
% 1.82/0.59  % (24266)------------------------------
% 1.82/0.59  % (24266)------------------------------
% 1.82/0.60  % (24271)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.82/0.60  % (24282)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.82/0.60  % (24274)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.82/0.60  % (24274)Refutation not found, incomplete strategy% (24274)------------------------------
% 1.82/0.60  % (24274)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.82/0.60  % (24274)Termination reason: Refutation not found, incomplete strategy
% 1.82/0.60  
% 1.82/0.60  % (24274)Memory used [KB]: 10746
% 1.82/0.60  % (24274)Time elapsed: 0.184 s
% 1.82/0.60  % (24274)------------------------------
% 1.82/0.60  % (24274)------------------------------
% 1.82/0.60  % (24280)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.82/0.60  % (24271)Refutation not found, incomplete strategy% (24271)------------------------------
% 1.82/0.60  % (24271)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.82/0.61  % (24290)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.82/0.62  % (24271)Termination reason: Refutation not found, incomplete strategy
% 1.82/0.62  
% 1.82/0.62  % (24271)Memory used [KB]: 10746
% 1.82/0.62  % (24271)Time elapsed: 0.181 s
% 1.82/0.62  % (24271)------------------------------
% 1.82/0.62  % (24271)------------------------------
% 1.82/0.62  % (24280)Refutation not found, incomplete strategy% (24280)------------------------------
% 1.82/0.62  % (24280)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.82/0.62  % (24280)Termination reason: Refutation not found, incomplete strategy
% 1.82/0.62  
% 2.11/0.62  % (24280)Memory used [KB]: 10746
% 2.11/0.62  % (24280)Time elapsed: 0.204 s
% 2.11/0.62  % (24280)------------------------------
% 2.11/0.62  % (24280)------------------------------
% 2.14/0.65  % (24290)Refutation found. Thanks to Tanya!
% 2.14/0.65  % SZS status Theorem for theBenchmark
% 2.14/0.65  % SZS output start Proof for theBenchmark
% 2.14/0.65  fof(f381,plain,(
% 2.14/0.65    $false),
% 2.14/0.65    inference(avatar_sat_refutation,[],[f113,f118,f123,f128,f133,f137,f141,f332,f380])).
% 2.14/0.65  fof(f380,plain,(
% 2.14/0.65    ~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6),
% 2.14/0.65    inference(avatar_contradiction_clause,[],[f379])).
% 2.14/0.65  fof(f379,plain,(
% 2.14/0.65    $false | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6)),
% 2.14/0.65    inference(subsumption_resolution,[],[f373,f73])).
% 2.14/0.65  fof(f73,plain,(
% 2.14/0.65    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.14/0.65    inference(cnf_transformation,[],[f3])).
% 2.14/0.65  fof(f3,axiom,(
% 2.14/0.65    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.14/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.14/0.66  fof(f373,plain,(
% 2.14/0.66    ~r1_tarski(k1_xboole_0,sK3(sK0,sK1)) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6)),
% 2.14/0.66    inference(unit_resulting_resolution,[],[f371,f102])).
% 2.14/0.66  fof(f102,plain,(
% 2.14/0.66    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.14/0.66    inference(cnf_transformation,[],[f37])).
% 2.14/0.66  fof(f37,plain,(
% 2.14/0.66    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.14/0.66    inference(ennf_transformation,[],[f5])).
% 2.14/0.66  fof(f5,axiom,(
% 2.14/0.66    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.14/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 2.14/0.66  fof(f371,plain,(
% 2.14/0.66    r2_hidden(sK3(sK0,sK1),k1_xboole_0) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6)),
% 2.14/0.66    inference(subsumption_resolution,[],[f370,f63])).
% 2.14/0.66  fof(f63,plain,(
% 2.14/0.66    ~v2_struct_0(sK0)),
% 2.14/0.66    inference(cnf_transformation,[],[f46])).
% 2.14/0.66  fof(f46,plain,(
% 2.14/0.66    ((! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,sK1)) & l1_waybel_0(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1)) | ~v1_compts_1(sK0)) & (! [X3] : ((v3_yellow_6(sK2(X3),sK0) & m2_yellow_6(sK2(X3),sK0,X3)) | ~l1_waybel_0(X3,sK0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.14/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f42,f45,f44,f43])).
% 2.14/0.66  fof(f43,plain,(
% 2.14/0.66    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ((? [X1] : (! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,X1)) & l1_waybel_0(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(sK0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,sK0) & m2_yellow_6(X4,sK0,X3)) | ~l1_waybel_0(X3,sK0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.14/0.66    introduced(choice_axiom,[])).
% 2.14/0.66  fof(f44,plain,(
% 2.14/0.66    ? [X1] : (! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,X1)) & l1_waybel_0(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,sK1)) & l1_waybel_0(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1))),
% 2.14/0.66    introduced(choice_axiom,[])).
% 2.14/0.66  fof(f45,plain,(
% 2.14/0.66    ! [X3] : (? [X4] : (v3_yellow_6(X4,sK0) & m2_yellow_6(X4,sK0,X3)) => (v3_yellow_6(sK2(X3),sK0) & m2_yellow_6(sK2(X3),sK0,X3)))),
% 2.14/0.66    introduced(choice_axiom,[])).
% 2.14/0.66  fof(f42,plain,(
% 2.14/0.66    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.14/0.66    inference(rectify,[],[f41])).
% 2.14/0.66  fof(f41,plain,(
% 2.14/0.66    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.14/0.66    inference(flattening,[],[f40])).
% 2.14/0.66  fof(f40,plain,(
% 2.14/0.66    ? [X0] : (((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | v1_compts_1(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.14/0.66    inference(nnf_transformation,[],[f18])).
% 2.14/0.66  fof(f18,plain,(
% 2.14/0.66    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.14/0.66    inference(flattening,[],[f17])).
% 2.14/0.66  fof(f17,plain,(
% 2.14/0.66    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.14/0.66    inference(ennf_transformation,[],[f16])).
% 2.14/0.66  fof(f16,negated_conjecture,(
% 2.14/0.66    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)))))),
% 2.14/0.66    inference(negated_conjecture,[],[f15])).
% 2.14/0.67  fof(f15,conjecture,(
% 2.14/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)))))),
% 2.14/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_yellow19)).
% 2.14/0.67  fof(f370,plain,(
% 2.14/0.67    r2_hidden(sK3(sK0,sK1),k1_xboole_0) | v2_struct_0(sK0) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6)),
% 2.14/0.67    inference(subsumption_resolution,[],[f369,f64])).
% 2.14/0.67  fof(f64,plain,(
% 2.14/0.67    v2_pre_topc(sK0)),
% 2.14/0.67    inference(cnf_transformation,[],[f46])).
% 2.14/0.67  fof(f369,plain,(
% 2.14/0.67    r2_hidden(sK3(sK0,sK1),k1_xboole_0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6)),
% 2.14/0.67    inference(subsumption_resolution,[],[f368,f65])).
% 2.14/0.67  fof(f65,plain,(
% 2.14/0.67    l1_pre_topc(sK0)),
% 2.14/0.67    inference(cnf_transformation,[],[f46])).
% 2.14/0.67  fof(f368,plain,(
% 2.14/0.67    r2_hidden(sK3(sK0,sK1),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6)),
% 2.14/0.67    inference(subsumption_resolution,[],[f367,f356])).
% 2.14/0.67  fof(f356,plain,(
% 2.14/0.67    ~v2_struct_0(sK6(sK0,sK1,sK3(sK0,sK1))) | (~spl8_1 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6)),
% 2.14/0.67    inference(unit_resulting_resolution,[],[f63,f142,f132,f127,f122,f117,f346,f91])).
% 2.14/0.67  fof(f91,plain,(
% 2.14/0.67    ( ! [X2,X0,X1] : (~v2_struct_0(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.14/0.67    inference(cnf_transformation,[],[f33])).
% 2.14/0.67  fof(f33,plain,(
% 2.14/0.67    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.14/0.67    inference(flattening,[],[f32])).
% 2.14/0.67  fof(f32,plain,(
% 2.14/0.67    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.14/0.67    inference(ennf_transformation,[],[f8])).
% 2.14/0.67  fof(f8,axiom,(
% 2.14/0.67    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))))),
% 2.14/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_yellow_6)).
% 2.14/0.67  fof(f346,plain,(
% 2.14/0.67    m2_yellow_6(sK6(sK0,sK1,sK3(sK0,sK1)),sK0,sK1) | (~spl8_1 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6)),
% 2.14/0.67    inference(unit_resulting_resolution,[],[f63,f64,f65,f132,f127,f122,f117,f335,f336,f88])).
% 2.14/0.67  fof(f88,plain,(
% 2.14/0.67    ( ! [X2,X0,X1] : (m2_yellow_6(sK6(X0,X1,X2),X0,X1) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.14/0.67    inference(cnf_transformation,[],[f56])).
% 2.14/0.67  fof(f56,plain,(
% 2.14/0.67    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k10_yellow_6(X0,sK6(X0,X1,X2))) & m2_yellow_6(sK6(X0,X1,X2),X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.14/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f29,f55])).
% 2.14/0.67  fof(f55,plain,(
% 2.14/0.67    ! [X2,X1,X0] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) => (r2_hidden(X2,k10_yellow_6(X0,sK6(X0,X1,X2))) & m2_yellow_6(sK6(X0,X1,X2),X0,X1)))),
% 2.14/0.67    introduced(choice_axiom,[])).
% 2.14/0.67  fof(f29,plain,(
% 2.14/0.67    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.14/0.67    inference(flattening,[],[f28])).
% 2.14/0.67  fof(f28,plain,(
% 2.14/0.67    ! [X0] : (! [X1] : (! [X2] : ((? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.14/0.67    inference(ennf_transformation,[],[f12])).
% 2.14/0.67  fof(f12,axiom,(
% 2.14/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m2_yellow_6(X3,X0,X1) => ~r2_hidden(X2,k10_yellow_6(X0,X3))) & r3_waybel_9(X0,X1,X2)))))),
% 2.14/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_waybel_9)).
% 2.14/0.67  fof(f336,plain,(
% 2.14/0.67    r3_waybel_9(sK0,sK1,sK3(sK0,sK1)) | (~spl8_1 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6)),
% 2.14/0.67    inference(unit_resulting_resolution,[],[f63,f64,f65,f108,f132,f127,f122,f117,f76])).
% 2.14/0.67  fof(f76,plain,(
% 2.14/0.67    ( ! [X0,X1] : (r3_waybel_9(X0,X1,sK3(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.14/0.67    inference(cnf_transformation,[],[f48])).
% 2.14/0.67  fof(f48,plain,(
% 2.14/0.67    ! [X0] : (! [X1] : ((r3_waybel_9(X0,X1,sK3(X0,X1)) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.14/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f47])).
% 2.14/0.67  fof(f47,plain,(
% 2.14/0.67    ! [X1,X0] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) => (r3_waybel_9(X0,X1,sK3(X0,X1)) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))))),
% 2.14/0.67    introduced(choice_axiom,[])).
% 2.14/0.67  fof(f21,plain,(
% 2.14/0.67    ! [X0] : (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.14/0.67    inference(flattening,[],[f20])).
% 2.14/0.67  fof(f20,plain,(
% 2.14/0.67    ! [X0] : ((! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | ~v1_compts_1(X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.14/0.67    inference(ennf_transformation,[],[f13])).
% 2.14/0.67  fof(f13,axiom,(
% 2.14/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))))))),
% 2.14/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l37_yellow19)).
% 2.14/0.67  fof(f108,plain,(
% 2.14/0.67    v1_compts_1(sK0) | ~spl8_1),
% 2.14/0.67    inference(avatar_component_clause,[],[f107])).
% 2.14/0.67  fof(f107,plain,(
% 2.14/0.67    spl8_1 <=> v1_compts_1(sK0)),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 2.14/0.67  fof(f335,plain,(
% 2.14/0.67    m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) | (~spl8_1 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6)),
% 2.14/0.67    inference(unit_resulting_resolution,[],[f63,f64,f65,f108,f132,f127,f122,f117,f75])).
% 2.14/0.67  fof(f75,plain,(
% 2.14/0.67    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.14/0.67    inference(cnf_transformation,[],[f48])).
% 2.14/0.67  fof(f117,plain,(
% 2.14/0.67    l1_waybel_0(sK1,sK0) | ~spl8_3),
% 2.14/0.67    inference(avatar_component_clause,[],[f115])).
% 2.14/0.67  fof(f115,plain,(
% 2.14/0.67    spl8_3 <=> l1_waybel_0(sK1,sK0)),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 2.14/0.67  fof(f122,plain,(
% 2.14/0.67    v7_waybel_0(sK1) | ~spl8_4),
% 2.14/0.67    inference(avatar_component_clause,[],[f120])).
% 2.14/0.67  fof(f120,plain,(
% 2.14/0.67    spl8_4 <=> v7_waybel_0(sK1)),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 2.14/0.67  fof(f127,plain,(
% 2.14/0.67    v4_orders_2(sK1) | ~spl8_5),
% 2.14/0.67    inference(avatar_component_clause,[],[f125])).
% 2.14/0.67  fof(f125,plain,(
% 2.14/0.67    spl8_5 <=> v4_orders_2(sK1)),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 2.14/0.67  fof(f132,plain,(
% 2.14/0.67    ~v2_struct_0(sK1) | spl8_6),
% 2.14/0.67    inference(avatar_component_clause,[],[f130])).
% 2.14/0.67  fof(f130,plain,(
% 2.14/0.67    spl8_6 <=> v2_struct_0(sK1)),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 2.14/0.67  fof(f142,plain,(
% 2.14/0.67    l1_struct_0(sK0)),
% 2.14/0.67    inference(unit_resulting_resolution,[],[f65,f74])).
% 2.14/0.67  fof(f74,plain,(
% 2.14/0.67    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.14/0.67    inference(cnf_transformation,[],[f19])).
% 2.14/0.67  fof(f19,plain,(
% 2.14/0.67    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.14/0.67    inference(ennf_transformation,[],[f6])).
% 2.14/0.67  fof(f6,axiom,(
% 2.14/0.67    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.14/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 2.14/0.67  fof(f367,plain,(
% 2.14/0.67    r2_hidden(sK3(sK0,sK1),k1_xboole_0) | v2_struct_0(sK6(sK0,sK1,sK3(sK0,sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6)),
% 2.14/0.67    inference(subsumption_resolution,[],[f366,f357])).
% 2.14/0.67  fof(f357,plain,(
% 2.14/0.67    v4_orders_2(sK6(sK0,sK1,sK3(sK0,sK1))) | (~spl8_1 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6)),
% 2.14/0.67    inference(unit_resulting_resolution,[],[f63,f142,f132,f127,f122,f117,f346,f92])).
% 2.14/0.67  fof(f92,plain,(
% 2.14/0.67    ( ! [X2,X0,X1] : (v4_orders_2(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.14/0.67    inference(cnf_transformation,[],[f33])).
% 2.14/0.67  fof(f366,plain,(
% 2.14/0.67    r2_hidden(sK3(sK0,sK1),k1_xboole_0) | ~v4_orders_2(sK6(sK0,sK1,sK3(sK0,sK1))) | v2_struct_0(sK6(sK0,sK1,sK3(sK0,sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6)),
% 2.14/0.67    inference(subsumption_resolution,[],[f365,f358])).
% 2.14/0.67  fof(f358,plain,(
% 2.14/0.67    v7_waybel_0(sK6(sK0,sK1,sK3(sK0,sK1))) | (~spl8_1 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6)),
% 2.14/0.67    inference(unit_resulting_resolution,[],[f63,f142,f132,f127,f122,f117,f346,f93])).
% 2.14/0.67  fof(f93,plain,(
% 2.14/0.67    ( ! [X2,X0,X1] : (v7_waybel_0(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.14/0.67    inference(cnf_transformation,[],[f33])).
% 2.14/0.67  fof(f365,plain,(
% 2.14/0.67    r2_hidden(sK3(sK0,sK1),k1_xboole_0) | ~v7_waybel_0(sK6(sK0,sK1,sK3(sK0,sK1))) | ~v4_orders_2(sK6(sK0,sK1,sK3(sK0,sK1))) | v2_struct_0(sK6(sK0,sK1,sK3(sK0,sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6)),
% 2.14/0.67    inference(subsumption_resolution,[],[f364,f359])).
% 2.14/0.67  fof(f359,plain,(
% 2.14/0.67    l1_waybel_0(sK6(sK0,sK1,sK3(sK0,sK1)),sK0) | (~spl8_1 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6)),
% 2.14/0.67    inference(unit_resulting_resolution,[],[f63,f142,f132,f127,f122,f117,f346,f94])).
% 2.14/0.67  fof(f94,plain,(
% 2.14/0.67    ( ! [X2,X0,X1] : (l1_waybel_0(X2,X0) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.14/0.67    inference(cnf_transformation,[],[f33])).
% 2.14/0.67  fof(f364,plain,(
% 2.14/0.67    r2_hidden(sK3(sK0,sK1),k1_xboole_0) | ~l1_waybel_0(sK6(sK0,sK1,sK3(sK0,sK1)),sK0) | ~v7_waybel_0(sK6(sK0,sK1,sK3(sK0,sK1))) | ~v4_orders_2(sK6(sK0,sK1,sK3(sK0,sK1))) | v2_struct_0(sK6(sK0,sK1,sK3(sK0,sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6)),
% 2.14/0.67    inference(subsumption_resolution,[],[f363,f355])).
% 2.14/0.67  fof(f355,plain,(
% 2.14/0.67    ~v3_yellow_6(sK6(sK0,sK1,sK3(sK0,sK1)),sK0) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6)),
% 2.14/0.67    inference(unit_resulting_resolution,[],[f346,f112])).
% 2.14/0.67  fof(f112,plain,(
% 2.14/0.67    ( ! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,sK1)) ) | ~spl8_2),
% 2.14/0.67    inference(avatar_component_clause,[],[f111])).
% 2.14/0.67  fof(f111,plain,(
% 2.14/0.67    spl8_2 <=> ! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,sK1))),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 2.14/0.67  fof(f363,plain,(
% 2.14/0.67    r2_hidden(sK3(sK0,sK1),k1_xboole_0) | v3_yellow_6(sK6(sK0,sK1,sK3(sK0,sK1)),sK0) | ~l1_waybel_0(sK6(sK0,sK1,sK3(sK0,sK1)),sK0) | ~v7_waybel_0(sK6(sK0,sK1,sK3(sK0,sK1))) | ~v4_orders_2(sK6(sK0,sK1,sK3(sK0,sK1))) | v2_struct_0(sK6(sK0,sK1,sK3(sK0,sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_1 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6)),
% 2.14/0.67    inference(superposition,[],[f347,f86])).
% 2.14/0.67  fof(f86,plain,(
% 2.14/0.67    ( ! [X0,X1] : (v3_yellow_6(X1,X0) | k1_xboole_0 = k10_yellow_6(X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.14/0.67    inference(cnf_transformation,[],[f54])).
% 2.14/0.67  fof(f54,plain,(
% 2.14/0.67    ! [X0] : (! [X1] : (((v3_yellow_6(X1,X0) | k1_xboole_0 = k10_yellow_6(X0,X1)) & (k1_xboole_0 != k10_yellow_6(X0,X1) | ~v3_yellow_6(X1,X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.14/0.67    inference(nnf_transformation,[],[f25])).
% 2.14/0.67  fof(f25,plain,(
% 2.14/0.67    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.14/0.67    inference(flattening,[],[f24])).
% 2.14/0.67  fof(f24,plain,(
% 2.14/0.67    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.14/0.67    inference(ennf_transformation,[],[f9])).
% 2.14/0.67  fof(f9,axiom,(
% 2.14/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1))))),
% 2.14/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_yellow_6)).
% 2.14/0.67  fof(f347,plain,(
% 2.14/0.67    r2_hidden(sK3(sK0,sK1),k10_yellow_6(sK0,sK6(sK0,sK1,sK3(sK0,sK1)))) | (~spl8_1 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6)),
% 2.14/0.67    inference(unit_resulting_resolution,[],[f63,f64,f65,f132,f127,f122,f117,f335,f336,f89])).
% 2.14/0.67  fof(f89,plain,(
% 2.14/0.67    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,sK6(X0,X1,X2))) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.14/0.67    inference(cnf_transformation,[],[f56])).
% 2.14/0.67  fof(f332,plain,(
% 2.14/0.67    spl8_1 | ~spl8_7 | ~spl8_8),
% 2.14/0.67    inference(avatar_contradiction_clause,[],[f331])).
% 2.14/0.67  fof(f331,plain,(
% 2.14/0.67    $false | (spl8_1 | ~spl8_7 | ~spl8_8)),
% 2.14/0.67    inference(subsumption_resolution,[],[f327,f300])).
% 2.14/0.67  fof(f300,plain,(
% 2.14/0.67    r3_waybel_9(sK0,sK2(sK4(sK0)),sK7(k10_yellow_6(sK0,sK2(sK4(sK0))),k1_xboole_0)) | (spl8_1 | ~spl8_7 | ~spl8_8)),
% 2.14/0.67    inference(unit_resulting_resolution,[],[f63,f64,f65,f156,f157,f158,f159,f219,f268,f87])).
% 2.14/0.67  fof(f87,plain,(
% 2.14/0.67    ( ! [X2,X0,X1] : (r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.14/0.67    inference(cnf_transformation,[],[f27])).
% 2.14/0.67  fof(f27,plain,(
% 2.14/0.67    ! [X0] : (! [X1] : (! [X2] : (r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.14/0.67    inference(flattening,[],[f26])).
% 2.14/0.67  fof(f26,plain,(
% 2.14/0.67    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.14/0.67    inference(ennf_transformation,[],[f10])).
% 2.14/0.67  fof(f10,axiom,(
% 2.14/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,X1)) => r3_waybel_9(X0,X1,X2)))))),
% 2.14/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_waybel_9)).
% 2.14/0.67  fof(f268,plain,(
% 2.14/0.67    m1_subset_1(sK7(k10_yellow_6(sK0,sK2(sK4(sK0))),k1_xboole_0),u1_struct_0(sK0)) | (spl8_1 | ~spl8_7 | ~spl8_8)),
% 2.14/0.67    inference(unit_resulting_resolution,[],[f181,f219,f103])).
% 2.14/0.67  fof(f103,plain,(
% 2.14/0.67    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.14/0.67    inference(cnf_transformation,[],[f39])).
% 2.14/0.67  fof(f39,plain,(
% 2.14/0.67    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.14/0.67    inference(flattening,[],[f38])).
% 2.14/0.67  fof(f38,plain,(
% 2.14/0.67    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.14/0.67    inference(ennf_transformation,[],[f4])).
% 2.14/0.67  fof(f4,axiom,(
% 2.14/0.67    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.14/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 2.14/0.67  fof(f181,plain,(
% 2.14/0.67    m1_subset_1(k10_yellow_6(sK0,sK2(sK4(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) | (spl8_1 | ~spl8_8)),
% 2.14/0.67    inference(unit_resulting_resolution,[],[f63,f64,f65,f156,f157,f158,f159,f95])).
% 2.14/0.67  fof(f95,plain,(
% 2.14/0.67    ( ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.14/0.67    inference(cnf_transformation,[],[f35])).
% 2.14/0.67  fof(f35,plain,(
% 2.14/0.67    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.14/0.67    inference(flattening,[],[f34])).
% 2.14/0.67  fof(f34,plain,(
% 2.14/0.67    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.14/0.67    inference(ennf_transformation,[],[f7])).
% 2.14/0.67  fof(f7,axiom,(
% 2.14/0.67    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.14/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_yellow_6)).
% 2.14/0.67  fof(f219,plain,(
% 2.14/0.67    r2_hidden(sK7(k10_yellow_6(sK0,sK2(sK4(sK0))),k1_xboole_0),k10_yellow_6(sK0,sK2(sK4(sK0)))) | (spl8_1 | ~spl8_7 | ~spl8_8)),
% 2.14/0.67    inference(unit_resulting_resolution,[],[f196,f100])).
% 2.14/0.67  fof(f100,plain,(
% 2.14/0.67    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK7(X0,X1),X0)) )),
% 2.14/0.67    inference(cnf_transformation,[],[f62])).
% 2.14/0.67  fof(f62,plain,(
% 2.14/0.67    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.14/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f60,f61])).
% 2.14/0.67  fof(f61,plain,(
% 2.14/0.67    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 2.14/0.67    introduced(choice_axiom,[])).
% 2.14/0.67  fof(f60,plain,(
% 2.14/0.67    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.14/0.67    inference(rectify,[],[f59])).
% 2.14/0.67  fof(f59,plain,(
% 2.14/0.67    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.14/0.67    inference(nnf_transformation,[],[f36])).
% 2.14/0.67  fof(f36,plain,(
% 2.14/0.67    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.14/0.67    inference(ennf_transformation,[],[f1])).
% 2.14/0.67  fof(f1,axiom,(
% 2.14/0.67    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.14/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.14/0.67  fof(f196,plain,(
% 2.14/0.67    ~r1_tarski(k10_yellow_6(sK0,sK2(sK4(sK0))),k1_xboole_0) | (spl8_1 | ~spl8_7 | ~spl8_8)),
% 2.14/0.67    inference(unit_resulting_resolution,[],[f73,f180,f98])).
% 2.14/0.67  fof(f98,plain,(
% 2.14/0.67    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.14/0.67    inference(cnf_transformation,[],[f58])).
% 2.14/0.67  fof(f58,plain,(
% 2.14/0.67    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.14/0.67    inference(flattening,[],[f57])).
% 2.14/0.67  fof(f57,plain,(
% 2.14/0.67    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.14/0.67    inference(nnf_transformation,[],[f2])).
% 2.14/0.67  fof(f2,axiom,(
% 2.14/0.67    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.14/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.14/0.67  fof(f180,plain,(
% 2.14/0.67    k1_xboole_0 != k10_yellow_6(sK0,sK2(sK4(sK0))) | (spl8_1 | ~spl8_7 | ~spl8_8)),
% 2.14/0.67    inference(unit_resulting_resolution,[],[f63,f64,f65,f156,f157,f158,f149,f159,f85])).
% 2.14/0.67  fof(f85,plain,(
% 2.14/0.67    ( ! [X0,X1] : (k1_xboole_0 != k10_yellow_6(X0,X1) | ~v3_yellow_6(X1,X0) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.14/0.67    inference(cnf_transformation,[],[f54])).
% 2.14/0.67  fof(f149,plain,(
% 2.14/0.67    v3_yellow_6(sK2(sK4(sK0)),sK0) | (spl8_1 | ~spl8_7)),
% 2.14/0.67    inference(unit_resulting_resolution,[],[f145,f143,f144,f146,f136])).
% 2.14/0.67  fof(f136,plain,(
% 2.14/0.67    ( ! [X3] : (~v7_waybel_0(X3) | v2_struct_0(X3) | ~v4_orders_2(X3) | v3_yellow_6(sK2(X3),sK0) | ~l1_waybel_0(X3,sK0)) ) | ~spl8_7),
% 2.14/0.67    inference(avatar_component_clause,[],[f135])).
% 2.14/0.67  fof(f135,plain,(
% 2.14/0.67    spl8_7 <=> ! [X3] : (v3_yellow_6(sK2(X3),sK0) | v2_struct_0(X3) | ~v4_orders_2(X3) | ~v7_waybel_0(X3) | ~l1_waybel_0(X3,sK0))),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 2.14/0.67  fof(f146,plain,(
% 2.14/0.67    l1_waybel_0(sK4(sK0),sK0) | spl8_1),
% 2.14/0.67    inference(unit_resulting_resolution,[],[f63,f64,f65,f109,f82])).
% 2.14/0.67  fof(f82,plain,(
% 2.14/0.67    ( ! [X0] : (v1_compts_1(X0) | l1_waybel_0(sK4(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.14/0.67    inference(cnf_transformation,[],[f53])).
% 2.14/0.67  fof(f53,plain,(
% 2.14/0.67    ! [X0] : (((v1_compts_1(X0) | (! [X2] : (~r3_waybel_9(X0,sK4(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(sK4(X0),k6_yellow_6(X0)) & l1_waybel_0(sK4(X0),X0) & v7_waybel_0(sK4(X0)) & v4_orders_2(sK4(X0)) & ~v2_struct_0(sK4(X0)))) & (! [X3] : ((r3_waybel_9(X0,X3,sK5(X0,X3)) & m1_subset_1(sK5(X0,X3),u1_struct_0(X0))) | ~r2_hidden(X3,k6_yellow_6(X0)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.14/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f50,f52,f51])).
% 2.14/0.67  fof(f51,plain,(
% 2.14/0.67    ! [X0] : (? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(X1,k6_yellow_6(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (~r3_waybel_9(X0,sK4(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(sK4(X0),k6_yellow_6(X0)) & l1_waybel_0(sK4(X0),X0) & v7_waybel_0(sK4(X0)) & v4_orders_2(sK4(X0)) & ~v2_struct_0(sK4(X0))))),
% 2.14/0.67    introduced(choice_axiom,[])).
% 2.14/0.67  fof(f52,plain,(
% 2.14/0.67    ! [X3,X0] : (? [X4] : (r3_waybel_9(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (r3_waybel_9(X0,X3,sK5(X0,X3)) & m1_subset_1(sK5(X0,X3),u1_struct_0(X0))))),
% 2.14/0.67    introduced(choice_axiom,[])).
% 2.14/0.67  fof(f50,plain,(
% 2.14/0.67    ! [X0] : (((v1_compts_1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(X1,k6_yellow_6(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (! [X3] : (? [X4] : (r3_waybel_9(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r2_hidden(X3,k6_yellow_6(X0)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.14/0.67    inference(rectify,[],[f49])).
% 2.14/0.67  fof(f49,plain,(
% 2.14/0.67    ! [X0] : (((v1_compts_1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(X1,k6_yellow_6(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~r2_hidden(X1,k6_yellow_6(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.14/0.67    inference(nnf_transformation,[],[f23])).
% 2.14/0.67  fof(f23,plain,(
% 2.14/0.67    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~r2_hidden(X1,k6_yellow_6(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.14/0.67    inference(flattening,[],[f22])).
% 2.14/0.67  fof(f22,plain,(
% 2.14/0.67    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : ((? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~r2_hidden(X1,k6_yellow_6(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.14/0.67    inference(ennf_transformation,[],[f14])).
% 2.14/0.67  fof(f14,axiom,(
% 2.14/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ~(! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~r3_waybel_9(X0,X1,X2)) & r2_hidden(X1,k6_yellow_6(X0))))))),
% 2.14/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_yellow19)).
% 2.14/0.67  fof(f109,plain,(
% 2.14/0.67    ~v1_compts_1(sK0) | spl8_1),
% 2.14/0.67    inference(avatar_component_clause,[],[f107])).
% 2.14/0.67  fof(f144,plain,(
% 2.14/0.67    v4_orders_2(sK4(sK0)) | spl8_1),
% 2.14/0.67    inference(unit_resulting_resolution,[],[f63,f64,f65,f109,f80])).
% 2.14/0.67  fof(f80,plain,(
% 2.14/0.67    ( ! [X0] : (v1_compts_1(X0) | v4_orders_2(sK4(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.14/0.67    inference(cnf_transformation,[],[f53])).
% 2.14/0.67  fof(f143,plain,(
% 2.14/0.67    ~v2_struct_0(sK4(sK0)) | spl8_1),
% 2.14/0.67    inference(unit_resulting_resolution,[],[f63,f64,f65,f109,f79])).
% 2.14/0.67  fof(f79,plain,(
% 2.14/0.67    ( ! [X0] : (v1_compts_1(X0) | ~v2_struct_0(sK4(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.14/0.67    inference(cnf_transformation,[],[f53])).
% 2.14/0.67  fof(f145,plain,(
% 2.14/0.67    v7_waybel_0(sK4(sK0)) | spl8_1),
% 2.14/0.67    inference(unit_resulting_resolution,[],[f63,f64,f65,f109,f81])).
% 2.14/0.67  fof(f81,plain,(
% 2.14/0.67    ( ! [X0] : (v1_compts_1(X0) | v7_waybel_0(sK4(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.14/0.67    inference(cnf_transformation,[],[f53])).
% 2.14/0.67  fof(f159,plain,(
% 2.14/0.67    l1_waybel_0(sK2(sK4(sK0)),sK0) | (spl8_1 | ~spl8_8)),
% 2.14/0.67    inference(unit_resulting_resolution,[],[f63,f142,f143,f144,f145,f146,f148,f94])).
% 2.14/0.67  fof(f148,plain,(
% 2.14/0.67    m2_yellow_6(sK2(sK4(sK0)),sK0,sK4(sK0)) | (spl8_1 | ~spl8_8)),
% 2.14/0.67    inference(unit_resulting_resolution,[],[f145,f143,f144,f146,f140])).
% 2.14/0.67  fof(f140,plain,(
% 2.14/0.67    ( ! [X3] : (~v7_waybel_0(X3) | v2_struct_0(X3) | ~v4_orders_2(X3) | m2_yellow_6(sK2(X3),sK0,X3) | ~l1_waybel_0(X3,sK0)) ) | ~spl8_8),
% 2.14/0.67    inference(avatar_component_clause,[],[f139])).
% 2.14/0.67  fof(f139,plain,(
% 2.14/0.67    spl8_8 <=> ! [X3] : (m2_yellow_6(sK2(X3),sK0,X3) | v2_struct_0(X3) | ~v4_orders_2(X3) | ~v7_waybel_0(X3) | ~l1_waybel_0(X3,sK0))),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 2.14/0.67  fof(f158,plain,(
% 2.14/0.67    v7_waybel_0(sK2(sK4(sK0))) | (spl8_1 | ~spl8_8)),
% 2.14/0.67    inference(unit_resulting_resolution,[],[f63,f142,f143,f144,f145,f146,f148,f93])).
% 2.14/0.67  fof(f157,plain,(
% 2.14/0.67    v4_orders_2(sK2(sK4(sK0))) | (spl8_1 | ~spl8_8)),
% 2.14/0.67    inference(unit_resulting_resolution,[],[f63,f142,f143,f144,f145,f146,f148,f92])).
% 2.14/0.67  fof(f156,plain,(
% 2.14/0.67    ~v2_struct_0(sK2(sK4(sK0))) | (spl8_1 | ~spl8_8)),
% 2.14/0.67    inference(unit_resulting_resolution,[],[f63,f142,f143,f144,f145,f146,f148,f91])).
% 2.14/0.67  fof(f327,plain,(
% 2.14/0.67    ~r3_waybel_9(sK0,sK2(sK4(sK0)),sK7(k10_yellow_6(sK0,sK2(sK4(sK0))),k1_xboole_0)) | (spl8_1 | ~spl8_7 | ~spl8_8)),
% 2.14/0.67    inference(unit_resulting_resolution,[],[f63,f64,f65,f143,f144,f145,f146,f148,f268,f301,f90])).
% 2.14/0.67  fof(f90,plain,(
% 2.14/0.67    ( ! [X2,X0,X3,X1] : (r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.14/0.67    inference(cnf_transformation,[],[f31])).
% 2.14/0.67  fof(f31,plain,(
% 2.14/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.14/0.67    inference(flattening,[],[f30])).
% 2.14/0.67  fof(f30,plain,(
% 2.14/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.14/0.67    inference(ennf_transformation,[],[f11])).
% 2.14/0.67  fof(f11,axiom,(
% 2.14/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_waybel_9(X0,X2,X3) => r3_waybel_9(X0,X1,X3))))))),
% 2.14/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_waybel_9)).
% 2.14/0.67  fof(f301,plain,(
% 2.14/0.67    ~r3_waybel_9(sK0,sK4(sK0),sK7(k10_yellow_6(sK0,sK2(sK4(sK0))),k1_xboole_0)) | (spl8_1 | ~spl8_7 | ~spl8_8)),
% 2.14/0.67    inference(unit_resulting_resolution,[],[f63,f64,f65,f109,f268,f84])).
% 2.14/0.67  fof(f84,plain,(
% 2.14/0.67    ( ! [X2,X0] : (v1_compts_1(X0) | ~r3_waybel_9(X0,sK4(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.14/0.67    inference(cnf_transformation,[],[f53])).
% 2.14/0.67  fof(f141,plain,(
% 2.14/0.67    spl8_1 | spl8_8),
% 2.14/0.67    inference(avatar_split_clause,[],[f66,f139,f107])).
% 2.14/0.67  fof(f66,plain,(
% 2.14/0.67    ( ! [X3] : (m2_yellow_6(sK2(X3),sK0,X3) | ~l1_waybel_0(X3,sK0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | v1_compts_1(sK0)) )),
% 2.14/0.67    inference(cnf_transformation,[],[f46])).
% 2.14/0.67  fof(f137,plain,(
% 2.14/0.67    spl8_1 | spl8_7),
% 2.14/0.67    inference(avatar_split_clause,[],[f67,f135,f107])).
% 2.14/0.67  fof(f67,plain,(
% 2.14/0.67    ( ! [X3] : (v3_yellow_6(sK2(X3),sK0) | ~l1_waybel_0(X3,sK0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | v1_compts_1(sK0)) )),
% 2.14/0.67    inference(cnf_transformation,[],[f46])).
% 2.14/0.67  fof(f133,plain,(
% 2.14/0.67    ~spl8_1 | ~spl8_6),
% 2.14/0.67    inference(avatar_split_clause,[],[f68,f130,f107])).
% 2.14/0.67  fof(f68,plain,(
% 2.14/0.67    ~v2_struct_0(sK1) | ~v1_compts_1(sK0)),
% 2.14/0.67    inference(cnf_transformation,[],[f46])).
% 2.14/0.67  fof(f128,plain,(
% 2.14/0.67    ~spl8_1 | spl8_5),
% 2.14/0.67    inference(avatar_split_clause,[],[f69,f125,f107])).
% 2.14/0.67  fof(f69,plain,(
% 2.14/0.67    v4_orders_2(sK1) | ~v1_compts_1(sK0)),
% 2.14/0.67    inference(cnf_transformation,[],[f46])).
% 2.14/0.67  fof(f123,plain,(
% 2.14/0.67    ~spl8_1 | spl8_4),
% 2.14/0.67    inference(avatar_split_clause,[],[f70,f120,f107])).
% 2.14/0.67  fof(f70,plain,(
% 2.14/0.67    v7_waybel_0(sK1) | ~v1_compts_1(sK0)),
% 2.14/0.67    inference(cnf_transformation,[],[f46])).
% 2.14/0.67  fof(f118,plain,(
% 2.14/0.67    ~spl8_1 | spl8_3),
% 2.14/0.67    inference(avatar_split_clause,[],[f71,f115,f107])).
% 2.14/0.67  fof(f71,plain,(
% 2.14/0.67    l1_waybel_0(sK1,sK0) | ~v1_compts_1(sK0)),
% 2.14/0.67    inference(cnf_transformation,[],[f46])).
% 2.14/0.67  fof(f113,plain,(
% 2.14/0.67    ~spl8_1 | spl8_2),
% 2.14/0.67    inference(avatar_split_clause,[],[f72,f111,f107])).
% 2.14/0.67  fof(f72,plain,(
% 2.14/0.67    ( ! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,sK1) | ~v1_compts_1(sK0)) )),
% 2.14/0.67    inference(cnf_transformation,[],[f46])).
% 2.14/0.67  % SZS output end Proof for theBenchmark
% 2.14/0.67  % (24290)------------------------------
% 2.14/0.67  % (24290)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.14/0.67  % (24290)Termination reason: Refutation
% 2.14/0.67  
% 2.14/0.67  % (24290)Memory used [KB]: 11001
% 2.14/0.67  % (24290)Time elapsed: 0.231 s
% 2.14/0.67  % (24290)------------------------------
% 2.14/0.67  % (24290)------------------------------
% 2.14/0.68  % (24260)Success in time 0.317 s
%------------------------------------------------------------------------------
