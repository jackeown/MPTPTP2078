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
% DateTime   : Thu Dec  3 13:23:39 EST 2020

% Result     : Theorem 1.97s
% Output     : Refutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :  193 (55368 expanded)
%              Number of leaves         :   35 (18342 expanded)
%              Depth                    :   27
%              Number of atoms          : 1372 (663720 expanded)
%              Number of equality atoms :   31 ( 266 expanded)
%              Maximal formula depth    :   17 (   8 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1289,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f124,f129,f134,f139,f144,f148,f152,f356,f1185,f1187,f1288])).

fof(f1288,plain,
    ( ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | spl10_6 ),
    inference(avatar_contradiction_clause,[],[f1287])).

fof(f1287,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | spl10_6 ),
    inference(subsumption_resolution,[],[f1283,f79])).

fof(f79,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f1283,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3(sK0,sK1))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | spl10_6 ),
    inference(unit_resulting_resolution,[],[f1281,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f1281,plain,
    ( r2_hidden(sK3(sK0,sK1),k1_xboole_0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | spl10_6 ),
    inference(subsumption_resolution,[],[f1280,f69])).

fof(f69,plain,(
    ~ v2_struct_0(sK0) ),
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
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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

fof(f1280,plain,
    ( r2_hidden(sK3(sK0,sK1),k1_xboole_0)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | spl10_6 ),
    inference(subsumption_resolution,[],[f1279,f70])).

fof(f70,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f1279,plain,
    ( r2_hidden(sK3(sK0,sK1),k1_xboole_0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | spl10_6 ),
    inference(subsumption_resolution,[],[f1278,f71])).

fof(f71,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f1278,plain,
    ( r2_hidden(sK3(sK0,sK1),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | spl10_6 ),
    inference(subsumption_resolution,[],[f1277,f1236])).

fof(f1236,plain,
    ( ~ v2_struct_0(sK5(sK0,sK1,sK3(sK0,sK1)))
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | spl10_6 ),
    inference(unit_resulting_resolution,[],[f69,f153,f143,f138,f133,f128,f1214,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(X2)
      | ~ m2_yellow_6(X2,X0,X1)
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f1214,plain,
    ( m2_yellow_6(sK5(sK0,sK1,sK3(sK0,sK1)),sK0,sK1)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | spl10_6 ),
    inference(unit_resulting_resolution,[],[f69,f70,f71,f143,f138,f133,f128,f1203,f1204,f92])).

fof(f92,plain,(
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
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f30,f55])).

fof(f55,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X2,k10_yellow_6(X0,X3))
          & m2_yellow_6(X3,X0,X1) )
     => ( r2_hidden(X2,k10_yellow_6(X0,sK5(X0,X1,X2)))
        & m2_yellow_6(sK5(X0,X1,X2),X0,X1) ) ) ),
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f1204,plain,
    ( r3_waybel_9(sK0,sK1,sK3(sK0,sK1))
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | spl10_6 ),
    inference(unit_resulting_resolution,[],[f69,f70,f71,f119,f143,f138,f133,f128,f82])).

fof(f82,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f119,plain,
    ( v1_compts_1(sK0)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl10_1
  <=> v1_compts_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f1203,plain,
    ( m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | spl10_6 ),
    inference(unit_resulting_resolution,[],[f69,f70,f71,f119,f143,f138,f133,f128,f81])).

fof(f81,plain,(
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

fof(f128,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl10_3
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f133,plain,
    ( v7_waybel_0(sK1)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl10_4
  <=> v7_waybel_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f138,plain,
    ( v4_orders_2(sK1)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl10_5
  <=> v4_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f143,plain,
    ( ~ v2_struct_0(sK1)
    | spl10_6 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl10_6
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f153,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f71,f80])).

fof(f80,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f1277,plain,
    ( r2_hidden(sK3(sK0,sK1),k1_xboole_0)
    | v2_struct_0(sK5(sK0,sK1,sK3(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | spl10_6 ),
    inference(subsumption_resolution,[],[f1276,f1237])).

fof(f1237,plain,
    ( v4_orders_2(sK5(sK0,sK1,sK3(sK0,sK1)))
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | spl10_6 ),
    inference(unit_resulting_resolution,[],[f69,f153,f143,f138,f133,f128,f1214,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1276,plain,
    ( r2_hidden(sK3(sK0,sK1),k1_xboole_0)
    | ~ v4_orders_2(sK5(sK0,sK1,sK3(sK0,sK1)))
    | v2_struct_0(sK5(sK0,sK1,sK3(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | spl10_6 ),
    inference(subsumption_resolution,[],[f1275,f1238])).

fof(f1238,plain,
    ( v7_waybel_0(sK5(sK0,sK1,sK3(sK0,sK1)))
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | spl10_6 ),
    inference(unit_resulting_resolution,[],[f69,f153,f143,f138,f133,f128,f1214,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1275,plain,
    ( r2_hidden(sK3(sK0,sK1),k1_xboole_0)
    | ~ v7_waybel_0(sK5(sK0,sK1,sK3(sK0,sK1)))
    | ~ v4_orders_2(sK5(sK0,sK1,sK3(sK0,sK1)))
    | v2_struct_0(sK5(sK0,sK1,sK3(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | spl10_6 ),
    inference(subsumption_resolution,[],[f1274,f1239])).

fof(f1239,plain,
    ( l1_waybel_0(sK5(sK0,sK1,sK3(sK0,sK1)),sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | spl10_6 ),
    inference(unit_resulting_resolution,[],[f69,f153,f143,f138,f133,f128,f1214,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(X2,X0)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1274,plain,
    ( r2_hidden(sK3(sK0,sK1),k1_xboole_0)
    | ~ l1_waybel_0(sK5(sK0,sK1,sK3(sK0,sK1)),sK0)
    | ~ v7_waybel_0(sK5(sK0,sK1,sK3(sK0,sK1)))
    | ~ v4_orders_2(sK5(sK0,sK1,sK3(sK0,sK1)))
    | v2_struct_0(sK5(sK0,sK1,sK3(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | spl10_6 ),
    inference(subsumption_resolution,[],[f1245,f1235])).

fof(f1235,plain,
    ( ~ v3_yellow_6(sK5(sK0,sK1,sK3(sK0,sK1)),sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | spl10_6 ),
    inference(unit_resulting_resolution,[],[f1214,f123])).

fof(f123,plain,
    ( ! [X2] :
        ( ~ v3_yellow_6(X2,sK0)
        | ~ m2_yellow_6(X2,sK0,sK1) )
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl10_2
  <=> ! [X2] :
        ( ~ v3_yellow_6(X2,sK0)
        | ~ m2_yellow_6(X2,sK0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f1245,plain,
    ( r2_hidden(sK3(sK0,sK1),k1_xboole_0)
    | v3_yellow_6(sK5(sK0,sK1,sK3(sK0,sK1)),sK0)
    | ~ l1_waybel_0(sK5(sK0,sK1,sK3(sK0,sK1)),sK0)
    | ~ v7_waybel_0(sK5(sK0,sK1,sK3(sK0,sK1)))
    | ~ v4_orders_2(sK5(sK0,sK1,sK3(sK0,sK1)))
    | v2_struct_0(sK5(sK0,sK1,sK3(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | spl10_6 ),
    inference(superposition,[],[f1215,f90])).

fof(f90,plain,(
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
         => ( v3_yellow_6(X1,X0)
          <=> k1_xboole_0 != k10_yellow_6(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_yellow_6)).

fof(f1215,plain,
    ( r2_hidden(sK3(sK0,sK1),k10_yellow_6(sK0,sK5(sK0,sK1,sK3(sK0,sK1))))
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | spl10_6 ),
    inference(unit_resulting_resolution,[],[f69,f70,f71,f143,f138,f133,f128,f1203,f1204,f93])).

fof(f93,plain,(
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
    inference(cnf_transformation,[],[f56])).

fof(f1187,plain,
    ( ~ spl10_12
    | spl10_1
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f829,f188,f150,f146,f118,f448])).

fof(f448,plain,
    ( spl10_12
  <=> r2_hidden(sK6(sK0,sK2(sK4(sK0)),k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f146,plain,
    ( spl10_7
  <=> ! [X3] :
        ( v3_yellow_6(sK2(X3),sK0)
        | v2_struct_0(X3)
        | ~ v4_orders_2(X3)
        | ~ v7_waybel_0(X3)
        | ~ l1_waybel_0(X3,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f150,plain,
    ( spl10_8
  <=> ! [X3] :
        ( m2_yellow_6(sK2(X3),sK0,X3)
        | v2_struct_0(X3)
        | ~ v4_orders_2(X3)
        | ~ v7_waybel_0(X3)
        | ~ l1_waybel_0(X3,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f188,plain,
    ( spl10_10
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f829,plain,
    ( ~ r2_hidden(sK6(sK0,sK2(sK4(sK0)),k1_xboole_0),k1_xboole_0)
    | spl10_1
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10 ),
    inference(unit_resulting_resolution,[],[f79,f606,f107])).

fof(f107,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK9(X0,X1),X1)
          & r2_hidden(sK9(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f65,f66])).

fof(f66,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK9(X0,X1),X1)
        & r2_hidden(sK9(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f606,plain,
    ( ~ r2_hidden(sK6(sK0,sK2(sK4(sK0)),k1_xboole_0),k10_yellow_6(sK0,sK2(sK4(sK0))))
    | spl10_1
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10 ),
    inference(unit_resulting_resolution,[],[f69,f70,f71,f166,f167,f168,f169,f361,f549,f91])).

fof(f91,plain,(
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
             => ( r2_hidden(X2,k10_yellow_6(X0,X1))
               => r3_waybel_9(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_waybel_9)).

fof(f549,plain,
    ( ~ r3_waybel_9(sK0,sK2(sK4(sK0)),sK6(sK0,sK2(sK4(sK0)),k1_xboole_0))
    | spl10_1
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10 ),
    inference(unit_resulting_resolution,[],[f69,f70,f71,f154,f155,f156,f157,f159,f361,f441,f94])).

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
              ( m2_yellow_6(X2,X0,X1)
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r3_waybel_9(X0,X2,X3)
                   => r3_waybel_9(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_waybel_9)).

fof(f441,plain,
    ( ~ r3_waybel_9(sK0,sK4(sK0),sK6(sK0,sK2(sK4(sK0)),k1_xboole_0))
    | spl10_1
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10 ),
    inference(unit_resulting_resolution,[],[f69,f70,f71,f120,f361,f88])).

fof(f88,plain,(
    ! [X2,X0] :
      ( v1_compts_1(X0)
      | ~ r3_waybel_9(X0,sK4(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ( ! [X2] :
            ( ~ r3_waybel_9(X0,sK4(X0),X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & r2_hidden(sK4(X0),k6_yellow_6(X0))
        & l1_waybel_0(sK4(X0),X0)
        & v7_waybel_0(sK4(X0))
        & v4_orders_2(sK4(X0))
        & ~ v2_struct_0(sK4(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f52])).

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

fof(f24,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ? [X1] :
          ( ! [X2] :
              ( ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & r2_hidden(X1,k6_yellow_6(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ? [X1] :
          ( ! [X2] :
              ( ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & r2_hidden(X1,k6_yellow_6(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ~ ( ! [X2] :
                    ( m1_subset_1(X2,u1_struct_0(X0))
                   => ~ r3_waybel_9(X0,X1,X2) )
                & r2_hidden(X1,k6_yellow_6(X0)) ) )
       => v1_compts_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_yellow19)).

fof(f120,plain,
    ( ~ v1_compts_1(sK0)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f118])).

fof(f159,plain,
    ( m2_yellow_6(sK2(sK4(sK0)),sK0,sK4(sK0))
    | spl10_1
    | ~ spl10_8 ),
    inference(unit_resulting_resolution,[],[f156,f154,f155,f157,f151])).

fof(f151,plain,
    ( ! [X3] :
        ( ~ v7_waybel_0(X3)
        | v2_struct_0(X3)
        | ~ v4_orders_2(X3)
        | m2_yellow_6(sK2(X3),sK0,X3)
        | ~ l1_waybel_0(X3,sK0) )
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f150])).

fof(f157,plain,
    ( l1_waybel_0(sK4(sK0),sK0)
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f69,f70,f71,f120,f86])).

fof(f86,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | l1_waybel_0(sK4(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f156,plain,
    ( v7_waybel_0(sK4(sK0))
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f69,f70,f71,f120,f85])).

fof(f85,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | v7_waybel_0(sK4(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f155,plain,
    ( v4_orders_2(sK4(sK0))
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f69,f70,f71,f120,f84])).

fof(f84,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | v4_orders_2(sK4(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f154,plain,
    ( ~ v2_struct_0(sK4(sK0))
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f69,f70,f71,f120,f83])).

fof(f83,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ~ v2_struct_0(sK4(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f361,plain,
    ( m1_subset_1(sK6(sK0,sK2(sK4(sK0)),k1_xboole_0),u1_struct_0(sK0))
    | spl10_1
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10 ),
    inference(unit_resulting_resolution,[],[f69,f70,f71,f166,f167,f168,f169,f195,f190,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( k10_yellow_6(X0,X1) = X2
      | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f59,f62,f61,f60])).

fof(f60,plain,(
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

fof(f61,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_waybel_0(X0,X1,X4)
          & m1_connsp_2(X4,X0,sK6(X0,X1,X2)) )
     => ( ~ r1_waybel_0(X0,X1,sK7(X0,X1,X2))
        & m1_connsp_2(sK7(X0,X1,X2),X0,sK6(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X6,X1,X0] :
      ( ? [X7] :
          ( ~ r1_waybel_0(X0,X1,X7)
          & m1_connsp_2(X7,X0,X6) )
     => ( ~ r1_waybel_0(X0,X1,sK8(X0,X1,X6))
        & m1_connsp_2(sK8(X0,X1,X6),X0,X6) ) ) ),
    introduced(choice_axiom,[])).

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
    inference(rectify,[],[f58])).

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
    inference(flattening,[],[f57])).

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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f190,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f188])).

fof(f195,plain,
    ( k1_xboole_0 != k10_yellow_6(sK0,sK2(sK4(sK0)))
    | spl10_1
    | ~ spl10_7
    | ~ spl10_8 ),
    inference(unit_resulting_resolution,[],[f69,f70,f71,f166,f167,f168,f160,f169,f89])).

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
    inference(cnf_transformation,[],[f54])).

fof(f160,plain,
    ( v3_yellow_6(sK2(sK4(sK0)),sK0)
    | spl10_1
    | ~ spl10_7 ),
    inference(unit_resulting_resolution,[],[f156,f154,f155,f157,f147])).

fof(f147,plain,
    ( ! [X3] :
        ( ~ v7_waybel_0(X3)
        | v2_struct_0(X3)
        | ~ v4_orders_2(X3)
        | v3_yellow_6(sK2(X3),sK0)
        | ~ l1_waybel_0(X3,sK0) )
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f146])).

fof(f169,plain,
    ( l1_waybel_0(sK2(sK4(sK0)),sK0)
    | spl10_1
    | ~ spl10_8 ),
    inference(unit_resulting_resolution,[],[f69,f153,f154,f155,f156,f157,f159,f105])).

fof(f168,plain,
    ( v7_waybel_0(sK2(sK4(sK0)))
    | spl10_1
    | ~ spl10_8 ),
    inference(unit_resulting_resolution,[],[f69,f153,f154,f155,f156,f157,f159,f104])).

fof(f167,plain,
    ( v4_orders_2(sK2(sK4(sK0)))
    | spl10_1
    | ~ spl10_8 ),
    inference(unit_resulting_resolution,[],[f69,f153,f154,f155,f156,f157,f159,f103])).

fof(f166,plain,
    ( ~ v2_struct_0(sK2(sK4(sK0)))
    | spl10_1
    | ~ spl10_8 ),
    inference(unit_resulting_resolution,[],[f69,f153,f154,f155,f156,f157,f159,f102])).

fof(f1185,plain,
    ( spl10_1
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_12 ),
    inference(avatar_contradiction_clause,[],[f1184])).

fof(f1184,plain,
    ( $false
    | spl10_1
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_12 ),
    inference(subsumption_resolution,[],[f1180,f827])).

fof(f827,plain,
    ( m1_connsp_2(sK8(sK0,sK2(sK4(sK0)),sK6(sK0,sK2(sK4(sK0)),k1_xboole_0)),sK0,sK6(sK0,sK2(sK4(sK0)),k1_xboole_0))
    | spl10_1
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10 ),
    inference(unit_resulting_resolution,[],[f69,f70,f71,f166,f167,f168,f169,f196,f361,f606,f115])).

fof(f115,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(X6,k10_yellow_6(X0,X1))
      | m1_connsp_2(sK8(X0,X1,X6),X0,X6)
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
    inference(cnf_transformation,[],[f63])).

fof(f196,plain,
    ( m1_subset_1(k10_yellow_6(sK0,sK2(sK4(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl10_1
    | ~ spl10_8 ),
    inference(unit_resulting_resolution,[],[f69,f70,f71,f166,f167,f168,f169,f106])).

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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f1180,plain,
    ( ~ m1_connsp_2(sK8(sK0,sK2(sK4(sK0)),sK6(sK0,sK2(sK4(sK0)),k1_xboole_0)),sK0,sK6(sK0,sK2(sK4(sK0)),k1_xboole_0))
    | spl10_1
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_12 ),
    inference(unit_resulting_resolution,[],[f828,f460])).

fof(f460,plain,
    ( ! [X0] :
        ( r1_waybel_0(sK0,sK2(sK4(sK0)),X0)
        | ~ m1_connsp_2(X0,sK0,sK6(sK0,sK2(sK4(sK0)),k1_xboole_0)) )
    | spl10_1
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_12 ),
    inference(subsumption_resolution,[],[f459,f190])).

fof(f459,plain,
    ( ! [X0] :
        ( r1_waybel_0(sK0,sK2(sK4(sK0)),X0)
        | ~ m1_connsp_2(X0,sK0,sK6(sK0,sK2(sK4(sK0)),k1_xboole_0))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl10_1
    | ~ spl10_7
    | ~ spl10_8
    | spl10_12 ),
    inference(subsumption_resolution,[],[f458,f450])).

fof(f450,plain,
    ( ~ r2_hidden(sK6(sK0,sK2(sK4(sK0)),k1_xboole_0),k1_xboole_0)
    | spl10_12 ),
    inference(avatar_component_clause,[],[f448])).

fof(f458,plain,
    ( ! [X0] :
        ( r1_waybel_0(sK0,sK2(sK4(sK0)),X0)
        | ~ m1_connsp_2(X0,sK0,sK6(sK0,sK2(sK4(sK0)),k1_xboole_0))
        | r2_hidden(sK6(sK0,sK2(sK4(sK0)),k1_xboole_0),k1_xboole_0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl10_1
    | ~ spl10_7
    | ~ spl10_8 ),
    inference(equality_resolution,[],[f263])).

fof(f263,plain,
    ( ! [X2,X1] :
        ( k1_xboole_0 != X1
        | r1_waybel_0(sK0,sK2(sK4(sK0)),X2)
        | ~ m1_connsp_2(X2,sK0,sK6(sK0,sK2(sK4(sK0)),X1))
        | r2_hidden(sK6(sK0,sK2(sK4(sK0)),X1),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl10_1
    | ~ spl10_7
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f262,f69])).

fof(f262,plain,
    ( ! [X2,X1] :
        ( k1_xboole_0 != X1
        | r1_waybel_0(sK0,sK2(sK4(sK0)),X2)
        | ~ m1_connsp_2(X2,sK0,sK6(sK0,sK2(sK4(sK0)),X1))
        | r2_hidden(sK6(sK0,sK2(sK4(sK0)),X1),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0) )
    | spl10_1
    | ~ spl10_7
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f261,f70])).

fof(f261,plain,
    ( ! [X2,X1] :
        ( k1_xboole_0 != X1
        | r1_waybel_0(sK0,sK2(sK4(sK0)),X2)
        | ~ m1_connsp_2(X2,sK0,sK6(sK0,sK2(sK4(sK0)),X1))
        | r2_hidden(sK6(sK0,sK2(sK4(sK0)),X1),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl10_1
    | ~ spl10_7
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f260,f71])).

fof(f260,plain,
    ( ! [X2,X1] :
        ( k1_xboole_0 != X1
        | r1_waybel_0(sK0,sK2(sK4(sK0)),X2)
        | ~ m1_connsp_2(X2,sK0,sK6(sK0,sK2(sK4(sK0)),X1))
        | r2_hidden(sK6(sK0,sK2(sK4(sK0)),X1),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl10_1
    | ~ spl10_7
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f259,f166])).

fof(f259,plain,
    ( ! [X2,X1] :
        ( k1_xboole_0 != X1
        | r1_waybel_0(sK0,sK2(sK4(sK0)),X2)
        | ~ m1_connsp_2(X2,sK0,sK6(sK0,sK2(sK4(sK0)),X1))
        | r2_hidden(sK6(sK0,sK2(sK4(sK0)),X1),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(sK2(sK4(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl10_1
    | ~ spl10_7
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f258,f167])).

fof(f258,plain,
    ( ! [X2,X1] :
        ( k1_xboole_0 != X1
        | r1_waybel_0(sK0,sK2(sK4(sK0)),X2)
        | ~ m1_connsp_2(X2,sK0,sK6(sK0,sK2(sK4(sK0)),X1))
        | r2_hidden(sK6(sK0,sK2(sK4(sK0)),X1),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_orders_2(sK2(sK4(sK0)))
        | v2_struct_0(sK2(sK4(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl10_1
    | ~ spl10_7
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f257,f168])).

fof(f257,plain,
    ( ! [X2,X1] :
        ( k1_xboole_0 != X1
        | r1_waybel_0(sK0,sK2(sK4(sK0)),X2)
        | ~ m1_connsp_2(X2,sK0,sK6(sK0,sK2(sK4(sK0)),X1))
        | r2_hidden(sK6(sK0,sK2(sK4(sK0)),X1),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v7_waybel_0(sK2(sK4(sK0)))
        | ~ v4_orders_2(sK2(sK4(sK0)))
        | v2_struct_0(sK2(sK4(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl10_1
    | ~ spl10_7
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f245,f169])).

fof(f245,plain,
    ( ! [X2,X1] :
        ( k1_xboole_0 != X1
        | r1_waybel_0(sK0,sK2(sK4(sK0)),X2)
        | ~ m1_connsp_2(X2,sK0,sK6(sK0,sK2(sK4(sK0)),X1))
        | r2_hidden(sK6(sK0,sK2(sK4(sK0)),X1),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_waybel_0(sK2(sK4(sK0)),sK0)
        | ~ v7_waybel_0(sK2(sK4(sK0)))
        | ~ v4_orders_2(sK2(sK4(sK0)))
        | v2_struct_0(sK2(sK4(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl10_1
    | ~ spl10_7
    | ~ spl10_8 ),
    inference(superposition,[],[f195,f99])).

fof(f99,plain,(
    ! [X2,X0,X5,X1] :
      ( k10_yellow_6(X0,X1) = X2
      | r1_waybel_0(X0,X1,X5)
      | ~ m1_connsp_2(X5,X0,sK6(X0,X1,X2))
      | r2_hidden(sK6(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f828,plain,
    ( ~ r1_waybel_0(sK0,sK2(sK4(sK0)),sK8(sK0,sK2(sK4(sK0)),sK6(sK0,sK2(sK4(sK0)),k1_xboole_0)))
    | spl10_1
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10 ),
    inference(unit_resulting_resolution,[],[f69,f70,f71,f166,f167,f168,f169,f196,f361,f606,f114])).

fof(f114,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(X6,k10_yellow_6(X0,X1))
      | ~ r1_waybel_0(X0,X1,sK8(X0,X1,X6))
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
    inference(cnf_transformation,[],[f63])).

fof(f356,plain,(
    spl10_10 ),
    inference(avatar_contradiction_clause,[],[f355])).

fof(f355,plain,
    ( $false
    | spl10_10 ),
    inference(subsumption_resolution,[],[f352,f79])).

fof(f352,plain,
    ( ~ r1_tarski(k1_xboole_0,u1_struct_0(sK0))
    | spl10_10 ),
    inference(unit_resulting_resolution,[],[f189,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f189,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl10_10 ),
    inference(avatar_component_clause,[],[f188])).

fof(f152,plain,
    ( spl10_1
    | spl10_8 ),
    inference(avatar_split_clause,[],[f72,f150,f118])).

fof(f72,plain,(
    ! [X3] :
      ( m2_yellow_6(sK2(X3),sK0,X3)
      | ~ l1_waybel_0(X3,sK0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f148,plain,
    ( spl10_1
    | spl10_7 ),
    inference(avatar_split_clause,[],[f73,f146,f118])).

fof(f73,plain,(
    ! [X3] :
      ( v3_yellow_6(sK2(X3),sK0)
      | ~ l1_waybel_0(X3,sK0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f144,plain,
    ( ~ spl10_1
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f74,f141,f118])).

fof(f74,plain,
    ( ~ v2_struct_0(sK1)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f139,plain,
    ( ~ spl10_1
    | spl10_5 ),
    inference(avatar_split_clause,[],[f75,f136,f118])).

fof(f75,plain,
    ( v4_orders_2(sK1)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f134,plain,
    ( ~ spl10_1
    | spl10_4 ),
    inference(avatar_split_clause,[],[f76,f131,f118])).

fof(f76,plain,
    ( v7_waybel_0(sK1)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f129,plain,
    ( ~ spl10_1
    | spl10_3 ),
    inference(avatar_split_clause,[],[f77,f126,f118])).

fof(f77,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f124,plain,
    ( ~ spl10_1
    | spl10_2 ),
    inference(avatar_split_clause,[],[f78,f122,f118])).

fof(f78,plain,(
    ! [X2] :
      ( ~ v3_yellow_6(X2,sK0)
      | ~ m2_yellow_6(X2,sK0,sK1)
      | ~ v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:47:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (32568)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.51  % (32591)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.21/0.51  % (32585)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.21/0.51  % (32577)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.21/0.51  % (32567)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.21/0.51  % (32566)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.21/0.51  % (32576)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.21/0.52  % (32569)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.21/0.52  % (32565)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.21/0.52  % (32571)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.21/0.52  % (32575)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.21/0.53  % (32585)Refutation not found, incomplete strategy% (32585)------------------------------
% 1.21/0.53  % (32585)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.53  % (32583)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.21/0.53  % (32570)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.21/0.53  % (32585)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.53  
% 1.21/0.53  % (32585)Memory used [KB]: 11001
% 1.21/0.53  % (32585)Time elapsed: 0.064 s
% 1.21/0.53  % (32585)------------------------------
% 1.21/0.53  % (32585)------------------------------
% 1.21/0.53  % (32581)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.32/0.53  % (32564)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.32/0.53  % (32574)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.32/0.53  % (32573)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.32/0.54  % (32567)Refutation not found, incomplete strategy% (32567)------------------------------
% 1.32/0.54  % (32567)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (32567)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.54  
% 1.32/0.54  % (32567)Memory used [KB]: 6268
% 1.32/0.54  % (32567)Time elapsed: 0.108 s
% 1.32/0.54  % (32567)------------------------------
% 1.32/0.54  % (32567)------------------------------
% 1.32/0.54  % (32584)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.32/0.54  % (32588)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.32/0.54  % (32590)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.32/0.54  % (32592)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.32/0.54  % (32563)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.32/0.54  % (32579)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.32/0.54  % (32589)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.32/0.55  % (32578)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.32/0.55  % (32580)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.32/0.55  % (32574)Refutation not found, incomplete strategy% (32574)------------------------------
% 1.32/0.55  % (32574)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  % (32574)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.55  
% 1.32/0.55  % (32574)Memory used [KB]: 10746
% 1.32/0.55  % (32574)Time elapsed: 0.153 s
% 1.32/0.55  % (32574)------------------------------
% 1.32/0.55  % (32574)------------------------------
% 1.32/0.55  % (32582)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.32/0.55  % (32580)Refutation not found, incomplete strategy% (32580)------------------------------
% 1.32/0.55  % (32580)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  % (32580)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.55  
% 1.32/0.55  % (32580)Memory used [KB]: 10746
% 1.32/0.55  % (32580)Time elapsed: 0.150 s
% 1.32/0.55  % (32580)------------------------------
% 1.32/0.55  % (32580)------------------------------
% 1.32/0.55  % (32586)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.32/0.55  % (32572)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.32/0.56  % (32572)Refutation not found, incomplete strategy% (32572)------------------------------
% 1.32/0.56  % (32572)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.56  % (32572)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.56  
% 1.32/0.56  % (32572)Memory used [KB]: 10746
% 1.32/0.56  % (32572)Time elapsed: 0.152 s
% 1.32/0.56  % (32572)------------------------------
% 1.32/0.56  % (32572)------------------------------
% 1.32/0.56  % (32573)Refutation not found, incomplete strategy% (32573)------------------------------
% 1.32/0.56  % (32573)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.56  % (32573)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.56  
% 1.32/0.56  % (32573)Memory used [KB]: 10746
% 1.32/0.56  % (32573)Time elapsed: 0.152 s
% 1.32/0.56  % (32573)------------------------------
% 1.32/0.56  % (32573)------------------------------
% 1.32/0.56  % (32587)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.97/0.65  % (32603)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.97/0.65  % (32589)Refutation found. Thanks to Tanya!
% 1.97/0.65  % SZS status Theorem for theBenchmark
% 1.97/0.65  % SZS output start Proof for theBenchmark
% 1.97/0.65  fof(f1289,plain,(
% 1.97/0.65    $false),
% 1.97/0.65    inference(avatar_sat_refutation,[],[f124,f129,f134,f139,f144,f148,f152,f356,f1185,f1187,f1288])).
% 1.97/0.65  fof(f1288,plain,(
% 1.97/0.65    ~spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_5 | spl10_6),
% 1.97/0.65    inference(avatar_contradiction_clause,[],[f1287])).
% 1.97/0.65  fof(f1287,plain,(
% 1.97/0.65    $false | (~spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_5 | spl10_6)),
% 1.97/0.65    inference(subsumption_resolution,[],[f1283,f79])).
% 1.97/0.65  fof(f79,plain,(
% 1.97/0.65    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.97/0.65    inference(cnf_transformation,[],[f2])).
% 1.97/0.65  fof(f2,axiom,(
% 1.97/0.65    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.97/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.97/0.65  fof(f1283,plain,(
% 1.97/0.65    ~r1_tarski(k1_xboole_0,sK3(sK0,sK1)) | (~spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_5 | spl10_6)),
% 1.97/0.65    inference(unit_resulting_resolution,[],[f1281,f112])).
% 1.97/0.65  fof(f112,plain,(
% 1.97/0.65    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.97/0.65    inference(cnf_transformation,[],[f40])).
% 1.97/0.65  fof(f40,plain,(
% 1.97/0.65    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.97/0.65    inference(ennf_transformation,[],[f5])).
% 1.97/0.65  fof(f5,axiom,(
% 1.97/0.65    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.97/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.97/0.65  fof(f1281,plain,(
% 1.97/0.65    r2_hidden(sK3(sK0,sK1),k1_xboole_0) | (~spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_5 | spl10_6)),
% 1.97/0.65    inference(subsumption_resolution,[],[f1280,f69])).
% 1.97/0.65  fof(f69,plain,(
% 1.97/0.65    ~v2_struct_0(sK0)),
% 1.97/0.65    inference(cnf_transformation,[],[f49])).
% 1.97/0.65  fof(f49,plain,(
% 1.97/0.65    ((! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,sK1)) & l1_waybel_0(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1)) | ~v1_compts_1(sK0)) & (! [X3] : ((v3_yellow_6(sK2(X3),sK0) & m2_yellow_6(sK2(X3),sK0,X3)) | ~l1_waybel_0(X3,sK0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.97/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f45,f48,f47,f46])).
% 1.97/0.65  fof(f46,plain,(
% 1.97/0.65    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ((? [X1] : (! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,X1)) & l1_waybel_0(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(sK0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,sK0) & m2_yellow_6(X4,sK0,X3)) | ~l1_waybel_0(X3,sK0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.97/0.65    introduced(choice_axiom,[])).
% 1.97/0.65  fof(f47,plain,(
% 1.97/0.65    ? [X1] : (! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,X1)) & l1_waybel_0(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,sK1)) & l1_waybel_0(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1))),
% 1.97/0.65    introduced(choice_axiom,[])).
% 1.97/0.65  fof(f48,plain,(
% 1.97/0.65    ! [X3] : (? [X4] : (v3_yellow_6(X4,sK0) & m2_yellow_6(X4,sK0,X3)) => (v3_yellow_6(sK2(X3),sK0) & m2_yellow_6(sK2(X3),sK0,X3)))),
% 1.97/0.65    introduced(choice_axiom,[])).
% 1.97/0.65  fof(f45,plain,(
% 1.97/0.65    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.97/0.65    inference(rectify,[],[f44])).
% 1.97/0.65  fof(f44,plain,(
% 1.97/0.65    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.97/0.65    inference(flattening,[],[f43])).
% 1.97/0.65  fof(f43,plain,(
% 1.97/0.65    ? [X0] : (((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | v1_compts_1(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.97/0.65    inference(nnf_transformation,[],[f19])).
% 1.97/0.65  fof(f19,plain,(
% 1.97/0.65    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.97/0.65    inference(flattening,[],[f18])).
% 1.97/0.65  fof(f18,plain,(
% 1.97/0.65    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.97/0.65    inference(ennf_transformation,[],[f17])).
% 1.97/0.65  fof(f17,negated_conjecture,(
% 1.97/0.65    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)))))),
% 1.97/0.65    inference(negated_conjecture,[],[f16])).
% 1.97/0.65  fof(f16,conjecture,(
% 1.97/0.65    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)))))),
% 1.97/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_yellow19)).
% 1.97/0.65  fof(f1280,plain,(
% 1.97/0.65    r2_hidden(sK3(sK0,sK1),k1_xboole_0) | v2_struct_0(sK0) | (~spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_5 | spl10_6)),
% 1.97/0.65    inference(subsumption_resolution,[],[f1279,f70])).
% 1.97/0.65  fof(f70,plain,(
% 1.97/0.65    v2_pre_topc(sK0)),
% 1.97/0.65    inference(cnf_transformation,[],[f49])).
% 1.97/0.65  fof(f1279,plain,(
% 1.97/0.65    r2_hidden(sK3(sK0,sK1),k1_xboole_0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_5 | spl10_6)),
% 1.97/0.65    inference(subsumption_resolution,[],[f1278,f71])).
% 1.97/0.65  fof(f71,plain,(
% 1.97/0.65    l1_pre_topc(sK0)),
% 1.97/0.65    inference(cnf_transformation,[],[f49])).
% 1.97/0.65  fof(f1278,plain,(
% 1.97/0.65    r2_hidden(sK3(sK0,sK1),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_5 | spl10_6)),
% 1.97/0.65    inference(subsumption_resolution,[],[f1277,f1236])).
% 1.97/0.65  fof(f1236,plain,(
% 1.97/0.65    ~v2_struct_0(sK5(sK0,sK1,sK3(sK0,sK1))) | (~spl10_1 | ~spl10_3 | ~spl10_4 | ~spl10_5 | spl10_6)),
% 1.97/0.65    inference(unit_resulting_resolution,[],[f69,f153,f143,f138,f133,f128,f1214,f102])).
% 1.97/0.65  fof(f102,plain,(
% 1.97/0.65    ( ! [X2,X0,X1] : (~v2_struct_0(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.97/0.65    inference(cnf_transformation,[],[f36])).
% 1.97/0.65  fof(f36,plain,(
% 1.97/0.65    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.97/0.65    inference(flattening,[],[f35])).
% 1.97/0.65  fof(f35,plain,(
% 1.97/0.65    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.97/0.65    inference(ennf_transformation,[],[f9])).
% 1.97/0.65  fof(f9,axiom,(
% 1.97/0.65    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))))),
% 1.97/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_yellow_6)).
% 1.97/0.65  fof(f1214,plain,(
% 1.97/0.65    m2_yellow_6(sK5(sK0,sK1,sK3(sK0,sK1)),sK0,sK1) | (~spl10_1 | ~spl10_3 | ~spl10_4 | ~spl10_5 | spl10_6)),
% 1.97/0.65    inference(unit_resulting_resolution,[],[f69,f70,f71,f143,f138,f133,f128,f1203,f1204,f92])).
% 1.97/0.65  fof(f92,plain,(
% 1.97/0.65    ( ! [X2,X0,X1] : (m2_yellow_6(sK5(X0,X1,X2),X0,X1) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.97/0.65    inference(cnf_transformation,[],[f56])).
% 1.97/0.65  fof(f56,plain,(
% 1.97/0.65    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k10_yellow_6(X0,sK5(X0,X1,X2))) & m2_yellow_6(sK5(X0,X1,X2),X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.97/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f30,f55])).
% 1.97/0.65  fof(f55,plain,(
% 1.97/0.65    ! [X2,X1,X0] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) => (r2_hidden(X2,k10_yellow_6(X0,sK5(X0,X1,X2))) & m2_yellow_6(sK5(X0,X1,X2),X0,X1)))),
% 1.97/0.65    introduced(choice_axiom,[])).
% 1.97/0.65  fof(f30,plain,(
% 1.97/0.65    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.97/0.65    inference(flattening,[],[f29])).
% 1.97/0.65  fof(f29,plain,(
% 1.97/0.65    ! [X0] : (! [X1] : (! [X2] : ((? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.97/0.65    inference(ennf_transformation,[],[f13])).
% 1.97/0.65  fof(f13,axiom,(
% 1.97/0.65    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m2_yellow_6(X3,X0,X1) => ~r2_hidden(X2,k10_yellow_6(X0,X3))) & r3_waybel_9(X0,X1,X2)))))),
% 1.97/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_waybel_9)).
% 1.97/0.65  fof(f1204,plain,(
% 1.97/0.65    r3_waybel_9(sK0,sK1,sK3(sK0,sK1)) | (~spl10_1 | ~spl10_3 | ~spl10_4 | ~spl10_5 | spl10_6)),
% 1.97/0.65    inference(unit_resulting_resolution,[],[f69,f70,f71,f119,f143,f138,f133,f128,f82])).
% 1.97/0.65  fof(f82,plain,(
% 1.97/0.65    ( ! [X0,X1] : (r3_waybel_9(X0,X1,sK3(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.97/0.65    inference(cnf_transformation,[],[f51])).
% 1.97/0.65  fof(f51,plain,(
% 1.97/0.65    ! [X0] : (! [X1] : ((r3_waybel_9(X0,X1,sK3(X0,X1)) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.97/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f50])).
% 1.97/0.65  fof(f50,plain,(
% 1.97/0.65    ! [X1,X0] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) => (r3_waybel_9(X0,X1,sK3(X0,X1)) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))))),
% 1.97/0.65    introduced(choice_axiom,[])).
% 1.97/0.65  fof(f22,plain,(
% 1.97/0.65    ! [X0] : (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.97/0.65    inference(flattening,[],[f21])).
% 1.97/0.65  fof(f21,plain,(
% 1.97/0.65    ! [X0] : ((! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | ~v1_compts_1(X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.97/0.65    inference(ennf_transformation,[],[f14])).
% 1.97/0.65  fof(f14,axiom,(
% 1.97/0.65    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))))))),
% 1.97/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l37_yellow19)).
% 1.97/0.65  fof(f119,plain,(
% 1.97/0.65    v1_compts_1(sK0) | ~spl10_1),
% 1.97/0.65    inference(avatar_component_clause,[],[f118])).
% 1.97/0.65  fof(f118,plain,(
% 1.97/0.65    spl10_1 <=> v1_compts_1(sK0)),
% 1.97/0.65    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 1.97/0.65  fof(f1203,plain,(
% 1.97/0.65    m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) | (~spl10_1 | ~spl10_3 | ~spl10_4 | ~spl10_5 | spl10_6)),
% 1.97/0.65    inference(unit_resulting_resolution,[],[f69,f70,f71,f119,f143,f138,f133,f128,f81])).
% 1.97/0.65  fof(f81,plain,(
% 1.97/0.65    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.97/0.65    inference(cnf_transformation,[],[f51])).
% 1.97/0.65  fof(f128,plain,(
% 1.97/0.65    l1_waybel_0(sK1,sK0) | ~spl10_3),
% 1.97/0.65    inference(avatar_component_clause,[],[f126])).
% 1.97/0.65  fof(f126,plain,(
% 1.97/0.65    spl10_3 <=> l1_waybel_0(sK1,sK0)),
% 1.97/0.65    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 1.97/0.65  fof(f133,plain,(
% 1.97/0.65    v7_waybel_0(sK1) | ~spl10_4),
% 1.97/0.65    inference(avatar_component_clause,[],[f131])).
% 1.97/0.65  fof(f131,plain,(
% 1.97/0.65    spl10_4 <=> v7_waybel_0(sK1)),
% 1.97/0.65    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 1.97/0.65  fof(f138,plain,(
% 1.97/0.65    v4_orders_2(sK1) | ~spl10_5),
% 1.97/0.65    inference(avatar_component_clause,[],[f136])).
% 1.97/0.65  fof(f136,plain,(
% 1.97/0.65    spl10_5 <=> v4_orders_2(sK1)),
% 1.97/0.65    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 1.97/0.65  fof(f143,plain,(
% 1.97/0.65    ~v2_struct_0(sK1) | spl10_6),
% 1.97/0.65    inference(avatar_component_clause,[],[f141])).
% 1.97/0.65  fof(f141,plain,(
% 1.97/0.65    spl10_6 <=> v2_struct_0(sK1)),
% 1.97/0.65    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 1.97/0.65  fof(f153,plain,(
% 1.97/0.65    l1_struct_0(sK0)),
% 1.97/0.65    inference(unit_resulting_resolution,[],[f71,f80])).
% 1.97/0.65  fof(f80,plain,(
% 1.97/0.65    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.97/0.65    inference(cnf_transformation,[],[f20])).
% 1.97/0.65  fof(f20,plain,(
% 1.97/0.65    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.97/0.65    inference(ennf_transformation,[],[f6])).
% 1.97/0.65  fof(f6,axiom,(
% 1.97/0.65    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.97/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.97/0.65  fof(f1277,plain,(
% 1.97/0.65    r2_hidden(sK3(sK0,sK1),k1_xboole_0) | v2_struct_0(sK5(sK0,sK1,sK3(sK0,sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_5 | spl10_6)),
% 1.97/0.65    inference(subsumption_resolution,[],[f1276,f1237])).
% 1.97/0.65  fof(f1237,plain,(
% 1.97/0.65    v4_orders_2(sK5(sK0,sK1,sK3(sK0,sK1))) | (~spl10_1 | ~spl10_3 | ~spl10_4 | ~spl10_5 | spl10_6)),
% 1.97/0.65    inference(unit_resulting_resolution,[],[f69,f153,f143,f138,f133,f128,f1214,f103])).
% 1.97/0.65  fof(f103,plain,(
% 1.97/0.65    ( ! [X2,X0,X1] : (v4_orders_2(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.97/0.65    inference(cnf_transformation,[],[f36])).
% 1.97/0.65  fof(f1276,plain,(
% 1.97/0.65    r2_hidden(sK3(sK0,sK1),k1_xboole_0) | ~v4_orders_2(sK5(sK0,sK1,sK3(sK0,sK1))) | v2_struct_0(sK5(sK0,sK1,sK3(sK0,sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_5 | spl10_6)),
% 1.97/0.65    inference(subsumption_resolution,[],[f1275,f1238])).
% 1.97/0.65  fof(f1238,plain,(
% 1.97/0.65    v7_waybel_0(sK5(sK0,sK1,sK3(sK0,sK1))) | (~spl10_1 | ~spl10_3 | ~spl10_4 | ~spl10_5 | spl10_6)),
% 1.97/0.65    inference(unit_resulting_resolution,[],[f69,f153,f143,f138,f133,f128,f1214,f104])).
% 1.97/0.65  fof(f104,plain,(
% 1.97/0.65    ( ! [X2,X0,X1] : (v7_waybel_0(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.97/0.65    inference(cnf_transformation,[],[f36])).
% 1.97/0.65  fof(f1275,plain,(
% 1.97/0.65    r2_hidden(sK3(sK0,sK1),k1_xboole_0) | ~v7_waybel_0(sK5(sK0,sK1,sK3(sK0,sK1))) | ~v4_orders_2(sK5(sK0,sK1,sK3(sK0,sK1))) | v2_struct_0(sK5(sK0,sK1,sK3(sK0,sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_5 | spl10_6)),
% 1.97/0.65    inference(subsumption_resolution,[],[f1274,f1239])).
% 1.97/0.65  fof(f1239,plain,(
% 1.97/0.65    l1_waybel_0(sK5(sK0,sK1,sK3(sK0,sK1)),sK0) | (~spl10_1 | ~spl10_3 | ~spl10_4 | ~spl10_5 | spl10_6)),
% 1.97/0.65    inference(unit_resulting_resolution,[],[f69,f153,f143,f138,f133,f128,f1214,f105])).
% 1.97/0.65  fof(f105,plain,(
% 1.97/0.65    ( ! [X2,X0,X1] : (l1_waybel_0(X2,X0) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.97/0.65    inference(cnf_transformation,[],[f36])).
% 1.97/0.65  fof(f1274,plain,(
% 1.97/0.65    r2_hidden(sK3(sK0,sK1),k1_xboole_0) | ~l1_waybel_0(sK5(sK0,sK1,sK3(sK0,sK1)),sK0) | ~v7_waybel_0(sK5(sK0,sK1,sK3(sK0,sK1))) | ~v4_orders_2(sK5(sK0,sK1,sK3(sK0,sK1))) | v2_struct_0(sK5(sK0,sK1,sK3(sK0,sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_5 | spl10_6)),
% 1.97/0.65    inference(subsumption_resolution,[],[f1245,f1235])).
% 1.97/0.65  fof(f1235,plain,(
% 1.97/0.65    ~v3_yellow_6(sK5(sK0,sK1,sK3(sK0,sK1)),sK0) | (~spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_5 | spl10_6)),
% 1.97/0.65    inference(unit_resulting_resolution,[],[f1214,f123])).
% 1.97/0.65  fof(f123,plain,(
% 1.97/0.65    ( ! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,sK1)) ) | ~spl10_2),
% 1.97/0.65    inference(avatar_component_clause,[],[f122])).
% 1.97/0.65  fof(f122,plain,(
% 1.97/0.65    spl10_2 <=> ! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,sK1))),
% 1.97/0.65    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 1.97/0.65  fof(f1245,plain,(
% 1.97/0.65    r2_hidden(sK3(sK0,sK1),k1_xboole_0) | v3_yellow_6(sK5(sK0,sK1,sK3(sK0,sK1)),sK0) | ~l1_waybel_0(sK5(sK0,sK1,sK3(sK0,sK1)),sK0) | ~v7_waybel_0(sK5(sK0,sK1,sK3(sK0,sK1))) | ~v4_orders_2(sK5(sK0,sK1,sK3(sK0,sK1))) | v2_struct_0(sK5(sK0,sK1,sK3(sK0,sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl10_1 | ~spl10_3 | ~spl10_4 | ~spl10_5 | spl10_6)),
% 1.97/0.65    inference(superposition,[],[f1215,f90])).
% 1.97/0.65  fof(f90,plain,(
% 1.97/0.65    ( ! [X0,X1] : (v3_yellow_6(X1,X0) | k1_xboole_0 = k10_yellow_6(X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.97/0.65    inference(cnf_transformation,[],[f54])).
% 1.97/0.65  fof(f54,plain,(
% 1.97/0.65    ! [X0] : (! [X1] : (((v3_yellow_6(X1,X0) | k1_xboole_0 = k10_yellow_6(X0,X1)) & (k1_xboole_0 != k10_yellow_6(X0,X1) | ~v3_yellow_6(X1,X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.97/0.65    inference(nnf_transformation,[],[f26])).
% 1.97/0.65  fof(f26,plain,(
% 1.97/0.65    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.97/0.65    inference(flattening,[],[f25])).
% 1.97/0.65  fof(f25,plain,(
% 1.97/0.65    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.97/0.65    inference(ennf_transformation,[],[f10])).
% 1.97/0.65  fof(f10,axiom,(
% 1.97/0.65    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1))))),
% 1.97/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_yellow_6)).
% 1.97/0.65  fof(f1215,plain,(
% 1.97/0.65    r2_hidden(sK3(sK0,sK1),k10_yellow_6(sK0,sK5(sK0,sK1,sK3(sK0,sK1)))) | (~spl10_1 | ~spl10_3 | ~spl10_4 | ~spl10_5 | spl10_6)),
% 1.97/0.65    inference(unit_resulting_resolution,[],[f69,f70,f71,f143,f138,f133,f128,f1203,f1204,f93])).
% 1.97/0.65  fof(f93,plain,(
% 1.97/0.65    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,sK5(X0,X1,X2))) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.97/0.65    inference(cnf_transformation,[],[f56])).
% 1.97/0.65  fof(f1187,plain,(
% 1.97/0.65    ~spl10_12 | spl10_1 | ~spl10_7 | ~spl10_8 | ~spl10_10),
% 1.97/0.65    inference(avatar_split_clause,[],[f829,f188,f150,f146,f118,f448])).
% 1.97/0.65  fof(f448,plain,(
% 1.97/0.65    spl10_12 <=> r2_hidden(sK6(sK0,sK2(sK4(sK0)),k1_xboole_0),k1_xboole_0)),
% 1.97/0.65    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 1.97/0.65  fof(f146,plain,(
% 1.97/0.65    spl10_7 <=> ! [X3] : (v3_yellow_6(sK2(X3),sK0) | v2_struct_0(X3) | ~v4_orders_2(X3) | ~v7_waybel_0(X3) | ~l1_waybel_0(X3,sK0))),
% 1.97/0.65    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 1.97/0.65  fof(f150,plain,(
% 1.97/0.65    spl10_8 <=> ! [X3] : (m2_yellow_6(sK2(X3),sK0,X3) | v2_struct_0(X3) | ~v4_orders_2(X3) | ~v7_waybel_0(X3) | ~l1_waybel_0(X3,sK0))),
% 1.97/0.65    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 1.97/0.65  fof(f188,plain,(
% 1.97/0.65    spl10_10 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.97/0.65    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 1.97/0.65  fof(f829,plain,(
% 1.97/0.65    ~r2_hidden(sK6(sK0,sK2(sK4(sK0)),k1_xboole_0),k1_xboole_0) | (spl10_1 | ~spl10_7 | ~spl10_8 | ~spl10_10)),
% 1.97/0.65    inference(unit_resulting_resolution,[],[f79,f606,f107])).
% 1.97/0.65  fof(f107,plain,(
% 1.97/0.65    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.97/0.65    inference(cnf_transformation,[],[f67])).
% 1.97/0.65  fof(f67,plain,(
% 1.97/0.65    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.97/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f65,f66])).
% 1.97/0.65  fof(f66,plain,(
% 1.97/0.65    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0)))),
% 1.97/0.65    introduced(choice_axiom,[])).
% 1.97/0.65  fof(f65,plain,(
% 1.97/0.65    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.97/0.65    inference(rectify,[],[f64])).
% 1.97/0.65  fof(f64,plain,(
% 1.97/0.65    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.97/0.65    inference(nnf_transformation,[],[f39])).
% 1.97/0.65  fof(f39,plain,(
% 1.97/0.65    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.97/0.65    inference(ennf_transformation,[],[f1])).
% 1.97/0.65  fof(f1,axiom,(
% 1.97/0.65    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.97/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.97/0.65  fof(f606,plain,(
% 1.97/0.65    ~r2_hidden(sK6(sK0,sK2(sK4(sK0)),k1_xboole_0),k10_yellow_6(sK0,sK2(sK4(sK0)))) | (spl10_1 | ~spl10_7 | ~spl10_8 | ~spl10_10)),
% 1.97/0.65    inference(unit_resulting_resolution,[],[f69,f70,f71,f166,f167,f168,f169,f361,f549,f91])).
% 1.97/0.65  fof(f91,plain,(
% 1.97/0.65    ( ! [X2,X0,X1] : (r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.97/0.65    inference(cnf_transformation,[],[f28])).
% 1.97/0.65  fof(f28,plain,(
% 1.97/0.65    ! [X0] : (! [X1] : (! [X2] : (r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.97/0.65    inference(flattening,[],[f27])).
% 1.97/0.65  fof(f27,plain,(
% 1.97/0.65    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.97/0.65    inference(ennf_transformation,[],[f11])).
% 1.97/0.65  fof(f11,axiom,(
% 1.97/0.65    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,X1)) => r3_waybel_9(X0,X1,X2)))))),
% 1.97/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_waybel_9)).
% 1.97/0.65  fof(f549,plain,(
% 1.97/0.65    ~r3_waybel_9(sK0,sK2(sK4(sK0)),sK6(sK0,sK2(sK4(sK0)),k1_xboole_0)) | (spl10_1 | ~spl10_7 | ~spl10_8 | ~spl10_10)),
% 1.97/0.65    inference(unit_resulting_resolution,[],[f69,f70,f71,f154,f155,f156,f157,f159,f361,f441,f94])).
% 1.97/0.65  fof(f94,plain,(
% 1.97/0.65    ( ! [X2,X0,X3,X1] : (r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.97/0.65    inference(cnf_transformation,[],[f32])).
% 1.97/0.65  fof(f32,plain,(
% 1.97/0.65    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.97/0.65    inference(flattening,[],[f31])).
% 1.97/0.65  fof(f31,plain,(
% 1.97/0.65    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.97/0.65    inference(ennf_transformation,[],[f12])).
% 1.97/0.65  fof(f12,axiom,(
% 1.97/0.65    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_waybel_9(X0,X2,X3) => r3_waybel_9(X0,X1,X3))))))),
% 1.97/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_waybel_9)).
% 1.97/0.65  fof(f441,plain,(
% 1.97/0.65    ~r3_waybel_9(sK0,sK4(sK0),sK6(sK0,sK2(sK4(sK0)),k1_xboole_0)) | (spl10_1 | ~spl10_7 | ~spl10_8 | ~spl10_10)),
% 1.97/0.65    inference(unit_resulting_resolution,[],[f69,f70,f71,f120,f361,f88])).
% 1.97/0.65  fof(f88,plain,(
% 1.97/0.65    ( ! [X2,X0] : (v1_compts_1(X0) | ~r3_waybel_9(X0,sK4(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.97/0.65    inference(cnf_transformation,[],[f53])).
% 1.97/0.65  fof(f53,plain,(
% 1.97/0.65    ! [X0] : (v1_compts_1(X0) | (! [X2] : (~r3_waybel_9(X0,sK4(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(sK4(X0),k6_yellow_6(X0)) & l1_waybel_0(sK4(X0),X0) & v7_waybel_0(sK4(X0)) & v4_orders_2(sK4(X0)) & ~v2_struct_0(sK4(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.97/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f52])).
% 1.97/0.65  fof(f52,plain,(
% 1.97/0.65    ! [X0] : (? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(X1,k6_yellow_6(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (~r3_waybel_9(X0,sK4(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(sK4(X0),k6_yellow_6(X0)) & l1_waybel_0(sK4(X0),X0) & v7_waybel_0(sK4(X0)) & v4_orders_2(sK4(X0)) & ~v2_struct_0(sK4(X0))))),
% 1.97/0.65    introduced(choice_axiom,[])).
% 1.97/0.65  fof(f24,plain,(
% 1.97/0.65    ! [X0] : (v1_compts_1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(X1,k6_yellow_6(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.97/0.65    inference(flattening,[],[f23])).
% 1.97/0.65  fof(f23,plain,(
% 1.97/0.65    ! [X0] : ((v1_compts_1(X0) | ? [X1] : ((! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(X1,k6_yellow_6(X0))) & (l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.97/0.65    inference(ennf_transformation,[],[f15])).
% 1.97/0.65  fof(f15,axiom,(
% 1.97/0.65    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ~(! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~r3_waybel_9(X0,X1,X2)) & r2_hidden(X1,k6_yellow_6(X0)))) => v1_compts_1(X0)))),
% 1.97/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_yellow19)).
% 1.97/0.65  fof(f120,plain,(
% 1.97/0.65    ~v1_compts_1(sK0) | spl10_1),
% 1.97/0.65    inference(avatar_component_clause,[],[f118])).
% 1.97/0.65  fof(f159,plain,(
% 1.97/0.65    m2_yellow_6(sK2(sK4(sK0)),sK0,sK4(sK0)) | (spl10_1 | ~spl10_8)),
% 1.97/0.65    inference(unit_resulting_resolution,[],[f156,f154,f155,f157,f151])).
% 1.97/0.65  fof(f151,plain,(
% 1.97/0.65    ( ! [X3] : (~v7_waybel_0(X3) | v2_struct_0(X3) | ~v4_orders_2(X3) | m2_yellow_6(sK2(X3),sK0,X3) | ~l1_waybel_0(X3,sK0)) ) | ~spl10_8),
% 1.97/0.65    inference(avatar_component_clause,[],[f150])).
% 1.97/0.65  fof(f157,plain,(
% 1.97/0.65    l1_waybel_0(sK4(sK0),sK0) | spl10_1),
% 1.97/0.65    inference(unit_resulting_resolution,[],[f69,f70,f71,f120,f86])).
% 1.97/0.65  fof(f86,plain,(
% 1.97/0.65    ( ! [X0] : (v1_compts_1(X0) | l1_waybel_0(sK4(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.97/0.65    inference(cnf_transformation,[],[f53])).
% 1.97/0.65  fof(f156,plain,(
% 1.97/0.65    v7_waybel_0(sK4(sK0)) | spl10_1),
% 1.97/0.65    inference(unit_resulting_resolution,[],[f69,f70,f71,f120,f85])).
% 1.97/0.65  fof(f85,plain,(
% 1.97/0.65    ( ! [X0] : (v1_compts_1(X0) | v7_waybel_0(sK4(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.97/0.65    inference(cnf_transformation,[],[f53])).
% 1.97/0.65  fof(f155,plain,(
% 1.97/0.65    v4_orders_2(sK4(sK0)) | spl10_1),
% 1.97/0.65    inference(unit_resulting_resolution,[],[f69,f70,f71,f120,f84])).
% 1.97/0.65  fof(f84,plain,(
% 1.97/0.65    ( ! [X0] : (v1_compts_1(X0) | v4_orders_2(sK4(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.97/0.65    inference(cnf_transformation,[],[f53])).
% 1.97/0.65  fof(f154,plain,(
% 1.97/0.65    ~v2_struct_0(sK4(sK0)) | spl10_1),
% 1.97/0.65    inference(unit_resulting_resolution,[],[f69,f70,f71,f120,f83])).
% 1.97/0.65  fof(f83,plain,(
% 1.97/0.65    ( ! [X0] : (v1_compts_1(X0) | ~v2_struct_0(sK4(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.97/0.65    inference(cnf_transformation,[],[f53])).
% 1.97/0.65  fof(f361,plain,(
% 1.97/0.65    m1_subset_1(sK6(sK0,sK2(sK4(sK0)),k1_xboole_0),u1_struct_0(sK0)) | (spl10_1 | ~spl10_7 | ~spl10_8 | ~spl10_10)),
% 1.97/0.65    inference(unit_resulting_resolution,[],[f69,f70,f71,f166,f167,f168,f169,f195,f190,f98])).
% 1.97/0.65  fof(f98,plain,(
% 1.97/0.65    ( ! [X2,X0,X1] : (k10_yellow_6(X0,X1) = X2 | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.97/0.65    inference(cnf_transformation,[],[f63])).
% 1.97/0.65  fof(f63,plain,(
% 1.97/0.65    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | (((~r1_waybel_0(X0,X1,sK7(X0,X1,X2)) & m1_connsp_2(sK7(X0,X1,X2),X0,sK6(X0,X1,X2))) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK6(X0,X1,X2))) | r2_hidden(sK6(X0,X1,X2),X2)) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)))) & (! [X6] : (((r2_hidden(X6,X2) | (~r1_waybel_0(X0,X1,sK8(X0,X1,X6)) & m1_connsp_2(sK8(X0,X1,X6),X0,X6))) & (! [X8] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6)) | ~r2_hidden(X6,X2))) | ~m1_subset_1(X6,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.97/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f59,f62,f61,f60])).
% 1.97/0.65  fof(f60,plain,(
% 1.97/0.65    ! [X2,X1,X0] : (? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0))) => ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,sK6(X0,X1,X2))) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK6(X0,X1,X2))) | r2_hidden(sK6(X0,X1,X2),X2)) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))))),
% 1.97/0.65    introduced(choice_axiom,[])).
% 1.97/0.65  fof(f61,plain,(
% 1.97/0.65    ! [X2,X1,X0] : (? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,sK6(X0,X1,X2))) => (~r1_waybel_0(X0,X1,sK7(X0,X1,X2)) & m1_connsp_2(sK7(X0,X1,X2),X0,sK6(X0,X1,X2))))),
% 1.97/0.65    introduced(choice_axiom,[])).
% 1.97/0.65  fof(f62,plain,(
% 1.97/0.65    ! [X6,X1,X0] : (? [X7] : (~r1_waybel_0(X0,X1,X7) & m1_connsp_2(X7,X0,X6)) => (~r1_waybel_0(X0,X1,sK8(X0,X1,X6)) & m1_connsp_2(sK8(X0,X1,X6),X0,X6)))),
% 1.97/0.65    introduced(choice_axiom,[])).
% 1.97/0.65  fof(f59,plain,(
% 1.97/0.65    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X6] : (((r2_hidden(X6,X2) | ? [X7] : (~r1_waybel_0(X0,X1,X7) & m1_connsp_2(X7,X0,X6))) & (! [X8] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6)) | ~r2_hidden(X6,X2))) | ~m1_subset_1(X6,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.97/0.65    inference(rectify,[],[f58])).
% 1.97/0.65  fof(f58,plain,(
% 1.97/0.65    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3))) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.97/0.65    inference(flattening,[],[f57])).
% 1.97/0.65  fof(f57,plain,(
% 1.97/0.65    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : (((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | r2_hidden(X3,X2))) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3))) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.97/0.65    inference(nnf_transformation,[],[f34])).
% 1.97/0.65  fof(f34,plain,(
% 1.97/0.65    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.97/0.65    inference(flattening,[],[f33])).
% 1.97/0.65  fof(f33,plain,(
% 1.97/0.65    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.97/0.65    inference(ennf_transformation,[],[f7])).
% 1.97/0.65  fof(f7,axiom,(
% 1.97/0.65    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (k10_yellow_6(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) <=> ! [X4] : (m1_connsp_2(X4,X0,X3) => r1_waybel_0(X0,X1,X4))))))))),
% 1.97/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_yellow_6)).
% 1.97/0.65  fof(f190,plain,(
% 1.97/0.65    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl10_10),
% 1.97/0.65    inference(avatar_component_clause,[],[f188])).
% 1.97/0.65  fof(f195,plain,(
% 1.97/0.65    k1_xboole_0 != k10_yellow_6(sK0,sK2(sK4(sK0))) | (spl10_1 | ~spl10_7 | ~spl10_8)),
% 1.97/0.65    inference(unit_resulting_resolution,[],[f69,f70,f71,f166,f167,f168,f160,f169,f89])).
% 1.97/0.65  fof(f89,plain,(
% 1.97/0.65    ( ! [X0,X1] : (k1_xboole_0 != k10_yellow_6(X0,X1) | ~v3_yellow_6(X1,X0) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.97/0.65    inference(cnf_transformation,[],[f54])).
% 1.97/0.65  fof(f160,plain,(
% 1.97/0.65    v3_yellow_6(sK2(sK4(sK0)),sK0) | (spl10_1 | ~spl10_7)),
% 1.97/0.65    inference(unit_resulting_resolution,[],[f156,f154,f155,f157,f147])).
% 1.97/0.65  fof(f147,plain,(
% 1.97/0.65    ( ! [X3] : (~v7_waybel_0(X3) | v2_struct_0(X3) | ~v4_orders_2(X3) | v3_yellow_6(sK2(X3),sK0) | ~l1_waybel_0(X3,sK0)) ) | ~spl10_7),
% 1.97/0.65    inference(avatar_component_clause,[],[f146])).
% 1.97/0.65  fof(f169,plain,(
% 1.97/0.65    l1_waybel_0(sK2(sK4(sK0)),sK0) | (spl10_1 | ~spl10_8)),
% 1.97/0.65    inference(unit_resulting_resolution,[],[f69,f153,f154,f155,f156,f157,f159,f105])).
% 1.97/0.65  fof(f168,plain,(
% 1.97/0.65    v7_waybel_0(sK2(sK4(sK0))) | (spl10_1 | ~spl10_8)),
% 1.97/0.65    inference(unit_resulting_resolution,[],[f69,f153,f154,f155,f156,f157,f159,f104])).
% 1.97/0.65  fof(f167,plain,(
% 1.97/0.65    v4_orders_2(sK2(sK4(sK0))) | (spl10_1 | ~spl10_8)),
% 1.97/0.65    inference(unit_resulting_resolution,[],[f69,f153,f154,f155,f156,f157,f159,f103])).
% 1.97/0.65  fof(f166,plain,(
% 1.97/0.65    ~v2_struct_0(sK2(sK4(sK0))) | (spl10_1 | ~spl10_8)),
% 1.97/0.65    inference(unit_resulting_resolution,[],[f69,f153,f154,f155,f156,f157,f159,f102])).
% 1.97/0.65  fof(f1185,plain,(
% 1.97/0.65    spl10_1 | ~spl10_7 | ~spl10_8 | ~spl10_10 | spl10_12),
% 1.97/0.65    inference(avatar_contradiction_clause,[],[f1184])).
% 1.97/0.65  fof(f1184,plain,(
% 1.97/0.65    $false | (spl10_1 | ~spl10_7 | ~spl10_8 | ~spl10_10 | spl10_12)),
% 1.97/0.65    inference(subsumption_resolution,[],[f1180,f827])).
% 1.97/0.65  fof(f827,plain,(
% 1.97/0.65    m1_connsp_2(sK8(sK0,sK2(sK4(sK0)),sK6(sK0,sK2(sK4(sK0)),k1_xboole_0)),sK0,sK6(sK0,sK2(sK4(sK0)),k1_xboole_0)) | (spl10_1 | ~spl10_7 | ~spl10_8 | ~spl10_10)),
% 1.97/0.65    inference(unit_resulting_resolution,[],[f69,f70,f71,f166,f167,f168,f169,f196,f361,f606,f115])).
% 1.97/0.65  fof(f115,plain,(
% 1.97/0.65    ( ! [X6,X0,X1] : (r2_hidden(X6,k10_yellow_6(X0,X1)) | m1_connsp_2(sK8(X0,X1,X6),X0,X6) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.97/0.65    inference(equality_resolution,[],[f96])).
% 1.97/0.65  fof(f96,plain,(
% 1.97/0.65    ( ! [X6,X2,X0,X1] : (r2_hidden(X6,X2) | m1_connsp_2(sK8(X0,X1,X6),X0,X6) | ~m1_subset_1(X6,u1_struct_0(X0)) | k10_yellow_6(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.97/0.65    inference(cnf_transformation,[],[f63])).
% 1.97/0.65  fof(f196,plain,(
% 1.97/0.65    m1_subset_1(k10_yellow_6(sK0,sK2(sK4(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) | (spl10_1 | ~spl10_8)),
% 1.97/0.65    inference(unit_resulting_resolution,[],[f69,f70,f71,f166,f167,f168,f169,f106])).
% 1.97/0.65  fof(f106,plain,(
% 1.97/0.65    ( ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.97/0.65    inference(cnf_transformation,[],[f38])).
% 1.97/0.65  fof(f38,plain,(
% 1.97/0.65    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.97/0.65    inference(flattening,[],[f37])).
% 1.97/0.65  fof(f37,plain,(
% 1.97/0.65    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.97/0.65    inference(ennf_transformation,[],[f8])).
% 1.97/0.65  fof(f8,axiom,(
% 1.97/0.65    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.97/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_yellow_6)).
% 1.97/0.65  fof(f1180,plain,(
% 1.97/0.65    ~m1_connsp_2(sK8(sK0,sK2(sK4(sK0)),sK6(sK0,sK2(sK4(sK0)),k1_xboole_0)),sK0,sK6(sK0,sK2(sK4(sK0)),k1_xboole_0)) | (spl10_1 | ~spl10_7 | ~spl10_8 | ~spl10_10 | spl10_12)),
% 1.97/0.65    inference(unit_resulting_resolution,[],[f828,f460])).
% 1.97/0.65  fof(f460,plain,(
% 1.97/0.65    ( ! [X0] : (r1_waybel_0(sK0,sK2(sK4(sK0)),X0) | ~m1_connsp_2(X0,sK0,sK6(sK0,sK2(sK4(sK0)),k1_xboole_0))) ) | (spl10_1 | ~spl10_7 | ~spl10_8 | ~spl10_10 | spl10_12)),
% 1.97/0.65    inference(subsumption_resolution,[],[f459,f190])).
% 1.97/0.65  fof(f459,plain,(
% 1.97/0.65    ( ! [X0] : (r1_waybel_0(sK0,sK2(sK4(sK0)),X0) | ~m1_connsp_2(X0,sK0,sK6(sK0,sK2(sK4(sK0)),k1_xboole_0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl10_1 | ~spl10_7 | ~spl10_8 | spl10_12)),
% 1.97/0.65    inference(subsumption_resolution,[],[f458,f450])).
% 1.97/0.65  fof(f450,plain,(
% 1.97/0.65    ~r2_hidden(sK6(sK0,sK2(sK4(sK0)),k1_xboole_0),k1_xboole_0) | spl10_12),
% 1.97/0.65    inference(avatar_component_clause,[],[f448])).
% 1.97/0.65  fof(f458,plain,(
% 1.97/0.65    ( ! [X0] : (r1_waybel_0(sK0,sK2(sK4(sK0)),X0) | ~m1_connsp_2(X0,sK0,sK6(sK0,sK2(sK4(sK0)),k1_xboole_0)) | r2_hidden(sK6(sK0,sK2(sK4(sK0)),k1_xboole_0),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl10_1 | ~spl10_7 | ~spl10_8)),
% 1.97/0.65    inference(equality_resolution,[],[f263])).
% 1.97/0.65  fof(f263,plain,(
% 1.97/0.65    ( ! [X2,X1] : (k1_xboole_0 != X1 | r1_waybel_0(sK0,sK2(sK4(sK0)),X2) | ~m1_connsp_2(X2,sK0,sK6(sK0,sK2(sK4(sK0)),X1)) | r2_hidden(sK6(sK0,sK2(sK4(sK0)),X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl10_1 | ~spl10_7 | ~spl10_8)),
% 1.97/0.65    inference(subsumption_resolution,[],[f262,f69])).
% 1.97/0.65  fof(f262,plain,(
% 1.97/0.65    ( ! [X2,X1] : (k1_xboole_0 != X1 | r1_waybel_0(sK0,sK2(sK4(sK0)),X2) | ~m1_connsp_2(X2,sK0,sK6(sK0,sK2(sK4(sK0)),X1)) | r2_hidden(sK6(sK0,sK2(sK4(sK0)),X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) ) | (spl10_1 | ~spl10_7 | ~spl10_8)),
% 1.97/0.65    inference(subsumption_resolution,[],[f261,f70])).
% 1.97/0.65  fof(f261,plain,(
% 1.97/0.65    ( ! [X2,X1] : (k1_xboole_0 != X1 | r1_waybel_0(sK0,sK2(sK4(sK0)),X2) | ~m1_connsp_2(X2,sK0,sK6(sK0,sK2(sK4(sK0)),X1)) | r2_hidden(sK6(sK0,sK2(sK4(sK0)),X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl10_1 | ~spl10_7 | ~spl10_8)),
% 1.97/0.65    inference(subsumption_resolution,[],[f260,f71])).
% 1.97/0.65  fof(f260,plain,(
% 1.97/0.65    ( ! [X2,X1] : (k1_xboole_0 != X1 | r1_waybel_0(sK0,sK2(sK4(sK0)),X2) | ~m1_connsp_2(X2,sK0,sK6(sK0,sK2(sK4(sK0)),X1)) | r2_hidden(sK6(sK0,sK2(sK4(sK0)),X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl10_1 | ~spl10_7 | ~spl10_8)),
% 1.97/0.65    inference(subsumption_resolution,[],[f259,f166])).
% 1.97/0.65  fof(f259,plain,(
% 1.97/0.65    ( ! [X2,X1] : (k1_xboole_0 != X1 | r1_waybel_0(sK0,sK2(sK4(sK0)),X2) | ~m1_connsp_2(X2,sK0,sK6(sK0,sK2(sK4(sK0)),X1)) | r2_hidden(sK6(sK0,sK2(sK4(sK0)),X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK2(sK4(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl10_1 | ~spl10_7 | ~spl10_8)),
% 1.97/0.65    inference(subsumption_resolution,[],[f258,f167])).
% 1.97/0.65  fof(f258,plain,(
% 1.97/0.65    ( ! [X2,X1] : (k1_xboole_0 != X1 | r1_waybel_0(sK0,sK2(sK4(sK0)),X2) | ~m1_connsp_2(X2,sK0,sK6(sK0,sK2(sK4(sK0)),X1)) | r2_hidden(sK6(sK0,sK2(sK4(sK0)),X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl10_1 | ~spl10_7 | ~spl10_8)),
% 1.97/0.65    inference(subsumption_resolution,[],[f257,f168])).
% 1.97/0.65  fof(f257,plain,(
% 1.97/0.65    ( ! [X2,X1] : (k1_xboole_0 != X1 | r1_waybel_0(sK0,sK2(sK4(sK0)),X2) | ~m1_connsp_2(X2,sK0,sK6(sK0,sK2(sK4(sK0)),X1)) | r2_hidden(sK6(sK0,sK2(sK4(sK0)),X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v7_waybel_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl10_1 | ~spl10_7 | ~spl10_8)),
% 1.97/0.65    inference(subsumption_resolution,[],[f245,f169])).
% 1.97/0.65  fof(f245,plain,(
% 1.97/0.65    ( ! [X2,X1] : (k1_xboole_0 != X1 | r1_waybel_0(sK0,sK2(sK4(sK0)),X2) | ~m1_connsp_2(X2,sK0,sK6(sK0,sK2(sK4(sK0)),X1)) | r2_hidden(sK6(sK0,sK2(sK4(sK0)),X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK2(sK4(sK0)),sK0) | ~v7_waybel_0(sK2(sK4(sK0))) | ~v4_orders_2(sK2(sK4(sK0))) | v2_struct_0(sK2(sK4(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl10_1 | ~spl10_7 | ~spl10_8)),
% 1.97/0.65    inference(superposition,[],[f195,f99])).
% 1.97/0.65  fof(f99,plain,(
% 1.97/0.65    ( ! [X2,X0,X5,X1] : (k10_yellow_6(X0,X1) = X2 | r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK6(X0,X1,X2)) | r2_hidden(sK6(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.97/0.65    inference(cnf_transformation,[],[f63])).
% 1.97/0.65  fof(f828,plain,(
% 1.97/0.65    ~r1_waybel_0(sK0,sK2(sK4(sK0)),sK8(sK0,sK2(sK4(sK0)),sK6(sK0,sK2(sK4(sK0)),k1_xboole_0))) | (spl10_1 | ~spl10_7 | ~spl10_8 | ~spl10_10)),
% 1.97/0.65    inference(unit_resulting_resolution,[],[f69,f70,f71,f166,f167,f168,f169,f196,f361,f606,f114])).
% 1.97/0.65  fof(f114,plain,(
% 1.97/0.65    ( ! [X6,X0,X1] : (r2_hidden(X6,k10_yellow_6(X0,X1)) | ~r1_waybel_0(X0,X1,sK8(X0,X1,X6)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.97/0.65    inference(equality_resolution,[],[f97])).
% 1.97/0.65  fof(f97,plain,(
% 1.97/0.65    ( ! [X6,X2,X0,X1] : (r2_hidden(X6,X2) | ~r1_waybel_0(X0,X1,sK8(X0,X1,X6)) | ~m1_subset_1(X6,u1_struct_0(X0)) | k10_yellow_6(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.97/0.65    inference(cnf_transformation,[],[f63])).
% 1.97/0.65  fof(f356,plain,(
% 1.97/0.65    spl10_10),
% 1.97/0.65    inference(avatar_contradiction_clause,[],[f355])).
% 1.97/0.65  fof(f355,plain,(
% 1.97/0.65    $false | spl10_10),
% 1.97/0.65    inference(subsumption_resolution,[],[f352,f79])).
% 1.97/0.65  fof(f352,plain,(
% 1.97/0.65    ~r1_tarski(k1_xboole_0,u1_struct_0(sK0)) | spl10_10),
% 1.97/0.65    inference(unit_resulting_resolution,[],[f189,f111])).
% 1.97/0.65  fof(f111,plain,(
% 1.97/0.65    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.97/0.65    inference(cnf_transformation,[],[f68])).
% 1.97/0.65  fof(f68,plain,(
% 1.97/0.65    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.97/0.65    inference(nnf_transformation,[],[f3])).
% 1.97/0.65  fof(f3,axiom,(
% 1.97/0.65    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.97/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.97/0.65  fof(f189,plain,(
% 1.97/0.65    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | spl10_10),
% 1.97/0.65    inference(avatar_component_clause,[],[f188])).
% 1.97/0.65  fof(f152,plain,(
% 1.97/0.65    spl10_1 | spl10_8),
% 1.97/0.65    inference(avatar_split_clause,[],[f72,f150,f118])).
% 1.97/0.65  fof(f72,plain,(
% 1.97/0.65    ( ! [X3] : (m2_yellow_6(sK2(X3),sK0,X3) | ~l1_waybel_0(X3,sK0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | v1_compts_1(sK0)) )),
% 1.97/0.65    inference(cnf_transformation,[],[f49])).
% 1.97/0.65  fof(f148,plain,(
% 1.97/0.65    spl10_1 | spl10_7),
% 1.97/0.65    inference(avatar_split_clause,[],[f73,f146,f118])).
% 1.97/0.65  fof(f73,plain,(
% 1.97/0.65    ( ! [X3] : (v3_yellow_6(sK2(X3),sK0) | ~l1_waybel_0(X3,sK0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | v1_compts_1(sK0)) )),
% 1.97/0.65    inference(cnf_transformation,[],[f49])).
% 1.97/0.65  fof(f144,plain,(
% 1.97/0.65    ~spl10_1 | ~spl10_6),
% 1.97/0.65    inference(avatar_split_clause,[],[f74,f141,f118])).
% 1.97/0.65  fof(f74,plain,(
% 1.97/0.65    ~v2_struct_0(sK1) | ~v1_compts_1(sK0)),
% 1.97/0.65    inference(cnf_transformation,[],[f49])).
% 1.97/0.65  fof(f139,plain,(
% 1.97/0.65    ~spl10_1 | spl10_5),
% 1.97/0.65    inference(avatar_split_clause,[],[f75,f136,f118])).
% 1.97/0.65  fof(f75,plain,(
% 1.97/0.65    v4_orders_2(sK1) | ~v1_compts_1(sK0)),
% 1.97/0.65    inference(cnf_transformation,[],[f49])).
% 1.97/0.65  fof(f134,plain,(
% 1.97/0.65    ~spl10_1 | spl10_4),
% 1.97/0.65    inference(avatar_split_clause,[],[f76,f131,f118])).
% 1.97/0.65  fof(f76,plain,(
% 1.97/0.65    v7_waybel_0(sK1) | ~v1_compts_1(sK0)),
% 1.97/0.65    inference(cnf_transformation,[],[f49])).
% 1.97/0.65  fof(f129,plain,(
% 1.97/0.65    ~spl10_1 | spl10_3),
% 1.97/0.65    inference(avatar_split_clause,[],[f77,f126,f118])).
% 1.97/0.65  fof(f77,plain,(
% 1.97/0.65    l1_waybel_0(sK1,sK0) | ~v1_compts_1(sK0)),
% 1.97/0.65    inference(cnf_transformation,[],[f49])).
% 1.97/0.65  fof(f124,plain,(
% 1.97/0.65    ~spl10_1 | spl10_2),
% 1.97/0.65    inference(avatar_split_clause,[],[f78,f122,f118])).
% 1.97/0.65  fof(f78,plain,(
% 1.97/0.65    ( ! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,sK1) | ~v1_compts_1(sK0)) )),
% 1.97/0.65    inference(cnf_transformation,[],[f49])).
% 1.97/0.65  % SZS output end Proof for theBenchmark
% 1.97/0.67  % (32603)Refutation not found, incomplete strategy% (32603)------------------------------
% 1.97/0.67  % (32603)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.97/0.67  % (32604)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 1.97/0.67  % (32603)Termination reason: Refutation not found, incomplete strategy
% 1.97/0.67  
% 1.97/0.67  % (32603)Memory used [KB]: 6268
% 1.97/0.67  % (32603)Time elapsed: 0.099 s
% 1.97/0.67  % (32603)------------------------------
% 1.97/0.67  % (32603)------------------------------
% 1.97/0.68  % (32589)------------------------------
% 1.97/0.68  % (32589)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.97/0.68  % (32589)Termination reason: Refutation
% 1.97/0.68  
% 1.97/0.68  % (32589)Memory used [KB]: 11769
% 1.97/0.68  % (32589)Time elapsed: 0.234 s
% 1.97/0.68  % (32589)------------------------------
% 1.97/0.68  % (32589)------------------------------
% 1.97/0.68  % (32559)Success in time 0.313 s
%------------------------------------------------------------------------------
