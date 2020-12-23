%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:38 EST 2020

% Result     : Theorem 2.22s
% Output     : Refutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :  171 (28595 expanded)
%              Number of leaves         :   31 (9472 expanded)
%              Depth                    :   23
%              Number of atoms          : 1105 (342286 expanded)
%              Number of equality atoms :   14 (  97 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f388,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f115,f120,f125,f130,f135,f139,f143,f339,f387])).

fof(f387,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6 ),
    inference(avatar_contradiction_clause,[],[f386])).

fof(f386,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6 ),
    inference(subsumption_resolution,[],[f380,f75])).

fof(f75,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f380,plain,
    ( ~ r1_tarski(k1_xboole_0,sK4(sK0,sK1))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6 ),
    inference(unit_resulting_resolution,[],[f378,f104])).

fof(f104,plain,(
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

fof(f378,plain,
    ( r2_hidden(sK4(sK0,sK1),k1_xboole_0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6 ),
    inference(subsumption_resolution,[],[f377,f65])).

fof(f65,plain,(
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

fof(f377,plain,
    ( r2_hidden(sK4(sK0,sK1),k1_xboole_0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6 ),
    inference(subsumption_resolution,[],[f376,f66])).

fof(f66,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f376,plain,
    ( r2_hidden(sK4(sK0,sK1),k1_xboole_0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6 ),
    inference(subsumption_resolution,[],[f375,f67])).

fof(f67,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f375,plain,
    ( r2_hidden(sK4(sK0,sK1),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6 ),
    inference(subsumption_resolution,[],[f374,f363])).

fof(f363,plain,
    ( ~ v2_struct_0(sK5(sK0,sK1,sK4(sK0,sK1)))
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6 ),
    inference(unit_resulting_resolution,[],[f65,f144,f134,f129,f124,f119,f353,f93])).

fof(f93,plain,(
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

fof(f353,plain,
    ( m2_yellow_6(sK5(sK0,sK1,sK4(sK0,sK1)),sK0,sK1)
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6 ),
    inference(unit_resulting_resolution,[],[f65,f66,f67,f134,f129,f124,f119,f342,f343,f88])).

fof(f88,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f53])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X2,k10_yellow_6(X0,X3))
          & m2_yellow_6(X3,X0,X1) )
     => ( r2_hidden(X2,k10_yellow_6(X0,sK5(X0,X1,X2)))
        & m2_yellow_6(sK5(X0,X1,X2),X0,X1) ) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_waybel_9)).

fof(f343,plain,
    ( r3_waybel_9(sK0,sK1,sK4(sK0,sK1))
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6 ),
    inference(unit_resulting_resolution,[],[f65,f66,f67,f110,f134,f129,f124,f119,f79])).

fof(f79,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
           => ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_yellow19)).

fof(f110,plain,
    ( v1_compts_1(sK0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl8_1
  <=> v1_compts_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f342,plain,
    ( m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6 ),
    inference(unit_resulting_resolution,[],[f65,f66,f67,f110,f134,f129,f124,f119,f78])).

fof(f78,plain,(
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

fof(f119,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl8_3
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f124,plain,
    ( v7_waybel_0(sK1)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl8_4
  <=> v7_waybel_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f129,plain,
    ( v4_orders_2(sK1)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl8_5
  <=> v4_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f134,plain,
    ( ~ v2_struct_0(sK1)
    | spl8_6 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl8_6
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f144,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f67,f76])).

fof(f76,plain,(
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

fof(f374,plain,
    ( r2_hidden(sK4(sK0,sK1),k1_xboole_0)
    | v2_struct_0(sK5(sK0,sK1,sK4(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6 ),
    inference(subsumption_resolution,[],[f373,f364])).

fof(f364,plain,
    ( v4_orders_2(sK5(sK0,sK1,sK4(sK0,sK1)))
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6 ),
    inference(unit_resulting_resolution,[],[f65,f144,f134,f129,f124,f119,f353,f94])).

fof(f94,plain,(
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

fof(f373,plain,
    ( r2_hidden(sK4(sK0,sK1),k1_xboole_0)
    | ~ v4_orders_2(sK5(sK0,sK1,sK4(sK0,sK1)))
    | v2_struct_0(sK5(sK0,sK1,sK4(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6 ),
    inference(subsumption_resolution,[],[f372,f365])).

fof(f365,plain,
    ( v7_waybel_0(sK5(sK0,sK1,sK4(sK0,sK1)))
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6 ),
    inference(unit_resulting_resolution,[],[f65,f144,f134,f129,f124,f119,f353,f95])).

fof(f95,plain,(
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

fof(f372,plain,
    ( r2_hidden(sK4(sK0,sK1),k1_xboole_0)
    | ~ v7_waybel_0(sK5(sK0,sK1,sK4(sK0,sK1)))
    | ~ v4_orders_2(sK5(sK0,sK1,sK4(sK0,sK1)))
    | v2_struct_0(sK5(sK0,sK1,sK4(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6 ),
    inference(subsumption_resolution,[],[f371,f366])).

fof(f366,plain,
    ( l1_waybel_0(sK5(sK0,sK1,sK4(sK0,sK1)),sK0)
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6 ),
    inference(unit_resulting_resolution,[],[f65,f144,f134,f129,f124,f119,f353,f96])).

fof(f96,plain,(
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

fof(f371,plain,
    ( r2_hidden(sK4(sK0,sK1),k1_xboole_0)
    | ~ l1_waybel_0(sK5(sK0,sK1,sK4(sK0,sK1)),sK0)
    | ~ v7_waybel_0(sK5(sK0,sK1,sK4(sK0,sK1)))
    | ~ v4_orders_2(sK5(sK0,sK1,sK4(sK0,sK1)))
    | v2_struct_0(sK5(sK0,sK1,sK4(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6 ),
    inference(subsumption_resolution,[],[f370,f362])).

fof(f362,plain,
    ( ~ v3_yellow_6(sK5(sK0,sK1,sK4(sK0,sK1)),sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6 ),
    inference(unit_resulting_resolution,[],[f353,f114])).

fof(f114,plain,
    ( ! [X2] :
        ( ~ v3_yellow_6(X2,sK0)
        | ~ m2_yellow_6(X2,sK0,sK1) )
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl8_2
  <=> ! [X2] :
        ( ~ v3_yellow_6(X2,sK0)
        | ~ m2_yellow_6(X2,sK0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f370,plain,
    ( r2_hidden(sK4(sK0,sK1),k1_xboole_0)
    | v3_yellow_6(sK5(sK0,sK1,sK4(sK0,sK1)),sK0)
    | ~ l1_waybel_0(sK5(sK0,sK1,sK4(sK0,sK1)),sK0)
    | ~ v7_waybel_0(sK5(sK0,sK1,sK4(sK0,sK1)))
    | ~ v4_orders_2(sK5(sK0,sK1,sK4(sK0,sK1)))
    | v2_struct_0(sK5(sK0,sK1,sK4(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6 ),
    inference(superposition,[],[f354,f86])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_yellow_6)).

fof(f354,plain,
    ( r2_hidden(sK4(sK0,sK1),k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,sK1))))
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6 ),
    inference(unit_resulting_resolution,[],[f65,f66,f67,f134,f129,f124,f119,f342,f343,f89])).

fof(f89,plain,(
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

fof(f339,plain,
    ( spl8_1
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(avatar_contradiction_clause,[],[f338])).

fof(f338,plain,
    ( $false
    | spl8_1
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f335,f314])).

fof(f314,plain,
    ( ~ r2_waybel_0(sK0,sK2(sK3(sK0)),sK6(sK0,sK3(sK0),sK7(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_xboole_0)))
    | spl8_1
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f65,f144,f145,f146,f147,f148,f149,f277,f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_waybel_0(X0,X1,X3)
      | ~ r2_waybel_0(X0,X2,X3)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_waybel_0(X0,X1,X3)
                  | ~ r2_waybel_0(X0,X2,X3) )
              | ~ m2_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_waybel_0(X0,X1,X3)
                  | ~ r2_waybel_0(X0,X2,X3) )
              | ~ m2_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m2_yellow_6(X2,X0,X1)
             => ! [X3] :
                  ( r2_waybel_0(X0,X2,X3)
                 => r2_waybel_0(X0,X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow_6)).

fof(f277,plain,
    ( ~ r2_waybel_0(sK0,sK3(sK0),sK6(sK0,sK3(sK0),sK7(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_xboole_0)))
    | spl8_1
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f65,f66,f67,f145,f148,f227,f259,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( r3_waybel_9(X0,X1,X2)
      | ~ r2_waybel_0(X0,X1,sK6(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_waybel_9(X0,X1,X2)
                  | ( ~ r2_waybel_0(X0,X1,sK6(X0,X1,X2))
                    & m1_connsp_2(sK6(X0,X1,X2),X0,X2) ) )
                & ( ! [X4] :
                      ( r2_waybel_0(X0,X1,X4)
                      | ~ m1_connsp_2(X4,X0,X2) )
                  | ~ r3_waybel_9(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f56,f57])).

fof(f57,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_waybel_0(X0,X1,X3)
          & m1_connsp_2(X3,X0,X2) )
     => ( ~ r2_waybel_0(X0,X1,sK6(X0,X1,X2))
        & m1_connsp_2(sK6(X0,X1,X2),X0,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_waybel_9(X0,X1,X2)
                  | ? [X3] :
                      ( ~ r2_waybel_0(X0,X1,X3)
                      & m1_connsp_2(X3,X0,X2) ) )
                & ( ! [X4] :
                      ( r2_waybel_0(X0,X1,X4)
                      | ~ m1_connsp_2(X4,X0,X2) )
                  | ~ r3_waybel_9(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_waybel_9(X0,X1,X2)
                  | ? [X3] :
                      ( ~ r2_waybel_0(X0,X1,X3)
                      & m1_connsp_2(X3,X0,X2) ) )
                & ( ! [X3] :
                      ( r2_waybel_0(X0,X1,X3)
                      | ~ m1_connsp_2(X3,X0,X2) )
                  | ~ r3_waybel_9(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_waybel_9(X0,X1,X2)
              <=> ! [X3] :
                    ( r2_waybel_0(X0,X1,X3)
                    | ~ m1_connsp_2(X3,X0,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_waybel_9(X0,X1,X2)
              <=> ! [X3] :
                    ( r2_waybel_0(X0,X1,X3)
                    | ~ m1_connsp_2(X3,X0,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
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
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_waybel_9(X0,X1,X2)
              <=> ! [X3] :
                    ( m1_connsp_2(X3,X0,X2)
                   => r2_waybel_0(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_waybel_9)).

fof(f259,plain,
    ( ~ r3_waybel_9(sK0,sK3(sK0),sK7(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_xboole_0))
    | spl8_1
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f65,f66,f67,f111,f227,f84])).

fof(f84,plain,(
    ! [X2,X0] :
      ( v1_compts_1(X0)
      | ~ r3_waybel_9(X0,sK3(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f111,plain,
    ( ~ v1_compts_1(sK0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f109])).

fof(f227,plain,
    ( m1_subset_1(sK7(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_xboole_0),u1_struct_0(sK0))
    | spl8_1
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f177,f200,f105])).

fof(f105,plain,(
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

fof(f200,plain,
    ( r2_hidden(sK7(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_xboole_0),k10_yellow_6(sK0,sK2(sK3(sK0))))
    | spl8_1
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f185,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK7(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f62,f63])).

fof(f63,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f61])).

fof(f61,plain,(
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

fof(f185,plain,
    ( ~ r1_tarski(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_xboole_0)
    | spl8_1
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f75,f176,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
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

fof(f176,plain,
    ( k1_xboole_0 != k10_yellow_6(sK0,sK2(sK3(sK0)))
    | spl8_1
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f65,f66,f67,f152,f153,f154,f150,f155,f85])).

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
    inference(cnf_transformation,[],[f52])).

fof(f155,plain,
    ( l1_waybel_0(sK2(sK3(sK0)),sK0)
    | spl8_1
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f65,f144,f145,f146,f147,f148,f149,f96])).

fof(f150,plain,
    ( v3_yellow_6(sK2(sK3(sK0)),sK0)
    | spl8_1
    | ~ spl8_7 ),
    inference(unit_resulting_resolution,[],[f147,f145,f146,f148,f138])).

fof(f138,plain,
    ( ! [X3] :
        ( ~ v7_waybel_0(X3)
        | v2_struct_0(X3)
        | ~ v4_orders_2(X3)
        | v3_yellow_6(sK2(X3),sK0)
        | ~ l1_waybel_0(X3,sK0) )
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl8_7
  <=> ! [X3] :
        ( v3_yellow_6(sK2(X3),sK0)
        | v2_struct_0(X3)
        | ~ v4_orders_2(X3)
        | ~ v7_waybel_0(X3)
        | ~ l1_waybel_0(X3,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f154,plain,
    ( v7_waybel_0(sK2(sK3(sK0)))
    | spl8_1
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f65,f144,f145,f146,f147,f148,f149,f95])).

fof(f153,plain,
    ( v4_orders_2(sK2(sK3(sK0)))
    | spl8_1
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f65,f144,f145,f146,f147,f148,f149,f94])).

fof(f152,plain,
    ( ~ v2_struct_0(sK2(sK3(sK0)))
    | spl8_1
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f65,f144,f145,f146,f147,f148,f149,f93])).

fof(f177,plain,
    ( m1_subset_1(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl8_1
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f65,f66,f67,f152,f153,f154,f155,f97])).

fof(f97,plain,(
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

fof(f149,plain,
    ( m2_yellow_6(sK2(sK3(sK0)),sK0,sK3(sK0))
    | spl8_1
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f147,f145,f146,f148,f142])).

fof(f142,plain,
    ( ! [X3] :
        ( ~ v7_waybel_0(X3)
        | v2_struct_0(X3)
        | ~ v4_orders_2(X3)
        | m2_yellow_6(sK2(X3),sK0,X3)
        | ~ l1_waybel_0(X3,sK0) )
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl8_8
  <=> ! [X3] :
        ( m2_yellow_6(sK2(X3),sK0,X3)
        | v2_struct_0(X3)
        | ~ v4_orders_2(X3)
        | ~ v7_waybel_0(X3)
        | ~ l1_waybel_0(X3,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f148,plain,
    ( l1_waybel_0(sK3(sK0),sK0)
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f65,f66,f67,f111,f83])).

fof(f83,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | l1_waybel_0(sK3(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f147,plain,
    ( v7_waybel_0(sK3(sK0))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f65,f66,f67,f111,f82])).

fof(f82,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | v7_waybel_0(sK3(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f146,plain,
    ( v4_orders_2(sK3(sK0))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f65,f66,f67,f111,f81])).

fof(f81,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | v4_orders_2(sK3(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f145,plain,
    ( ~ v2_struct_0(sK3(sK0))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f65,f66,f67,f111,f80])).

fof(f80,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ~ v2_struct_0(sK3(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f335,plain,
    ( r2_waybel_0(sK0,sK2(sK3(sK0)),sK6(sK0,sK3(sK0),sK7(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_xboole_0)))
    | spl8_1
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f65,f66,f67,f152,f155,f260,f227,f276,f90])).

fof(f90,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_waybel_0(X0,X1,X4)
      | ~ m1_connsp_2(X4,X0,X2)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f276,plain,
    ( m1_connsp_2(sK6(sK0,sK3(sK0),sK7(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_xboole_0)),sK0,sK7(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_xboole_0))
    | spl8_1
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f65,f66,f67,f145,f148,f227,f259,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( r3_waybel_9(X0,X1,X2)
      | m1_connsp_2(sK6(X0,X1,X2),X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f260,plain,
    ( r3_waybel_9(sK0,sK2(sK3(sK0)),sK7(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_xboole_0))
    | spl8_1
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f65,f66,f67,f152,f153,f154,f155,f200,f227,f87])).

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
             => ( r2_hidden(X2,k10_yellow_6(X0,X1))
               => r3_waybel_9(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_waybel_9)).

fof(f143,plain,
    ( spl8_1
    | spl8_8 ),
    inference(avatar_split_clause,[],[f68,f141,f109])).

fof(f68,plain,(
    ! [X3] :
      ( m2_yellow_6(sK2(X3),sK0,X3)
      | ~ l1_waybel_0(X3,sK0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f139,plain,
    ( spl8_1
    | spl8_7 ),
    inference(avatar_split_clause,[],[f69,f137,f109])).

fof(f69,plain,(
    ! [X3] :
      ( v3_yellow_6(sK2(X3),sK0)
      | ~ l1_waybel_0(X3,sK0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f135,plain,
    ( ~ spl8_1
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f70,f132,f109])).

fof(f70,plain,
    ( ~ v2_struct_0(sK1)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f130,plain,
    ( ~ spl8_1
    | spl8_5 ),
    inference(avatar_split_clause,[],[f71,f127,f109])).

fof(f71,plain,
    ( v4_orders_2(sK1)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f125,plain,
    ( ~ spl8_1
    | spl8_4 ),
    inference(avatar_split_clause,[],[f72,f122,f109])).

fof(f72,plain,
    ( v7_waybel_0(sK1)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f120,plain,
    ( ~ spl8_1
    | spl8_3 ),
    inference(avatar_split_clause,[],[f73,f117,f109])).

fof(f73,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f115,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f74,f113,f109])).

fof(f74,plain,(
    ! [X2] :
      ( ~ v3_yellow_6(X2,sK0)
      | ~ m2_yellow_6(X2,sK0,sK1)
      | ~ v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:07:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.56  % (10427)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.39/0.56  % (10419)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.39/0.56  % (10418)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.39/0.57  % (10436)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.39/0.57  % (10420)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.39/0.57  % (10426)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.59/0.58  % (10435)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.59/0.58  % (10416)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.59/0.58  % (10417)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.59/0.59  % (10424)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.59/0.59  % (10428)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.59/0.59  % (10431)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.59/0.59  % (10434)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.59/0.59  % (10434)Refutation not found, incomplete strategy% (10434)------------------------------
% 1.59/0.59  % (10434)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.59  % (10434)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.59  
% 1.59/0.59  % (10434)Memory used [KB]: 10874
% 1.59/0.59  % (10434)Time elapsed: 0.157 s
% 1.59/0.59  % (10434)------------------------------
% 1.59/0.59  % (10434)------------------------------
% 1.59/0.59  % (10425)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.59/0.59  % (10415)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.59/0.59  % (10440)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.59/0.59  % (10432)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.59/0.59  % (10429)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.59/0.60  % (10429)Refutation not found, incomplete strategy% (10429)------------------------------
% 1.59/0.60  % (10429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.60  % (10429)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.60  
% 1.59/0.60  % (10429)Memory used [KB]: 10746
% 1.59/0.60  % (10429)Time elapsed: 0.125 s
% 1.59/0.60  % (10429)------------------------------
% 1.59/0.60  % (10429)------------------------------
% 1.59/0.60  % (10437)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.59/0.60  % (10441)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.59/0.60  % (10423)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.59/0.60  % (10433)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.59/0.60  % (10421)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.59/0.61  % (10439)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.59/0.61  % (10413)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.59/0.62  % (10422)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.59/0.62  % (10414)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.59/0.62  % (10438)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.59/0.62  % (10412)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.59/0.63  % (10430)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.59/0.64  % (10422)Refutation not found, incomplete strategy% (10422)------------------------------
% 1.59/0.64  % (10422)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.05/0.64  % (10422)Termination reason: Refutation not found, incomplete strategy
% 2.05/0.64  
% 2.05/0.64  % (10422)Memory used [KB]: 10746
% 2.05/0.64  % (10422)Time elapsed: 0.205 s
% 2.05/0.64  % (10422)------------------------------
% 2.05/0.64  % (10422)------------------------------
% 2.22/0.67  % (10438)Refutation found. Thanks to Tanya!
% 2.22/0.67  % SZS status Theorem for theBenchmark
% 2.22/0.68  % SZS output start Proof for theBenchmark
% 2.22/0.68  fof(f388,plain,(
% 2.22/0.68    $false),
% 2.22/0.68    inference(avatar_sat_refutation,[],[f115,f120,f125,f130,f135,f139,f143,f339,f387])).
% 2.22/0.68  fof(f387,plain,(
% 2.22/0.68    ~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6),
% 2.22/0.68    inference(avatar_contradiction_clause,[],[f386])).
% 2.22/0.68  fof(f386,plain,(
% 2.22/0.68    $false | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6)),
% 2.22/0.68    inference(subsumption_resolution,[],[f380,f75])).
% 2.22/0.68  fof(f75,plain,(
% 2.22/0.68    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f3])).
% 2.22/0.68  fof(f3,axiom,(
% 2.22/0.68    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.22/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.22/0.68  fof(f380,plain,(
% 2.22/0.68    ~r1_tarski(k1_xboole_0,sK4(sK0,sK1)) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6)),
% 2.22/0.68    inference(unit_resulting_resolution,[],[f378,f104])).
% 2.22/0.68  fof(f104,plain,(
% 2.22/0.68    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f37])).
% 2.22/0.68  fof(f37,plain,(
% 2.22/0.68    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.22/0.68    inference(ennf_transformation,[],[f5])).
% 2.22/0.68  fof(f5,axiom,(
% 2.22/0.68    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.22/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 2.22/0.68  fof(f378,plain,(
% 2.22/0.68    r2_hidden(sK4(sK0,sK1),k1_xboole_0) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6)),
% 2.22/0.68    inference(subsumption_resolution,[],[f377,f65])).
% 2.22/0.68  fof(f65,plain,(
% 2.22/0.68    ~v2_struct_0(sK0)),
% 2.22/0.68    inference(cnf_transformation,[],[f46])).
% 2.22/0.68  fof(f46,plain,(
% 2.22/0.68    ((! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,sK1)) & l1_waybel_0(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1)) | ~v1_compts_1(sK0)) & (! [X3] : ((v3_yellow_6(sK2(X3),sK0) & m2_yellow_6(sK2(X3),sK0,X3)) | ~l1_waybel_0(X3,sK0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.22/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f42,f45,f44,f43])).
% 2.22/0.68  fof(f43,plain,(
% 2.22/0.68    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ((? [X1] : (! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,X1)) & l1_waybel_0(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(sK0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,sK0) & m2_yellow_6(X4,sK0,X3)) | ~l1_waybel_0(X3,sK0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.22/0.68    introduced(choice_axiom,[])).
% 2.22/0.68  fof(f44,plain,(
% 2.22/0.68    ? [X1] : (! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,X1)) & l1_waybel_0(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,sK1)) & l1_waybel_0(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1))),
% 2.22/0.68    introduced(choice_axiom,[])).
% 2.22/0.68  fof(f45,plain,(
% 2.22/0.68    ! [X3] : (? [X4] : (v3_yellow_6(X4,sK0) & m2_yellow_6(X4,sK0,X3)) => (v3_yellow_6(sK2(X3),sK0) & m2_yellow_6(sK2(X3),sK0,X3)))),
% 2.22/0.68    introduced(choice_axiom,[])).
% 2.22/0.68  fof(f42,plain,(
% 2.22/0.68    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.22/0.68    inference(rectify,[],[f41])).
% 2.22/0.68  fof(f41,plain,(
% 2.22/0.68    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.22/0.68    inference(flattening,[],[f40])).
% 2.22/0.68  fof(f40,plain,(
% 2.22/0.68    ? [X0] : (((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | v1_compts_1(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.22/0.68    inference(nnf_transformation,[],[f18])).
% 2.22/0.68  fof(f18,plain,(
% 2.22/0.68    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.22/0.68    inference(flattening,[],[f17])).
% 2.22/0.68  fof(f17,plain,(
% 2.22/0.68    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.22/0.68    inference(ennf_transformation,[],[f16])).
% 2.22/0.68  fof(f16,negated_conjecture,(
% 2.22/0.68    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)))))),
% 2.22/0.68    inference(negated_conjecture,[],[f15])).
% 2.22/0.68  fof(f15,conjecture,(
% 2.22/0.68    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)))))),
% 2.22/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_yellow19)).
% 2.22/0.68  fof(f377,plain,(
% 2.22/0.68    r2_hidden(sK4(sK0,sK1),k1_xboole_0) | v2_struct_0(sK0) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6)),
% 2.22/0.68    inference(subsumption_resolution,[],[f376,f66])).
% 2.22/0.68  fof(f66,plain,(
% 2.22/0.68    v2_pre_topc(sK0)),
% 2.22/0.68    inference(cnf_transformation,[],[f46])).
% 2.22/0.68  fof(f376,plain,(
% 2.22/0.68    r2_hidden(sK4(sK0,sK1),k1_xboole_0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6)),
% 2.22/0.68    inference(subsumption_resolution,[],[f375,f67])).
% 2.22/0.68  fof(f67,plain,(
% 2.22/0.68    l1_pre_topc(sK0)),
% 2.22/0.68    inference(cnf_transformation,[],[f46])).
% 2.22/0.68  fof(f375,plain,(
% 2.22/0.68    r2_hidden(sK4(sK0,sK1),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6)),
% 2.22/0.68    inference(subsumption_resolution,[],[f374,f363])).
% 2.22/0.68  fof(f363,plain,(
% 2.22/0.68    ~v2_struct_0(sK5(sK0,sK1,sK4(sK0,sK1))) | (~spl8_1 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6)),
% 2.22/0.68    inference(unit_resulting_resolution,[],[f65,f144,f134,f129,f124,f119,f353,f93])).
% 2.22/0.68  fof(f93,plain,(
% 2.22/0.68    ( ! [X2,X0,X1] : (~v2_struct_0(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f33])).
% 2.22/0.68  fof(f33,plain,(
% 2.22/0.68    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.22/0.68    inference(flattening,[],[f32])).
% 2.22/0.68  fof(f32,plain,(
% 2.22/0.68    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.22/0.68    inference(ennf_transformation,[],[f8])).
% 2.22/0.68  fof(f8,axiom,(
% 2.22/0.68    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))))),
% 2.22/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_yellow_6)).
% 2.22/0.68  fof(f353,plain,(
% 2.22/0.68    m2_yellow_6(sK5(sK0,sK1,sK4(sK0,sK1)),sK0,sK1) | (~spl8_1 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6)),
% 2.22/0.68    inference(unit_resulting_resolution,[],[f65,f66,f67,f134,f129,f124,f119,f342,f343,f88])).
% 2.22/0.68  fof(f88,plain,(
% 2.22/0.68    ( ! [X2,X0,X1] : (m2_yellow_6(sK5(X0,X1,X2),X0,X1) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f54])).
% 2.22/0.68  fof(f54,plain,(
% 2.22/0.68    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k10_yellow_6(X0,sK5(X0,X1,X2))) & m2_yellow_6(sK5(X0,X1,X2),X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.22/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f53])).
% 2.22/0.68  fof(f53,plain,(
% 2.22/0.68    ! [X2,X1,X0] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) => (r2_hidden(X2,k10_yellow_6(X0,sK5(X0,X1,X2))) & m2_yellow_6(sK5(X0,X1,X2),X0,X1)))),
% 2.22/0.68    introduced(choice_axiom,[])).
% 2.22/0.68  fof(f29,plain,(
% 2.22/0.68    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.22/0.68    inference(flattening,[],[f28])).
% 2.22/0.68  fof(f28,plain,(
% 2.22/0.68    ! [X0] : (! [X1] : (! [X2] : ((? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.22/0.68    inference(ennf_transformation,[],[f13])).
% 2.22/0.68  fof(f13,axiom,(
% 2.22/0.68    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m2_yellow_6(X3,X0,X1) => ~r2_hidden(X2,k10_yellow_6(X0,X3))) & r3_waybel_9(X0,X1,X2)))))),
% 2.22/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_waybel_9)).
% 2.22/0.68  fof(f343,plain,(
% 2.22/0.68    r3_waybel_9(sK0,sK1,sK4(sK0,sK1)) | (~spl8_1 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6)),
% 2.22/0.68    inference(unit_resulting_resolution,[],[f65,f66,f67,f110,f134,f129,f124,f119,f79])).
% 2.22/0.68  fof(f79,plain,(
% 2.22/0.68    ( ! [X0,X3] : (r3_waybel_9(X0,X3,sK4(X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f51])).
% 2.22/0.68  fof(f51,plain,(
% 2.22/0.68    ! [X0] : (((v1_compts_1(X0) | (! [X2] : (~r3_waybel_9(X0,sK3(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(sK3(X0),X0) & v7_waybel_0(sK3(X0)) & v4_orders_2(sK3(X0)) & ~v2_struct_0(sK3(X0)))) & (! [X3] : ((r3_waybel_9(X0,X3,sK4(X0,X3)) & m1_subset_1(sK4(X0,X3),u1_struct_0(X0))) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.22/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f48,f50,f49])).
% 2.22/0.68  fof(f49,plain,(
% 2.22/0.68    ! [X0] : (? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (~r3_waybel_9(X0,sK3(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(sK3(X0),X0) & v7_waybel_0(sK3(X0)) & v4_orders_2(sK3(X0)) & ~v2_struct_0(sK3(X0))))),
% 2.22/0.68    introduced(choice_axiom,[])).
% 2.22/0.68  fof(f50,plain,(
% 2.22/0.68    ! [X3,X0] : (? [X4] : (r3_waybel_9(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (r3_waybel_9(X0,X3,sK4(X0,X3)) & m1_subset_1(sK4(X0,X3),u1_struct_0(X0))))),
% 2.22/0.68    introduced(choice_axiom,[])).
% 2.22/0.68  fof(f48,plain,(
% 2.22/0.68    ! [X0] : (((v1_compts_1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (! [X3] : (? [X4] : (r3_waybel_9(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.22/0.68    inference(rectify,[],[f47])).
% 2.22/0.68  fof(f47,plain,(
% 2.22/0.68    ! [X0] : (((v1_compts_1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.22/0.68    inference(nnf_transformation,[],[f23])).
% 2.22/0.68  fof(f23,plain,(
% 2.22/0.68    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.22/0.68    inference(flattening,[],[f22])).
% 2.22/0.68  fof(f22,plain,(
% 2.22/0.68    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.22/0.68    inference(ennf_transformation,[],[f14])).
% 2.22/0.68  fof(f14,axiom,(
% 2.22/0.68    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))))))),
% 2.22/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_yellow19)).
% 2.22/0.68  fof(f110,plain,(
% 2.22/0.68    v1_compts_1(sK0) | ~spl8_1),
% 2.22/0.68    inference(avatar_component_clause,[],[f109])).
% 2.22/0.68  fof(f109,plain,(
% 2.22/0.68    spl8_1 <=> v1_compts_1(sK0)),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 2.22/0.68  fof(f342,plain,(
% 2.22/0.68    m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | (~spl8_1 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6)),
% 2.22/0.68    inference(unit_resulting_resolution,[],[f65,f66,f67,f110,f134,f129,f124,f119,f78])).
% 2.22/0.68  fof(f78,plain,(
% 2.22/0.68    ( ! [X0,X3] : (m1_subset_1(sK4(X0,X3),u1_struct_0(X0)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f51])).
% 2.22/0.68  fof(f119,plain,(
% 2.22/0.68    l1_waybel_0(sK1,sK0) | ~spl8_3),
% 2.22/0.68    inference(avatar_component_clause,[],[f117])).
% 2.22/0.68  fof(f117,plain,(
% 2.22/0.68    spl8_3 <=> l1_waybel_0(sK1,sK0)),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 2.22/0.68  fof(f124,plain,(
% 2.22/0.68    v7_waybel_0(sK1) | ~spl8_4),
% 2.22/0.68    inference(avatar_component_clause,[],[f122])).
% 2.22/0.68  fof(f122,plain,(
% 2.22/0.68    spl8_4 <=> v7_waybel_0(sK1)),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 2.22/0.68  fof(f129,plain,(
% 2.22/0.68    v4_orders_2(sK1) | ~spl8_5),
% 2.22/0.68    inference(avatar_component_clause,[],[f127])).
% 2.22/0.68  fof(f127,plain,(
% 2.22/0.68    spl8_5 <=> v4_orders_2(sK1)),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 2.22/0.68  fof(f134,plain,(
% 2.22/0.68    ~v2_struct_0(sK1) | spl8_6),
% 2.22/0.68    inference(avatar_component_clause,[],[f132])).
% 2.22/0.68  fof(f132,plain,(
% 2.22/0.68    spl8_6 <=> v2_struct_0(sK1)),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 2.22/0.68  fof(f144,plain,(
% 2.22/0.68    l1_struct_0(sK0)),
% 2.22/0.68    inference(unit_resulting_resolution,[],[f67,f76])).
% 2.22/0.68  fof(f76,plain,(
% 2.22/0.68    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f19])).
% 2.22/0.68  fof(f19,plain,(
% 2.22/0.68    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.22/0.68    inference(ennf_transformation,[],[f6])).
% 2.22/0.68  fof(f6,axiom,(
% 2.22/0.68    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.22/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 2.22/0.68  fof(f374,plain,(
% 2.22/0.68    r2_hidden(sK4(sK0,sK1),k1_xboole_0) | v2_struct_0(sK5(sK0,sK1,sK4(sK0,sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6)),
% 2.22/0.68    inference(subsumption_resolution,[],[f373,f364])).
% 2.22/0.68  fof(f364,plain,(
% 2.22/0.68    v4_orders_2(sK5(sK0,sK1,sK4(sK0,sK1))) | (~spl8_1 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6)),
% 2.22/0.68    inference(unit_resulting_resolution,[],[f65,f144,f134,f129,f124,f119,f353,f94])).
% 2.22/0.68  fof(f94,plain,(
% 2.22/0.68    ( ! [X2,X0,X1] : (v4_orders_2(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f33])).
% 2.22/0.68  fof(f373,plain,(
% 2.22/0.68    r2_hidden(sK4(sK0,sK1),k1_xboole_0) | ~v4_orders_2(sK5(sK0,sK1,sK4(sK0,sK1))) | v2_struct_0(sK5(sK0,sK1,sK4(sK0,sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6)),
% 2.22/0.68    inference(subsumption_resolution,[],[f372,f365])).
% 2.22/0.68  fof(f365,plain,(
% 2.22/0.68    v7_waybel_0(sK5(sK0,sK1,sK4(sK0,sK1))) | (~spl8_1 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6)),
% 2.22/0.68    inference(unit_resulting_resolution,[],[f65,f144,f134,f129,f124,f119,f353,f95])).
% 2.22/0.68  fof(f95,plain,(
% 2.22/0.68    ( ! [X2,X0,X1] : (v7_waybel_0(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f33])).
% 2.22/0.68  fof(f372,plain,(
% 2.22/0.68    r2_hidden(sK4(sK0,sK1),k1_xboole_0) | ~v7_waybel_0(sK5(sK0,sK1,sK4(sK0,sK1))) | ~v4_orders_2(sK5(sK0,sK1,sK4(sK0,sK1))) | v2_struct_0(sK5(sK0,sK1,sK4(sK0,sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6)),
% 2.22/0.68    inference(subsumption_resolution,[],[f371,f366])).
% 2.22/0.68  fof(f366,plain,(
% 2.22/0.68    l1_waybel_0(sK5(sK0,sK1,sK4(sK0,sK1)),sK0) | (~spl8_1 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6)),
% 2.22/0.68    inference(unit_resulting_resolution,[],[f65,f144,f134,f129,f124,f119,f353,f96])).
% 2.22/0.68  fof(f96,plain,(
% 2.22/0.68    ( ! [X2,X0,X1] : (l1_waybel_0(X2,X0) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f33])).
% 2.22/0.68  fof(f371,plain,(
% 2.22/0.68    r2_hidden(sK4(sK0,sK1),k1_xboole_0) | ~l1_waybel_0(sK5(sK0,sK1,sK4(sK0,sK1)),sK0) | ~v7_waybel_0(sK5(sK0,sK1,sK4(sK0,sK1))) | ~v4_orders_2(sK5(sK0,sK1,sK4(sK0,sK1))) | v2_struct_0(sK5(sK0,sK1,sK4(sK0,sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6)),
% 2.22/0.68    inference(subsumption_resolution,[],[f370,f362])).
% 2.22/0.68  fof(f362,plain,(
% 2.22/0.68    ~v3_yellow_6(sK5(sK0,sK1,sK4(sK0,sK1)),sK0) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6)),
% 2.22/0.68    inference(unit_resulting_resolution,[],[f353,f114])).
% 2.22/0.68  fof(f114,plain,(
% 2.22/0.68    ( ! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,sK1)) ) | ~spl8_2),
% 2.22/0.68    inference(avatar_component_clause,[],[f113])).
% 2.22/0.68  fof(f113,plain,(
% 2.22/0.68    spl8_2 <=> ! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,sK1))),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 2.22/0.68  fof(f370,plain,(
% 2.22/0.68    r2_hidden(sK4(sK0,sK1),k1_xboole_0) | v3_yellow_6(sK5(sK0,sK1,sK4(sK0,sK1)),sK0) | ~l1_waybel_0(sK5(sK0,sK1,sK4(sK0,sK1)),sK0) | ~v7_waybel_0(sK5(sK0,sK1,sK4(sK0,sK1))) | ~v4_orders_2(sK5(sK0,sK1,sK4(sK0,sK1))) | v2_struct_0(sK5(sK0,sK1,sK4(sK0,sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_1 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6)),
% 2.22/0.68    inference(superposition,[],[f354,f86])).
% 2.22/0.68  fof(f86,plain,(
% 2.22/0.68    ( ! [X0,X1] : (v3_yellow_6(X1,X0) | k1_xboole_0 = k10_yellow_6(X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f52])).
% 2.22/0.68  fof(f52,plain,(
% 2.22/0.68    ! [X0] : (! [X1] : (((v3_yellow_6(X1,X0) | k1_xboole_0 = k10_yellow_6(X0,X1)) & (k1_xboole_0 != k10_yellow_6(X0,X1) | ~v3_yellow_6(X1,X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.22/0.68    inference(nnf_transformation,[],[f25])).
% 2.22/0.68  fof(f25,plain,(
% 2.22/0.68    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.22/0.68    inference(flattening,[],[f24])).
% 2.22/0.68  fof(f24,plain,(
% 2.22/0.68    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.22/0.68    inference(ennf_transformation,[],[f10])).
% 2.22/0.68  fof(f10,axiom,(
% 2.22/0.68    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1))))),
% 2.22/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_yellow_6)).
% 2.22/0.68  fof(f354,plain,(
% 2.22/0.68    r2_hidden(sK4(sK0,sK1),k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,sK1)))) | (~spl8_1 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6)),
% 2.22/0.68    inference(unit_resulting_resolution,[],[f65,f66,f67,f134,f129,f124,f119,f342,f343,f89])).
% 2.22/0.68  fof(f89,plain,(
% 2.22/0.68    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,sK5(X0,X1,X2))) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f54])).
% 2.22/0.68  fof(f339,plain,(
% 2.22/0.68    spl8_1 | ~spl8_7 | ~spl8_8),
% 2.22/0.68    inference(avatar_contradiction_clause,[],[f338])).
% 2.22/0.68  fof(f338,plain,(
% 2.22/0.68    $false | (spl8_1 | ~spl8_7 | ~spl8_8)),
% 2.22/0.68    inference(subsumption_resolution,[],[f335,f314])).
% 2.22/0.68  fof(f314,plain,(
% 2.22/0.68    ~r2_waybel_0(sK0,sK2(sK3(sK0)),sK6(sK0,sK3(sK0),sK7(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_xboole_0))) | (spl8_1 | ~spl8_7 | ~spl8_8)),
% 2.22/0.68    inference(unit_resulting_resolution,[],[f65,f144,f145,f146,f147,f148,f149,f277,f77])).
% 2.22/0.68  fof(f77,plain,(
% 2.22/0.68    ( ! [X2,X0,X3,X1] : (r2_waybel_0(X0,X1,X3) | ~r2_waybel_0(X0,X2,X3) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f21])).
% 2.22/0.68  fof(f21,plain,(
% 2.22/0.68    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_waybel_0(X0,X1,X3) | ~r2_waybel_0(X0,X2,X3)) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.22/0.68    inference(flattening,[],[f20])).
% 2.22/0.68  fof(f20,plain,(
% 2.22/0.68    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_waybel_0(X0,X1,X3) | ~r2_waybel_0(X0,X2,X3)) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.22/0.68    inference(ennf_transformation,[],[f9])).
% 2.22/0.68  fof(f9,axiom,(
% 2.22/0.68    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => ! [X3] : (r2_waybel_0(X0,X2,X3) => r2_waybel_0(X0,X1,X3)))))),
% 2.22/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow_6)).
% 2.22/0.68  fof(f277,plain,(
% 2.22/0.68    ~r2_waybel_0(sK0,sK3(sK0),sK6(sK0,sK3(sK0),sK7(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_xboole_0))) | (spl8_1 | ~spl8_7 | ~spl8_8)),
% 2.22/0.68    inference(unit_resulting_resolution,[],[f65,f66,f67,f145,f148,f227,f259,f92])).
% 2.22/0.68  fof(f92,plain,(
% 2.22/0.68    ( ! [X2,X0,X1] : (r3_waybel_9(X0,X1,X2) | ~r2_waybel_0(X0,X1,sK6(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f58])).
% 2.22/0.68  fof(f58,plain,(
% 2.22/0.68    ! [X0] : (! [X1] : (! [X2] : (((r3_waybel_9(X0,X1,X2) | (~r2_waybel_0(X0,X1,sK6(X0,X1,X2)) & m1_connsp_2(sK6(X0,X1,X2),X0,X2))) & (! [X4] : (r2_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X2)) | ~r3_waybel_9(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.22/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f56,f57])).
% 2.22/0.68  fof(f57,plain,(
% 2.22/0.68    ! [X2,X1,X0] : (? [X3] : (~r2_waybel_0(X0,X1,X3) & m1_connsp_2(X3,X0,X2)) => (~r2_waybel_0(X0,X1,sK6(X0,X1,X2)) & m1_connsp_2(sK6(X0,X1,X2),X0,X2)))),
% 2.22/0.68    introduced(choice_axiom,[])).
% 2.22/0.68  fof(f56,plain,(
% 2.22/0.68    ! [X0] : (! [X1] : (! [X2] : (((r3_waybel_9(X0,X1,X2) | ? [X3] : (~r2_waybel_0(X0,X1,X3) & m1_connsp_2(X3,X0,X2))) & (! [X4] : (r2_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X2)) | ~r3_waybel_9(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.22/0.68    inference(rectify,[],[f55])).
% 2.22/0.68  fof(f55,plain,(
% 2.22/0.68    ! [X0] : (! [X1] : (! [X2] : (((r3_waybel_9(X0,X1,X2) | ? [X3] : (~r2_waybel_0(X0,X1,X3) & m1_connsp_2(X3,X0,X2))) & (! [X3] : (r2_waybel_0(X0,X1,X3) | ~m1_connsp_2(X3,X0,X2)) | ~r3_waybel_9(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.22/0.68    inference(nnf_transformation,[],[f31])).
% 2.22/0.68  fof(f31,plain,(
% 2.22/0.68    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> ! [X3] : (r2_waybel_0(X0,X1,X3) | ~m1_connsp_2(X3,X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.22/0.68    inference(flattening,[],[f30])).
% 2.22/0.68  fof(f30,plain,(
% 2.22/0.68    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> ! [X3] : (r2_waybel_0(X0,X1,X3) | ~m1_connsp_2(X3,X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.22/0.68    inference(ennf_transformation,[],[f11])).
% 2.22/0.68  fof(f11,axiom,(
% 2.22/0.68    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X2) <=> ! [X3] : (m1_connsp_2(X3,X0,X2) => r2_waybel_0(X0,X1,X3))))))),
% 2.22/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_waybel_9)).
% 2.22/0.68  fof(f259,plain,(
% 2.22/0.68    ~r3_waybel_9(sK0,sK3(sK0),sK7(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_xboole_0)) | (spl8_1 | ~spl8_7 | ~spl8_8)),
% 2.22/0.68    inference(unit_resulting_resolution,[],[f65,f66,f67,f111,f227,f84])).
% 2.22/0.68  fof(f84,plain,(
% 2.22/0.68    ( ! [X2,X0] : (v1_compts_1(X0) | ~r3_waybel_9(X0,sK3(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f51])).
% 2.22/0.68  fof(f111,plain,(
% 2.22/0.68    ~v1_compts_1(sK0) | spl8_1),
% 2.22/0.68    inference(avatar_component_clause,[],[f109])).
% 2.22/0.68  fof(f227,plain,(
% 2.22/0.68    m1_subset_1(sK7(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_xboole_0),u1_struct_0(sK0)) | (spl8_1 | ~spl8_7 | ~spl8_8)),
% 2.22/0.68    inference(unit_resulting_resolution,[],[f177,f200,f105])).
% 2.22/0.68  fof(f105,plain,(
% 2.22/0.68    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f39])).
% 2.22/0.68  fof(f39,plain,(
% 2.22/0.68    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.22/0.68    inference(flattening,[],[f38])).
% 2.22/0.68  fof(f38,plain,(
% 2.22/0.68    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.22/0.68    inference(ennf_transformation,[],[f4])).
% 2.22/0.68  fof(f4,axiom,(
% 2.22/0.68    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.22/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 2.22/0.68  fof(f200,plain,(
% 2.22/0.68    r2_hidden(sK7(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_xboole_0),k10_yellow_6(sK0,sK2(sK3(sK0)))) | (spl8_1 | ~spl8_7 | ~spl8_8)),
% 2.22/0.68    inference(unit_resulting_resolution,[],[f185,f102])).
% 2.22/0.68  fof(f102,plain,(
% 2.22/0.68    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK7(X0,X1),X0)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f64])).
% 2.22/0.68  fof(f64,plain,(
% 2.22/0.68    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.22/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f62,f63])).
% 2.22/0.68  fof(f63,plain,(
% 2.22/0.68    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 2.22/0.68    introduced(choice_axiom,[])).
% 2.22/0.68  fof(f62,plain,(
% 2.22/0.68    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.22/0.68    inference(rectify,[],[f61])).
% 2.22/0.68  fof(f61,plain,(
% 2.22/0.68    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.22/0.68    inference(nnf_transformation,[],[f36])).
% 2.22/0.68  fof(f36,plain,(
% 2.22/0.68    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.22/0.68    inference(ennf_transformation,[],[f1])).
% 2.22/0.68  fof(f1,axiom,(
% 2.22/0.68    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.22/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.22/0.68  fof(f185,plain,(
% 2.22/0.68    ~r1_tarski(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_xboole_0) | (spl8_1 | ~spl8_7 | ~spl8_8)),
% 2.22/0.68    inference(unit_resulting_resolution,[],[f75,f176,f100])).
% 2.22/0.68  fof(f100,plain,(
% 2.22/0.68    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f60])).
% 2.22/0.68  fof(f60,plain,(
% 2.22/0.68    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.22/0.68    inference(flattening,[],[f59])).
% 2.22/0.68  fof(f59,plain,(
% 2.22/0.68    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.22/0.68    inference(nnf_transformation,[],[f2])).
% 2.22/0.68  fof(f2,axiom,(
% 2.22/0.68    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.22/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.22/0.68  fof(f176,plain,(
% 2.22/0.68    k1_xboole_0 != k10_yellow_6(sK0,sK2(sK3(sK0))) | (spl8_1 | ~spl8_7 | ~spl8_8)),
% 2.22/0.68    inference(unit_resulting_resolution,[],[f65,f66,f67,f152,f153,f154,f150,f155,f85])).
% 2.22/0.68  fof(f85,plain,(
% 2.22/0.68    ( ! [X0,X1] : (k1_xboole_0 != k10_yellow_6(X0,X1) | ~v3_yellow_6(X1,X0) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f52])).
% 2.22/0.68  fof(f155,plain,(
% 2.22/0.68    l1_waybel_0(sK2(sK3(sK0)),sK0) | (spl8_1 | ~spl8_8)),
% 2.22/0.68    inference(unit_resulting_resolution,[],[f65,f144,f145,f146,f147,f148,f149,f96])).
% 2.22/0.68  fof(f150,plain,(
% 2.22/0.68    v3_yellow_6(sK2(sK3(sK0)),sK0) | (spl8_1 | ~spl8_7)),
% 2.22/0.68    inference(unit_resulting_resolution,[],[f147,f145,f146,f148,f138])).
% 2.22/0.68  fof(f138,plain,(
% 2.22/0.68    ( ! [X3] : (~v7_waybel_0(X3) | v2_struct_0(X3) | ~v4_orders_2(X3) | v3_yellow_6(sK2(X3),sK0) | ~l1_waybel_0(X3,sK0)) ) | ~spl8_7),
% 2.22/0.68    inference(avatar_component_clause,[],[f137])).
% 2.22/0.68  fof(f137,plain,(
% 2.22/0.68    spl8_7 <=> ! [X3] : (v3_yellow_6(sK2(X3),sK0) | v2_struct_0(X3) | ~v4_orders_2(X3) | ~v7_waybel_0(X3) | ~l1_waybel_0(X3,sK0))),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 2.22/0.68  fof(f154,plain,(
% 2.22/0.68    v7_waybel_0(sK2(sK3(sK0))) | (spl8_1 | ~spl8_8)),
% 2.22/0.68    inference(unit_resulting_resolution,[],[f65,f144,f145,f146,f147,f148,f149,f95])).
% 2.22/0.68  fof(f153,plain,(
% 2.22/0.68    v4_orders_2(sK2(sK3(sK0))) | (spl8_1 | ~spl8_8)),
% 2.22/0.68    inference(unit_resulting_resolution,[],[f65,f144,f145,f146,f147,f148,f149,f94])).
% 2.22/0.68  fof(f152,plain,(
% 2.22/0.68    ~v2_struct_0(sK2(sK3(sK0))) | (spl8_1 | ~spl8_8)),
% 2.22/0.68    inference(unit_resulting_resolution,[],[f65,f144,f145,f146,f147,f148,f149,f93])).
% 2.22/0.68  fof(f177,plain,(
% 2.22/0.68    m1_subset_1(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) | (spl8_1 | ~spl8_8)),
% 2.22/0.68    inference(unit_resulting_resolution,[],[f65,f66,f67,f152,f153,f154,f155,f97])).
% 2.22/0.68  fof(f97,plain,(
% 2.22/0.68    ( ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f35])).
% 2.22/0.68  fof(f35,plain,(
% 2.22/0.68    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.22/0.68    inference(flattening,[],[f34])).
% 2.22/0.68  fof(f34,plain,(
% 2.22/0.68    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.22/0.68    inference(ennf_transformation,[],[f7])).
% 2.22/0.68  fof(f7,axiom,(
% 2.22/0.68    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.22/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_yellow_6)).
% 2.22/0.68  fof(f149,plain,(
% 2.22/0.68    m2_yellow_6(sK2(sK3(sK0)),sK0,sK3(sK0)) | (spl8_1 | ~spl8_8)),
% 2.22/0.68    inference(unit_resulting_resolution,[],[f147,f145,f146,f148,f142])).
% 2.22/0.68  fof(f142,plain,(
% 2.22/0.68    ( ! [X3] : (~v7_waybel_0(X3) | v2_struct_0(X3) | ~v4_orders_2(X3) | m2_yellow_6(sK2(X3),sK0,X3) | ~l1_waybel_0(X3,sK0)) ) | ~spl8_8),
% 2.22/0.68    inference(avatar_component_clause,[],[f141])).
% 2.22/0.68  fof(f141,plain,(
% 2.22/0.68    spl8_8 <=> ! [X3] : (m2_yellow_6(sK2(X3),sK0,X3) | v2_struct_0(X3) | ~v4_orders_2(X3) | ~v7_waybel_0(X3) | ~l1_waybel_0(X3,sK0))),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 2.22/0.68  fof(f148,plain,(
% 2.22/0.68    l1_waybel_0(sK3(sK0),sK0) | spl8_1),
% 2.22/0.68    inference(unit_resulting_resolution,[],[f65,f66,f67,f111,f83])).
% 2.22/0.68  fof(f83,plain,(
% 2.22/0.68    ( ! [X0] : (v1_compts_1(X0) | l1_waybel_0(sK3(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f51])).
% 2.22/0.68  fof(f147,plain,(
% 2.22/0.68    v7_waybel_0(sK3(sK0)) | spl8_1),
% 2.22/0.68    inference(unit_resulting_resolution,[],[f65,f66,f67,f111,f82])).
% 2.22/0.68  fof(f82,plain,(
% 2.22/0.68    ( ! [X0] : (v1_compts_1(X0) | v7_waybel_0(sK3(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f51])).
% 2.22/0.68  fof(f146,plain,(
% 2.22/0.68    v4_orders_2(sK3(sK0)) | spl8_1),
% 2.22/0.68    inference(unit_resulting_resolution,[],[f65,f66,f67,f111,f81])).
% 2.22/0.68  fof(f81,plain,(
% 2.22/0.68    ( ! [X0] : (v1_compts_1(X0) | v4_orders_2(sK3(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f51])).
% 2.22/0.68  fof(f145,plain,(
% 2.22/0.68    ~v2_struct_0(sK3(sK0)) | spl8_1),
% 2.22/0.68    inference(unit_resulting_resolution,[],[f65,f66,f67,f111,f80])).
% 2.22/0.68  fof(f80,plain,(
% 2.22/0.68    ( ! [X0] : (v1_compts_1(X0) | ~v2_struct_0(sK3(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f51])).
% 2.22/0.68  fof(f335,plain,(
% 2.22/0.68    r2_waybel_0(sK0,sK2(sK3(sK0)),sK6(sK0,sK3(sK0),sK7(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_xboole_0))) | (spl8_1 | ~spl8_7 | ~spl8_8)),
% 2.22/0.68    inference(unit_resulting_resolution,[],[f65,f66,f67,f152,f155,f260,f227,f276,f90])).
% 2.22/0.68  fof(f90,plain,(
% 2.22/0.68    ( ! [X4,X2,X0,X1] : (r2_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X2) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f58])).
% 2.22/0.68  fof(f276,plain,(
% 2.22/0.68    m1_connsp_2(sK6(sK0,sK3(sK0),sK7(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_xboole_0)),sK0,sK7(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_xboole_0)) | (spl8_1 | ~spl8_7 | ~spl8_8)),
% 2.22/0.68    inference(unit_resulting_resolution,[],[f65,f66,f67,f145,f148,f227,f259,f91])).
% 2.22/0.68  fof(f91,plain,(
% 2.22/0.68    ( ! [X2,X0,X1] : (r3_waybel_9(X0,X1,X2) | m1_connsp_2(sK6(X0,X1,X2),X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f58])).
% 2.22/0.68  fof(f260,plain,(
% 2.22/0.68    r3_waybel_9(sK0,sK2(sK3(sK0)),sK7(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_xboole_0)) | (spl8_1 | ~spl8_7 | ~spl8_8)),
% 2.22/0.68    inference(unit_resulting_resolution,[],[f65,f66,f67,f152,f153,f154,f155,f200,f227,f87])).
% 2.22/0.68  fof(f87,plain,(
% 2.22/0.68    ( ! [X2,X0,X1] : (r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f27])).
% 2.22/0.68  fof(f27,plain,(
% 2.22/0.68    ! [X0] : (! [X1] : (! [X2] : (r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.22/0.68    inference(flattening,[],[f26])).
% 2.22/0.68  fof(f26,plain,(
% 2.22/0.68    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.22/0.68    inference(ennf_transformation,[],[f12])).
% 2.22/0.68  fof(f12,axiom,(
% 2.22/0.68    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,X1)) => r3_waybel_9(X0,X1,X2)))))),
% 2.22/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_waybel_9)).
% 2.22/0.68  fof(f143,plain,(
% 2.22/0.68    spl8_1 | spl8_8),
% 2.22/0.68    inference(avatar_split_clause,[],[f68,f141,f109])).
% 2.22/0.68  fof(f68,plain,(
% 2.22/0.68    ( ! [X3] : (m2_yellow_6(sK2(X3),sK0,X3) | ~l1_waybel_0(X3,sK0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | v1_compts_1(sK0)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f46])).
% 2.22/0.68  fof(f139,plain,(
% 2.22/0.68    spl8_1 | spl8_7),
% 2.22/0.68    inference(avatar_split_clause,[],[f69,f137,f109])).
% 2.22/0.69  fof(f69,plain,(
% 2.22/0.69    ( ! [X3] : (v3_yellow_6(sK2(X3),sK0) | ~l1_waybel_0(X3,sK0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | v1_compts_1(sK0)) )),
% 2.22/0.69    inference(cnf_transformation,[],[f46])).
% 2.22/0.69  fof(f135,plain,(
% 2.22/0.69    ~spl8_1 | ~spl8_6),
% 2.22/0.69    inference(avatar_split_clause,[],[f70,f132,f109])).
% 2.22/0.69  fof(f70,plain,(
% 2.22/0.69    ~v2_struct_0(sK1) | ~v1_compts_1(sK0)),
% 2.22/0.69    inference(cnf_transformation,[],[f46])).
% 2.22/0.69  fof(f130,plain,(
% 2.22/0.69    ~spl8_1 | spl8_5),
% 2.22/0.69    inference(avatar_split_clause,[],[f71,f127,f109])).
% 2.22/0.69  fof(f71,plain,(
% 2.22/0.69    v4_orders_2(sK1) | ~v1_compts_1(sK0)),
% 2.22/0.69    inference(cnf_transformation,[],[f46])).
% 2.22/0.69  fof(f125,plain,(
% 2.22/0.69    ~spl8_1 | spl8_4),
% 2.22/0.69    inference(avatar_split_clause,[],[f72,f122,f109])).
% 2.22/0.69  fof(f72,plain,(
% 2.22/0.69    v7_waybel_0(sK1) | ~v1_compts_1(sK0)),
% 2.22/0.69    inference(cnf_transformation,[],[f46])).
% 2.22/0.69  fof(f120,plain,(
% 2.22/0.69    ~spl8_1 | spl8_3),
% 2.22/0.69    inference(avatar_split_clause,[],[f73,f117,f109])).
% 2.22/0.69  fof(f73,plain,(
% 2.22/0.69    l1_waybel_0(sK1,sK0) | ~v1_compts_1(sK0)),
% 2.22/0.69    inference(cnf_transformation,[],[f46])).
% 2.22/0.69  fof(f115,plain,(
% 2.22/0.69    ~spl8_1 | spl8_2),
% 2.22/0.69    inference(avatar_split_clause,[],[f74,f113,f109])).
% 2.22/0.69  fof(f74,plain,(
% 2.22/0.69    ( ! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,sK1) | ~v1_compts_1(sK0)) )),
% 2.22/0.69    inference(cnf_transformation,[],[f46])).
% 2.22/0.69  % SZS output end Proof for theBenchmark
% 2.22/0.69  % (10438)------------------------------
% 2.22/0.69  % (10438)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.69  % (10438)Termination reason: Refutation
% 2.22/0.69  
% 2.22/0.69  % (10438)Memory used [KB]: 11129
% 2.22/0.69  % (10438)Time elapsed: 0.256 s
% 2.22/0.69  % (10438)------------------------------
% 2.22/0.69  % (10438)------------------------------
% 2.22/0.69  % (10411)Success in time 0.314 s
%------------------------------------------------------------------------------
