%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT2075+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 639 expanded)
%              Number of leaves         :   16 ( 218 expanded)
%              Depth                    :   14
%              Number of atoms          :  458 (7317 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f95,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f52,f57,f62,f67,f71,f75,f84,f94])).

fof(f94,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_6 ),
    inference(avatar_contradiction_clause,[],[f93])).

fof(f93,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_6 ),
    inference(subsumption_resolution,[],[f92,f88])).

fof(f88,plain,
    ( m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_6 ),
    inference(unit_resulting_resolution,[],[f23,f24,f25,f42,f66,f61,f56,f51,f33])).

fof(f33,plain,(
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
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f9,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r3_waybel_9(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X1,sK3(X0,X1))
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f51,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl5_3
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f56,plain,
    ( v7_waybel_0(sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl5_4
  <=> v7_waybel_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f61,plain,
    ( v4_orders_2(sK1)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl5_5
  <=> v4_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f66,plain,
    ( ~ v2_struct_0(sK1)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl5_6
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f42,plain,
    ( v1_compts_1(sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl5_1
  <=> v1_compts_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f25,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( ( ! [X2] :
            ( ~ r3_waybel_9(sK0,sK1,X2)
            | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
        & l1_waybel_0(sK1,sK0)
        & v7_waybel_0(sK1)
        & v4_orders_2(sK1)
        & ~ v2_struct_0(sK1) )
      | ~ v1_compts_1(sK0) )
    & ( ! [X3] :
          ( ( r3_waybel_9(sK0,X3,sK2(X3))
            & m1_subset_1(sK2(X3),u1_struct_0(sK0)) )
          | ~ l1_waybel_0(X3,sK0)
          | ~ v7_waybel_0(X3)
          | ~ v4_orders_2(X3)
          | v2_struct_0(X3) )
      | v1_compts_1(sK0) )
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f17,f16,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ( ? [X1] :
              ( ! [X2] :
                  ( ~ r3_waybel_9(X0,X1,X2)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              & l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
          | ~ v1_compts_1(X0) )
        & ( ! [X3] :
              ( ? [X4] :
                  ( r3_waybel_9(X0,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
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
                ( ~ r3_waybel_9(sK0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
            & l1_waybel_0(X1,sK0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        | ~ v1_compts_1(sK0) )
      & ( ! [X3] :
            ( ? [X4] :
                ( r3_waybel_9(sK0,X3,X4)
                & m1_subset_1(X4,u1_struct_0(sK0)) )
            | ~ l1_waybel_0(X3,sK0)
            | ~ v7_waybel_0(X3)
            | ~ v4_orders_2(X3)
            | v2_struct_0(X3) )
        | v1_compts_1(sK0) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X1] :
        ( ! [X2] :
            ( ~ r3_waybel_9(sK0,X1,X2)
            | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
        & l1_waybel_0(X1,sK0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1) )
   => ( ! [X2] :
          ( ~ r3_waybel_9(sK0,sK1,X2)
          | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
      & l1_waybel_0(sK1,sK0)
      & v7_waybel_0(sK1)
      & v4_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X3] :
      ( ? [X4] :
          ( r3_waybel_9(sK0,X3,X4)
          & m1_subset_1(X4,u1_struct_0(sK0)) )
     => ( r3_waybel_9(sK0,X3,sK2(X3))
        & m1_subset_1(sK2(X3),u1_struct_0(sK0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ! [X2] :
                ( ~ r3_waybel_9(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        | ~ v1_compts_1(X0) )
      & ( ! [X3] :
            ( ? [X4] :
                ( r3_waybel_9(X0,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ l1_waybel_0(X3,X0)
            | ~ v7_waybel_0(X3)
            | ~ v4_orders_2(X3)
            | v2_struct_0(X3) )
        | v1_compts_1(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ! [X2] :
                ( ~ r3_waybel_9(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        | ~ v1_compts_1(X0) )
      & ( ! [X1] :
            ( ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) )
        | v1_compts_1(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ! [X2] :
                ( ~ r3_waybel_9(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        | ~ v1_compts_1(X0) )
      & ( ! [X1] :
            ( ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) )
        | v1_compts_1(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ( v1_compts_1(X0)
      <~> ! [X1] :
            ( ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ( v1_compts_1(X0)
      <~> ! [X1] :
            ( ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
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
                  ( r3_waybel_9(X0,X1,X2)
                  & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
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

fof(f24,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f23,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f92,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_6 ),
    inference(unit_resulting_resolution,[],[f87,f46])).

fof(f46,plain,
    ( ! [X2] :
        ( ~ r3_waybel_9(sK0,sK1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl5_2
  <=> ! [X2] :
        ( ~ r3_waybel_9(sK0,sK1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f87,plain,
    ( r3_waybel_9(sK0,sK1,sK3(sK0,sK1))
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_6 ),
    inference(unit_resulting_resolution,[],[f23,f24,f25,f42,f66,f61,f56,f51,f34])).

fof(f34,plain,(
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
    inference(cnf_transformation,[],[f20])).

fof(f84,plain,
    ( spl5_1
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(avatar_contradiction_clause,[],[f83])).

fof(f83,plain,
    ( $false
    | spl5_1
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f82,f81])).

fof(f81,plain,
    ( r3_waybel_9(sK0,sK4(sK0),sK2(sK4(sK0)))
    | spl5_1
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f76,f78,f77,f79,f70])).

fof(f70,plain,
    ( ! [X3] :
        ( r3_waybel_9(sK0,X3,sK2(X3))
        | v2_struct_0(X3)
        | ~ v4_orders_2(X3)
        | ~ v7_waybel_0(X3)
        | ~ l1_waybel_0(X3,sK0) )
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl5_7
  <=> ! [X3] :
        ( r3_waybel_9(sK0,X3,sK2(X3))
        | v2_struct_0(X3)
        | ~ v4_orders_2(X3)
        | ~ v7_waybel_0(X3)
        | ~ l1_waybel_0(X3,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f79,plain,
    ( l1_waybel_0(sK4(sK0),sK0)
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f23,f24,f25,f43,f38])).

fof(f38,plain,(
    ! [X0] :
      ( l1_waybel_0(sK4(X0),X0)
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ( ! [X2] :
            ( ~ r3_waybel_9(X0,sK4(X0),X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & l1_waybel_0(sK4(X0),X0)
        & v7_waybel_0(sK4(X0))
        & v4_orders_2(sK4(X0))
        & ~ v2_struct_0(sK4(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f11,f21])).

fof(f21,plain,(
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
            ( ~ r3_waybel_9(X0,sK4(X0),X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & l1_waybel_0(sK4(X0),X0)
        & v7_waybel_0(sK4(X0))
        & v4_orders_2(sK4(X0))
        & ~ v2_struct_0(sK4(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ? [X1] :
          ( ! [X2] :
              ( ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ? [X1] :
          ( ! [X2] :
              ( ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ~ ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ~ r3_waybel_9(X0,X1,X2) ) )
       => v1_compts_1(X0) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,axiom,(
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

fof(f43,plain,
    ( ~ v1_compts_1(sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f77,plain,
    ( v4_orders_2(sK4(sK0))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f23,f24,f25,f43,f36])).

fof(f36,plain,(
    ! [X0] :
      ( v4_orders_2(sK4(X0))
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f78,plain,
    ( v7_waybel_0(sK4(sK0))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f23,f24,f25,f43,f37])).

fof(f37,plain,(
    ! [X0] :
      ( v7_waybel_0(sK4(X0))
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f76,plain,
    ( ~ v2_struct_0(sK4(sK0))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f23,f24,f25,f43,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v2_struct_0(sK4(X0))
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f82,plain,
    ( ~ r3_waybel_9(sK0,sK4(sK0),sK2(sK4(sK0)))
    | spl5_1
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f23,f24,f25,f43,f80,f39])).

fof(f39,plain,(
    ! [X2,X0] :
      ( v1_compts_1(X0)
      | ~ r3_waybel_9(X0,sK4(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f80,plain,
    ( m1_subset_1(sK2(sK4(sK0)),u1_struct_0(sK0))
    | spl5_1
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f76,f78,f77,f79,f74])).

fof(f74,plain,
    ( ! [X3] :
        ( m1_subset_1(sK2(X3),u1_struct_0(sK0))
        | v2_struct_0(X3)
        | ~ v4_orders_2(X3)
        | ~ v7_waybel_0(X3)
        | ~ l1_waybel_0(X3,sK0) )
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl5_8
  <=> ! [X3] :
        ( m1_subset_1(sK2(X3),u1_struct_0(sK0))
        | v2_struct_0(X3)
        | ~ v4_orders_2(X3)
        | ~ v7_waybel_0(X3)
        | ~ l1_waybel_0(X3,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f75,plain,
    ( spl5_1
    | spl5_8 ),
    inference(avatar_split_clause,[],[f26,f73,f41])).

fof(f26,plain,(
    ! [X3] :
      ( m1_subset_1(sK2(X3),u1_struct_0(sK0))
      | ~ l1_waybel_0(X3,sK0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f71,plain,
    ( spl5_1
    | spl5_7 ),
    inference(avatar_split_clause,[],[f27,f69,f41])).

fof(f27,plain,(
    ! [X3] :
      ( r3_waybel_9(sK0,X3,sK2(X3))
      | ~ l1_waybel_0(X3,sK0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f67,plain,
    ( ~ spl5_1
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f28,f64,f41])).

fof(f28,plain,
    ( ~ v2_struct_0(sK1)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f62,plain,
    ( ~ spl5_1
    | spl5_5 ),
    inference(avatar_split_clause,[],[f29,f59,f41])).

fof(f29,plain,
    ( v4_orders_2(sK1)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f57,plain,
    ( ~ spl5_1
    | spl5_4 ),
    inference(avatar_split_clause,[],[f30,f54,f41])).

fof(f30,plain,
    ( v7_waybel_0(sK1)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f52,plain,
    ( ~ spl5_1
    | spl5_3 ),
    inference(avatar_split_clause,[],[f31,f49,f41])).

fof(f31,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f47,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f32,f45,f41])).

fof(f32,plain,(
    ! [X2] :
      ( ~ r3_waybel_9(sK0,sK1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f18])).

%------------------------------------------------------------------------------
