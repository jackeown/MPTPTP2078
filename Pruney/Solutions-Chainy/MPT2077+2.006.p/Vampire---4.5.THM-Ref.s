%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:39 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :  243 ( 801 expanded)
%              Number of leaves         :   31 ( 248 expanded)
%              Depth                    :   69
%              Number of atoms          : 1860 (7018 expanded)
%              Number of equality atoms :   18 (  23 expanded)
%              Maximal formula depth    :   22 (   9 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1010,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f138,f139,f1003,f1009])).

fof(f1009,plain,
    ( ~ spl13_1
    | spl13_2 ),
    inference(avatar_contradiction_clause,[],[f1008])).

fof(f1008,plain,
    ( $false
    | ~ spl13_1
    | spl13_2 ),
    inference(subsumption_resolution,[],[f1007,f132])).

fof(f132,plain,
    ( v1_compts_1(sK7)
    | ~ spl13_1 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl13_1
  <=> v1_compts_1(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f1007,plain,
    ( ~ v1_compts_1(sK7)
    | spl13_2 ),
    inference(subsumption_resolution,[],[f1006,f87])).

fof(f87,plain,(
    v2_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,
    ( ( ~ sP0(sK7)
      | ~ v1_compts_1(sK7) )
    & ( sP0(sK7)
      | v1_compts_1(sK7) )
    & l1_pre_topc(sK7)
    & v2_pre_topc(sK7)
    & ~ v2_struct_0(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f57,f58])).

fof(f58,plain,
    ( ? [X0] :
        ( ( ~ sP0(X0)
          | ~ v1_compts_1(X0) )
        & ( sP0(X0)
          | v1_compts_1(X0) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ( ~ sP0(sK7)
        | ~ v1_compts_1(sK7) )
      & ( sP0(sK7)
        | v1_compts_1(sK7) )
      & l1_pre_topc(sK7)
      & v2_pre_topc(sK7)
      & ~ v2_struct_0(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ? [X0] :
      ( ( ~ sP0(X0)
        | ~ v1_compts_1(X0) )
      & ( sP0(X0)
        | v1_compts_1(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ? [X0] :
      ( ( ~ sP0(X0)
        | ~ v1_compts_1(X0) )
      & ( sP0(X0)
        | v1_compts_1(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ? [X0] :
      ( ( v1_compts_1(X0)
      <~> sP0(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f19,f42])).

fof(f42,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1] :
          ( ? [X2] :
              ( v3_yellow_6(X2,X0)
              & m2_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

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

fof(f1006,plain,
    ( ~ v2_pre_topc(sK7)
    | ~ v1_compts_1(sK7)
    | spl13_2 ),
    inference(subsumption_resolution,[],[f1005,f88])).

fof(f88,plain,(
    l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f59])).

fof(f1005,plain,
    ( ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(sK7)
    | ~ v1_compts_1(sK7)
    | spl13_2 ),
    inference(subsumption_resolution,[],[f1004,f86])).

fof(f86,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f59])).

fof(f1004,plain,
    ( v2_struct_0(sK7)
    | ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(sK7)
    | ~ v1_compts_1(sK7)
    | spl13_2 ),
    inference(resolution,[],[f137,f360])).

fof(f360,plain,(
    ! [X5] :
      ( sP0(X5)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | ~ v1_compts_1(X5) ) ),
    inference(subsumption_resolution,[],[f359,f81])).

fof(f81,plain,(
    ! [X0] :
      ( ~ v2_struct_0(sK5(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( ! [X2] :
              ( ~ v3_yellow_6(X2,X0)
              | ~ m2_yellow_6(X2,X0,sK5(X0)) )
          & l1_waybel_0(sK5(X0),X0)
          & v7_waybel_0(sK5(X0))
          & v4_orders_2(sK5(X0))
          & ~ v2_struct_0(sK5(X0)) ) )
      & ( ! [X3] :
            ( ( v3_yellow_6(sK6(X0,X3),X0)
              & m2_yellow_6(sK6(X0,X3),X0,X3) )
            | ~ l1_waybel_0(X3,X0)
            | ~ v7_waybel_0(X3)
            | ~ v4_orders_2(X3)
            | v2_struct_0(X3) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f52,f54,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ v3_yellow_6(X2,X0)
              | ~ m2_yellow_6(X2,X0,X1) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
     => ( ! [X2] :
            ( ~ v3_yellow_6(X2,X0)
            | ~ m2_yellow_6(X2,X0,sK5(X0)) )
        & l1_waybel_0(sK5(X0),X0)
        & v7_waybel_0(sK5(X0))
        & v4_orders_2(sK5(X0))
        & ~ v2_struct_0(sK5(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( v3_yellow_6(X4,X0)
          & m2_yellow_6(X4,X0,X3) )
     => ( v3_yellow_6(sK6(X0,X3),X0)
        & m2_yellow_6(sK6(X0,X3),X0,X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ! [X2] :
                ( ~ v3_yellow_6(X2,X0)
                | ~ m2_yellow_6(X2,X0,X1) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) ) )
      & ( ! [X3] :
            ( ? [X4] :
                ( v3_yellow_6(X4,X0)
                & m2_yellow_6(X4,X0,X3) )
            | ~ l1_waybel_0(X3,X0)
            | ~ v7_waybel_0(X3)
            | ~ v4_orders_2(X3)
            | v2_struct_0(X3) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ! [X2] :
                ( ~ v3_yellow_6(X2,X0)
                | ~ m2_yellow_6(X2,X0,X1) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) ) )
      & ( ! [X1] :
            ( ? [X2] :
                ( v3_yellow_6(X2,X0)
                & m2_yellow_6(X2,X0,X1) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f359,plain,(
    ! [X5] :
      ( ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X5)
      | sP0(X5)
      | v2_struct_0(sK5(X5))
      | ~ v1_compts_1(X5) ) ),
    inference(subsumption_resolution,[],[f358,f82])).

fof(f82,plain,(
    ! [X0] :
      ( v4_orders_2(sK5(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f358,plain,(
    ! [X5] :
      ( ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X5)
      | sP0(X5)
      | ~ v4_orders_2(sK5(X5))
      | v2_struct_0(sK5(X5))
      | ~ v1_compts_1(X5) ) ),
    inference(subsumption_resolution,[],[f357,f83])).

fof(f83,plain,(
    ! [X0] :
      ( v7_waybel_0(sK5(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f357,plain,(
    ! [X5] :
      ( ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X5)
      | sP0(X5)
      | ~ v7_waybel_0(sK5(X5))
      | ~ v4_orders_2(sK5(X5))
      | v2_struct_0(sK5(X5))
      | ~ v1_compts_1(X5) ) ),
    inference(subsumption_resolution,[],[f356,f84])).

fof(f84,plain,(
    ! [X0] :
      ( l1_waybel_0(sK5(X0),X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f356,plain,(
    ! [X5] :
      ( ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X5)
      | sP0(X5)
      | ~ l1_waybel_0(sK5(X5),X5)
      | ~ v7_waybel_0(sK5(X5))
      | ~ v4_orders_2(sK5(X5))
      | v2_struct_0(sK5(X5))
      | ~ v1_compts_1(X5) ) ),
    inference(subsumption_resolution,[],[f349,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK8(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r3_waybel_9(X0,X1,sK8(X0,X1))
            & m1_subset_1(sK8(X0,X1),u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f22,f60])).

fof(f60,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r3_waybel_9(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X1,sK8(X0,X1))
        & m1_subset_1(sK8(X0,X1),u1_struct_0(X0)) ) ) ),
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

fof(f349,plain,(
    ! [X5] :
      ( ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X5)
      | ~ m1_subset_1(sK8(X5,sK5(X5)),u1_struct_0(X5))
      | sP0(X5)
      | ~ l1_waybel_0(sK5(X5),X5)
      | ~ v7_waybel_0(sK5(X5))
      | ~ v4_orders_2(sK5(X5))
      | v2_struct_0(sK5(X5))
      | ~ v1_compts_1(X5) ) ),
    inference(duplicate_literal_removal,[],[f345])).

fof(f345,plain,(
    ! [X5] :
      ( ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X5)
      | ~ m1_subset_1(sK8(X5,sK5(X5)),u1_struct_0(X5))
      | sP0(X5)
      | ~ l1_waybel_0(sK5(X5),X5)
      | ~ v7_waybel_0(sK5(X5))
      | ~ v4_orders_2(sK5(X5))
      | v2_struct_0(sK5(X5))
      | ~ v1_compts_1(X5)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5) ) ),
    inference(resolution,[],[f342,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( r3_waybel_9(X0,X1,sK8(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f342,plain,(
    ! [X0,X1] :
      ( ~ r3_waybel_9(X0,sK5(X0),X1)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP0(X0) ) ),
    inference(subsumption_resolution,[],[f341,f81])).

fof(f341,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK5(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ r3_waybel_9(X0,sK5(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP0(X0) ) ),
    inference(subsumption_resolution,[],[f340,f82])).

fof(f340,plain,(
    ! [X0,X1] :
      ( ~ v4_orders_2(sK5(X0))
      | v2_struct_0(sK5(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ r3_waybel_9(X0,sK5(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP0(X0) ) ),
    inference(subsumption_resolution,[],[f339,f83])).

fof(f339,plain,(
    ! [X0,X1] :
      ( ~ v7_waybel_0(sK5(X0))
      | ~ v4_orders_2(sK5(X0))
      | v2_struct_0(sK5(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ r3_waybel_9(X0,sK5(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP0(X0) ) ),
    inference(subsumption_resolution,[],[f338,f84])).

fof(f338,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(sK5(X0),X0)
      | ~ v7_waybel_0(sK5(X0))
      | ~ v4_orders_2(sK5(X0))
      | v2_struct_0(sK5(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ r3_waybel_9(X0,sK5(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP0(X0) ) ),
    inference(duplicate_literal_removal,[],[f337])).

fof(f337,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(sK5(X0),X0)
      | ~ v7_waybel_0(sK5(X0))
      | ~ v4_orders_2(sK5(X0))
      | v2_struct_0(sK5(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ r3_waybel_9(X0,sK5(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ r3_waybel_9(X0,sK5(X0),X1)
      | sP0(X0) ) ),
    inference(resolution,[],[f305,f188])).

fof(f188,plain,(
    ! [X0,X1] :
      ( ~ v3_yellow_6(sK11(X0,sK5(X0),X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ r3_waybel_9(X0,sK5(X0),X1)
      | sP0(X0) ) ),
    inference(subsumption_resolution,[],[f187,f81])).

fof(f187,plain,(
    ! [X0,X1] :
      ( ~ r3_waybel_9(X0,sK5(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(sK5(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v3_yellow_6(sK11(X0,sK5(X0),X1),X0)
      | sP0(X0) ) ),
    inference(subsumption_resolution,[],[f186,f82])).

fof(f186,plain,(
    ! [X0,X1] :
      ( ~ r3_waybel_9(X0,sK5(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v4_orders_2(sK5(X0))
      | v2_struct_0(sK5(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v3_yellow_6(sK11(X0,sK5(X0),X1),X0)
      | sP0(X0) ) ),
    inference(subsumption_resolution,[],[f185,f83])).

fof(f185,plain,(
    ! [X0,X1] :
      ( ~ r3_waybel_9(X0,sK5(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v7_waybel_0(sK5(X0))
      | ~ v4_orders_2(sK5(X0))
      | v2_struct_0(sK5(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v3_yellow_6(sK11(X0,sK5(X0),X1),X0)
      | sP0(X0) ) ),
    inference(subsumption_resolution,[],[f182,f84])).

fof(f182,plain,(
    ! [X0,X1] :
      ( ~ r3_waybel_9(X0,sK5(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_waybel_0(sK5(X0),X0)
      | ~ v7_waybel_0(sK5(X0))
      | ~ v4_orders_2(sK5(X0))
      | v2_struct_0(sK5(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v3_yellow_6(sK11(X0,sK5(X0),X1),X0)
      | sP0(X0) ) ),
    inference(resolution,[],[f110,f85])).

fof(f85,plain,(
    ! [X2,X0] :
      ( ~ m2_yellow_6(X2,X0,sK5(X0))
      | ~ v3_yellow_6(X2,X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( m2_yellow_6(sK11(X0,X1,X2),X0,X1)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,sK11(X0,X1,X2)))
                & m2_yellow_6(sK11(X0,X1,X2),X0,X1) )
              | ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f30,f69])).

fof(f69,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X2,k10_yellow_6(X0,X3))
          & m2_yellow_6(X3,X0,X1) )
     => ( r2_hidden(X2,k10_yellow_6(X0,sK11(X0,X1,X2)))
        & m2_yellow_6(sK11(X0,X1,X2),X0,X1) ) ) ),
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

fof(f305,plain,(
    ! [X2,X0,X1] :
      ( v3_yellow_6(sK11(X0,X1,X2),X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f304,f206])).

fof(f206,plain,(
    ! [X10,X11,X9] :
      ( ~ v2_struct_0(sK11(X10,X11,X9))
      | ~ l1_waybel_0(X11,X10)
      | ~ v7_waybel_0(X11)
      | ~ v4_orders_2(X11)
      | v2_struct_0(X11)
      | ~ l1_pre_topc(X10)
      | ~ v2_pre_topc(X10)
      | v2_struct_0(X10)
      | ~ r3_waybel_9(X10,X11,X9)
      | ~ m1_subset_1(X9,u1_struct_0(X10)) ) ),
    inference(resolution,[],[f189,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ sP4(X0,X1)
      | ~ v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1) )
      | ~ sP4(X0,X1) ) ),
    inference(rectify,[],[f75])).

fof(f75,plain,(
    ! [X0,X2] :
      ( ( l1_waybel_0(X2,X0)
        & v7_waybel_0(X2)
        & v4_orders_2(X2)
        & ~ v2_struct_0(X2) )
      | ~ sP4(X0,X2) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X2] :
      ( ( l1_waybel_0(X2,X0)
        & v7_waybel_0(X2)
        & v4_orders_2(X2)
        & ~ v2_struct_0(X2) )
      | ~ sP4(X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f189,plain,(
    ! [X4,X2,X3] :
      ( sP4(X2,sK11(X2,X3,X4))
      | ~ m1_subset_1(X4,u1_struct_0(X2))
      | ~ l1_waybel_0(X3,X2)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ r3_waybel_9(X2,X3,X4) ) ),
    inference(subsumption_resolution,[],[f184,f93])).

fof(f93,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f184,plain,(
    ! [X4,X2,X3] :
      ( ~ r3_waybel_9(X2,X3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X2))
      | ~ l1_waybel_0(X3,X2)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | sP4(X2,sK11(X2,X3,X4))
      | ~ l1_struct_0(X2) ) ),
    inference(duplicate_literal_removal,[],[f183])).

fof(f183,plain,(
    ! [X4,X2,X3] :
      ( ~ r3_waybel_9(X2,X3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X2))
      | ~ l1_waybel_0(X3,X2)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | sP4(X2,sK11(X2,X3,X4))
      | ~ l1_waybel_0(X3,X2)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | ~ l1_struct_0(X2)
      | v2_struct_0(X2) ) ),
    inference(resolution,[],[f110,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_yellow_6(X2,X0,X1)
      | sP4(X0,X2)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( sP4(X0,X2)
          | ~ m2_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f36,f49])).

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

fof(f304,plain,(
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
      | v3_yellow_6(sK11(X0,X1,X2),X0)
      | v2_struct_0(sK11(X0,X1,X2)) ) ),
    inference(subsumption_resolution,[],[f303,f205])).

fof(f205,plain,(
    ! [X6,X8,X7] :
      ( v4_orders_2(sK11(X7,X8,X6))
      | ~ l1_waybel_0(X8,X7)
      | ~ v7_waybel_0(X8)
      | ~ v4_orders_2(X8)
      | v2_struct_0(X8)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7)
      | ~ r3_waybel_9(X7,X8,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X7)) ) ),
    inference(resolution,[],[f189,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ sP4(X0,X1)
      | v4_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f303,plain,(
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
      | v3_yellow_6(sK11(X0,X1,X2),X0)
      | ~ v4_orders_2(sK11(X0,X1,X2))
      | v2_struct_0(sK11(X0,X1,X2)) ) ),
    inference(subsumption_resolution,[],[f302,f204])).

fof(f204,plain,(
    ! [X4,X5,X3] :
      ( v7_waybel_0(sK11(X4,X5,X3))
      | ~ l1_waybel_0(X5,X4)
      | ~ v7_waybel_0(X5)
      | ~ v4_orders_2(X5)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | ~ r3_waybel_9(X4,X5,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X4)) ) ),
    inference(resolution,[],[f189,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ sP4(X0,X1)
      | v7_waybel_0(X1) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f302,plain,(
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
      | v3_yellow_6(sK11(X0,X1,X2),X0)
      | ~ v7_waybel_0(sK11(X0,X1,X2))
      | ~ v4_orders_2(sK11(X0,X1,X2))
      | v2_struct_0(sK11(X0,X1,X2)) ) ),
    inference(subsumption_resolution,[],[f301,f203])).

fof(f203,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(sK11(X1,X2,X0),X1)
      | ~ l1_waybel_0(X2,X1)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ r3_waybel_9(X1,X2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f189,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ sP4(X0,X1)
      | l1_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f301,plain,(
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
      | v3_yellow_6(sK11(X0,X1,X2),X0)
      | ~ l1_waybel_0(sK11(X0,X1,X2),X0)
      | ~ v7_waybel_0(sK11(X0,X1,X2))
      | ~ v4_orders_2(sK11(X0,X1,X2))
      | v2_struct_0(sK11(X0,X1,X2)) ) ),
    inference(subsumption_resolution,[],[f300,f91])).

fof(f91,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f300,plain,(
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
      | v3_yellow_6(sK11(X0,X1,X2),X0)
      | ~ l1_waybel_0(sK11(X0,X1,X2),X0)
      | ~ v7_waybel_0(sK11(X0,X1,X2))
      | ~ v4_orders_2(sK11(X0,X1,X2))
      | v2_struct_0(sK11(X0,X1,X2)) ) ),
    inference(duplicate_literal_removal,[],[f299])).

fof(f299,plain,(
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
      | v3_yellow_6(sK11(X0,X1,X2),X0)
      | ~ l1_waybel_0(sK11(X0,X1,X2),X0)
      | ~ v7_waybel_0(sK11(X0,X1,X2))
      | ~ v4_orders_2(sK11(X0,X1,X2))
      | v2_struct_0(sK11(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f209,f108])).

fof(f108,plain,(
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
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
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

fof(f209,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_tarski(k10_yellow_6(X6,sK11(X6,X7,X8)),X8)
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ l1_waybel_0(X7,X6)
      | ~ v7_waybel_0(X7)
      | ~ v4_orders_2(X7)
      | v2_struct_0(X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | ~ r3_waybel_9(X6,X7,X8) ) ),
    inference(resolution,[],[f111,f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k10_yellow_6(X0,sK11(X0,X1,X2)))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f137,plain,
    ( ~ sP0(sK7)
    | spl13_2 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl13_2
  <=> sP0(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f1003,plain,
    ( spl13_1
    | ~ spl13_2 ),
    inference(avatar_contradiction_clause,[],[f1002])).

fof(f1002,plain,
    ( $false
    | spl13_1
    | ~ spl13_2 ),
    inference(subsumption_resolution,[],[f1001,f133])).

fof(f133,plain,
    ( ~ v1_compts_1(sK7)
    | spl13_1 ),
    inference(avatar_component_clause,[],[f131])).

fof(f1001,plain,
    ( v1_compts_1(sK7)
    | ~ spl13_2 ),
    inference(subsumption_resolution,[],[f1000,f88])).

fof(f1000,plain,
    ( ~ l1_pre_topc(sK7)
    | v1_compts_1(sK7)
    | ~ spl13_2 ),
    inference(subsumption_resolution,[],[f999,f87])).

fof(f999,plain,
    ( ~ v2_pre_topc(sK7)
    | ~ l1_pre_topc(sK7)
    | v1_compts_1(sK7)
    | ~ spl13_2 ),
    inference(subsumption_resolution,[],[f996,f86])).

fof(f996,plain,
    ( v2_struct_0(sK7)
    | ~ v2_pre_topc(sK7)
    | ~ l1_pre_topc(sK7)
    | v1_compts_1(sK7)
    | ~ spl13_2 ),
    inference(resolution,[],[f995,f136])).

fof(f136,plain,
    ( sP0(sK7)
    | ~ spl13_2 ),
    inference(avatar_component_clause,[],[f135])).

fof(f995,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v1_compts_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f994])).

fof(f994,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP0(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v1_compts_1(X0) ) ),
    inference(resolution,[],[f993,f141])).

fof(f141,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v1_compts_1(X0) ) ),
    inference(resolution,[],[f106,f97])).

fof(f97,plain,(
    ! [X0] :
      ( ~ sP2(X0)
      | ~ sP1(X0)
      | v1_compts_1(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ~ sP1(X0) )
        & ( sP1(X0)
          | ~ v1_compts_1(X0) ) )
      | ~ sP2(X0) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> sP1(X0) )
      | ~ sP2(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f106,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f24,f45,f44])).

fof(f44,plain,(
    ! [X0] :
      ( sP1(X0)
    <=> ! [X1] :
          ( ? [X2] :
              ( r3_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ r2_hidden(X1,k6_yellow_6(X0))
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f993,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f992,f103])).

fof(f103,plain,(
    ! [X0] :
      ( l1_waybel_0(sK9(X0),X0)
      | sP1(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ( sP1(X0)
        | ( ! [X2] :
              ( ~ r3_waybel_9(X0,sK9(X0),X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & r2_hidden(sK9(X0),k6_yellow_6(X0))
          & l1_waybel_0(sK9(X0),X0)
          & v7_waybel_0(sK9(X0))
          & v4_orders_2(sK9(X0))
          & ~ v2_struct_0(sK9(X0)) ) )
      & ( ! [X3] :
            ( ( r3_waybel_9(X0,X3,sK10(X0,X3))
              & m1_subset_1(sK10(X0,X3),u1_struct_0(X0)) )
            | ~ r2_hidden(X3,k6_yellow_6(X0))
            | ~ l1_waybel_0(X3,X0)
            | ~ v7_waybel_0(X3)
            | ~ v4_orders_2(X3)
            | v2_struct_0(X3) )
        | ~ sP1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f64,f66,f65])).

fof(f65,plain,(
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
            ( ~ r3_waybel_9(X0,sK9(X0),X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & r2_hidden(sK9(X0),k6_yellow_6(X0))
        & l1_waybel_0(sK9(X0),X0)
        & v7_waybel_0(sK9(X0))
        & v4_orders_2(sK9(X0))
        & ~ v2_struct_0(sK9(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( r3_waybel_9(X0,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X3,sK10(X0,X3))
        & m1_subset_1(sK10(X0,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0] :
      ( ( sP1(X0)
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
        | ~ sP1(X0) ) ) ),
    inference(rectify,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ( sP1(X0)
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
        | ~ sP1(X0) ) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f992,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP0(X0)
      | sP1(X0)
      | ~ l1_waybel_0(sK9(X0),X0) ) ),
    inference(subsumption_resolution,[],[f991,f100])).

fof(f100,plain,(
    ! [X0] :
      ( ~ v2_struct_0(sK9(X0))
      | sP1(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f991,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP0(X0)
      | sP1(X0)
      | v2_struct_0(sK9(X0))
      | ~ l1_waybel_0(sK9(X0),X0) ) ),
    inference(subsumption_resolution,[],[f990,f101])).

fof(f101,plain,(
    ! [X0] :
      ( v4_orders_2(sK9(X0))
      | sP1(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f990,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP0(X0)
      | sP1(X0)
      | ~ v4_orders_2(sK9(X0))
      | v2_struct_0(sK9(X0))
      | ~ l1_waybel_0(sK9(X0),X0) ) ),
    inference(subsumption_resolution,[],[f989,f102])).

fof(f102,plain,(
    ! [X0] :
      ( v7_waybel_0(sK9(X0))
      | sP1(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f989,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP0(X0)
      | sP1(X0)
      | ~ v7_waybel_0(sK9(X0))
      | ~ v4_orders_2(sK9(X0))
      | v2_struct_0(sK9(X0))
      | ~ l1_waybel_0(sK9(X0),X0) ) ),
    inference(subsumption_resolution,[],[f988,f93])).

fof(f988,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP0(X0)
      | sP1(X0)
      | ~ v7_waybel_0(sK9(X0))
      | ~ v4_orders_2(sK9(X0))
      | v2_struct_0(sK9(X0))
      | ~ l1_struct_0(X0)
      | ~ l1_waybel_0(sK9(X0),X0) ) ),
    inference(duplicate_literal_removal,[],[f987])).

fof(f987,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP0(X0)
      | sP1(X0)
      | ~ v7_waybel_0(sK9(X0))
      | ~ v4_orders_2(sK9(X0))
      | v2_struct_0(sK9(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | ~ sP0(X0)
      | ~ l1_waybel_0(sK9(X0),X0) ) ),
    inference(resolution,[],[f986,f166])).

fof(f166,plain,(
    ! [X6,X7] :
      ( ~ v2_struct_0(sK6(X7,X6))
      | ~ v7_waybel_0(X6)
      | ~ v4_orders_2(X6)
      | v2_struct_0(X6)
      | ~ l1_struct_0(X7)
      | v2_struct_0(X7)
      | ~ sP0(X7)
      | ~ l1_waybel_0(X6,X7) ) ),
    inference(resolution,[],[f162,f117])).

fof(f162,plain,(
    ! [X0,X1] :
      ( sP4(X0,sK6(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | ~ sP0(X0) ) ),
    inference(duplicate_literal_removal,[],[f161])).

fof(f161,plain,(
    ! [X0,X1] :
      ( sP4(X0,sK6(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ sP0(X0) ) ),
    inference(resolution,[],[f121,f79])).

fof(f79,plain,(
    ! [X0,X3] :
      ( m2_yellow_6(sK6(X0,X3),X0,X3)
      | ~ l1_waybel_0(X3,X0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f986,plain,(
    ! [X0] :
      ( v2_struct_0(sK6(X0,sK9(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP0(X0)
      | sP1(X0) ) ),
    inference(subsumption_resolution,[],[f985,f103])).

fof(f985,plain,(
    ! [X0] :
      ( v2_struct_0(sK6(X0,sK9(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP0(X0)
      | sP1(X0)
      | ~ l1_waybel_0(sK9(X0),X0) ) ),
    inference(subsumption_resolution,[],[f984,f100])).

fof(f984,plain,(
    ! [X0] :
      ( v2_struct_0(sK6(X0,sK9(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP0(X0)
      | sP1(X0)
      | v2_struct_0(sK9(X0))
      | ~ l1_waybel_0(sK9(X0),X0) ) ),
    inference(subsumption_resolution,[],[f983,f101])).

fof(f983,plain,(
    ! [X0] :
      ( v2_struct_0(sK6(X0,sK9(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP0(X0)
      | sP1(X0)
      | ~ v4_orders_2(sK9(X0))
      | v2_struct_0(sK9(X0))
      | ~ l1_waybel_0(sK9(X0),X0) ) ),
    inference(subsumption_resolution,[],[f982,f102])).

fof(f982,plain,(
    ! [X0] :
      ( v2_struct_0(sK6(X0,sK9(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP0(X0)
      | sP1(X0)
      | ~ v7_waybel_0(sK9(X0))
      | ~ v4_orders_2(sK9(X0))
      | v2_struct_0(sK9(X0))
      | ~ l1_waybel_0(sK9(X0),X0) ) ),
    inference(subsumption_resolution,[],[f981,f93])).

fof(f981,plain,(
    ! [X0] :
      ( v2_struct_0(sK6(X0,sK9(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP0(X0)
      | sP1(X0)
      | ~ v7_waybel_0(sK9(X0))
      | ~ v4_orders_2(sK9(X0))
      | v2_struct_0(sK9(X0))
      | ~ l1_struct_0(X0)
      | ~ l1_waybel_0(sK9(X0),X0) ) ),
    inference(duplicate_literal_removal,[],[f980])).

fof(f980,plain,(
    ! [X0] :
      ( v2_struct_0(sK6(X0,sK9(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP0(X0)
      | sP1(X0)
      | ~ v7_waybel_0(sK9(X0))
      | ~ v4_orders_2(sK9(X0))
      | v2_struct_0(sK9(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | ~ sP0(X0)
      | ~ l1_waybel_0(sK9(X0),X0) ) ),
    inference(resolution,[],[f979,f165])).

fof(f165,plain,(
    ! [X4,X5] :
      ( v4_orders_2(sK6(X5,X4))
      | ~ v7_waybel_0(X4)
      | ~ v4_orders_2(X4)
      | v2_struct_0(X4)
      | ~ l1_struct_0(X5)
      | v2_struct_0(X5)
      | ~ sP0(X5)
      | ~ l1_waybel_0(X4,X5) ) ),
    inference(resolution,[],[f162,f118])).

fof(f979,plain,(
    ! [X0] :
      ( ~ v4_orders_2(sK6(X0,sK9(X0)))
      | v2_struct_0(sK6(X0,sK9(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP0(X0)
      | sP1(X0) ) ),
    inference(subsumption_resolution,[],[f978,f103])).

fof(f978,plain,(
    ! [X0] :
      ( ~ v4_orders_2(sK6(X0,sK9(X0)))
      | v2_struct_0(sK6(X0,sK9(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP0(X0)
      | sP1(X0)
      | ~ l1_waybel_0(sK9(X0),X0) ) ),
    inference(subsumption_resolution,[],[f977,f100])).

fof(f977,plain,(
    ! [X0] :
      ( ~ v4_orders_2(sK6(X0,sK9(X0)))
      | v2_struct_0(sK6(X0,sK9(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP0(X0)
      | sP1(X0)
      | v2_struct_0(sK9(X0))
      | ~ l1_waybel_0(sK9(X0),X0) ) ),
    inference(subsumption_resolution,[],[f976,f101])).

fof(f976,plain,(
    ! [X0] :
      ( ~ v4_orders_2(sK6(X0,sK9(X0)))
      | v2_struct_0(sK6(X0,sK9(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP0(X0)
      | sP1(X0)
      | ~ v4_orders_2(sK9(X0))
      | v2_struct_0(sK9(X0))
      | ~ l1_waybel_0(sK9(X0),X0) ) ),
    inference(subsumption_resolution,[],[f975,f102])).

fof(f975,plain,(
    ! [X0] :
      ( ~ v4_orders_2(sK6(X0,sK9(X0)))
      | v2_struct_0(sK6(X0,sK9(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP0(X0)
      | sP1(X0)
      | ~ v7_waybel_0(sK9(X0))
      | ~ v4_orders_2(sK9(X0))
      | v2_struct_0(sK9(X0))
      | ~ l1_waybel_0(sK9(X0),X0) ) ),
    inference(subsumption_resolution,[],[f974,f93])).

fof(f974,plain,(
    ! [X0] :
      ( ~ v4_orders_2(sK6(X0,sK9(X0)))
      | v2_struct_0(sK6(X0,sK9(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP0(X0)
      | sP1(X0)
      | ~ v7_waybel_0(sK9(X0))
      | ~ v4_orders_2(sK9(X0))
      | v2_struct_0(sK9(X0))
      | ~ l1_struct_0(X0)
      | ~ l1_waybel_0(sK9(X0),X0) ) ),
    inference(duplicate_literal_removal,[],[f973])).

fof(f973,plain,(
    ! [X0] :
      ( ~ v4_orders_2(sK6(X0,sK9(X0)))
      | v2_struct_0(sK6(X0,sK9(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP0(X0)
      | sP1(X0)
      | ~ v7_waybel_0(sK9(X0))
      | ~ v4_orders_2(sK9(X0))
      | v2_struct_0(sK9(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | ~ sP0(X0)
      | ~ l1_waybel_0(sK9(X0),X0) ) ),
    inference(resolution,[],[f972,f164])).

fof(f164,plain,(
    ! [X2,X3] :
      ( v7_waybel_0(sK6(X3,X2))
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X3)
      | v2_struct_0(X3)
      | ~ sP0(X3)
      | ~ l1_waybel_0(X2,X3) ) ),
    inference(resolution,[],[f162,f119])).

fof(f972,plain,(
    ! [X0] :
      ( ~ v7_waybel_0(sK6(X0,sK9(X0)))
      | ~ v4_orders_2(sK6(X0,sK9(X0)))
      | v2_struct_0(sK6(X0,sK9(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP0(X0)
      | sP1(X0) ) ),
    inference(subsumption_resolution,[],[f971,f103])).

fof(f971,plain,(
    ! [X0] :
      ( ~ v7_waybel_0(sK6(X0,sK9(X0)))
      | ~ v4_orders_2(sK6(X0,sK9(X0)))
      | v2_struct_0(sK6(X0,sK9(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP0(X0)
      | sP1(X0)
      | ~ l1_waybel_0(sK9(X0),X0) ) ),
    inference(subsumption_resolution,[],[f970,f100])).

fof(f970,plain,(
    ! [X0] :
      ( ~ v7_waybel_0(sK6(X0,sK9(X0)))
      | ~ v4_orders_2(sK6(X0,sK9(X0)))
      | v2_struct_0(sK6(X0,sK9(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP0(X0)
      | sP1(X0)
      | v2_struct_0(sK9(X0))
      | ~ l1_waybel_0(sK9(X0),X0) ) ),
    inference(subsumption_resolution,[],[f969,f101])).

fof(f969,plain,(
    ! [X0] :
      ( ~ v7_waybel_0(sK6(X0,sK9(X0)))
      | ~ v4_orders_2(sK6(X0,sK9(X0)))
      | v2_struct_0(sK6(X0,sK9(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP0(X0)
      | sP1(X0)
      | ~ v4_orders_2(sK9(X0))
      | v2_struct_0(sK9(X0))
      | ~ l1_waybel_0(sK9(X0),X0) ) ),
    inference(subsumption_resolution,[],[f968,f102])).

fof(f968,plain,(
    ! [X0] :
      ( ~ v7_waybel_0(sK6(X0,sK9(X0)))
      | ~ v4_orders_2(sK6(X0,sK9(X0)))
      | v2_struct_0(sK6(X0,sK9(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP0(X0)
      | sP1(X0)
      | ~ v7_waybel_0(sK9(X0))
      | ~ v4_orders_2(sK9(X0))
      | v2_struct_0(sK9(X0))
      | ~ l1_waybel_0(sK9(X0),X0) ) ),
    inference(subsumption_resolution,[],[f967,f93])).

fof(f967,plain,(
    ! [X0] :
      ( ~ v7_waybel_0(sK6(X0,sK9(X0)))
      | ~ v4_orders_2(sK6(X0,sK9(X0)))
      | v2_struct_0(sK6(X0,sK9(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP0(X0)
      | sP1(X0)
      | ~ v7_waybel_0(sK9(X0))
      | ~ v4_orders_2(sK9(X0))
      | v2_struct_0(sK9(X0))
      | ~ l1_struct_0(X0)
      | ~ l1_waybel_0(sK9(X0),X0) ) ),
    inference(duplicate_literal_removal,[],[f966])).

fof(f966,plain,(
    ! [X0] :
      ( ~ v7_waybel_0(sK6(X0,sK9(X0)))
      | ~ v4_orders_2(sK6(X0,sK9(X0)))
      | v2_struct_0(sK6(X0,sK9(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP0(X0)
      | sP1(X0)
      | ~ v7_waybel_0(sK9(X0))
      | ~ v4_orders_2(sK9(X0))
      | v2_struct_0(sK9(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | ~ sP0(X0)
      | ~ l1_waybel_0(sK9(X0),X0) ) ),
    inference(resolution,[],[f965,f163])).

fof(f163,plain,(
    ! [X0,X1] :
      ( l1_waybel_0(sK6(X1,X0),X1)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ sP0(X1)
      | ~ l1_waybel_0(X0,X1) ) ),
    inference(resolution,[],[f162,f120])).

fof(f965,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(sK6(X0,sK9(X0)),X0)
      | ~ v7_waybel_0(sK6(X0,sK9(X0)))
      | ~ v4_orders_2(sK6(X0,sK9(X0)))
      | v2_struct_0(sK6(X0,sK9(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP0(X0)
      | sP1(X0) ) ),
    inference(subsumption_resolution,[],[f964,f100])).

fof(f964,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(sK6(X0,sK9(X0)),X0)
      | ~ v7_waybel_0(sK6(X0,sK9(X0)))
      | ~ v4_orders_2(sK6(X0,sK9(X0)))
      | v2_struct_0(sK6(X0,sK9(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP0(X0)
      | sP1(X0)
      | v2_struct_0(sK9(X0)) ) ),
    inference(subsumption_resolution,[],[f963,f101])).

fof(f963,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(sK6(X0,sK9(X0)),X0)
      | ~ v7_waybel_0(sK6(X0,sK9(X0)))
      | ~ v4_orders_2(sK6(X0,sK9(X0)))
      | v2_struct_0(sK6(X0,sK9(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP0(X0)
      | sP1(X0)
      | ~ v4_orders_2(sK9(X0))
      | v2_struct_0(sK9(X0)) ) ),
    inference(subsumption_resolution,[],[f962,f102])).

fof(f962,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(sK6(X0,sK9(X0)),X0)
      | ~ v7_waybel_0(sK6(X0,sK9(X0)))
      | ~ v4_orders_2(sK6(X0,sK9(X0)))
      | v2_struct_0(sK6(X0,sK9(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP0(X0)
      | sP1(X0)
      | ~ v7_waybel_0(sK9(X0))
      | ~ v4_orders_2(sK9(X0))
      | v2_struct_0(sK9(X0)) ) ),
    inference(subsumption_resolution,[],[f961,f103])).

fof(f961,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(sK6(X0,sK9(X0)),X0)
      | ~ v7_waybel_0(sK6(X0,sK9(X0)))
      | ~ v4_orders_2(sK6(X0,sK9(X0)))
      | v2_struct_0(sK6(X0,sK9(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP0(X0)
      | sP1(X0)
      | ~ l1_waybel_0(sK9(X0),X0)
      | ~ v7_waybel_0(sK9(X0))
      | ~ v4_orders_2(sK9(X0))
      | v2_struct_0(sK9(X0)) ) ),
    inference(duplicate_literal_removal,[],[f960])).

fof(f960,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(sK6(X0,sK9(X0)),X0)
      | ~ v7_waybel_0(sK6(X0,sK9(X0)))
      | ~ v4_orders_2(sK6(X0,sK9(X0)))
      | v2_struct_0(sK6(X0,sK9(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP0(X0)
      | sP1(X0)
      | ~ l1_waybel_0(sK9(X0),X0)
      | ~ v7_waybel_0(sK9(X0))
      | ~ v4_orders_2(sK9(X0))
      | v2_struct_0(sK9(X0))
      | ~ sP0(X0) ) ),
    inference(resolution,[],[f956,f80])).

fof(f80,plain,(
    ! [X0,X3] :
      ( v3_yellow_6(sK6(X0,X3),X0)
      | ~ l1_waybel_0(X3,X0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f956,plain,(
    ! [X8] :
      ( ~ v3_yellow_6(sK6(X8,sK9(X8)),X8)
      | ~ l1_waybel_0(sK6(X8,sK9(X8)),X8)
      | ~ v7_waybel_0(sK6(X8,sK9(X8)))
      | ~ v4_orders_2(sK6(X8,sK9(X8)))
      | v2_struct_0(sK6(X8,sK9(X8)))
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ sP0(X8)
      | sP1(X8) ) ),
    inference(trivial_inequality_removal,[],[f955])).

fof(f955,plain,(
    ! [X8] :
      ( k1_xboole_0 != k1_xboole_0
      | ~ v3_yellow_6(sK6(X8,sK9(X8)),X8)
      | ~ l1_waybel_0(sK6(X8,sK9(X8)),X8)
      | ~ v7_waybel_0(sK6(X8,sK9(X8)))
      | ~ v4_orders_2(sK6(X8,sK9(X8)))
      | v2_struct_0(sK6(X8,sK9(X8)))
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ sP0(X8)
      | sP1(X8) ) ),
    inference(duplicate_literal_removal,[],[f944])).

fof(f944,plain,(
    ! [X8] :
      ( k1_xboole_0 != k1_xboole_0
      | ~ v3_yellow_6(sK6(X8,sK9(X8)),X8)
      | ~ l1_waybel_0(sK6(X8,sK9(X8)),X8)
      | ~ v7_waybel_0(sK6(X8,sK9(X8)))
      | ~ v4_orders_2(sK6(X8,sK9(X8)))
      | v2_struct_0(sK6(X8,sK9(X8)))
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ sP0(X8)
      | ~ l1_waybel_0(sK6(X8,sK9(X8)),X8)
      | ~ v7_waybel_0(sK6(X8,sK9(X8)))
      | ~ v4_orders_2(sK6(X8,sK9(X8)))
      | v2_struct_0(sK6(X8,sK9(X8)))
      | ~ l1_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ v2_pre_topc(X8)
      | sP1(X8) ) ),
    inference(superposition,[],[f107,f939])).

fof(f939,plain,(
    ! [X2] :
      ( k1_xboole_0 = k10_yellow_6(X2,sK6(X2,sK9(X2)))
      | ~ sP0(X2)
      | ~ l1_waybel_0(sK6(X2,sK9(X2)),X2)
      | ~ v7_waybel_0(sK6(X2,sK9(X2)))
      | ~ v4_orders_2(sK6(X2,sK9(X2)))
      | v2_struct_0(sK6(X2,sK9(X2)))
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ v2_pre_topc(X2)
      | sP1(X2) ) ),
    inference(subsumption_resolution,[],[f933,f92])).

fof(f92,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f933,plain,(
    ! [X2] :
      ( sP1(X2)
      | ~ sP0(X2)
      | ~ l1_waybel_0(sK6(X2,sK9(X2)),X2)
      | ~ v7_waybel_0(sK6(X2,sK9(X2)))
      | ~ v4_orders_2(sK6(X2,sK9(X2)))
      | v2_struct_0(sK6(X2,sK9(X2)))
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v2_pre_topc(X2)
      | k1_xboole_0 = k10_yellow_6(X2,sK6(X2,sK9(X2))) ) ),
    inference(resolution,[],[f908,f143])).

fof(f143,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f125,f91])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f908,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_yellow_6(X0,sK6(X0,sK9(X0))),X1)
      | sP1(X0)
      | ~ sP0(X0)
      | ~ l1_waybel_0(sK6(X0,sK9(X0)),X0)
      | ~ v7_waybel_0(sK6(X0,sK9(X0)))
      | ~ v4_orders_2(sK6(X0,sK9(X0)))
      | v2_struct_0(sK6(X0,sK9(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f905])).

fof(f905,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | sP1(X0)
      | ~ sP0(X0)
      | ~ l1_waybel_0(sK6(X0,sK9(X0)),X0)
      | ~ v7_waybel_0(sK6(X0,sK9(X0)))
      | ~ v4_orders_2(sK6(X0,sK9(X0)))
      | v2_struct_0(sK6(X0,sK9(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(k10_yellow_6(X0,sK6(X0,sK9(X0))),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_waybel_0(sK6(X0,sK9(X0)),X0)
      | ~ v7_waybel_0(sK6(X0,sK9(X0)))
      | ~ v4_orders_2(sK6(X0,sK9(X0)))
      | v2_struct_0(sK6(X0,sK9(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f687,f122])).

fof(f122,plain,(
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

fof(f687,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k10_yellow_6(X0,sK6(X0,sK9(X0))),k1_zfmisc_1(X2))
      | v2_struct_0(X0)
      | sP1(X0)
      | ~ sP0(X0)
      | ~ l1_waybel_0(sK6(X0,sK9(X0)),X0)
      | ~ v7_waybel_0(sK6(X0,sK9(X0)))
      | ~ v4_orders_2(sK6(X0,sK9(X0)))
      | v2_struct_0(sK6(X0,sK9(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(k10_yellow_6(X0,sK6(X0,sK9(X0))),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f686,f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( sP3(X2,X1,X0)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | sP3(X2,X1,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_folding,[],[f34,f47])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
      | ~ sP3(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).

fof(f686,plain,(
    ! [X8,X7,X9] :
      ( ~ sP3(X7,k10_yellow_6(X8,sK6(X8,sK9(X8))),X9)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | sP1(X8)
      | ~ sP0(X8)
      | ~ l1_waybel_0(sK6(X8,sK9(X8)),X8)
      | ~ v7_waybel_0(sK6(X8,sK9(X8)))
      | ~ v4_orders_2(sK6(X8,sK9(X8)))
      | v2_struct_0(sK6(X8,sK9(X8)))
      | ~ l1_pre_topc(X8) ) ),
    inference(subsumption_resolution,[],[f251,f175])).

fof(f175,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK12(X2,k10_yellow_6(X1,X0),X3),u1_struct_0(X1))
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ v7_waybel_0(X0)
      | ~ l1_waybel_0(X0,X1)
      | ~ sP3(X2,k10_yellow_6(X1,X0),X3) ) ),
    inference(resolution,[],[f168,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK12(X0,X1,X2),X1)
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r2_hidden(sK12(X0,X1,X2),X0)
        & r2_hidden(sK12(X0,X1,X2),X1)
        & m1_subset_1(sK12(X0,X1,X2),X2) )
      | ~ sP3(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f72,f73])).

fof(f73,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X0)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X2) )
     => ( ~ r2_hidden(sK12(X0,X1,X2),X0)
        & r2_hidden(sK12(X0,X1,X2),X1)
        & m1_subset_1(sK12(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X0)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X2) )
      | ~ sP3(X0,X1,X2) ) ),
    inference(rectify,[],[f71])).

fof(f71,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
      | ~ sP3(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f168,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k10_yellow_6(X1,X0))
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X0,X1) ) ),
    inference(resolution,[],[f122,f127])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f251,plain,(
    ! [X8,X7,X9] :
      ( ~ m1_subset_1(sK12(X7,k10_yellow_6(X8,sK6(X8,sK9(X8))),X9),u1_struct_0(X8))
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | sP1(X8)
      | ~ sP0(X8)
      | ~ l1_waybel_0(sK6(X8,sK9(X8)),X8)
      | ~ v7_waybel_0(sK6(X8,sK9(X8)))
      | ~ v4_orders_2(sK6(X8,sK9(X8)))
      | v2_struct_0(sK6(X8,sK9(X8)))
      | ~ sP3(X7,k10_yellow_6(X8,sK6(X8,sK9(X8))),X9) ) ),
    inference(duplicate_literal_removal,[],[f250])).

fof(f250,plain,(
    ! [X8,X7,X9] :
      ( ~ m1_subset_1(sK12(X7,k10_yellow_6(X8,sK6(X8,sK9(X8))),X9),u1_struct_0(X8))
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | sP1(X8)
      | ~ sP0(X8)
      | ~ l1_waybel_0(sK6(X8,sK9(X8)),X8)
      | ~ v7_waybel_0(sK6(X8,sK9(X8)))
      | ~ v4_orders_2(sK6(X8,sK9(X8)))
      | v2_struct_0(sK6(X8,sK9(X8)))
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ sP3(X7,k10_yellow_6(X8,sK6(X8,sK9(X8))),X9) ) ),
    inference(resolution,[],[f245,f179])).

fof(f179,plain,(
    ! [X2,X0,X3,X1] :
      ( r3_waybel_9(X0,X1,sK12(X2,k10_yellow_6(X0,X1),X3))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP3(X2,k10_yellow_6(X0,X1),X3) ) ),
    inference(resolution,[],[f178,f114])).

fof(f178,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k10_yellow_6(X0,X1))
      | r3_waybel_9(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f109,f168])).

fof(f109,plain,(
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

fof(f245,plain,(
    ! [X0,X1] :
      ( ~ r3_waybel_9(X1,sK6(X1,sK9(X1)),X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | sP1(X1)
      | ~ sP0(X1) ) ),
    inference(subsumption_resolution,[],[f244,f100])).

fof(f244,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ r3_waybel_9(X1,sK6(X1,sK9(X1)),X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | sP1(X1)
      | v2_struct_0(sK9(X1))
      | ~ sP0(X1) ) ),
    inference(subsumption_resolution,[],[f243,f101])).

fof(f243,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ r3_waybel_9(X1,sK6(X1,sK9(X1)),X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | sP1(X1)
      | ~ v4_orders_2(sK9(X1))
      | v2_struct_0(sK9(X1))
      | ~ sP0(X1) ) ),
    inference(subsumption_resolution,[],[f242,f102])).

fof(f242,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ r3_waybel_9(X1,sK6(X1,sK9(X1)),X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | sP1(X1)
      | ~ v7_waybel_0(sK9(X1))
      | ~ v4_orders_2(sK9(X1))
      | v2_struct_0(sK9(X1))
      | ~ sP0(X1) ) ),
    inference(subsumption_resolution,[],[f239,f103])).

fof(f239,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ r3_waybel_9(X1,sK6(X1,sK9(X1)),X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | sP1(X1)
      | ~ l1_waybel_0(sK9(X1),X1)
      | ~ v7_waybel_0(sK9(X1))
      | ~ v4_orders_2(sK9(X1))
      | v2_struct_0(sK9(X1))
      | ~ sP0(X1) ) ),
    inference(resolution,[],[f238,f79])).

fof(f238,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_yellow_6(X1,X0,sK9(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | sP1(X0) ) ),
    inference(subsumption_resolution,[],[f237,f100])).

fof(f237,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m2_yellow_6(X1,X0,sK9(X0))
      | v2_struct_0(sK9(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | sP1(X0) ) ),
    inference(subsumption_resolution,[],[f236,f101])).

fof(f236,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m2_yellow_6(X1,X0,sK9(X0))
      | ~ v4_orders_2(sK9(X0))
      | v2_struct_0(sK9(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | sP1(X0) ) ),
    inference(subsumption_resolution,[],[f235,f102])).

fof(f235,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m2_yellow_6(X1,X0,sK9(X0))
      | ~ v7_waybel_0(sK9(X0))
      | ~ v4_orders_2(sK9(X0))
      | v2_struct_0(sK9(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | sP1(X0) ) ),
    inference(subsumption_resolution,[],[f234,f103])).

fof(f234,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m2_yellow_6(X1,X0,sK9(X0))
      | ~ l1_waybel_0(sK9(X0),X0)
      | ~ v7_waybel_0(sK9(X0))
      | ~ v4_orders_2(sK9(X0))
      | v2_struct_0(sK9(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | sP1(X0) ) ),
    inference(duplicate_literal_removal,[],[f233])).

fof(f233,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m2_yellow_6(X1,X0,sK9(X0))
      | ~ l1_waybel_0(sK9(X0),X0)
      | ~ v7_waybel_0(sK9(X0))
      | ~ v4_orders_2(sK9(X0))
      | v2_struct_0(sK9(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | sP1(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f112,f105])).

fof(f105,plain,(
    ! [X2,X0] :
      ( ~ r3_waybel_9(X0,sK9(X0),X2)
      | sP1(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f112,plain,(
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

fof(f107,plain,(
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
    inference(cnf_transformation,[],[f68])).

fof(f139,plain,
    ( spl13_1
    | spl13_2 ),
    inference(avatar_split_clause,[],[f89,f135,f131])).

fof(f89,plain,
    ( sP0(sK7)
    | v1_compts_1(sK7) ),
    inference(cnf_transformation,[],[f59])).

fof(f138,plain,
    ( ~ spl13_1
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f90,f135,f131])).

fof(f90,plain,
    ( ~ sP0(sK7)
    | ~ v1_compts_1(sK7) ),
    inference(cnf_transformation,[],[f59])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:32:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (3170)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.48  % (3174)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (3174)Refutation not found, incomplete strategy% (3174)------------------------------
% 0.21/0.48  % (3174)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (3174)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (3174)Memory used [KB]: 6140
% 0.21/0.48  % (3174)Time elapsed: 0.084 s
% 0.21/0.48  % (3174)------------------------------
% 0.21/0.48  % (3174)------------------------------
% 0.21/0.48  % (3186)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.49  % (3188)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.49  % (3163)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.49  % (3165)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (3164)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (3173)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.50  % (3171)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.50  % (3160)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (3160)Refutation not found, incomplete strategy% (3160)------------------------------
% 0.21/0.51  % (3160)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (3160)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (3160)Memory used [KB]: 10618
% 0.21/0.51  % (3160)Time elapsed: 0.092 s
% 0.21/0.51  % (3160)------------------------------
% 0.21/0.51  % (3160)------------------------------
% 0.21/0.51  % (3179)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.51  % (3162)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (3185)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (3168)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  % (3177)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (3183)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.52  % (3176)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (3168)Refutation not found, incomplete strategy% (3168)------------------------------
% 0.21/0.52  % (3168)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (3168)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (3168)Memory used [KB]: 1663
% 0.21/0.52  % (3168)Time elapsed: 0.108 s
% 0.21/0.52  % (3168)------------------------------
% 0.21/0.52  % (3168)------------------------------
% 0.21/0.52  % (3178)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.52  % (3172)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.52  % (3172)Refutation not found, incomplete strategy% (3172)------------------------------
% 0.21/0.52  % (3172)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (3172)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (3172)Memory used [KB]: 10746
% 0.21/0.52  % (3172)Time elapsed: 0.116 s
% 0.21/0.52  % (3172)------------------------------
% 0.21/0.52  % (3172)------------------------------
% 0.21/0.53  % (3167)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.53  % (3169)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.53  % (3167)Refutation not found, incomplete strategy% (3167)------------------------------
% 0.21/0.53  % (3167)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (3167)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (3167)Memory used [KB]: 10618
% 0.21/0.53  % (3167)Time elapsed: 0.072 s
% 0.21/0.53  % (3167)------------------------------
% 0.21/0.53  % (3167)------------------------------
% 0.21/0.53  % (3180)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.53  % (3182)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.54  % (3187)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.54  % (3184)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.54  % (3166)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.54  % (3166)Refutation not found, incomplete strategy% (3166)------------------------------
% 0.21/0.54  % (3166)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (3166)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (3166)Memory used [KB]: 6140
% 0.21/0.54  % (3166)Time elapsed: 0.137 s
% 0.21/0.54  % (3166)------------------------------
% 0.21/0.54  % (3166)------------------------------
% 1.49/0.55  % (3165)Refutation found. Thanks to Tanya!
% 1.49/0.55  % SZS status Theorem for theBenchmark
% 1.49/0.55  % SZS output start Proof for theBenchmark
% 1.49/0.55  fof(f1010,plain,(
% 1.49/0.55    $false),
% 1.49/0.55    inference(avatar_sat_refutation,[],[f138,f139,f1003,f1009])).
% 1.49/0.55  fof(f1009,plain,(
% 1.49/0.55    ~spl13_1 | spl13_2),
% 1.49/0.55    inference(avatar_contradiction_clause,[],[f1008])).
% 1.49/0.55  fof(f1008,plain,(
% 1.49/0.55    $false | (~spl13_1 | spl13_2)),
% 1.49/0.55    inference(subsumption_resolution,[],[f1007,f132])).
% 1.49/0.55  fof(f132,plain,(
% 1.49/0.55    v1_compts_1(sK7) | ~spl13_1),
% 1.49/0.55    inference(avatar_component_clause,[],[f131])).
% 1.49/0.55  fof(f131,plain,(
% 1.49/0.55    spl13_1 <=> v1_compts_1(sK7)),
% 1.49/0.55    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).
% 1.49/0.55  fof(f1007,plain,(
% 1.49/0.55    ~v1_compts_1(sK7) | spl13_2),
% 1.49/0.55    inference(subsumption_resolution,[],[f1006,f87])).
% 1.49/0.55  fof(f87,plain,(
% 1.49/0.55    v2_pre_topc(sK7)),
% 1.49/0.55    inference(cnf_transformation,[],[f59])).
% 1.49/0.55  fof(f59,plain,(
% 1.49/0.55    (~sP0(sK7) | ~v1_compts_1(sK7)) & (sP0(sK7) | v1_compts_1(sK7)) & l1_pre_topc(sK7) & v2_pre_topc(sK7) & ~v2_struct_0(sK7)),
% 1.49/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f57,f58])).
% 1.49/0.55  fof(f58,plain,(
% 1.49/0.55    ? [X0] : ((~sP0(X0) | ~v1_compts_1(X0)) & (sP0(X0) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ((~sP0(sK7) | ~v1_compts_1(sK7)) & (sP0(sK7) | v1_compts_1(sK7)) & l1_pre_topc(sK7) & v2_pre_topc(sK7) & ~v2_struct_0(sK7))),
% 1.49/0.55    introduced(choice_axiom,[])).
% 1.49/0.55  fof(f57,plain,(
% 1.49/0.55    ? [X0] : ((~sP0(X0) | ~v1_compts_1(X0)) & (sP0(X0) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.49/0.55    inference(flattening,[],[f56])).
% 1.49/0.55  fof(f56,plain,(
% 1.49/0.55    ? [X0] : (((~sP0(X0) | ~v1_compts_1(X0)) & (sP0(X0) | v1_compts_1(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.49/0.55    inference(nnf_transformation,[],[f43])).
% 1.49/0.55  fof(f43,plain,(
% 1.49/0.55    ? [X0] : ((v1_compts_1(X0) <~> sP0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.49/0.55    inference(definition_folding,[],[f19,f42])).
% 1.49/0.55  fof(f42,plain,(
% 1.49/0.55    ! [X0] : (sP0(X0) <=> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))),
% 1.49/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.49/0.55  fof(f19,plain,(
% 1.49/0.55    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.49/0.55    inference(flattening,[],[f18])).
% 1.49/0.55  fof(f18,plain,(
% 1.49/0.55    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.49/0.55    inference(ennf_transformation,[],[f17])).
% 1.49/0.55  fof(f17,negated_conjecture,(
% 1.49/0.55    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)))))),
% 1.49/0.55    inference(negated_conjecture,[],[f16])).
% 1.49/0.55  fof(f16,conjecture,(
% 1.49/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)))))),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_yellow19)).
% 1.49/0.55  fof(f1006,plain,(
% 1.49/0.55    ~v2_pre_topc(sK7) | ~v1_compts_1(sK7) | spl13_2),
% 1.49/0.55    inference(subsumption_resolution,[],[f1005,f88])).
% 1.49/0.55  fof(f88,plain,(
% 1.49/0.55    l1_pre_topc(sK7)),
% 1.49/0.55    inference(cnf_transformation,[],[f59])).
% 1.49/0.55  fof(f1005,plain,(
% 1.49/0.55    ~l1_pre_topc(sK7) | ~v2_pre_topc(sK7) | ~v1_compts_1(sK7) | spl13_2),
% 1.49/0.55    inference(subsumption_resolution,[],[f1004,f86])).
% 1.49/0.55  fof(f86,plain,(
% 1.49/0.55    ~v2_struct_0(sK7)),
% 1.49/0.55    inference(cnf_transformation,[],[f59])).
% 1.49/0.55  fof(f1004,plain,(
% 1.49/0.55    v2_struct_0(sK7) | ~l1_pre_topc(sK7) | ~v2_pre_topc(sK7) | ~v1_compts_1(sK7) | spl13_2),
% 1.49/0.55    inference(resolution,[],[f137,f360])).
% 1.49/0.55  fof(f360,plain,(
% 1.49/0.55    ( ! [X5] : (sP0(X5) | v2_struct_0(X5) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | ~v1_compts_1(X5)) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f359,f81])).
% 1.49/0.55  fof(f81,plain,(
% 1.49/0.55    ( ! [X0] : (~v2_struct_0(sK5(X0)) | sP0(X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f55])).
% 1.49/0.55  fof(f55,plain,(
% 1.49/0.55    ! [X0] : ((sP0(X0) | (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,sK5(X0))) & l1_waybel_0(sK5(X0),X0) & v7_waybel_0(sK5(X0)) & v4_orders_2(sK5(X0)) & ~v2_struct_0(sK5(X0)))) & (! [X3] : ((v3_yellow_6(sK6(X0,X3),X0) & m2_yellow_6(sK6(X0,X3),X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | ~sP0(X0)))),
% 1.49/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f52,f54,f53])).
% 1.49/0.55  fof(f53,plain,(
% 1.49/0.55    ! [X0] : (? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,sK5(X0))) & l1_waybel_0(sK5(X0),X0) & v7_waybel_0(sK5(X0)) & v4_orders_2(sK5(X0)) & ~v2_struct_0(sK5(X0))))),
% 1.49/0.55    introduced(choice_axiom,[])).
% 1.49/0.55  fof(f54,plain,(
% 1.49/0.55    ! [X3,X0] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) => (v3_yellow_6(sK6(X0,X3),X0) & m2_yellow_6(sK6(X0,X3),X0,X3)))),
% 1.49/0.55    introduced(choice_axiom,[])).
% 1.49/0.55  fof(f52,plain,(
% 1.49/0.55    ! [X0] : ((sP0(X0) | ? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | ~sP0(X0)))),
% 1.49/0.55    inference(rectify,[],[f51])).
% 1.49/0.55  fof(f51,plain,(
% 1.49/0.55    ! [X0] : ((sP0(X0) | ? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~sP0(X0)))),
% 1.49/0.55    inference(nnf_transformation,[],[f42])).
% 1.49/0.55  fof(f359,plain,(
% 1.49/0.55    ( ! [X5] : (~v2_pre_topc(X5) | v2_struct_0(X5) | ~l1_pre_topc(X5) | sP0(X5) | v2_struct_0(sK5(X5)) | ~v1_compts_1(X5)) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f358,f82])).
% 1.49/0.55  fof(f82,plain,(
% 1.49/0.55    ( ! [X0] : (v4_orders_2(sK5(X0)) | sP0(X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f55])).
% 1.49/0.55  fof(f358,plain,(
% 1.49/0.55    ( ! [X5] : (~v2_pre_topc(X5) | v2_struct_0(X5) | ~l1_pre_topc(X5) | sP0(X5) | ~v4_orders_2(sK5(X5)) | v2_struct_0(sK5(X5)) | ~v1_compts_1(X5)) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f357,f83])).
% 1.49/0.55  fof(f83,plain,(
% 1.49/0.55    ( ! [X0] : (v7_waybel_0(sK5(X0)) | sP0(X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f55])).
% 1.49/0.55  fof(f357,plain,(
% 1.49/0.55    ( ! [X5] : (~v2_pre_topc(X5) | v2_struct_0(X5) | ~l1_pre_topc(X5) | sP0(X5) | ~v7_waybel_0(sK5(X5)) | ~v4_orders_2(sK5(X5)) | v2_struct_0(sK5(X5)) | ~v1_compts_1(X5)) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f356,f84])).
% 1.49/0.55  fof(f84,plain,(
% 1.49/0.55    ( ! [X0] : (l1_waybel_0(sK5(X0),X0) | sP0(X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f55])).
% 1.49/0.55  fof(f356,plain,(
% 1.49/0.55    ( ! [X5] : (~v2_pre_topc(X5) | v2_struct_0(X5) | ~l1_pre_topc(X5) | sP0(X5) | ~l1_waybel_0(sK5(X5),X5) | ~v7_waybel_0(sK5(X5)) | ~v4_orders_2(sK5(X5)) | v2_struct_0(sK5(X5)) | ~v1_compts_1(X5)) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f349,f94])).
% 1.49/0.55  fof(f94,plain,(
% 1.49/0.55    ( ! [X0,X1] : (m1_subset_1(sK8(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f61])).
% 1.49/0.55  fof(f61,plain,(
% 1.49/0.55    ! [X0] : (! [X1] : ((r3_waybel_9(X0,X1,sK8(X0,X1)) & m1_subset_1(sK8(X0,X1),u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.49/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f22,f60])).
% 1.49/0.55  fof(f60,plain,(
% 1.49/0.55    ! [X1,X0] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) => (r3_waybel_9(X0,X1,sK8(X0,X1)) & m1_subset_1(sK8(X0,X1),u1_struct_0(X0))))),
% 1.49/0.55    introduced(choice_axiom,[])).
% 1.49/0.55  fof(f22,plain,(
% 1.49/0.55    ! [X0] : (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.49/0.55    inference(flattening,[],[f21])).
% 1.49/0.55  fof(f21,plain,(
% 1.49/0.55    ! [X0] : ((! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | ~v1_compts_1(X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.49/0.55    inference(ennf_transformation,[],[f14])).
% 1.49/0.55  fof(f14,axiom,(
% 1.49/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))))))),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l37_yellow19)).
% 1.49/0.55  fof(f349,plain,(
% 1.49/0.55    ( ! [X5] : (~v2_pre_topc(X5) | v2_struct_0(X5) | ~l1_pre_topc(X5) | ~m1_subset_1(sK8(X5,sK5(X5)),u1_struct_0(X5)) | sP0(X5) | ~l1_waybel_0(sK5(X5),X5) | ~v7_waybel_0(sK5(X5)) | ~v4_orders_2(sK5(X5)) | v2_struct_0(sK5(X5)) | ~v1_compts_1(X5)) )),
% 1.49/0.55    inference(duplicate_literal_removal,[],[f345])).
% 1.49/0.55  fof(f345,plain,(
% 1.49/0.55    ( ! [X5] : (~v2_pre_topc(X5) | v2_struct_0(X5) | ~l1_pre_topc(X5) | ~m1_subset_1(sK8(X5,sK5(X5)),u1_struct_0(X5)) | sP0(X5) | ~l1_waybel_0(sK5(X5),X5) | ~v7_waybel_0(sK5(X5)) | ~v4_orders_2(sK5(X5)) | v2_struct_0(sK5(X5)) | ~v1_compts_1(X5) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) )),
% 1.49/0.55    inference(resolution,[],[f342,f95])).
% 1.49/0.55  fof(f95,plain,(
% 1.49/0.55    ( ! [X0,X1] : (r3_waybel_9(X0,X1,sK8(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f61])).
% 1.49/0.55  fof(f342,plain,(
% 1.49/0.55    ( ! [X0,X1] : (~r3_waybel_9(X0,sK5(X0),X1) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | sP0(X0)) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f341,f81])).
% 1.49/0.55  fof(f341,plain,(
% 1.49/0.55    ( ! [X0,X1] : (v2_struct_0(sK5(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~r3_waybel_9(X0,sK5(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | sP0(X0)) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f340,f82])).
% 1.49/0.55  fof(f340,plain,(
% 1.49/0.55    ( ! [X0,X1] : (~v4_orders_2(sK5(X0)) | v2_struct_0(sK5(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~r3_waybel_9(X0,sK5(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | sP0(X0)) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f339,f83])).
% 1.49/0.55  fof(f339,plain,(
% 1.49/0.55    ( ! [X0,X1] : (~v7_waybel_0(sK5(X0)) | ~v4_orders_2(sK5(X0)) | v2_struct_0(sK5(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~r3_waybel_9(X0,sK5(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | sP0(X0)) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f338,f84])).
% 1.49/0.55  fof(f338,plain,(
% 1.49/0.55    ( ! [X0,X1] : (~l1_waybel_0(sK5(X0),X0) | ~v7_waybel_0(sK5(X0)) | ~v4_orders_2(sK5(X0)) | v2_struct_0(sK5(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~r3_waybel_9(X0,sK5(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | sP0(X0)) )),
% 1.49/0.55    inference(duplicate_literal_removal,[],[f337])).
% 1.49/0.55  fof(f337,plain,(
% 1.49/0.55    ( ! [X0,X1] : (~l1_waybel_0(sK5(X0),X0) | ~v7_waybel_0(sK5(X0)) | ~v4_orders_2(sK5(X0)) | v2_struct_0(sK5(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~r3_waybel_9(X0,sK5(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~r3_waybel_9(X0,sK5(X0),X1) | sP0(X0)) )),
% 1.49/0.55    inference(resolution,[],[f305,f188])).
% 1.49/0.55  fof(f188,plain,(
% 1.49/0.55    ( ! [X0,X1] : (~v3_yellow_6(sK11(X0,sK5(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~r3_waybel_9(X0,sK5(X0),X1) | sP0(X0)) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f187,f81])).
% 1.49/0.55  fof(f187,plain,(
% 1.49/0.55    ( ! [X0,X1] : (~r3_waybel_9(X0,sK5(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(sK5(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v3_yellow_6(sK11(X0,sK5(X0),X1),X0) | sP0(X0)) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f186,f82])).
% 1.49/0.55  fof(f186,plain,(
% 1.49/0.55    ( ! [X0,X1] : (~r3_waybel_9(X0,sK5(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v4_orders_2(sK5(X0)) | v2_struct_0(sK5(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v3_yellow_6(sK11(X0,sK5(X0),X1),X0) | sP0(X0)) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f185,f83])).
% 1.49/0.55  fof(f185,plain,(
% 1.49/0.55    ( ! [X0,X1] : (~r3_waybel_9(X0,sK5(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v7_waybel_0(sK5(X0)) | ~v4_orders_2(sK5(X0)) | v2_struct_0(sK5(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v3_yellow_6(sK11(X0,sK5(X0),X1),X0) | sP0(X0)) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f182,f84])).
% 1.49/0.55  fof(f182,plain,(
% 1.49/0.55    ( ! [X0,X1] : (~r3_waybel_9(X0,sK5(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_waybel_0(sK5(X0),X0) | ~v7_waybel_0(sK5(X0)) | ~v4_orders_2(sK5(X0)) | v2_struct_0(sK5(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v3_yellow_6(sK11(X0,sK5(X0),X1),X0) | sP0(X0)) )),
% 1.49/0.55    inference(resolution,[],[f110,f85])).
% 1.49/0.55  fof(f85,plain,(
% 1.49/0.55    ( ! [X2,X0] : (~m2_yellow_6(X2,X0,sK5(X0)) | ~v3_yellow_6(X2,X0) | sP0(X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f55])).
% 1.49/0.55  fof(f110,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (m2_yellow_6(sK11(X0,X1,X2),X0,X1) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f70])).
% 1.49/0.55  fof(f70,plain,(
% 1.49/0.55    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k10_yellow_6(X0,sK11(X0,X1,X2))) & m2_yellow_6(sK11(X0,X1,X2),X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.49/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f30,f69])).
% 1.49/0.55  fof(f69,plain,(
% 1.49/0.55    ! [X2,X1,X0] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) => (r2_hidden(X2,k10_yellow_6(X0,sK11(X0,X1,X2))) & m2_yellow_6(sK11(X0,X1,X2),X0,X1)))),
% 1.49/0.55    introduced(choice_axiom,[])).
% 1.49/0.55  fof(f30,plain,(
% 1.49/0.55    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.49/0.55    inference(flattening,[],[f29])).
% 1.49/0.55  fof(f29,plain,(
% 1.49/0.55    ! [X0] : (! [X1] : (! [X2] : ((? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.49/0.55    inference(ennf_transformation,[],[f13])).
% 1.49/0.55  fof(f13,axiom,(
% 1.49/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m2_yellow_6(X3,X0,X1) => ~r2_hidden(X2,k10_yellow_6(X0,X3))) & r3_waybel_9(X0,X1,X2)))))),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_waybel_9)).
% 1.49/0.55  fof(f305,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (v3_yellow_6(sK11(X0,X1,X2),X0) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f304,f206])).
% 1.49/0.55  fof(f206,plain,(
% 1.49/0.55    ( ! [X10,X11,X9] : (~v2_struct_0(sK11(X10,X11,X9)) | ~l1_waybel_0(X11,X10) | ~v7_waybel_0(X11) | ~v4_orders_2(X11) | v2_struct_0(X11) | ~l1_pre_topc(X10) | ~v2_pre_topc(X10) | v2_struct_0(X10) | ~r3_waybel_9(X10,X11,X9) | ~m1_subset_1(X9,u1_struct_0(X10))) )),
% 1.49/0.55    inference(resolution,[],[f189,f117])).
% 1.49/0.55  fof(f117,plain,(
% 1.49/0.55    ( ! [X0,X1] : (~sP4(X0,X1) | ~v2_struct_0(X1)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f76])).
% 1.49/0.55  fof(f76,plain,(
% 1.49/0.55    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~sP4(X0,X1))),
% 1.49/0.55    inference(rectify,[],[f75])).
% 1.49/0.55  fof(f75,plain,(
% 1.49/0.55    ! [X0,X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~sP4(X0,X2))),
% 1.49/0.55    inference(nnf_transformation,[],[f49])).
% 1.49/0.55  fof(f49,plain,(
% 1.49/0.55    ! [X0,X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~sP4(X0,X2))),
% 1.49/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 1.49/0.55  fof(f189,plain,(
% 1.49/0.55    ( ! [X4,X2,X3] : (sP4(X2,sK11(X2,X3,X4)) | ~m1_subset_1(X4,u1_struct_0(X2)) | ~l1_waybel_0(X3,X2) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~r3_waybel_9(X2,X3,X4)) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f184,f93])).
% 1.49/0.55  fof(f93,plain,(
% 1.49/0.55    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f20])).
% 1.49/0.55  fof(f20,plain,(
% 1.49/0.55    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.49/0.55    inference(ennf_transformation,[],[f7])).
% 1.49/0.55  fof(f7,axiom,(
% 1.49/0.55    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.49/0.55  fof(f184,plain,(
% 1.49/0.55    ( ! [X4,X2,X3] : (~r3_waybel_9(X2,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X2)) | ~l1_waybel_0(X3,X2) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | sP4(X2,sK11(X2,X3,X4)) | ~l1_struct_0(X2)) )),
% 1.49/0.55    inference(duplicate_literal_removal,[],[f183])).
% 1.49/0.55  fof(f183,plain,(
% 1.49/0.55    ( ! [X4,X2,X3] : (~r3_waybel_9(X2,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X2)) | ~l1_waybel_0(X3,X2) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | sP4(X2,sK11(X2,X3,X4)) | ~l1_waybel_0(X3,X2) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | ~l1_struct_0(X2) | v2_struct_0(X2)) )),
% 1.49/0.55    inference(resolution,[],[f110,f121])).
% 1.49/0.55  fof(f121,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (~m2_yellow_6(X2,X0,X1) | sP4(X0,X2) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f50])).
% 1.49/0.55  fof(f50,plain,(
% 1.49/0.55    ! [X0,X1] : (! [X2] : (sP4(X0,X2) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.49/0.55    inference(definition_folding,[],[f36,f49])).
% 1.49/0.55  fof(f36,plain,(
% 1.49/0.55    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.49/0.55    inference(flattening,[],[f35])).
% 1.49/0.55  fof(f35,plain,(
% 1.49/0.55    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.49/0.55    inference(ennf_transformation,[],[f9])).
% 1.49/0.55  fof(f9,axiom,(
% 1.49/0.55    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))))),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_yellow_6)).
% 1.49/0.55  fof(f304,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~r3_waybel_9(X0,X1,X2) | v3_yellow_6(sK11(X0,X1,X2),X0) | v2_struct_0(sK11(X0,X1,X2))) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f303,f205])).
% 1.49/0.55  fof(f205,plain,(
% 1.49/0.55    ( ! [X6,X8,X7] : (v4_orders_2(sK11(X7,X8,X6)) | ~l1_waybel_0(X8,X7) | ~v7_waybel_0(X8) | ~v4_orders_2(X8) | v2_struct_0(X8) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7) | ~r3_waybel_9(X7,X8,X6) | ~m1_subset_1(X6,u1_struct_0(X7))) )),
% 1.49/0.55    inference(resolution,[],[f189,f118])).
% 1.49/0.55  fof(f118,plain,(
% 1.49/0.55    ( ! [X0,X1] : (~sP4(X0,X1) | v4_orders_2(X1)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f76])).
% 1.49/0.55  fof(f303,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~r3_waybel_9(X0,X1,X2) | v3_yellow_6(sK11(X0,X1,X2),X0) | ~v4_orders_2(sK11(X0,X1,X2)) | v2_struct_0(sK11(X0,X1,X2))) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f302,f204])).
% 1.49/0.55  fof(f204,plain,(
% 1.49/0.55    ( ! [X4,X5,X3] : (v7_waybel_0(sK11(X4,X5,X3)) | ~l1_waybel_0(X5,X4) | ~v7_waybel_0(X5) | ~v4_orders_2(X5) | v2_struct_0(X5) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4) | ~r3_waybel_9(X4,X5,X3) | ~m1_subset_1(X3,u1_struct_0(X4))) )),
% 1.49/0.55    inference(resolution,[],[f189,f119])).
% 1.49/0.55  fof(f119,plain,(
% 1.49/0.55    ( ! [X0,X1] : (~sP4(X0,X1) | v7_waybel_0(X1)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f76])).
% 1.49/0.55  fof(f302,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~r3_waybel_9(X0,X1,X2) | v3_yellow_6(sK11(X0,X1,X2),X0) | ~v7_waybel_0(sK11(X0,X1,X2)) | ~v4_orders_2(sK11(X0,X1,X2)) | v2_struct_0(sK11(X0,X1,X2))) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f301,f203])).
% 1.49/0.55  fof(f203,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (l1_waybel_0(sK11(X1,X2,X0),X1) | ~l1_waybel_0(X2,X1) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~r3_waybel_9(X1,X2,X0) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 1.49/0.55    inference(resolution,[],[f189,f120])).
% 1.49/0.55  fof(f120,plain,(
% 1.49/0.55    ( ! [X0,X1] : (~sP4(X0,X1) | l1_waybel_0(X1,X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f76])).
% 1.49/0.55  fof(f301,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~r3_waybel_9(X0,X1,X2) | v3_yellow_6(sK11(X0,X1,X2),X0) | ~l1_waybel_0(sK11(X0,X1,X2),X0) | ~v7_waybel_0(sK11(X0,X1,X2)) | ~v4_orders_2(sK11(X0,X1,X2)) | v2_struct_0(sK11(X0,X1,X2))) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f300,f91])).
% 1.49/0.55  fof(f91,plain,(
% 1.49/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f2])).
% 1.49/0.55  fof(f2,axiom,(
% 1.49/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.49/0.55  fof(f300,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (~r1_tarski(k1_xboole_0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~r3_waybel_9(X0,X1,X2) | v3_yellow_6(sK11(X0,X1,X2),X0) | ~l1_waybel_0(sK11(X0,X1,X2),X0) | ~v7_waybel_0(sK11(X0,X1,X2)) | ~v4_orders_2(sK11(X0,X1,X2)) | v2_struct_0(sK11(X0,X1,X2))) )),
% 1.49/0.55    inference(duplicate_literal_removal,[],[f299])).
% 1.49/0.55  fof(f299,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (~r1_tarski(k1_xboole_0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~r3_waybel_9(X0,X1,X2) | v3_yellow_6(sK11(X0,X1,X2),X0) | ~l1_waybel_0(sK11(X0,X1,X2),X0) | ~v7_waybel_0(sK11(X0,X1,X2)) | ~v4_orders_2(sK11(X0,X1,X2)) | v2_struct_0(sK11(X0,X1,X2)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.49/0.55    inference(superposition,[],[f209,f108])).
% 1.49/0.55  fof(f108,plain,(
% 1.49/0.55    ( ! [X0,X1] : (k1_xboole_0 = k10_yellow_6(X0,X1) | v3_yellow_6(X1,X0) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f68])).
% 1.49/0.55  fof(f68,plain,(
% 1.49/0.55    ! [X0] : (! [X1] : (((v3_yellow_6(X1,X0) | k1_xboole_0 = k10_yellow_6(X0,X1)) & (k1_xboole_0 != k10_yellow_6(X0,X1) | ~v3_yellow_6(X1,X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.49/0.55    inference(nnf_transformation,[],[f26])).
% 1.49/0.55  fof(f26,plain,(
% 1.49/0.55    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.49/0.55    inference(flattening,[],[f25])).
% 1.49/0.55  fof(f25,plain,(
% 1.49/0.55    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.49/0.55    inference(ennf_transformation,[],[f10])).
% 1.49/0.55  fof(f10,axiom,(
% 1.49/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1))))),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_yellow_6)).
% 1.49/0.55  fof(f209,plain,(
% 1.49/0.55    ( ! [X6,X8,X7] : (~r1_tarski(k10_yellow_6(X6,sK11(X6,X7,X8)),X8) | ~m1_subset_1(X8,u1_struct_0(X6)) | ~l1_waybel_0(X7,X6) | ~v7_waybel_0(X7) | ~v4_orders_2(X7) | v2_struct_0(X7) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6) | ~r3_waybel_9(X6,X7,X8)) )),
% 1.49/0.55    inference(resolution,[],[f111,f126])).
% 1.49/0.55  fof(f126,plain,(
% 1.49/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f39])).
% 1.49/0.55  fof(f39,plain,(
% 1.49/0.55    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.49/0.55    inference(ennf_transformation,[],[f6])).
% 1.49/0.55  fof(f6,axiom,(
% 1.49/0.55    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.49/0.55  fof(f111,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,sK11(X0,X1,X2))) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f70])).
% 1.49/0.55  fof(f137,plain,(
% 1.49/0.55    ~sP0(sK7) | spl13_2),
% 1.49/0.55    inference(avatar_component_clause,[],[f135])).
% 1.49/0.55  fof(f135,plain,(
% 1.49/0.55    spl13_2 <=> sP0(sK7)),
% 1.49/0.55    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).
% 1.49/0.55  fof(f1003,plain,(
% 1.49/0.55    spl13_1 | ~spl13_2),
% 1.49/0.55    inference(avatar_contradiction_clause,[],[f1002])).
% 1.49/0.55  fof(f1002,plain,(
% 1.49/0.55    $false | (spl13_1 | ~spl13_2)),
% 1.49/0.55    inference(subsumption_resolution,[],[f1001,f133])).
% 1.49/0.55  fof(f133,plain,(
% 1.49/0.55    ~v1_compts_1(sK7) | spl13_1),
% 1.49/0.55    inference(avatar_component_clause,[],[f131])).
% 1.49/0.55  fof(f1001,plain,(
% 1.49/0.55    v1_compts_1(sK7) | ~spl13_2),
% 1.49/0.55    inference(subsumption_resolution,[],[f1000,f88])).
% 1.49/0.55  fof(f1000,plain,(
% 1.49/0.55    ~l1_pre_topc(sK7) | v1_compts_1(sK7) | ~spl13_2),
% 1.49/0.55    inference(subsumption_resolution,[],[f999,f87])).
% 1.49/0.55  fof(f999,plain,(
% 1.49/0.55    ~v2_pre_topc(sK7) | ~l1_pre_topc(sK7) | v1_compts_1(sK7) | ~spl13_2),
% 1.49/0.55    inference(subsumption_resolution,[],[f996,f86])).
% 1.49/0.55  fof(f996,plain,(
% 1.49/0.55    v2_struct_0(sK7) | ~v2_pre_topc(sK7) | ~l1_pre_topc(sK7) | v1_compts_1(sK7) | ~spl13_2),
% 1.49/0.55    inference(resolution,[],[f995,f136])).
% 1.49/0.55  fof(f136,plain,(
% 1.49/0.55    sP0(sK7) | ~spl13_2),
% 1.49/0.55    inference(avatar_component_clause,[],[f135])).
% 1.49/0.55  fof(f995,plain,(
% 1.49/0.55    ( ! [X0] : (~sP0(X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v1_compts_1(X0)) )),
% 1.49/0.55    inference(duplicate_literal_removal,[],[f994])).
% 1.49/0.55  fof(f994,plain,(
% 1.49/0.55    ( ! [X0] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP0(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | v1_compts_1(X0)) )),
% 1.49/0.55    inference(resolution,[],[f993,f141])).
% 1.49/0.55  fof(f141,plain,(
% 1.49/0.55    ( ! [X0] : (~sP1(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | v1_compts_1(X0)) )),
% 1.49/0.55    inference(resolution,[],[f106,f97])).
% 1.49/0.55  fof(f97,plain,(
% 1.49/0.55    ( ! [X0] : (~sP2(X0) | ~sP1(X0) | v1_compts_1(X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f62])).
% 1.49/0.55  fof(f62,plain,(
% 1.49/0.55    ! [X0] : (((v1_compts_1(X0) | ~sP1(X0)) & (sP1(X0) | ~v1_compts_1(X0))) | ~sP2(X0))),
% 1.49/0.55    inference(nnf_transformation,[],[f45])).
% 1.49/0.55  fof(f45,plain,(
% 1.49/0.55    ! [X0] : ((v1_compts_1(X0) <=> sP1(X0)) | ~sP2(X0))),
% 1.49/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.49/0.55  fof(f106,plain,(
% 1.49/0.55    ( ! [X0] : (sP2(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f46])).
% 1.49/0.55  fof(f46,plain,(
% 1.49/0.55    ! [X0] : (sP2(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.49/0.55    inference(definition_folding,[],[f24,f45,f44])).
% 1.49/0.55  fof(f44,plain,(
% 1.49/0.55    ! [X0] : (sP1(X0) <=> ! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~r2_hidden(X1,k6_yellow_6(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))),
% 1.49/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.49/0.55  fof(f24,plain,(
% 1.49/0.55    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~r2_hidden(X1,k6_yellow_6(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.49/0.55    inference(flattening,[],[f23])).
% 1.49/0.55  fof(f23,plain,(
% 1.49/0.55    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : ((? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~r2_hidden(X1,k6_yellow_6(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.49/0.55    inference(ennf_transformation,[],[f15])).
% 1.49/0.55  fof(f15,axiom,(
% 1.49/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ~(! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~r3_waybel_9(X0,X1,X2)) & r2_hidden(X1,k6_yellow_6(X0))))))),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_yellow19)).
% 1.49/0.55  fof(f993,plain,(
% 1.49/0.55    ( ! [X0] : (sP1(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP0(X0) | ~l1_pre_topc(X0)) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f992,f103])).
% 1.49/0.55  fof(f103,plain,(
% 1.49/0.55    ( ! [X0] : (l1_waybel_0(sK9(X0),X0) | sP1(X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f67])).
% 1.49/0.55  fof(f67,plain,(
% 1.49/0.55    ! [X0] : ((sP1(X0) | (! [X2] : (~r3_waybel_9(X0,sK9(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(sK9(X0),k6_yellow_6(X0)) & l1_waybel_0(sK9(X0),X0) & v7_waybel_0(sK9(X0)) & v4_orders_2(sK9(X0)) & ~v2_struct_0(sK9(X0)))) & (! [X3] : ((r3_waybel_9(X0,X3,sK10(X0,X3)) & m1_subset_1(sK10(X0,X3),u1_struct_0(X0))) | ~r2_hidden(X3,k6_yellow_6(X0)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | ~sP1(X0)))),
% 1.49/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f64,f66,f65])).
% 1.49/0.55  fof(f65,plain,(
% 1.49/0.55    ! [X0] : (? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(X1,k6_yellow_6(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (~r3_waybel_9(X0,sK9(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(sK9(X0),k6_yellow_6(X0)) & l1_waybel_0(sK9(X0),X0) & v7_waybel_0(sK9(X0)) & v4_orders_2(sK9(X0)) & ~v2_struct_0(sK9(X0))))),
% 1.49/0.55    introduced(choice_axiom,[])).
% 1.49/0.55  fof(f66,plain,(
% 1.49/0.55    ! [X3,X0] : (? [X4] : (r3_waybel_9(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (r3_waybel_9(X0,X3,sK10(X0,X3)) & m1_subset_1(sK10(X0,X3),u1_struct_0(X0))))),
% 1.49/0.55    introduced(choice_axiom,[])).
% 1.49/0.55  fof(f64,plain,(
% 1.49/0.55    ! [X0] : ((sP1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(X1,k6_yellow_6(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (! [X3] : (? [X4] : (r3_waybel_9(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r2_hidden(X3,k6_yellow_6(X0)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | ~sP1(X0)))),
% 1.49/0.55    inference(rectify,[],[f63])).
% 1.49/0.55  fof(f63,plain,(
% 1.49/0.55    ! [X0] : ((sP1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(X1,k6_yellow_6(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~r2_hidden(X1,k6_yellow_6(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~sP1(X0)))),
% 1.49/0.55    inference(nnf_transformation,[],[f44])).
% 1.49/0.55  fof(f992,plain,(
% 1.49/0.55    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP0(X0) | sP1(X0) | ~l1_waybel_0(sK9(X0),X0)) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f991,f100])).
% 1.49/0.55  fof(f100,plain,(
% 1.49/0.55    ( ! [X0] : (~v2_struct_0(sK9(X0)) | sP1(X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f67])).
% 1.49/0.55  fof(f991,plain,(
% 1.49/0.55    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP0(X0) | sP1(X0) | v2_struct_0(sK9(X0)) | ~l1_waybel_0(sK9(X0),X0)) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f990,f101])).
% 1.49/0.55  fof(f101,plain,(
% 1.49/0.55    ( ! [X0] : (v4_orders_2(sK9(X0)) | sP1(X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f67])).
% 1.49/0.55  fof(f990,plain,(
% 1.49/0.55    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP0(X0) | sP1(X0) | ~v4_orders_2(sK9(X0)) | v2_struct_0(sK9(X0)) | ~l1_waybel_0(sK9(X0),X0)) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f989,f102])).
% 1.49/0.55  fof(f102,plain,(
% 1.49/0.55    ( ! [X0] : (v7_waybel_0(sK9(X0)) | sP1(X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f67])).
% 1.49/0.55  fof(f989,plain,(
% 1.49/0.55    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP0(X0) | sP1(X0) | ~v7_waybel_0(sK9(X0)) | ~v4_orders_2(sK9(X0)) | v2_struct_0(sK9(X0)) | ~l1_waybel_0(sK9(X0),X0)) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f988,f93])).
% 1.49/0.55  fof(f988,plain,(
% 1.49/0.55    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP0(X0) | sP1(X0) | ~v7_waybel_0(sK9(X0)) | ~v4_orders_2(sK9(X0)) | v2_struct_0(sK9(X0)) | ~l1_struct_0(X0) | ~l1_waybel_0(sK9(X0),X0)) )),
% 1.49/0.55    inference(duplicate_literal_removal,[],[f987])).
% 1.49/0.55  fof(f987,plain,(
% 1.49/0.55    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP0(X0) | sP1(X0) | ~v7_waybel_0(sK9(X0)) | ~v4_orders_2(sK9(X0)) | v2_struct_0(sK9(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0) | ~sP0(X0) | ~l1_waybel_0(sK9(X0),X0)) )),
% 1.49/0.55    inference(resolution,[],[f986,f166])).
% 1.49/0.55  fof(f166,plain,(
% 1.49/0.55    ( ! [X6,X7] : (~v2_struct_0(sK6(X7,X6)) | ~v7_waybel_0(X6) | ~v4_orders_2(X6) | v2_struct_0(X6) | ~l1_struct_0(X7) | v2_struct_0(X7) | ~sP0(X7) | ~l1_waybel_0(X6,X7)) )),
% 1.49/0.55    inference(resolution,[],[f162,f117])).
% 1.49/0.55  fof(f162,plain,(
% 1.49/0.55    ( ! [X0,X1] : (sP4(X0,sK6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0) | ~sP0(X0)) )),
% 1.49/0.55    inference(duplicate_literal_removal,[],[f161])).
% 1.49/0.55  fof(f161,plain,(
% 1.49/0.55    ( ! [X0,X1] : (sP4(X0,sK6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~sP0(X0)) )),
% 1.49/0.55    inference(resolution,[],[f121,f79])).
% 1.49/0.55  fof(f79,plain,(
% 1.49/0.55    ( ! [X0,X3] : (m2_yellow_6(sK6(X0,X3),X0,X3) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | ~sP0(X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f55])).
% 1.49/0.55  fof(f986,plain,(
% 1.49/0.55    ( ! [X0] : (v2_struct_0(sK6(X0,sK9(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP0(X0) | sP1(X0)) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f985,f103])).
% 1.49/0.55  fof(f985,plain,(
% 1.49/0.55    ( ! [X0] : (v2_struct_0(sK6(X0,sK9(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP0(X0) | sP1(X0) | ~l1_waybel_0(sK9(X0),X0)) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f984,f100])).
% 1.49/0.55  fof(f984,plain,(
% 1.49/0.55    ( ! [X0] : (v2_struct_0(sK6(X0,sK9(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP0(X0) | sP1(X0) | v2_struct_0(sK9(X0)) | ~l1_waybel_0(sK9(X0),X0)) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f983,f101])).
% 1.49/0.55  fof(f983,plain,(
% 1.49/0.55    ( ! [X0] : (v2_struct_0(sK6(X0,sK9(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP0(X0) | sP1(X0) | ~v4_orders_2(sK9(X0)) | v2_struct_0(sK9(X0)) | ~l1_waybel_0(sK9(X0),X0)) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f982,f102])).
% 1.49/0.55  fof(f982,plain,(
% 1.49/0.55    ( ! [X0] : (v2_struct_0(sK6(X0,sK9(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP0(X0) | sP1(X0) | ~v7_waybel_0(sK9(X0)) | ~v4_orders_2(sK9(X0)) | v2_struct_0(sK9(X0)) | ~l1_waybel_0(sK9(X0),X0)) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f981,f93])).
% 1.49/0.55  fof(f981,plain,(
% 1.49/0.55    ( ! [X0] : (v2_struct_0(sK6(X0,sK9(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP0(X0) | sP1(X0) | ~v7_waybel_0(sK9(X0)) | ~v4_orders_2(sK9(X0)) | v2_struct_0(sK9(X0)) | ~l1_struct_0(X0) | ~l1_waybel_0(sK9(X0),X0)) )),
% 1.49/0.55    inference(duplicate_literal_removal,[],[f980])).
% 1.49/0.55  fof(f980,plain,(
% 1.49/0.55    ( ! [X0] : (v2_struct_0(sK6(X0,sK9(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP0(X0) | sP1(X0) | ~v7_waybel_0(sK9(X0)) | ~v4_orders_2(sK9(X0)) | v2_struct_0(sK9(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0) | ~sP0(X0) | ~l1_waybel_0(sK9(X0),X0)) )),
% 1.49/0.55    inference(resolution,[],[f979,f165])).
% 1.49/0.55  fof(f165,plain,(
% 1.49/0.55    ( ! [X4,X5] : (v4_orders_2(sK6(X5,X4)) | ~v7_waybel_0(X4) | ~v4_orders_2(X4) | v2_struct_0(X4) | ~l1_struct_0(X5) | v2_struct_0(X5) | ~sP0(X5) | ~l1_waybel_0(X4,X5)) )),
% 1.49/0.55    inference(resolution,[],[f162,f118])).
% 1.49/0.55  fof(f979,plain,(
% 1.49/0.55    ( ! [X0] : (~v4_orders_2(sK6(X0,sK9(X0))) | v2_struct_0(sK6(X0,sK9(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP0(X0) | sP1(X0)) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f978,f103])).
% 1.49/0.55  fof(f978,plain,(
% 1.49/0.55    ( ! [X0] : (~v4_orders_2(sK6(X0,sK9(X0))) | v2_struct_0(sK6(X0,sK9(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP0(X0) | sP1(X0) | ~l1_waybel_0(sK9(X0),X0)) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f977,f100])).
% 1.49/0.55  fof(f977,plain,(
% 1.49/0.55    ( ! [X0] : (~v4_orders_2(sK6(X0,sK9(X0))) | v2_struct_0(sK6(X0,sK9(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP0(X0) | sP1(X0) | v2_struct_0(sK9(X0)) | ~l1_waybel_0(sK9(X0),X0)) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f976,f101])).
% 1.49/0.55  fof(f976,plain,(
% 1.49/0.55    ( ! [X0] : (~v4_orders_2(sK6(X0,sK9(X0))) | v2_struct_0(sK6(X0,sK9(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP0(X0) | sP1(X0) | ~v4_orders_2(sK9(X0)) | v2_struct_0(sK9(X0)) | ~l1_waybel_0(sK9(X0),X0)) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f975,f102])).
% 1.49/0.55  fof(f975,plain,(
% 1.49/0.55    ( ! [X0] : (~v4_orders_2(sK6(X0,sK9(X0))) | v2_struct_0(sK6(X0,sK9(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP0(X0) | sP1(X0) | ~v7_waybel_0(sK9(X0)) | ~v4_orders_2(sK9(X0)) | v2_struct_0(sK9(X0)) | ~l1_waybel_0(sK9(X0),X0)) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f974,f93])).
% 1.49/0.55  fof(f974,plain,(
% 1.49/0.55    ( ! [X0] : (~v4_orders_2(sK6(X0,sK9(X0))) | v2_struct_0(sK6(X0,sK9(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP0(X0) | sP1(X0) | ~v7_waybel_0(sK9(X0)) | ~v4_orders_2(sK9(X0)) | v2_struct_0(sK9(X0)) | ~l1_struct_0(X0) | ~l1_waybel_0(sK9(X0),X0)) )),
% 1.49/0.55    inference(duplicate_literal_removal,[],[f973])).
% 1.49/0.55  fof(f973,plain,(
% 1.49/0.55    ( ! [X0] : (~v4_orders_2(sK6(X0,sK9(X0))) | v2_struct_0(sK6(X0,sK9(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP0(X0) | sP1(X0) | ~v7_waybel_0(sK9(X0)) | ~v4_orders_2(sK9(X0)) | v2_struct_0(sK9(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0) | ~sP0(X0) | ~l1_waybel_0(sK9(X0),X0)) )),
% 1.49/0.55    inference(resolution,[],[f972,f164])).
% 1.49/0.55  fof(f164,plain,(
% 1.49/0.55    ( ! [X2,X3] : (v7_waybel_0(sK6(X3,X2)) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~l1_struct_0(X3) | v2_struct_0(X3) | ~sP0(X3) | ~l1_waybel_0(X2,X3)) )),
% 1.49/0.55    inference(resolution,[],[f162,f119])).
% 1.49/0.55  fof(f972,plain,(
% 1.49/0.55    ( ! [X0] : (~v7_waybel_0(sK6(X0,sK9(X0))) | ~v4_orders_2(sK6(X0,sK9(X0))) | v2_struct_0(sK6(X0,sK9(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP0(X0) | sP1(X0)) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f971,f103])).
% 1.49/0.55  fof(f971,plain,(
% 1.49/0.55    ( ! [X0] : (~v7_waybel_0(sK6(X0,sK9(X0))) | ~v4_orders_2(sK6(X0,sK9(X0))) | v2_struct_0(sK6(X0,sK9(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP0(X0) | sP1(X0) | ~l1_waybel_0(sK9(X0),X0)) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f970,f100])).
% 1.49/0.55  fof(f970,plain,(
% 1.49/0.55    ( ! [X0] : (~v7_waybel_0(sK6(X0,sK9(X0))) | ~v4_orders_2(sK6(X0,sK9(X0))) | v2_struct_0(sK6(X0,sK9(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP0(X0) | sP1(X0) | v2_struct_0(sK9(X0)) | ~l1_waybel_0(sK9(X0),X0)) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f969,f101])).
% 1.49/0.55  fof(f969,plain,(
% 1.49/0.55    ( ! [X0] : (~v7_waybel_0(sK6(X0,sK9(X0))) | ~v4_orders_2(sK6(X0,sK9(X0))) | v2_struct_0(sK6(X0,sK9(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP0(X0) | sP1(X0) | ~v4_orders_2(sK9(X0)) | v2_struct_0(sK9(X0)) | ~l1_waybel_0(sK9(X0),X0)) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f968,f102])).
% 1.49/0.55  fof(f968,plain,(
% 1.49/0.55    ( ! [X0] : (~v7_waybel_0(sK6(X0,sK9(X0))) | ~v4_orders_2(sK6(X0,sK9(X0))) | v2_struct_0(sK6(X0,sK9(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP0(X0) | sP1(X0) | ~v7_waybel_0(sK9(X0)) | ~v4_orders_2(sK9(X0)) | v2_struct_0(sK9(X0)) | ~l1_waybel_0(sK9(X0),X0)) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f967,f93])).
% 1.49/0.55  fof(f967,plain,(
% 1.49/0.55    ( ! [X0] : (~v7_waybel_0(sK6(X0,sK9(X0))) | ~v4_orders_2(sK6(X0,sK9(X0))) | v2_struct_0(sK6(X0,sK9(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP0(X0) | sP1(X0) | ~v7_waybel_0(sK9(X0)) | ~v4_orders_2(sK9(X0)) | v2_struct_0(sK9(X0)) | ~l1_struct_0(X0) | ~l1_waybel_0(sK9(X0),X0)) )),
% 1.49/0.55    inference(duplicate_literal_removal,[],[f966])).
% 1.49/0.55  fof(f966,plain,(
% 1.49/0.55    ( ! [X0] : (~v7_waybel_0(sK6(X0,sK9(X0))) | ~v4_orders_2(sK6(X0,sK9(X0))) | v2_struct_0(sK6(X0,sK9(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP0(X0) | sP1(X0) | ~v7_waybel_0(sK9(X0)) | ~v4_orders_2(sK9(X0)) | v2_struct_0(sK9(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0) | ~sP0(X0) | ~l1_waybel_0(sK9(X0),X0)) )),
% 1.49/0.55    inference(resolution,[],[f965,f163])).
% 1.49/0.55  fof(f163,plain,(
% 1.49/0.55    ( ! [X0,X1] : (l1_waybel_0(sK6(X1,X0),X1) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~sP0(X1) | ~l1_waybel_0(X0,X1)) )),
% 1.49/0.55    inference(resolution,[],[f162,f120])).
% 1.49/0.55  fof(f965,plain,(
% 1.49/0.55    ( ! [X0] : (~l1_waybel_0(sK6(X0,sK9(X0)),X0) | ~v7_waybel_0(sK6(X0,sK9(X0))) | ~v4_orders_2(sK6(X0,sK9(X0))) | v2_struct_0(sK6(X0,sK9(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP0(X0) | sP1(X0)) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f964,f100])).
% 1.49/0.55  fof(f964,plain,(
% 1.49/0.55    ( ! [X0] : (~l1_waybel_0(sK6(X0,sK9(X0)),X0) | ~v7_waybel_0(sK6(X0,sK9(X0))) | ~v4_orders_2(sK6(X0,sK9(X0))) | v2_struct_0(sK6(X0,sK9(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP0(X0) | sP1(X0) | v2_struct_0(sK9(X0))) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f963,f101])).
% 1.49/0.55  fof(f963,plain,(
% 1.49/0.55    ( ! [X0] : (~l1_waybel_0(sK6(X0,sK9(X0)),X0) | ~v7_waybel_0(sK6(X0,sK9(X0))) | ~v4_orders_2(sK6(X0,sK9(X0))) | v2_struct_0(sK6(X0,sK9(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP0(X0) | sP1(X0) | ~v4_orders_2(sK9(X0)) | v2_struct_0(sK9(X0))) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f962,f102])).
% 1.49/0.55  fof(f962,plain,(
% 1.49/0.55    ( ! [X0] : (~l1_waybel_0(sK6(X0,sK9(X0)),X0) | ~v7_waybel_0(sK6(X0,sK9(X0))) | ~v4_orders_2(sK6(X0,sK9(X0))) | v2_struct_0(sK6(X0,sK9(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP0(X0) | sP1(X0) | ~v7_waybel_0(sK9(X0)) | ~v4_orders_2(sK9(X0)) | v2_struct_0(sK9(X0))) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f961,f103])).
% 1.49/0.55  fof(f961,plain,(
% 1.49/0.55    ( ! [X0] : (~l1_waybel_0(sK6(X0,sK9(X0)),X0) | ~v7_waybel_0(sK6(X0,sK9(X0))) | ~v4_orders_2(sK6(X0,sK9(X0))) | v2_struct_0(sK6(X0,sK9(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP0(X0) | sP1(X0) | ~l1_waybel_0(sK9(X0),X0) | ~v7_waybel_0(sK9(X0)) | ~v4_orders_2(sK9(X0)) | v2_struct_0(sK9(X0))) )),
% 1.49/0.55    inference(duplicate_literal_removal,[],[f960])).
% 1.49/0.55  fof(f960,plain,(
% 1.49/0.55    ( ! [X0] : (~l1_waybel_0(sK6(X0,sK9(X0)),X0) | ~v7_waybel_0(sK6(X0,sK9(X0))) | ~v4_orders_2(sK6(X0,sK9(X0))) | v2_struct_0(sK6(X0,sK9(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP0(X0) | sP1(X0) | ~l1_waybel_0(sK9(X0),X0) | ~v7_waybel_0(sK9(X0)) | ~v4_orders_2(sK9(X0)) | v2_struct_0(sK9(X0)) | ~sP0(X0)) )),
% 1.49/0.55    inference(resolution,[],[f956,f80])).
% 1.49/0.55  fof(f80,plain,(
% 1.49/0.55    ( ! [X0,X3] : (v3_yellow_6(sK6(X0,X3),X0) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | ~sP0(X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f55])).
% 1.49/0.55  fof(f956,plain,(
% 1.49/0.55    ( ! [X8] : (~v3_yellow_6(sK6(X8,sK9(X8)),X8) | ~l1_waybel_0(sK6(X8,sK9(X8)),X8) | ~v7_waybel_0(sK6(X8,sK9(X8))) | ~v4_orders_2(sK6(X8,sK9(X8))) | v2_struct_0(sK6(X8,sK9(X8))) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~sP0(X8) | sP1(X8)) )),
% 1.49/0.55    inference(trivial_inequality_removal,[],[f955])).
% 1.49/0.55  fof(f955,plain,(
% 1.49/0.55    ( ! [X8] : (k1_xboole_0 != k1_xboole_0 | ~v3_yellow_6(sK6(X8,sK9(X8)),X8) | ~l1_waybel_0(sK6(X8,sK9(X8)),X8) | ~v7_waybel_0(sK6(X8,sK9(X8))) | ~v4_orders_2(sK6(X8,sK9(X8))) | v2_struct_0(sK6(X8,sK9(X8))) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~sP0(X8) | sP1(X8)) )),
% 1.49/0.55    inference(duplicate_literal_removal,[],[f944])).
% 1.49/0.55  fof(f944,plain,(
% 1.49/0.55    ( ! [X8] : (k1_xboole_0 != k1_xboole_0 | ~v3_yellow_6(sK6(X8,sK9(X8)),X8) | ~l1_waybel_0(sK6(X8,sK9(X8)),X8) | ~v7_waybel_0(sK6(X8,sK9(X8))) | ~v4_orders_2(sK6(X8,sK9(X8))) | v2_struct_0(sK6(X8,sK9(X8))) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~sP0(X8) | ~l1_waybel_0(sK6(X8,sK9(X8)),X8) | ~v7_waybel_0(sK6(X8,sK9(X8))) | ~v4_orders_2(sK6(X8,sK9(X8))) | v2_struct_0(sK6(X8,sK9(X8))) | ~l1_pre_topc(X8) | v2_struct_0(X8) | ~v2_pre_topc(X8) | sP1(X8)) )),
% 1.49/0.55    inference(superposition,[],[f107,f939])).
% 1.49/0.55  fof(f939,plain,(
% 1.49/0.55    ( ! [X2] : (k1_xboole_0 = k10_yellow_6(X2,sK6(X2,sK9(X2))) | ~sP0(X2) | ~l1_waybel_0(sK6(X2,sK9(X2)),X2) | ~v7_waybel_0(sK6(X2,sK9(X2))) | ~v4_orders_2(sK6(X2,sK9(X2))) | v2_struct_0(sK6(X2,sK9(X2))) | ~l1_pre_topc(X2) | v2_struct_0(X2) | ~v2_pre_topc(X2) | sP1(X2)) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f933,f92])).
% 1.49/0.55  fof(f92,plain,(
% 1.49/0.55    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.49/0.55    inference(cnf_transformation,[],[f3])).
% 1.49/0.55  fof(f3,axiom,(
% 1.49/0.55    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.49/0.55  fof(f933,plain,(
% 1.49/0.55    ( ! [X2] : (sP1(X2) | ~sP0(X2) | ~l1_waybel_0(sK6(X2,sK9(X2)),X2) | ~v7_waybel_0(sK6(X2,sK9(X2))) | ~v4_orders_2(sK6(X2,sK9(X2))) | v2_struct_0(sK6(X2,sK9(X2))) | ~l1_pre_topc(X2) | v2_struct_0(X2) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X2))) | ~v2_pre_topc(X2) | k1_xboole_0 = k10_yellow_6(X2,sK6(X2,sK9(X2)))) )),
% 1.49/0.55    inference(resolution,[],[f908,f143])).
% 1.49/0.55  fof(f143,plain,(
% 1.49/0.55    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.49/0.55    inference(resolution,[],[f125,f91])).
% 1.49/0.55  fof(f125,plain,(
% 1.49/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f78])).
% 1.49/0.55  fof(f78,plain,(
% 1.49/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.49/0.55    inference(flattening,[],[f77])).
% 1.49/0.55  fof(f77,plain,(
% 1.49/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.49/0.55    inference(nnf_transformation,[],[f1])).
% 1.49/0.55  fof(f1,axiom,(
% 1.49/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.49/0.55  fof(f908,plain,(
% 1.49/0.55    ( ! [X0,X1] : (r1_tarski(k10_yellow_6(X0,sK6(X0,sK9(X0))),X1) | sP1(X0) | ~sP0(X0) | ~l1_waybel_0(sK6(X0,sK9(X0)),X0) | ~v7_waybel_0(sK6(X0,sK9(X0))) | ~v4_orders_2(sK6(X0,sK9(X0))) | v2_struct_0(sK6(X0,sK9(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0)) )),
% 1.49/0.55    inference(duplicate_literal_removal,[],[f905])).
% 1.49/0.55  fof(f905,plain,(
% 1.49/0.55    ( ! [X0,X1] : (v2_struct_0(X0) | sP1(X0) | ~sP0(X0) | ~l1_waybel_0(sK6(X0,sK9(X0)),X0) | ~v7_waybel_0(sK6(X0,sK9(X0))) | ~v4_orders_2(sK6(X0,sK9(X0))) | v2_struct_0(sK6(X0,sK9(X0))) | ~l1_pre_topc(X0) | r1_tarski(k10_yellow_6(X0,sK6(X0,sK9(X0))),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_waybel_0(sK6(X0,sK9(X0)),X0) | ~v7_waybel_0(sK6(X0,sK9(X0))) | ~v4_orders_2(sK6(X0,sK9(X0))) | v2_struct_0(sK6(X0,sK9(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.49/0.55    inference(resolution,[],[f687,f122])).
% 1.49/0.55  fof(f122,plain,(
% 1.49/0.55    ( ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f38])).
% 1.49/0.55  fof(f38,plain,(
% 1.49/0.55    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.49/0.55    inference(flattening,[],[f37])).
% 1.49/0.55  fof(f37,plain,(
% 1.49/0.55    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.49/0.55    inference(ennf_transformation,[],[f8])).
% 1.49/0.55  fof(f8,axiom,(
% 1.49/0.55    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_yellow_6)).
% 1.49/0.55  fof(f687,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(k10_yellow_6(X0,sK6(X0,sK9(X0))),k1_zfmisc_1(X2)) | v2_struct_0(X0) | sP1(X0) | ~sP0(X0) | ~l1_waybel_0(sK6(X0,sK9(X0)),X0) | ~v7_waybel_0(sK6(X0,sK9(X0))) | ~v4_orders_2(sK6(X0,sK9(X0))) | v2_struct_0(sK6(X0,sK9(X0))) | ~l1_pre_topc(X0) | r1_tarski(k10_yellow_6(X0,sK6(X0,sK9(X0))),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v2_pre_topc(X0)) )),
% 1.49/0.55    inference(resolution,[],[f686,f116])).
% 1.49/0.55  fof(f116,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (sP3(X2,X1,X0) | r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.49/0.55    inference(cnf_transformation,[],[f48])).
% 1.49/0.55  fof(f48,plain,(
% 1.49/0.55    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | sP3(X2,X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.49/0.55    inference(definition_folding,[],[f34,f47])).
% 1.49/0.55  fof(f47,plain,(
% 1.49/0.55    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~sP3(X2,X1,X0))),
% 1.49/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 1.49/0.55  fof(f34,plain,(
% 1.49/0.55    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.49/0.55    inference(flattening,[],[f33])).
% 1.49/0.55  fof(f33,plain,(
% 1.49/0.55    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.49/0.55    inference(ennf_transformation,[],[f4])).
% 1.49/0.55  fof(f4,axiom,(
% 1.49/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).
% 1.49/0.55  fof(f686,plain,(
% 1.49/0.55    ( ! [X8,X7,X9] : (~sP3(X7,k10_yellow_6(X8,sK6(X8,sK9(X8))),X9) | ~v2_pre_topc(X8) | v2_struct_0(X8) | sP1(X8) | ~sP0(X8) | ~l1_waybel_0(sK6(X8,sK9(X8)),X8) | ~v7_waybel_0(sK6(X8,sK9(X8))) | ~v4_orders_2(sK6(X8,sK9(X8))) | v2_struct_0(sK6(X8,sK9(X8))) | ~l1_pre_topc(X8)) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f251,f175])).
% 1.49/0.55  fof(f175,plain,(
% 1.49/0.55    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK12(X2,k10_yellow_6(X1,X0),X3),u1_struct_0(X1)) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,X1) | ~sP3(X2,k10_yellow_6(X1,X0),X3)) )),
% 1.49/0.55    inference(resolution,[],[f168,f114])).
% 1.49/0.55  fof(f114,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (r2_hidden(sK12(X0,X1,X2),X1) | ~sP3(X0,X1,X2)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f74])).
% 1.49/0.55  fof(f74,plain,(
% 1.49/0.55    ! [X0,X1,X2] : ((~r2_hidden(sK12(X0,X1,X2),X0) & r2_hidden(sK12(X0,X1,X2),X1) & m1_subset_1(sK12(X0,X1,X2),X2)) | ~sP3(X0,X1,X2))),
% 1.49/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f72,f73])).
% 1.49/0.55  fof(f73,plain,(
% 1.49/0.55    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X0) & r2_hidden(X3,X1) & m1_subset_1(X3,X2)) => (~r2_hidden(sK12(X0,X1,X2),X0) & r2_hidden(sK12(X0,X1,X2),X1) & m1_subset_1(sK12(X0,X1,X2),X2)))),
% 1.49/0.55    introduced(choice_axiom,[])).
% 1.49/0.55  fof(f72,plain,(
% 1.49/0.55    ! [X0,X1,X2] : (? [X3] : (~r2_hidden(X3,X0) & r2_hidden(X3,X1) & m1_subset_1(X3,X2)) | ~sP3(X0,X1,X2))),
% 1.49/0.55    inference(rectify,[],[f71])).
% 1.49/0.55  fof(f71,plain,(
% 1.49/0.55    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~sP3(X2,X1,X0))),
% 1.49/0.55    inference(nnf_transformation,[],[f47])).
% 1.49/0.55  fof(f168,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X2,k10_yellow_6(X1,X0)) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X0,X1)) )),
% 1.49/0.55    inference(resolution,[],[f122,f127])).
% 1.49/0.55  fof(f127,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f41])).
% 1.49/0.55  fof(f41,plain,(
% 1.49/0.55    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.49/0.55    inference(flattening,[],[f40])).
% 1.49/0.55  fof(f40,plain,(
% 1.49/0.55    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.49/0.55    inference(ennf_transformation,[],[f5])).
% 1.49/0.55  fof(f5,axiom,(
% 1.49/0.55    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 1.49/0.55  fof(f251,plain,(
% 1.49/0.55    ( ! [X8,X7,X9] : (~m1_subset_1(sK12(X7,k10_yellow_6(X8,sK6(X8,sK9(X8))),X9),u1_struct_0(X8)) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | sP1(X8) | ~sP0(X8) | ~l1_waybel_0(sK6(X8,sK9(X8)),X8) | ~v7_waybel_0(sK6(X8,sK9(X8))) | ~v4_orders_2(sK6(X8,sK9(X8))) | v2_struct_0(sK6(X8,sK9(X8))) | ~sP3(X7,k10_yellow_6(X8,sK6(X8,sK9(X8))),X9)) )),
% 1.49/0.55    inference(duplicate_literal_removal,[],[f250])).
% 1.49/0.55  fof(f250,plain,(
% 1.49/0.55    ( ! [X8,X7,X9] : (~m1_subset_1(sK12(X7,k10_yellow_6(X8,sK6(X8,sK9(X8))),X9),u1_struct_0(X8)) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | sP1(X8) | ~sP0(X8) | ~l1_waybel_0(sK6(X8,sK9(X8)),X8) | ~v7_waybel_0(sK6(X8,sK9(X8))) | ~v4_orders_2(sK6(X8,sK9(X8))) | v2_struct_0(sK6(X8,sK9(X8))) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~sP3(X7,k10_yellow_6(X8,sK6(X8,sK9(X8))),X9)) )),
% 1.49/0.55    inference(resolution,[],[f245,f179])).
% 1.49/0.55  fof(f179,plain,(
% 1.49/0.55    ( ! [X2,X0,X3,X1] : (r3_waybel_9(X0,X1,sK12(X2,k10_yellow_6(X0,X1),X3)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP3(X2,k10_yellow_6(X0,X1),X3)) )),
% 1.49/0.55    inference(resolution,[],[f178,f114])).
% 1.49/0.55  fof(f178,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X2,k10_yellow_6(X0,X1)) | r3_waybel_9(X0,X1,X2) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f109,f168])).
% 1.49/0.55  fof(f109,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f28])).
% 1.49/0.55  fof(f28,plain,(
% 1.49/0.55    ! [X0] : (! [X1] : (! [X2] : (r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.49/0.55    inference(flattening,[],[f27])).
% 1.49/0.55  fof(f27,plain,(
% 1.49/0.55    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.49/0.55    inference(ennf_transformation,[],[f11])).
% 1.49/0.55  fof(f11,axiom,(
% 1.49/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,X1)) => r3_waybel_9(X0,X1,X2)))))),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_waybel_9)).
% 1.49/0.55  fof(f245,plain,(
% 1.49/0.55    ( ! [X0,X1] : (~r3_waybel_9(X1,sK6(X1,sK9(X1)),X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | sP1(X1) | ~sP0(X1)) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f244,f100])).
% 1.49/0.55  fof(f244,plain,(
% 1.49/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~r3_waybel_9(X1,sK6(X1,sK9(X1)),X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | sP1(X1) | v2_struct_0(sK9(X1)) | ~sP0(X1)) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f243,f101])).
% 1.49/0.55  fof(f243,plain,(
% 1.49/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~r3_waybel_9(X1,sK6(X1,sK9(X1)),X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | sP1(X1) | ~v4_orders_2(sK9(X1)) | v2_struct_0(sK9(X1)) | ~sP0(X1)) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f242,f102])).
% 1.49/0.55  fof(f242,plain,(
% 1.49/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~r3_waybel_9(X1,sK6(X1,sK9(X1)),X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | sP1(X1) | ~v7_waybel_0(sK9(X1)) | ~v4_orders_2(sK9(X1)) | v2_struct_0(sK9(X1)) | ~sP0(X1)) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f239,f103])).
% 1.49/0.55  fof(f239,plain,(
% 1.49/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~r3_waybel_9(X1,sK6(X1,sK9(X1)),X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | sP1(X1) | ~l1_waybel_0(sK9(X1),X1) | ~v7_waybel_0(sK9(X1)) | ~v4_orders_2(sK9(X1)) | v2_struct_0(sK9(X1)) | ~sP0(X1)) )),
% 1.49/0.55    inference(resolution,[],[f238,f79])).
% 1.49/0.55  fof(f238,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (~m2_yellow_6(X1,X0,sK9(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | sP1(X0)) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f237,f100])).
% 1.49/0.55  fof(f237,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m2_yellow_6(X1,X0,sK9(X0)) | v2_struct_0(sK9(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | sP1(X0)) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f236,f101])).
% 1.49/0.55  fof(f236,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m2_yellow_6(X1,X0,sK9(X0)) | ~v4_orders_2(sK9(X0)) | v2_struct_0(sK9(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | sP1(X0)) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f235,f102])).
% 1.49/0.55  fof(f235,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m2_yellow_6(X1,X0,sK9(X0)) | ~v7_waybel_0(sK9(X0)) | ~v4_orders_2(sK9(X0)) | v2_struct_0(sK9(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | sP1(X0)) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f234,f103])).
% 1.49/0.55  fof(f234,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m2_yellow_6(X1,X0,sK9(X0)) | ~l1_waybel_0(sK9(X0),X0) | ~v7_waybel_0(sK9(X0)) | ~v4_orders_2(sK9(X0)) | v2_struct_0(sK9(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | sP1(X0)) )),
% 1.49/0.55    inference(duplicate_literal_removal,[],[f233])).
% 1.49/0.55  fof(f233,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m2_yellow_6(X1,X0,sK9(X0)) | ~l1_waybel_0(sK9(X0),X0) | ~v7_waybel_0(sK9(X0)) | ~v4_orders_2(sK9(X0)) | v2_struct_0(sK9(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | sP1(X0) | ~m1_subset_1(X2,u1_struct_0(X0))) )),
% 1.49/0.55    inference(resolution,[],[f112,f105])).
% 1.49/0.55  fof(f105,plain,(
% 1.49/0.55    ( ! [X2,X0] : (~r3_waybel_9(X0,sK9(X0),X2) | sP1(X0) | ~m1_subset_1(X2,u1_struct_0(X0))) )),
% 1.49/0.55    inference(cnf_transformation,[],[f67])).
% 1.49/0.55  fof(f112,plain,(
% 1.49/0.55    ( ! [X2,X0,X3,X1] : (r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f32])).
% 1.49/0.55  fof(f32,plain,(
% 1.49/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.49/0.55    inference(flattening,[],[f31])).
% 1.49/0.55  fof(f31,plain,(
% 1.49/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.49/0.55    inference(ennf_transformation,[],[f12])).
% 1.49/0.55  fof(f12,axiom,(
% 1.49/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_waybel_9(X0,X2,X3) => r3_waybel_9(X0,X1,X3))))))),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_waybel_9)).
% 1.49/0.55  fof(f107,plain,(
% 1.49/0.55    ( ! [X0,X1] : (k1_xboole_0 != k10_yellow_6(X0,X1) | ~v3_yellow_6(X1,X0) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f68])).
% 1.49/0.55  fof(f139,plain,(
% 1.49/0.55    spl13_1 | spl13_2),
% 1.49/0.55    inference(avatar_split_clause,[],[f89,f135,f131])).
% 1.49/0.55  fof(f89,plain,(
% 1.49/0.55    sP0(sK7) | v1_compts_1(sK7)),
% 1.49/0.55    inference(cnf_transformation,[],[f59])).
% 1.49/0.55  fof(f138,plain,(
% 1.49/0.55    ~spl13_1 | ~spl13_2),
% 1.49/0.55    inference(avatar_split_clause,[],[f90,f135,f131])).
% 1.49/0.55  fof(f90,plain,(
% 1.49/0.55    ~sP0(sK7) | ~v1_compts_1(sK7)),
% 1.49/0.55    inference(cnf_transformation,[],[f59])).
% 1.49/0.55  % SZS output end Proof for theBenchmark
% 1.49/0.55  % (3165)------------------------------
% 1.49/0.55  % (3165)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.55  % (3165)Termination reason: Refutation
% 1.49/0.55  
% 1.49/0.55  % (3165)Memory used [KB]: 6652
% 1.49/0.55  % (3165)Time elapsed: 0.112 s
% 1.49/0.55  % (3165)------------------------------
% 1.49/0.55  % (3165)------------------------------
% 1.49/0.55  % (3155)Success in time 0.197 s
%------------------------------------------------------------------------------
