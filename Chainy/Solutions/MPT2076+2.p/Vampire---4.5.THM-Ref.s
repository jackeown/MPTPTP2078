%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT2076+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:40 EST 2020

% Result     : Theorem 1.04s
% Output     : Refutation 1.04s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 687 expanded)
%              Number of leaves         :   11 ( 210 expanded)
%              Depth                    :   13
%              Number of atoms          :  398 (5629 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5054,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f4818,f4820,f4975,f5053])).

fof(f5053,plain,
    ( ~ spl31_1
    | spl31_2 ),
    inference(avatar_contradiction_clause,[],[f5048])).

fof(f5048,plain,
    ( $false
    | ~ spl31_1
    | spl31_2 ),
    inference(unit_resulting_resolution,[],[f4816,f5006,f5007,f4701])).

fof(f4701,plain,(
    ! [X2,X0] :
      ( sP0(X0)
      | ~ r3_waybel_9(X0,sK7(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f4633])).

fof(f4633,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( ! [X2] :
              ( ~ r3_waybel_9(X0,sK7(X0),X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & r2_hidden(sK7(X0),k6_yellow_6(X0))
          & l1_waybel_0(sK7(X0),X0)
          & v7_waybel_0(sK7(X0))
          & v4_orders_2(sK7(X0))
          & ~ v2_struct_0(sK7(X0)) ) )
      & ( ! [X3] :
            ( ( r3_waybel_9(X0,X3,sK8(X0,X3))
              & m1_subset_1(sK8(X0,X3),u1_struct_0(X0)) )
            | ~ r2_hidden(X3,k6_yellow_6(X0))
            | ~ l1_waybel_0(X3,X0)
            | ~ v7_waybel_0(X3)
            | ~ v4_orders_2(X3)
            | v2_struct_0(X3) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f4630,f4632,f4631])).

fof(f4631,plain,(
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
            ( ~ r3_waybel_9(X0,sK7(X0),X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & r2_hidden(sK7(X0),k6_yellow_6(X0))
        & l1_waybel_0(sK7(X0),X0)
        & v7_waybel_0(sK7(X0))
        & v4_orders_2(sK7(X0))
        & ~ v2_struct_0(sK7(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f4632,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( r3_waybel_9(X0,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X3,sK8(X0,X3))
        & m1_subset_1(sK8(X0,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f4630,plain,(
    ! [X0] :
      ( ( sP0(X0)
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
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f4629])).

fof(f4629,plain,(
    ! [X0] :
      ( ( sP0(X0)
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
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f4618])).

fof(f4618,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1] :
          ( ? [X2] :
              ( r3_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ r2_hidden(X1,k6_yellow_6(X0))
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f5007,plain,
    ( r3_waybel_9(sK9,sK7(sK9),sK16(sK9,sK7(sK9)))
    | ~ spl31_1
    | spl31_2 ),
    inference(unit_resulting_resolution,[],[f4702,f4703,f4704,f4813,f4977,f4978,f4979,f4980,f4745])).

fof(f4745,plain,(
    ! [X0,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | r3_waybel_9(X0,X1,sK16(X0,X1))
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4659])).

fof(f4659,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r3_waybel_9(X0,X1,sK16(X0,X1))
            & m1_subset_1(sK16(X0,X1),u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16])],[f4578,f4658])).

fof(f4658,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r3_waybel_9(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X1,sK16(X0,X1))
        & m1_subset_1(sK16(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f4578,plain,(
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
    inference(flattening,[],[f4577])).

fof(f4577,plain,(
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
    inference(ennf_transformation,[],[f4520])).

fof(f4520,axiom,(
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

fof(f4980,plain,
    ( l1_waybel_0(sK7(sK9),sK9)
    | spl31_2 ),
    inference(unit_resulting_resolution,[],[f4816,f4699])).

fof(f4699,plain,(
    ! [X0] :
      ( sP0(X0)
      | l1_waybel_0(sK7(X0),X0) ) ),
    inference(cnf_transformation,[],[f4633])).

fof(f4979,plain,
    ( v7_waybel_0(sK7(sK9))
    | spl31_2 ),
    inference(unit_resulting_resolution,[],[f4816,f4698])).

fof(f4698,plain,(
    ! [X0] :
      ( v7_waybel_0(sK7(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f4633])).

fof(f4978,plain,
    ( v4_orders_2(sK7(sK9))
    | spl31_2 ),
    inference(unit_resulting_resolution,[],[f4816,f4697])).

fof(f4697,plain,(
    ! [X0] :
      ( v4_orders_2(sK7(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f4633])).

fof(f4977,plain,
    ( ~ v2_struct_0(sK7(sK9))
    | spl31_2 ),
    inference(unit_resulting_resolution,[],[f4816,f4696])).

fof(f4696,plain,(
    ! [X0] :
      ( ~ v2_struct_0(sK7(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f4633])).

fof(f4813,plain,
    ( v1_compts_1(sK9)
    | ~ spl31_1 ),
    inference(avatar_component_clause,[],[f4811])).

fof(f4811,plain,
    ( spl31_1
  <=> v1_compts_1(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1])])).

fof(f4704,plain,(
    l1_pre_topc(sK9) ),
    inference(cnf_transformation,[],[f4637])).

fof(f4637,plain,
    ( ( ~ sP0(sK9)
      | ~ v1_compts_1(sK9) )
    & ( sP0(sK9)
      | v1_compts_1(sK9) )
    & l1_pre_topc(sK9)
    & v2_pre_topc(sK9)
    & ~ v2_struct_0(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f4635,f4636])).

fof(f4636,plain,
    ( ? [X0] :
        ( ( ~ sP0(X0)
          | ~ v1_compts_1(X0) )
        & ( sP0(X0)
          | v1_compts_1(X0) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ( ~ sP0(sK9)
        | ~ v1_compts_1(sK9) )
      & ( sP0(sK9)
        | v1_compts_1(sK9) )
      & l1_pre_topc(sK9)
      & v2_pre_topc(sK9)
      & ~ v2_struct_0(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f4635,plain,(
    ? [X0] :
      ( ( ~ sP0(X0)
        | ~ v1_compts_1(X0) )
      & ( sP0(X0)
        | v1_compts_1(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f4634])).

fof(f4634,plain,(
    ? [X0] :
      ( ( ~ sP0(X0)
        | ~ v1_compts_1(X0) )
      & ( sP0(X0)
        | v1_compts_1(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f4619])).

fof(f4619,plain,(
    ? [X0] :
      ( ( v1_compts_1(X0)
      <~> sP0(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f4562,f4618])).

fof(f4562,plain,(
    ? [X0] :
      ( ( v1_compts_1(X0)
      <~> ! [X1] :
            ( ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r2_hidden(X1,k6_yellow_6(X0))
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f4561])).

fof(f4561,plain,(
    ? [X0] :
      ( ( v1_compts_1(X0)
      <~> ! [X1] :
            ( ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r2_hidden(X1,k6_yellow_6(X0))
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4552])).

fof(f4552,negated_conjecture,(
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
             => ~ ( ! [X2] :
                      ( m1_subset_1(X2,u1_struct_0(X0))
                     => ~ r3_waybel_9(X0,X1,X2) )
                  & r2_hidden(X1,k6_yellow_6(X0)) ) ) ) ) ),
    inference(negated_conjecture,[],[f4551])).

fof(f4551,conjecture,(
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

fof(f4703,plain,(
    v2_pre_topc(sK9) ),
    inference(cnf_transformation,[],[f4637])).

fof(f4702,plain,(
    ~ v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f4637])).

fof(f5006,plain,
    ( m1_subset_1(sK16(sK9,sK7(sK9)),u1_struct_0(sK9))
    | ~ spl31_1
    | spl31_2 ),
    inference(unit_resulting_resolution,[],[f4702,f4703,f4704,f4813,f4977,f4978,f4979,f4980,f4744])).

fof(f4744,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK16(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4659])).

fof(f4816,plain,
    ( ~ sP0(sK9)
    | spl31_2 ),
    inference(avatar_component_clause,[],[f4815])).

fof(f4815,plain,
    ( spl31_2
  <=> sP0(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_2])])).

fof(f4975,plain,
    ( spl31_1
    | ~ spl31_2 ),
    inference(avatar_contradiction_clause,[],[f4970])).

fof(f4970,plain,
    ( $false
    | spl31_1
    | ~ spl31_2 ),
    inference(unit_resulting_resolution,[],[f4702,f4703,f4704,f4812,f4859,f4860,f4782])).

fof(f4782,plain,(
    ! [X2,X0] :
      ( v1_compts_1(X0)
      | ~ r3_waybel_9(X0,sK27(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4686])).

fof(f4686,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ( ! [X2] :
            ( ~ r3_waybel_9(X0,sK27(X0),X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & r2_hidden(sK27(X0),k6_yellow_6(X0))
        & l1_waybel_0(sK27(X0),X0)
        & v7_waybel_0(sK27(X0))
        & v4_orders_2(sK27(X0))
        & ~ v2_struct_0(sK27(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK27])],[f4603,f4685])).

fof(f4685,plain,(
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
            ( ~ r3_waybel_9(X0,sK27(X0),X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & r2_hidden(sK27(X0),k6_yellow_6(X0))
        & l1_waybel_0(sK27(X0),X0)
        & v7_waybel_0(sK27(X0))
        & v4_orders_2(sK27(X0))
        & ~ v2_struct_0(sK27(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f4603,plain,(
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
    inference(flattening,[],[f4602])).

fof(f4602,plain,(
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
    inference(ennf_transformation,[],[f4521])).

fof(f4521,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_yellow19)).

fof(f4860,plain,
    ( r3_waybel_9(sK9,sK27(sK9),sK8(sK9,sK27(sK9)))
    | spl31_1
    | ~ spl31_2 ),
    inference(unit_resulting_resolution,[],[f4817,f4822,f4823,f4824,f4825,f4826,f4695])).

fof(f4695,plain,(
    ! [X0,X3] :
      ( ~ sP0(X0)
      | ~ r2_hidden(X3,k6_yellow_6(X0))
      | ~ l1_waybel_0(X3,X0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | r3_waybel_9(X0,X3,sK8(X0,X3)) ) ),
    inference(cnf_transformation,[],[f4633])).

fof(f4826,plain,
    ( r2_hidden(sK27(sK9),k6_yellow_6(sK9))
    | spl31_1 ),
    inference(unit_resulting_resolution,[],[f4702,f4703,f4704,f4812,f4781])).

fof(f4781,plain,(
    ! [X0] :
      ( r2_hidden(sK27(X0),k6_yellow_6(X0))
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4686])).

fof(f4825,plain,
    ( l1_waybel_0(sK27(sK9),sK9)
    | spl31_1 ),
    inference(unit_resulting_resolution,[],[f4702,f4703,f4704,f4812,f4780])).

fof(f4780,plain,(
    ! [X0] :
      ( l1_waybel_0(sK27(X0),X0)
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4686])).

fof(f4824,plain,
    ( v7_waybel_0(sK27(sK9))
    | spl31_1 ),
    inference(unit_resulting_resolution,[],[f4702,f4703,f4704,f4812,f4779])).

fof(f4779,plain,(
    ! [X0] :
      ( v7_waybel_0(sK27(X0))
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4686])).

fof(f4823,plain,
    ( v4_orders_2(sK27(sK9))
    | spl31_1 ),
    inference(unit_resulting_resolution,[],[f4702,f4703,f4704,f4812,f4778])).

fof(f4778,plain,(
    ! [X0] :
      ( v4_orders_2(sK27(X0))
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4686])).

fof(f4822,plain,
    ( ~ v2_struct_0(sK27(sK9))
    | spl31_1 ),
    inference(unit_resulting_resolution,[],[f4702,f4703,f4704,f4812,f4777])).

fof(f4777,plain,(
    ! [X0] :
      ( ~ v2_struct_0(sK27(X0))
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4686])).

fof(f4817,plain,
    ( sP0(sK9)
    | ~ spl31_2 ),
    inference(avatar_component_clause,[],[f4815])).

fof(f4859,plain,
    ( m1_subset_1(sK8(sK9,sK27(sK9)),u1_struct_0(sK9))
    | spl31_1
    | ~ spl31_2 ),
    inference(unit_resulting_resolution,[],[f4817,f4822,f4823,f4824,f4825,f4826,f4694])).

fof(f4694,plain,(
    ! [X0,X3] :
      ( m1_subset_1(sK8(X0,X3),u1_struct_0(X0))
      | ~ r2_hidden(X3,k6_yellow_6(X0))
      | ~ l1_waybel_0(X3,X0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f4633])).

fof(f4812,plain,
    ( ~ v1_compts_1(sK9)
    | spl31_1 ),
    inference(avatar_component_clause,[],[f4811])).

fof(f4820,plain,
    ( ~ spl31_1
    | ~ spl31_2 ),
    inference(avatar_split_clause,[],[f4706,f4815,f4811])).

fof(f4706,plain,
    ( ~ sP0(sK9)
    | ~ v1_compts_1(sK9) ),
    inference(cnf_transformation,[],[f4637])).

fof(f4818,plain,
    ( spl31_1
    | spl31_2 ),
    inference(avatar_split_clause,[],[f4705,f4815,f4811])).

fof(f4705,plain,
    ( sP0(sK9)
    | v1_compts_1(sK9) ),
    inference(cnf_transformation,[],[f4637])).
%------------------------------------------------------------------------------
