%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT2076+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:08 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 640 expanded)
%              Number of leaves         :   15 ( 203 expanded)
%              Depth                    :   27
%              Number of atoms          :  768 (7631 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f147,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f77,f83,f89,f95,f123,f129,f146])).

fof(f146,plain,
    ( spl5_1
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(avatar_contradiction_clause,[],[f145])).

% (16318)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% (16308)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% (16313)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
fof(f145,plain,
    ( $false
    | spl5_1
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f144,f22])).

fof(f22,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ( ( ! [X2] :
            ( ~ r3_waybel_9(sK0,sK1,X2)
            | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
        & r2_hidden(sK1,k6_yellow_6(sK0))
        & l1_waybel_0(sK1,sK0)
        & v7_waybel_0(sK1)
        & v4_orders_2(sK1)
        & ~ v2_struct_0(sK1) )
      | ~ v1_compts_1(sK0) )
    & ( ! [X3] :
          ( ( r3_waybel_9(sK0,X3,sK2(X3))
            & m1_subset_1(sK2(X3),u1_struct_0(sK0)) )
          | ~ r2_hidden(X3,k6_yellow_6(sK0))
          | ~ l1_waybel_0(X3,sK0)
          | ~ v7_waybel_0(X3)
          | ~ v4_orders_2(X3)
          | v2_struct_0(X3) )
      | v1_compts_1(sK0) )
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f16,f15,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( ( ? [X1] :
              ( ! [X2] :
                  ( ~ r3_waybel_9(X0,X1,X2)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              & r2_hidden(X1,k6_yellow_6(X0))
              & l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
          | ~ v1_compts_1(X0) )
        & ( ! [X3] :
              ( ? [X4] :
                  ( r3_waybel_9(X0,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_hidden(X3,k6_yellow_6(X0))
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
            & r2_hidden(X1,k6_yellow_6(sK0))
            & l1_waybel_0(X1,sK0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        | ~ v1_compts_1(sK0) )
      & ( ! [X3] :
            ( ? [X4] :
                ( r3_waybel_9(sK0,X3,X4)
                & m1_subset_1(X4,u1_struct_0(sK0)) )
            | ~ r2_hidden(X3,k6_yellow_6(sK0))
            | ~ l1_waybel_0(X3,sK0)
            | ~ v7_waybel_0(X3)
            | ~ v4_orders_2(X3)
            | v2_struct_0(X3) )
        | v1_compts_1(sK0) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X1] :
        ( ! [X2] :
            ( ~ r3_waybel_9(sK0,X1,X2)
            | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
        & r2_hidden(X1,k6_yellow_6(sK0))
        & l1_waybel_0(X1,sK0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1) )
   => ( ! [X2] :
          ( ~ r3_waybel_9(sK0,sK1,X2)
          | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
      & r2_hidden(sK1,k6_yellow_6(sK0))
      & l1_waybel_0(sK1,sK0)
      & v7_waybel_0(sK1)
      & v4_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X3] :
      ( ? [X4] :
          ( r3_waybel_9(sK0,X3,X4)
          & m1_subset_1(X4,u1_struct_0(sK0)) )
     => ( r3_waybel_9(sK0,X3,sK2(X3))
        & m1_subset_1(sK2(X3),u1_struct_0(sK0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ! [X2] :
                ( ~ r3_waybel_9(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & r2_hidden(X1,k6_yellow_6(X0))
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        | ~ v1_compts_1(X0) )
      & ( ! [X3] :
            ( ? [X4] :
                ( r3_waybel_9(X0,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r2_hidden(X3,k6_yellow_6(X0))
            | ~ l1_waybel_0(X3,X0)
            | ~ v7_waybel_0(X3)
            | ~ v4_orders_2(X3)
            | v2_struct_0(X3) )
        | v1_compts_1(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ! [X2] :
                ( ~ r3_waybel_9(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & r2_hidden(X1,k6_yellow_6(X0))
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        | ~ v1_compts_1(X0) )
      & ( ! [X1] :
            ( ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r2_hidden(X1,k6_yellow_6(X0))
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) )
        | v1_compts_1(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ! [X2] :
                ( ~ r3_waybel_9(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & r2_hidden(X1,k6_yellow_6(X0))
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        | ~ v1_compts_1(X0) )
      & ( ! [X1] :
            ( ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r2_hidden(X1,k6_yellow_6(X0))
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) )
        | v1_compts_1(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
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
    inference(flattening,[],[f5])).

fof(f5,plain,(
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
             => ~ ( ! [X2] :
                      ( m1_subset_1(X2,u1_struct_0(X0))
                     => ~ r3_waybel_9(X0,X1,X2) )
                  & r2_hidden(X1,k6_yellow_6(X0)) ) ) ) ) ),
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
           => ~ ( ! [X2] :
                    ( m1_subset_1(X2,u1_struct_0(X0))
                   => ~ r3_waybel_9(X0,X1,X2) )
                & r2_hidden(X1,k6_yellow_6(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_yellow19)).

fof(f144,plain,
    ( v2_struct_0(sK0)
    | spl5_1
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f143,f23])).

fof(f23,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f143,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_1
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f142,f24])).

fof(f24,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f142,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_1
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f141,f44])).

fof(f44,plain,
    ( ~ v1_compts_1(sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl5_1
  <=> v1_compts_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f141,plain,
    ( v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_1
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(resolution,[],[f140,f39])).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),k6_yellow_6(X0))
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f10,f20])).

fof(f20,plain,(
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

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f2])).

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

fof(f140,plain,
    ( ~ r2_hidden(sK4(sK0),k6_yellow_6(sK0))
    | spl5_1
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f139,f59])).

fof(f59,plain,
    ( ~ v2_struct_0(sK4(sK0))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl5_3
  <=> v2_struct_0(sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f139,plain,
    ( ~ r2_hidden(sK4(sK0),k6_yellow_6(sK0))
    | v2_struct_0(sK4(sK0))
    | spl5_1
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f138,f63])).

fof(f63,plain,
    ( v4_orders_2(sK4(sK0))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl5_4
  <=> v4_orders_2(sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f138,plain,
    ( ~ r2_hidden(sK4(sK0),k6_yellow_6(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | spl5_1
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f137,f67])).

fof(f67,plain,
    ( v7_waybel_0(sK4(sK0))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl5_5
  <=> v7_waybel_0(sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f137,plain,
    ( ~ r2_hidden(sK4(sK0),k6_yellow_6(sK0))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | spl5_1
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f136,f71])).

fof(f71,plain,
    ( l1_waybel_0(sK4(sK0),sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl5_6
  <=> l1_waybel_0(sK4(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f136,plain,
    ( ~ r2_hidden(sK4(sK0),k6_yellow_6(sK0))
    | ~ l1_waybel_0(sK4(sK0),sK0)
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | spl5_1
    | ~ spl5_7 ),
    inference(resolution,[],[f135,f134])).

fof(f134,plain,
    ( ~ m1_subset_1(sK2(sK4(sK0)),u1_struct_0(sK0))
    | spl5_1
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f133,f22])).

fof(f133,plain,
    ( ~ m1_subset_1(sK2(sK4(sK0)),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | spl5_1
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f132,f23])).

fof(f132,plain,
    ( ~ m1_subset_1(sK2(sK4(sK0)),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_1
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f131,f24])).

fof(f131,plain,
    ( ~ m1_subset_1(sK2(sK4(sK0)),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_1
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f130,f44])).

fof(f130,plain,
    ( v1_compts_1(sK0)
    | ~ m1_subset_1(sK2(sK4(sK0)),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_7 ),
    inference(resolution,[],[f76,f40])).

fof(f40,plain,(
    ! [X2,X0] :
      ( ~ r3_waybel_9(X0,sK4(X0),X2)
      | v1_compts_1(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f76,plain,
    ( r3_waybel_9(sK0,sK4(sK0),sK2(sK4(sK0)))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl5_7
  <=> r3_waybel_9(sK0,sK4(sK0),sK2(sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f135,plain,
    ( ! [X3] :
        ( m1_subset_1(sK2(X3),u1_struct_0(sK0))
        | ~ r2_hidden(X3,k6_yellow_6(sK0))
        | ~ l1_waybel_0(X3,sK0)
        | ~ v7_waybel_0(X3)
        | ~ v4_orders_2(X3)
        | v2_struct_0(X3) )
    | spl5_1 ),
    inference(subsumption_resolution,[],[f25,f44])).

fof(f25,plain,(
    ! [X3] :
      ( m1_subset_1(sK2(X3),u1_struct_0(sK0))
      | ~ r2_hidden(X3,k6_yellow_6(sK0))
      | ~ l1_waybel_0(X3,sK0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f129,plain,
    ( spl5_1
    | ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f128])).

fof(f128,plain,
    ( $false
    | spl5_1
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f127,f22])).

fof(f127,plain,
    ( v2_struct_0(sK0)
    | spl5_1
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f126,f23])).

fof(f126,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_1
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f125,f24])).

fof(f125,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_1
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f124,f44])).

fof(f124,plain,
    ( v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3 ),
    inference(resolution,[],[f60,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v2_struct_0(sK4(X0))
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f60,plain,
    ( v2_struct_0(sK4(sK0))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f123,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f121,f22])).

fof(f121,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f120,f23])).

fof(f120,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f119,f24])).

fof(f119,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f118,f43])).

fof(f43,plain,
    ( v1_compts_1(sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f118,plain,
    ( ~ v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f117,f48])).

fof(f48,plain,
    ( ~ v2_struct_0(sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl5_2
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f117,plain,
    ( v2_struct_0(sK1)
    | ~ v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f116,f99])).

fof(f99,plain,
    ( v4_orders_2(sK1)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f28,f43])).

fof(f28,plain,
    ( v4_orders_2(sK1)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f116,plain,
    ( ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f115,f100])).

fof(f100,plain,
    ( v7_waybel_0(sK1)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f29,f43])).

fof(f29,plain,
    ( v7_waybel_0(sK1)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f115,plain,
    ( ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f114,f101])).

fof(f101,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f30,f43])).

fof(f30,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f114,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_1
    | spl5_2 ),
    inference(resolution,[],[f113,f33])).

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
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f8,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r3_waybel_9(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X1,sK3(X0,X1))
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

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
    inference(flattening,[],[f7])).

fof(f7,plain,(
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

fof(f113,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f112,f101])).

fof(f112,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f111,f48])).

fof(f111,plain,
    ( v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f110,f99])).

fof(f110,plain,
    ( ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f109,f100])).

fof(f109,plain,
    ( ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ spl5_1 ),
    inference(resolution,[],[f107,f103])).

fof(f103,plain,
    ( ! [X2] :
        ( ~ r3_waybel_9(sK0,sK1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f32,f43])).

fof(f32,plain,(
    ! [X2] :
      ( ~ r3_waybel_9(sK0,sK1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f107,plain,
    ( ! [X0] :
        ( r3_waybel_9(sK0,X0,sK3(sK0,X0))
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK0) )
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f106,f22])).

fof(f106,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | r3_waybel_9(sK0,X0,sK3(sK0,X0))
        | v2_struct_0(sK0) )
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f105,f23])).

fof(f105,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | r3_waybel_9(sK0,X0,sK3(sK0,X0))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f104,f24])).

fof(f104,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | r3_waybel_9(sK0,X0,sK3(sK0,X0))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_1 ),
    inference(resolution,[],[f34,f43])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_compts_1(X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | r3_waybel_9(X0,X1,sK3(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f95,plain,
    ( spl5_1
    | spl5_6 ),
    inference(avatar_contradiction_clause,[],[f94])).

fof(f94,plain,
    ( $false
    | spl5_1
    | spl5_6 ),
    inference(subsumption_resolution,[],[f93,f22])).

fof(f93,plain,
    ( v2_struct_0(sK0)
    | spl5_1
    | spl5_6 ),
    inference(subsumption_resolution,[],[f92,f23])).

fof(f92,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_1
    | spl5_6 ),
    inference(subsumption_resolution,[],[f91,f24])).

fof(f91,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_1
    | spl5_6 ),
    inference(subsumption_resolution,[],[f90,f44])).

fof(f90,plain,
    ( v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_6 ),
    inference(resolution,[],[f72,f38])).

fof(f38,plain,(
    ! [X0] :
      ( l1_waybel_0(sK4(X0),X0)
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f72,plain,
    ( ~ l1_waybel_0(sK4(sK0),sK0)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f70])).

fof(f89,plain,
    ( spl5_1
    | spl5_5 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | spl5_1
    | spl5_5 ),
    inference(subsumption_resolution,[],[f87,f22])).

fof(f87,plain,
    ( v2_struct_0(sK0)
    | spl5_1
    | spl5_5 ),
    inference(subsumption_resolution,[],[f86,f23])).

fof(f86,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_1
    | spl5_5 ),
    inference(subsumption_resolution,[],[f85,f24])).

fof(f85,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_1
    | spl5_5 ),
    inference(subsumption_resolution,[],[f84,f44])).

fof(f84,plain,
    ( v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_5 ),
    inference(resolution,[],[f68,f37])).

fof(f37,plain,(
    ! [X0] :
      ( v7_waybel_0(sK4(X0))
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f68,plain,
    ( ~ v7_waybel_0(sK4(sK0))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f66])).

fof(f83,plain,
    ( spl5_1
    | spl5_4 ),
    inference(avatar_contradiction_clause,[],[f82])).

fof(f82,plain,
    ( $false
    | spl5_1
    | spl5_4 ),
    inference(subsumption_resolution,[],[f81,f22])).

fof(f81,plain,
    ( v2_struct_0(sK0)
    | spl5_1
    | spl5_4 ),
    inference(subsumption_resolution,[],[f80,f23])).

fof(f80,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_1
    | spl5_4 ),
    inference(subsumption_resolution,[],[f79,f24])).

fof(f79,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_1
    | spl5_4 ),
    inference(subsumption_resolution,[],[f78,f44])).

fof(f78,plain,
    ( v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_4 ),
    inference(resolution,[],[f64,f36])).

fof(f36,plain,(
    ! [X0] :
      ( v4_orders_2(sK4(X0))
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f64,plain,
    ( ~ v4_orders_2(sK4(sK0))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f77,plain,
    ( spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7
    | spl5_1 ),
    inference(avatar_split_clause,[],[f56,f42,f74,f70,f66,f62,f58])).

fof(f56,plain,
    ( r3_waybel_9(sK0,sK4(sK0),sK2(sK4(sK0)))
    | ~ l1_waybel_0(sK4(sK0),sK0)
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | spl5_1 ),
    inference(subsumption_resolution,[],[f55,f22])).

fof(f55,plain,
    ( v2_struct_0(sK0)
    | r3_waybel_9(sK0,sK4(sK0),sK2(sK4(sK0)))
    | ~ l1_waybel_0(sK4(sK0),sK0)
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | spl5_1 ),
    inference(subsumption_resolution,[],[f54,f23])).

fof(f54,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | r3_waybel_9(sK0,sK4(sK0),sK2(sK4(sK0)))
    | ~ l1_waybel_0(sK4(sK0),sK0)
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | spl5_1 ),
    inference(subsumption_resolution,[],[f53,f24])).

fof(f53,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | r3_waybel_9(sK0,sK4(sK0),sK2(sK4(sK0)))
    | ~ l1_waybel_0(sK4(sK0),sK0)
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | spl5_1 ),
    inference(subsumption_resolution,[],[f52,f44])).

fof(f52,plain,
    ( v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | r3_waybel_9(sK0,sK4(sK0),sK2(sK4(sK0)))
    | ~ l1_waybel_0(sK4(sK0),sK0)
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | spl5_1 ),
    inference(resolution,[],[f39,f51])).

fof(f51,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k6_yellow_6(sK0))
        | r3_waybel_9(sK0,X3,sK2(X3))
        | ~ l1_waybel_0(X3,sK0)
        | ~ v7_waybel_0(X3)
        | ~ v4_orders_2(X3)
        | v2_struct_0(X3) )
    | spl5_1 ),
    inference(subsumption_resolution,[],[f26,f44])).

% (16319)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
fof(f26,plain,(
    ! [X3] :
      ( r3_waybel_9(sK0,X3,sK2(X3))
      | ~ r2_hidden(X3,k6_yellow_6(sK0))
      | ~ l1_waybel_0(X3,sK0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f49,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f27,f46,f42])).

fof(f27,plain,
    ( ~ v2_struct_0(sK1)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

%------------------------------------------------------------------------------
