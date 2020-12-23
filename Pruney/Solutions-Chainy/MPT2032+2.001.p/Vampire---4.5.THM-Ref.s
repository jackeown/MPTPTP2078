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
% DateTime   : Thu Dec  3 13:23:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 465 expanded)
%              Number of leaves         :   16 ( 195 expanded)
%              Depth                    :   22
%              Number of atoms          :  482 (4184 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f118,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f91,f93,f117])).

% (24448)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
fof(f117,plain,(
    ~ spl8_1 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f115,f44])).

fof(f44,plain,(
    ~ r3_waybel_9(sK3,sK4,sK6) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ r3_waybel_9(sK3,sK4,sK6)
    & r3_waybel_9(sK3,sK5,sK6)
    & m1_subset_1(sK6,u1_struct_0(sK3))
    & m2_yellow_6(sK5,sK3,sK4)
    & l1_waybel_0(sK4,sK3)
    & v7_waybel_0(sK4)
    & v4_orders_2(sK4)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f8,f24,f23,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r3_waybel_9(X0,X1,X3)
                    & r3_waybel_9(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m2_yellow_6(X2,X0,X1) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r3_waybel_9(sK3,X1,X3)
                  & r3_waybel_9(sK3,X2,X3)
                  & m1_subset_1(X3,u1_struct_0(sK3)) )
              & m2_yellow_6(X2,sK3,X1) )
          & l1_waybel_0(X1,sK3)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r3_waybel_9(sK3,X1,X3)
                & r3_waybel_9(sK3,X2,X3)
                & m1_subset_1(X3,u1_struct_0(sK3)) )
            & m2_yellow_6(X2,sK3,X1) )
        & l1_waybel_0(X1,sK3)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r3_waybel_9(sK3,sK4,X3)
              & r3_waybel_9(sK3,X2,X3)
              & m1_subset_1(X3,u1_struct_0(sK3)) )
          & m2_yellow_6(X2,sK3,sK4) )
      & l1_waybel_0(sK4,sK3)
      & v7_waybel_0(sK4)
      & v4_orders_2(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r3_waybel_9(sK3,sK4,X3)
            & r3_waybel_9(sK3,X2,X3)
            & m1_subset_1(X3,u1_struct_0(sK3)) )
        & m2_yellow_6(X2,sK3,sK4) )
   => ( ? [X3] :
          ( ~ r3_waybel_9(sK3,sK4,X3)
          & r3_waybel_9(sK3,sK5,X3)
          & m1_subset_1(X3,u1_struct_0(sK3)) )
      & m2_yellow_6(sK5,sK3,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X3] :
        ( ~ r3_waybel_9(sK3,sK4,X3)
        & r3_waybel_9(sK3,sK5,X3)
        & m1_subset_1(X3,u1_struct_0(sK3)) )
   => ( ~ r3_waybel_9(sK3,sK4,sK6)
      & r3_waybel_9(sK3,sK5,sK6)
      & m1_subset_1(sK6,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r3_waybel_9(X0,X1,X3)
                  & r3_waybel_9(X0,X2,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m2_yellow_6(X2,X0,X1) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r3_waybel_9(X0,X1,X3)
                  & r3_waybel_9(X0,X2,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m2_yellow_6(X2,X0,X1) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
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

fof(f115,plain,
    ( r3_waybel_9(sK3,sK4,sK6)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f114,f40])).

fof(f40,plain,(
    l1_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f114,plain,
    ( ~ l1_waybel_0(sK4,sK3)
    | r3_waybel_9(sK3,sK4,sK6)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f112,f37])).

fof(f37,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f112,plain,
    ( v2_struct_0(sK4)
    | ~ l1_waybel_0(sK4,sK3)
    | r3_waybel_9(sK3,sK4,sK6)
    | ~ spl8_1 ),
    inference(resolution,[],[f111,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ sP0(X0,sK3,sK6)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X0,sK3)
      | r3_waybel_9(sK3,X0,sK6) ) ),
    inference(resolution,[],[f62,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | r3_waybel_9(X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_waybel_9(X1,X2,X0)
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ r3_waybel_9(X1,X2,X0) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ( ( r3_waybel_9(X0,X1,X2)
          | ~ sP0(X1,X0,X2) )
        & ( sP0(X1,X0,X2)
          | ~ r3_waybel_9(X0,X1,X2) ) )
      | ~ sP1(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ( r3_waybel_9(X0,X1,X2)
      <=> sP0(X1,X0,X2) )
      | ~ sP1(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f62,plain,(
    ! [X0] :
      ( sP1(sK6,sK3,X0)
      | ~ l1_waybel_0(X0,sK3)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f61,f34])).

fof(f34,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f61,plain,(
    ! [X0] :
      ( sP1(sK6,sK3,X0)
      | ~ l1_waybel_0(X0,sK3)
      | v2_struct_0(X0)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f60,f35])).

fof(f35,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f60,plain,(
    ! [X0] :
      ( sP1(sK6,sK3,X0)
      | ~ l1_waybel_0(X0,sK3)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f59,f36])).

fof(f36,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f59,plain,(
    ! [X0] :
      ( sP1(sK6,sK3,X0)
      | ~ l1_waybel_0(X0,sK3)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f51,f42])).

fof(f42,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f25])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP1(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X2,X0,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f11,f17,f16])).

fof(f16,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_waybel_0(X0,X1,X3)
          | ~ m1_connsp_2(X3,X0,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f111,plain,
    ( sP0(sK4,sK3,sK6)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f110,f37])).

fof(f110,plain,
    ( v2_struct_0(sK4)
    | sP0(sK4,sK3,sK6)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f109,f38])).

fof(f38,plain,(
    v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f109,plain,
    ( ~ v4_orders_2(sK4)
    | v2_struct_0(sK4)
    | sP0(sK4,sK3,sK6)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f108,f39])).

fof(f39,plain,(
    v7_waybel_0(sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f108,plain,
    ( ~ v7_waybel_0(sK4)
    | ~ v4_orders_2(sK4)
    | v2_struct_0(sK4)
    | sP0(sK4,sK3,sK6)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f107,f40])).

fof(f107,plain,
    ( ~ l1_waybel_0(sK4,sK3)
    | ~ v7_waybel_0(sK4)
    | ~ v4_orders_2(sK4)
    | v2_struct_0(sK4)
    | sP0(sK4,sK3,sK6)
    | ~ spl8_1 ),
    inference(resolution,[],[f104,f41])).

fof(f41,plain,(
    m2_yellow_6(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f104,plain,
    ( ! [X0] :
        ( ~ m2_yellow_6(sK5,sK3,X0)
        | ~ l1_waybel_0(X0,sK3)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | sP0(X0,sK3,sK6) )
    | ~ spl8_1 ),
    inference(duplicate_literal_removal,[],[f102])).

fof(f102,plain,
    ( ! [X0] :
        ( ~ m2_yellow_6(sK5,sK3,X0)
        | ~ l1_waybel_0(X0,sK3)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | sP0(X0,sK3,sK6)
        | sP0(X0,sK3,sK6) )
    | ~ spl8_1 ),
    inference(resolution,[],[f101,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_waybel_0(X1,X0,sK7(X0,X1,X2))
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ~ r2_waybel_0(X1,X0,sK7(X0,X1,X2))
          & m1_connsp_2(sK7(X0,X1,X2),X1,X2) ) )
      & ( ! [X4] :
            ( r2_waybel_0(X1,X0,X4)
            | ~ m1_connsp_2(X4,X1,X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f29,f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_waybel_0(X1,X0,X3)
          & m1_connsp_2(X3,X1,X2) )
     => ( ~ r2_waybel_0(X1,X0,sK7(X0,X1,X2))
        & m1_connsp_2(sK7(X0,X1,X2),X1,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ~ r2_waybel_0(X1,X0,X3)
            & m1_connsp_2(X3,X1,X2) ) )
      & ( ! [X4] :
            ( r2_waybel_0(X1,X0,X4)
            | ~ m1_connsp_2(X4,X1,X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ~ r2_waybel_0(X0,X1,X3)
            & m1_connsp_2(X3,X0,X2) ) )
      & ( ! [X3] :
            ( r2_waybel_0(X0,X1,X3)
            | ~ m1_connsp_2(X3,X0,X2) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f101,plain,
    ( ! [X0,X1] :
        ( r2_waybel_0(sK3,X0,sK7(X1,sK3,sK6))
        | ~ m2_yellow_6(sK5,sK3,X0)
        | ~ l1_waybel_0(X0,sK3)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | sP0(X1,sK3,sK6) )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f100,f34])).

fof(f100,plain,
    ( ! [X0,X1] :
        ( r2_waybel_0(sK3,X0,sK7(X1,sK3,sK6))
        | ~ m2_yellow_6(sK5,sK3,X0)
        | ~ l1_waybel_0(X0,sK3)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | v2_struct_0(sK3)
        | sP0(X1,sK3,sK6) )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f99,f58])).

fof(f58,plain,(
    l1_struct_0(sK3) ),
    inference(resolution,[],[f45,f36])).

fof(f45,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

% (24437)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
fof(f99,plain,
    ( ! [X0,X1] :
        ( r2_waybel_0(sK3,X0,sK7(X1,sK3,sK6))
        | ~ m2_yellow_6(sK5,sK3,X0)
        | ~ l1_waybel_0(X0,sK3)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_struct_0(sK3)
        | v2_struct_0(sK3)
        | sP0(X1,sK3,sK6) )
    | ~ spl8_1 ),
    inference(resolution,[],[f52,f96])).

fof(f96,plain,
    ( ! [X0] :
        ( r2_waybel_0(sK3,sK5,sK7(X0,sK3,sK6))
        | sP0(X0,sK3,sK6) )
    | ~ spl8_1 ),
    inference(resolution,[],[f95,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(sK7(X0,X1,X2),X1,X2)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f95,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(X0,sK3,sK6)
        | r2_waybel_0(sK3,sK5,X0) )
    | ~ spl8_1 ),
    inference(resolution,[],[f69,f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ m1_connsp_2(X4,X1,X2)
      | r2_waybel_0(X1,X0,X4) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f69,plain,
    ( sP0(sK5,sK3,sK6)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl8_1
  <=> sP0(sK5,sK3,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_waybel_0(X0,X2,X3)
      | r2_waybel_0(X0,X1,X3)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f93,plain,(
    ~ spl8_3 ),
    inference(avatar_contradiction_clause,[],[f92])).

fof(f92,plain,
    ( $false
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f77,f89])).

fof(f89,plain,(
    ~ v2_struct_0(sK5) ),
    inference(resolution,[],[f85,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1)
      | ~ v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1) )
      | ~ sP2(X0,X1) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X2] :
      ( ( l1_waybel_0(X2,X0)
        & v7_waybel_0(X2)
        & v4_orders_2(X2)
        & ~ v2_struct_0(X2) )
      | ~ sP2(X0,X2) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X2] :
      ( ( l1_waybel_0(X2,X0)
        & v7_waybel_0(X2)
        & v4_orders_2(X2)
        & ~ v2_struct_0(X2) )
      | ~ sP2(X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f85,plain,(
    sP2(sK3,sK5) ),
    inference(subsumption_resolution,[],[f84,f34])).

fof(f84,plain,
    ( sP2(sK3,sK5)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f83,f58])).

fof(f83,plain,
    ( sP2(sK3,sK5)
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f82,f37])).

fof(f82,plain,
    ( sP2(sK3,sK5)
    | v2_struct_0(sK4)
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f81,f38])).

fof(f81,plain,
    ( sP2(sK3,sK5)
    | ~ v4_orders_2(sK4)
    | v2_struct_0(sK4)
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f80,f39])).

fof(f80,plain,
    ( sP2(sK3,sK5)
    | ~ v7_waybel_0(sK4)
    | ~ v4_orders_2(sK4)
    | v2_struct_0(sK4)
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f79,f40])).

fof(f79,plain,
    ( sP2(sK3,sK5)
    | ~ l1_waybel_0(sK4,sK3)
    | ~ v7_waybel_0(sK4)
    | ~ v4_orders_2(sK4)
    | v2_struct_0(sK4)
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f57,f41])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_yellow_6(X2,X0,X1)
      | sP2(X0,X2)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( sP2(X0,X2)
          | ~ m2_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f15,f19])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f77,plain,
    ( v2_struct_0(sK5)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl8_3
  <=> v2_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f91,plain,(
    spl8_2 ),
    inference(avatar_contradiction_clause,[],[f90])).

fof(f90,plain,
    ( $false
    | spl8_2 ),
    inference(subsumption_resolution,[],[f86,f73])).

fof(f73,plain,
    ( ~ l1_waybel_0(sK5,sK3)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl8_2
  <=> l1_waybel_0(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f86,plain,(
    l1_waybel_0(sK5,sK3) ),
    inference(resolution,[],[f85,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1)
      | l1_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f78,plain,
    ( spl8_1
    | ~ spl8_2
    | spl8_3 ),
    inference(avatar_split_clause,[],[f65,f75,f71,f67])).

fof(f65,plain,
    ( v2_struct_0(sK5)
    | ~ l1_waybel_0(sK5,sK3)
    | sP0(sK5,sK3,sK6) ),
    inference(resolution,[],[f64,f43])).

fof(f43,plain,(
    r3_waybel_9(sK3,sK5,sK6) ),
    inference(cnf_transformation,[],[f25])).

fof(f64,plain,(
    ! [X1] :
      ( ~ r3_waybel_9(sK3,X1,sK6)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,sK3)
      | sP0(X1,sK3,sK6) ) ),
    inference(resolution,[],[f62,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r3_waybel_9(X1,X2,X0)
      | sP0(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : run_vampire %s %d
% 0.14/0.33  % Computer   : n010.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 13:16:44 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.20/0.46  % (24439)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.20/0.46  % (24440)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.46  % (24438)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.20/0.46  % (24439)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % (24446)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.20/0.46  % (24445)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.20/0.46  % (24447)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f118,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f78,f91,f93,f117])).
% 0.20/0.46  % (24448)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 0.20/0.46  fof(f117,plain,(
% 0.20/0.46    ~spl8_1),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f116])).
% 0.20/0.46  fof(f116,plain,(
% 0.20/0.46    $false | ~spl8_1),
% 0.20/0.46    inference(subsumption_resolution,[],[f115,f44])).
% 0.20/0.46  fof(f44,plain,(
% 0.20/0.46    ~r3_waybel_9(sK3,sK4,sK6)),
% 0.20/0.46    inference(cnf_transformation,[],[f25])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    (((~r3_waybel_9(sK3,sK4,sK6) & r3_waybel_9(sK3,sK5,sK6) & m1_subset_1(sK6,u1_struct_0(sK3))) & m2_yellow_6(sK5,sK3,sK4)) & l1_waybel_0(sK4,sK3) & v7_waybel_0(sK4) & v4_orders_2(sK4) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f8,f24,f23,f22,f21])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r3_waybel_9(X0,X1,X3) & r3_waybel_9(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r3_waybel_9(sK3,X1,X3) & r3_waybel_9(sK3,X2,X3) & m1_subset_1(X3,u1_struct_0(sK3))) & m2_yellow_6(X2,sK3,X1)) & l1_waybel_0(X1,sK3) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ? [X1] : (? [X2] : (? [X3] : (~r3_waybel_9(sK3,X1,X3) & r3_waybel_9(sK3,X2,X3) & m1_subset_1(X3,u1_struct_0(sK3))) & m2_yellow_6(X2,sK3,X1)) & l1_waybel_0(X1,sK3) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~r3_waybel_9(sK3,sK4,X3) & r3_waybel_9(sK3,X2,X3) & m1_subset_1(X3,u1_struct_0(sK3))) & m2_yellow_6(X2,sK3,sK4)) & l1_waybel_0(sK4,sK3) & v7_waybel_0(sK4) & v4_orders_2(sK4) & ~v2_struct_0(sK4))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ? [X2] : (? [X3] : (~r3_waybel_9(sK3,sK4,X3) & r3_waybel_9(sK3,X2,X3) & m1_subset_1(X3,u1_struct_0(sK3))) & m2_yellow_6(X2,sK3,sK4)) => (? [X3] : (~r3_waybel_9(sK3,sK4,X3) & r3_waybel_9(sK3,sK5,X3) & m1_subset_1(X3,u1_struct_0(sK3))) & m2_yellow_6(sK5,sK3,sK4))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    ? [X3] : (~r3_waybel_9(sK3,sK4,X3) & r3_waybel_9(sK3,sK5,X3) & m1_subset_1(X3,u1_struct_0(sK3))) => (~r3_waybel_9(sK3,sK4,sK6) & r3_waybel_9(sK3,sK5,sK6) & m1_subset_1(sK6,u1_struct_0(sK3)))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f8,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r3_waybel_9(X0,X1,X3) & r3_waybel_9(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.46    inference(flattening,[],[f7])).
% 0.20/0.46  fof(f7,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r3_waybel_9(X0,X1,X3) & r3_waybel_9(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m2_yellow_6(X2,X0,X1)) & (l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,negated_conjecture,(
% 0.20/0.46    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_waybel_9(X0,X2,X3) => r3_waybel_9(X0,X1,X3))))))),
% 0.20/0.46    inference(negated_conjecture,[],[f5])).
% 0.20/0.46  fof(f5,conjecture,(
% 0.20/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_waybel_9(X0,X2,X3) => r3_waybel_9(X0,X1,X3))))))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_waybel_9)).
% 0.20/0.46  fof(f115,plain,(
% 0.20/0.46    r3_waybel_9(sK3,sK4,sK6) | ~spl8_1),
% 0.20/0.46    inference(subsumption_resolution,[],[f114,f40])).
% 0.20/0.46  fof(f40,plain,(
% 0.20/0.46    l1_waybel_0(sK4,sK3)),
% 0.20/0.46    inference(cnf_transformation,[],[f25])).
% 0.20/0.46  fof(f114,plain,(
% 0.20/0.46    ~l1_waybel_0(sK4,sK3) | r3_waybel_9(sK3,sK4,sK6) | ~spl8_1),
% 0.20/0.46    inference(subsumption_resolution,[],[f112,f37])).
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    ~v2_struct_0(sK4)),
% 0.20/0.46    inference(cnf_transformation,[],[f25])).
% 0.20/0.46  fof(f112,plain,(
% 0.20/0.46    v2_struct_0(sK4) | ~l1_waybel_0(sK4,sK3) | r3_waybel_9(sK3,sK4,sK6) | ~spl8_1),
% 0.20/0.46    inference(resolution,[],[f111,f63])).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    ( ! [X0] : (~sP0(X0,sK3,sK6) | v2_struct_0(X0) | ~l1_waybel_0(X0,sK3) | r3_waybel_9(sK3,X0,sK6)) )),
% 0.20/0.47    inference(resolution,[],[f62,f47])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | r3_waybel_9(X1,X2,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (((r3_waybel_9(X1,X2,X0) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~r3_waybel_9(X1,X2,X0))) | ~sP1(X0,X1,X2))),
% 0.20/0.47    inference(rectify,[],[f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ! [X2,X0,X1] : (((r3_waybel_9(X0,X1,X2) | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | ~r3_waybel_9(X0,X1,X2))) | ~sP1(X2,X0,X1))),
% 0.20/0.47    inference(nnf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X2,X0,X1] : ((r3_waybel_9(X0,X1,X2) <=> sP0(X1,X0,X2)) | ~sP1(X2,X0,X1))),
% 0.20/0.47    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    ( ! [X0] : (sP1(sK6,sK3,X0) | ~l1_waybel_0(X0,sK3) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f61,f34])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ~v2_struct_0(sK3)),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f61,plain,(
% 0.20/0.47    ( ! [X0] : (sP1(sK6,sK3,X0) | ~l1_waybel_0(X0,sK3) | v2_struct_0(X0) | v2_struct_0(sK3)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f60,f35])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    v2_pre_topc(sK3)),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    ( ! [X0] : (sP1(sK6,sK3,X0) | ~l1_waybel_0(X0,sK3) | v2_struct_0(X0) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f59,f36])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    l1_pre_topc(sK3)),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    ( ! [X0] : (sP1(sK6,sK3,X0) | ~l1_waybel_0(X0,sK3) | v2_struct_0(X0) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 0.20/0.47    inference(resolution,[],[f51,f42])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    m1_subset_1(sK6,u1_struct_0(sK3))),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | sP1(X2,X0,X1) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : (sP1(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(definition_folding,[],[f11,f17,f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_waybel_0(X0,X1,X3) | ~m1_connsp_2(X3,X0,X2)))),
% 0.20/0.47    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> ! [X3] : (r2_waybel_0(X0,X1,X3) | ~m1_connsp_2(X3,X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f10])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> ! [X3] : (r2_waybel_0(X0,X1,X3) | ~m1_connsp_2(X3,X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X2) <=> ! [X3] : (m1_connsp_2(X3,X0,X2) => r2_waybel_0(X0,X1,X3))))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_waybel_9)).
% 0.20/0.47  fof(f111,plain,(
% 0.20/0.47    sP0(sK4,sK3,sK6) | ~spl8_1),
% 0.20/0.47    inference(subsumption_resolution,[],[f110,f37])).
% 0.20/0.47  fof(f110,plain,(
% 0.20/0.47    v2_struct_0(sK4) | sP0(sK4,sK3,sK6) | ~spl8_1),
% 0.20/0.47    inference(subsumption_resolution,[],[f109,f38])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    v4_orders_2(sK4)),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f109,plain,(
% 0.20/0.47    ~v4_orders_2(sK4) | v2_struct_0(sK4) | sP0(sK4,sK3,sK6) | ~spl8_1),
% 0.20/0.47    inference(subsumption_resolution,[],[f108,f39])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    v7_waybel_0(sK4)),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f108,plain,(
% 0.20/0.47    ~v7_waybel_0(sK4) | ~v4_orders_2(sK4) | v2_struct_0(sK4) | sP0(sK4,sK3,sK6) | ~spl8_1),
% 0.20/0.47    inference(subsumption_resolution,[],[f107,f40])).
% 0.20/0.47  fof(f107,plain,(
% 0.20/0.47    ~l1_waybel_0(sK4,sK3) | ~v7_waybel_0(sK4) | ~v4_orders_2(sK4) | v2_struct_0(sK4) | sP0(sK4,sK3,sK6) | ~spl8_1),
% 0.20/0.47    inference(resolution,[],[f104,f41])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    m2_yellow_6(sK5,sK3,sK4)),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f104,plain,(
% 0.20/0.47    ( ! [X0] : (~m2_yellow_6(sK5,sK3,X0) | ~l1_waybel_0(X0,sK3) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | sP0(X0,sK3,sK6)) ) | ~spl8_1),
% 0.20/0.47    inference(duplicate_literal_removal,[],[f102])).
% 0.20/0.47  fof(f102,plain,(
% 0.20/0.47    ( ! [X0] : (~m2_yellow_6(sK5,sK3,X0) | ~l1_waybel_0(X0,sK3) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | sP0(X0,sK3,sK6) | sP0(X0,sK3,sK6)) ) | ~spl8_1),
% 0.20/0.47    inference(resolution,[],[f101,f50])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r2_waybel_0(X1,X0,sK7(X0,X1,X2)) | sP0(X0,X1,X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f31])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (~r2_waybel_0(X1,X0,sK7(X0,X1,X2)) & m1_connsp_2(sK7(X0,X1,X2),X1,X2))) & (! [X4] : (r2_waybel_0(X1,X0,X4) | ~m1_connsp_2(X4,X1,X2)) | ~sP0(X0,X1,X2)))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f29,f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ! [X2,X1,X0] : (? [X3] : (~r2_waybel_0(X1,X0,X3) & m1_connsp_2(X3,X1,X2)) => (~r2_waybel_0(X1,X0,sK7(X0,X1,X2)) & m1_connsp_2(sK7(X0,X1,X2),X1,X2)))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (~r2_waybel_0(X1,X0,X3) & m1_connsp_2(X3,X1,X2))) & (! [X4] : (r2_waybel_0(X1,X0,X4) | ~m1_connsp_2(X4,X1,X2)) | ~sP0(X0,X1,X2)))),
% 0.20/0.47    inference(rectify,[],[f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (~r2_waybel_0(X0,X1,X3) & m1_connsp_2(X3,X0,X2))) & (! [X3] : (r2_waybel_0(X0,X1,X3) | ~m1_connsp_2(X3,X0,X2)) | ~sP0(X1,X0,X2)))),
% 0.20/0.47    inference(nnf_transformation,[],[f16])).
% 0.20/0.47  fof(f101,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r2_waybel_0(sK3,X0,sK7(X1,sK3,sK6)) | ~m2_yellow_6(sK5,sK3,X0) | ~l1_waybel_0(X0,sK3) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | sP0(X1,sK3,sK6)) ) | ~spl8_1),
% 0.20/0.47    inference(subsumption_resolution,[],[f100,f34])).
% 0.20/0.47  fof(f100,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r2_waybel_0(sK3,X0,sK7(X1,sK3,sK6)) | ~m2_yellow_6(sK5,sK3,X0) | ~l1_waybel_0(X0,sK3) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | v2_struct_0(sK3) | sP0(X1,sK3,sK6)) ) | ~spl8_1),
% 0.20/0.47    inference(subsumption_resolution,[],[f99,f58])).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    l1_struct_0(sK3)),
% 0.20/0.47    inference(resolution,[],[f45,f36])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.47  % (24437)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.20/0.47  fof(f99,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r2_waybel_0(sK3,X0,sK7(X1,sK3,sK6)) | ~m2_yellow_6(sK5,sK3,X0) | ~l1_waybel_0(X0,sK3) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK3) | v2_struct_0(sK3) | sP0(X1,sK3,sK6)) ) | ~spl8_1),
% 0.20/0.47    inference(resolution,[],[f52,f96])).
% 0.20/0.47  fof(f96,plain,(
% 0.20/0.47    ( ! [X0] : (r2_waybel_0(sK3,sK5,sK7(X0,sK3,sK6)) | sP0(X0,sK3,sK6)) ) | ~spl8_1),
% 0.20/0.47    inference(resolution,[],[f95,f49])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (m1_connsp_2(sK7(X0,X1,X2),X1,X2) | sP0(X0,X1,X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f31])).
% 0.20/0.47  fof(f95,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK6) | r2_waybel_0(sK3,sK5,X0)) ) | ~spl8_1),
% 0.20/0.47    inference(resolution,[],[f69,f48])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~m1_connsp_2(X4,X1,X2) | r2_waybel_0(X1,X0,X4)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f31])).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    sP0(sK5,sK3,sK6) | ~spl8_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f67])).
% 0.20/0.47  fof(f67,plain,(
% 0.20/0.47    spl8_1 <=> sP0(sK5,sK3,sK6)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (~r2_waybel_0(X0,X2,X3) | r2_waybel_0(X0,X1,X3) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_waybel_0(X0,X1,X3) | ~r2_waybel_0(X0,X2,X3)) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_waybel_0(X0,X1,X3) | ~r2_waybel_0(X0,X2,X3)) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => ! [X3] : (r2_waybel_0(X0,X2,X3) => r2_waybel_0(X0,X1,X3)))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow_6)).
% 0.20/0.47  fof(f93,plain,(
% 0.20/0.47    ~spl8_3),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f92])).
% 0.20/0.47  fof(f92,plain,(
% 0.20/0.47    $false | ~spl8_3),
% 0.20/0.47    inference(subsumption_resolution,[],[f77,f89])).
% 0.20/0.47  fof(f89,plain,(
% 0.20/0.47    ~v2_struct_0(sK5)),
% 0.20/0.47    inference(resolution,[],[f85,f53])).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~sP2(X0,X1) | ~v2_struct_0(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~sP2(X0,X1))),
% 0.20/0.47    inference(rectify,[],[f32])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ! [X0,X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~sP2(X0,X2))),
% 0.20/0.47    inference(nnf_transformation,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0,X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~sP2(X0,X2))),
% 0.20/0.47    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.20/0.47  fof(f85,plain,(
% 0.20/0.47    sP2(sK3,sK5)),
% 0.20/0.47    inference(subsumption_resolution,[],[f84,f34])).
% 0.20/0.47  fof(f84,plain,(
% 0.20/0.47    sP2(sK3,sK5) | v2_struct_0(sK3)),
% 0.20/0.47    inference(subsumption_resolution,[],[f83,f58])).
% 0.20/0.47  fof(f83,plain,(
% 0.20/0.47    sP2(sK3,sK5) | ~l1_struct_0(sK3) | v2_struct_0(sK3)),
% 0.20/0.47    inference(subsumption_resolution,[],[f82,f37])).
% 0.20/0.47  fof(f82,plain,(
% 0.20/0.47    sP2(sK3,sK5) | v2_struct_0(sK4) | ~l1_struct_0(sK3) | v2_struct_0(sK3)),
% 0.20/0.47    inference(subsumption_resolution,[],[f81,f38])).
% 0.20/0.47  fof(f81,plain,(
% 0.20/0.47    sP2(sK3,sK5) | ~v4_orders_2(sK4) | v2_struct_0(sK4) | ~l1_struct_0(sK3) | v2_struct_0(sK3)),
% 0.20/0.47    inference(subsumption_resolution,[],[f80,f39])).
% 0.20/0.47  fof(f80,plain,(
% 0.20/0.47    sP2(sK3,sK5) | ~v7_waybel_0(sK4) | ~v4_orders_2(sK4) | v2_struct_0(sK4) | ~l1_struct_0(sK3) | v2_struct_0(sK3)),
% 0.20/0.47    inference(subsumption_resolution,[],[f79,f40])).
% 0.20/0.47  fof(f79,plain,(
% 0.20/0.47    sP2(sK3,sK5) | ~l1_waybel_0(sK4,sK3) | ~v7_waybel_0(sK4) | ~v4_orders_2(sK4) | v2_struct_0(sK4) | ~l1_struct_0(sK3) | v2_struct_0(sK3)),
% 0.20/0.47    inference(resolution,[],[f57,f41])).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m2_yellow_6(X2,X0,X1) | sP2(X0,X2) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X0,X1] : (! [X2] : (sP2(X0,X2) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(definition_folding,[],[f15,f19])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_yellow_6)).
% 0.20/0.47  fof(f77,plain,(
% 0.20/0.47    v2_struct_0(sK5) | ~spl8_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f75])).
% 0.20/0.47  fof(f75,plain,(
% 0.20/0.47    spl8_3 <=> v2_struct_0(sK5)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.20/0.47  fof(f91,plain,(
% 0.20/0.47    spl8_2),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f90])).
% 0.20/0.47  fof(f90,plain,(
% 0.20/0.47    $false | spl8_2),
% 0.20/0.47    inference(subsumption_resolution,[],[f86,f73])).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    ~l1_waybel_0(sK5,sK3) | spl8_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f71])).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    spl8_2 <=> l1_waybel_0(sK5,sK3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.20/0.47  fof(f86,plain,(
% 0.20/0.47    l1_waybel_0(sK5,sK3)),
% 0.20/0.47    inference(resolution,[],[f85,f56])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~sP2(X0,X1) | l1_waybel_0(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f33])).
% 0.20/0.47  fof(f78,plain,(
% 0.20/0.47    spl8_1 | ~spl8_2 | spl8_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f65,f75,f71,f67])).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    v2_struct_0(sK5) | ~l1_waybel_0(sK5,sK3) | sP0(sK5,sK3,sK6)),
% 0.20/0.47    inference(resolution,[],[f64,f43])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    r3_waybel_9(sK3,sK5,sK6)),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    ( ! [X1] : (~r3_waybel_9(sK3,X1,sK6) | v2_struct_0(X1) | ~l1_waybel_0(X1,sK3) | sP0(X1,sK3,sK6)) )),
% 0.20/0.47    inference(resolution,[],[f62,f46])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~r3_waybel_9(X1,X2,X0) | sP0(X2,X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f27])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (24439)------------------------------
% 0.20/0.47  % (24439)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (24439)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (24439)Memory used [KB]: 5373
% 0.20/0.47  % (24439)Time elapsed: 0.053 s
% 0.20/0.47  % (24439)------------------------------
% 0.20/0.47  % (24439)------------------------------
% 0.20/0.47  % (24430)Success in time 0.122 s
%------------------------------------------------------------------------------
