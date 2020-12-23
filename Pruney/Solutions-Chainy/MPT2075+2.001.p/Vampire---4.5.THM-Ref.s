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
% DateTime   : Thu Dec  3 13:23:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 371 expanded)
%              Number of leaves         :    8 (  82 expanded)
%              Depth                    :   17
%              Number of atoms          :  440 (2432 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f124,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f70,f93,f110,f116,f123])).

fof(f123,plain,
    ( spl5_1
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | spl5_1
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f121,f32])).

fof(f32,plain,
    ( ~ v1_compts_1(sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl5_1
  <=> v1_compts_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f121,plain,
    ( v1_compts_1(sK0)
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f120,f18])).

fof(f18,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f6])).

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
    inference(flattening,[],[f5])).

fof(f5,plain,(
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

fof(f120,plain,
    ( v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f119,f65])).

fof(f65,plain,
    ( m1_subset_1(sK2(sK4(sK0)),u1_struct_0(sK0))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl5_3
  <=> m1_subset_1(sK2(sK4(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f119,plain,
    ( ~ m1_subset_1(sK2(sK4(sK0)),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f118,f20])).

fof(f20,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f118,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2(sK4(sK0)),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f117,f19])).

fof(f19,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f117,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2(sK4(sK0)),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl5_5 ),
    inference(resolution,[],[f109,f23])).

fof(f23,plain,(
    ! [X2,X0] :
      ( ~ r3_waybel_9(X0,sK4(X0),X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | v1_compts_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

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

fof(f109,plain,
    ( r3_waybel_9(sK0,sK4(sK0),sK2(sK4(sK0)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl5_5
  <=> r3_waybel_9(sK0,sK4(sK0),sK2(sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f116,plain,
    ( spl5_1
    | ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f115])).

fof(f115,plain,
    ( $false
    | spl5_1
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f114,f32])).

fof(f114,plain,
    ( v1_compts_1(sK0)
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f113,f18])).

fof(f113,plain,
    ( v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f112,f20])).

fof(f112,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f111,f19])).

fof(f111,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl5_4 ),
    inference(resolution,[],[f69,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v2_struct_0(sK4(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_compts_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f69,plain,
    ( v2_struct_0(sK4(sK0))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl5_4
  <=> v2_struct_0(sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f110,plain,
    ( spl5_5
    | spl5_4
    | spl5_1 ),
    inference(avatar_split_clause,[],[f105,f30,f67,f107])).

fof(f105,plain,
    ( v2_struct_0(sK4(sK0))
    | r3_waybel_9(sK0,sK4(sK0),sK2(sK4(sK0)))
    | spl5_1 ),
    inference(subsumption_resolution,[],[f104,f95])).

fof(f95,plain,
    ( v7_waybel_0(sK4(sK0))
    | spl5_1 ),
    inference(subsumption_resolution,[],[f46,f32])).

fof(f46,plain,
    ( v7_waybel_0(sK4(sK0))
    | v1_compts_1(sK0) ),
    inference(subsumption_resolution,[],[f45,f18])).

fof(f45,plain,
    ( v2_struct_0(sK0)
    | v7_waybel_0(sK4(sK0))
    | v1_compts_1(sK0) ),
    inference(subsumption_resolution,[],[f44,f19])).

fof(f44,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v7_waybel_0(sK4(sK0))
    | v1_compts_1(sK0) ),
    inference(resolution,[],[f26,f20])).

fof(f26,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v7_waybel_0(sK4(X0))
      | v1_compts_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f104,plain,
    ( ~ v7_waybel_0(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | r3_waybel_9(sK0,sK4(sK0),sK2(sK4(sK0)))
    | spl5_1 ),
    inference(subsumption_resolution,[],[f103,f94])).

fof(f94,plain,
    ( v4_orders_2(sK4(sK0))
    | spl5_1 ),
    inference(subsumption_resolution,[],[f42,f32])).

fof(f42,plain,
    ( v4_orders_2(sK4(sK0))
    | v1_compts_1(sK0) ),
    inference(subsumption_resolution,[],[f41,f18])).

fof(f41,plain,
    ( v2_struct_0(sK0)
    | v4_orders_2(sK4(sK0))
    | v1_compts_1(sK0) ),
    inference(subsumption_resolution,[],[f40,f19])).

fof(f40,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v4_orders_2(sK4(sK0))
    | v1_compts_1(sK0) ),
    inference(resolution,[],[f25,f20])).

fof(f25,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v4_orders_2(sK4(X0))
      | v1_compts_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f103,plain,
    ( ~ v4_orders_2(sK4(sK0))
    | ~ v7_waybel_0(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | r3_waybel_9(sK0,sK4(sK0),sK2(sK4(sK0)))
    | spl5_1 ),
    inference(resolution,[],[f102,f96])).

fof(f96,plain,
    ( l1_waybel_0(sK4(sK0),sK0)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f50,f32])).

fof(f50,plain,
    ( l1_waybel_0(sK4(sK0),sK0)
    | v1_compts_1(sK0) ),
    inference(subsumption_resolution,[],[f49,f18])).

fof(f49,plain,
    ( v2_struct_0(sK0)
    | l1_waybel_0(sK4(sK0),sK0)
    | v1_compts_1(sK0) ),
    inference(subsumption_resolution,[],[f48,f19])).

fof(f48,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | l1_waybel_0(sK4(sK0),sK0)
    | v1_compts_1(sK0) ),
    inference(resolution,[],[f27,f20])).

fof(f27,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | l1_waybel_0(sK4(X0),X0)
      | v1_compts_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f102,plain,
    ( ! [X1] :
        ( ~ l1_waybel_0(X1,sK0)
        | ~ v4_orders_2(X1)
        | ~ v7_waybel_0(X1)
        | v2_struct_0(X1)
        | r3_waybel_9(sK0,X1,sK2(X1)) )
    | spl5_1 ),
    inference(subsumption_resolution,[],[f12,f32])).

fof(f12,plain,(
    ! [X1] :
      ( v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,sK0)
      | r3_waybel_9(sK0,X1,sK2(X1))
      | v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f93,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_contradiction_clause,[],[f92])).

fof(f92,plain,
    ( $false
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f91,f82])).

fof(f82,plain,
    ( m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f81,f18])).

fof(f81,plain,
    ( v2_struct_0(sK0)
    | m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f80,f72])).

fof(f72,plain,
    ( v7_waybel_0(sK1)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f16,f31])).

fof(f31,plain,
    ( v1_compts_1(sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f16,plain,
    ( v7_waybel_0(sK1)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f80,plain,
    ( ~ v7_waybel_0(sK1)
    | v2_struct_0(sK0)
    | m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f79,f71])).

fof(f71,plain,
    ( v4_orders_2(sK1)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f15,f31])).

fof(f15,plain,
    ( v4_orders_2(sK1)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f79,plain,
    ( ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | v2_struct_0(sK0)
    | m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f78,f36])).

fof(f36,plain,
    ( ~ v2_struct_0(sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl5_2
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f78,plain,
    ( v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | v2_struct_0(sK0)
    | m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f77,f31])).

fof(f77,plain,
    ( ~ v1_compts_1(sK0)
    | v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | v2_struct_0(sK0)
    | m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f76,f20])).

fof(f76,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_compts_1(sK0)
    | v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | v2_struct_0(sK0)
    | m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f75,f19])).

fof(f75,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_compts_1(sK0)
    | v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | v2_struct_0(sK0)
    | m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ spl5_1 ),
    inference(resolution,[],[f21,f73])).

fof(f73,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f17,f31])).

fof(f17,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | v2_struct_0(X0)
      | m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f8])).

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

fof(f91,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ spl5_1
    | spl5_2 ),
    inference(resolution,[],[f90,f74])).

fof(f74,plain,
    ( ! [X2] :
        ( ~ r3_waybel_9(sK0,sK1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f13,f31])).

fof(f13,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK1,X2)
      | ~ v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f90,plain,
    ( r3_waybel_9(sK0,sK1,sK3(sK0,sK1))
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f89,f18])).

fof(f89,plain,
    ( v2_struct_0(sK0)
    | r3_waybel_9(sK0,sK1,sK3(sK0,sK1))
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f88,f72])).

fof(f88,plain,
    ( ~ v7_waybel_0(sK1)
    | v2_struct_0(sK0)
    | r3_waybel_9(sK0,sK1,sK3(sK0,sK1))
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f87,f71])).

fof(f87,plain,
    ( ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | v2_struct_0(sK0)
    | r3_waybel_9(sK0,sK1,sK3(sK0,sK1))
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f86,f36])).

fof(f86,plain,
    ( v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | v2_struct_0(sK0)
    | r3_waybel_9(sK0,sK1,sK3(sK0,sK1))
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f85,f31])).

fof(f85,plain,
    ( ~ v1_compts_1(sK0)
    | v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | v2_struct_0(sK0)
    | r3_waybel_9(sK0,sK1,sK3(sK0,sK1))
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f84,f20])).

fof(f84,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_compts_1(sK0)
    | v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | v2_struct_0(sK0)
    | r3_waybel_9(sK0,sK1,sK3(sK0,sK1))
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f83,f19])).

fof(f83,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_compts_1(sK0)
    | v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | v2_struct_0(sK0)
    | r3_waybel_9(sK0,sK1,sK3(sK0,sK1))
    | ~ spl5_1 ),
    inference(resolution,[],[f22,f73])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | v2_struct_0(X0)
      | r3_waybel_9(X0,X1,sK3(X0,X1)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f70,plain,
    ( spl5_3
    | spl5_4
    | spl5_1 ),
    inference(avatar_split_clause,[],[f61,f30,f67,f63])).

fof(f61,plain,
    ( v2_struct_0(sK4(sK0))
    | m1_subset_1(sK2(sK4(sK0)),u1_struct_0(sK0))
    | spl5_1 ),
    inference(subsumption_resolution,[],[f60,f47])).

fof(f47,plain,
    ( v7_waybel_0(sK4(sK0))
    | spl5_1 ),
    inference(subsumption_resolution,[],[f46,f32])).

fof(f60,plain,
    ( ~ v7_waybel_0(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | m1_subset_1(sK2(sK4(sK0)),u1_struct_0(sK0))
    | spl5_1 ),
    inference(subsumption_resolution,[],[f57,f43])).

fof(f43,plain,
    ( v4_orders_2(sK4(sK0))
    | spl5_1 ),
    inference(subsumption_resolution,[],[f42,f32])).

fof(f57,plain,
    ( ~ v4_orders_2(sK4(sK0))
    | ~ v7_waybel_0(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | m1_subset_1(sK2(sK4(sK0)),u1_struct_0(sK0))
    | spl5_1 ),
    inference(resolution,[],[f51,f38])).

fof(f38,plain,
    ( ! [X1] :
        ( ~ l1_waybel_0(X1,sK0)
        | ~ v4_orders_2(X1)
        | ~ v7_waybel_0(X1)
        | v2_struct_0(X1)
        | m1_subset_1(sK2(X1),u1_struct_0(sK0)) )
    | spl5_1 ),
    inference(subsumption_resolution,[],[f11,f32])).

% (15992)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
fof(f11,plain,(
    ! [X1] :
      ( v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,sK0)
      | m1_subset_1(sK2(X1),u1_struct_0(sK0))
      | v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f51,plain,
    ( l1_waybel_0(sK4(sK0),sK0)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f50,f32])).

fof(f37,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f14,f34,f30])).

fof(f14,plain,
    ( ~ v2_struct_0(sK1)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:27:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (15997)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.49  % (15999)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (15997)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f37,f70,f93,f110,f116,f123])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    spl5_1 | ~spl5_3 | ~spl5_5),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f122])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    $false | (spl5_1 | ~spl5_3 | ~spl5_5)),
% 0.21/0.49    inference(subsumption_resolution,[],[f121,f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ~v1_compts_1(sK0) | spl5_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    spl5_1 <=> v1_compts_1(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    v1_compts_1(sK0) | (~spl5_3 | ~spl5_5)),
% 0.21/0.49    inference(subsumption_resolution,[],[f120,f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ~v2_struct_0(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,plain,(
% 0.21/0.49    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f5])).
% 0.21/0.49  fof(f5,plain,(
% 0.21/0.49    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))))))),
% 0.21/0.49    inference(negated_conjecture,[],[f3])).
% 0.21/0.49  fof(f3,conjecture,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_yellow19)).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    v2_struct_0(sK0) | v1_compts_1(sK0) | (~spl5_3 | ~spl5_5)),
% 0.21/0.49    inference(subsumption_resolution,[],[f119,f65])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    m1_subset_1(sK2(sK4(sK0)),u1_struct_0(sK0)) | ~spl5_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f63])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    spl5_3 <=> m1_subset_1(sK2(sK4(sK0)),u1_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    ~m1_subset_1(sK2(sK4(sK0)),u1_struct_0(sK0)) | v2_struct_0(sK0) | v1_compts_1(sK0) | ~spl5_5),
% 0.21/0.49    inference(subsumption_resolution,[],[f118,f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    l1_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | ~m1_subset_1(sK2(sK4(sK0)),u1_struct_0(sK0)) | v2_struct_0(sK0) | v1_compts_1(sK0) | ~spl5_5),
% 0.21/0.49    inference(subsumption_resolution,[],[f117,f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    v2_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK2(sK4(sK0)),u1_struct_0(sK0)) | v2_struct_0(sK0) | v1_compts_1(sK0) | ~spl5_5),
% 0.21/0.49    inference(resolution,[],[f109,f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ( ! [X2,X0] : (~r3_waybel_9(X0,sK4(X0),X2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0) | v1_compts_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0] : (v1_compts_1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(X1,k6_yellow_6(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0] : ((v1_compts_1(X0) | ? [X1] : ((! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(X1,k6_yellow_6(X0))) & (l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ~(! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~r3_waybel_9(X0,X1,X2)) & r2_hidden(X1,k6_yellow_6(X0)))) => v1_compts_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_yellow19)).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    r3_waybel_9(sK0,sK4(sK0),sK2(sK4(sK0))) | ~spl5_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f107])).
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    spl5_5 <=> r3_waybel_9(sK0,sK4(sK0),sK2(sK4(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    spl5_1 | ~spl5_4),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f115])).
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    $false | (spl5_1 | ~spl5_4)),
% 0.21/0.49    inference(subsumption_resolution,[],[f114,f32])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    v1_compts_1(sK0) | ~spl5_4),
% 0.21/0.49    inference(subsumption_resolution,[],[f113,f18])).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    v2_struct_0(sK0) | v1_compts_1(sK0) | ~spl5_4),
% 0.21/0.49    inference(subsumption_resolution,[],[f112,f20])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_compts_1(sK0) | ~spl5_4),
% 0.21/0.49    inference(subsumption_resolution,[],[f111,f19])).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_compts_1(sK0) | ~spl5_4),
% 0.21/0.49    inference(resolution,[],[f69,f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ( ! [X0] : (~v2_struct_0(sK4(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v1_compts_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    v2_struct_0(sK4(sK0)) | ~spl5_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f67])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    spl5_4 <=> v2_struct_0(sK4(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    spl5_5 | spl5_4 | spl5_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f105,f30,f67,f107])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    v2_struct_0(sK4(sK0)) | r3_waybel_9(sK0,sK4(sK0),sK2(sK4(sK0))) | spl5_1),
% 0.21/0.49    inference(subsumption_resolution,[],[f104,f95])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    v7_waybel_0(sK4(sK0)) | spl5_1),
% 0.21/0.49    inference(subsumption_resolution,[],[f46,f32])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    v7_waybel_0(sK4(sK0)) | v1_compts_1(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f45,f18])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    v2_struct_0(sK0) | v7_waybel_0(sK4(sK0)) | v1_compts_1(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f44,f19])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | v7_waybel_0(sK4(sK0)) | v1_compts_1(sK0)),
% 0.21/0.49    inference(resolution,[],[f26,f20])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v7_waybel_0(sK4(X0)) | v1_compts_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    ~v7_waybel_0(sK4(sK0)) | v2_struct_0(sK4(sK0)) | r3_waybel_9(sK0,sK4(sK0),sK2(sK4(sK0))) | spl5_1),
% 0.21/0.49    inference(subsumption_resolution,[],[f103,f94])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    v4_orders_2(sK4(sK0)) | spl5_1),
% 0.21/0.49    inference(subsumption_resolution,[],[f42,f32])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    v4_orders_2(sK4(sK0)) | v1_compts_1(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f41,f18])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    v2_struct_0(sK0) | v4_orders_2(sK4(sK0)) | v1_compts_1(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f40,f19])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | v4_orders_2(sK4(sK0)) | v1_compts_1(sK0)),
% 0.21/0.50    inference(resolution,[],[f25,f20])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v4_orders_2(sK4(X0)) | v1_compts_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    ~v4_orders_2(sK4(sK0)) | ~v7_waybel_0(sK4(sK0)) | v2_struct_0(sK4(sK0)) | r3_waybel_9(sK0,sK4(sK0),sK2(sK4(sK0))) | spl5_1),
% 0.21/0.50    inference(resolution,[],[f102,f96])).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    l1_waybel_0(sK4(sK0),sK0) | spl5_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f50,f32])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    l1_waybel_0(sK4(sK0),sK0) | v1_compts_1(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f49,f18])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    v2_struct_0(sK0) | l1_waybel_0(sK4(sK0),sK0) | v1_compts_1(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f48,f19])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | l1_waybel_0(sK4(sK0),sK0) | v1_compts_1(sK0)),
% 0.21/0.50    inference(resolution,[],[f27,f20])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | l1_waybel_0(sK4(X0),X0) | v1_compts_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    ( ! [X1] : (~l1_waybel_0(X1,sK0) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | v2_struct_0(X1) | r3_waybel_9(sK0,X1,sK2(X1))) ) | spl5_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f12,f32])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ( ! [X1] : (v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,sK0) | r3_waybel_9(sK0,X1,sK2(X1)) | v1_compts_1(sK0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f93,plain,(
% 0.21/0.50    ~spl5_1 | spl5_2),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f92])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    $false | (~spl5_1 | spl5_2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f91,f82])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) | (~spl5_1 | spl5_2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f81,f18])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    v2_struct_0(sK0) | m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) | (~spl5_1 | spl5_2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f80,f72])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    v7_waybel_0(sK1) | ~spl5_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f16,f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    v1_compts_1(sK0) | ~spl5_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f30])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    v7_waybel_0(sK1) | ~v1_compts_1(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    ~v7_waybel_0(sK1) | v2_struct_0(sK0) | m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) | (~spl5_1 | spl5_2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f79,f71])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    v4_orders_2(sK1) | ~spl5_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f15,f31])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    v4_orders_2(sK1) | ~v1_compts_1(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | v2_struct_0(sK0) | m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) | (~spl5_1 | spl5_2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f78,f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ~v2_struct_0(sK1) | spl5_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    spl5_2 <=> v2_struct_0(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | v2_struct_0(sK0) | m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) | ~spl5_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f77,f31])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    ~v1_compts_1(sK0) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | v2_struct_0(sK0) | m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) | ~spl5_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f76,f20])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | v2_struct_0(sK0) | m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) | ~spl5_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f75,f19])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | v2_struct_0(sK0) | m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) | ~spl5_1),
% 0.21/0.50    inference(resolution,[],[f21,f73])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    l1_waybel_0(sK1,sK0) | ~spl5_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f17,f31])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    l1_waybel_0(sK1,sK0) | ~v1_compts_1(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~l1_waybel_0(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | v2_struct_0(X0) | m1_subset_1(sK3(X0,X1),u1_struct_0(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f7])).
% 0.21/0.50  fof(f7,plain,(
% 0.21/0.50    ! [X0] : ((! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | ~v1_compts_1(X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l37_yellow19)).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    ~m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) | (~spl5_1 | spl5_2)),
% 0.21/0.50    inference(resolution,[],[f90,f74])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ( ! [X2] : (~r3_waybel_9(sK0,sK1,X2) | ~m1_subset_1(X2,u1_struct_0(sK0))) ) | ~spl5_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f13,f31])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X2) | ~v1_compts_1(sK0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    r3_waybel_9(sK0,sK1,sK3(sK0,sK1)) | (~spl5_1 | spl5_2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f89,f18])).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    v2_struct_0(sK0) | r3_waybel_9(sK0,sK1,sK3(sK0,sK1)) | (~spl5_1 | spl5_2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f88,f72])).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    ~v7_waybel_0(sK1) | v2_struct_0(sK0) | r3_waybel_9(sK0,sK1,sK3(sK0,sK1)) | (~spl5_1 | spl5_2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f87,f71])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | v2_struct_0(sK0) | r3_waybel_9(sK0,sK1,sK3(sK0,sK1)) | (~spl5_1 | spl5_2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f86,f36])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | v2_struct_0(sK0) | r3_waybel_9(sK0,sK1,sK3(sK0,sK1)) | ~spl5_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f85,f31])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    ~v1_compts_1(sK0) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | v2_struct_0(sK0) | r3_waybel_9(sK0,sK1,sK3(sK0,sK1)) | ~spl5_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f84,f20])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | v2_struct_0(sK0) | r3_waybel_9(sK0,sK1,sK3(sK0,sK1)) | ~spl5_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f83,f19])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | v2_struct_0(sK0) | r3_waybel_9(sK0,sK1,sK3(sK0,sK1)) | ~spl5_1),
% 0.21/0.50    inference(resolution,[],[f22,f73])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~l1_waybel_0(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | v2_struct_0(X0) | r3_waybel_9(X0,X1,sK3(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    spl5_3 | spl5_4 | spl5_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f61,f30,f67,f63])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    v2_struct_0(sK4(sK0)) | m1_subset_1(sK2(sK4(sK0)),u1_struct_0(sK0)) | spl5_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f60,f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    v7_waybel_0(sK4(sK0)) | spl5_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f46,f32])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ~v7_waybel_0(sK4(sK0)) | v2_struct_0(sK4(sK0)) | m1_subset_1(sK2(sK4(sK0)),u1_struct_0(sK0)) | spl5_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f57,f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    v4_orders_2(sK4(sK0)) | spl5_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f42,f32])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ~v4_orders_2(sK4(sK0)) | ~v7_waybel_0(sK4(sK0)) | v2_struct_0(sK4(sK0)) | m1_subset_1(sK2(sK4(sK0)),u1_struct_0(sK0)) | spl5_1),
% 0.21/0.50    inference(resolution,[],[f51,f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X1] : (~l1_waybel_0(X1,sK0) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | v2_struct_0(X1) | m1_subset_1(sK2(X1),u1_struct_0(sK0))) ) | spl5_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f11,f32])).
% 0.21/0.50  % (15992)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ( ! [X1] : (v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,sK0) | m1_subset_1(sK2(X1),u1_struct_0(sK0)) | v1_compts_1(sK0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    l1_waybel_0(sK4(sK0),sK0) | spl5_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f50,f32])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ~spl5_1 | ~spl5_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f14,f34,f30])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ~v2_struct_0(sK1) | ~v1_compts_1(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (15997)------------------------------
% 0.21/0.50  % (15997)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (15997)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (15997)Memory used [KB]: 5373
% 0.21/0.50  % (15997)Time elapsed: 0.075 s
% 0.21/0.50  % (15997)------------------------------
% 0.21/0.50  % (15997)------------------------------
% 0.21/0.50  % (15990)Success in time 0.142 s
%------------------------------------------------------------------------------
