%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:19 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  182 (1597 expanded)
%              Number of leaves         :   16 ( 427 expanded)
%              Depth                    :   32
%              Number of atoms          : 1220 (16937 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f194,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f103,f126,f130,f135,f143,f155,f169,f193])).

fof(f193,plain,
    ( ~ spl6_1
    | ~ spl6_4
    | spl6_5 ),
    inference(avatar_contradiction_clause,[],[f192])).

fof(f192,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_4
    | spl6_5 ),
    inference(subsumption_resolution,[],[f191,f73])).

fof(f73,plain,
    ( sP1(sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl6_1
  <=> sP1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f191,plain,
    ( ~ sP1(sK2)
    | ~ spl6_1
    | ~ spl6_4
    | spl6_5 ),
    inference(resolution,[],[f190,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v2_struct_0(sK4(X0))
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( ( ~ r2_hidden(k1_waybel_2(X0,sK4(X0)),k10_yellow_6(X0,sK4(X0)))
          | ~ r1_waybel_9(X0,sK4(X0)) )
        & v10_waybel_0(sK4(X0),X0)
        & l1_waybel_0(sK4(X0),X0)
        & v7_waybel_0(sK4(X0))
        & v4_orders_2(sK4(X0))
        & ~ v2_struct_0(sK4(X0)) )
      | ~ sP1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1))
            | ~ r1_waybel_9(X0,X1) )
          & v10_waybel_0(X1,X0)
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
     => ( ( ~ r2_hidden(k1_waybel_2(X0,sK4(X0)),k10_yellow_6(X0,sK4(X0)))
          | ~ r1_waybel_9(X0,sK4(X0)) )
        & v10_waybel_0(sK4(X0),X0)
        & l1_waybel_0(sK4(X0),X0)
        & v7_waybel_0(sK4(X0))
        & v4_orders_2(sK4(X0))
        & ~ v2_struct_0(sK4(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1))
            | ~ r1_waybel_9(X0,X1) )
          & v10_waybel_0(X1,X0)
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      | ~ sP1(X0) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2))
            | ~ r1_waybel_9(X0,X2) )
          & v10_waybel_0(X2,X0)
          & l1_waybel_0(X2,X0)
          & v7_waybel_0(X2)
          & v4_orders_2(X2)
          & ~ v2_struct_0(X2) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2))
            | ~ r1_waybel_9(X0,X2) )
          & v10_waybel_0(X2,X0)
          & l1_waybel_0(X2,X0)
          & v7_waybel_0(X2)
          & v4_orders_2(X2)
          & ~ v2_struct_0(X2) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f190,plain,
    ( v2_struct_0(sK4(sK2))
    | ~ spl6_1
    | ~ spl6_4
    | spl6_5 ),
    inference(subsumption_resolution,[],[f189,f29])).

fof(f29,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ v2_waybel_2(sK2)
    & ! [X1] :
        ( v5_pre_topc(k4_waybel_1(sK2,X1),sK2,sK2)
        | ~ m1_subset_1(X1,u1_struct_0(sK2)) )
    & l1_waybel_9(sK2)
    & v1_compts_1(sK2)
    & v2_lattice3(sK2)
    & v1_lattice3(sK2)
    & v5_orders_2(sK2)
    & v4_orders_2(sK2)
    & v3_orders_2(sK2)
    & v8_pre_topc(sK2)
    & v2_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f8,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ~ v2_waybel_2(X0)
        & ! [X1] :
            ( v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)
            | ~ m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ~ v2_waybel_2(sK2)
      & ! [X1] :
          ( v5_pre_topc(k4_waybel_1(sK2,X1),sK2,sK2)
          | ~ m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_waybel_9(sK2)
      & v1_compts_1(sK2)
      & v2_lattice3(sK2)
      & v1_lattice3(sK2)
      & v5_orders_2(sK2)
      & v4_orders_2(sK2)
      & v3_orders_2(sK2)
      & v8_pre_topc(sK2)
      & v2_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ~ v2_waybel_2(X0)
      & ! [X1] :
          ( v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_waybel_9(X0)
      & v1_compts_1(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ~ v2_waybel_2(X0)
      & ! [X1] :
          ( v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_waybel_9(X0)
      & v1_compts_1(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_waybel_9(X0)
          & v1_compts_1(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & v8_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ( ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(X0))
             => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) )
         => v2_waybel_2(X0) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) )
       => v2_waybel_2(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_waybel_9)).

fof(f189,plain,
    ( v2_struct_0(sK4(sK2))
    | ~ v2_pre_topc(sK2)
    | ~ spl6_1
    | ~ spl6_4
    | spl6_5 ),
    inference(subsumption_resolution,[],[f188,f30])).

fof(f30,plain,(
    v8_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f188,plain,
    ( v2_struct_0(sK4(sK2))
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl6_1
    | ~ spl6_4
    | spl6_5 ),
    inference(subsumption_resolution,[],[f187,f31])).

fof(f31,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f187,plain,
    ( v2_struct_0(sK4(sK2))
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl6_1
    | ~ spl6_4
    | spl6_5 ),
    inference(subsumption_resolution,[],[f186,f32])).

fof(f32,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f186,plain,
    ( v2_struct_0(sK4(sK2))
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl6_1
    | ~ spl6_4
    | spl6_5 ),
    inference(subsumption_resolution,[],[f185,f33])).

fof(f33,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f185,plain,
    ( v2_struct_0(sK4(sK2))
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl6_1
    | ~ spl6_4
    | spl6_5 ),
    inference(subsumption_resolution,[],[f184,f34])).

fof(f34,plain,(
    v1_lattice3(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f184,plain,
    ( v2_struct_0(sK4(sK2))
    | ~ v1_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl6_1
    | ~ spl6_4
    | spl6_5 ),
    inference(subsumption_resolution,[],[f183,f35])).

fof(f35,plain,(
    v2_lattice3(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f183,plain,
    ( v2_struct_0(sK4(sK2))
    | ~ v2_lattice3(sK2)
    | ~ v1_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl6_1
    | ~ spl6_4
    | spl6_5 ),
    inference(subsumption_resolution,[],[f182,f36])).

fof(f36,plain,(
    v1_compts_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f182,plain,
    ( v2_struct_0(sK4(sK2))
    | ~ v1_compts_1(sK2)
    | ~ v2_lattice3(sK2)
    | ~ v1_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl6_1
    | ~ spl6_4
    | spl6_5 ),
    inference(subsumption_resolution,[],[f181,f37])).

fof(f37,plain,(
    l1_waybel_9(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f181,plain,
    ( v2_struct_0(sK4(sK2))
    | ~ l1_waybel_9(sK2)
    | ~ v1_compts_1(sK2)
    | ~ v2_lattice3(sK2)
    | ~ v1_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl6_1
    | ~ spl6_4
    | spl6_5 ),
    inference(subsumption_resolution,[],[f180,f120])).

fof(f120,plain,
    ( ~ sP0(sK2)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl6_5
  <=> sP0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f180,plain,
    ( v2_struct_0(sK4(sK2))
    | sP0(sK2)
    | ~ l1_waybel_9(sK2)
    | ~ v1_compts_1(sK2)
    | ~ v2_lattice3(sK2)
    | ~ v1_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl6_1
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f179,f170])).

fof(f170,plain,
    ( v4_orders_2(sK4(sK2))
    | ~ spl6_1 ),
    inference(resolution,[],[f73,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | v4_orders_2(sK4(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f179,plain,
    ( ~ v4_orders_2(sK4(sK2))
    | v2_struct_0(sK4(sK2))
    | sP0(sK2)
    | ~ l1_waybel_9(sK2)
    | ~ v1_compts_1(sK2)
    | ~ v2_lattice3(sK2)
    | ~ v1_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl6_1
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f178,f171])).

fof(f171,plain,
    ( v7_waybel_0(sK4(sK2))
    | ~ spl6_1 ),
    inference(resolution,[],[f73,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | v7_waybel_0(sK4(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f178,plain,
    ( ~ v7_waybel_0(sK4(sK2))
    | ~ v4_orders_2(sK4(sK2))
    | v2_struct_0(sK4(sK2))
    | sP0(sK2)
    | ~ l1_waybel_9(sK2)
    | ~ v1_compts_1(sK2)
    | ~ v2_lattice3(sK2)
    | ~ v1_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl6_1
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f177,f172])).

fof(f172,plain,
    ( l1_waybel_0(sK4(sK2),sK2)
    | ~ spl6_1 ),
    inference(resolution,[],[f73,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | l1_waybel_0(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f177,plain,
    ( ~ l1_waybel_0(sK4(sK2),sK2)
    | ~ v7_waybel_0(sK4(sK2))
    | ~ v4_orders_2(sK4(sK2))
    | v2_struct_0(sK4(sK2))
    | sP0(sK2)
    | ~ l1_waybel_9(sK2)
    | ~ v1_compts_1(sK2)
    | ~ v2_lattice3(sK2)
    | ~ v1_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl6_1
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f176,f173])).

fof(f173,plain,
    ( v10_waybel_0(sK4(sK2),sK2)
    | ~ spl6_1 ),
    inference(resolution,[],[f73,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | v10_waybel_0(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f176,plain,
    ( ~ v10_waybel_0(sK4(sK2),sK2)
    | ~ l1_waybel_0(sK4(sK2),sK2)
    | ~ v7_waybel_0(sK4(sK2))
    | ~ v4_orders_2(sK4(sK2))
    | v2_struct_0(sK4(sK2))
    | sP0(sK2)
    | ~ l1_waybel_9(sK2)
    | ~ v1_compts_1(sK2)
    | ~ v2_lattice3(sK2)
    | ~ v1_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl6_1
    | ~ spl6_4 ),
    inference(resolution,[],[f175,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1))
      | ~ v10_waybel_0(X1,X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | sP0(X0)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1))
            & r1_waybel_9(X0,X1) )
          | ~ v10_waybel_0(X1,X0)
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | sP0(X0)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X2] :
          ( ( r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2))
            & r1_waybel_9(X0,X2) )
          | ~ v10_waybel_0(X2,X0)
          | ~ l1_waybel_0(X2,X0)
          | ~ v7_waybel_0(X2)
          | ~ v4_orders_2(X2)
          | v2_struct_0(X2) )
      | sP0(X0)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_folding,[],[f10,f13])).

fof(f13,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ sP0(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X2] :
          ( ( r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2))
            & r1_waybel_9(X0,X2) )
          | ~ v10_waybel_0(X2,X0)
          | ~ l1_waybel_0(X2,X0)
          | ~ v7_waybel_0(X2)
          | ~ v4_orders_2(X2)
          | v2_struct_0(X2) )
      | ? [X1] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X2] :
          ( ( r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2))
            & r1_waybel_9(X0,X2) )
          | ~ v10_waybel_0(X2,X0)
          | ~ l1_waybel_0(X2,X0)
          | ~ v7_waybel_0(X2)
          | ~ v4_orders_2(X2)
          | v2_struct_0(X2) )
      | ? [X1] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,plain,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) )
       => ! [X2] :
            ( ( l1_waybel_0(X2,X0)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
           => ( v10_waybel_0(X2,X0)
             => ( r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2))
                & r1_waybel_9(X0,X2) ) ) ) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ( v10_waybel_0(X1,X0)
             => ( r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1))
                & r1_waybel_9(X0,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_waybel_9)).

fof(f175,plain,
    ( ~ r2_hidden(k1_waybel_2(sK2,sK4(sK2)),k10_yellow_6(sK2,sK4(sK2)))
    | ~ spl6_1
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f174,f101])).

fof(f101,plain,
    ( r1_waybel_9(sK2,sK4(sK2))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl6_4
  <=> r1_waybel_9(sK2,sK4(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f174,plain,
    ( ~ r1_waybel_9(sK2,sK4(sK2))
    | ~ r2_hidden(k1_waybel_2(sK2,sK4(sK2)),k10_yellow_6(sK2,sK4(sK2)))
    | ~ spl6_1 ),
    inference(resolution,[],[f73,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ r1_waybel_9(X0,sK4(X0))
      | ~ r2_hidden(k1_waybel_2(X0,sK4(X0)),k10_yellow_6(X0,sK4(X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f169,plain,
    ( spl6_2
    | ~ spl6_6 ),
    inference(avatar_contradiction_clause,[],[f168])).

fof(f168,plain,
    ( $false
    | spl6_2
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f167,f29])).

fof(f167,plain,
    ( ~ v2_pre_topc(sK2)
    | spl6_2
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f166,f30])).

fof(f166,plain,
    ( ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | spl6_2
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f165,f31])).

fof(f165,plain,
    ( ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | spl6_2
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f164,f32])).

fof(f164,plain,
    ( ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | spl6_2
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f163,f33])).

fof(f163,plain,
    ( ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | spl6_2
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f162,f34])).

fof(f162,plain,
    ( ~ v1_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | spl6_2
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f161,f35])).

fof(f161,plain,
    ( ~ v2_lattice3(sK2)
    | ~ v1_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | spl6_2
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f160,f37])).

fof(f160,plain,
    ( ~ l1_waybel_9(sK2)
    | ~ v2_lattice3(sK2)
    | ~ v1_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | spl6_2
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f159,f156])).

fof(f156,plain,
    ( ~ sP1(sK2)
    | ~ spl6_6 ),
    inference(resolution,[],[f125,f44])).

fof(f125,plain,
    ( v2_struct_0(sK4(sK2))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl6_6
  <=> v2_struct_0(sK4(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f159,plain,
    ( sP1(sK2)
    | ~ l1_waybel_9(sK2)
    | ~ v2_lattice3(sK2)
    | ~ v1_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | spl6_2 ),
    inference(subsumption_resolution,[],[f158,f39])).

fof(f39,plain,(
    ~ v2_waybel_2(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f158,plain,
    ( v2_waybel_2(sK2)
    | sP1(sK2)
    | ~ l1_waybel_9(sK2)
    | ~ v2_lattice3(sK2)
    | ~ v1_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | spl6_2 ),
    inference(resolution,[],[f157,f50])).

fof(f50,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(X0),u1_struct_0(X0))
      | v2_waybel_2(X0)
      | sP1(X0)
      | ~ l1_waybel_9(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v2_waybel_2(X0)
      | ( ~ v5_pre_topc(k4_waybel_1(X0,sK5(X0)),X0,X0)
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) )
      | sP1(X0)
      | ~ l1_waybel_9(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f16,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ~ v5_pre_topc(k4_waybel_1(X0,sK5(X0)),X0,X0)
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( v2_waybel_2(X0)
      | ? [X1] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      | sP1(X0)
      | ~ l1_waybel_9(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_folding,[],[f12,f15])).

fof(f12,plain,(
    ! [X0] :
      ( v2_waybel_2(X0)
      | ? [X1] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      | ? [X2] :
          ( ( ~ r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2))
            | ~ r1_waybel_9(X0,X2) )
          & v10_waybel_0(X2,X0)
          & l1_waybel_0(X2,X0)
          & v7_waybel_0(X2)
          & v4_orders_2(X2)
          & ~ v2_struct_0(X2) )
      | ~ l1_waybel_9(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( v2_waybel_2(X0)
      | ? [X1] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      | ? [X2] :
          ( ( ~ r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2))
            | ~ r1_waybel_9(X0,X2) )
          & v10_waybel_0(X2,X0)
          & l1_waybel_0(X2,X0)
          & v7_waybel_0(X2)
          & v4_orders_2(X2)
          & ~ v2_struct_0(X2) )
      | ~ l1_waybel_9(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( ( ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(X0))
             => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) )
          & ! [X2] :
              ( ( l1_waybel_0(X2,X0)
                & v7_waybel_0(X2)
                & v4_orders_2(X2)
                & ~ v2_struct_0(X2) )
             => ( v10_waybel_0(X2,X0)
               => ( r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2))
                  & r1_waybel_9(X0,X2) ) ) ) )
       => v2_waybel_2(X0) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( ( ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(X0))
             => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) )
          & ! [X1] :
              ( ( l1_waybel_0(X1,X0)
                & v7_waybel_0(X1)
                & v4_orders_2(X1)
                & ~ v2_struct_0(X1) )
             => ( v10_waybel_0(X1,X0)
               => ( r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1))
                  & r1_waybel_9(X0,X1) ) ) ) )
       => v2_waybel_2(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_waybel_9)).

fof(f157,plain,
    ( ~ m1_subset_1(sK5(sK2),u1_struct_0(sK2))
    | spl6_2 ),
    inference(resolution,[],[f77,f38])).

fof(f38,plain,(
    ! [X1] :
      ( v5_pre_topc(k4_waybel_1(sK2,X1),sK2,sK2)
      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f77,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK2,sK5(sK2)),sK2,sK2)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl6_2
  <=> v5_pre_topc(k4_waybel_1(sK2,sK5(sK2)),sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f155,plain,
    ( ~ spl6_1
    | spl6_4
    | ~ spl6_7 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | ~ spl6_1
    | spl6_4
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f153,f73])).

fof(f153,plain,
    ( ~ sP1(sK2)
    | ~ spl6_1
    | spl6_4
    | ~ spl6_7 ),
    inference(resolution,[],[f152,f44])).

fof(f152,plain,
    ( v2_struct_0(sK4(sK2))
    | ~ spl6_1
    | spl6_4
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f151,f146])).

fof(f146,plain,
    ( l1_waybel_0(sK4(sK2),sK2)
    | ~ spl6_1 ),
    inference(resolution,[],[f73,f47])).

fof(f151,plain,
    ( v2_struct_0(sK4(sK2))
    | ~ l1_waybel_0(sK4(sK2),sK2)
    | ~ spl6_1
    | spl6_4
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f150,f145])).

fof(f145,plain,
    ( v7_waybel_0(sK4(sK2))
    | ~ spl6_1 ),
    inference(resolution,[],[f73,f46])).

fof(f150,plain,
    ( v2_struct_0(sK4(sK2))
    | ~ v7_waybel_0(sK4(sK2))
    | ~ l1_waybel_0(sK4(sK2),sK2)
    | ~ spl6_1
    | spl6_4
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f149,f144])).

fof(f144,plain,
    ( v4_orders_2(sK4(sK2))
    | ~ spl6_1 ),
    inference(resolution,[],[f73,f45])).

fof(f149,plain,
    ( v2_struct_0(sK4(sK2))
    | ~ v4_orders_2(sK4(sK2))
    | ~ v7_waybel_0(sK4(sK2))
    | ~ l1_waybel_0(sK4(sK2),sK2)
    | ~ spl6_1
    | spl6_4
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f136,f147])).

fof(f147,plain,
    ( v10_waybel_0(sK4(sK2),sK2)
    | ~ spl6_1 ),
    inference(resolution,[],[f73,f48])).

fof(f136,plain,
    ( ~ v10_waybel_0(sK4(sK2),sK2)
    | v2_struct_0(sK4(sK2))
    | ~ v4_orders_2(sK4(sK2))
    | ~ v7_waybel_0(sK4(sK2))
    | ~ l1_waybel_0(sK4(sK2),sK2)
    | spl6_4
    | ~ spl6_7 ),
    inference(resolution,[],[f129,f102])).

fof(f102,plain,
    ( ~ r1_waybel_9(sK2,sK4(sK2))
    | spl6_4 ),
    inference(avatar_component_clause,[],[f100])).

fof(f129,plain,
    ( ! [X0] :
        ( r1_waybel_9(sK2,X0)
        | ~ v10_waybel_0(X0,sK2)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK2) )
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl6_7
  <=> ! [X0] :
        ( ~ v10_waybel_0(X0,sK2)
        | r1_waybel_9(sK2,X0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f143,plain,
    ( spl6_2
    | spl6_4
    | ~ spl6_7 ),
    inference(avatar_contradiction_clause,[],[f142])).

fof(f142,plain,
    ( $false
    | spl6_2
    | spl6_4
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f141,f89])).

fof(f89,plain,
    ( sP1(sK2)
    | spl6_2 ),
    inference(subsumption_resolution,[],[f88,f29])).

fof(f88,plain,
    ( sP1(sK2)
    | ~ v2_pre_topc(sK2)
    | spl6_2 ),
    inference(subsumption_resolution,[],[f87,f30])).

fof(f87,plain,
    ( sP1(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | spl6_2 ),
    inference(subsumption_resolution,[],[f86,f31])).

fof(f86,plain,
    ( sP1(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | spl6_2 ),
    inference(subsumption_resolution,[],[f85,f32])).

fof(f85,plain,
    ( sP1(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | spl6_2 ),
    inference(subsumption_resolution,[],[f84,f33])).

fof(f84,plain,
    ( sP1(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | spl6_2 ),
    inference(subsumption_resolution,[],[f83,f34])).

fof(f83,plain,
    ( sP1(sK2)
    | ~ v1_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | spl6_2 ),
    inference(subsumption_resolution,[],[f82,f35])).

fof(f82,plain,
    ( sP1(sK2)
    | ~ v2_lattice3(sK2)
    | ~ v1_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | spl6_2 ),
    inference(subsumption_resolution,[],[f81,f37])).

fof(f81,plain,
    ( sP1(sK2)
    | ~ l1_waybel_9(sK2)
    | ~ v2_lattice3(sK2)
    | ~ v1_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | spl6_2 ),
    inference(subsumption_resolution,[],[f80,f39])).

fof(f80,plain,
    ( v2_waybel_2(sK2)
    | sP1(sK2)
    | ~ l1_waybel_9(sK2)
    | ~ v2_lattice3(sK2)
    | ~ v1_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | spl6_2 ),
    inference(resolution,[],[f79,f50])).

fof(f79,plain,
    ( ~ m1_subset_1(sK5(sK2),u1_struct_0(sK2))
    | spl6_2 ),
    inference(resolution,[],[f38,f77])).

fof(f141,plain,
    ( ~ sP1(sK2)
    | spl6_2
    | spl6_4
    | ~ spl6_7 ),
    inference(resolution,[],[f140,f44])).

fof(f140,plain,
    ( v2_struct_0(sK4(sK2))
    | spl6_2
    | spl6_4
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f139,f92])).

fof(f92,plain,
    ( l1_waybel_0(sK4(sK2),sK2)
    | spl6_2 ),
    inference(resolution,[],[f89,f47])).

fof(f139,plain,
    ( v2_struct_0(sK4(sK2))
    | ~ l1_waybel_0(sK4(sK2),sK2)
    | spl6_2
    | spl6_4
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f138,f91])).

fof(f91,plain,
    ( v7_waybel_0(sK4(sK2))
    | spl6_2 ),
    inference(resolution,[],[f89,f46])).

fof(f138,plain,
    ( v2_struct_0(sK4(sK2))
    | ~ v7_waybel_0(sK4(sK2))
    | ~ l1_waybel_0(sK4(sK2),sK2)
    | spl6_2
    | spl6_4
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f137,f90])).

fof(f90,plain,
    ( v4_orders_2(sK4(sK2))
    | spl6_2 ),
    inference(resolution,[],[f89,f45])).

fof(f137,plain,
    ( v2_struct_0(sK4(sK2))
    | ~ v4_orders_2(sK4(sK2))
    | ~ v7_waybel_0(sK4(sK2))
    | ~ l1_waybel_0(sK4(sK2),sK2)
    | spl6_2
    | spl6_4
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f136,f93])).

fof(f93,plain,
    ( v10_waybel_0(sK4(sK2),sK2)
    | spl6_2 ),
    inference(resolution,[],[f89,f48])).

fof(f135,plain,(
    ~ spl6_5 ),
    inference(avatar_contradiction_clause,[],[f134])).

fof(f134,plain,
    ( $false
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f133,f121])).

fof(f121,plain,
    ( sP0(sK2)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f119])).

fof(f133,plain,
    ( ~ sP0(sK2)
    | ~ spl6_5 ),
    inference(resolution,[],[f132,f40])).

fof(f40,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) )
      | ~ sP0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f20])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ sP0(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f132,plain,
    ( ~ m1_subset_1(sK3(sK2),u1_struct_0(sK2))
    | ~ spl6_5 ),
    inference(resolution,[],[f131,f38])).

fof(f131,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK2,sK3(sK2)),sK2,sK2)
    | ~ spl6_5 ),
    inference(resolution,[],[f121,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f130,plain,
    ( spl6_5
    | spl6_7 ),
    inference(avatar_split_clause,[],[f60,f128,f119])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v10_waybel_0(X0,sK2)
      | ~ l1_waybel_0(X0,sK2)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | sP0(sK2)
      | r1_waybel_9(sK2,X0) ) ),
    inference(global_subsumption,[],[f37,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v10_waybel_0(X0,sK2)
      | ~ l1_waybel_0(X0,sK2)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | sP0(sK2)
      | ~ l1_waybel_9(sK2)
      | r1_waybel_9(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f58,f29])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v10_waybel_0(X0,sK2)
      | ~ l1_waybel_0(X0,sK2)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | sP0(sK2)
      | ~ l1_waybel_9(sK2)
      | r1_waybel_9(sK2,X0)
      | ~ v2_pre_topc(sK2) ) ),
    inference(subsumption_resolution,[],[f57,f30])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v10_waybel_0(X0,sK2)
      | ~ l1_waybel_0(X0,sK2)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | sP0(sK2)
      | ~ l1_waybel_9(sK2)
      | r1_waybel_9(sK2,X0)
      | ~ v8_pre_topc(sK2)
      | ~ v2_pre_topc(sK2) ) ),
    inference(subsumption_resolution,[],[f56,f31])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v10_waybel_0(X0,sK2)
      | ~ l1_waybel_0(X0,sK2)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | sP0(sK2)
      | ~ l1_waybel_9(sK2)
      | r1_waybel_9(sK2,X0)
      | ~ v3_orders_2(sK2)
      | ~ v8_pre_topc(sK2)
      | ~ v2_pre_topc(sK2) ) ),
    inference(subsumption_resolution,[],[f55,f32])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v10_waybel_0(X0,sK2)
      | ~ l1_waybel_0(X0,sK2)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | sP0(sK2)
      | ~ l1_waybel_9(sK2)
      | r1_waybel_9(sK2,X0)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | ~ v8_pre_topc(sK2)
      | ~ v2_pre_topc(sK2) ) ),
    inference(subsumption_resolution,[],[f54,f33])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v10_waybel_0(X0,sK2)
      | ~ l1_waybel_0(X0,sK2)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | sP0(sK2)
      | ~ l1_waybel_9(sK2)
      | r1_waybel_9(sK2,X0)
      | ~ v5_orders_2(sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | ~ v8_pre_topc(sK2)
      | ~ v2_pre_topc(sK2) ) ),
    inference(subsumption_resolution,[],[f53,f34])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v10_waybel_0(X0,sK2)
      | ~ l1_waybel_0(X0,sK2)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | sP0(sK2)
      | ~ l1_waybel_9(sK2)
      | r1_waybel_9(sK2,X0)
      | ~ v1_lattice3(sK2)
      | ~ v5_orders_2(sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | ~ v8_pre_topc(sK2)
      | ~ v2_pre_topc(sK2) ) ),
    inference(subsumption_resolution,[],[f52,f35])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v10_waybel_0(X0,sK2)
      | ~ l1_waybel_0(X0,sK2)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | sP0(sK2)
      | ~ l1_waybel_9(sK2)
      | r1_waybel_9(sK2,X0)
      | ~ v2_lattice3(sK2)
      | ~ v1_lattice3(sK2)
      | ~ v5_orders_2(sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | ~ v8_pre_topc(sK2)
      | ~ v2_pre_topc(sK2) ) ),
    inference(resolution,[],[f36,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_compts_1(X0)
      | ~ v10_waybel_0(X1,X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | sP0(X0)
      | ~ l1_waybel_9(X0)
      | r1_waybel_9(X0,X1)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f126,plain,
    ( spl6_5
    | spl6_6
    | spl6_2
    | spl6_3 ),
    inference(avatar_split_clause,[],[f117,f96,f75,f123,f119])).

fof(f96,plain,
    ( spl6_3
  <=> r2_hidden(k1_waybel_2(sK2,sK4(sK2)),k10_yellow_6(sK2,sK4(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f117,plain,
    ( v2_struct_0(sK4(sK2))
    | sP0(sK2)
    | spl6_2
    | spl6_3 ),
    inference(subsumption_resolution,[],[f116,f29])).

fof(f116,plain,
    ( v2_struct_0(sK4(sK2))
    | sP0(sK2)
    | ~ v2_pre_topc(sK2)
    | spl6_2
    | spl6_3 ),
    inference(subsumption_resolution,[],[f115,f30])).

fof(f115,plain,
    ( v2_struct_0(sK4(sK2))
    | sP0(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | spl6_2
    | spl6_3 ),
    inference(subsumption_resolution,[],[f114,f31])).

fof(f114,plain,
    ( v2_struct_0(sK4(sK2))
    | sP0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | spl6_2
    | spl6_3 ),
    inference(subsumption_resolution,[],[f113,f32])).

fof(f113,plain,
    ( v2_struct_0(sK4(sK2))
    | sP0(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | spl6_2
    | spl6_3 ),
    inference(subsumption_resolution,[],[f112,f33])).

fof(f112,plain,
    ( v2_struct_0(sK4(sK2))
    | sP0(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | spl6_2
    | spl6_3 ),
    inference(subsumption_resolution,[],[f111,f34])).

fof(f111,plain,
    ( v2_struct_0(sK4(sK2))
    | sP0(sK2)
    | ~ v1_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | spl6_2
    | spl6_3 ),
    inference(subsumption_resolution,[],[f110,f35])).

fof(f110,plain,
    ( v2_struct_0(sK4(sK2))
    | sP0(sK2)
    | ~ v2_lattice3(sK2)
    | ~ v1_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | spl6_2
    | spl6_3 ),
    inference(subsumption_resolution,[],[f109,f36])).

fof(f109,plain,
    ( v2_struct_0(sK4(sK2))
    | sP0(sK2)
    | ~ v1_compts_1(sK2)
    | ~ v2_lattice3(sK2)
    | ~ v1_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | spl6_2
    | spl6_3 ),
    inference(subsumption_resolution,[],[f108,f37])).

fof(f108,plain,
    ( v2_struct_0(sK4(sK2))
    | sP0(sK2)
    | ~ l1_waybel_9(sK2)
    | ~ v1_compts_1(sK2)
    | ~ v2_lattice3(sK2)
    | ~ v1_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | spl6_2
    | spl6_3 ),
    inference(subsumption_resolution,[],[f107,f90])).

fof(f107,plain,
    ( ~ v4_orders_2(sK4(sK2))
    | v2_struct_0(sK4(sK2))
    | sP0(sK2)
    | ~ l1_waybel_9(sK2)
    | ~ v1_compts_1(sK2)
    | ~ v2_lattice3(sK2)
    | ~ v1_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | spl6_2
    | spl6_3 ),
    inference(subsumption_resolution,[],[f106,f91])).

fof(f106,plain,
    ( ~ v7_waybel_0(sK4(sK2))
    | ~ v4_orders_2(sK4(sK2))
    | v2_struct_0(sK4(sK2))
    | sP0(sK2)
    | ~ l1_waybel_9(sK2)
    | ~ v1_compts_1(sK2)
    | ~ v2_lattice3(sK2)
    | ~ v1_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | spl6_2
    | spl6_3 ),
    inference(subsumption_resolution,[],[f105,f92])).

fof(f105,plain,
    ( ~ l1_waybel_0(sK4(sK2),sK2)
    | ~ v7_waybel_0(sK4(sK2))
    | ~ v4_orders_2(sK4(sK2))
    | v2_struct_0(sK4(sK2))
    | sP0(sK2)
    | ~ l1_waybel_9(sK2)
    | ~ v1_compts_1(sK2)
    | ~ v2_lattice3(sK2)
    | ~ v1_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | spl6_2
    | spl6_3 ),
    inference(subsumption_resolution,[],[f104,f93])).

fof(f104,plain,
    ( ~ v10_waybel_0(sK4(sK2),sK2)
    | ~ l1_waybel_0(sK4(sK2),sK2)
    | ~ v7_waybel_0(sK4(sK2))
    | ~ v4_orders_2(sK4(sK2))
    | v2_struct_0(sK4(sK2))
    | sP0(sK2)
    | ~ l1_waybel_9(sK2)
    | ~ v1_compts_1(sK2)
    | ~ v2_lattice3(sK2)
    | ~ v1_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | spl6_3 ),
    inference(resolution,[],[f98,f43])).

fof(f98,plain,
    ( ~ r2_hidden(k1_waybel_2(sK2,sK4(sK2)),k10_yellow_6(sK2,sK4(sK2)))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f96])).

fof(f103,plain,
    ( ~ spl6_3
    | ~ spl6_4
    | spl6_2 ),
    inference(avatar_split_clause,[],[f94,f75,f100,f96])).

% (25113)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
fof(f94,plain,
    ( ~ r1_waybel_9(sK2,sK4(sK2))
    | ~ r2_hidden(k1_waybel_2(sK2,sK4(sK2)),k10_yellow_6(sK2,sK4(sK2)))
    | spl6_2 ),
    inference(resolution,[],[f89,f49])).

fof(f78,plain,
    ( spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f69,f75,f71])).

fof(f69,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK2,sK5(sK2)),sK2,sK2)
    | sP1(sK2) ),
    inference(global_subsumption,[],[f39,f68])).

fof(f68,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK2,sK5(sK2)),sK2,sK2)
    | sP1(sK2)
    | v2_waybel_2(sK2) ),
    inference(subsumption_resolution,[],[f67,f29])).

fof(f67,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK2,sK5(sK2)),sK2,sK2)
    | sP1(sK2)
    | v2_waybel_2(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f66,f30])).

fof(f66,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK2,sK5(sK2)),sK2,sK2)
    | sP1(sK2)
    | v2_waybel_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f65,f31])).

fof(f65,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK2,sK5(sK2)),sK2,sK2)
    | sP1(sK2)
    | v2_waybel_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f64,f32])).

fof(f64,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK2,sK5(sK2)),sK2,sK2)
    | sP1(sK2)
    | v2_waybel_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f63,f33])).

fof(f63,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK2,sK5(sK2)),sK2,sK2)
    | sP1(sK2)
    | v2_waybel_2(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f62,f34])).

fof(f62,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK2,sK5(sK2)),sK2,sK2)
    | sP1(sK2)
    | v2_waybel_2(sK2)
    | ~ v1_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f61,f35])).

fof(f61,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK2,sK5(sK2)),sK2,sK2)
    | sP1(sK2)
    | v2_waybel_2(sK2)
    | ~ v2_lattice3(sK2)
    | ~ v1_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(resolution,[],[f37,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ l1_waybel_9(X0)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK5(X0)),X0,X0)
      | sP1(X0)
      | v2_waybel_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:12:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.42  % (25117)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.19/0.42  % (25117)Refutation found. Thanks to Tanya!
% 0.19/0.42  % SZS status Theorem for theBenchmark
% 0.19/0.42  % SZS output start Proof for theBenchmark
% 0.19/0.42  fof(f194,plain,(
% 0.19/0.42    $false),
% 0.19/0.42    inference(avatar_sat_refutation,[],[f78,f103,f126,f130,f135,f143,f155,f169,f193])).
% 0.19/0.42  fof(f193,plain,(
% 0.19/0.42    ~spl6_1 | ~spl6_4 | spl6_5),
% 0.19/0.42    inference(avatar_contradiction_clause,[],[f192])).
% 0.19/0.42  fof(f192,plain,(
% 0.19/0.42    $false | (~spl6_1 | ~spl6_4 | spl6_5)),
% 0.19/0.42    inference(subsumption_resolution,[],[f191,f73])).
% 0.19/0.42  fof(f73,plain,(
% 0.19/0.42    sP1(sK2) | ~spl6_1),
% 0.19/0.42    inference(avatar_component_clause,[],[f71])).
% 0.19/0.42  fof(f71,plain,(
% 0.19/0.42    spl6_1 <=> sP1(sK2)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.19/0.42  fof(f191,plain,(
% 0.19/0.42    ~sP1(sK2) | (~spl6_1 | ~spl6_4 | spl6_5)),
% 0.19/0.42    inference(resolution,[],[f190,f44])).
% 0.19/0.42  fof(f44,plain,(
% 0.19/0.42    ( ! [X0] : (~v2_struct_0(sK4(X0)) | ~sP1(X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f26])).
% 0.19/0.42  fof(f26,plain,(
% 0.19/0.42    ! [X0] : (((~r2_hidden(k1_waybel_2(X0,sK4(X0)),k10_yellow_6(X0,sK4(X0))) | ~r1_waybel_9(X0,sK4(X0))) & v10_waybel_0(sK4(X0),X0) & l1_waybel_0(sK4(X0),X0) & v7_waybel_0(sK4(X0)) & v4_orders_2(sK4(X0)) & ~v2_struct_0(sK4(X0))) | ~sP1(X0))),
% 0.19/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).
% 0.19/0.42  fof(f25,plain,(
% 0.19/0.42    ! [X0] : (? [X1] : ((~r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1)) | ~r1_waybel_9(X0,X1)) & v10_waybel_0(X1,X0) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ((~r2_hidden(k1_waybel_2(X0,sK4(X0)),k10_yellow_6(X0,sK4(X0))) | ~r1_waybel_9(X0,sK4(X0))) & v10_waybel_0(sK4(X0),X0) & l1_waybel_0(sK4(X0),X0) & v7_waybel_0(sK4(X0)) & v4_orders_2(sK4(X0)) & ~v2_struct_0(sK4(X0))))),
% 0.19/0.42    introduced(choice_axiom,[])).
% 0.19/0.42  fof(f24,plain,(
% 0.19/0.42    ! [X0] : (? [X1] : ((~r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1)) | ~r1_waybel_9(X0,X1)) & v10_waybel_0(X1,X0) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~sP1(X0))),
% 0.19/0.42    inference(rectify,[],[f23])).
% 0.19/0.42  fof(f23,plain,(
% 0.19/0.42    ! [X0] : (? [X2] : ((~r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2)) | ~r1_waybel_9(X0,X2)) & v10_waybel_0(X2,X0) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~sP1(X0))),
% 0.19/0.42    inference(nnf_transformation,[],[f15])).
% 0.19/0.42  fof(f15,plain,(
% 0.19/0.42    ! [X0] : (? [X2] : ((~r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2)) | ~r1_waybel_9(X0,X2)) & v10_waybel_0(X2,X0) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~sP1(X0))),
% 0.19/0.42    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.19/0.42  fof(f190,plain,(
% 0.19/0.42    v2_struct_0(sK4(sK2)) | (~spl6_1 | ~spl6_4 | spl6_5)),
% 0.19/0.42    inference(subsumption_resolution,[],[f189,f29])).
% 0.19/0.42  fof(f29,plain,(
% 0.19/0.42    v2_pre_topc(sK2)),
% 0.19/0.42    inference(cnf_transformation,[],[f18])).
% 0.19/0.42  fof(f18,plain,(
% 0.19/0.42    ~v2_waybel_2(sK2) & ! [X1] : (v5_pre_topc(k4_waybel_1(sK2,X1),sK2,sK2) | ~m1_subset_1(X1,u1_struct_0(sK2))) & l1_waybel_9(sK2) & v1_compts_1(sK2) & v2_lattice3(sK2) & v1_lattice3(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & v8_pre_topc(sK2) & v2_pre_topc(sK2)),
% 0.19/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f8,f17])).
% 0.19/0.42  fof(f17,plain,(
% 0.19/0.42    ? [X0] : (~v2_waybel_2(X0) & ! [X1] : (v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) | ~m1_subset_1(X1,u1_struct_0(X0))) & l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (~v2_waybel_2(sK2) & ! [X1] : (v5_pre_topc(k4_waybel_1(sK2,X1),sK2,sK2) | ~m1_subset_1(X1,u1_struct_0(sK2))) & l1_waybel_9(sK2) & v1_compts_1(sK2) & v2_lattice3(sK2) & v1_lattice3(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & v8_pre_topc(sK2) & v2_pre_topc(sK2))),
% 0.19/0.42    introduced(choice_axiom,[])).
% 0.19/0.42  fof(f8,plain,(
% 0.19/0.42    ? [X0] : (~v2_waybel_2(X0) & ! [X1] : (v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) | ~m1_subset_1(X1,u1_struct_0(X0))) & l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0))),
% 0.19/0.42    inference(flattening,[],[f7])).
% 0.19/0.42  fof(f7,plain,(
% 0.19/0.42    ? [X0] : ((~v2_waybel_2(X0) & ! [X1] : (v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.19/0.42    inference(ennf_transformation,[],[f4])).
% 0.19/0.42  fof(f4,negated_conjecture,(
% 0.19/0.42    ~! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)) => v2_waybel_2(X0)))),
% 0.19/0.42    inference(negated_conjecture,[],[f3])).
% 0.19/0.42  fof(f3,conjecture,(
% 0.19/0.42    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)) => v2_waybel_2(X0)))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_waybel_9)).
% 0.19/0.42  fof(f189,plain,(
% 0.19/0.42    v2_struct_0(sK4(sK2)) | ~v2_pre_topc(sK2) | (~spl6_1 | ~spl6_4 | spl6_5)),
% 0.19/0.42    inference(subsumption_resolution,[],[f188,f30])).
% 0.19/0.42  fof(f30,plain,(
% 0.19/0.42    v8_pre_topc(sK2)),
% 0.19/0.42    inference(cnf_transformation,[],[f18])).
% 0.19/0.42  fof(f188,plain,(
% 0.19/0.42    v2_struct_0(sK4(sK2)) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2) | (~spl6_1 | ~spl6_4 | spl6_5)),
% 0.19/0.42    inference(subsumption_resolution,[],[f187,f31])).
% 0.19/0.42  fof(f31,plain,(
% 0.19/0.42    v3_orders_2(sK2)),
% 0.19/0.42    inference(cnf_transformation,[],[f18])).
% 0.19/0.42  fof(f187,plain,(
% 0.19/0.42    v2_struct_0(sK4(sK2)) | ~v3_orders_2(sK2) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2) | (~spl6_1 | ~spl6_4 | spl6_5)),
% 0.19/0.42    inference(subsumption_resolution,[],[f186,f32])).
% 0.19/0.42  fof(f32,plain,(
% 0.19/0.42    v4_orders_2(sK2)),
% 0.19/0.42    inference(cnf_transformation,[],[f18])).
% 0.19/0.42  fof(f186,plain,(
% 0.19/0.42    v2_struct_0(sK4(sK2)) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2) | (~spl6_1 | ~spl6_4 | spl6_5)),
% 0.19/0.42    inference(subsumption_resolution,[],[f185,f33])).
% 0.19/0.42  fof(f33,plain,(
% 0.19/0.42    v5_orders_2(sK2)),
% 0.19/0.42    inference(cnf_transformation,[],[f18])).
% 0.19/0.42  fof(f185,plain,(
% 0.19/0.42    v2_struct_0(sK4(sK2)) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2) | (~spl6_1 | ~spl6_4 | spl6_5)),
% 0.19/0.42    inference(subsumption_resolution,[],[f184,f34])).
% 0.19/0.42  fof(f34,plain,(
% 0.19/0.42    v1_lattice3(sK2)),
% 0.19/0.42    inference(cnf_transformation,[],[f18])).
% 0.19/0.42  fof(f184,plain,(
% 0.19/0.42    v2_struct_0(sK4(sK2)) | ~v1_lattice3(sK2) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2) | (~spl6_1 | ~spl6_4 | spl6_5)),
% 0.19/0.42    inference(subsumption_resolution,[],[f183,f35])).
% 0.19/0.42  fof(f35,plain,(
% 0.19/0.42    v2_lattice3(sK2)),
% 0.19/0.42    inference(cnf_transformation,[],[f18])).
% 0.19/0.42  fof(f183,plain,(
% 0.19/0.42    v2_struct_0(sK4(sK2)) | ~v2_lattice3(sK2) | ~v1_lattice3(sK2) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2) | (~spl6_1 | ~spl6_4 | spl6_5)),
% 0.19/0.42    inference(subsumption_resolution,[],[f182,f36])).
% 0.19/0.42  fof(f36,plain,(
% 0.19/0.42    v1_compts_1(sK2)),
% 0.19/0.42    inference(cnf_transformation,[],[f18])).
% 0.19/0.42  fof(f182,plain,(
% 0.19/0.42    v2_struct_0(sK4(sK2)) | ~v1_compts_1(sK2) | ~v2_lattice3(sK2) | ~v1_lattice3(sK2) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2) | (~spl6_1 | ~spl6_4 | spl6_5)),
% 0.19/0.42    inference(subsumption_resolution,[],[f181,f37])).
% 0.19/0.42  fof(f37,plain,(
% 0.19/0.42    l1_waybel_9(sK2)),
% 0.19/0.42    inference(cnf_transformation,[],[f18])).
% 0.19/0.42  fof(f181,plain,(
% 0.19/0.42    v2_struct_0(sK4(sK2)) | ~l1_waybel_9(sK2) | ~v1_compts_1(sK2) | ~v2_lattice3(sK2) | ~v1_lattice3(sK2) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2) | (~spl6_1 | ~spl6_4 | spl6_5)),
% 0.19/0.42    inference(subsumption_resolution,[],[f180,f120])).
% 0.19/0.42  fof(f120,plain,(
% 0.19/0.42    ~sP0(sK2) | spl6_5),
% 0.19/0.42    inference(avatar_component_clause,[],[f119])).
% 0.19/0.42  fof(f119,plain,(
% 0.19/0.42    spl6_5 <=> sP0(sK2)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.19/0.42  fof(f180,plain,(
% 0.19/0.42    v2_struct_0(sK4(sK2)) | sP0(sK2) | ~l1_waybel_9(sK2) | ~v1_compts_1(sK2) | ~v2_lattice3(sK2) | ~v1_lattice3(sK2) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2) | (~spl6_1 | ~spl6_4)),
% 0.19/0.42    inference(subsumption_resolution,[],[f179,f170])).
% 0.19/0.42  fof(f170,plain,(
% 0.19/0.42    v4_orders_2(sK4(sK2)) | ~spl6_1),
% 0.19/0.42    inference(resolution,[],[f73,f45])).
% 0.19/0.42  fof(f45,plain,(
% 0.19/0.42    ( ! [X0] : (~sP1(X0) | v4_orders_2(sK4(X0))) )),
% 0.19/0.42    inference(cnf_transformation,[],[f26])).
% 0.19/0.42  fof(f179,plain,(
% 0.19/0.42    ~v4_orders_2(sK4(sK2)) | v2_struct_0(sK4(sK2)) | sP0(sK2) | ~l1_waybel_9(sK2) | ~v1_compts_1(sK2) | ~v2_lattice3(sK2) | ~v1_lattice3(sK2) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2) | (~spl6_1 | ~spl6_4)),
% 0.19/0.42    inference(subsumption_resolution,[],[f178,f171])).
% 0.19/0.42  fof(f171,plain,(
% 0.19/0.42    v7_waybel_0(sK4(sK2)) | ~spl6_1),
% 0.19/0.42    inference(resolution,[],[f73,f46])).
% 0.19/0.42  fof(f46,plain,(
% 0.19/0.42    ( ! [X0] : (~sP1(X0) | v7_waybel_0(sK4(X0))) )),
% 0.19/0.42    inference(cnf_transformation,[],[f26])).
% 0.19/0.42  fof(f178,plain,(
% 0.19/0.42    ~v7_waybel_0(sK4(sK2)) | ~v4_orders_2(sK4(sK2)) | v2_struct_0(sK4(sK2)) | sP0(sK2) | ~l1_waybel_9(sK2) | ~v1_compts_1(sK2) | ~v2_lattice3(sK2) | ~v1_lattice3(sK2) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2) | (~spl6_1 | ~spl6_4)),
% 0.19/0.42    inference(subsumption_resolution,[],[f177,f172])).
% 0.19/0.42  fof(f172,plain,(
% 0.19/0.42    l1_waybel_0(sK4(sK2),sK2) | ~spl6_1),
% 0.19/0.42    inference(resolution,[],[f73,f47])).
% 0.19/0.42  fof(f47,plain,(
% 0.19/0.42    ( ! [X0] : (~sP1(X0) | l1_waybel_0(sK4(X0),X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f26])).
% 0.19/0.42  fof(f177,plain,(
% 0.19/0.42    ~l1_waybel_0(sK4(sK2),sK2) | ~v7_waybel_0(sK4(sK2)) | ~v4_orders_2(sK4(sK2)) | v2_struct_0(sK4(sK2)) | sP0(sK2) | ~l1_waybel_9(sK2) | ~v1_compts_1(sK2) | ~v2_lattice3(sK2) | ~v1_lattice3(sK2) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2) | (~spl6_1 | ~spl6_4)),
% 0.19/0.42    inference(subsumption_resolution,[],[f176,f173])).
% 0.19/0.42  fof(f173,plain,(
% 0.19/0.42    v10_waybel_0(sK4(sK2),sK2) | ~spl6_1),
% 0.19/0.42    inference(resolution,[],[f73,f48])).
% 0.19/0.42  fof(f48,plain,(
% 0.19/0.42    ( ! [X0] : (~sP1(X0) | v10_waybel_0(sK4(X0),X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f26])).
% 0.19/0.42  fof(f176,plain,(
% 0.19/0.42    ~v10_waybel_0(sK4(sK2),sK2) | ~l1_waybel_0(sK4(sK2),sK2) | ~v7_waybel_0(sK4(sK2)) | ~v4_orders_2(sK4(sK2)) | v2_struct_0(sK4(sK2)) | sP0(sK2) | ~l1_waybel_9(sK2) | ~v1_compts_1(sK2) | ~v2_lattice3(sK2) | ~v1_lattice3(sK2) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2) | (~spl6_1 | ~spl6_4)),
% 0.19/0.42    inference(resolution,[],[f175,f43])).
% 0.19/0.42  fof(f43,plain,(
% 0.19/0.42    ( ! [X0,X1] : (r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1)) | ~v10_waybel_0(X1,X0) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | sP0(X0) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f22])).
% 0.19/0.42  fof(f22,plain,(
% 0.19/0.42    ! [X0] : (! [X1] : ((r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1)) & r1_waybel_9(X0,X1)) | ~v10_waybel_0(X1,X0) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | sP0(X0) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.42    inference(rectify,[],[f14])).
% 0.19/0.42  fof(f14,plain,(
% 0.19/0.42    ! [X0] : (! [X2] : ((r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2)) & r1_waybel_9(X0,X2)) | ~v10_waybel_0(X2,X0) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2)) | sP0(X0) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.42    inference(definition_folding,[],[f10,f13])).
% 0.19/0.42  fof(f13,plain,(
% 0.19/0.42    ! [X0] : (? [X1] : (~v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) & m1_subset_1(X1,u1_struct_0(X0))) | ~sP0(X0))),
% 0.19/0.42    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.19/0.42  fof(f10,plain,(
% 0.19/0.42    ! [X0] : (! [X2] : ((r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2)) & r1_waybel_9(X0,X2)) | ~v10_waybel_0(X2,X0) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2)) | ? [X1] : (~v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) & m1_subset_1(X1,u1_struct_0(X0))) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.42    inference(flattening,[],[f9])).
% 0.19/0.42  fof(f9,plain,(
% 0.19/0.42    ! [X0] : ((! [X2] : (((r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2)) & r1_waybel_9(X0,X2)) | ~v10_waybel_0(X2,X0)) | (~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2))) | ? [X1] : (~v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) & m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.19/0.42    inference(ennf_transformation,[],[f5])).
% 0.19/0.42  fof(f5,plain,(
% 0.19/0.42    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (v10_waybel_0(X2,X0) => (r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2)) & r1_waybel_9(X0,X2))))))),
% 0.19/0.42    inference(rectify,[],[f2])).
% 0.19/0.42  fof(f2,axiom,(
% 0.19/0.42    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (v10_waybel_0(X1,X0) => (r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1)) & r1_waybel_9(X0,X1))))))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_waybel_9)).
% 0.19/0.42  fof(f175,plain,(
% 0.19/0.42    ~r2_hidden(k1_waybel_2(sK2,sK4(sK2)),k10_yellow_6(sK2,sK4(sK2))) | (~spl6_1 | ~spl6_4)),
% 0.19/0.42    inference(subsumption_resolution,[],[f174,f101])).
% 0.19/0.42  fof(f101,plain,(
% 0.19/0.42    r1_waybel_9(sK2,sK4(sK2)) | ~spl6_4),
% 0.19/0.42    inference(avatar_component_clause,[],[f100])).
% 0.19/0.42  fof(f100,plain,(
% 0.19/0.42    spl6_4 <=> r1_waybel_9(sK2,sK4(sK2))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.19/0.42  fof(f174,plain,(
% 0.19/0.42    ~r1_waybel_9(sK2,sK4(sK2)) | ~r2_hidden(k1_waybel_2(sK2,sK4(sK2)),k10_yellow_6(sK2,sK4(sK2))) | ~spl6_1),
% 0.19/0.42    inference(resolution,[],[f73,f49])).
% 0.19/0.42  fof(f49,plain,(
% 0.19/0.42    ( ! [X0] : (~sP1(X0) | ~r1_waybel_9(X0,sK4(X0)) | ~r2_hidden(k1_waybel_2(X0,sK4(X0)),k10_yellow_6(X0,sK4(X0)))) )),
% 0.19/0.42    inference(cnf_transformation,[],[f26])).
% 0.19/0.42  fof(f169,plain,(
% 0.19/0.42    spl6_2 | ~spl6_6),
% 0.19/0.42    inference(avatar_contradiction_clause,[],[f168])).
% 0.19/0.42  fof(f168,plain,(
% 0.19/0.42    $false | (spl6_2 | ~spl6_6)),
% 0.19/0.42    inference(subsumption_resolution,[],[f167,f29])).
% 0.19/0.42  fof(f167,plain,(
% 0.19/0.42    ~v2_pre_topc(sK2) | (spl6_2 | ~spl6_6)),
% 0.19/0.42    inference(subsumption_resolution,[],[f166,f30])).
% 0.19/0.42  fof(f166,plain,(
% 0.19/0.42    ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2) | (spl6_2 | ~spl6_6)),
% 0.19/0.42    inference(subsumption_resolution,[],[f165,f31])).
% 0.19/0.42  fof(f165,plain,(
% 0.19/0.42    ~v3_orders_2(sK2) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2) | (spl6_2 | ~spl6_6)),
% 0.19/0.42    inference(subsumption_resolution,[],[f164,f32])).
% 0.19/0.42  fof(f164,plain,(
% 0.19/0.42    ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2) | (spl6_2 | ~spl6_6)),
% 0.19/0.42    inference(subsumption_resolution,[],[f163,f33])).
% 0.19/0.42  fof(f163,plain,(
% 0.19/0.42    ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2) | (spl6_2 | ~spl6_6)),
% 0.19/0.42    inference(subsumption_resolution,[],[f162,f34])).
% 0.19/0.42  fof(f162,plain,(
% 0.19/0.42    ~v1_lattice3(sK2) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2) | (spl6_2 | ~spl6_6)),
% 0.19/0.42    inference(subsumption_resolution,[],[f161,f35])).
% 0.19/0.42  fof(f161,plain,(
% 0.19/0.42    ~v2_lattice3(sK2) | ~v1_lattice3(sK2) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2) | (spl6_2 | ~spl6_6)),
% 0.19/0.42    inference(subsumption_resolution,[],[f160,f37])).
% 0.19/0.42  fof(f160,plain,(
% 0.19/0.42    ~l1_waybel_9(sK2) | ~v2_lattice3(sK2) | ~v1_lattice3(sK2) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2) | (spl6_2 | ~spl6_6)),
% 0.19/0.42    inference(subsumption_resolution,[],[f159,f156])).
% 0.19/0.42  fof(f156,plain,(
% 0.19/0.42    ~sP1(sK2) | ~spl6_6),
% 0.19/0.42    inference(resolution,[],[f125,f44])).
% 0.19/0.42  fof(f125,plain,(
% 0.19/0.42    v2_struct_0(sK4(sK2)) | ~spl6_6),
% 0.19/0.42    inference(avatar_component_clause,[],[f123])).
% 0.19/0.42  fof(f123,plain,(
% 0.19/0.42    spl6_6 <=> v2_struct_0(sK4(sK2))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.19/0.42  fof(f159,plain,(
% 0.19/0.42    sP1(sK2) | ~l1_waybel_9(sK2) | ~v2_lattice3(sK2) | ~v1_lattice3(sK2) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2) | spl6_2),
% 0.19/0.42    inference(subsumption_resolution,[],[f158,f39])).
% 0.19/0.42  fof(f39,plain,(
% 0.19/0.42    ~v2_waybel_2(sK2)),
% 0.19/0.42    inference(cnf_transformation,[],[f18])).
% 0.19/0.42  fof(f158,plain,(
% 0.19/0.42    v2_waybel_2(sK2) | sP1(sK2) | ~l1_waybel_9(sK2) | ~v2_lattice3(sK2) | ~v1_lattice3(sK2) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2) | spl6_2),
% 0.19/0.42    inference(resolution,[],[f157,f50])).
% 0.19/0.42  fof(f50,plain,(
% 0.19/0.42    ( ! [X0] : (m1_subset_1(sK5(X0),u1_struct_0(X0)) | v2_waybel_2(X0) | sP1(X0) | ~l1_waybel_9(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f28])).
% 0.19/0.42  fof(f28,plain,(
% 0.19/0.42    ! [X0] : (v2_waybel_2(X0) | (~v5_pre_topc(k4_waybel_1(X0,sK5(X0)),X0,X0) & m1_subset_1(sK5(X0),u1_struct_0(X0))) | sP1(X0) | ~l1_waybel_9(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f16,f27])).
% 0.19/0.42  fof(f27,plain,(
% 0.19/0.42    ! [X0] : (? [X1] : (~v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) & m1_subset_1(X1,u1_struct_0(X0))) => (~v5_pre_topc(k4_waybel_1(X0,sK5(X0)),X0,X0) & m1_subset_1(sK5(X0),u1_struct_0(X0))))),
% 0.19/0.42    introduced(choice_axiom,[])).
% 0.19/0.42  fof(f16,plain,(
% 0.19/0.42    ! [X0] : (v2_waybel_2(X0) | ? [X1] : (~v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) & m1_subset_1(X1,u1_struct_0(X0))) | sP1(X0) | ~l1_waybel_9(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.42    inference(definition_folding,[],[f12,f15])).
% 0.19/0.42  fof(f12,plain,(
% 0.19/0.42    ! [X0] : (v2_waybel_2(X0) | ? [X1] : (~v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) & m1_subset_1(X1,u1_struct_0(X0))) | ? [X2] : ((~r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2)) | ~r1_waybel_9(X0,X2)) & v10_waybel_0(X2,X0) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~l1_waybel_9(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.42    inference(flattening,[],[f11])).
% 0.19/0.42  fof(f11,plain,(
% 0.19/0.42    ! [X0] : ((v2_waybel_2(X0) | (? [X1] : (~v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) & m1_subset_1(X1,u1_struct_0(X0))) | ? [X2] : (((~r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2)) | ~r1_waybel_9(X0,X2)) & v10_waybel_0(X2,X0)) & (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))))) | (~l1_waybel_9(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.19/0.42    inference(ennf_transformation,[],[f6])).
% 0.19/0.42  fof(f6,plain,(
% 0.19/0.42    ! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ((! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)) & ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (v10_waybel_0(X2,X0) => (r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2)) & r1_waybel_9(X0,X2))))) => v2_waybel_2(X0)))),
% 0.19/0.42    inference(rectify,[],[f1])).
% 0.19/0.42  fof(f1,axiom,(
% 0.19/0.42    ! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ((! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)) & ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (v10_waybel_0(X1,X0) => (r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1)) & r1_waybel_9(X0,X1))))) => v2_waybel_2(X0)))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_waybel_9)).
% 0.19/0.42  fof(f157,plain,(
% 0.19/0.42    ~m1_subset_1(sK5(sK2),u1_struct_0(sK2)) | spl6_2),
% 0.19/0.42    inference(resolution,[],[f77,f38])).
% 0.19/0.42  fof(f38,plain,(
% 0.19/0.42    ( ! [X1] : (v5_pre_topc(k4_waybel_1(sK2,X1),sK2,sK2) | ~m1_subset_1(X1,u1_struct_0(sK2))) )),
% 0.19/0.42    inference(cnf_transformation,[],[f18])).
% 0.19/0.42  fof(f77,plain,(
% 0.19/0.42    ~v5_pre_topc(k4_waybel_1(sK2,sK5(sK2)),sK2,sK2) | spl6_2),
% 0.19/0.42    inference(avatar_component_clause,[],[f75])).
% 0.19/0.42  fof(f75,plain,(
% 0.19/0.42    spl6_2 <=> v5_pre_topc(k4_waybel_1(sK2,sK5(sK2)),sK2,sK2)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.19/0.42  fof(f155,plain,(
% 0.19/0.42    ~spl6_1 | spl6_4 | ~spl6_7),
% 0.19/0.42    inference(avatar_contradiction_clause,[],[f154])).
% 0.19/0.42  fof(f154,plain,(
% 0.19/0.42    $false | (~spl6_1 | spl6_4 | ~spl6_7)),
% 0.19/0.42    inference(subsumption_resolution,[],[f153,f73])).
% 0.19/0.42  fof(f153,plain,(
% 0.19/0.42    ~sP1(sK2) | (~spl6_1 | spl6_4 | ~spl6_7)),
% 0.19/0.42    inference(resolution,[],[f152,f44])).
% 0.19/0.42  fof(f152,plain,(
% 0.19/0.42    v2_struct_0(sK4(sK2)) | (~spl6_1 | spl6_4 | ~spl6_7)),
% 0.19/0.42    inference(subsumption_resolution,[],[f151,f146])).
% 0.19/0.42  fof(f146,plain,(
% 0.19/0.42    l1_waybel_0(sK4(sK2),sK2) | ~spl6_1),
% 0.19/0.42    inference(resolution,[],[f73,f47])).
% 0.19/0.42  fof(f151,plain,(
% 0.19/0.42    v2_struct_0(sK4(sK2)) | ~l1_waybel_0(sK4(sK2),sK2) | (~spl6_1 | spl6_4 | ~spl6_7)),
% 0.19/0.42    inference(subsumption_resolution,[],[f150,f145])).
% 0.19/0.42  fof(f145,plain,(
% 0.19/0.42    v7_waybel_0(sK4(sK2)) | ~spl6_1),
% 0.19/0.42    inference(resolution,[],[f73,f46])).
% 0.19/0.42  fof(f150,plain,(
% 0.19/0.42    v2_struct_0(sK4(sK2)) | ~v7_waybel_0(sK4(sK2)) | ~l1_waybel_0(sK4(sK2),sK2) | (~spl6_1 | spl6_4 | ~spl6_7)),
% 0.19/0.42    inference(subsumption_resolution,[],[f149,f144])).
% 0.19/0.42  fof(f144,plain,(
% 0.19/0.42    v4_orders_2(sK4(sK2)) | ~spl6_1),
% 0.19/0.42    inference(resolution,[],[f73,f45])).
% 0.19/0.42  fof(f149,plain,(
% 0.19/0.42    v2_struct_0(sK4(sK2)) | ~v4_orders_2(sK4(sK2)) | ~v7_waybel_0(sK4(sK2)) | ~l1_waybel_0(sK4(sK2),sK2) | (~spl6_1 | spl6_4 | ~spl6_7)),
% 0.19/0.42    inference(subsumption_resolution,[],[f136,f147])).
% 0.19/0.42  fof(f147,plain,(
% 0.19/0.42    v10_waybel_0(sK4(sK2),sK2) | ~spl6_1),
% 0.19/0.42    inference(resolution,[],[f73,f48])).
% 0.19/0.42  fof(f136,plain,(
% 0.19/0.42    ~v10_waybel_0(sK4(sK2),sK2) | v2_struct_0(sK4(sK2)) | ~v4_orders_2(sK4(sK2)) | ~v7_waybel_0(sK4(sK2)) | ~l1_waybel_0(sK4(sK2),sK2) | (spl6_4 | ~spl6_7)),
% 0.19/0.42    inference(resolution,[],[f129,f102])).
% 0.19/0.42  fof(f102,plain,(
% 0.19/0.42    ~r1_waybel_9(sK2,sK4(sK2)) | spl6_4),
% 0.19/0.42    inference(avatar_component_clause,[],[f100])).
% 0.19/0.42  fof(f129,plain,(
% 0.19/0.42    ( ! [X0] : (r1_waybel_9(sK2,X0) | ~v10_waybel_0(X0,sK2) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK2)) ) | ~spl6_7),
% 0.19/0.42    inference(avatar_component_clause,[],[f128])).
% 0.19/0.42  fof(f128,plain,(
% 0.19/0.42    spl6_7 <=> ! [X0] : (~v10_waybel_0(X0,sK2) | r1_waybel_9(sK2,X0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK2))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.19/0.42  fof(f143,plain,(
% 0.19/0.42    spl6_2 | spl6_4 | ~spl6_7),
% 0.19/0.42    inference(avatar_contradiction_clause,[],[f142])).
% 0.19/0.42  fof(f142,plain,(
% 0.19/0.42    $false | (spl6_2 | spl6_4 | ~spl6_7)),
% 0.19/0.42    inference(subsumption_resolution,[],[f141,f89])).
% 0.19/0.42  fof(f89,plain,(
% 0.19/0.42    sP1(sK2) | spl6_2),
% 0.19/0.42    inference(subsumption_resolution,[],[f88,f29])).
% 0.19/0.42  fof(f88,plain,(
% 0.19/0.42    sP1(sK2) | ~v2_pre_topc(sK2) | spl6_2),
% 0.19/0.42    inference(subsumption_resolution,[],[f87,f30])).
% 0.19/0.42  fof(f87,plain,(
% 0.19/0.42    sP1(sK2) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2) | spl6_2),
% 0.19/0.42    inference(subsumption_resolution,[],[f86,f31])).
% 0.19/0.42  fof(f86,plain,(
% 0.19/0.42    sP1(sK2) | ~v3_orders_2(sK2) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2) | spl6_2),
% 0.19/0.42    inference(subsumption_resolution,[],[f85,f32])).
% 0.19/0.42  fof(f85,plain,(
% 0.19/0.42    sP1(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2) | spl6_2),
% 0.19/0.42    inference(subsumption_resolution,[],[f84,f33])).
% 0.19/0.42  fof(f84,plain,(
% 0.19/0.42    sP1(sK2) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2) | spl6_2),
% 0.19/0.42    inference(subsumption_resolution,[],[f83,f34])).
% 0.19/0.42  fof(f83,plain,(
% 0.19/0.42    sP1(sK2) | ~v1_lattice3(sK2) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2) | spl6_2),
% 0.19/0.42    inference(subsumption_resolution,[],[f82,f35])).
% 0.19/0.42  fof(f82,plain,(
% 0.19/0.42    sP1(sK2) | ~v2_lattice3(sK2) | ~v1_lattice3(sK2) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2) | spl6_2),
% 0.19/0.42    inference(subsumption_resolution,[],[f81,f37])).
% 0.19/0.42  fof(f81,plain,(
% 0.19/0.42    sP1(sK2) | ~l1_waybel_9(sK2) | ~v2_lattice3(sK2) | ~v1_lattice3(sK2) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2) | spl6_2),
% 0.19/0.42    inference(subsumption_resolution,[],[f80,f39])).
% 0.19/0.42  fof(f80,plain,(
% 0.19/0.42    v2_waybel_2(sK2) | sP1(sK2) | ~l1_waybel_9(sK2) | ~v2_lattice3(sK2) | ~v1_lattice3(sK2) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2) | spl6_2),
% 0.19/0.42    inference(resolution,[],[f79,f50])).
% 0.19/0.42  fof(f79,plain,(
% 0.19/0.42    ~m1_subset_1(sK5(sK2),u1_struct_0(sK2)) | spl6_2),
% 0.19/0.42    inference(resolution,[],[f38,f77])).
% 0.19/0.42  fof(f141,plain,(
% 0.19/0.42    ~sP1(sK2) | (spl6_2 | spl6_4 | ~spl6_7)),
% 0.19/0.42    inference(resolution,[],[f140,f44])).
% 0.19/0.42  fof(f140,plain,(
% 0.19/0.42    v2_struct_0(sK4(sK2)) | (spl6_2 | spl6_4 | ~spl6_7)),
% 0.19/0.42    inference(subsumption_resolution,[],[f139,f92])).
% 0.19/0.42  fof(f92,plain,(
% 0.19/0.42    l1_waybel_0(sK4(sK2),sK2) | spl6_2),
% 0.19/0.42    inference(resolution,[],[f89,f47])).
% 0.19/0.42  fof(f139,plain,(
% 0.19/0.42    v2_struct_0(sK4(sK2)) | ~l1_waybel_0(sK4(sK2),sK2) | (spl6_2 | spl6_4 | ~spl6_7)),
% 0.19/0.42    inference(subsumption_resolution,[],[f138,f91])).
% 0.19/0.42  fof(f91,plain,(
% 0.19/0.42    v7_waybel_0(sK4(sK2)) | spl6_2),
% 0.19/0.42    inference(resolution,[],[f89,f46])).
% 0.19/0.42  fof(f138,plain,(
% 0.19/0.42    v2_struct_0(sK4(sK2)) | ~v7_waybel_0(sK4(sK2)) | ~l1_waybel_0(sK4(sK2),sK2) | (spl6_2 | spl6_4 | ~spl6_7)),
% 0.19/0.42    inference(subsumption_resolution,[],[f137,f90])).
% 0.19/0.42  fof(f90,plain,(
% 0.19/0.42    v4_orders_2(sK4(sK2)) | spl6_2),
% 0.19/0.42    inference(resolution,[],[f89,f45])).
% 0.19/0.42  fof(f137,plain,(
% 0.19/0.42    v2_struct_0(sK4(sK2)) | ~v4_orders_2(sK4(sK2)) | ~v7_waybel_0(sK4(sK2)) | ~l1_waybel_0(sK4(sK2),sK2) | (spl6_2 | spl6_4 | ~spl6_7)),
% 0.19/0.42    inference(subsumption_resolution,[],[f136,f93])).
% 0.19/0.42  fof(f93,plain,(
% 0.19/0.42    v10_waybel_0(sK4(sK2),sK2) | spl6_2),
% 0.19/0.42    inference(resolution,[],[f89,f48])).
% 0.19/0.42  fof(f135,plain,(
% 0.19/0.42    ~spl6_5),
% 0.19/0.42    inference(avatar_contradiction_clause,[],[f134])).
% 0.19/0.42  fof(f134,plain,(
% 0.19/0.42    $false | ~spl6_5),
% 0.19/0.42    inference(subsumption_resolution,[],[f133,f121])).
% 0.19/0.42  fof(f121,plain,(
% 0.19/0.42    sP0(sK2) | ~spl6_5),
% 0.19/0.42    inference(avatar_component_clause,[],[f119])).
% 0.19/0.42  fof(f133,plain,(
% 0.19/0.42    ~sP0(sK2) | ~spl6_5),
% 0.19/0.42    inference(resolution,[],[f132,f40])).
% 0.19/0.42  fof(f40,plain,(
% 0.19/0.42    ( ! [X0] : (m1_subset_1(sK3(X0),u1_struct_0(X0)) | ~sP0(X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f21])).
% 0.19/0.42  fof(f21,plain,(
% 0.19/0.42    ! [X0] : ((~v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0) & m1_subset_1(sK3(X0),u1_struct_0(X0))) | ~sP0(X0))),
% 0.19/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f20])).
% 0.19/0.42  fof(f20,plain,(
% 0.19/0.42    ! [X0] : (? [X1] : (~v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) & m1_subset_1(X1,u1_struct_0(X0))) => (~v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 0.19/0.42    introduced(choice_axiom,[])).
% 0.19/0.42  fof(f19,plain,(
% 0.19/0.42    ! [X0] : (? [X1] : (~v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) & m1_subset_1(X1,u1_struct_0(X0))) | ~sP0(X0))),
% 0.19/0.42    inference(nnf_transformation,[],[f13])).
% 0.19/0.42  fof(f132,plain,(
% 0.19/0.42    ~m1_subset_1(sK3(sK2),u1_struct_0(sK2)) | ~spl6_5),
% 0.19/0.42    inference(resolution,[],[f131,f38])).
% 0.19/0.42  fof(f131,plain,(
% 0.19/0.42    ~v5_pre_topc(k4_waybel_1(sK2,sK3(sK2)),sK2,sK2) | ~spl6_5),
% 0.19/0.42    inference(resolution,[],[f121,f41])).
% 0.19/0.42  fof(f41,plain,(
% 0.19/0.42    ( ! [X0] : (~sP0(X0) | ~v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f21])).
% 0.19/0.42  fof(f130,plain,(
% 0.19/0.42    spl6_5 | spl6_7),
% 0.19/0.42    inference(avatar_split_clause,[],[f60,f128,f119])).
% 0.19/0.42  fof(f60,plain,(
% 0.19/0.42    ( ! [X0] : (~v10_waybel_0(X0,sK2) | ~l1_waybel_0(X0,sK2) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | sP0(sK2) | r1_waybel_9(sK2,X0)) )),
% 0.19/0.42    inference(global_subsumption,[],[f37,f59])).
% 0.19/0.42  fof(f59,plain,(
% 0.19/0.42    ( ! [X0] : (~v10_waybel_0(X0,sK2) | ~l1_waybel_0(X0,sK2) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | sP0(sK2) | ~l1_waybel_9(sK2) | r1_waybel_9(sK2,X0)) )),
% 0.19/0.42    inference(subsumption_resolution,[],[f58,f29])).
% 0.19/0.42  fof(f58,plain,(
% 0.19/0.42    ( ! [X0] : (~v10_waybel_0(X0,sK2) | ~l1_waybel_0(X0,sK2) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | sP0(sK2) | ~l1_waybel_9(sK2) | r1_waybel_9(sK2,X0) | ~v2_pre_topc(sK2)) )),
% 0.19/0.42    inference(subsumption_resolution,[],[f57,f30])).
% 0.19/0.42  fof(f57,plain,(
% 0.19/0.42    ( ! [X0] : (~v10_waybel_0(X0,sK2) | ~l1_waybel_0(X0,sK2) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | sP0(sK2) | ~l1_waybel_9(sK2) | r1_waybel_9(sK2,X0) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2)) )),
% 0.19/0.42    inference(subsumption_resolution,[],[f56,f31])).
% 0.19/0.42  fof(f56,plain,(
% 0.19/0.42    ( ! [X0] : (~v10_waybel_0(X0,sK2) | ~l1_waybel_0(X0,sK2) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | sP0(sK2) | ~l1_waybel_9(sK2) | r1_waybel_9(sK2,X0) | ~v3_orders_2(sK2) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2)) )),
% 0.19/0.42    inference(subsumption_resolution,[],[f55,f32])).
% 0.19/0.42  fof(f55,plain,(
% 0.19/0.42    ( ! [X0] : (~v10_waybel_0(X0,sK2) | ~l1_waybel_0(X0,sK2) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | sP0(sK2) | ~l1_waybel_9(sK2) | r1_waybel_9(sK2,X0) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2)) )),
% 0.19/0.42    inference(subsumption_resolution,[],[f54,f33])).
% 0.19/0.42  fof(f54,plain,(
% 0.19/0.42    ( ! [X0] : (~v10_waybel_0(X0,sK2) | ~l1_waybel_0(X0,sK2) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | sP0(sK2) | ~l1_waybel_9(sK2) | r1_waybel_9(sK2,X0) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2)) )),
% 0.19/0.42    inference(subsumption_resolution,[],[f53,f34])).
% 0.19/0.42  fof(f53,plain,(
% 0.19/0.42    ( ! [X0] : (~v10_waybel_0(X0,sK2) | ~l1_waybel_0(X0,sK2) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | sP0(sK2) | ~l1_waybel_9(sK2) | r1_waybel_9(sK2,X0) | ~v1_lattice3(sK2) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2)) )),
% 0.19/0.42    inference(subsumption_resolution,[],[f52,f35])).
% 0.19/0.42  fof(f52,plain,(
% 0.19/0.42    ( ! [X0] : (~v10_waybel_0(X0,sK2) | ~l1_waybel_0(X0,sK2) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | sP0(sK2) | ~l1_waybel_9(sK2) | r1_waybel_9(sK2,X0) | ~v2_lattice3(sK2) | ~v1_lattice3(sK2) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2)) )),
% 0.19/0.42    inference(resolution,[],[f36,f42])).
% 0.19/0.42  fof(f42,plain,(
% 0.19/0.42    ( ! [X0,X1] : (~v1_compts_1(X0) | ~v10_waybel_0(X1,X0) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | sP0(X0) | ~l1_waybel_9(X0) | r1_waybel_9(X0,X1) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f22])).
% 0.19/0.42  fof(f126,plain,(
% 0.19/0.42    spl6_5 | spl6_6 | spl6_2 | spl6_3),
% 0.19/0.42    inference(avatar_split_clause,[],[f117,f96,f75,f123,f119])).
% 0.19/0.42  fof(f96,plain,(
% 0.19/0.42    spl6_3 <=> r2_hidden(k1_waybel_2(sK2,sK4(sK2)),k10_yellow_6(sK2,sK4(sK2)))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.19/0.42  fof(f117,plain,(
% 0.19/0.42    v2_struct_0(sK4(sK2)) | sP0(sK2) | (spl6_2 | spl6_3)),
% 0.19/0.42    inference(subsumption_resolution,[],[f116,f29])).
% 0.19/0.42  fof(f116,plain,(
% 0.19/0.42    v2_struct_0(sK4(sK2)) | sP0(sK2) | ~v2_pre_topc(sK2) | (spl6_2 | spl6_3)),
% 0.19/0.42    inference(subsumption_resolution,[],[f115,f30])).
% 0.19/0.42  fof(f115,plain,(
% 0.19/0.42    v2_struct_0(sK4(sK2)) | sP0(sK2) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2) | (spl6_2 | spl6_3)),
% 0.19/0.42    inference(subsumption_resolution,[],[f114,f31])).
% 0.19/0.42  fof(f114,plain,(
% 0.19/0.42    v2_struct_0(sK4(sK2)) | sP0(sK2) | ~v3_orders_2(sK2) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2) | (spl6_2 | spl6_3)),
% 0.19/0.42    inference(subsumption_resolution,[],[f113,f32])).
% 0.19/0.42  fof(f113,plain,(
% 0.19/0.42    v2_struct_0(sK4(sK2)) | sP0(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2) | (spl6_2 | spl6_3)),
% 0.19/0.42    inference(subsumption_resolution,[],[f112,f33])).
% 0.19/0.42  fof(f112,plain,(
% 0.19/0.42    v2_struct_0(sK4(sK2)) | sP0(sK2) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2) | (spl6_2 | spl6_3)),
% 0.19/0.42    inference(subsumption_resolution,[],[f111,f34])).
% 0.19/0.42  fof(f111,plain,(
% 0.19/0.42    v2_struct_0(sK4(sK2)) | sP0(sK2) | ~v1_lattice3(sK2) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2) | (spl6_2 | spl6_3)),
% 0.19/0.42    inference(subsumption_resolution,[],[f110,f35])).
% 0.19/0.42  fof(f110,plain,(
% 0.19/0.42    v2_struct_0(sK4(sK2)) | sP0(sK2) | ~v2_lattice3(sK2) | ~v1_lattice3(sK2) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2) | (spl6_2 | spl6_3)),
% 0.19/0.42    inference(subsumption_resolution,[],[f109,f36])).
% 0.19/0.42  fof(f109,plain,(
% 0.19/0.42    v2_struct_0(sK4(sK2)) | sP0(sK2) | ~v1_compts_1(sK2) | ~v2_lattice3(sK2) | ~v1_lattice3(sK2) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2) | (spl6_2 | spl6_3)),
% 0.19/0.42    inference(subsumption_resolution,[],[f108,f37])).
% 0.19/0.42  fof(f108,plain,(
% 0.19/0.42    v2_struct_0(sK4(sK2)) | sP0(sK2) | ~l1_waybel_9(sK2) | ~v1_compts_1(sK2) | ~v2_lattice3(sK2) | ~v1_lattice3(sK2) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2) | (spl6_2 | spl6_3)),
% 0.19/0.42    inference(subsumption_resolution,[],[f107,f90])).
% 0.19/0.42  fof(f107,plain,(
% 0.19/0.42    ~v4_orders_2(sK4(sK2)) | v2_struct_0(sK4(sK2)) | sP0(sK2) | ~l1_waybel_9(sK2) | ~v1_compts_1(sK2) | ~v2_lattice3(sK2) | ~v1_lattice3(sK2) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2) | (spl6_2 | spl6_3)),
% 0.19/0.42    inference(subsumption_resolution,[],[f106,f91])).
% 0.19/0.42  fof(f106,plain,(
% 0.19/0.42    ~v7_waybel_0(sK4(sK2)) | ~v4_orders_2(sK4(sK2)) | v2_struct_0(sK4(sK2)) | sP0(sK2) | ~l1_waybel_9(sK2) | ~v1_compts_1(sK2) | ~v2_lattice3(sK2) | ~v1_lattice3(sK2) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2) | (spl6_2 | spl6_3)),
% 0.19/0.42    inference(subsumption_resolution,[],[f105,f92])).
% 0.19/0.42  fof(f105,plain,(
% 0.19/0.42    ~l1_waybel_0(sK4(sK2),sK2) | ~v7_waybel_0(sK4(sK2)) | ~v4_orders_2(sK4(sK2)) | v2_struct_0(sK4(sK2)) | sP0(sK2) | ~l1_waybel_9(sK2) | ~v1_compts_1(sK2) | ~v2_lattice3(sK2) | ~v1_lattice3(sK2) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2) | (spl6_2 | spl6_3)),
% 0.19/0.42    inference(subsumption_resolution,[],[f104,f93])).
% 0.19/0.42  fof(f104,plain,(
% 0.19/0.42    ~v10_waybel_0(sK4(sK2),sK2) | ~l1_waybel_0(sK4(sK2),sK2) | ~v7_waybel_0(sK4(sK2)) | ~v4_orders_2(sK4(sK2)) | v2_struct_0(sK4(sK2)) | sP0(sK2) | ~l1_waybel_9(sK2) | ~v1_compts_1(sK2) | ~v2_lattice3(sK2) | ~v1_lattice3(sK2) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2) | spl6_3),
% 0.19/0.42    inference(resolution,[],[f98,f43])).
% 0.19/0.42  fof(f98,plain,(
% 0.19/0.42    ~r2_hidden(k1_waybel_2(sK2,sK4(sK2)),k10_yellow_6(sK2,sK4(sK2))) | spl6_3),
% 0.19/0.42    inference(avatar_component_clause,[],[f96])).
% 0.19/0.42  fof(f103,plain,(
% 0.19/0.42    ~spl6_3 | ~spl6_4 | spl6_2),
% 0.19/0.42    inference(avatar_split_clause,[],[f94,f75,f100,f96])).
% 0.19/0.43  % (25113)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.19/0.44  fof(f94,plain,(
% 0.19/0.44    ~r1_waybel_9(sK2,sK4(sK2)) | ~r2_hidden(k1_waybel_2(sK2,sK4(sK2)),k10_yellow_6(sK2,sK4(sK2))) | spl6_2),
% 0.19/0.44    inference(resolution,[],[f89,f49])).
% 0.19/0.44  fof(f78,plain,(
% 0.19/0.44    spl6_1 | ~spl6_2),
% 0.19/0.44    inference(avatar_split_clause,[],[f69,f75,f71])).
% 0.19/0.44  fof(f69,plain,(
% 0.19/0.44    ~v5_pre_topc(k4_waybel_1(sK2,sK5(sK2)),sK2,sK2) | sP1(sK2)),
% 0.19/0.44    inference(global_subsumption,[],[f39,f68])).
% 0.19/0.44  fof(f68,plain,(
% 0.19/0.44    ~v5_pre_topc(k4_waybel_1(sK2,sK5(sK2)),sK2,sK2) | sP1(sK2) | v2_waybel_2(sK2)),
% 0.19/0.44    inference(subsumption_resolution,[],[f67,f29])).
% 0.19/0.44  fof(f67,plain,(
% 0.19/0.44    ~v5_pre_topc(k4_waybel_1(sK2,sK5(sK2)),sK2,sK2) | sP1(sK2) | v2_waybel_2(sK2) | ~v2_pre_topc(sK2)),
% 0.19/0.44    inference(subsumption_resolution,[],[f66,f30])).
% 0.19/0.44  fof(f66,plain,(
% 0.19/0.44    ~v5_pre_topc(k4_waybel_1(sK2,sK5(sK2)),sK2,sK2) | sP1(sK2) | v2_waybel_2(sK2) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2)),
% 0.19/0.44    inference(subsumption_resolution,[],[f65,f31])).
% 0.19/0.44  fof(f65,plain,(
% 0.19/0.44    ~v5_pre_topc(k4_waybel_1(sK2,sK5(sK2)),sK2,sK2) | sP1(sK2) | v2_waybel_2(sK2) | ~v3_orders_2(sK2) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2)),
% 0.19/0.44    inference(subsumption_resolution,[],[f64,f32])).
% 0.19/0.44  fof(f64,plain,(
% 0.19/0.44    ~v5_pre_topc(k4_waybel_1(sK2,sK5(sK2)),sK2,sK2) | sP1(sK2) | v2_waybel_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2)),
% 0.19/0.44    inference(subsumption_resolution,[],[f63,f33])).
% 0.19/0.44  fof(f63,plain,(
% 0.19/0.44    ~v5_pre_topc(k4_waybel_1(sK2,sK5(sK2)),sK2,sK2) | sP1(sK2) | v2_waybel_2(sK2) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2)),
% 0.19/0.44    inference(subsumption_resolution,[],[f62,f34])).
% 0.19/0.44  fof(f62,plain,(
% 0.19/0.44    ~v5_pre_topc(k4_waybel_1(sK2,sK5(sK2)),sK2,sK2) | sP1(sK2) | v2_waybel_2(sK2) | ~v1_lattice3(sK2) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2)),
% 0.19/0.44    inference(subsumption_resolution,[],[f61,f35])).
% 0.19/0.44  fof(f61,plain,(
% 0.19/0.44    ~v5_pre_topc(k4_waybel_1(sK2,sK5(sK2)),sK2,sK2) | sP1(sK2) | v2_waybel_2(sK2) | ~v2_lattice3(sK2) | ~v1_lattice3(sK2) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | ~v8_pre_topc(sK2) | ~v2_pre_topc(sK2)),
% 0.19/0.44    inference(resolution,[],[f37,f51])).
% 0.19/0.44  fof(f51,plain,(
% 0.19/0.44    ( ! [X0] : (~l1_waybel_9(X0) | ~v5_pre_topc(k4_waybel_1(X0,sK5(X0)),X0,X0) | sP1(X0) | v2_waybel_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f28])).
% 0.19/0.44  % SZS output end Proof for theBenchmark
% 0.19/0.44  % (25117)------------------------------
% 0.19/0.44  % (25117)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.44  % (25117)Termination reason: Refutation
% 0.19/0.44  
% 0.19/0.44  % (25117)Memory used [KB]: 9978
% 0.19/0.44  % (25117)Time elapsed: 0.049 s
% 0.19/0.44  % (25117)------------------------------
% 0.19/0.44  % (25117)------------------------------
% 0.19/0.44  % (25107)Success in time 0.097 s
%------------------------------------------------------------------------------
