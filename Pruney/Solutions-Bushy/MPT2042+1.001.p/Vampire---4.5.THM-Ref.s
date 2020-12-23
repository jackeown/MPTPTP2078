%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT2042+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:04 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 336 expanded)
%              Number of leaves         :   11 (  89 expanded)
%              Depth                    :   26
%              Number of atoms          :  757 (3605 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   19 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f117,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f84,f116])).

fof(f116,plain,(
    ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f115])).

fof(f115,plain,
    ( $false
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f114,f53])).

fof(f53,plain,(
    ~ sP0(sK2) ),
    inference(subsumption_resolution,[],[f52,f40])).

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

fof(f13,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ sP0(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f52,plain,
    ( ~ m1_subset_1(sK3(sK2),u1_struct_0(sK2))
    | ~ sP0(sK2) ),
    inference(resolution,[],[f38,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f38,plain,(
    ! [X1] :
      ( v5_pre_topc(k4_waybel_1(sK2,X1),sK2,sK2)
      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ) ),
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

fof(f114,plain,
    ( sP0(sK2)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f113,f29])).

fof(f29,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f113,plain,
    ( ~ v2_pre_topc(sK2)
    | sP0(sK2)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f112,f30])).

fof(f30,plain,(
    v8_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f112,plain,
    ( ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | sP0(sK2)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f111,f31])).

fof(f31,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f111,plain,
    ( ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | sP0(sK2)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f110,f32])).

fof(f32,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f110,plain,
    ( ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | sP0(sK2)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f109,f33])).

fof(f33,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f109,plain,
    ( ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | sP0(sK2)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f108,f34])).

fof(f34,plain,(
    v1_lattice3(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f108,plain,
    ( ~ v1_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | sP0(sK2)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f107,f35])).

fof(f35,plain,(
    v2_lattice3(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f107,plain,
    ( ~ v2_lattice3(sK2)
    | ~ v1_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | sP0(sK2)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f106,f36])).

fof(f36,plain,(
    v1_compts_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f106,plain,
    ( ~ v1_compts_1(sK2)
    | ~ v2_lattice3(sK2)
    | ~ v1_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | sP0(sK2)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f105,f37])).

fof(f37,plain,(
    l1_waybel_9(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f105,plain,
    ( ~ l1_waybel_9(sK2)
    | ~ v1_compts_1(sK2)
    | ~ v2_lattice3(sK2)
    | ~ v1_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | sP0(sK2)
    | ~ spl6_2 ),
    inference(resolution,[],[f104,f71])).

fof(f71,plain,
    ( sP1(sK2)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl6_2
  <=> sP1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f104,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | sP0(X0) ) ),
    inference(subsumption_resolution,[],[f103,f44])).

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

fof(f103,plain,(
    ! [X0] :
      ( v2_struct_0(sK4(X0))
      | sP0(X0)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ sP1(X0) ) ),
    inference(subsumption_resolution,[],[f102,f45])).

fof(f45,plain,(
    ! [X0] :
      ( v4_orders_2(sK4(X0))
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f102,plain,(
    ! [X0] :
      ( ~ v4_orders_2(sK4(X0))
      | v2_struct_0(sK4(X0))
      | sP0(X0)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ sP1(X0) ) ),
    inference(subsumption_resolution,[],[f101,f46])).

fof(f46,plain,(
    ! [X0] :
      ( v7_waybel_0(sK4(X0))
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f101,plain,(
    ! [X0] :
      ( ~ v7_waybel_0(sK4(X0))
      | ~ v4_orders_2(sK4(X0))
      | v2_struct_0(sK4(X0))
      | sP0(X0)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ sP1(X0) ) ),
    inference(subsumption_resolution,[],[f100,f47])).

fof(f47,plain,(
    ! [X0] :
      ( l1_waybel_0(sK4(X0),X0)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f100,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(sK4(X0),X0)
      | ~ v7_waybel_0(sK4(X0))
      | ~ v4_orders_2(sK4(X0))
      | v2_struct_0(sK4(X0))
      | sP0(X0)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ sP1(X0) ) ),
    inference(subsumption_resolution,[],[f99,f48])).

fof(f48,plain,(
    ! [X0] :
      ( v10_waybel_0(sK4(X0),X0)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f99,plain,(
    ! [X0] :
      ( ~ v10_waybel_0(sK4(X0),X0)
      | ~ l1_waybel_0(sK4(X0),X0)
      | ~ v7_waybel_0(sK4(X0))
      | ~ v4_orders_2(sK4(X0))
      | v2_struct_0(sK4(X0))
      | sP0(X0)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ sP1(X0) ) ),
    inference(subsumption_resolution,[],[f98,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v10_waybel_0(X1,X0)
      | r1_waybel_9(X0,X1)
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

fof(f98,plain,(
    ! [X0] :
      ( ~ v10_waybel_0(sK4(X0),X0)
      | ~ l1_waybel_0(sK4(X0),X0)
      | ~ v7_waybel_0(sK4(X0))
      | ~ v4_orders_2(sK4(X0))
      | v2_struct_0(sK4(X0))
      | sP0(X0)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ r1_waybel_9(X0,sK4(X0))
      | ~ sP1(X0) ) ),
    inference(resolution,[],[f43,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ r2_hidden(k1_waybel_2(X0,sK4(X0)),k10_yellow_6(X0,sK4(X0)))
      | ~ r1_waybel_9(X0,sK4(X0))
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

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

fof(f84,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_contradiction_clause,[],[f83])).

fof(f83,plain,
    ( $false
    | spl6_1
    | spl6_2 ),
    inference(subsumption_resolution,[],[f82,f29])).

fof(f82,plain,
    ( ~ v2_pre_topc(sK2)
    | spl6_1
    | spl6_2 ),
    inference(subsumption_resolution,[],[f81,f30])).

fof(f81,plain,
    ( ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | spl6_1
    | spl6_2 ),
    inference(subsumption_resolution,[],[f80,f31])).

fof(f80,plain,
    ( ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | spl6_1
    | spl6_2 ),
    inference(subsumption_resolution,[],[f79,f32])).

fof(f79,plain,
    ( ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | spl6_1
    | spl6_2 ),
    inference(subsumption_resolution,[],[f78,f33])).

fof(f78,plain,
    ( ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | spl6_1
    | spl6_2 ),
    inference(subsumption_resolution,[],[f77,f34])).

fof(f77,plain,
    ( ~ v1_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | spl6_1
    | spl6_2 ),
    inference(subsumption_resolution,[],[f76,f35])).

fof(f76,plain,
    ( ~ v2_lattice3(sK2)
    | ~ v1_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | spl6_1
    | spl6_2 ),
    inference(subsumption_resolution,[],[f75,f37])).

fof(f75,plain,
    ( ~ l1_waybel_9(sK2)
    | ~ v2_lattice3(sK2)
    | ~ v1_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | spl6_1
    | spl6_2 ),
    inference(subsumption_resolution,[],[f74,f70])).

fof(f70,plain,
    ( ~ sP1(sK2)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f74,plain,
    ( sP1(sK2)
    | ~ l1_waybel_9(sK2)
    | ~ v2_lattice3(sK2)
    | ~ v1_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f73,f39])).

fof(f39,plain,(
    ~ v2_waybel_2(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f73,plain,
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
    | spl6_1 ),
    inference(resolution,[],[f67,f50])).

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

fof(f67,plain,
    ( ~ m1_subset_1(sK5(sK2),u1_struct_0(sK2))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl6_1
  <=> m1_subset_1(sK5(sK2),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f72,plain,
    ( ~ spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f63,f69,f65])).

fof(f63,plain,
    ( sP1(sK2)
    | ~ m1_subset_1(sK5(sK2),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f62,f29])).

fof(f62,plain,
    ( sP1(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ m1_subset_1(sK5(sK2),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f61,f30])).

fof(f61,plain,
    ( sP1(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ m1_subset_1(sK5(sK2),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f60,f31])).

fof(f60,plain,
    ( sP1(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ m1_subset_1(sK5(sK2),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f59,f32])).

fof(f59,plain,
    ( sP1(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ m1_subset_1(sK5(sK2),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f58,f33])).

fof(f58,plain,
    ( sP1(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ m1_subset_1(sK5(sK2),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f57,f34])).

fof(f57,plain,
    ( sP1(sK2)
    | ~ v1_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ m1_subset_1(sK5(sK2),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f56,f35])).

fof(f56,plain,
    ( sP1(sK2)
    | ~ v2_lattice3(sK2)
    | ~ v1_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ m1_subset_1(sK5(sK2),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f55,f37])).

fof(f55,plain,
    ( sP1(sK2)
    | ~ l1_waybel_9(sK2)
    | ~ v2_lattice3(sK2)
    | ~ v1_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v8_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ m1_subset_1(sK5(sK2),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f54,f39])).

fof(f54,plain,
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
    | ~ m1_subset_1(sK5(sK2),u1_struct_0(sK2)) ),
    inference(resolution,[],[f51,f38])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v5_pre_topc(k4_waybel_1(X0,sK5(X0)),X0,X0)
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

%------------------------------------------------------------------------------
