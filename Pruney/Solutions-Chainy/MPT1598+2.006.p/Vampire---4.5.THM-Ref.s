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
% DateTime   : Thu Dec  3 13:16:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 337 expanded)
%              Number of leaves         :   33 ( 133 expanded)
%              Depth                    :   18
%              Number of atoms          :  671 (1256 expanded)
%              Number of equality atoms :   28 (  80 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f294,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f77,f81,f85,f89,f101,f106,f128,f130,f133,f142,f154,f163,f171,f173,f179,f193,f282,f293])).

fof(f293,plain,
    ( spl4_1
    | ~ spl4_7
    | ~ spl4_6
    | ~ spl4_17
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f289,f280,f177,f99,f104,f71])).

fof(f71,plain,
    ( spl4_1
  <=> r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f104,plain,
    ( spl4_7
  <=> m1_subset_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f99,plain,
    ( spl4_6
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f177,plain,
    ( spl4_17
  <=> r1_tarski(sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f280,plain,
    ( spl4_28
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,sK0)
        | r1_tarski(X1,k10_lattice3(k2_yellow_1(sK0),X1,X0))
        | ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X1,X0),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f289,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ spl4_6
    | ~ spl4_17
    | ~ spl4_28 ),
    inference(resolution,[],[f286,f181])).

fof(f181,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
        | r1_tarski(k2_xboole_0(X1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) )
    | ~ spl4_17 ),
    inference(resolution,[],[f178,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f178,plain,
    ( r1_tarski(sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f177])).

fof(f286,plain,
    ( ! [X0] :
        ( r1_tarski(sK1,k10_lattice3(k2_yellow_1(sK0),sK1,X0))
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl4_6
    | ~ spl4_28 ),
    inference(resolution,[],[f285,f100])).

fof(f100,plain,
    ( m1_subset_1(sK1,sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f99])).

fof(f285,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,sK0)
        | r1_tarski(X0,k10_lattice3(k2_yellow_1(sK0),X0,X1))
        | ~ m1_subset_1(X1,sK0) )
    | ~ spl4_28 ),
    inference(duplicate_literal_removal,[],[f283])).

% (31870)Refutation not found, incomplete strategy% (31870)------------------------------
% (31870)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (31870)Termination reason: Refutation not found, incomplete strategy

% (31870)Memory used [KB]: 10618
% (31870)Time elapsed: 0.070 s
% (31870)------------------------------
% (31870)------------------------------
fof(f283,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,k10_lattice3(k2_yellow_1(sK0),X0,X1))
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl4_28 ),
    inference(resolution,[],[f281,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k10_lattice3(k2_yellow_1(X0),X1,X2),X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(global_subsumption,[],[f49,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k10_lattice3(k2_yellow_1(X0),X1,X2),X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ l1_orders_2(k2_yellow_1(X0)) ) ),
    inference(superposition,[],[f65,f50])).

fof(f50,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_lattice3)).

fof(f49,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f281,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X1,X0),sK0)
        | r1_tarski(X1,k10_lattice3(k2_yellow_1(sK0),X1,X0))
        | ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f280])).

fof(f282,plain,
    ( spl4_5
    | spl4_28
    | spl4_5
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f278,f140,f87,f280,f87])).

fof(f87,plain,
    ( spl4_5
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f140,plain,
    ( spl4_12
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,sK0)
        | r1_orders_2(k2_yellow_1(sK0),X1,k10_lattice3(k2_yellow_1(sK0),X1,X0))
        | ~ m1_subset_1(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f278,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X1,X0),sK0)
        | r1_tarski(X1,k10_lattice3(k2_yellow_1(sK0),X1,X0))
        | v1_xboole_0(sK0) )
    | spl4_5
    | ~ spl4_12 ),
    inference(duplicate_literal_removal,[],[f276])).

fof(f276,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X1,X0),sK0)
        | r1_tarski(X1,k10_lattice3(k2_yellow_1(sK0),X1,X0))
        | ~ m1_subset_1(X1,sK0)
        | v1_xboole_0(sK0) )
    | spl4_5
    | ~ spl4_12 ),
    inference(resolution,[],[f275,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,X0)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f92,f50])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | r1_tarski(X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f53,f50])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
                  | ~ r1_tarski(X1,X2) )
                & ( r1_tarski(X1,X2)
                  | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).

fof(f275,plain,
    ( ! [X0,X1] :
        ( r3_orders_2(k2_yellow_1(sK0),X1,k10_lattice3(k2_yellow_1(sK0),X1,X0))
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X1,sK0) )
    | spl4_5
    | ~ spl4_12 ),
    inference(duplicate_literal_removal,[],[f273])).

fof(f273,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,sK0)
        | r3_orders_2(k2_yellow_1(sK0),X1,k10_lattice3(k2_yellow_1(sK0),X1,X0))
        | ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X1,sK0) )
    | spl4_5
    | ~ spl4_12 ),
    inference(resolution,[],[f144,f108])).

fof(f144,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X0,X1),sK0)
        | ~ m1_subset_1(X1,sK0)
        | r3_orders_2(k2_yellow_1(sK0),X0,k10_lattice3(k2_yellow_1(sK0),X0,X1))
        | ~ m1_subset_1(X0,sK0) )
    | spl4_5
    | ~ spl4_12 ),
    inference(duplicate_literal_removal,[],[f143])).

fof(f143,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X1,sK0)
        | r3_orders_2(k2_yellow_1(sK0),X0,k10_lattice3(k2_yellow_1(sK0),X0,X1))
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X0,X1),sK0) )
    | spl4_5
    | ~ spl4_12 ),
    inference(resolution,[],[f141,f114])).

fof(f114,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(k2_yellow_1(sK0),X0,X1)
        | r3_orders_2(k2_yellow_1(sK0),X0,X1)
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X1,sK0) )
    | spl4_5 ),
    inference(resolution,[],[f113,f88])).

fof(f88,plain,
    ( ~ v1_xboole_0(sK0)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f87])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X1)
      | ~ r1_orders_2(k2_yellow_1(X1),X2,X0)
      | r3_orders_2(k2_yellow_1(X1),X2,X0)
      | ~ m1_subset_1(X2,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f112,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ~ v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_orders_2(k2_yellow_1(X0))
        & ~ v2_struct_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_yellow_1)).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(k2_yellow_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
      | r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(global_subsumption,[],[f47,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
      | r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ v3_orders_2(k2_yellow_1(X0))
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(forward_demodulation,[],[f110,f50])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ v3_orders_2(k2_yellow_1(X0))
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(forward_demodulation,[],[f109,f50])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ v3_orders_2(k2_yellow_1(X0))
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(resolution,[],[f64,f49])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r3_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

% (31889)Termination reason: Refutation not found, incomplete strategy
fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f47,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(f141,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(k2_yellow_1(sK0),X1,k10_lattice3(k2_yellow_1(sK0),X1,X0))
        | ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f140])).

fof(f193,plain,
    ( spl4_5
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f192,f137,f87])).

fof(f137,plain,
    ( spl4_11
  <=> v2_struct_0(k2_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f192,plain,
    ( v1_xboole_0(sK0)
    | ~ spl4_11 ),
    inference(resolution,[],[f138,f52])).

fof(f138,plain,
    ( v2_struct_0(k2_yellow_1(sK0))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f137])).

fof(f179,plain,
    ( spl4_5
    | ~ spl4_7
    | spl4_17
    | ~ spl4_15
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f174,f169,f166,f177,f104,f87])).

fof(f166,plain,
    ( spl4_15
  <=> m1_subset_1(k10_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f169,plain,
    ( spl4_16
  <=> r3_orders_2(k2_yellow_1(sK0),sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f174,plain,
    ( ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | r1_tarski(sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK0)
    | ~ spl4_16 ),
    inference(resolution,[],[f170,f93])).

fof(f170,plain,
    ( r3_orders_2(k2_yellow_1(sK0),sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f169])).

fof(f173,plain,
    ( ~ spl4_6
    | ~ spl4_7
    | spl4_15 ),
    inference(avatar_split_clause,[],[f172,f166,f104,f99])).

fof(f172,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(sK1,sK0)
    | spl4_15 ),
    inference(resolution,[],[f167,f108])).

fof(f167,plain,
    ( ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | spl4_15 ),
    inference(avatar_component_clause,[],[f166])).

fof(f171,plain,
    ( ~ spl4_15
    | ~ spl4_7
    | spl4_16
    | spl4_5
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f164,f161,f87,f169,f104,f166])).

fof(f161,plain,
    ( spl4_14
  <=> r1_orders_2(k2_yellow_1(sK0),sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f164,plain,
    ( r3_orders_2(k2_yellow_1(sK0),sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | spl4_5
    | ~ spl4_14 ),
    inference(resolution,[],[f162,f114])).

fof(f162,plain,
    ( r1_orders_2(k2_yellow_1(sK0),sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f161])).

fof(f163,plain,
    ( ~ spl4_6
    | ~ spl4_7
    | spl4_14
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f155,f152,f140,f161,f104,f99])).

fof(f152,plain,
    ( spl4_13
  <=> k10_lattice3(k2_yellow_1(sK0),sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f155,plain,
    ( r1_orders_2(k2_yellow_1(sK0),sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(sK1,sK0)
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(superposition,[],[f141,f153])).

fof(f153,plain,
    ( k10_lattice3(k2_yellow_1(sK0),sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),sK2,sK1)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f152])).

fof(f154,plain,
    ( spl4_13
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f149,f126,f104,f99,f152])).

fof(f126,plain,
    ( spl4_10
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,sK0)
        | k10_lattice3(k2_yellow_1(sK0),X1,X0) = k10_lattice3(k2_yellow_1(sK0),X0,X1)
        | ~ m1_subset_1(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f149,plain,
    ( k10_lattice3(k2_yellow_1(sK0),sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),sK2,sK1)
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_10 ),
    inference(resolution,[],[f145,f105])).

fof(f105,plain,
    ( m1_subset_1(sK2,sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f104])).

fof(f145,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | k10_lattice3(k2_yellow_1(sK0),sK1,X0) = k10_lattice3(k2_yellow_1(sK0),X0,sK1) )
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(resolution,[],[f127,f100])).

fof(f127,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,sK0)
        | k10_lattice3(k2_yellow_1(sK0),X1,X0) = k10_lattice3(k2_yellow_1(sK0),X0,X1)
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f126])).

fof(f142,plain,
    ( spl4_11
    | ~ spl4_8
    | ~ spl4_9
    | spl4_12
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f135,f83,f140,f123,f120,f137])).

fof(f120,plain,
    ( spl4_8
  <=> v5_orders_2(k2_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f123,plain,
    ( spl4_9
  <=> l1_orders_2(k2_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f83,plain,
    ( spl4_4
  <=> v1_lattice3(k2_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f135,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(X0,sK0)
        | ~ l1_orders_2(k2_yellow_1(sK0))
        | r1_orders_2(k2_yellow_1(sK0),X1,k10_lattice3(k2_yellow_1(sK0),X1,X0))
        | ~ v5_orders_2(k2_yellow_1(sK0))
        | v2_struct_0(k2_yellow_1(sK0)) )
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f134,f50])).

fof(f134,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | ~ l1_orders_2(k2_yellow_1(sK0))
        | r1_orders_2(k2_yellow_1(sK0),X1,k10_lattice3(k2_yellow_1(sK0),X1,X0))
        | ~ v5_orders_2(k2_yellow_1(sK0))
        | v2_struct_0(k2_yellow_1(sK0)) )
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f131,f50])).

fof(f131,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | ~ l1_orders_2(k2_yellow_1(sK0))
        | r1_orders_2(k2_yellow_1(sK0),X1,k10_lattice3(k2_yellow_1(sK0),X1,X0))
        | ~ v5_orders_2(k2_yellow_1(sK0))
        | v2_struct_0(k2_yellow_1(sK0)) )
    | ~ spl4_4 ),
    inference(resolution,[],[f94,f84])).

fof(f84,plain,
    ( v1_lattice3(k2_yellow_1(sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_lattice3(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f69,f65])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | k10_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k10_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,X3,sK3(X0,X1,X2,X3))
                        & r1_orders_2(X0,X2,sK3(X0,X1,X2,X3))
                        & r1_orders_2(X0,X1,sK3(X0,X1,X2,X3))
                        & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).

% (31889)Memory used [KB]: 10618
fof(f39,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r1_orders_2(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X3,sK3(X0,X1,X2,X3))
        & r1_orders_2(X0,X2,sK3(X0,X1,X2,X3))
        & r1_orders_2(X0,X1,sK3(X0,X1,X2,X3))
        & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

% (31872)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% (31889)Time elapsed: 0.055 s
fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k10_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f37])).

% (31889)------------------------------
% (31889)------------------------------
fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k10_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X3,X4)
                            | ~ r1_orders_2(X0,X2,X4)
                            | ~ r1_orders_2(X0,X1,X4)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k10_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X3,X4)
                            | ~ r1_orders_2(X0,X2,X4)
                            | ~ r1_orders_2(X0,X1,X4)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k10_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k10_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k10_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X2,X4)
                              & r1_orders_2(X0,X1,X4) )
                           => r1_orders_2(X0,X3,X4) ) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l26_lattice3)).

fof(f133,plain,(
    spl4_9 ),
    inference(avatar_contradiction_clause,[],[f132])).

fof(f132,plain,
    ( $false
    | spl4_9 ),
    inference(resolution,[],[f124,f49])).

fof(f124,plain,
    ( ~ l1_orders_2(k2_yellow_1(sK0))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f123])).

fof(f130,plain,(
    spl4_8 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | spl4_8 ),
    inference(resolution,[],[f121,f48])).

fof(f48,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f121,plain,
    ( ~ v5_orders_2(k2_yellow_1(sK0))
    | spl4_8 ),
    inference(avatar_component_clause,[],[f120])).

fof(f128,plain,
    ( ~ spl4_8
    | ~ spl4_9
    | spl4_10
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f118,f83,f126,f123,f120])).

fof(f118,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(X0,sK0)
        | ~ l1_orders_2(k2_yellow_1(sK0))
        | k10_lattice3(k2_yellow_1(sK0),X1,X0) = k10_lattice3(k2_yellow_1(sK0),X0,X1)
        | ~ v5_orders_2(k2_yellow_1(sK0)) )
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f117,f50])).

fof(f117,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | ~ l1_orders_2(k2_yellow_1(sK0))
        | k10_lattice3(k2_yellow_1(sK0),X1,X0) = k10_lattice3(k2_yellow_1(sK0),X0,X1)
        | ~ v5_orders_2(k2_yellow_1(sK0)) )
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f116,f50])).

fof(f116,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | ~ l1_orders_2(k2_yellow_1(sK0))
        | k10_lattice3(k2_yellow_1(sK0),X1,X0) = k10_lattice3(k2_yellow_1(sK0),X0,X1)
        | ~ v5_orders_2(k2_yellow_1(sK0)) )
    | ~ spl4_4 ),
    inference(resolution,[],[f62,f84])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_lattice3(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_lattice3)).

fof(f106,plain,
    ( spl4_7
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f102,f75,f104])).

fof(f75,plain,
    ( spl4_2
  <=> m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f102,plain,
    ( m1_subset_1(sK2,sK0)
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f76,f50])).

fof(f76,plain,
    ( m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f101,plain,
    ( spl4_6
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f97,f79,f99])).

fof(f79,plain,
    ( spl4_3
  <=> m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f97,plain,
    ( m1_subset_1(sK1,sK0)
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f80,f50])).

fof(f80,plain,
    ( m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f89,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f42,f87])).

fof(f42,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ~ r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    & v1_lattice3(k2_yellow_1(sK0))
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f33,f32,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))
                & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
            & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
        & v1_lattice3(k2_yellow_1(X0))
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(sK0),X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) )
      & v1_lattice3(k2_yellow_1(sK0))
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(sK0),X1,X2))
            & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
        & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k2_xboole_0(sK1,X2),k10_lattice3(k2_yellow_1(sK0),sK1,X2))
          & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k2_xboole_0(sK1,X2),k10_lattice3(k2_yellow_1(sK0),sK1,X2))
        & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
   => ( ~ r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
      & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v1_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v1_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( v1_lattice3(k2_yellow_1(X0))
         => ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
                 => r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_lattice3(k2_yellow_1(X0))
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
               => r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_1)).

fof(f85,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f43,f83])).

fof(f43,plain,(
    v1_lattice3(k2_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f34])).

fof(f81,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f44,f79])).

fof(f44,plain,(
    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f77,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f45,f75])).

fof(f45,plain,(
    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f73,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f46,f71])).

fof(f46,plain,(
    ~ r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:13:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (31884)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.48  % (31875)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (31870)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (31884)Refutation not found, incomplete strategy% (31884)------------------------------
% 0.21/0.48  % (31884)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (31884)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (31884)Memory used [KB]: 6140
% 0.21/0.48  % (31884)Time elapsed: 0.010 s
% 0.21/0.48  % (31884)------------------------------
% 0.21/0.48  % (31884)------------------------------
% 0.21/0.48  % (31889)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (31889)Refutation not found, incomplete strategy% (31889)------------------------------
% 0.21/0.48  % (31889)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (31877)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.48  % (31875)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f294,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f73,f77,f81,f85,f89,f101,f106,f128,f130,f133,f142,f154,f163,f171,f173,f179,f193,f282,f293])).
% 0.21/0.48  fof(f293,plain,(
% 0.21/0.48    spl4_1 | ~spl4_7 | ~spl4_6 | ~spl4_17 | ~spl4_28),
% 0.21/0.48    inference(avatar_split_clause,[],[f289,f280,f177,f99,f104,f71])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    spl4_1 <=> r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    spl4_7 <=> m1_subset_1(sK2,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    spl4_6 <=> m1_subset_1(sK1,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.48  fof(f177,plain,(
% 0.21/0.48    spl4_17 <=> r1_tarski(sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.21/0.48  fof(f280,plain,(
% 0.21/0.48    spl4_28 <=> ! [X1,X0] : (~m1_subset_1(X0,sK0) | r1_tarski(X1,k10_lattice3(k2_yellow_1(sK0),X1,X0)) | ~m1_subset_1(X1,sK0) | ~m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X1,X0),sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.21/0.48  fof(f289,plain,(
% 0.21/0.48    ~m1_subset_1(sK2,sK0) | r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) | (~spl4_6 | ~spl4_17 | ~spl4_28)),
% 0.21/0.48    inference(resolution,[],[f286,f181])).
% 0.21/0.48  fof(f181,plain,(
% 0.21/0.48    ( ! [X1] : (~r1_tarski(X1,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) | r1_tarski(k2_xboole_0(X1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2))) ) | ~spl4_17),
% 0.21/0.48    inference(resolution,[],[f178,f66])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_tarski(X2,X1) | r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.21/0.48  fof(f178,plain,(
% 0.21/0.48    r1_tarski(sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~spl4_17),
% 0.21/0.48    inference(avatar_component_clause,[],[f177])).
% 0.21/0.48  fof(f286,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(sK1,k10_lattice3(k2_yellow_1(sK0),sK1,X0)) | ~m1_subset_1(X0,sK0)) ) | (~spl4_6 | ~spl4_28)),
% 0.21/0.48    inference(resolution,[],[f285,f100])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    m1_subset_1(sK1,sK0) | ~spl4_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f99])).
% 0.21/0.48  fof(f285,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,sK0) | r1_tarski(X0,k10_lattice3(k2_yellow_1(sK0),X0,X1)) | ~m1_subset_1(X1,sK0)) ) | ~spl4_28),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f283])).
% 0.21/0.48  % (31870)Refutation not found, incomplete strategy% (31870)------------------------------
% 0.21/0.48  % (31870)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (31870)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (31870)Memory used [KB]: 10618
% 0.21/0.48  % (31870)Time elapsed: 0.070 s
% 0.21/0.48  % (31870)------------------------------
% 0.21/0.48  % (31870)------------------------------
% 0.21/0.48  fof(f283,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(X0,k10_lattice3(k2_yellow_1(sK0),X0,X1)) | ~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,sK0) | ~m1_subset_1(X1,sK0) | ~m1_subset_1(X0,sK0)) ) | ~spl4_28),
% 0.21/0.48    inference(resolution,[],[f281,f108])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (m1_subset_1(k10_lattice3(k2_yellow_1(X0),X1,X2),X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0)) )),
% 0.21/0.48    inference(global_subsumption,[],[f49,f107])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (m1_subset_1(k10_lattice3(k2_yellow_1(X0),X1,X2),X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~l1_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.48    inference(superposition,[],[f65,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.21/0.48    inference(flattening,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0)) => m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_lattice3)).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 0.21/0.48    inference(pure_predicate_removal,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 0.21/0.48  fof(f281,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X1,X0),sK0) | r1_tarski(X1,k10_lattice3(k2_yellow_1(sK0),X1,X0)) | ~m1_subset_1(X1,sK0) | ~m1_subset_1(X0,sK0)) ) | ~spl4_28),
% 0.21/0.48    inference(avatar_component_clause,[],[f280])).
% 0.21/0.48  fof(f282,plain,(
% 0.21/0.48    spl4_5 | spl4_28 | spl4_5 | ~spl4_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f278,f140,f87,f280,f87])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    spl4_5 <=> v1_xboole_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.48  fof(f140,plain,(
% 0.21/0.48    spl4_12 <=> ! [X1,X0] : (~m1_subset_1(X1,sK0) | r1_orders_2(k2_yellow_1(sK0),X1,k10_lattice3(k2_yellow_1(sK0),X1,X0)) | ~m1_subset_1(X0,sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.48  fof(f278,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,sK0) | ~m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X1,X0),sK0) | r1_tarski(X1,k10_lattice3(k2_yellow_1(sK0),X1,X0)) | v1_xboole_0(sK0)) ) | (spl4_5 | ~spl4_12)),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f276])).
% 0.21/0.48  fof(f276,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,sK0) | ~m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X1,X0),sK0) | r1_tarski(X1,k10_lattice3(k2_yellow_1(sK0),X1,X0)) | ~m1_subset_1(X1,sK0) | v1_xboole_0(sK0)) ) | (spl4_5 | ~spl4_12)),
% 0.21/0.48    inference(resolution,[],[f275,f93])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,X0) | r1_tarski(X1,X2) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f92,f50])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f53,f50])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (((r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).
% 0.21/0.48  fof(f275,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r3_orders_2(k2_yellow_1(sK0),X1,k10_lattice3(k2_yellow_1(sK0),X1,X0)) | ~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,sK0)) ) | (spl4_5 | ~spl4_12)),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f273])).
% 0.21/0.48  fof(f273,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,sK0) | r3_orders_2(k2_yellow_1(sK0),X1,k10_lattice3(k2_yellow_1(sK0),X1,X0)) | ~m1_subset_1(X1,sK0) | ~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,sK0)) ) | (spl4_5 | ~spl4_12)),
% 0.21/0.48    inference(resolution,[],[f144,f108])).
% 0.21/0.48  fof(f144,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X0,X1),sK0) | ~m1_subset_1(X1,sK0) | r3_orders_2(k2_yellow_1(sK0),X0,k10_lattice3(k2_yellow_1(sK0),X0,X1)) | ~m1_subset_1(X0,sK0)) ) | (spl4_5 | ~spl4_12)),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f143])).
% 0.21/0.48  fof(f143,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,sK0) | r3_orders_2(k2_yellow_1(sK0),X0,k10_lattice3(k2_yellow_1(sK0),X0,X1)) | ~m1_subset_1(X0,sK0) | ~m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X0,X1),sK0)) ) | (spl4_5 | ~spl4_12)),
% 0.21/0.48    inference(resolution,[],[f141,f114])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_orders_2(k2_yellow_1(sK0),X0,X1) | r3_orders_2(k2_yellow_1(sK0),X0,X1) | ~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,sK0)) ) | spl4_5),
% 0.21/0.48    inference(resolution,[],[f113,f88])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    ~v1_xboole_0(sK0) | spl4_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f87])).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v1_xboole_0(X1) | ~r1_orders_2(k2_yellow_1(X1),X2,X0) | r3_orders_2(k2_yellow_1(X1),X2,X0) | ~m1_subset_1(X2,X1) | ~m1_subset_1(X0,X1)) )),
% 0.21/0.48    inference(resolution,[],[f112,f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : (~v1_xboole_0(X0) => ~v2_struct_0(k2_yellow_1(X0)))),
% 0.21/0.48    inference(pure_predicate_removal,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0] : (~v1_xboole_0(X0) => (v1_orders_2(k2_yellow_1(X0)) & ~v2_struct_0(k2_yellow_1(X0))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_yellow_1)).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v2_struct_0(k2_yellow_1(X0)) | ~m1_subset_1(X2,X0) | ~r1_orders_2(k2_yellow_1(X0),X1,X2) | r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,X0)) )),
% 0.21/0.48    inference(global_subsumption,[],[f47,f111])).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | ~m1_subset_1(X2,X0) | ~r1_orders_2(k2_yellow_1(X0),X1,X2) | r3_orders_2(k2_yellow_1(X0),X1,X2) | ~v3_orders_2(k2_yellow_1(X0)) | v2_struct_0(k2_yellow_1(X0))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f110,f50])).
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | ~r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | r3_orders_2(k2_yellow_1(X0),X1,X2) | ~v3_orders_2(k2_yellow_1(X0)) | v2_struct_0(k2_yellow_1(X0))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f109,f50])).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | r3_orders_2(k2_yellow_1(X0),X1,X2) | ~v3_orders_2(k2_yellow_1(X0)) | v2_struct_0(k2_yellow_1(X0))) )),
% 0.21/0.48    inference(resolution,[],[f64,f49])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r3_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f25])).
% 0.21/0.49  % (31889)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)))),
% 0.21/0.49    inference(pure_predicate_removal,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.21/0.49    inference(pure_predicate_removal,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).
% 0.21/0.49  fof(f141,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_orders_2(k2_yellow_1(sK0),X1,k10_lattice3(k2_yellow_1(sK0),X1,X0)) | ~m1_subset_1(X1,sK0) | ~m1_subset_1(X0,sK0)) ) | ~spl4_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f140])).
% 0.21/0.49  fof(f193,plain,(
% 0.21/0.49    spl4_5 | ~spl4_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f192,f137,f87])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    spl4_11 <=> v2_struct_0(k2_yellow_1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.49  fof(f192,plain,(
% 0.21/0.49    v1_xboole_0(sK0) | ~spl4_11),
% 0.21/0.49    inference(resolution,[],[f138,f52])).
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    v2_struct_0(k2_yellow_1(sK0)) | ~spl4_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f137])).
% 0.21/0.49  fof(f179,plain,(
% 0.21/0.49    spl4_5 | ~spl4_7 | spl4_17 | ~spl4_15 | ~spl4_16),
% 0.21/0.49    inference(avatar_split_clause,[],[f174,f169,f166,f177,f104,f87])).
% 0.21/0.49  fof(f166,plain,(
% 0.21/0.49    spl4_15 <=> m1_subset_1(k10_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.49  fof(f169,plain,(
% 0.21/0.49    spl4_16 <=> r3_orders_2(k2_yellow_1(sK0),sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.49  fof(f174,plain,(
% 0.21/0.49    ~m1_subset_1(k10_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | r1_tarski(sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~m1_subset_1(sK2,sK0) | v1_xboole_0(sK0) | ~spl4_16),
% 0.21/0.49    inference(resolution,[],[f170,f93])).
% 0.21/0.49  fof(f170,plain,(
% 0.21/0.49    r3_orders_2(k2_yellow_1(sK0),sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~spl4_16),
% 0.21/0.49    inference(avatar_component_clause,[],[f169])).
% 0.21/0.49  fof(f173,plain,(
% 0.21/0.49    ~spl4_6 | ~spl4_7 | spl4_15),
% 0.21/0.49    inference(avatar_split_clause,[],[f172,f166,f104,f99])).
% 0.21/0.49  fof(f172,plain,(
% 0.21/0.49    ~m1_subset_1(sK2,sK0) | ~m1_subset_1(sK1,sK0) | spl4_15),
% 0.21/0.49    inference(resolution,[],[f167,f108])).
% 0.21/0.49  fof(f167,plain,(
% 0.21/0.49    ~m1_subset_1(k10_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | spl4_15),
% 0.21/0.49    inference(avatar_component_clause,[],[f166])).
% 0.21/0.49  fof(f171,plain,(
% 0.21/0.49    ~spl4_15 | ~spl4_7 | spl4_16 | spl4_5 | ~spl4_14),
% 0.21/0.49    inference(avatar_split_clause,[],[f164,f161,f87,f169,f104,f166])).
% 0.21/0.49  fof(f161,plain,(
% 0.21/0.49    spl4_14 <=> r1_orders_2(k2_yellow_1(sK0),sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.49  fof(f164,plain,(
% 0.21/0.49    r3_orders_2(k2_yellow_1(sK0),sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~m1_subset_1(sK2,sK0) | ~m1_subset_1(k10_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | (spl4_5 | ~spl4_14)),
% 0.21/0.49    inference(resolution,[],[f162,f114])).
% 0.21/0.49  fof(f162,plain,(
% 0.21/0.49    r1_orders_2(k2_yellow_1(sK0),sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~spl4_14),
% 0.21/0.49    inference(avatar_component_clause,[],[f161])).
% 0.21/0.49  fof(f163,plain,(
% 0.21/0.49    ~spl4_6 | ~spl4_7 | spl4_14 | ~spl4_12 | ~spl4_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f155,f152,f140,f161,f104,f99])).
% 0.21/0.49  fof(f152,plain,(
% 0.21/0.49    spl4_13 <=> k10_lattice3(k2_yellow_1(sK0),sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),sK2,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.49  fof(f155,plain,(
% 0.21/0.49    r1_orders_2(k2_yellow_1(sK0),sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~m1_subset_1(sK2,sK0) | ~m1_subset_1(sK1,sK0) | (~spl4_12 | ~spl4_13)),
% 0.21/0.49    inference(superposition,[],[f141,f153])).
% 0.21/0.49  fof(f153,plain,(
% 0.21/0.49    k10_lattice3(k2_yellow_1(sK0),sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),sK2,sK1) | ~spl4_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f152])).
% 0.21/0.49  fof(f154,plain,(
% 0.21/0.49    spl4_13 | ~spl4_6 | ~spl4_7 | ~spl4_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f149,f126,f104,f99,f152])).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    spl4_10 <=> ! [X1,X0] : (~m1_subset_1(X1,sK0) | k10_lattice3(k2_yellow_1(sK0),X1,X0) = k10_lattice3(k2_yellow_1(sK0),X0,X1) | ~m1_subset_1(X0,sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.49  fof(f149,plain,(
% 0.21/0.49    k10_lattice3(k2_yellow_1(sK0),sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),sK2,sK1) | (~spl4_6 | ~spl4_7 | ~spl4_10)),
% 0.21/0.49    inference(resolution,[],[f145,f105])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    m1_subset_1(sK2,sK0) | ~spl4_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f104])).
% 0.21/0.49  fof(f145,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,sK0) | k10_lattice3(k2_yellow_1(sK0),sK1,X0) = k10_lattice3(k2_yellow_1(sK0),X0,sK1)) ) | (~spl4_6 | ~spl4_10)),
% 0.21/0.49    inference(resolution,[],[f127,f100])).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,sK0) | k10_lattice3(k2_yellow_1(sK0),X1,X0) = k10_lattice3(k2_yellow_1(sK0),X0,X1) | ~m1_subset_1(X0,sK0)) ) | ~spl4_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f126])).
% 0.21/0.49  fof(f142,plain,(
% 0.21/0.49    spl4_11 | ~spl4_8 | ~spl4_9 | spl4_12 | ~spl4_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f135,f83,f140,f123,f120,f137])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    spl4_8 <=> v5_orders_2(k2_yellow_1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    spl4_9 <=> l1_orders_2(k2_yellow_1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    spl4_4 <=> v1_lattice3(k2_yellow_1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.49  fof(f135,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,sK0) | ~m1_subset_1(X0,sK0) | ~l1_orders_2(k2_yellow_1(sK0)) | r1_orders_2(k2_yellow_1(sK0),X1,k10_lattice3(k2_yellow_1(sK0),X1,X0)) | ~v5_orders_2(k2_yellow_1(sK0)) | v2_struct_0(k2_yellow_1(sK0))) ) | ~spl4_4),
% 0.21/0.49    inference(forward_demodulation,[],[f134,f50])).
% 0.21/0.49  fof(f134,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | r1_orders_2(k2_yellow_1(sK0),X1,k10_lattice3(k2_yellow_1(sK0),X1,X0)) | ~v5_orders_2(k2_yellow_1(sK0)) | v2_struct_0(k2_yellow_1(sK0))) ) | ~spl4_4),
% 0.21/0.49    inference(forward_demodulation,[],[f131,f50])).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | r1_orders_2(k2_yellow_1(sK0),X1,k10_lattice3(k2_yellow_1(sK0),X1,X0)) | ~v5_orders_2(k2_yellow_1(sK0)) | v2_struct_0(k2_yellow_1(sK0))) ) | ~spl4_4),
% 0.21/0.49    inference(resolution,[],[f94,f84])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    v1_lattice3(k2_yellow_1(sK0)) | ~spl4_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f83])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_lattice3(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f69,f65])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) | ~m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f55])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X1,X3) | k10_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f40])).
% 0.21/0.49  
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,X3,sK3(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK3(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK3(X0,X1,X2,X3)) & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).
% 0.21/0.49  % (31889)Memory used [KB]: 10618
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,X3,sK3(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK3(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK3(X0,X1,X2,X3)) & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  % (31872)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (31889)Time elapsed: 0.055 s
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(rectify,[],[f37])).
% 0.21/0.49  % (31889)------------------------------
% 0.21/0.49  % (31889)------------------------------
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3))) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X3,X4) | (~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l26_lattice3)).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    spl4_9),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f132])).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    $false | spl4_9),
% 0.21/0.49    inference(resolution,[],[f124,f49])).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    ~l1_orders_2(k2_yellow_1(sK0)) | spl4_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f123])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    spl4_8),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f129])).
% 0.21/0.49  fof(f129,plain,(
% 0.21/0.49    $false | spl4_8),
% 0.21/0.49    inference(resolution,[],[f121,f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    ~v5_orders_2(k2_yellow_1(sK0)) | spl4_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f120])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    ~spl4_8 | ~spl4_9 | spl4_10 | ~spl4_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f118,f83,f126,f123,f120])).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,sK0) | ~m1_subset_1(X0,sK0) | ~l1_orders_2(k2_yellow_1(sK0)) | k10_lattice3(k2_yellow_1(sK0),X1,X0) = k10_lattice3(k2_yellow_1(sK0),X0,X1) | ~v5_orders_2(k2_yellow_1(sK0))) ) | ~spl4_4),
% 0.21/0.49    inference(forward_demodulation,[],[f117,f50])).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | k10_lattice3(k2_yellow_1(sK0),X1,X0) = k10_lattice3(k2_yellow_1(sK0),X0,X1) | ~v5_orders_2(k2_yellow_1(sK0))) ) | ~spl4_4),
% 0.21/0.49    inference(forward_demodulation,[],[f116,f50])).
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | k10_lattice3(k2_yellow_1(sK0),X1,X0) = k10_lattice3(k2_yellow_1(sK0),X0,X1) | ~v5_orders_2(k2_yellow_1(sK0))) ) | ~spl4_4),
% 0.21/0.49    inference(resolution,[],[f62,f84])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_lattice3(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1) | ~v5_orders_2(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 0.21/0.49    inference(flattening,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_lattice3)).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    spl4_7 | ~spl4_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f102,f75,f104])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    spl4_2 <=> m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    m1_subset_1(sK2,sK0) | ~spl4_2),
% 0.21/0.49    inference(forward_demodulation,[],[f76,f50])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~spl4_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f75])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    spl4_6 | ~spl4_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f97,f79,f99])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    spl4_3 <=> m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    m1_subset_1(sK1,sK0) | ~spl4_3),
% 0.21/0.49    inference(forward_demodulation,[],[f80,f50])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~spl4_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f79])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    ~spl4_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f42,f87])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ~v1_xboole_0(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ((~r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))) & v1_lattice3(k2_yellow_1(sK0)) & ~v1_xboole_0(sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f33,f32,f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v1_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(sK0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))) & v1_lattice3(k2_yellow_1(sK0)) & ~v1_xboole_0(sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ? [X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(sK0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))) => (? [X2] : (~r1_tarski(k2_xboole_0(sK1,X2),k10_lattice3(k2_yellow_1(sK0),sK1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ? [X2] : (~r1_tarski(k2_xboole_0(sK1,X2),k10_lattice3(k2_yellow_1(sK0),sK1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) => (~r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v1_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0))),
% 0.21/0.49    inference(flattening,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ? [X0] : ((? [X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v1_lattice3(k2_yellow_1(X0))) & ~v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,negated_conjecture,(
% 0.21/0.49    ~! [X0] : (~v1_xboole_0(X0) => (v1_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))))))),
% 0.21/0.49    inference(negated_conjecture,[],[f11])).
% 0.21/0.49  fof(f11,conjecture,(
% 0.21/0.49    ! [X0] : (~v1_xboole_0(X0) => (v1_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_1)).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    spl4_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f43,f83])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    v1_lattice3(k2_yellow_1(sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    spl4_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f44,f79])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    spl4_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f45,f75])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    ~spl4_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f46,f71])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ~r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (31875)------------------------------
% 0.21/0.49  % (31875)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (31875)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (31875)Memory used [KB]: 10874
% 0.21/0.49  % (31875)Time elapsed: 0.012 s
% 0.21/0.49  % (31875)------------------------------
% 0.21/0.49  % (31875)------------------------------
% 0.21/0.49  % (31866)Success in time 0.129 s
%------------------------------------------------------------------------------
