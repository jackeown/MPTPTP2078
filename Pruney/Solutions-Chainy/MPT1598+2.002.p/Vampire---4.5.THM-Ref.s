%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:27 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 359 expanded)
%              Number of leaves         :   29 ( 125 expanded)
%              Depth                    :   19
%              Number of atoms          :  705 (1476 expanded)
%              Number of equality atoms :   16 (  78 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (16636)Refutation not found, incomplete strategy% (16636)------------------------------
% (16636)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (16636)Termination reason: Refutation not found, incomplete strategy

% (16636)Memory used [KB]: 6140
% (16636)Time elapsed: 0.124 s
% (16636)------------------------------
% (16636)------------------------------
fof(f617,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f73,f77,f81,f85,f97,f102,f124,f139,f378,f388,f394,f396,f416,f610,f616])).

fof(f616,plain,
    ( ~ spl4_7
    | ~ spl4_6
    | ~ spl4_10
    | spl4_42 ),
    inference(avatar_split_clause,[],[f615,f608,f137,f95,f100])).

fof(f100,plain,
    ( spl4_7
  <=> m1_subset_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f95,plain,
    ( spl4_6
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f137,plain,
    ( spl4_10
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,sK0)
        | r1_tarski(X1,k10_lattice3(k2_yellow_1(sK0),X1,X0))
        | ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X1,X0),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f608,plain,
    ( spl4_42
  <=> r1_tarski(sK1,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f615,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | ~ m1_subset_1(sK2,sK0)
    | ~ spl4_10
    | spl4_42 ),
    inference(resolution,[],[f609,f141])).

fof(f141,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,k10_lattice3(k2_yellow_1(sK0),X0,X1))
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X1,sK0) )
    | ~ spl4_10 ),
    inference(duplicate_literal_removal,[],[f140])).

fof(f140,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,k10_lattice3(k2_yellow_1(sK0),X0,X1))
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl4_10 ),
    inference(resolution,[],[f138,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k10_lattice3(k2_yellow_1(X0),X1,X2),X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(global_subsumption,[],[f46,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k10_lattice3(k2_yellow_1(X0),X1,X2),X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ l1_orders_2(k2_yellow_1(X0)) ) ),
    inference(superposition,[],[f61,f47])).

fof(f47,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

% (16654)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_lattice3)).

fof(f46,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f138,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X1,X0),sK0)
        | r1_tarski(X1,k10_lattice3(k2_yellow_1(sK0),X1,X0))
        | ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f137])).

fof(f609,plain,
    ( ~ r1_tarski(sK1,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | spl4_42 ),
    inference(avatar_component_clause,[],[f608])).

fof(f610,plain,
    ( ~ spl4_42
    | spl4_1
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f603,f414,f67,f608])).

fof(f67,plain,
    ( spl4_1
  <=> r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f414,plain,
    ( spl4_15
  <=> r1_tarski(sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f603,plain,
    ( ~ r1_tarski(sK1,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | spl4_1
    | ~ spl4_15 ),
    inference(resolution,[],[f433,f68])).

fof(f68,plain,
    ( ~ r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f433,plain,
    ( ! [X1] :
        ( r1_tarski(k2_xboole_0(X1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
        | ~ r1_tarski(X1,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) )
    | ~ spl4_15 ),
    inference(resolution,[],[f415,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f415,plain,
    ( r1_tarski(sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f414])).

fof(f416,plain,
    ( spl4_15
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f407,f386,f100,f95,f414])).

fof(f386,plain,
    ( spl4_12
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,sK0)
        | r1_tarski(X1,k10_lattice3(k2_yellow_1(sK0),X0,X1))
        | ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X0,X1),sK0)
        | ~ m1_subset_1(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f407,plain,
    ( r1_tarski(sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(resolution,[],[f403,f101])).

fof(f101,plain,
    ( m1_subset_1(sK2,sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f100])).

fof(f403,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | r1_tarski(X0,k10_lattice3(k2_yellow_1(sK0),sK1,X0)) )
    | ~ spl4_6
    | ~ spl4_12 ),
    inference(resolution,[],[f402,f96])).

fof(f96,plain,
    ( m1_subset_1(sK1,sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f95])).

fof(f402,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,sK0)
        | r1_tarski(X0,k10_lattice3(k2_yellow_1(sK0),X1,X0))
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl4_12 ),
    inference(duplicate_literal_removal,[],[f401])).

fof(f401,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,k10_lattice3(k2_yellow_1(sK0),X1,X0))
        | ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X1,sK0) )
    | ~ spl4_12 ),
    inference(resolution,[],[f387,f104])).

fof(f387,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X0,X1),sK0)
        | r1_tarski(X1,k10_lattice3(k2_yellow_1(sK0),X0,X1))
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X1,sK0) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f386])).

fof(f396,plain,(
    spl4_13 ),
    inference(avatar_contradiction_clause,[],[f395])).

fof(f395,plain,
    ( $false
    | spl4_13 ),
    inference(resolution,[],[f392,f46])).

fof(f392,plain,
    ( ~ l1_orders_2(k2_yellow_1(sK0))
    | spl4_13 ),
    inference(avatar_component_clause,[],[f391])).

fof(f391,plain,
    ( spl4_13
  <=> l1_orders_2(k2_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f394,plain,
    ( ~ spl4_13
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f389,f119,f79,f391])).

fof(f79,plain,
    ( spl4_4
  <=> v1_lattice3(k2_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f119,plain,
    ( spl4_8
  <=> v2_struct_0(k2_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f389,plain,
    ( ~ v1_lattice3(k2_yellow_1(sK0))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ spl4_8 ),
    inference(resolution,[],[f120,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).

fof(f120,plain,
    ( v2_struct_0(k2_yellow_1(sK0))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f119])).

fof(f388,plain,
    ( spl4_5
    | spl4_12
    | ~ spl4_4
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f384,f376,f79,f386,f83])).

fof(f83,plain,
    ( spl4_5
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f376,plain,
    ( spl4_11
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,sK0)
        | r1_orders_2(k2_yellow_1(sK0),X0,k10_lattice3(k2_yellow_1(sK0),X1,X0))
        | ~ m1_subset_1(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f384,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X0,X1),sK0)
        | r1_tarski(X1,k10_lattice3(k2_yellow_1(sK0),X0,X1))
        | v1_xboole_0(sK0) )
    | ~ spl4_4
    | ~ spl4_11 ),
    inference(duplicate_literal_removal,[],[f383])).

fof(f383,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X0,X1),sK0)
        | r1_tarski(X1,k10_lattice3(k2_yellow_1(sK0),X0,X1))
        | ~ m1_subset_1(X1,sK0)
        | v1_xboole_0(sK0) )
    | ~ spl4_4
    | ~ spl4_11 ),
    inference(resolution,[],[f382,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,X0)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f88,f47])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | r1_tarski(X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f49,f47])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).

fof(f382,plain,
    ( ! [X0,X1] :
        ( r3_orders_2(k2_yellow_1(sK0),X1,k10_lattice3(k2_yellow_1(sK0),X0,X1))
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X1,sK0) )
    | ~ spl4_4
    | ~ spl4_11 ),
    inference(duplicate_literal_removal,[],[f381])).

fof(f381,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,sK0)
        | r3_orders_2(k2_yellow_1(sK0),X1,k10_lattice3(k2_yellow_1(sK0),X0,X1))
        | ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl4_4
    | ~ spl4_11 ),
    inference(resolution,[],[f380,f104])).

fof(f380,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X1,X0),sK0)
        | ~ m1_subset_1(X1,sK0)
        | r3_orders_2(k2_yellow_1(sK0),X0,k10_lattice3(k2_yellow_1(sK0),X1,X0))
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl4_4
    | ~ spl4_11 ),
    inference(duplicate_literal_removal,[],[f379])).

fof(f379,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X1,sK0)
        | r3_orders_2(k2_yellow_1(sK0),X0,k10_lattice3(k2_yellow_1(sK0),X1,X0))
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X1,X0),sK0) )
    | ~ spl4_4
    | ~ spl4_11 ),
    inference(resolution,[],[f377,f111])).

fof(f111,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(k2_yellow_1(sK0),X0,X1)
        | r3_orders_2(k2_yellow_1(sK0),X0,X1)
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X1,sK0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f110,f80])).

fof(f80,plain,
    ( v1_lattice3(k2_yellow_1(sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_lattice3(k2_yellow_1(X1))
      | ~ r1_orders_2(k2_yellow_1(X1),X2,X0)
      | r3_orders_2(k2_yellow_1(X1),X2,X0)
      | ~ m1_subset_1(X2,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(global_subsumption,[],[f46,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | ~ r1_orders_2(k2_yellow_1(X1),X2,X0)
      | r3_orders_2(k2_yellow_1(X1),X2,X0)
      | ~ m1_subset_1(X2,X1)
      | ~ v1_lattice3(k2_yellow_1(X1))
      | ~ l1_orders_2(k2_yellow_1(X1)) ) ),
    inference(resolution,[],[f108,f51])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(k2_yellow_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
      | r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(global_subsumption,[],[f44,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
      | r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ v3_orders_2(k2_yellow_1(X0))
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(forward_demodulation,[],[f106,f47])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ v3_orders_2(k2_yellow_1(X0))
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(forward_demodulation,[],[f105,f47])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ v3_orders_2(k2_yellow_1(X0))
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(resolution,[],[f60,f46])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r3_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f44,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(f377,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(k2_yellow_1(sK0),X0,k10_lattice3(k2_yellow_1(sK0),X1,X0))
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X1,sK0) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f376])).

fof(f378,plain,
    ( spl4_8
    | spl4_11
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f374,f79,f376,f119])).

fof(f374,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X1,sK0)
        | r1_orders_2(k2_yellow_1(sK0),X0,k10_lattice3(k2_yellow_1(sK0),X1,X0))
        | v2_struct_0(k2_yellow_1(sK0)) )
    | ~ spl4_4 ),
    inference(resolution,[],[f128,f80])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_lattice3(k2_yellow_1(X1))
      | ~ m1_subset_1(X0,X1)
      | ~ m1_subset_1(X2,X1)
      | r1_orders_2(k2_yellow_1(X1),X0,k10_lattice3(k2_yellow_1(X1),X2,X0))
      | v2_struct_0(k2_yellow_1(X1)) ) ),
    inference(global_subsumption,[],[f46,f127])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X1)
      | ~ m1_subset_1(X0,X1)
      | ~ l1_orders_2(k2_yellow_1(X1))
      | ~ v1_lattice3(k2_yellow_1(X1))
      | r1_orders_2(k2_yellow_1(X1),X0,k10_lattice3(k2_yellow_1(X1),X2,X0))
      | v2_struct_0(k2_yellow_1(X1)) ) ),
    inference(forward_demodulation,[],[f126,f47])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
      | ~ l1_orders_2(k2_yellow_1(X1))
      | ~ v1_lattice3(k2_yellow_1(X1))
      | r1_orders_2(k2_yellow_1(X1),X0,k10_lattice3(k2_yellow_1(X1),X2,X0))
      | v2_struct_0(k2_yellow_1(X1)) ) ),
    inference(forward_demodulation,[],[f125,f47])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
      | ~ l1_orders_2(k2_yellow_1(X1))
      | ~ v1_lattice3(k2_yellow_1(X1))
      | r1_orders_2(k2_yellow_1(X1),X0,k10_lattice3(k2_yellow_1(X1),X2,X0))
      | v2_struct_0(k2_yellow_1(X1)) ) ),
    inference(resolution,[],[f91,f45])).

fof(f45,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

% (16649)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2))
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f64,f61])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X2,X3)
      | k10_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).

fof(f36,plain,(
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

% (16641)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

% (16648)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f33,plain,(
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
    inference(nnf_transformation,[],[f21])).

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
    inference(flattening,[],[f20])).

% (16646)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
fof(f20,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l26_lattice3)).

fof(f139,plain,
    ( spl4_5
    | spl4_10
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f134,f122,f79,f137,f83])).

% (16655)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
fof(f122,plain,
    ( spl4_9
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X1,sK0)
        | r1_orders_2(k2_yellow_1(sK0),X1,k10_lattice3(k2_yellow_1(sK0),X1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f134,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X1,X0),sK0)
        | r1_tarski(X1,k10_lattice3(k2_yellow_1(sK0),X1,X0))
        | v1_xboole_0(sK0) )
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(duplicate_literal_removal,[],[f133])).

fof(f133,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X1,X0),sK0)
        | r1_tarski(X1,k10_lattice3(k2_yellow_1(sK0),X1,X0))
        | ~ m1_subset_1(X1,sK0)
        | v1_xboole_0(sK0) )
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(resolution,[],[f132,f89])).

fof(f132,plain,
    ( ! [X0,X1] :
        ( r3_orders_2(k2_yellow_1(sK0),X1,k10_lattice3(k2_yellow_1(sK0),X1,X0))
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X1,sK0) )
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(duplicate_literal_removal,[],[f131])).

fof(f131,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,sK0)
        | r3_orders_2(k2_yellow_1(sK0),X1,k10_lattice3(k2_yellow_1(sK0),X1,X0))
        | ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X1,sK0) )
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(resolution,[],[f130,f104])).

fof(f130,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X0,X1),sK0)
        | ~ m1_subset_1(X1,sK0)
        | r3_orders_2(k2_yellow_1(sK0),X0,k10_lattice3(k2_yellow_1(sK0),X0,X1))
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(duplicate_literal_removal,[],[f129])).

fof(f129,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X1,sK0)
        | r3_orders_2(k2_yellow_1(sK0),X0,k10_lattice3(k2_yellow_1(sK0),X0,X1))
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X0,X1),sK0) )
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(resolution,[],[f123,f111])).

fof(f123,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(k2_yellow_1(sK0),X1,k10_lattice3(k2_yellow_1(sK0),X1,X0))
        | ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f122])).

fof(f124,plain,
    ( spl4_8
    | spl4_9
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f117,f79,f122,f119])).

fof(f117,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X1,sK0)
        | r1_orders_2(k2_yellow_1(sK0),X1,k10_lattice3(k2_yellow_1(sK0),X1,X0))
        | v2_struct_0(k2_yellow_1(sK0)) )
    | ~ spl4_4 ),
    inference(resolution,[],[f116,f80])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_lattice3(k2_yellow_1(X1))
      | ~ m1_subset_1(X0,X1)
      | ~ m1_subset_1(X2,X1)
      | r1_orders_2(k2_yellow_1(X1),X2,k10_lattice3(k2_yellow_1(X1),X2,X0))
      | v2_struct_0(k2_yellow_1(X1)) ) ),
    inference(global_subsumption,[],[f46,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X1)
      | ~ m1_subset_1(X0,X1)
      | ~ l1_orders_2(k2_yellow_1(X1))
      | ~ v1_lattice3(k2_yellow_1(X1))
      | r1_orders_2(k2_yellow_1(X1),X2,k10_lattice3(k2_yellow_1(X1),X2,X0))
      | v2_struct_0(k2_yellow_1(X1)) ) ),
    inference(forward_demodulation,[],[f114,f47])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
      | ~ l1_orders_2(k2_yellow_1(X1))
      | ~ v1_lattice3(k2_yellow_1(X1))
      | r1_orders_2(k2_yellow_1(X1),X2,k10_lattice3(k2_yellow_1(X1),X2,X0))
      | v2_struct_0(k2_yellow_1(X1)) ) ),
    inference(forward_demodulation,[],[f113,f47])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
      | ~ l1_orders_2(k2_yellow_1(X1))
      | ~ v1_lattice3(k2_yellow_1(X1))
      | r1_orders_2(k2_yellow_1(X1),X2,k10_lattice3(k2_yellow_1(X1),X2,X0))
      | v2_struct_0(k2_yellow_1(X1)) ) ),
    inference(resolution,[],[f90,f45])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f65,f61])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f102,plain,
    ( spl4_7
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f98,f71,f100])).

fof(f71,plain,
    ( spl4_2
  <=> m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f98,plain,
    ( m1_subset_1(sK2,sK0)
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f72,f47])).

fof(f72,plain,
    ( m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f97,plain,
    ( spl4_6
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f93,f75,f95])).

fof(f75,plain,
    ( spl4_3
  <=> m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f93,plain,
    ( m1_subset_1(sK1,sK0)
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f76,f47])).

fof(f76,plain,
    ( m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f75])).

fof(f85,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f39,f83])).

fof(f39,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ~ r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    & v1_lattice3(k2_yellow_1(sK0))
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f30,f29,f28])).

fof(f28,plain,
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

fof(f29,plain,
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

fof(f30,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k2_xboole_0(sK1,X2),k10_lattice3(k2_yellow_1(sK0),sK1,X2))
        & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
   => ( ~ r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
      & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v1_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v1_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( v1_lattice3(k2_yellow_1(X0))
         => ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
                 => r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_lattice3(k2_yellow_1(X0))
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
               => r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_1)).

fof(f81,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f40,f79])).

fof(f40,plain,(
    v1_lattice3(k2_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f77,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f41,f75])).

fof(f41,plain,(
    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f73,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f42,f71])).

fof(f42,plain,(
    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f69,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f43,f67])).

fof(f43,plain,(
    ~ r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:02:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (16642)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.51  % (16643)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.51  % (16644)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.51  % (16650)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.51  % (16651)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.52  % (16651)Refutation not found, incomplete strategy% (16651)------------------------------
% 0.22/0.52  % (16651)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (16651)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (16651)Memory used [KB]: 6140
% 0.22/0.52  % (16651)Time elapsed: 0.070 s
% 0.22/0.52  % (16651)------------------------------
% 0.22/0.52  % (16651)------------------------------
% 0.22/0.52  % (16652)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.54  % (16636)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.56  % (16638)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.56  % (16640)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.56  % (16642)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % (16639)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.56  % (16653)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.57  % (16636)Refutation not found, incomplete strategy% (16636)------------------------------
% 0.22/0.57  % (16636)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (16636)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (16636)Memory used [KB]: 6140
% 0.22/0.57  % (16636)Time elapsed: 0.124 s
% 0.22/0.57  % (16636)------------------------------
% 0.22/0.57  % (16636)------------------------------
% 0.22/0.57  fof(f617,plain,(
% 0.22/0.57    $false),
% 0.22/0.57    inference(avatar_sat_refutation,[],[f69,f73,f77,f81,f85,f97,f102,f124,f139,f378,f388,f394,f396,f416,f610,f616])).
% 0.22/0.57  fof(f616,plain,(
% 0.22/0.57    ~spl4_7 | ~spl4_6 | ~spl4_10 | spl4_42),
% 0.22/0.57    inference(avatar_split_clause,[],[f615,f608,f137,f95,f100])).
% 0.22/0.57  fof(f100,plain,(
% 0.22/0.57    spl4_7 <=> m1_subset_1(sK2,sK0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.57  fof(f95,plain,(
% 0.22/0.57    spl4_6 <=> m1_subset_1(sK1,sK0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.57  fof(f137,plain,(
% 0.22/0.57    spl4_10 <=> ! [X1,X0] : (~m1_subset_1(X0,sK0) | r1_tarski(X1,k10_lattice3(k2_yellow_1(sK0),X1,X0)) | ~m1_subset_1(X1,sK0) | ~m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X1,X0),sK0))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.57  fof(f608,plain,(
% 0.22/0.57    spl4_42 <=> r1_tarski(sK1,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 0.22/0.57  fof(f615,plain,(
% 0.22/0.57    ~m1_subset_1(sK1,sK0) | ~m1_subset_1(sK2,sK0) | (~spl4_10 | spl4_42)),
% 0.22/0.57    inference(resolution,[],[f609,f141])).
% 0.22/0.57  fof(f141,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_tarski(X0,k10_lattice3(k2_yellow_1(sK0),X0,X1)) | ~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,sK0)) ) | ~spl4_10),
% 0.22/0.57    inference(duplicate_literal_removal,[],[f140])).
% 0.22/0.57  fof(f140,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_tarski(X0,k10_lattice3(k2_yellow_1(sK0),X0,X1)) | ~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,sK0) | ~m1_subset_1(X1,sK0) | ~m1_subset_1(X0,sK0)) ) | ~spl4_10),
% 0.22/0.57    inference(resolution,[],[f138,f104])).
% 0.22/0.57  fof(f104,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (m1_subset_1(k10_lattice3(k2_yellow_1(X0),X1,X2),X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0)) )),
% 0.22/0.57    inference(global_subsumption,[],[f46,f103])).
% 0.22/0.57  fof(f103,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (m1_subset_1(k10_lattice3(k2_yellow_1(X0),X1,X2),X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~l1_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.57    inference(superposition,[],[f61,f47])).
% 0.22/0.57  fof(f47,plain,(
% 0.22/0.57    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.22/0.57    inference(cnf_transformation,[],[f8])).
% 0.22/0.57  fof(f8,axiom,(
% 0.22/0.57    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).
% 0.22/0.57  % (16654)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.57  fof(f61,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f25])).
% 0.22/0.57  fof(f25,plain,(
% 0.22/0.57    ! [X0,X1,X2] : (m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.22/0.57    inference(flattening,[],[f24])).
% 0.22/0.57  fof(f24,plain,(
% 0.22/0.57    ! [X0,X1,X2] : (m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f4])).
% 0.22/0.57  fof(f4,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0)) => m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_lattice3)).
% 0.22/0.57  fof(f46,plain,(
% 0.22/0.57    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f13])).
% 0.22/0.57  fof(f13,plain,(
% 0.22/0.57    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 0.22/0.57    inference(pure_predicate_removal,[],[f6])).
% 0.22/0.57  fof(f6,axiom,(
% 0.22/0.57    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 0.22/0.57  fof(f138,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X1,X0),sK0) | r1_tarski(X1,k10_lattice3(k2_yellow_1(sK0),X1,X0)) | ~m1_subset_1(X1,sK0) | ~m1_subset_1(X0,sK0)) ) | ~spl4_10),
% 0.22/0.57    inference(avatar_component_clause,[],[f137])).
% 0.22/0.57  fof(f609,plain,(
% 0.22/0.57    ~r1_tarski(sK1,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) | spl4_42),
% 0.22/0.57    inference(avatar_component_clause,[],[f608])).
% 0.22/0.57  fof(f610,plain,(
% 0.22/0.57    ~spl4_42 | spl4_1 | ~spl4_15),
% 0.22/0.57    inference(avatar_split_clause,[],[f603,f414,f67,f608])).
% 0.22/0.57  fof(f67,plain,(
% 0.22/0.57    spl4_1 <=> r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.57  fof(f414,plain,(
% 0.22/0.57    spl4_15 <=> r1_tarski(sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.22/0.57  fof(f603,plain,(
% 0.22/0.57    ~r1_tarski(sK1,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) | (spl4_1 | ~spl4_15)),
% 0.22/0.57    inference(resolution,[],[f433,f68])).
% 0.22/0.57  fof(f68,plain,(
% 0.22/0.57    ~r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) | spl4_1),
% 0.22/0.57    inference(avatar_component_clause,[],[f67])).
% 0.22/0.57  fof(f433,plain,(
% 0.22/0.57    ( ! [X1] : (r1_tarski(k2_xboole_0(X1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~r1_tarski(X1,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))) ) | ~spl4_15),
% 0.22/0.57    inference(resolution,[],[f415,f62])).
% 0.22/0.57  fof(f62,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X2,X1) | r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f27])).
% 0.22/0.57  fof(f27,plain,(
% 0.22/0.57    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.22/0.57    inference(flattening,[],[f26])).
% 0.22/0.57  fof(f26,plain,(
% 0.22/0.57    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.22/0.57    inference(ennf_transformation,[],[f1])).
% 0.22/0.57  fof(f1,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.22/0.57  fof(f415,plain,(
% 0.22/0.57    r1_tarski(sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~spl4_15),
% 0.22/0.57    inference(avatar_component_clause,[],[f414])).
% 0.22/0.57  fof(f416,plain,(
% 0.22/0.57    spl4_15 | ~spl4_6 | ~spl4_7 | ~spl4_12),
% 0.22/0.57    inference(avatar_split_clause,[],[f407,f386,f100,f95,f414])).
% 0.22/0.57  fof(f386,plain,(
% 0.22/0.57    spl4_12 <=> ! [X1,X0] : (~m1_subset_1(X0,sK0) | r1_tarski(X1,k10_lattice3(k2_yellow_1(sK0),X0,X1)) | ~m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X0,X1),sK0) | ~m1_subset_1(X1,sK0))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.22/0.57  fof(f407,plain,(
% 0.22/0.57    r1_tarski(sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) | (~spl4_6 | ~spl4_7 | ~spl4_12)),
% 0.22/0.57    inference(resolution,[],[f403,f101])).
% 0.22/0.57  fof(f101,plain,(
% 0.22/0.57    m1_subset_1(sK2,sK0) | ~spl4_7),
% 0.22/0.57    inference(avatar_component_clause,[],[f100])).
% 0.22/0.57  fof(f403,plain,(
% 0.22/0.57    ( ! [X0] : (~m1_subset_1(X0,sK0) | r1_tarski(X0,k10_lattice3(k2_yellow_1(sK0),sK1,X0))) ) | (~spl4_6 | ~spl4_12)),
% 0.22/0.57    inference(resolution,[],[f402,f96])).
% 0.22/0.57  fof(f96,plain,(
% 0.22/0.57    m1_subset_1(sK1,sK0) | ~spl4_6),
% 0.22/0.57    inference(avatar_component_clause,[],[f95])).
% 0.22/0.57  fof(f402,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,sK0) | r1_tarski(X0,k10_lattice3(k2_yellow_1(sK0),X1,X0)) | ~m1_subset_1(X0,sK0)) ) | ~spl4_12),
% 0.22/0.57    inference(duplicate_literal_removal,[],[f401])).
% 0.22/0.57  fof(f401,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_tarski(X0,k10_lattice3(k2_yellow_1(sK0),X1,X0)) | ~m1_subset_1(X1,sK0) | ~m1_subset_1(X0,sK0) | ~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,sK0)) ) | ~spl4_12),
% 0.22/0.57    inference(resolution,[],[f387,f104])).
% 0.22/0.57  fof(f387,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X0,X1),sK0) | r1_tarski(X1,k10_lattice3(k2_yellow_1(sK0),X0,X1)) | ~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,sK0)) ) | ~spl4_12),
% 0.22/0.57    inference(avatar_component_clause,[],[f386])).
% 0.22/0.57  fof(f396,plain,(
% 0.22/0.57    spl4_13),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f395])).
% 0.22/0.57  fof(f395,plain,(
% 0.22/0.57    $false | spl4_13),
% 0.22/0.57    inference(resolution,[],[f392,f46])).
% 0.22/0.57  fof(f392,plain,(
% 0.22/0.57    ~l1_orders_2(k2_yellow_1(sK0)) | spl4_13),
% 0.22/0.57    inference(avatar_component_clause,[],[f391])).
% 0.22/0.57  fof(f391,plain,(
% 0.22/0.57    spl4_13 <=> l1_orders_2(k2_yellow_1(sK0))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.22/0.57  fof(f394,plain,(
% 0.22/0.57    ~spl4_13 | ~spl4_4 | ~spl4_8),
% 0.22/0.57    inference(avatar_split_clause,[],[f389,f119,f79,f391])).
% 0.22/0.57  fof(f79,plain,(
% 0.22/0.57    spl4_4 <=> v1_lattice3(k2_yellow_1(sK0))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.57  fof(f119,plain,(
% 0.22/0.57    spl4_8 <=> v2_struct_0(k2_yellow_1(sK0))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.57  fof(f389,plain,(
% 0.22/0.57    ~v1_lattice3(k2_yellow_1(sK0)) | ~l1_orders_2(k2_yellow_1(sK0)) | ~spl4_8),
% 0.22/0.57    inference(resolution,[],[f120,f51])).
% 0.22/0.57  fof(f51,plain,(
% 0.22/0.57    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f19])).
% 0.22/0.57  fof(f19,plain,(
% 0.22/0.57    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 0.22/0.57    inference(flattening,[],[f18])).
% 0.22/0.57  fof(f18,plain,(
% 0.22/0.57    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f3])).
% 0.22/0.57  fof(f3,axiom,(
% 0.22/0.57    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).
% 0.22/0.57  fof(f120,plain,(
% 0.22/0.57    v2_struct_0(k2_yellow_1(sK0)) | ~spl4_8),
% 0.22/0.57    inference(avatar_component_clause,[],[f119])).
% 0.22/0.57  fof(f388,plain,(
% 0.22/0.57    spl4_5 | spl4_12 | ~spl4_4 | ~spl4_11),
% 0.22/0.57    inference(avatar_split_clause,[],[f384,f376,f79,f386,f83])).
% 0.22/0.57  fof(f83,plain,(
% 0.22/0.57    spl4_5 <=> v1_xboole_0(sK0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.57  fof(f376,plain,(
% 0.22/0.57    spl4_11 <=> ! [X1,X0] : (~m1_subset_1(X0,sK0) | r1_orders_2(k2_yellow_1(sK0),X0,k10_lattice3(k2_yellow_1(sK0),X1,X0)) | ~m1_subset_1(X1,sK0))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.22/0.57  fof(f384,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,sK0) | ~m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X0,X1),sK0) | r1_tarski(X1,k10_lattice3(k2_yellow_1(sK0),X0,X1)) | v1_xboole_0(sK0)) ) | (~spl4_4 | ~spl4_11)),
% 0.22/0.57    inference(duplicate_literal_removal,[],[f383])).
% 0.22/0.57  fof(f383,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,sK0) | ~m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X0,X1),sK0) | r1_tarski(X1,k10_lattice3(k2_yellow_1(sK0),X0,X1)) | ~m1_subset_1(X1,sK0) | v1_xboole_0(sK0)) ) | (~spl4_4 | ~spl4_11)),
% 0.22/0.57    inference(resolution,[],[f382,f89])).
% 0.22/0.57  fof(f89,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,X0) | r1_tarski(X1,X2) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.57    inference(forward_demodulation,[],[f88,f47])).
% 0.22/0.57  fof(f88,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.22/0.57    inference(forward_demodulation,[],[f49,f47])).
% 0.22/0.57  fof(f49,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f32])).
% 0.22/0.57  fof(f32,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (! [X2] : (((r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.22/0.57    inference(nnf_transformation,[],[f17])).
% 0.22/0.57  fof(f17,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f9])).
% 0.22/0.57  fof(f9,axiom,(
% 0.22/0.57    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).
% 0.22/0.57  fof(f382,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r3_orders_2(k2_yellow_1(sK0),X1,k10_lattice3(k2_yellow_1(sK0),X0,X1)) | ~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,sK0)) ) | (~spl4_4 | ~spl4_11)),
% 0.22/0.57    inference(duplicate_literal_removal,[],[f381])).
% 0.22/0.57  fof(f381,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,sK0) | r3_orders_2(k2_yellow_1(sK0),X1,k10_lattice3(k2_yellow_1(sK0),X0,X1)) | ~m1_subset_1(X1,sK0) | ~m1_subset_1(X1,sK0) | ~m1_subset_1(X0,sK0)) ) | (~spl4_4 | ~spl4_11)),
% 0.22/0.57    inference(resolution,[],[f380,f104])).
% 0.22/0.57  fof(f380,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X1,X0),sK0) | ~m1_subset_1(X1,sK0) | r3_orders_2(k2_yellow_1(sK0),X0,k10_lattice3(k2_yellow_1(sK0),X1,X0)) | ~m1_subset_1(X0,sK0)) ) | (~spl4_4 | ~spl4_11)),
% 0.22/0.57    inference(duplicate_literal_removal,[],[f379])).
% 0.22/0.57  fof(f379,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,sK0) | r3_orders_2(k2_yellow_1(sK0),X0,k10_lattice3(k2_yellow_1(sK0),X1,X0)) | ~m1_subset_1(X0,sK0) | ~m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X1,X0),sK0)) ) | (~spl4_4 | ~spl4_11)),
% 0.22/0.57    inference(resolution,[],[f377,f111])).
% 0.22/0.57  fof(f111,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r1_orders_2(k2_yellow_1(sK0),X0,X1) | r3_orders_2(k2_yellow_1(sK0),X0,X1) | ~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,sK0)) ) | ~spl4_4),
% 0.22/0.57    inference(resolution,[],[f110,f80])).
% 0.22/0.57  fof(f80,plain,(
% 0.22/0.57    v1_lattice3(k2_yellow_1(sK0)) | ~spl4_4),
% 0.22/0.57    inference(avatar_component_clause,[],[f79])).
% 0.22/0.57  fof(f110,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~v1_lattice3(k2_yellow_1(X1)) | ~r1_orders_2(k2_yellow_1(X1),X2,X0) | r3_orders_2(k2_yellow_1(X1),X2,X0) | ~m1_subset_1(X2,X1) | ~m1_subset_1(X0,X1)) )),
% 0.22/0.57    inference(global_subsumption,[],[f46,f109])).
% 0.22/0.57  fof(f109,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X0,X1) | ~r1_orders_2(k2_yellow_1(X1),X2,X0) | r3_orders_2(k2_yellow_1(X1),X2,X0) | ~m1_subset_1(X2,X1) | ~v1_lattice3(k2_yellow_1(X1)) | ~l1_orders_2(k2_yellow_1(X1))) )),
% 0.22/0.57    inference(resolution,[],[f108,f51])).
% 0.22/0.57  fof(f108,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (v2_struct_0(k2_yellow_1(X0)) | ~m1_subset_1(X2,X0) | ~r1_orders_2(k2_yellow_1(X0),X1,X2) | r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,X0)) )),
% 0.22/0.57    inference(global_subsumption,[],[f44,f107])).
% 0.22/0.57  fof(f107,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | ~m1_subset_1(X2,X0) | ~r1_orders_2(k2_yellow_1(X0),X1,X2) | r3_orders_2(k2_yellow_1(X0),X1,X2) | ~v3_orders_2(k2_yellow_1(X0)) | v2_struct_0(k2_yellow_1(X0))) )),
% 0.22/0.57    inference(forward_demodulation,[],[f106,f47])).
% 0.22/0.57  fof(f106,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | ~r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | r3_orders_2(k2_yellow_1(X0),X1,X2) | ~v3_orders_2(k2_yellow_1(X0)) | v2_struct_0(k2_yellow_1(X0))) )),
% 0.22/0.57    inference(forward_demodulation,[],[f105,f47])).
% 0.22/0.57  fof(f105,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | r3_orders_2(k2_yellow_1(X0),X1,X2) | ~v3_orders_2(k2_yellow_1(X0)) | v2_struct_0(k2_yellow_1(X0))) )),
% 0.22/0.57    inference(resolution,[],[f60,f46])).
% 0.22/0.57  fof(f60,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r3_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f38])).
% 0.22/0.57  fof(f38,plain,(
% 0.22/0.57    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.57    inference(nnf_transformation,[],[f23])).
% 0.22/0.57  fof(f23,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.57    inference(flattening,[],[f22])).
% 0.22/0.57  fof(f22,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f2])).
% 0.22/0.57  fof(f2,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.22/0.57  fof(f44,plain,(
% 0.22/0.57    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f14])).
% 0.22/0.57  fof(f14,plain,(
% 0.22/0.57    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)))),
% 0.22/0.57    inference(pure_predicate_removal,[],[f12])).
% 0.22/0.57  fof(f12,plain,(
% 0.22/0.57    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.22/0.57    inference(pure_predicate_removal,[],[f7])).
% 0.22/0.57  fof(f7,axiom,(
% 0.22/0.57    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).
% 0.22/0.57  fof(f377,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_orders_2(k2_yellow_1(sK0),X0,k10_lattice3(k2_yellow_1(sK0),X1,X0)) | ~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,sK0)) ) | ~spl4_11),
% 0.22/0.57    inference(avatar_component_clause,[],[f376])).
% 0.22/0.57  fof(f378,plain,(
% 0.22/0.57    spl4_8 | spl4_11 | ~spl4_4),
% 0.22/0.57    inference(avatar_split_clause,[],[f374,f79,f376,f119])).
% 0.22/0.57  fof(f374,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,sK0) | r1_orders_2(k2_yellow_1(sK0),X0,k10_lattice3(k2_yellow_1(sK0),X1,X0)) | v2_struct_0(k2_yellow_1(sK0))) ) | ~spl4_4),
% 0.22/0.57    inference(resolution,[],[f128,f80])).
% 0.22/0.57  fof(f128,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~v1_lattice3(k2_yellow_1(X1)) | ~m1_subset_1(X0,X1) | ~m1_subset_1(X2,X1) | r1_orders_2(k2_yellow_1(X1),X0,k10_lattice3(k2_yellow_1(X1),X2,X0)) | v2_struct_0(k2_yellow_1(X1))) )),
% 0.22/0.57    inference(global_subsumption,[],[f46,f127])).
% 0.22/0.57  fof(f127,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X1) | ~m1_subset_1(X0,X1) | ~l1_orders_2(k2_yellow_1(X1)) | ~v1_lattice3(k2_yellow_1(X1)) | r1_orders_2(k2_yellow_1(X1),X0,k10_lattice3(k2_yellow_1(X1),X2,X0)) | v2_struct_0(k2_yellow_1(X1))) )),
% 0.22/0.57    inference(forward_demodulation,[],[f126,f47])).
% 0.22/0.57  fof(f126,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X0,X1) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) | ~l1_orders_2(k2_yellow_1(X1)) | ~v1_lattice3(k2_yellow_1(X1)) | r1_orders_2(k2_yellow_1(X1),X0,k10_lattice3(k2_yellow_1(X1),X2,X0)) | v2_struct_0(k2_yellow_1(X1))) )),
% 0.22/0.57    inference(forward_demodulation,[],[f125,f47])).
% 0.22/0.57  fof(f125,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) | ~l1_orders_2(k2_yellow_1(X1)) | ~v1_lattice3(k2_yellow_1(X1)) | r1_orders_2(k2_yellow_1(X1),X0,k10_lattice3(k2_yellow_1(X1),X2,X0)) | v2_struct_0(k2_yellow_1(X1))) )),
% 0.22/0.57    inference(resolution,[],[f91,f45])).
% 0.22/0.57  fof(f45,plain,(
% 0.22/0.57    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f14])).
% 0.22/0.57  % (16649)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.57  fof(f91,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~v5_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2)) | v2_struct_0(X0)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f64,f61])).
% 0.22/0.57  fof(f64,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2)) | ~m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.57    inference(equality_resolution,[],[f53])).
% 0.22/0.57  fof(f53,plain,(
% 0.22/0.57    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X2,X3) | k10_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f37])).
% 0.22/0.57  fof(f37,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,X3,sK3(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK3(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK3(X0,X1,X2,X3)) & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).
% 0.22/0.57  fof(f36,plain,(
% 0.22/0.57    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,X3,sK3(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK3(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK3(X0,X1,X2,X3)) & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0))))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  % (16641)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.57  fof(f35,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.57    inference(rectify,[],[f34])).
% 0.22/0.57  fof(f34,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.57    inference(flattening,[],[f33])).
% 0.22/0.57  % (16648)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.57  fof(f33,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3))) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.57    inference(nnf_transformation,[],[f21])).
% 0.22/0.57  fof(f21,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.57    inference(flattening,[],[f20])).
% 0.22/0.57  % (16646)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.57  fof(f20,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X3,X4) | (~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f5])).
% 0.22/0.57  fof(f5,axiom,(
% 0.22/0.57    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)))))))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l26_lattice3)).
% 0.22/0.57  fof(f139,plain,(
% 0.22/0.57    spl4_5 | spl4_10 | ~spl4_4 | ~spl4_9),
% 0.22/0.57    inference(avatar_split_clause,[],[f134,f122,f79,f137,f83])).
% 0.22/0.57  % (16655)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.57  fof(f122,plain,(
% 0.22/0.57    spl4_9 <=> ! [X1,X0] : (~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,sK0) | r1_orders_2(k2_yellow_1(sK0),X1,k10_lattice3(k2_yellow_1(sK0),X1,X0)))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.57  fof(f134,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,sK0) | ~m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X1,X0),sK0) | r1_tarski(X1,k10_lattice3(k2_yellow_1(sK0),X1,X0)) | v1_xboole_0(sK0)) ) | (~spl4_4 | ~spl4_9)),
% 0.22/0.57    inference(duplicate_literal_removal,[],[f133])).
% 0.22/0.57  fof(f133,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,sK0) | ~m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X1,X0),sK0) | r1_tarski(X1,k10_lattice3(k2_yellow_1(sK0),X1,X0)) | ~m1_subset_1(X1,sK0) | v1_xboole_0(sK0)) ) | (~spl4_4 | ~spl4_9)),
% 0.22/0.57    inference(resolution,[],[f132,f89])).
% 0.22/0.57  fof(f132,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r3_orders_2(k2_yellow_1(sK0),X1,k10_lattice3(k2_yellow_1(sK0),X1,X0)) | ~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,sK0)) ) | (~spl4_4 | ~spl4_9)),
% 0.22/0.57    inference(duplicate_literal_removal,[],[f131])).
% 0.22/0.57  fof(f131,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,sK0) | r3_orders_2(k2_yellow_1(sK0),X1,k10_lattice3(k2_yellow_1(sK0),X1,X0)) | ~m1_subset_1(X1,sK0) | ~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,sK0)) ) | (~spl4_4 | ~spl4_9)),
% 0.22/0.57    inference(resolution,[],[f130,f104])).
% 0.22/0.57  fof(f130,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X0,X1),sK0) | ~m1_subset_1(X1,sK0) | r3_orders_2(k2_yellow_1(sK0),X0,k10_lattice3(k2_yellow_1(sK0),X0,X1)) | ~m1_subset_1(X0,sK0)) ) | (~spl4_4 | ~spl4_9)),
% 0.22/0.57    inference(duplicate_literal_removal,[],[f129])).
% 0.22/0.57  fof(f129,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,sK0) | r3_orders_2(k2_yellow_1(sK0),X0,k10_lattice3(k2_yellow_1(sK0),X0,X1)) | ~m1_subset_1(X0,sK0) | ~m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X0,X1),sK0)) ) | (~spl4_4 | ~spl4_9)),
% 0.22/0.57    inference(resolution,[],[f123,f111])).
% 0.22/0.57  fof(f123,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_orders_2(k2_yellow_1(sK0),X1,k10_lattice3(k2_yellow_1(sK0),X1,X0)) | ~m1_subset_1(X1,sK0) | ~m1_subset_1(X0,sK0)) ) | ~spl4_9),
% 0.22/0.57    inference(avatar_component_clause,[],[f122])).
% 0.22/0.57  fof(f124,plain,(
% 0.22/0.57    spl4_8 | spl4_9 | ~spl4_4),
% 0.22/0.57    inference(avatar_split_clause,[],[f117,f79,f122,f119])).
% 0.22/0.57  fof(f117,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,sK0) | r1_orders_2(k2_yellow_1(sK0),X1,k10_lattice3(k2_yellow_1(sK0),X1,X0)) | v2_struct_0(k2_yellow_1(sK0))) ) | ~spl4_4),
% 0.22/0.57    inference(resolution,[],[f116,f80])).
% 0.22/0.57  fof(f116,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~v1_lattice3(k2_yellow_1(X1)) | ~m1_subset_1(X0,X1) | ~m1_subset_1(X2,X1) | r1_orders_2(k2_yellow_1(X1),X2,k10_lattice3(k2_yellow_1(X1),X2,X0)) | v2_struct_0(k2_yellow_1(X1))) )),
% 0.22/0.57    inference(global_subsumption,[],[f46,f115])).
% 0.22/0.57  fof(f115,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X1) | ~m1_subset_1(X0,X1) | ~l1_orders_2(k2_yellow_1(X1)) | ~v1_lattice3(k2_yellow_1(X1)) | r1_orders_2(k2_yellow_1(X1),X2,k10_lattice3(k2_yellow_1(X1),X2,X0)) | v2_struct_0(k2_yellow_1(X1))) )),
% 0.22/0.57    inference(forward_demodulation,[],[f114,f47])).
% 0.22/0.57  fof(f114,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X0,X1) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) | ~l1_orders_2(k2_yellow_1(X1)) | ~v1_lattice3(k2_yellow_1(X1)) | r1_orders_2(k2_yellow_1(X1),X2,k10_lattice3(k2_yellow_1(X1),X2,X0)) | v2_struct_0(k2_yellow_1(X1))) )),
% 0.22/0.57    inference(forward_demodulation,[],[f113,f47])).
% 0.22/0.57  fof(f113,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) | ~l1_orders_2(k2_yellow_1(X1)) | ~v1_lattice3(k2_yellow_1(X1)) | r1_orders_2(k2_yellow_1(X1),X2,k10_lattice3(k2_yellow_1(X1),X2,X0)) | v2_struct_0(k2_yellow_1(X1))) )),
% 0.22/0.57    inference(resolution,[],[f90,f45])).
% 0.22/0.57  fof(f90,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~v5_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) | v2_struct_0(X0)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f65,f61])).
% 0.22/0.57  fof(f65,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) | ~m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.57    inference(equality_resolution,[],[f52])).
% 0.22/0.57  fof(f52,plain,(
% 0.22/0.57    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X1,X3) | k10_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f37])).
% 0.22/0.57  fof(f102,plain,(
% 0.22/0.57    spl4_7 | ~spl4_2),
% 0.22/0.57    inference(avatar_split_clause,[],[f98,f71,f100])).
% 0.22/0.57  fof(f71,plain,(
% 0.22/0.57    spl4_2 <=> m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.57  fof(f98,plain,(
% 0.22/0.57    m1_subset_1(sK2,sK0) | ~spl4_2),
% 0.22/0.57    inference(forward_demodulation,[],[f72,f47])).
% 0.22/0.57  fof(f72,plain,(
% 0.22/0.57    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~spl4_2),
% 0.22/0.57    inference(avatar_component_clause,[],[f71])).
% 0.22/0.57  fof(f97,plain,(
% 0.22/0.57    spl4_6 | ~spl4_3),
% 0.22/0.57    inference(avatar_split_clause,[],[f93,f75,f95])).
% 0.22/0.57  fof(f75,plain,(
% 0.22/0.57    spl4_3 <=> m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.57  fof(f93,plain,(
% 0.22/0.57    m1_subset_1(sK1,sK0) | ~spl4_3),
% 0.22/0.57    inference(forward_demodulation,[],[f76,f47])).
% 0.22/0.57  fof(f76,plain,(
% 0.22/0.57    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~spl4_3),
% 0.22/0.57    inference(avatar_component_clause,[],[f75])).
% 0.22/0.57  fof(f85,plain,(
% 0.22/0.57    ~spl4_5),
% 0.22/0.57    inference(avatar_split_clause,[],[f39,f83])).
% 0.22/0.57  fof(f39,plain,(
% 0.22/0.57    ~v1_xboole_0(sK0)),
% 0.22/0.57    inference(cnf_transformation,[],[f31])).
% 0.22/0.57  fof(f31,plain,(
% 0.22/0.57    ((~r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))) & v1_lattice3(k2_yellow_1(sK0)) & ~v1_xboole_0(sK0)),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f30,f29,f28])).
% 0.22/0.57  fof(f28,plain,(
% 0.22/0.57    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v1_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(sK0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))) & v1_lattice3(k2_yellow_1(sK0)) & ~v1_xboole_0(sK0))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f29,plain,(
% 0.22/0.57    ? [X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(sK0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))) => (? [X2] : (~r1_tarski(k2_xboole_0(sK1,X2),k10_lattice3(k2_yellow_1(sK0),sK1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f30,plain,(
% 0.22/0.57    ? [X2] : (~r1_tarski(k2_xboole_0(sK1,X2),k10_lattice3(k2_yellow_1(sK0),sK1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) => (~r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f16,plain,(
% 0.22/0.57    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v1_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0))),
% 0.22/0.57    inference(flattening,[],[f15])).
% 0.22/0.57  fof(f15,plain,(
% 0.22/0.57    ? [X0] : ((? [X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v1_lattice3(k2_yellow_1(X0))) & ~v1_xboole_0(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f11])).
% 0.22/0.57  fof(f11,negated_conjecture,(
% 0.22/0.57    ~! [X0] : (~v1_xboole_0(X0) => (v1_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))))))),
% 0.22/0.57    inference(negated_conjecture,[],[f10])).
% 0.22/0.57  fof(f10,conjecture,(
% 0.22/0.57    ! [X0] : (~v1_xboole_0(X0) => (v1_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))))))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_1)).
% 0.22/0.57  fof(f81,plain,(
% 0.22/0.57    spl4_4),
% 0.22/0.57    inference(avatar_split_clause,[],[f40,f79])).
% 0.22/0.57  fof(f40,plain,(
% 0.22/0.57    v1_lattice3(k2_yellow_1(sK0))),
% 0.22/0.57    inference(cnf_transformation,[],[f31])).
% 0.22/0.57  fof(f77,plain,(
% 0.22/0.57    spl4_3),
% 0.22/0.57    inference(avatar_split_clause,[],[f41,f75])).
% 0.22/0.57  fof(f41,plain,(
% 0.22/0.57    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 0.22/0.57    inference(cnf_transformation,[],[f31])).
% 0.22/0.57  fof(f73,plain,(
% 0.22/0.57    spl4_2),
% 0.22/0.57    inference(avatar_split_clause,[],[f42,f71])).
% 0.22/0.57  fof(f42,plain,(
% 0.22/0.57    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 0.22/0.57    inference(cnf_transformation,[],[f31])).
% 0.22/0.57  fof(f69,plain,(
% 0.22/0.57    ~spl4_1),
% 0.22/0.57    inference(avatar_split_clause,[],[f43,f67])).
% 0.22/0.57  fof(f43,plain,(
% 0.22/0.57    ~r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.22/0.57    inference(cnf_transformation,[],[f31])).
% 0.22/0.57  % SZS output end Proof for theBenchmark
% 0.22/0.57  % (16642)------------------------------
% 0.22/0.57  % (16642)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (16642)Termination reason: Refutation
% 0.22/0.57  
% 0.22/0.57  % (16642)Memory used [KB]: 11257
% 0.22/0.57  % (16642)Time elapsed: 0.111 s
% 0.22/0.57  % (16642)------------------------------
% 0.22/0.57  % (16642)------------------------------
% 0.22/0.57  % (16635)Success in time 0.206 s
%------------------------------------------------------------------------------
