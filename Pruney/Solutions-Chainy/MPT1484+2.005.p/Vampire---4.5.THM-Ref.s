%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 252 expanded)
%              Number of leaves         :   21 (  84 expanded)
%              Depth                    :   18
%              Number of atoms          :  781 (1229 expanded)
%              Number of equality atoms :   51 (  85 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f374,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f74,f79,f84,f89,f116,f121,f127,f132,f171,f180,f359,f371])).

fof(f371,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_6
    | spl5_9
    | ~ spl5_10
    | spl5_11
    | ~ spl5_14 ),
    inference(avatar_contradiction_clause,[],[f370])).

fof(f370,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_6
    | spl5_9
    | ~ spl5_10
    | spl5_11
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f369,f170])).

fof(f170,plain,
    ( sK2 != k10_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl5_11
  <=> sK2 = k10_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f369,plain,
    ( sK2 = k10_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_6
    | spl5_9
    | ~ spl5_10
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f368,f165])).

fof(f165,plain,
    ( m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl5_10
  <=> m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f368,plain,
    ( ~ m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | sK2 = k10_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_6
    | spl5_9
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f366,f115])).

fof(f115,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl5_6
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f366,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | sK2 = k10_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | spl5_9
    | ~ spl5_14 ),
    inference(resolution,[],[f358,f195])).

% (6744)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
fof(f195,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k10_lattice3(sK0,X0,X1) = X1 )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | spl5_9 ),
    inference(subsumption_resolution,[],[f194,f133])).

fof(f133,plain,
    ( ! [X4] :
        ( r3_orders_2(sK0,X4,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
    | ~ spl5_1
    | ~ spl5_5
    | spl5_9 ),
    inference(subsumption_resolution,[],[f111,f131])).

fof(f131,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_9 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl5_9
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f111,plain,
    ( ! [X4] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r3_orders_2(sK0,X4,X4) )
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f108,f68])).

fof(f68,plain,
    ( v3_orders_2(sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl5_1
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f108,plain,
    ( ! [X4] :
        ( ~ v3_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r3_orders_2(sK0,X4,X4) )
    | ~ spl5_5 ),
    inference(resolution,[],[f88,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r3_orders_2(X0,X1,X1) ) ),
    inference(condensation,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r3_orders_2(X0,X1,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
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
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

fof(f88,plain,
    ( l1_orders_2(sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl5_5
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f194,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k10_lattice3(sK0,X0,X1) = X1
        | ~ r3_orders_2(sK0,X1,X1) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | spl5_9 ),
    inference(duplicate_literal_removal,[],[f193])).

fof(f193,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k10_lattice3(sK0,X0,X1) = X1
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r3_orders_2(sK0,X1,X1) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | spl5_9 ),
    inference(resolution,[],[f191,f135])).

fof(f135,plain,
    ( ! [X2,X3] :
        ( r1_orders_2(sK0,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_orders_2(sK0,X2,X3) )
    | ~ spl5_1
    | ~ spl5_5
    | spl5_9 ),
    inference(subsumption_resolution,[],[f110,f131])).

fof(f110,plain,
    ( ! [X2,X3] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_orders_2(sK0,X2,X3)
        | ~ r3_orders_2(sK0,X2,X3) )
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f107,f68])).

fof(f107,plain,
    ( ! [X2,X3] :
        ( ~ v3_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_orders_2(sK0,X2,X3)
        | ~ r3_orders_2(sK0,X2,X3) )
    | ~ spl5_5 ),
    inference(resolution,[],[f88,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f191,plain,
    ( ! [X2,X3] :
        ( ~ r1_orders_2(sK0,X2,X2)
        | ~ r1_orders_2(sK0,X3,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k10_lattice3(sK0,X3,X2) = X2 )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(duplicate_literal_removal,[],[f188])).

fof(f188,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X3,X2)
        | ~ r1_orders_2(sK0,X2,X2)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k10_lattice3(sK0,X3,X2) = X2
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X3,X2)
        | ~ r1_orders_2(sK0,X2,X2)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k10_lattice3(sK0,X3,X2) = X2 )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(resolution,[],[f186,f182])).

fof(f182,plain,
    ( ! [X6,X7,X5] :
        ( r1_orders_2(sK0,X6,sK4(sK0,X5,X6,X7))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X5,X7)
        | ~ r1_orders_2(sK0,X6,X7)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | k10_lattice3(sK0,X5,X6) = X7 )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f181,f88])).

fof(f181,plain,
    ( ! [X6,X7,X5] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X5,X7)
        | ~ r1_orders_2(sK0,X6,X7)
        | r1_orders_2(sK0,X6,sK4(sK0,X5,X6,X7))
        | k10_lattice3(sK0,X5,X6) = X7 )
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f95,f78])).

fof(f78,plain,
    ( v1_lattice3(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl5_3
  <=> v1_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f95,plain,
    ( ! [X6,X7,X5] :
        ( ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X5,X7)
        | ~ r1_orders_2(sK0,X6,X7)
        | r1_orders_2(sK0,X6,sK4(sK0,X5,X6,X7))
        | k10_lattice3(sK0,X5,X6) = X7 )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f92,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

fof(f92,plain,
    ( ! [X6,X7,X5] :
        ( v2_struct_0(sK0)
        | ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X5,X7)
        | ~ r1_orders_2(sK0,X6,X7)
        | r1_orders_2(sK0,X6,sK4(sK0,X5,X6,X7))
        | k10_lattice3(sK0,X5,X6) = X7 )
    | ~ spl5_2 ),
    inference(resolution,[],[f73,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | r1_orders_2(X0,X2,sK4(X0,X1,X2,X3))
      | k10_lattice3(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l26_lattice3)).

fof(f73,plain,
    ( v5_orders_2(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl5_2
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f186,plain,
    ( ! [X10,X8,X9] :
        ( ~ r1_orders_2(sK0,X10,sK4(sK0,X8,X9,X10))
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X8,X10)
        | ~ r1_orders_2(sK0,X9,X10)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | k10_lattice3(sK0,X8,X9) = X10 )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f185,f88])).

fof(f185,plain,
    ( ! [X10,X8,X9] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X8,X10)
        | ~ r1_orders_2(sK0,X9,X10)
        | ~ r1_orders_2(sK0,X10,sK4(sK0,X8,X9,X10))
        | k10_lattice3(sK0,X8,X9) = X10 )
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f96,f78])).

fof(f96,plain,
    ( ! [X10,X8,X9] :
        ( ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X8,X10)
        | ~ r1_orders_2(sK0,X9,X10)
        | ~ r1_orders_2(sK0,X10,sK4(sK0,X8,X9,X10))
        | k10_lattice3(sK0,X8,X9) = X10 )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f93,f37])).

fof(f93,plain,
    ( ! [X10,X8,X9] :
        ( v2_struct_0(sK0)
        | ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X8,X10)
        | ~ r1_orders_2(sK0,X9,X10)
        | ~ r1_orders_2(sK0,X10,sK4(sK0,X8,X9,X10))
        | k10_lattice3(sK0,X8,X9) = X10 )
    | ~ spl5_2 ),
    inference(resolution,[],[f73,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X3,sK4(X0,X1,X2,X3))
      | k10_lattice3(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f358,plain,
    ( r1_orders_2(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f356])).

fof(f356,plain,
    ( spl5_14
  <=> r1_orders_2(sK0,k12_lattice3(sK0,sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f359,plain,
    ( spl5_14
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | spl5_9
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f317,f164,f129,f118,f113,f86,f81,f71,f356])).

fof(f81,plain,
    ( spl5_4
  <=> v2_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f118,plain,
    ( spl5_7
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f317,plain,
    ( r1_orders_2(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | spl5_9
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f316,f115])).

fof(f316,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r1_orders_2(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | spl5_9
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f313,f120])).

fof(f120,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f118])).

fof(f313,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r1_orders_2(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_5
    | spl5_9
    | ~ spl5_10 ),
    inference(resolution,[],[f156,f165])).

fof(f156,plain,
    ( ! [X6,X5] :
        ( ~ m1_subset_1(k12_lattice3(sK0,X5,X6),u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | r1_orders_2(sK0,k12_lattice3(sK0,X5,X6),X6) )
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_5
    | spl5_9 ),
    inference(subsumption_resolution,[],[f155,f131])).

fof(f155,plain,
    ( ! [X6,X5] :
        ( ~ m1_subset_1(k12_lattice3(sK0,X5,X6),u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r1_orders_2(sK0,k12_lattice3(sK0,X5,X6),X6) )
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f154,f88])).

fof(f154,plain,
    ( ! [X6,X5] :
        ( ~ m1_subset_1(k12_lattice3(sK0,X5,X6),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r1_orders_2(sK0,k12_lattice3(sK0,X5,X6),X6) )
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f153,f83])).

fof(f83,plain,
    ( v2_lattice3(sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f153,plain,
    ( ! [X6,X5] :
        ( ~ m1_subset_1(k12_lattice3(sK0,X5,X6),u1_struct_0(sK0))
        | ~ v2_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r1_orders_2(sK0,k12_lattice3(sK0,X5,X6),X6) )
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f142,f73])).

fof(f142,plain,
    ( ! [X6,X5] :
        ( ~ m1_subset_1(k12_lattice3(sK0,X5,X6),u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r1_orders_2(sK0,k12_lattice3(sK0,X5,X6),X6) )
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(duplicate_literal_removal,[],[f141])).

fof(f141,plain,
    ( ! [X6,X5] :
        ( ~ m1_subset_1(k12_lattice3(sK0,X5,X6),u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r1_orders_2(sK0,k12_lattice3(sK0,X5,X6),X6)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(superposition,[],[f58,f138])).

fof(f138,plain,
    ( ! [X0,X1] :
        ( k12_lattice3(sK0,X0,X1) = k11_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f102,f88])).

fof(f102,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k12_lattice3(sK0,X0,X1) = k11_lattice3(sK0,X0,X1) )
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f98,f73])).

fof(f98,plain,
    ( ! [X0,X1] :
        ( ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k12_lattice3(sK0,X0,X1) = k11_lattice3(sK0,X0,X1) )
    | ~ spl5_4 ),
    inference(resolution,[],[f83,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_orders_2(X0,X3,X2)
      | k11_lattice3(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f16])).

% (6739)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% (6734)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% (6747)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% (6746)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% (6730)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% (6748)Refutation not found, incomplete strategy% (6748)------------------------------
% (6748)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (6748)Termination reason: Refutation not found, incomplete strategy

% (6748)Memory used [KB]: 10618
% (6748)Time elapsed: 0.106 s
% (6748)------------------------------
% (6748)------------------------------
fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k11_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k11_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k11_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X4,X2)
                              & r1_orders_2(X0,X4,X1) )
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l28_lattice3)).

fof(f180,plain,
    ( ~ spl5_2
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | spl5_10 ),
    inference(avatar_contradiction_clause,[],[f179])).

fof(f179,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | spl5_10 ),
    inference(subsumption_resolution,[],[f178,f73])).

fof(f178,plain,
    ( ~ v5_orders_2(sK0)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | spl5_10 ),
    inference(subsumption_resolution,[],[f177,f115])).

fof(f177,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | spl5_10 ),
    inference(subsumption_resolution,[],[f176,f120])).

fof(f176,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ spl5_4
    | ~ spl5_5
    | spl5_10 ),
    inference(subsumption_resolution,[],[f175,f88])).

fof(f175,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ spl5_4
    | spl5_10 ),
    inference(subsumption_resolution,[],[f174,f83])).

fof(f174,plain,
    ( ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | spl5_10 ),
    inference(resolution,[],[f166,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k12_lattice3)).

fof(f166,plain,
    ( ~ m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | spl5_10 ),
    inference(avatar_component_clause,[],[f164])).

fof(f171,plain,
    ( ~ spl5_10
    | ~ spl5_11
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_6
    | spl5_8 ),
    inference(avatar_split_clause,[],[f160,f124,f113,f86,f76,f71,f168,f164])).

fof(f124,plain,
    ( spl5_8
  <=> sK2 = k13_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f160,plain,
    ( sK2 != k10_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
    | ~ m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_6
    | spl5_8 ),
    inference(subsumption_resolution,[],[f159,f115])).

fof(f159,plain,
    ( sK2 != k10_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | spl5_8 ),
    inference(superposition,[],[f126,f158])).

fof(f158,plain,
    ( ! [X0,X1] :
        ( k10_lattice3(sK0,X0,X1) = k13_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f157,f88])).

fof(f157,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k10_lattice3(sK0,X0,X1) = k13_lattice3(sK0,X0,X1) )
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f90,f78])).

fof(f90,plain,
    ( ! [X0,X1] :
        ( ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k10_lattice3(sK0,X0,X1) = k13_lattice3(sK0,X0,X1) )
    | ~ spl5_2 ),
    inference(resolution,[],[f73,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

fof(f126,plain,
    ( sK2 != k13_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f124])).

fof(f132,plain,
    ( ~ spl5_9
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f122,f86,f76,f129])).

fof(f122,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f97,f88])).

fof(f97,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v2_struct_0(sK0)
    | ~ spl5_3 ),
    inference(resolution,[],[f78,f37])).

fof(f127,plain,(
    ~ spl5_8 ),
    inference(avatar_split_clause,[],[f30,f124])).

fof(f30,plain,(
    sK2 != k13_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2 ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_lattice3)).

fof(f121,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f31,f118])).

fof(f31,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f116,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f29,f113])).

fof(f29,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f89,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f36,f86])).

fof(f36,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f84,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f35,f81])).

fof(f35,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f79,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f34,f76])).

fof(f34,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f74,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f33,f71])).

fof(f33,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f69,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f32,f66])).

fof(f32,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:32:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (6737)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.48  % (6733)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (6735)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (6729)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (6728)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (6729)Refutation not found, incomplete strategy% (6729)------------------------------
% 0.21/0.49  % (6729)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (6729)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (6729)Memory used [KB]: 10618
% 0.21/0.49  % (6729)Time elapsed: 0.070 s
% 0.21/0.49  % (6729)------------------------------
% 0.21/0.49  % (6729)------------------------------
% 0.21/0.50  % (6742)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (6738)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.50  % (6748)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (6743)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (6732)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (6736)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  % (6731)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (6741)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.51  % (6731)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f374,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f69,f74,f79,f84,f89,f116,f121,f127,f132,f171,f180,f359,f371])).
% 0.21/0.51  fof(f371,plain,(
% 0.21/0.51    ~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_6 | spl5_9 | ~spl5_10 | spl5_11 | ~spl5_14),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f370])).
% 0.21/0.51  fof(f370,plain,(
% 0.21/0.51    $false | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_6 | spl5_9 | ~spl5_10 | spl5_11 | ~spl5_14)),
% 0.21/0.51    inference(subsumption_resolution,[],[f369,f170])).
% 0.21/0.51  fof(f170,plain,(
% 0.21/0.51    sK2 != k10_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2) | spl5_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f168])).
% 0.21/0.51  fof(f168,plain,(
% 0.21/0.51    spl5_11 <=> sK2 = k10_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.51  fof(f369,plain,(
% 0.21/0.51    sK2 = k10_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_6 | spl5_9 | ~spl5_10 | ~spl5_14)),
% 0.21/0.51    inference(subsumption_resolution,[],[f368,f165])).
% 0.21/0.51  fof(f165,plain,(
% 0.21/0.51    m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~spl5_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f164])).
% 0.21/0.51  fof(f164,plain,(
% 0.21/0.51    spl5_10 <=> m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.51  fof(f368,plain,(
% 0.21/0.51    ~m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | sK2 = k10_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_6 | spl5_9 | ~spl5_14)),
% 0.21/0.51    inference(subsumption_resolution,[],[f366,f115])).
% 0.21/0.51  fof(f115,plain,(
% 0.21/0.51    m1_subset_1(sK2,u1_struct_0(sK0)) | ~spl5_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f113])).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    spl5_6 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.51  fof(f366,plain,(
% 0.21/0.51    ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | sK2 = k10_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_5 | spl5_9 | ~spl5_14)),
% 0.21/0.51    inference(resolution,[],[f358,f195])).
% 0.21/0.51  % (6744)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.51  fof(f195,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k10_lattice3(sK0,X0,X1) = X1) ) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_5 | spl5_9)),
% 0.21/0.51    inference(subsumption_resolution,[],[f194,f133])).
% 0.21/0.51  fof(f133,plain,(
% 0.21/0.51    ( ! [X4] : (r3_orders_2(sK0,X4,X4) | ~m1_subset_1(X4,u1_struct_0(sK0))) ) | (~spl5_1 | ~spl5_5 | spl5_9)),
% 0.21/0.51    inference(subsumption_resolution,[],[f111,f131])).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    ~v2_struct_0(sK0) | spl5_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f129])).
% 0.21/0.51  fof(f129,plain,(
% 0.21/0.51    spl5_9 <=> v2_struct_0(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    ( ! [X4] : (v2_struct_0(sK0) | ~m1_subset_1(X4,u1_struct_0(sK0)) | r3_orders_2(sK0,X4,X4)) ) | (~spl5_1 | ~spl5_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f108,f68])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    v3_orders_2(sK0) | ~spl5_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f66])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    spl5_1 <=> v3_orders_2(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    ( ! [X4] : (~v3_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X4,u1_struct_0(sK0)) | r3_orders_2(sK0,X4,X4)) ) | ~spl5_5),
% 0.21/0.51    inference(resolution,[],[f88,f64])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | r3_orders_2(X0,X1,X1)) )),
% 0.21/0.51    inference(condensation,[],[f52])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r3_orders_2(X0,X1,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => r3_orders_2(X0,X1,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    l1_orders_2(sK0) | ~spl5_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f86])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    spl5_5 <=> l1_orders_2(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.51  fof(f194,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k10_lattice3(sK0,X0,X1) = X1 | ~r3_orders_2(sK0,X1,X1)) ) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_5 | spl5_9)),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f193])).
% 0.21/0.51  fof(f193,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k10_lattice3(sK0,X0,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_orders_2(sK0,X1,X1)) ) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_5 | spl5_9)),
% 0.21/0.51    inference(resolution,[],[f191,f135])).
% 0.21/0.51  fof(f135,plain,(
% 0.21/0.51    ( ! [X2,X3] : (r1_orders_2(sK0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_orders_2(sK0,X2,X3)) ) | (~spl5_1 | ~spl5_5 | spl5_9)),
% 0.21/0.51    inference(subsumption_resolution,[],[f110,f131])).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    ( ! [X2,X3] : (v2_struct_0(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r1_orders_2(sK0,X2,X3) | ~r3_orders_2(sK0,X2,X3)) ) | (~spl5_1 | ~spl5_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f107,f68])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    ( ! [X2,X3] : (~v3_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r1_orders_2(sK0,X2,X3) | ~r3_orders_2(sK0,X2,X3)) ) | ~spl5_5),
% 0.21/0.51    inference(resolution,[],[f88,f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.21/0.51  fof(f191,plain,(
% 0.21/0.51    ( ! [X2,X3] : (~r1_orders_2(sK0,X2,X2) | ~r1_orders_2(sK0,X3,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | k10_lattice3(sK0,X3,X2) = X2) ) | (~spl5_2 | ~spl5_3 | ~spl5_5)),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f188])).
% 0.21/0.51  fof(f188,plain,(
% 0.21/0.51    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X3,X2) | ~r1_orders_2(sK0,X2,X2) | ~m1_subset_1(X3,u1_struct_0(sK0)) | k10_lattice3(sK0,X3,X2) = X2 | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X3,X2) | ~r1_orders_2(sK0,X2,X2) | ~m1_subset_1(X3,u1_struct_0(sK0)) | k10_lattice3(sK0,X3,X2) = X2) ) | (~spl5_2 | ~spl5_3 | ~spl5_5)),
% 0.21/0.51    inference(resolution,[],[f186,f182])).
% 0.21/0.51  fof(f182,plain,(
% 0.21/0.51    ( ! [X6,X7,X5] : (r1_orders_2(sK0,X6,sK4(sK0,X5,X6,X7)) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(X7,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X5,X7) | ~r1_orders_2(sK0,X6,X7) | ~m1_subset_1(X5,u1_struct_0(sK0)) | k10_lattice3(sK0,X5,X6) = X7) ) | (~spl5_2 | ~spl5_3 | ~spl5_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f181,f88])).
% 0.21/0.51  fof(f181,plain,(
% 0.21/0.51    ( ! [X6,X7,X5] : (~l1_orders_2(sK0) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(X7,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X5,X7) | ~r1_orders_2(sK0,X6,X7) | r1_orders_2(sK0,X6,sK4(sK0,X5,X6,X7)) | k10_lattice3(sK0,X5,X6) = X7) ) | (~spl5_2 | ~spl5_3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f95,f78])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    v1_lattice3(sK0) | ~spl5_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f76])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    spl5_3 <=> v1_lattice3(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    ( ! [X6,X7,X5] : (~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(X7,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X5,X7) | ~r1_orders_2(sK0,X6,X7) | r1_orders_2(sK0,X6,sK4(sK0,X5,X6,X7)) | k10_lattice3(sK0,X5,X6) = X7) ) | ~spl5_2),
% 0.21/0.51    inference(subsumption_resolution,[],[f92,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_lattice3(X0) | ~l1_orders_2(X0) | ~v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(flattening,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    ( ! [X6,X7,X5] : (v2_struct_0(sK0) | ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(X7,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X5,X7) | ~r1_orders_2(sK0,X6,X7) | r1_orders_2(sK0,X6,sK4(sK0,X5,X6,X7)) | k10_lattice3(sK0,X5,X6) = X7) ) | ~spl5_2),
% 0.21/0.51    inference(resolution,[],[f73,f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~v5_orders_2(X0) | v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X2,X3) | r1_orders_2(X0,X2,sK4(X0,X1,X2,X3)) | k10_lattice3(X0,X1,X2) = X3) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X3,X4) | (~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l26_lattice3)).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    v5_orders_2(sK0) | ~spl5_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f71])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    spl5_2 <=> v5_orders_2(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.51  fof(f186,plain,(
% 0.21/0.51    ( ! [X10,X8,X9] : (~r1_orders_2(sK0,X10,sK4(sK0,X8,X9,X10)) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X8,X10) | ~r1_orders_2(sK0,X9,X10) | ~m1_subset_1(X8,u1_struct_0(sK0)) | k10_lattice3(sK0,X8,X9) = X10) ) | (~spl5_2 | ~spl5_3 | ~spl5_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f185,f88])).
% 0.21/0.51  fof(f185,plain,(
% 0.21/0.51    ( ! [X10,X8,X9] : (~l1_orders_2(sK0) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X8,X10) | ~r1_orders_2(sK0,X9,X10) | ~r1_orders_2(sK0,X10,sK4(sK0,X8,X9,X10)) | k10_lattice3(sK0,X8,X9) = X10) ) | (~spl5_2 | ~spl5_3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f96,f78])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    ( ! [X10,X8,X9] : (~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X8,X10) | ~r1_orders_2(sK0,X9,X10) | ~r1_orders_2(sK0,X10,sK4(sK0,X8,X9,X10)) | k10_lattice3(sK0,X8,X9) = X10) ) | ~spl5_2),
% 0.21/0.51    inference(subsumption_resolution,[],[f93,f37])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    ( ! [X10,X8,X9] : (v2_struct_0(sK0) | ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X8,X10) | ~r1_orders_2(sK0,X9,X10) | ~r1_orders_2(sK0,X10,sK4(sK0,X8,X9,X10)) | k10_lattice3(sK0,X8,X9) = X10) ) | ~spl5_2),
% 0.21/0.51    inference(resolution,[],[f73,f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~v5_orders_2(X0) | v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X3,sK4(X0,X1,X2,X3)) | k10_lattice3(X0,X1,X2) = X3) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f358,plain,(
% 0.21/0.51    r1_orders_2(sK0,k12_lattice3(sK0,sK1,sK2),sK2) | ~spl5_14),
% 0.21/0.51    inference(avatar_component_clause,[],[f356])).
% 0.21/0.51  fof(f356,plain,(
% 0.21/0.51    spl5_14 <=> r1_orders_2(sK0,k12_lattice3(sK0,sK1,sK2),sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.51  fof(f359,plain,(
% 0.21/0.51    spl5_14 | ~spl5_2 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | spl5_9 | ~spl5_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f317,f164,f129,f118,f113,f86,f81,f71,f356])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    spl5_4 <=> v2_lattice3(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    spl5_7 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.51  fof(f317,plain,(
% 0.21/0.51    r1_orders_2(sK0,k12_lattice3(sK0,sK1,sK2),sK2) | (~spl5_2 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | spl5_9 | ~spl5_10)),
% 0.21/0.51    inference(subsumption_resolution,[],[f316,f115])).
% 0.21/0.51  fof(f316,plain,(
% 0.21/0.51    ~m1_subset_1(sK2,u1_struct_0(sK0)) | r1_orders_2(sK0,k12_lattice3(sK0,sK1,sK2),sK2) | (~spl5_2 | ~spl5_4 | ~spl5_5 | ~spl5_7 | spl5_9 | ~spl5_10)),
% 0.21/0.51    inference(subsumption_resolution,[],[f313,f120])).
% 0.21/0.51  fof(f120,plain,(
% 0.21/0.51    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl5_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f118])).
% 0.21/0.51  fof(f313,plain,(
% 0.21/0.51    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | r1_orders_2(sK0,k12_lattice3(sK0,sK1,sK2),sK2) | (~spl5_2 | ~spl5_4 | ~spl5_5 | spl5_9 | ~spl5_10)),
% 0.21/0.51    inference(resolution,[],[f156,f165])).
% 0.21/0.51  fof(f156,plain,(
% 0.21/0.51    ( ! [X6,X5] : (~m1_subset_1(k12_lattice3(sK0,X5,X6),u1_struct_0(sK0)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(X6,u1_struct_0(sK0)) | r1_orders_2(sK0,k12_lattice3(sK0,X5,X6),X6)) ) | (~spl5_2 | ~spl5_4 | ~spl5_5 | spl5_9)),
% 0.21/0.51    inference(subsumption_resolution,[],[f155,f131])).
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    ( ! [X6,X5] : (~m1_subset_1(k12_lattice3(sK0,X5,X6),u1_struct_0(sK0)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(X6,u1_struct_0(sK0)) | v2_struct_0(sK0) | r1_orders_2(sK0,k12_lattice3(sK0,X5,X6),X6)) ) | (~spl5_2 | ~spl5_4 | ~spl5_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f154,f88])).
% 0.21/0.51  fof(f154,plain,(
% 0.21/0.51    ( ! [X6,X5] : (~m1_subset_1(k12_lattice3(sK0,X5,X6),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(X6,u1_struct_0(sK0)) | v2_struct_0(sK0) | r1_orders_2(sK0,k12_lattice3(sK0,X5,X6),X6)) ) | (~spl5_2 | ~spl5_4 | ~spl5_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f153,f83])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    v2_lattice3(sK0) | ~spl5_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f81])).
% 0.21/0.51  fof(f153,plain,(
% 0.21/0.51    ( ! [X6,X5] : (~m1_subset_1(k12_lattice3(sK0,X5,X6),u1_struct_0(sK0)) | ~v2_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(X6,u1_struct_0(sK0)) | v2_struct_0(sK0) | r1_orders_2(sK0,k12_lattice3(sK0,X5,X6),X6)) ) | (~spl5_2 | ~spl5_4 | ~spl5_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f142,f73])).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    ( ! [X6,X5] : (~m1_subset_1(k12_lattice3(sK0,X5,X6),u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~v2_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(X6,u1_struct_0(sK0)) | v2_struct_0(sK0) | r1_orders_2(sK0,k12_lattice3(sK0,X5,X6),X6)) ) | (~spl5_2 | ~spl5_4 | ~spl5_5)),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f141])).
% 0.21/0.51  fof(f141,plain,(
% 0.21/0.51    ( ! [X6,X5] : (~m1_subset_1(k12_lattice3(sK0,X5,X6),u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~v2_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(X6,u1_struct_0(sK0)) | v2_struct_0(sK0) | r1_orders_2(sK0,k12_lattice3(sK0,X5,X6),X6) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(X5,u1_struct_0(sK0))) ) | (~spl5_2 | ~spl5_4 | ~spl5_5)),
% 0.21/0.51    inference(superposition,[],[f58,f138])).
% 0.21/0.51  fof(f138,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k12_lattice3(sK0,X0,X1) = k11_lattice3(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl5_2 | ~spl5_4 | ~spl5_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f102,f88])).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k12_lattice3(sK0,X0,X1) = k11_lattice3(sK0,X0,X1)) ) | (~spl5_2 | ~spl5_4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f98,f73])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k12_lattice3(sK0,X0,X1) = k11_lattice3(sK0,X0,X1)) ) | ~spl5_4),
% 0.21/0.51    inference(resolution,[],[f83,f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v2_lattice3(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.21/0.51    inference(flattening,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~v5_orders_2(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0) | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)) )),
% 0.21/0.51    inference(equality_resolution,[],[f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v5_orders_2(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | r1_orders_2(X0,X3,X2) | k11_lattice3(X0,X1,X2) != X3) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  % (6739)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.51  % (6734)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.51  % (6747)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.51  % (6746)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.52  % (6730)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.52  % (6748)Refutation not found, incomplete strategy% (6748)------------------------------
% 0.21/0.52  % (6748)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (6748)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (6748)Memory used [KB]: 10618
% 0.21/0.52  % (6748)Time elapsed: 0.106 s
% 0.21/0.52  % (6748)------------------------------
% 0.21/0.52  % (6748)------------------------------
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l28_lattice3)).
% 0.21/0.52  fof(f180,plain,(
% 0.21/0.52    ~spl5_2 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | spl5_10),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f179])).
% 0.21/0.52  fof(f179,plain,(
% 0.21/0.52    $false | (~spl5_2 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | spl5_10)),
% 0.21/0.52    inference(subsumption_resolution,[],[f178,f73])).
% 0.21/0.52  fof(f178,plain,(
% 0.21/0.52    ~v5_orders_2(sK0) | (~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | spl5_10)),
% 0.21/0.52    inference(subsumption_resolution,[],[f177,f115])).
% 0.21/0.52  fof(f177,plain,(
% 0.21/0.52    ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | (~spl5_4 | ~spl5_5 | ~spl5_7 | spl5_10)),
% 0.21/0.52    inference(subsumption_resolution,[],[f176,f120])).
% 0.21/0.52  fof(f176,plain,(
% 0.21/0.52    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | (~spl5_4 | ~spl5_5 | spl5_10)),
% 0.21/0.52    inference(subsumption_resolution,[],[f175,f88])).
% 0.21/0.52  fof(f175,plain,(
% 0.21/0.52    ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | (~spl5_4 | spl5_10)),
% 0.21/0.52    inference(subsumption_resolution,[],[f174,f83])).
% 0.21/0.52  fof(f174,plain,(
% 0.21/0.52    ~v2_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | spl5_10),
% 0.21/0.52    inference(resolution,[],[f166,f55])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v5_orders_2(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.21/0.52    inference(flattening,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k12_lattice3)).
% 0.21/0.52  fof(f166,plain,(
% 0.21/0.52    ~m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | spl5_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f164])).
% 0.21/0.52  fof(f171,plain,(
% 0.21/0.52    ~spl5_10 | ~spl5_11 | ~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_6 | spl5_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f160,f124,f113,f86,f76,f71,f168,f164])).
% 0.21/0.52  fof(f124,plain,(
% 0.21/0.52    spl5_8 <=> sK2 = k13_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.52  fof(f160,plain,(
% 0.21/0.52    sK2 != k10_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2) | ~m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | (~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_6 | spl5_8)),
% 0.21/0.52    inference(subsumption_resolution,[],[f159,f115])).
% 0.21/0.52  fof(f159,plain,(
% 0.21/0.52    sK2 != k10_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | (~spl5_2 | ~spl5_3 | ~spl5_5 | spl5_8)),
% 0.21/0.52    inference(superposition,[],[f126,f158])).
% 0.21/0.52  fof(f158,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k10_lattice3(sK0,X0,X1) = k13_lattice3(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl5_2 | ~spl5_3 | ~spl5_5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f157,f88])).
% 0.21/0.52  fof(f157,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k10_lattice3(sK0,X0,X1) = k13_lattice3(sK0,X0,X1)) ) | (~spl5_2 | ~spl5_3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f90,f78])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k10_lattice3(sK0,X0,X1) = k13_lattice3(sK0,X0,X1)) ) | ~spl5_2),
% 0.21/0.52    inference(resolution,[],[f73,f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v5_orders_2(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 0.21/0.52    inference(flattening,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k13_lattice3)).
% 0.21/0.52  fof(f126,plain,(
% 0.21/0.52    sK2 != k13_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2) | spl5_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f124])).
% 0.21/0.52  fof(f132,plain,(
% 0.21/0.52    ~spl5_9 | ~spl5_3 | ~spl5_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f122,f86,f76,f129])).
% 0.21/0.52  fof(f122,plain,(
% 0.21/0.52    ~v2_struct_0(sK0) | (~spl5_3 | ~spl5_5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f97,f88])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    ~l1_orders_2(sK0) | ~v2_struct_0(sK0) | ~spl5_3),
% 0.21/0.52    inference(resolution,[],[f78,f37])).
% 0.21/0.52  fof(f127,plain,(
% 0.21/0.52    ~spl5_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f30,f124])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    sK2 != k13_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0))),
% 0.21/0.52    inference(flattening,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,negated_conjecture,(
% 0.21/0.52    ~! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2)))),
% 0.21/0.52    inference(negated_conjecture,[],[f9])).
% 0.21/0.52  fof(f9,conjecture,(
% 0.21/0.52    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_lattice3)).
% 0.21/0.52  fof(f121,plain,(
% 0.21/0.52    spl5_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f31,f118])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f116,plain,(
% 0.21/0.52    spl5_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f29,f113])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    spl5_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f36,f86])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    l1_orders_2(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    spl5_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f35,f81])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    v2_lattice3(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    spl5_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f34,f76])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    v1_lattice3(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    spl5_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f33,f71])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    v5_orders_2(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    spl5_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f32,f66])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    v3_orders_2(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (6731)------------------------------
% 0.21/0.52  % (6731)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (6731)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (6731)Memory used [KB]: 10746
% 0.21/0.52  % (6731)Time elapsed: 0.089 s
% 0.21/0.52  % (6731)------------------------------
% 0.21/0.52  % (6731)------------------------------
% 0.21/0.52  % (6727)Success in time 0.156 s
%------------------------------------------------------------------------------
