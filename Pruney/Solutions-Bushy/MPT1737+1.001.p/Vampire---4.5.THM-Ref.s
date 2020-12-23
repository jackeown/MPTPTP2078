%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1737+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:27 EST 2020

% Result     : Theorem 4.16s
% Output     : Refutation 4.16s
% Verified   : 
% Statistics : Number of formulae       :  207 ( 489 expanded)
%              Number of leaves         :   56 ( 261 expanded)
%              Depth                    :   11
%              Number of atoms          : 1158 (3769 expanded)
%              Number of equality atoms :   36 (  46 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2747,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f101,f105,f109,f113,f117,f121,f125,f129,f133,f137,f141,f145,f167,f186,f205,f328,f330,f544,f640,f821,f846,f874,f894,f913,f1262,f1295,f1299,f2434,f2438,f2472,f2473,f2474,f2481,f2487,f2489,f2529,f2549,f2746])).

fof(f2746,plain,
    ( ~ spl4_12
    | ~ spl4_7
    | ~ spl4_15
    | spl4_16
    | ~ spl4_14
    | ~ spl4_379 ),
    inference(avatar_split_clause,[],[f2744,f2547,f135,f143,f139,f107,f127])).

fof(f127,plain,
    ( spl4_12
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f107,plain,
    ( spl4_7
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f139,plain,
    ( spl4_15
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f143,plain,
    ( spl4_16
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f135,plain,
    ( spl4_14
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f2547,plain,
    ( spl4_379
  <=> ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_379])])).

fof(f2744,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl4_14
    | ~ spl4_379 ),
    inference(resolution,[],[f2548,f136])).

fof(f136,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f135])).

fof(f2548,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_pre_topc(sK3,X0)
        | ~ m1_pre_topc(sK1,X0) )
    | ~ spl4_379 ),
    inference(avatar_component_clause,[],[f2547])).

fof(f2549,plain,
    ( spl4_13
    | spl4_9
    | spl4_379
    | ~ spl4_6
    | ~ spl4_377 ),
    inference(avatar_split_clause,[],[f2534,f2527,f103,f2547,f115,f131])).

fof(f131,plain,
    ( spl4_13
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f115,plain,
    ( spl4_9
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f103,plain,
    ( spl4_6
  <=> m1_pre_topc(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f2527,plain,
    ( spl4_377
  <=> r1_tsep_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_377])])).

fof(f2534,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK1,sK3)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl4_377 ),
    inference(resolution,[],[f2528,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ~ r1_tsep_1(X2,X1)
                & ~ r1_tsep_1(X1,X2) )
              | ~ m1_pre_topc(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ~ r1_tsep_1(X2,X1)
                & ~ r1_tsep_1(X1,X2) )
              | ~ m1_pre_topc(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( m1_pre_topc(X1,X2)
               => ( ~ r1_tsep_1(X2,X1)
                  & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tmap_1)).

fof(f2528,plain,
    ( r1_tsep_1(sK1,sK3)
    | ~ spl4_377 ),
    inference(avatar_component_clause,[],[f2527])).

fof(f2529,plain,
    ( spl4_377
    | ~ spl4_12
    | ~ spl4_2
    | spl4_13
    | ~ spl4_134 ),
    inference(avatar_split_clause,[],[f2523,f911,f131,f89,f127,f2527])).

fof(f89,plain,
    ( spl4_2
  <=> m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f911,plain,
    ( spl4_134
  <=> ! [X6] :
        ( r1_tsep_1(X6,sK3)
        | ~ m1_pre_topc(X6,k1_tsep_1(sK0,sK1,sK2))
        | ~ m1_pre_topc(X6,sK0)
        | v2_struct_0(X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_134])])).

fof(f2523,plain,
    ( ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK1,sK0)
    | r1_tsep_1(sK1,sK3)
    | spl4_13
    | ~ spl4_134 ),
    inference(resolution,[],[f912,f132])).

fof(f132,plain,
    ( ~ v2_struct_0(sK1)
    | spl4_13 ),
    inference(avatar_component_clause,[],[f131])).

fof(f912,plain,
    ( ! [X6] :
        ( v2_struct_0(X6)
        | ~ m1_pre_topc(X6,k1_tsep_1(sK0,sK1,sK2))
        | ~ m1_pre_topc(X6,sK0)
        | r1_tsep_1(X6,sK3) )
    | ~ spl4_134 ),
    inference(avatar_component_clause,[],[f911])).

fof(f2489,plain,
    ( ~ spl4_14
    | ~ spl4_12
    | spl4_370 ),
    inference(avatar_split_clause,[],[f2488,f2485,f127,f135])).

fof(f2485,plain,
    ( spl4_370
  <=> m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_370])])).

fof(f2488,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | spl4_370 ),
    inference(resolution,[],[f2486,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) ) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

fof(f2486,plain,
    ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0)
    | spl4_370 ),
    inference(avatar_component_clause,[],[f2485])).

fof(f2487,plain,
    ( ~ spl4_370
    | ~ spl4_15
    | ~ spl4_14
    | ~ spl4_362 ),
    inference(avatar_split_clause,[],[f2482,f2424,f135,f139,f2485])).

fof(f2424,plain,
    ( spl4_362
  <=> ! [X1] :
        ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_362])])).

fof(f2482,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0)
    | ~ spl4_14
    | ~ spl4_362 ),
    inference(resolution,[],[f2425,f136])).

fof(f2425,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1) )
    | ~ spl4_362 ),
    inference(avatar_component_clause,[],[f2424])).

fof(f2481,plain,
    ( ~ spl4_12
    | ~ spl4_14
    | ~ spl4_363 ),
    inference(avatar_split_clause,[],[f2479,f2427,f135,f127])).

fof(f2427,plain,
    ( spl4_363
  <=> ! [X0] :
        ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_363])])).

fof(f2479,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ spl4_14
    | ~ spl4_363 ),
    inference(resolution,[],[f2478,f136])).

fof(f2478,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK1,X0) )
    | ~ spl4_363 ),
    inference(duplicate_literal_removal,[],[f2476])).

fof(f2476,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl4_363 ),
    inference(resolution,[],[f2428,f59])).

fof(f2428,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl4_363 ),
    inference(avatar_component_clause,[],[f2427])).

fof(f2474,plain,
    ( k1_tsep_1(sK0,sK2,sK1) != k1_tsep_1(sK0,sK1,sK2)
    | v1_tsep_1(sK1,k1_tsep_1(sK0,sK2,sK1))
    | ~ v1_tsep_1(sK1,k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2473,plain,
    ( k1_tsep_1(sK0,sK2,sK1) != k1_tsep_1(sK0,sK1,sK2)
    | m1_pre_topc(sK1,k1_tsep_1(sK0,sK2,sK1))
    | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2472,plain,
    ( ~ spl4_194
    | ~ spl4_2
    | spl4_130 ),
    inference(avatar_split_clause,[],[f2471,f888,f89,f1274])).

fof(f1274,plain,
    ( spl4_194
  <=> l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_194])])).

fof(f888,plain,
    ( spl4_130
  <=> m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_130])])).

fof(f2471,plain,
    ( ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2))
    | ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | spl4_130 ),
    inference(resolution,[],[f2432,f59])).

fof(f2432,plain,
    ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),k1_tsep_1(sK0,sK1,sK2))
    | spl4_130 ),
    inference(avatar_component_clause,[],[f888])).

fof(f2438,plain,
    ( ~ spl4_15
    | ~ spl4_12
    | ~ spl4_14
    | spl4_364 ),
    inference(avatar_split_clause,[],[f2436,f2430,f135,f127,f139])).

fof(f2430,plain,
    ( spl4_364
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_364])])).

fof(f2436,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_14
    | spl4_364 ),
    inference(resolution,[],[f2435,f136])).

fof(f2435,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK1,X0)
        | ~ v2_pre_topc(X0) )
    | spl4_364 ),
    inference(resolution,[],[f2431,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f2431,plain,
    ( ~ v2_pre_topc(sK1)
    | spl4_364 ),
    inference(avatar_component_clause,[],[f2430])).

fof(f2434,plain,
    ( spl4_362
    | spl4_363
    | ~ spl4_193
    | ~ spl4_194
    | ~ spl4_364
    | ~ spl4_92
    | ~ spl4_130
    | ~ spl4_131
    | spl4_1 ),
    inference(avatar_split_clause,[],[f2422,f86,f892,f888,f623,f2430,f1274,f1271,f2427,f2424])).

fof(f1271,plain,
    ( spl4_193
  <=> v2_pre_topc(k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_193])])).

fof(f623,plain,
    ( spl4_92
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_92])])).

fof(f892,plain,
    ( spl4_131
  <=> v1_tsep_1(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_131])])).

fof(f86,plain,
    ( spl4_1
  <=> v1_tsep_1(sK1,k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f2422,plain,
    ( ! [X0,X1] :
        ( ~ v1_tsep_1(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),k1_tsep_1(sK0,sK1,sK2))
        | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),k1_tsep_1(sK0,sK1,sK2))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
        | ~ v2_pre_topc(k1_tsep_1(sK0,sK1,sK2))
        | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1) )
    | spl4_1 ),
    inference(resolution,[],[f1435,f87])).

fof(f87,plain,
    ( ~ v1_tsep_1(sK1,k1_tsep_1(sK0,sK1,sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f1435,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_tsep_1(X0,X1)
      | ~ v1_tsep_1(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2)
      | ~ l1_pre_topc(X2)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X3)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3) ) ),
    inference(resolution,[],[f785,f73])).

fof(f785,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ v1_tsep_1(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | v1_tsep_1(X0,X1)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2)
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f82,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ v1_tsep_1(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | v1_tsep_1(X1,X0)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_tsep_1(X2,X0)
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ m1_pre_topc(X2,X0)
                  | ~ v1_tsep_1(X2,X0) )
                & ( ( m1_pre_topc(X2,X0)
                    & v1_tsep_1(X2,X0) )
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ m1_pre_topc(X2,X0)
                  | ~ v1_tsep_1(X2,X0) )
                & ( ( m1_pre_topc(X2,X0)
                    & v1_tsep_1(X2,X0) )
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0) ) )
              | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0) ) )
              | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> ( m1_pre_topc(X2,X0)
                    & v1_tsep_1(X2,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_tmap_1)).

fof(f1299,plain,
    ( ~ spl4_42
    | ~ spl4_14
    | spl4_194 ),
    inference(avatar_split_clause,[],[f1297,f1274,f135,f321])).

fof(f321,plain,
    ( spl4_42
  <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f1297,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | ~ spl4_14
    | spl4_194 ),
    inference(resolution,[],[f1296,f136])).

fof(f1296,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),X0) )
    | spl4_194 ),
    inference(resolution,[],[f1275,f58])).

fof(f1275,plain,
    ( ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | spl4_194 ),
    inference(avatar_component_clause,[],[f1274])).

fof(f1295,plain,
    ( ~ spl4_15
    | ~ spl4_42
    | ~ spl4_14
    | spl4_193 ),
    inference(avatar_split_clause,[],[f1293,f1271,f135,f321,f139])).

fof(f1293,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_14
    | spl4_193 ),
    inference(resolution,[],[f1292,f136])).

fof(f1292,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),X0)
        | ~ v2_pre_topc(X0) )
    | spl4_193 ),
    inference(resolution,[],[f1272,f73])).

fof(f1272,plain,
    ( ~ v2_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | spl4_193 ),
    inference(avatar_component_clause,[],[f1271])).

fof(f1262,plain,
    ( spl4_16
    | ~ spl4_15
    | ~ spl4_14
    | spl4_13
    | ~ spl4_12
    | spl4_11
    | ~ spl4_10
    | spl4_2 ),
    inference(avatar_split_clause,[],[f1261,f89,f119,f123,f127,f131,f135,f139,f143])).

fof(f123,plain,
    ( spl4_11
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f119,plain,
    ( spl4_10
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f1261,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_2 ),
    inference(resolution,[],[f90,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tsep_1)).

fof(f90,plain,
    ( ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f913,plain,
    ( ~ spl4_7
    | spl4_9
    | ~ spl4_42
    | spl4_41
    | spl4_134
    | ~ spl4_77
    | ~ spl4_129 ),
    inference(avatar_split_clause,[],[f899,f885,f542,f911,f318,f321,f115,f107])).

fof(f318,plain,
    ( spl4_41
  <=> v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f542,plain,
    ( spl4_77
  <=> ! [X1,X0,X2] :
        ( r1_tsep_1(X0,X1)
        | ~ r1_tsep_1(X1,X2)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_77])])).

fof(f885,plain,
    ( spl4_129
  <=> r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_129])])).

fof(f899,plain,
    ( ! [X6] :
        ( r1_tsep_1(X6,sK3)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,sK0)
        | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ m1_pre_topc(X6,k1_tsep_1(sK0,sK1,sK2)) )
    | ~ spl4_77
    | ~ spl4_129 ),
    inference(resolution,[],[f886,f543])).

fof(f543,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tsep_1(X1,X2)
        | r1_tsep_1(X0,X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,X2) )
    | ~ spl4_77 ),
    inference(avatar_component_clause,[],[f542])).

fof(f886,plain,
    ( r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | ~ spl4_129 ),
    inference(avatar_component_clause,[],[f885])).

fof(f894,plain,
    ( spl4_16
    | ~ spl4_15
    | ~ spl4_14
    | spl4_41
    | ~ spl4_42
    | spl4_9
    | ~ spl4_8
    | ~ spl4_7
    | spl4_129
    | spl4_131
    | ~ spl4_127 ),
    inference(avatar_split_clause,[],[f882,f872,f892,f885,f107,f111,f115,f321,f318,f135,f139,f143])).

fof(f111,plain,
    ( spl4_8
  <=> v1_tsep_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f872,plain,
    ( spl4_127
  <=> g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k2_tsep_1(sK0,sK3,k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_127])])).

fof(f882,plain,
    ( v1_tsep_1(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),k1_tsep_1(sK0,sK1,sK2))
    | r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_tsep_1(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_127 ),
    inference(superposition,[],[f60,f873])).

fof(f873,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k2_tsep_1(sK0,sK3,k1_tsep_1(sK0,sK1,sK2))
    | ~ spl4_127 ),
    inference(avatar_component_clause,[],[f872])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(k2_tsep_1(X0,X2,X1),X1)
      | r1_tsep_1(X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_tsep_1(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(k2_tsep_1(X0,X2,X1),X1)
                & v1_tsep_1(k2_tsep_1(X0,X2,X1),X1) )
              | r1_tsep_1(X2,X1)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_tsep_1(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(k2_tsep_1(X0,X2,X1),X1)
                & v1_tsep_1(k2_tsep_1(X0,X2,X1),X1) )
              | r1_tsep_1(X2,X1)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_tsep_1(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
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
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_tsep_1(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ~ r1_tsep_1(X2,X1)
               => ( m1_pre_topc(k2_tsep_1(X0,X2,X1),X1)
                  & v1_tsep_1(k2_tsep_1(X0,X2,X1),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tmap_1)).

fof(f874,plain,
    ( spl4_13
    | ~ spl4_12
    | spl4_127
    | ~ spl4_6
    | ~ spl4_121 ),
    inference(avatar_split_clause,[],[f858,f844,f103,f872,f127,f131])).

fof(f844,plain,
    ( spl4_121
  <=> ! [X0] :
        ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(sK0,sK3,k1_tsep_1(sK0,X0,sK2))
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_121])])).

fof(f858,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k2_tsep_1(sK0,sK3,k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ spl4_6
    | ~ spl4_121 ),
    inference(resolution,[],[f845,f104])).

fof(f104,plain,
    ( m1_pre_topc(sK1,sK3)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f103])).

fof(f845,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(sK0,sK3,k1_tsep_1(sK0,X0,sK2))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0) )
    | ~ spl4_121 ),
    inference(avatar_component_clause,[],[f844])).

fof(f846,plain,
    ( ~ spl4_10
    | spl4_11
    | ~ spl4_7
    | spl4_9
    | spl4_121
    | ~ spl4_5
    | ~ spl4_120 ),
    inference(avatar_split_clause,[],[f838,f819,f99,f844,f115,f107,f123,f119])).

fof(f99,plain,
    ( spl4_5
  <=> r1_tsep_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f819,plain,
    ( spl4_120
  <=> ! [X1,X0,X2] :
        ( ~ r1_tsep_1(X0,X1)
        | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k2_tsep_1(sK0,X0,k1_tsep_1(sK0,X2,X1))
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_120])])).

fof(f838,plain,
    ( ! [X0] :
        ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(sK0,sK3,k1_tsep_1(sK0,X0,sK2))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,sK0)
        | ~ m1_pre_topc(X0,sK3) )
    | ~ spl4_5
    | ~ spl4_120 ),
    inference(resolution,[],[f820,f100])).

fof(f100,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f99])).

fof(f820,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tsep_1(X0,X1)
        | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k2_tsep_1(sK0,X0,k1_tsep_1(sK0,X2,X1))
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X2,X0) )
    | ~ spl4_120 ),
    inference(avatar_component_clause,[],[f819])).

fof(f821,plain,
    ( spl4_16
    | ~ spl4_15
    | spl4_120
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f816,f135,f819,f139,f143])).

fof(f816,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tsep_1(X0,X1)
        | ~ m1_pre_topc(X2,X0)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k2_tsep_1(sK0,X0,k1_tsep_1(sK0,X2,X1))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_14 ),
    inference(resolution,[],[f65,f136])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tsep_1(X2,X3)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3))
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1))
                    & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) )
                  | ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1))
                    & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) )
                  | ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
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
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( m1_pre_topc(X1,X2)
                   => ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1))
                        & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) )
                      | ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tmap_1)).

fof(f640,plain,
    ( ~ spl4_12
    | ~ spl4_14
    | spl4_92 ),
    inference(avatar_split_clause,[],[f638,f623,f135,f127])).

fof(f638,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ spl4_14
    | spl4_92 ),
    inference(resolution,[],[f637,f136])).

fof(f637,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK1,X0) )
    | spl4_92 ),
    inference(resolution,[],[f624,f58])).

fof(f624,plain,
    ( ~ l1_pre_topc(sK1)
    | spl4_92 ),
    inference(avatar_component_clause,[],[f623])).

fof(f544,plain,
    ( spl4_16
    | ~ spl4_15
    | spl4_77
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f539,f135,f542,f139,f143])).

fof(f539,plain,
    ( ! [X2,X0,X1] :
        ( r1_tsep_1(X0,X1)
        | ~ m1_pre_topc(X0,X2)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ r1_tsep_1(X1,X2)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_14 ),
    inference(resolution,[],[f71,f136])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | r1_tsep_1(X1,X3)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ r1_tsep_1(X3,X2)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
                  | ( r1_tsep_1(X3,X1)
                    & r1_tsep_1(X1,X3) )
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
                  | ( r1_tsep_1(X3,X1)
                    & r1_tsep_1(X1,X3) )
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( m1_pre_topc(X1,X2)
                   => ( ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) )
                      | ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tmap_1)).

fof(f330,plain,
    ( spl4_16
    | ~ spl4_14
    | spl4_13
    | ~ spl4_12
    | spl4_11
    | ~ spl4_10
    | ~ spl4_41 ),
    inference(avatar_split_clause,[],[f329,f318,f119,f123,f127,f131,f135,f143])).

fof(f329,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_41 ),
    inference(resolution,[],[f319,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(f319,plain,
    ( v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f318])).

fof(f328,plain,
    ( spl4_16
    | ~ spl4_14
    | spl4_13
    | ~ spl4_12
    | spl4_11
    | ~ spl4_10
    | spl4_42 ),
    inference(avatar_split_clause,[],[f327,f321,f119,f123,f127,f131,f135,f143])).

fof(f327,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_42 ),
    inference(resolution,[],[f322,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f322,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | spl4_42 ),
    inference(avatar_component_clause,[],[f321])).

fof(f205,plain,
    ( ~ spl4_10
    | spl4_26
    | spl4_11
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f200,f184,f123,f203,f119])).

fof(f203,plain,
    ( spl4_26
  <=> k1_tsep_1(sK0,sK2,sK1) = k1_tsep_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f184,plain,
    ( spl4_23
  <=> ! [X5] :
        ( k1_tsep_1(sK0,X5,sK1) = k1_tsep_1(sK0,sK1,X5)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f200,plain,
    ( k1_tsep_1(sK0,sK2,sK1) = k1_tsep_1(sK0,sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | spl4_11
    | ~ spl4_23 ),
    inference(resolution,[],[f185,f124])).

fof(f124,plain,
    ( ~ v2_struct_0(sK2)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f123])).

fof(f185,plain,
    ( ! [X5] :
        ( v2_struct_0(X5)
        | k1_tsep_1(sK0,X5,sK1) = k1_tsep_1(sK0,sK1,X5)
        | ~ m1_pre_topc(X5,sK0) )
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f184])).

fof(f186,plain,
    ( ~ spl4_12
    | spl4_23
    | spl4_13
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f170,f165,f131,f184,f127])).

fof(f165,plain,
    ( spl4_20
  <=> ! [X1,X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k1_tsep_1(sK0,X1,X0) = k1_tsep_1(sK0,X0,X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f170,plain,
    ( ! [X5] :
        ( k1_tsep_1(sK0,X5,sK1) = k1_tsep_1(sK0,sK1,X5)
        | ~ m1_pre_topc(X5,sK0)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(sK1,sK0) )
    | spl4_13
    | ~ spl4_20 ),
    inference(resolution,[],[f166,f132])).

fof(f166,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | k1_tsep_1(sK0,X1,X0) = k1_tsep_1(sK0,X0,X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f165])).

fof(f167,plain,
    ( spl4_16
    | spl4_20
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f161,f135,f165,f143])).

fof(f161,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | k1_tsep_1(sK0,X1,X0) = k1_tsep_1(sK0,X0,X1)
        | v2_struct_0(sK0) )
    | ~ spl4_14 ),
    inference(resolution,[],[f78,f136])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k1_tsep_1)).

fof(f145,plain,(
    ~ spl4_16 ),
    inference(avatar_split_clause,[],[f45,f143])).

fof(f45,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ( ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK2,sK1))
      | ~ v1_tsep_1(sK1,k1_tsep_1(sK0,sK2,sK1))
      | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2))
      | ~ v1_tsep_1(sK1,k1_tsep_1(sK0,sK1,sK2)) )
    & r1_tsep_1(sK3,sK2)
    & m1_pre_topc(sK1,sK3)
    & m1_pre_topc(sK3,sK0)
    & v1_tsep_1(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f41,f40,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ m1_pre_topc(X1,k1_tsep_1(X0,X2,X1))
                      | ~ v1_tsep_1(X1,k1_tsep_1(X0,X2,X1))
                      | ~ m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
                      | ~ v1_tsep_1(X1,k1_tsep_1(X0,X1,X2)) )
                    & r1_tsep_1(X3,X2)
                    & m1_pre_topc(X1,X3)
                    & m1_pre_topc(X3,X0)
                    & v1_tsep_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_pre_topc(X1,k1_tsep_1(sK0,X2,X1))
                    | ~ v1_tsep_1(X1,k1_tsep_1(sK0,X2,X1))
                    | ~ m1_pre_topc(X1,k1_tsep_1(sK0,X1,X2))
                    | ~ v1_tsep_1(X1,k1_tsep_1(sK0,X1,X2)) )
                  & r1_tsep_1(X3,X2)
                  & m1_pre_topc(X1,X3)
                  & m1_pre_topc(X3,sK0)
                  & v1_tsep_1(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ m1_pre_topc(X1,k1_tsep_1(sK0,X2,X1))
                  | ~ v1_tsep_1(X1,k1_tsep_1(sK0,X2,X1))
                  | ~ m1_pre_topc(X1,k1_tsep_1(sK0,X1,X2))
                  | ~ v1_tsep_1(X1,k1_tsep_1(sK0,X1,X2)) )
                & r1_tsep_1(X3,X2)
                & m1_pre_topc(X1,X3)
                & m1_pre_topc(X3,sK0)
                & v1_tsep_1(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ m1_pre_topc(sK1,k1_tsep_1(sK0,X2,sK1))
                | ~ v1_tsep_1(sK1,k1_tsep_1(sK0,X2,sK1))
                | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,X2))
                | ~ v1_tsep_1(sK1,k1_tsep_1(sK0,sK1,X2)) )
              & r1_tsep_1(X3,X2)
              & m1_pre_topc(sK1,X3)
              & m1_pre_topc(X3,sK0)
              & v1_tsep_1(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ m1_pre_topc(sK1,k1_tsep_1(sK0,X2,sK1))
              | ~ v1_tsep_1(sK1,k1_tsep_1(sK0,X2,sK1))
              | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,X2))
              | ~ v1_tsep_1(sK1,k1_tsep_1(sK0,sK1,X2)) )
            & r1_tsep_1(X3,X2)
            & m1_pre_topc(sK1,X3)
            & m1_pre_topc(X3,sK0)
            & v1_tsep_1(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ( ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK2,sK1))
            | ~ v1_tsep_1(sK1,k1_tsep_1(sK0,sK2,sK1))
            | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2))
            | ~ v1_tsep_1(sK1,k1_tsep_1(sK0,sK1,sK2)) )
          & r1_tsep_1(X3,sK2)
          & m1_pre_topc(sK1,X3)
          & m1_pre_topc(X3,sK0)
          & v1_tsep_1(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X3] :
        ( ( ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK2,sK1))
          | ~ v1_tsep_1(sK1,k1_tsep_1(sK0,sK2,sK1))
          | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2))
          | ~ v1_tsep_1(sK1,k1_tsep_1(sK0,sK1,sK2)) )
        & r1_tsep_1(X3,sK2)
        & m1_pre_topc(sK1,X3)
        & m1_pre_topc(X3,sK0)
        & v1_tsep_1(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ( ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK2,sK1))
        | ~ v1_tsep_1(sK1,k1_tsep_1(sK0,sK2,sK1))
        | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2))
        | ~ v1_tsep_1(sK1,k1_tsep_1(sK0,sK1,sK2)) )
      & r1_tsep_1(sK3,sK2)
      & m1_pre_topc(sK1,sK3)
      & m1_pre_topc(sK3,sK0)
      & v1_tsep_1(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_pre_topc(X1,k1_tsep_1(X0,X2,X1))
                    | ~ v1_tsep_1(X1,k1_tsep_1(X0,X2,X1))
                    | ~ m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
                    | ~ v1_tsep_1(X1,k1_tsep_1(X0,X1,X2)) )
                  & r1_tsep_1(X3,X2)
                  & m1_pre_topc(X1,X3)
                  & m1_pre_topc(X3,X0)
                  & v1_tsep_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_pre_topc(X1,k1_tsep_1(X0,X2,X1))
                    | ~ v1_tsep_1(X1,k1_tsep_1(X0,X2,X1))
                    | ~ m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
                    | ~ v1_tsep_1(X1,k1_tsep_1(X0,X1,X2)) )
                  & r1_tsep_1(X3,X2)
                  & m1_pre_topc(X1,X3)
                  & m1_pre_topc(X3,X0)
                  & v1_tsep_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_tsep_1(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( ( r1_tsep_1(X3,X2)
                        & m1_pre_topc(X1,X3) )
                     => ( m1_pre_topc(X1,k1_tsep_1(X0,X2,X1))
                        & v1_tsep_1(X1,k1_tsep_1(X0,X2,X1))
                        & m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
                        & v1_tsep_1(X1,k1_tsep_1(X0,X1,X2)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_tsep_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ( r1_tsep_1(X3,X2)
                      & m1_pre_topc(X1,X3) )
                   => ( m1_pre_topc(X1,k1_tsep_1(X0,X2,X1))
                      & v1_tsep_1(X1,k1_tsep_1(X0,X2,X1))
                      & m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
                      & v1_tsep_1(X1,k1_tsep_1(X0,X1,X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tmap_1)).

fof(f141,plain,(
    spl4_15 ),
    inference(avatar_split_clause,[],[f46,f139])).

fof(f46,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f137,plain,(
    spl4_14 ),
    inference(avatar_split_clause,[],[f47,f135])).

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f133,plain,(
    ~ spl4_13 ),
    inference(avatar_split_clause,[],[f48,f131])).

fof(f48,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f129,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f49,f127])).

fof(f49,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f125,plain,(
    ~ spl4_11 ),
    inference(avatar_split_clause,[],[f50,f123])).

fof(f50,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f121,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f51,f119])).

fof(f51,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f117,plain,(
    ~ spl4_9 ),
    inference(avatar_split_clause,[],[f52,f115])).

fof(f52,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f113,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f53,f111])).

fof(f53,plain,(
    v1_tsep_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f109,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f54,f107])).

fof(f54,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f105,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f55,f103])).

fof(f55,plain,(
    m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f101,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f56,f99])).

fof(f56,plain,(
    r1_tsep_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f97,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f57,f95,f92,f89,f86])).

fof(f92,plain,
    ( spl4_3
  <=> v1_tsep_1(sK1,k1_tsep_1(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f95,plain,
    ( spl4_4
  <=> m1_pre_topc(sK1,k1_tsep_1(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f57,plain,
    ( ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK2,sK1))
    | ~ v1_tsep_1(sK1,k1_tsep_1(sK0,sK2,sK1))
    | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_tsep_1(sK1,k1_tsep_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f42])).

%------------------------------------------------------------------------------
