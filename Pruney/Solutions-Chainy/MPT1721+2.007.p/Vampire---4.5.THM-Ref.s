%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:06 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 238 expanded)
%              Number of leaves         :   25 ( 115 expanded)
%              Depth                    :   11
%              Number of atoms          :  534 (2138 expanded)
%              Number of equality atoms :   22 (  26 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f142,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f52,f60,f64,f72,f76,f80,f84,f88,f92,f96,f106,f115,f129,f131,f137,f141])).

fof(f141,plain,
    ( ~ spl4_4
    | ~ spl4_5
    | spl4_1
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f138,f135,f46,f62,f58])).

fof(f58,plain,
    ( spl4_4
  <=> m1_pre_topc(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f62,plain,
    ( spl4_5
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f46,plain,
    ( spl4_1
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f135,plain,
    ( spl4_18
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0)
        | ~ m1_pre_topc(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f138,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK3)
    | spl4_1
    | ~ spl4_18 ),
    inference(resolution,[],[f136,f47])).

fof(f47,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f136,plain,
    ( ! [X0] :
        ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(sK1,X0) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f135])).

fof(f137,plain,
    ( ~ spl4_9
    | ~ spl4_11
    | spl4_18
    | ~ spl4_12
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f133,f127,f90,f135,f86,f78])).

fof(f78,plain,
    ( spl4_9
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f86,plain,
    ( spl4_11
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f90,plain,
    ( spl4_12
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f127,plain,
    ( spl4_17
  <=> ! [X1,X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK1,X1)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK1,X0)
        | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f133,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(sK1,sK0)
        | ~ m1_pre_topc(sK1,X0)
        | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0) )
    | ~ spl4_12
    | ~ spl4_17 ),
    inference(duplicate_literal_removal,[],[f132])).

fof(f132,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(sK1,sK0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(sK1,X0)
        | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0) )
    | ~ spl4_12
    | ~ spl4_17 ),
    inference(resolution,[],[f128,f91])).

fof(f91,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f90])).

fof(f128,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X1)
        | ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK1,X1)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK1,X0)
        | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0) )
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f127])).

fof(f131,plain,
    ( spl4_13
    | ~ spl4_11
    | spl4_10
    | ~ spl4_9
    | spl4_8
    | ~ spl4_7
    | spl4_16 ),
    inference(avatar_split_clause,[],[f130,f124,f70,f74,f78,f82,f86,f94])).

fof(f94,plain,
    ( spl4_13
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f82,plain,
    ( spl4_10
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f74,plain,
    ( spl4_8
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f70,plain,
    ( spl4_7
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f124,plain,
    ( spl4_16
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f130,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_16 ),
    inference(resolution,[],[f125,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tsep_1)).

fof(f125,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | spl4_16 ),
    inference(avatar_component_clause,[],[f124])).

fof(f129,plain,
    ( ~ spl4_11
    | ~ spl4_16
    | spl4_17
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f121,f113,f90,f127,f124,f86])).

fof(f113,plain,
    ( spl4_15
  <=> k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f121,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
        | ~ l1_pre_topc(sK0)
        | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0)
        | ~ m1_pre_topc(sK1,X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK1,X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1) )
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(resolution,[],[f120,f91])).

fof(f120,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_pre_topc(X1)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X1)
        | ~ l1_pre_topc(X1)
        | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0)
        | ~ m1_pre_topc(sK1,X0)
        | ~ m1_pre_topc(X0,X2)
        | ~ m1_pre_topc(sK1,X2)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2) )
    | ~ spl4_15 ),
    inference(resolution,[],[f117,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
                  | ~ m1_pre_topc(X1,X2) )
                & ( m1_pre_topc(X1,X2)
                  | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f117,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(X0))
        | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1) )
    | ~ spl4_15 ),
    inference(resolution,[],[f116,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f116,plain,
    ( ! [X0] :
        ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),X0)
        | ~ r1_tarski(u1_struct_0(sK1),X0) )
    | ~ spl4_15 ),
    inference(superposition,[],[f40,f114])).

fof(f114,plain,
    ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f113])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

fof(f115,plain,
    ( ~ spl4_7
    | spl4_8
    | ~ spl4_9
    | spl4_10
    | spl4_15
    | spl4_2
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f107,f104,f50,f113,f82,f78,f74,f70])).

fof(f50,plain,
    ( spl4_2
  <=> r1_tsep_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f104,plain,
    ( spl4_14
  <=> ! [X1,X0] :
        ( r1_tsep_1(X0,X1)
        | k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k2_tsep_1(sK0,X0,X1))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f107,plain,
    ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | spl4_2
    | ~ spl4_14 ),
    inference(resolution,[],[f105,f51])).

fof(f51,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f105,plain,
    ( ! [X0,X1] :
        ( r1_tsep_1(X0,X1)
        | k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k2_tsep_1(sK0,X0,X1))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f104])).

fof(f106,plain,
    ( spl4_13
    | spl4_14
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f101,f86,f104,f94])).

fof(f101,plain,
    ( ! [X0,X1] :
        ( r1_tsep_1(X0,X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k2_tsep_1(sK0,X0,X1))
        | v2_struct_0(sK0) )
    | ~ spl4_11 ),
    inference(resolution,[],[f99,f87])).

fof(f87,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f86])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2))
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f98,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f97,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f44,f43])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | k2_tsep_1(X0,X1,X2) != X3
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_pre_topc(X3)
      | v2_struct_0(X3)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k2_tsep_1(X0,X1,X2) = X3
                      | u1_struct_0(X3) != k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                    & ( u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
                      | k2_tsep_1(X0,X1,X2) != X3 ) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ~ r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                   => ( k2_tsep_1(X0,X1,X2) = X3
                    <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tsep_1)).

fof(f96,plain,(
    ~ spl4_13 ),
    inference(avatar_split_clause,[],[f23,f94])).

fof(f23,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3)
    & ~ r1_tsep_1(sK1,sK2)
    & m1_pre_topc(sK2,sK3)
    & m1_pre_topc(sK1,sK3)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f19,f18,f17,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                    & ~ r1_tsep_1(X1,X2)
                    & m1_pre_topc(X2,X3)
                    & m1_pre_topc(X1,X3)
                    & m1_pre_topc(X3,X0)
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
                  ( ~ m1_pre_topc(k2_tsep_1(sK0,X1,X2),X3)
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X1,X3)
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_pre_topc(k2_tsep_1(sK0,X1,X2),X3)
                & ~ r1_tsep_1(X1,X2)
                & m1_pre_topc(X2,X3)
                & m1_pre_topc(X1,X3)
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,X2),X3)
              & ~ r1_tsep_1(sK1,X2)
              & m1_pre_topc(X2,X3)
              & m1_pre_topc(sK1,X3)
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,X2),X3)
            & ~ r1_tsep_1(sK1,X2)
            & m1_pre_topc(X2,X3)
            & m1_pre_topc(sK1,X3)
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X3)
          & ~ r1_tsep_1(sK1,sK2)
          & m1_pre_topc(sK2,X3)
          & m1_pre_topc(sK1,X3)
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X3] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X3)
        & ~ r1_tsep_1(sK1,sK2)
        & m1_pre_topc(sK2,X3)
        & m1_pre_topc(sK1,X3)
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3)
      & ~ r1_tsep_1(sK1,sK2)
      & m1_pre_topc(sK2,sK3)
      & m1_pre_topc(sK1,sK3)
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X1,X3)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
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
                  ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X1,X3)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
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
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( ( m1_pre_topc(X2,X3)
                        & m1_pre_topc(X1,X3) )
                     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                        | r1_tsep_1(X1,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
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
                 => ( ( m1_pre_topc(X2,X3)
                      & m1_pre_topc(X1,X3) )
                   => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                      | r1_tsep_1(X1,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tmap_1)).

fof(f92,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f24,f90])).

fof(f24,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f88,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f25,f86])).

fof(f25,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f84,plain,(
    ~ spl4_10 ),
    inference(avatar_split_clause,[],[f26,f82])).

fof(f26,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f80,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f27,f78])).

fof(f27,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f76,plain,(
    ~ spl4_8 ),
    inference(avatar_split_clause,[],[f28,f74])).

fof(f28,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f72,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f29,f70])).

fof(f29,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f64,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f31,f62])).

fof(f31,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f60,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f32,f58])).

fof(f32,plain,(
    m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f52,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f34,f50])).

fof(f34,plain,(
    ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f48,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f35,f46])).

fof(f35,plain,(
    ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:26:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.41  % (5522)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (5523)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (5515)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (5515)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f142,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f48,f52,f60,f64,f72,f76,f80,f84,f88,f92,f96,f106,f115,f129,f131,f137,f141])).
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    ~spl4_4 | ~spl4_5 | spl4_1 | ~spl4_18),
% 0.21/0.48    inference(avatar_split_clause,[],[f138,f135,f46,f62,f58])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    spl4_4 <=> m1_pre_topc(sK1,sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    spl4_5 <=> m1_pre_topc(sK3,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    spl4_1 <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    spl4_18 <=> ! [X0] : (~m1_pre_topc(X0,sK0) | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0) | ~m1_pre_topc(sK1,X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.48  fof(f138,plain,(
% 0.21/0.48    ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK3) | (spl4_1 | ~spl4_18)),
% 0.21/0.48    inference(resolution,[],[f136,f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) | spl4_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f46])).
% 0.21/0.48  fof(f136,plain,(
% 0.21/0.48    ( ! [X0] : (m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(sK1,X0)) ) | ~spl4_18),
% 0.21/0.48    inference(avatar_component_clause,[],[f135])).
% 0.21/0.48  fof(f137,plain,(
% 0.21/0.48    ~spl4_9 | ~spl4_11 | spl4_18 | ~spl4_12 | ~spl4_17),
% 0.21/0.48    inference(avatar_split_clause,[],[f133,f127,f90,f135,f86,f78])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    spl4_9 <=> m1_pre_topc(sK1,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    spl4_11 <=> l1_pre_topc(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    spl4_12 <=> v2_pre_topc(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    spl4_17 <=> ! [X1,X0] : (~m1_pre_topc(X0,sK0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(sK1,X1) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK1,X0) | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.21/0.48  fof(f133,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | ~m1_pre_topc(sK1,X0) | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0)) ) | (~spl4_12 | ~spl4_17)),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f132])).
% 0.21/0.48  fof(f132,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(sK1,X0) | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0)) ) | (~spl4_12 | ~spl4_17)),
% 0.21/0.48    inference(resolution,[],[f128,f91])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    v2_pre_topc(sK0) | ~spl4_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f90])).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v2_pre_topc(X1) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(X1) | ~m1_pre_topc(sK1,X1) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK1,X0) | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0)) ) | ~spl4_17),
% 0.21/0.48    inference(avatar_component_clause,[],[f127])).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    spl4_13 | ~spl4_11 | spl4_10 | ~spl4_9 | spl4_8 | ~spl4_7 | spl4_16),
% 0.21/0.48    inference(avatar_split_clause,[],[f130,f124,f70,f74,f78,f82,f86,f94])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    spl4_13 <=> v2_struct_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    spl4_10 <=> v2_struct_0(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    spl4_8 <=> v2_struct_0(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    spl4_7 <=> m1_pre_topc(sK2,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    spl4_16 <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.48  fof(f130,plain,(
% 0.21/0.48    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl4_16),
% 0.21/0.48    inference(resolution,[],[f125,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tsep_1)).
% 0.21/0.48  fof(f125,plain,(
% 0.21/0.48    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | spl4_16),
% 0.21/0.48    inference(avatar_component_clause,[],[f124])).
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    ~spl4_11 | ~spl4_16 | spl4_17 | ~spl4_12 | ~spl4_15),
% 0.21/0.48    inference(avatar_split_clause,[],[f121,f113,f90,f127,f124,f86])).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    spl4_15 <=> k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.48  fof(f121,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_pre_topc(X0,sK0) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | ~l1_pre_topc(sK0) | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0) | ~m1_pre_topc(sK1,X0) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK1,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) ) | (~spl4_12 | ~spl4_15)),
% 0.21/0.48    inference(resolution,[],[f120,f91])).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v2_pre_topc(X1) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X1) | ~l1_pre_topc(X1) | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0) | ~m1_pre_topc(sK1,X0) | ~m1_pre_topc(X0,X2) | ~m1_pre_topc(sK1,X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) ) | ~spl4_15),
% 0.21/0.48    inference(resolution,[],[f117,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(u1_struct_0(sK1),u1_struct_0(X0)) | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) ) | ~spl4_15),
% 0.21/0.48    inference(resolution,[],[f116,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),X0) | ~r1_tarski(u1_struct_0(sK1),X0)) ) | ~spl4_15),
% 0.21/0.48    inference(superposition,[],[f40,f114])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) | ~spl4_15),
% 0.21/0.48    inference(avatar_component_clause,[],[f113])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    ~spl4_7 | spl4_8 | ~spl4_9 | spl4_10 | spl4_15 | spl4_2 | ~spl4_14),
% 0.21/0.48    inference(avatar_split_clause,[],[f107,f104,f50,f113,f82,f78,f74,f70])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    spl4_2 <=> r1_tsep_1(sK1,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    spl4_14 <=> ! [X1,X0] : (r1_tsep_1(X0,X1) | k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k2_tsep_1(sK0,X0,X1)) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | (spl4_2 | ~spl4_14)),
% 0.21/0.48    inference(resolution,[],[f105,f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ~r1_tsep_1(sK1,sK2) | spl4_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f50])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tsep_1(X0,X1) | k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k2_tsep_1(sK0,X0,X1)) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0)) ) | ~spl4_14),
% 0.21/0.48    inference(avatar_component_clause,[],[f104])).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    spl4_13 | spl4_14 | ~spl4_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f101,f86,f104,f94])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tsep_1(X0,X1) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k2_tsep_1(sK0,X0,X1)) | v2_struct_0(sK0)) ) | ~spl4_11),
% 0.21/0.48    inference(resolution,[],[f99,f87])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    l1_pre_topc(sK0) | ~spl4_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f86])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2)) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f98,f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v2_struct_0(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2)) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f97,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v1_pre_topc(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2)) | ~v1_pre_topc(k2_tsep_1(X0,X1,X2)) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f44,f43])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | ~v1_pre_topc(k2_tsep_1(X0,X1,X2)) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k2_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k2_tsep_1(X0,X1,X2) = X3 | u1_struct_0(X3) != k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) & (u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k2_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tsep_1)).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    ~spl4_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f23,f94])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ~v2_struct_0(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    (((~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK2,sK3) & m1_pre_topc(sK1,sK3) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f19,f18,f17,f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(sK0,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(sK0,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(sK0,sK1,X2),X3) & ~r1_tsep_1(sK1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(sK1,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(sK0,sK1,X2),X3) & ~r1_tsep_1(sK1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(sK1,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X3) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK2,X3) & m1_pre_topc(sK1,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ? [X3] : (~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X3) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK2,X3) & m1_pre_topc(sK1,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK2,sK3) & m1_pre_topc(sK1,sK3) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f7])).
% 0.21/0.49  fof(f7,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) & ~r1_tsep_1(X1,X2)) & (m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) | r1_tsep_1(X1,X2)))))))),
% 0.21/0.49    inference(negated_conjecture,[],[f5])).
% 0.21/0.49  fof(f5,conjecture,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) | r1_tsep_1(X1,X2)))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tmap_1)).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    spl4_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f24,f90])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    v2_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    spl4_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f25,f86])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    l1_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    ~spl4_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f26,f82])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ~v2_struct_0(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    spl4_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f27,f78])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    m1_pre_topc(sK1,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    ~spl4_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f28,f74])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ~v2_struct_0(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    spl4_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f29,f70])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    m1_pre_topc(sK2,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    spl4_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f31,f62])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    m1_pre_topc(sK3,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    spl4_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f32,f58])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    m1_pre_topc(sK1,sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ~spl4_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f34,f50])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ~r1_tsep_1(sK1,sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ~spl4_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f35,f46])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (5515)------------------------------
% 0.21/0.49  % (5515)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (5515)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (5515)Memory used [KB]: 10746
% 0.21/0.49  % (5515)Time elapsed: 0.009 s
% 0.21/0.49  % (5515)------------------------------
% 0.21/0.49  % (5515)------------------------------
% 0.21/0.49  % (5521)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (5508)Success in time 0.131 s
%------------------------------------------------------------------------------
