%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 245 expanded)
%              Number of leaves         :   25 ( 113 expanded)
%              Depth                    :   11
%              Number of atoms          :  659 (2209 expanded)
%              Number of equality atoms :   19 (  21 expanded)
%              Maximal formula depth    :   22 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f147,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f52,f56,f60,f64,f68,f76,f80,f84,f88,f92,f102,f112,f120,f129,f135,f146])).

fof(f146,plain,
    ( ~ spl4_3
    | spl4_9
    | ~ spl4_6
    | ~ spl4_4
    | spl4_5
    | ~ spl4_2
    | ~ spl4_8
    | spl4_1
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f136,f133,f46,f74,f50,f62,f58,f66,f78,f54])).

fof(f54,plain,
    ( spl4_3
  <=> m1_pre_topc(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f78,plain,
    ( spl4_9
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f66,plain,
    ( spl4_6
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f58,plain,
    ( spl4_4
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f62,plain,
    ( spl4_5
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f50,plain,
    ( spl4_2
  <=> m1_pre_topc(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f74,plain,
    ( spl4_8
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f46,plain,
    ( spl4_1
  <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f133,plain,
    ( spl4_17
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X2,X1)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK0)
        | ~ m1_pre_topc(X1,sK0)
        | m1_pre_topc(k1_tsep_1(sK0,X0,X2),X1)
        | ~ m1_pre_topc(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f136,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK2)
    | spl4_1
    | ~ spl4_17 ),
    inference(resolution,[],[f134,f47])).

fof(f47,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f134,plain,
    ( ! [X2,X0,X1] :
        ( m1_pre_topc(k1_tsep_1(sK0,X0,X2),X1)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X2,X1)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK0)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1) )
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f133])).

fof(f135,plain,
    ( spl4_12
    | ~ spl4_10
    | spl4_17
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f131,f127,f133,f82,f90])).

fof(f90,plain,
    ( spl4_12
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f82,plain,
    ( spl4_10
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f127,plain,
    ( spl4_16
  <=> ! [X1,X0,X2] :
        ( ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,X0,X2),sK0)
        | m1_pre_topc(k1_tsep_1(sK0,X0,X2),X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X1)
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f131,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | m1_pre_topc(k1_tsep_1(sK0,X0,X2),X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X1)
        | ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_16 ),
    inference(duplicate_literal_removal,[],[f130])).

fof(f130,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | m1_pre_topc(k1_tsep_1(sK0,X0,X2),X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X1)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_16 ),
    inference(resolution,[],[f128,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
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
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(f128,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_pre_topc(k1_tsep_1(sK0,X0,X2),sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | m1_pre_topc(k1_tsep_1(sK0,X0,X2),X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X1)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f127])).

fof(f129,plain,
    ( ~ spl4_10
    | spl4_16
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f125,f118,f86,f127,f82])).

fof(f86,plain,
    ( spl4_11
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f118,plain,
    ( spl4_15
  <=> ! [X1,X0,X2] :
        ( r1_tarski(u1_struct_0(k1_tsep_1(sK0,X0,X1)),u1_struct_0(X2))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X2)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X2)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X2,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f125,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X1)
        | ~ m1_pre_topc(X2,sK0)
        | ~ m1_pre_topc(X1,sK0)
        | m1_pre_topc(k1_tsep_1(sK0,X0,X2),X1)
        | ~ m1_pre_topc(k1_tsep_1(sK0,X0,X2),sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0) )
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(duplicate_literal_removal,[],[f124])).

fof(f124,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X1)
        | ~ m1_pre_topc(X2,sK0)
        | ~ m1_pre_topc(X1,sK0)
        | m1_pre_topc(k1_tsep_1(sK0,X0,X2),X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,X0,X2),sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0) )
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(resolution,[],[f122,f87])).

fof(f87,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f86])).

fof(f122,plain,
    ( ! [X6,X8,X7,X5] :
        ( ~ v2_pre_topc(X8)
        | ~ m1_pre_topc(X5,X6)
        | ~ m1_pre_topc(X5,sK0)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,X6)
        | ~ m1_pre_topc(X7,sK0)
        | ~ m1_pre_topc(X6,sK0)
        | m1_pre_topc(k1_tsep_1(sK0,X5,X7),X6)
        | ~ m1_pre_topc(X6,X8)
        | ~ m1_pre_topc(k1_tsep_1(sK0,X5,X7),X8)
        | ~ l1_pre_topc(X8)
        | v2_struct_0(X5) )
    | ~ spl4_15 ),
    inference(resolution,[],[f119,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f119,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(u1_struct_0(k1_tsep_1(sK0,X0,X1)),u1_struct_0(X2))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X2)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X2)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X2,sK0) )
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f118])).

fof(f120,plain,
    ( ~ spl4_10
    | spl4_15
    | ~ spl4_11
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f116,f110,f86,f118,f82])).

fof(f110,plain,
    ( spl4_14
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_pre_topc(X0,sK0)
        | r1_tarski(u1_struct_0(k1_tsep_1(sK0,X1,X0)),u1_struct_0(X2))
        | ~ m1_pre_topc(X2,sK0)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ m1_pre_topc(X0,X3)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_pre_topc(X0,X2)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X1,X2)
        | v2_struct_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f116,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(u1_struct_0(k1_tsep_1(sK0,X0,X1)),u1_struct_0(X2))
        | ~ m1_pre_topc(X2,sK0)
        | ~ m1_pre_topc(X1,sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X1,X2)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X0,X2)
        | v2_struct_0(X0) )
    | ~ spl4_11
    | ~ spl4_14 ),
    inference(duplicate_literal_removal,[],[f115])).

fof(f115,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(u1_struct_0(k1_tsep_1(sK0,X0,X1)),u1_struct_0(X2))
        | ~ m1_pre_topc(X2,sK0)
        | ~ m1_pre_topc(X1,sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X2,sK0)
        | ~ m1_pre_topc(X1,X2)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X0,X2)
        | v2_struct_0(X0) )
    | ~ spl4_11
    | ~ spl4_14 ),
    inference(resolution,[],[f111,f87])).

fof(f111,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v2_pre_topc(X3)
        | r1_tarski(u1_struct_0(k1_tsep_1(sK0,X1,X0)),u1_struct_0(X2))
        | ~ m1_pre_topc(X2,sK0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(X3)
        | ~ m1_pre_topc(X0,X3)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_pre_topc(X0,X2)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X1,X2)
        | v2_struct_0(X1) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f110])).

fof(f112,plain,
    ( ~ spl4_10
    | spl4_14
    | ~ spl4_11
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f107,f100,f86,f110,f82])).

fof(f100,plain,
    ( spl4_13
  <=> ! [X1,X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X0)) = u1_struct_0(k1_tsep_1(sK0,X1,X0))
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f107,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X2)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_pre_topc(X0,X3)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | ~ m1_pre_topc(X1,X2)
        | ~ m1_pre_topc(X2,sK0)
        | ~ l1_pre_topc(sK0)
        | r1_tarski(u1_struct_0(k1_tsep_1(sK0,X1,X0)),u1_struct_0(X2)) )
    | ~ spl4_11
    | ~ spl4_13 ),
    inference(duplicate_literal_removal,[],[f106])).

fof(f106,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X2)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_pre_topc(X0,X3)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | ~ m1_pre_topc(X1,X2)
        | ~ m1_pre_topc(X2,sK0)
        | ~ m1_pre_topc(X1,sK0)
        | ~ l1_pre_topc(sK0)
        | r1_tarski(u1_struct_0(k1_tsep_1(sK0,X1,X0)),u1_struct_0(X2)) )
    | ~ spl4_11
    | ~ spl4_13 ),
    inference(resolution,[],[f105,f87])).

fof(f105,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ v2_pre_topc(X4)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X2)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_pre_topc(X1,X3)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | ~ m1_pre_topc(X0,X2)
        | ~ m1_pre_topc(X2,X4)
        | ~ m1_pre_topc(X0,X4)
        | ~ l1_pre_topc(X4)
        | r1_tarski(u1_struct_0(k1_tsep_1(sK0,X0,X1)),u1_struct_0(X2)) )
    | ~ spl4_13 ),
    inference(resolution,[],[f104,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f104,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
        | r1_tarski(u1_struct_0(k1_tsep_1(sK0,X0,X1)),u1_struct_0(X2))
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X2)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_pre_topc(X1,X3)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3) )
    | ~ spl4_13 ),
    inference(resolution,[],[f103,f39])).

fof(f103,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(u1_struct_0(X1),X2)
        | r1_tarski(u1_struct_0(k1_tsep_1(sK0,X0,X1)),X2)
        | ~ r1_tarski(u1_struct_0(X0),X2)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | v2_struct_0(X1) )
    | ~ spl4_13 ),
    inference(superposition,[],[f43,f101])).

fof(f101,plain,
    ( ! [X0,X1] :
        ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(X0)) = u1_struct_0(k1_tsep_1(sK0,X1,X0))
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | v2_struct_0(X0) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f100])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
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

fof(f102,plain,
    ( spl4_12
    | spl4_13
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f97,f82,f100,f90])).

fof(f97,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X0)) = u1_struct_0(k1_tsep_1(sK0,X1,X0))
        | v2_struct_0(sK0) )
    | ~ spl4_10 ),
    inference(resolution,[],[f95,f83])).

fof(f83,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f82])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f94,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))
      | v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f93,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f44,f42])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | k1_tsep_1(X0,X1,X2) != X3
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k1_tsep_1(X0,X1,X2) = X3
                      | u1_struct_0(X3) != k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                    & ( u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
                      | k1_tsep_1(X0,X1,X2) != X3 ) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
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
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
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
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
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
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_pre_topc(X3)
                    & ~ v2_struct_0(X3) )
                 => ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tsep_1)).

fof(f92,plain,(
    ~ spl4_12 ),
    inference(avatar_split_clause,[],[f24,f90])).

fof(f24,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
    & m1_pre_topc(sK3,sK2)
    & m1_pre_topc(sK1,sK2)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f20,f19,f18,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
                    & m1_pre_topc(X3,X2)
                    & m1_pre_topc(X1,X2)
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
                  ( ~ m1_pre_topc(k1_tsep_1(sK0,X1,X3),X2)
                  & m1_pre_topc(X3,X2)
                  & m1_pre_topc(X1,X2)
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

fof(f18,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_pre_topc(k1_tsep_1(sK0,X1,X3),X2)
                & m1_pre_topc(X3,X2)
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,X3),X2)
              & m1_pre_topc(X3,X2)
              & m1_pre_topc(sK1,X2)
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,X3),X2)
            & m1_pre_topc(X3,X2)
            & m1_pre_topc(sK1,X2)
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,X3),sK2)
          & m1_pre_topc(X3,sK2)
          & m1_pre_topc(sK1,sK2)
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X3] :
        ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,X3),sK2)
        & m1_pre_topc(X3,sK2)
        & m1_pre_topc(sK1,sK2)
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
      & m1_pre_topc(sK3,sK2)
      & m1_pre_topc(sK1,sK2)
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
                  & m1_pre_topc(X3,X2)
                  & m1_pre_topc(X1,X2)
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
                  ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
                  & m1_pre_topc(X3,X2)
                  & m1_pre_topc(X1,X2)
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
                   => ( ( m1_pre_topc(X3,X2)
                        & m1_pre_topc(X1,X2) )
                     => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) ) ) ) ) ) ),
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
                 => ( ( m1_pre_topc(X3,X2)
                      & m1_pre_topc(X1,X2) )
                   => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tmap_1)).

fof(f88,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f25,f86])).

fof(f25,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f84,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f26,f82])).

fof(f26,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f80,plain,(
    ~ spl4_9 ),
    inference(avatar_split_clause,[],[f27,f78])).

fof(f27,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f76,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f28,f74])).

fof(f28,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f68,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f30,f66])).

fof(f30,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f64,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f31,f62])).

fof(f31,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f60,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f32,f58])).

fof(f32,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f56,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f33,f54])).

fof(f33,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f52,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f34,f50])).

fof(f34,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f48,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f35,f46])).

fof(f35,plain,(
    ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:14:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (15818)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.46  % (15832)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.46  % (15825)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.46  % (15815)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (15821)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (15821)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f147,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f48,f52,f56,f60,f64,f68,f76,f80,f84,f88,f92,f102,f112,f120,f129,f135,f146])).
% 0.21/0.47  fof(f146,plain,(
% 0.21/0.47    ~spl4_3 | spl4_9 | ~spl4_6 | ~spl4_4 | spl4_5 | ~spl4_2 | ~spl4_8 | spl4_1 | ~spl4_17),
% 0.21/0.47    inference(avatar_split_clause,[],[f136,f133,f46,f74,f50,f62,f58,f66,f78,f54])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    spl4_3 <=> m1_pre_topc(sK1,sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    spl4_9 <=> v2_struct_0(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    spl4_6 <=> m1_pre_topc(sK2,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    spl4_4 <=> m1_pre_topc(sK3,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    spl4_5 <=> v2_struct_0(sK3)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    spl4_2 <=> m1_pre_topc(sK3,sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    spl4_8 <=> m1_pre_topc(sK1,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    spl4_1 <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.47  fof(f133,plain,(
% 0.21/0.47    spl4_17 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X1,sK0) | m1_pre_topc(k1_tsep_1(sK0,X0,X2),X1) | ~m1_pre_topc(X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.21/0.47  fof(f136,plain,(
% 0.21/0.47    ~m1_pre_topc(sK1,sK0) | ~m1_pre_topc(sK3,sK2) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK2) | (spl4_1 | ~spl4_17)),
% 0.21/0.47    inference(resolution,[],[f134,f47])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) | spl4_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f46])).
% 0.21/0.47  fof(f134,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(sK0,X0,X2),X1) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,X1)) ) | ~spl4_17),
% 0.21/0.47    inference(avatar_component_clause,[],[f133])).
% 0.21/0.47  fof(f135,plain,(
% 0.21/0.47    spl4_12 | ~spl4_10 | spl4_17 | ~spl4_16),
% 0.21/0.47    inference(avatar_split_clause,[],[f131,f127,f133,f82,f90])).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    spl4_12 <=> v2_struct_0(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    spl4_10 <=> l1_pre_topc(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.47  fof(f127,plain,(
% 0.21/0.47    spl4_16 <=> ! [X1,X0,X2] : (~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(k1_tsep_1(sK0,X0,X2),sK0) | m1_pre_topc(k1_tsep_1(sK0,X0,X2),X1) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X0,sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.47  fof(f131,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~m1_pre_topc(X0,X1) | m1_pre_topc(k1_tsep_1(sK0,X0,X2),X1) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl4_16),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f130])).
% 0.21/0.47  fof(f130,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~m1_pre_topc(X0,X1) | m1_pre_topc(k1_tsep_1(sK0,X0,X2),X1) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl4_16),
% 0.21/0.47    inference(resolution,[],[f128,f42])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).
% 0.21/0.47  fof(f128,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_pre_topc(k1_tsep_1(sK0,X0,X2),sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,X1) | m1_pre_topc(k1_tsep_1(sK0,X0,X2),X1) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X0,sK0)) ) | ~spl4_16),
% 0.21/0.47    inference(avatar_component_clause,[],[f127])).
% 0.21/0.47  fof(f129,plain,(
% 0.21/0.47    ~spl4_10 | spl4_16 | ~spl4_11 | ~spl4_15),
% 0.21/0.47    inference(avatar_split_clause,[],[f125,f118,f86,f127,f82])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    spl4_11 <=> v2_pre_topc(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.47  fof(f118,plain,(
% 0.21/0.47    spl4_15 <=> ! [X1,X0,X2] : (r1_tarski(u1_struct_0(k1_tsep_1(sK0,X0,X1)),u1_struct_0(X2)) | v2_struct_0(X0) | ~m1_pre_topc(X0,X2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X2,sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.47  fof(f125,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X1,sK0) | m1_pre_topc(k1_tsep_1(sK0,X0,X2),X1) | ~m1_pre_topc(k1_tsep_1(sK0,X0,X2),sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0)) ) | (~spl4_11 | ~spl4_15)),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f124])).
% 0.21/0.47  fof(f124,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X1,sK0) | m1_pre_topc(k1_tsep_1(sK0,X0,X2),X1) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(k1_tsep_1(sK0,X0,X2),sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0)) ) | (~spl4_11 | ~spl4_15)),
% 0.21/0.47    inference(resolution,[],[f122,f87])).
% 0.21/0.47  fof(f87,plain,(
% 0.21/0.47    v2_pre_topc(sK0) | ~spl4_11),
% 0.21/0.47    inference(avatar_component_clause,[],[f86])).
% 0.21/0.47  fof(f122,plain,(
% 0.21/0.47    ( ! [X6,X8,X7,X5] : (~v2_pre_topc(X8) | ~m1_pre_topc(X5,X6) | ~m1_pre_topc(X5,sK0) | v2_struct_0(X7) | ~m1_pre_topc(X7,X6) | ~m1_pre_topc(X7,sK0) | ~m1_pre_topc(X6,sK0) | m1_pre_topc(k1_tsep_1(sK0,X5,X7),X6) | ~m1_pre_topc(X6,X8) | ~m1_pre_topc(k1_tsep_1(sK0,X5,X7),X8) | ~l1_pre_topc(X8) | v2_struct_0(X5)) ) | ~spl4_15),
% 0.21/0.47    inference(resolution,[],[f119,f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).
% 0.21/0.47  fof(f119,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(k1_tsep_1(sK0,X0,X1)),u1_struct_0(X2)) | v2_struct_0(X0) | ~m1_pre_topc(X0,X2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X2,sK0)) ) | ~spl4_15),
% 0.21/0.47    inference(avatar_component_clause,[],[f118])).
% 0.21/0.47  fof(f120,plain,(
% 0.21/0.47    ~spl4_10 | spl4_15 | ~spl4_11 | ~spl4_14),
% 0.21/0.47    inference(avatar_split_clause,[],[f116,f110,f86,f118,f82])).
% 0.21/0.47  fof(f110,plain,(
% 0.21/0.47    spl4_14 <=> ! [X1,X3,X0,X2] : (~m1_pre_topc(X0,sK0) | r1_tarski(u1_struct_0(k1_tsep_1(sK0,X1,X0)),u1_struct_0(X2)) | ~m1_pre_topc(X2,sK0) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~m1_pre_topc(X0,X3) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X0,X2) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X1,X2) | v2_struct_0(X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.47  fof(f116,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(k1_tsep_1(sK0,X0,X1)),u1_struct_0(X2)) | ~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X1,sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(X1,X2) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X0,X2) | v2_struct_0(X0)) ) | (~spl4_11 | ~spl4_14)),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f115])).
% 0.21/0.47  fof(f115,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(k1_tsep_1(sK0,X0,X1)),u1_struct_0(X2)) | ~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X1,sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X1,X2) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X0,X2) | v2_struct_0(X0)) ) | (~spl4_11 | ~spl4_14)),
% 0.21/0.47    inference(resolution,[],[f111,f87])).
% 0.21/0.47  fof(f111,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X3) | r1_tarski(u1_struct_0(k1_tsep_1(sK0,X1,X0)),u1_struct_0(X2)) | ~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(X3) | ~m1_pre_topc(X0,X3) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X0,X2) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X1,X2) | v2_struct_0(X1)) ) | ~spl4_14),
% 0.21/0.47    inference(avatar_component_clause,[],[f110])).
% 0.21/0.47  fof(f112,plain,(
% 0.21/0.47    ~spl4_10 | spl4_14 | ~spl4_11 | ~spl4_13),
% 0.21/0.47    inference(avatar_split_clause,[],[f107,f100,f86,f110,f82])).
% 0.21/0.47  fof(f100,plain,(
% 0.21/0.47    spl4_13 <=> ! [X1,X0] : (~m1_pre_topc(X0,sK0) | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X0)) = u1_struct_0(k1_tsep_1(sK0,X1,X0)) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | v2_struct_0(X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.47  fof(f107,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | v2_struct_0(X0) | ~m1_pre_topc(X0,X2) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X0,X3) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,sK0) | ~l1_pre_topc(sK0) | r1_tarski(u1_struct_0(k1_tsep_1(sK0,X1,X0)),u1_struct_0(X2))) ) | (~spl4_11 | ~spl4_13)),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f106])).
% 0.21/0.47  fof(f106,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | v2_struct_0(X0) | ~m1_pre_topc(X0,X2) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X0,X3) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X1,sK0) | ~l1_pre_topc(sK0) | r1_tarski(u1_struct_0(k1_tsep_1(sK0,X1,X0)),u1_struct_0(X2))) ) | (~spl4_11 | ~spl4_13)),
% 0.21/0.47    inference(resolution,[],[f105,f87])).
% 0.21/0.47  fof(f105,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X3,X1] : (~v2_pre_topc(X4) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X1,X3) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | ~m1_pre_topc(X0,X2) | ~m1_pre_topc(X2,X4) | ~m1_pre_topc(X0,X4) | ~l1_pre_topc(X4) | r1_tarski(u1_struct_0(k1_tsep_1(sK0,X0,X1)),u1_struct_0(X2))) ) | ~spl4_13),
% 0.21/0.47    inference(resolution,[],[f104,f39])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  fof(f104,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (~r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) | r1_tarski(u1_struct_0(k1_tsep_1(sK0,X0,X1)),u1_struct_0(X2)) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X1,X3) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3)) ) | ~spl4_13),
% 0.21/0.47    inference(resolution,[],[f103,f39])).
% 0.21/0.47  fof(f103,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r1_tarski(u1_struct_0(X1),X2) | r1_tarski(u1_struct_0(k1_tsep_1(sK0,X0,X1)),X2) | ~r1_tarski(u1_struct_0(X0),X2) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | v2_struct_0(X1)) ) | ~spl4_13),
% 0.21/0.47    inference(superposition,[],[f43,f101])).
% 0.21/0.47  fof(f101,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X0)) = u1_struct_0(k1_tsep_1(sK0,X1,X0)) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | v2_struct_0(X0)) ) | ~spl4_13),
% 0.21/0.47    inference(avatar_component_clause,[],[f100])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(flattening,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.21/0.47  fof(f102,plain,(
% 0.21/0.47    spl4_12 | spl4_13 | ~spl4_10),
% 0.21/0.47    inference(avatar_split_clause,[],[f97,f82,f100,f90])).
% 0.21/0.47  fof(f97,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X0)) = u1_struct_0(k1_tsep_1(sK0,X1,X0)) | v2_struct_0(sK0)) ) | ~spl4_10),
% 0.21/0.47    inference(resolution,[],[f95,f83])).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    l1_pre_topc(sK0) | ~spl4_10),
% 0.21/0.47    inference(avatar_component_clause,[],[f82])).
% 0.21/0.47  fof(f95,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f94,f40])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f94,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f93,f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (v1_pre_topc(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f93,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) | ~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f44,f42])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(equality_resolution,[],[f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tsep_1(X0,X1,X2) = X3 | u1_struct_0(X3) != k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) & (u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)))))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tsep_1)).
% 0.21/0.47  fof(f92,plain,(
% 0.21/0.47    ~spl4_12),
% 0.21/0.47    inference(avatar_split_clause,[],[f24,f90])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ~v2_struct_0(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    (((~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) & m1_pre_topc(sK3,sK2) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f20,f19,f18,f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(sK0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(sK0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(sK0,sK1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(sK1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(sK0,sK1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(sK1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (~m1_pre_topc(k1_tsep_1(sK0,sK1,X3),sK2) & m1_pre_topc(X3,sK2) & m1_pre_topc(sK1,sK2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ? [X3] : (~m1_pre_topc(k1_tsep_1(sK0,sK1,X3),sK2) & m1_pre_topc(X3,sK2) & m1_pre_topc(sK1,sK2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) & m1_pre_topc(sK3,sK2) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f7])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & (m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,negated_conjecture,(
% 0.21/0.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 0.21/0.47    inference(negated_conjecture,[],[f5])).
% 0.21/0.47  fof(f5,conjecture,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tmap_1)).
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    spl4_11),
% 0.21/0.47    inference(avatar_split_clause,[],[f25,f86])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    v2_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f84,plain,(
% 0.21/0.47    spl4_10),
% 0.21/0.47    inference(avatar_split_clause,[],[f26,f82])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    l1_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    ~spl4_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f27,f78])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ~v2_struct_0(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    spl4_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f28,f74])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    m1_pre_topc(sK1,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    spl4_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f30,f66])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    m1_pre_topc(sK2,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    ~spl4_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f31,f62])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ~v2_struct_0(sK3)),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    spl4_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f32,f58])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    m1_pre_topc(sK3,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    spl4_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f33,f54])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    m1_pre_topc(sK1,sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    spl4_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f34,f50])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    m1_pre_topc(sK3,sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    ~spl4_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f35,f46])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (15821)------------------------------
% 0.21/0.47  % (15821)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (15821)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (15821)Memory used [KB]: 10746
% 0.21/0.47  % (15821)Time elapsed: 0.071 s
% 0.21/0.47  % (15821)------------------------------
% 0.21/0.47  % (15821)------------------------------
% 0.21/0.48  % (15823)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.48  % (15817)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.48  % (15826)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.48  % (15824)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.48  % (15819)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (15828)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (15816)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (15816)Refutation not found, incomplete strategy% (15816)------------------------------
% 0.21/0.49  % (15816)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (15816)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (15816)Memory used [KB]: 10490
% 0.21/0.49  % (15816)Time elapsed: 0.060 s
% 0.21/0.49  % (15816)------------------------------
% 0.21/0.49  % (15816)------------------------------
% 0.21/0.49  % (15834)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.49  % (15833)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.49  % (15820)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (15830)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  % (15827)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (15814)Success in time 0.145 s
%------------------------------------------------------------------------------
