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
% DateTime   : Thu Dec  3 13:13:47 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 204 expanded)
%              Number of leaves         :   27 (  74 expanded)
%              Depth                    :   11
%              Number of atoms          :  380 ( 706 expanded)
%              Number of equality atoms :   47 (  77 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f403,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f67,f72,f77,f82,f97,f107,f118,f244,f303,f326,f367,f389,f390,f391,f402])).

fof(f402,plain,
    ( ~ spl8_1
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_15 ),
    inference(avatar_contradiction_clause,[],[f401])).

fof(f401,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f400,f61])).

fof(f61,plain,
    ( l1_pre_topc(sK0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl8_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f400,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f399,f96])).

fof(f96,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl8_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f399,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f398,f76])).

fof(f76,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl8_4
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f398,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl8_5
    | ~ spl8_15 ),
    inference(resolution,[],[f294,f81])).

fof(f81,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl8_5
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f294,plain,
    ( ! [X1] :
        ( ~ v4_pre_topc(sK1,X1)
        | ~ m1_pre_topc(sK2,X1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1) )
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f293])).

fof(f293,plain,
    ( spl8_15
  <=> ! [X1] :
        ( ~ m1_pre_topc(sK2,X1)
        | ~ v4_pre_topc(sK1,X1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f391,plain,
    ( sK1 != k3_xboole_0(sK1,k2_struct_0(sK2))
    | sK1 != sK3
    | v4_pre_topc(sK3,sK2)
    | ~ v4_pre_topc(k3_xboole_0(sK1,k2_struct_0(sK2)),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f390,plain,
    ( sK1 != k3_xboole_0(sK1,k2_struct_0(sK2))
    | m1_subset_1(k3_xboole_0(sK1,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f389,plain,
    ( spl8_25
    | ~ spl8_22 ),
    inference(avatar_split_clause,[],[f369,f364,f386])).

fof(f386,plain,
    ( spl8_25
  <=> sK1 = k3_xboole_0(sK1,k2_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f364,plain,
    ( spl8_22
  <=> r1_tarski(sK1,k2_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f369,plain,
    ( sK1 = k3_xboole_0(sK1,k2_struct_0(sK2))
    | ~ spl8_22 ),
    inference(resolution,[],[f366,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f366,plain,
    ( r1_tarski(sK1,k2_struct_0(sK2))
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f364])).

fof(f367,plain,
    ( spl8_22
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f361,f323,f241,f115,f104,f364])).

fof(f104,plain,
    ( spl8_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f115,plain,
    ( spl8_9
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f241,plain,
    ( spl8_12
  <=> l1_pre_topc(k1_pre_topc(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f323,plain,
    ( spl8_18
  <=> sK1 = k2_struct_0(k1_pre_topc(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f361,plain,
    ( r1_tarski(sK1,k2_struct_0(sK2))
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f360,f106])).

fof(f106,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f104])).

fof(f360,plain,
    ( r1_tarski(sK1,k2_struct_0(sK2))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f359,f117])).

fof(f117,plain,
    ( l1_pre_topc(sK2)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f115])).

fof(f359,plain,
    ( ~ l1_pre_topc(sK2)
    | r1_tarski(sK1,k2_struct_0(sK2))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_18 ),
    inference(resolution,[],[f336,f127])).

fof(f127,plain,
    ( ! [X11] :
        ( m1_pre_topc(k1_pre_topc(sK2,X11),sK2)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK2))) )
    | ~ spl8_9 ),
    inference(resolution,[],[f117,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(k1_pre_topc(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(f336,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k1_pre_topc(sK2,sK1),X0)
        | ~ l1_pre_topc(X0)
        | r1_tarski(sK1,k2_struct_0(X0)) )
    | ~ spl8_12
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f328,f243])).

fof(f243,plain,
    ( l1_pre_topc(k1_pre_topc(sK2,sK1))
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f241])).

fof(f328,plain,
    ( ! [X0] :
        ( r1_tarski(sK1,k2_struct_0(X0))
        | ~ l1_pre_topc(k1_pre_topc(sK2,sK1))
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(k1_pre_topc(sK2,sK1),X0) )
    | ~ spl8_18 ),
    inference(superposition,[],[f40,f325])).

fof(f325,plain,
    ( sK1 = k2_struct_0(k1_pre_topc(sK2,sK1))
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f323])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_pre_topc)).

fof(f326,plain,
    ( spl8_18
    | ~ spl8_8
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f316,f115,f104,f323])).

fof(f316,plain,
    ( sK1 = k2_struct_0(k1_pre_topc(sK2,sK1))
    | ~ spl8_8
    | ~ spl8_9 ),
    inference(resolution,[],[f315,f106])).

fof(f315,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | k2_struct_0(k1_pre_topc(sK2,X0)) = X0 )
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f195,f127])).

fof(f195,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_pre_topc(k1_pre_topc(sK2,X0),sK2)
        | k2_struct_0(k1_pre_topc(sK2,X0)) = X0 )
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f194,f117])).

fof(f194,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ l1_pre_topc(sK2)
        | ~ m1_pre_topc(k1_pre_topc(sK2,X0),sK2)
        | k2_struct_0(k1_pre_topc(sK2,X0)) = X0 )
    | ~ spl8_9 ),
    inference(duplicate_literal_removal,[],[f193])).

fof(f193,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ l1_pre_topc(sK2)
        | ~ m1_pre_topc(k1_pre_topc(sK2,X0),sK2)
        | k2_struct_0(k1_pre_topc(sK2,X0)) = X0 )
    | ~ spl8_9 ),
    inference(resolution,[],[f126,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X2,X0)
      | k2_struct_0(X2) = X1
      | k1_pre_topc(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2) )
             => ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_pre_topc)).

fof(f126,plain,
    ( ! [X10] :
        ( v1_pre_topc(k1_pre_topc(sK2,X10))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK2))) )
    | ~ spl8_9 ),
    inference(resolution,[],[f117,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_pre_topc(k1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f303,plain,
    ( spl8_15
    | ~ spl8_16
    | spl8_17
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f180,f104,f300,f296,f293])).

fof(f296,plain,
    ( spl8_16
  <=> m1_subset_1(k3_xboole_0(sK1,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f300,plain,
    ( spl8_17
  <=> v4_pre_topc(k3_xboole_0(sK1,k2_struct_0(sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f180,plain,
    ( ! [X1] :
        ( v4_pre_topc(k3_xboole_0(sK1,k2_struct_0(sK2)),sK2)
        | ~ m1_subset_1(k3_xboole_0(sK1,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_pre_topc(sK2,X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v4_pre_topc(sK1,X1) )
    | ~ spl8_8 ),
    inference(forward_demodulation,[],[f179,f48])).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f179,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k3_xboole_0(sK1,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_pre_topc(sK2,X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v4_pre_topc(sK1,X1)
        | v4_pre_topc(k3_xboole_0(k2_struct_0(sK2),sK1),sK2) )
    | ~ spl8_8 ),
    inference(forward_demodulation,[],[f177,f48])).

fof(f177,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k3_xboole_0(k2_struct_0(sK2),sK1),k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_pre_topc(sK2,X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v4_pre_topc(sK1,X1)
        | v4_pre_topc(k3_xboole_0(k2_struct_0(sK2),sK1),sK2) )
    | ~ spl8_8 ),
    inference(superposition,[],[f55,f138])).

fof(f138,plain,
    ( ! [X1] : k3_xboole_0(X1,sK1) = k9_subset_1(u1_struct_0(sK2),sK1,X1)
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f134,f106])).

fof(f134,plain,
    ( ! [X1] :
        ( k3_xboole_0(X1,sK1) = k9_subset_1(u1_struct_0(sK2),sK1,X1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK2))) )
    | ~ spl8_8 ),
    inference(superposition,[],[f109,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f109,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK2),X0,sK1) = k9_subset_1(u1_struct_0(sK2),sK1,X0)
    | ~ spl8_8 ),
    inference(resolution,[],[f106,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X3,X0)
      | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X3,X0)
      | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
      | v4_pre_topc(X2,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v4_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( v4_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_pre_topc)).

fof(f244,plain,
    ( spl8_12
    | ~ spl8_8
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f234,f115,f104,f241])).

fof(f234,plain,
    ( l1_pre_topc(k1_pre_topc(sK2,sK1))
    | ~ spl8_8
    | ~ spl8_9 ),
    inference(resolution,[],[f233,f106])).

fof(f233,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | l1_pre_topc(k1_pre_topc(sK2,X0)) )
    | ~ spl8_9 ),
    inference(resolution,[],[f127,f123])).

fof(f123,plain,
    ( ! [X5] :
        ( ~ m1_pre_topc(X5,sK2)
        | l1_pre_topc(X5) )
    | ~ spl8_9 ),
    inference(resolution,[],[f117,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f118,plain,
    ( spl8_9
    | ~ spl8_1
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f110,f74,f59,f115])).

fof(f110,plain,
    ( l1_pre_topc(sK2)
    | ~ spl8_1
    | ~ spl8_4 ),
    inference(resolution,[],[f86,f76])).

fof(f86,plain,
    ( ! [X5] :
        ( ~ m1_pre_topc(X5,sK0)
        | l1_pre_topc(X5) )
    | ~ spl8_1 ),
    inference(resolution,[],[f61,f41])).

fof(f107,plain,
    ( spl8_8
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f92,f64,f104])).

fof(f64,plain,
    ( spl8_2
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f92,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f24,f66])).

fof(f66,plain,
    ( sK1 = sK3
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f24,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v4_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v4_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v4_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v4_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( v4_pre_topc(X1,X0)
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                     => ( X1 = X3
                       => v4_pre_topc(X3,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v4_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v4_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tops_2)).

fof(f97,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f29,f94])).

fof(f29,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f82,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f28,f79])).

fof(f28,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f77,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f27,f74])).

fof(f27,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f72,plain,(
    ~ spl8_3 ),
    inference(avatar_split_clause,[],[f26,f69])).

fof(f69,plain,
    ( spl8_3
  <=> v4_pre_topc(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f26,plain,(
    ~ v4_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f67,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f25,f64])).

fof(f25,plain,(
    sK1 = sK3 ),
    inference(cnf_transformation,[],[f13])).

fof(f62,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f30,f59])).

fof(f30,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:41:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (19801)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.47  % (19815)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (19807)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (19815)Refutation not found, incomplete strategy% (19815)------------------------------
% 0.20/0.48  % (19815)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (19809)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % (19815)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (19815)Memory used [KB]: 10618
% 0.20/0.49  % (19815)Time elapsed: 0.061 s
% 0.20/0.49  % (19815)------------------------------
% 0.20/0.49  % (19815)------------------------------
% 0.20/0.49  % (19805)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.49  % (19804)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.50  % (19802)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.50  % (19808)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.50  % (19813)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.50  % (19798)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (19797)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.50  % (19810)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.51  % (19800)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (19795)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (19799)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.51  % (19796)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (19795)Refutation not found, incomplete strategy% (19795)------------------------------
% 0.20/0.51  % (19795)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (19795)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (19795)Memory used [KB]: 6268
% 0.20/0.51  % (19795)Time elapsed: 0.103 s
% 0.20/0.51  % (19795)------------------------------
% 0.20/0.51  % (19795)------------------------------
% 0.20/0.51  % (19796)Refutation not found, incomplete strategy% (19796)------------------------------
% 0.20/0.51  % (19796)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (19796)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (19796)Memory used [KB]: 10618
% 0.20/0.51  % (19796)Time elapsed: 0.067 s
% 0.20/0.51  % (19796)------------------------------
% 0.20/0.51  % (19796)------------------------------
% 0.20/0.51  % (19806)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.51  % (19808)Refutation not found, incomplete strategy% (19808)------------------------------
% 0.20/0.51  % (19808)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (19808)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (19808)Memory used [KB]: 1791
% 0.20/0.51  % (19808)Time elapsed: 0.107 s
% 0.20/0.51  % (19808)------------------------------
% 0.20/0.51  % (19808)------------------------------
% 0.20/0.52  % (19798)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f403,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f62,f67,f72,f77,f82,f97,f107,f118,f244,f303,f326,f367,f389,f390,f391,f402])).
% 0.20/0.52  fof(f402,plain,(
% 0.20/0.52    ~spl8_1 | ~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_15),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f401])).
% 0.20/0.52  fof(f401,plain,(
% 0.20/0.52    $false | (~spl8_1 | ~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_15)),
% 0.20/0.52    inference(subsumption_resolution,[],[f400,f61])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    l1_pre_topc(sK0) | ~spl8_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f59])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    spl8_1 <=> l1_pre_topc(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.20/0.52  fof(f400,plain,(
% 0.20/0.52    ~l1_pre_topc(sK0) | (~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_15)),
% 0.20/0.52    inference(subsumption_resolution,[],[f399,f96])).
% 0.20/0.52  fof(f96,plain,(
% 0.20/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl8_6),
% 0.20/0.52    inference(avatar_component_clause,[],[f94])).
% 0.20/0.52  fof(f94,plain,(
% 0.20/0.52    spl8_6 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.20/0.52  fof(f399,plain,(
% 0.20/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl8_4 | ~spl8_5 | ~spl8_15)),
% 0.20/0.52    inference(subsumption_resolution,[],[f398,f76])).
% 0.20/0.52  fof(f76,plain,(
% 0.20/0.52    m1_pre_topc(sK2,sK0) | ~spl8_4),
% 0.20/0.52    inference(avatar_component_clause,[],[f74])).
% 0.20/0.52  fof(f74,plain,(
% 0.20/0.52    spl8_4 <=> m1_pre_topc(sK2,sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.20/0.52  fof(f398,plain,(
% 0.20/0.52    ~m1_pre_topc(sK2,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl8_5 | ~spl8_15)),
% 0.20/0.52    inference(resolution,[],[f294,f81])).
% 0.20/0.52  fof(f81,plain,(
% 0.20/0.52    v4_pre_topc(sK1,sK0) | ~spl8_5),
% 0.20/0.52    inference(avatar_component_clause,[],[f79])).
% 0.20/0.52  fof(f79,plain,(
% 0.20/0.52    spl8_5 <=> v4_pre_topc(sK1,sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.20/0.52  fof(f294,plain,(
% 0.20/0.52    ( ! [X1] : (~v4_pre_topc(sK1,X1) | ~m1_pre_topc(sK2,X1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1)) ) | ~spl8_15),
% 0.20/0.52    inference(avatar_component_clause,[],[f293])).
% 0.20/0.52  fof(f293,plain,(
% 0.20/0.52    spl8_15 <=> ! [X1] : (~m1_pre_topc(sK2,X1) | ~v4_pre_topc(sK1,X1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.20/0.52  fof(f391,plain,(
% 0.20/0.52    sK1 != k3_xboole_0(sK1,k2_struct_0(sK2)) | sK1 != sK3 | v4_pre_topc(sK3,sK2) | ~v4_pre_topc(k3_xboole_0(sK1,k2_struct_0(sK2)),sK2)),
% 0.20/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.52  fof(f390,plain,(
% 0.20/0.52    sK1 != k3_xboole_0(sK1,k2_struct_0(sK2)) | m1_subset_1(k3_xboole_0(sK1,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.20/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.52  fof(f389,plain,(
% 0.20/0.52    spl8_25 | ~spl8_22),
% 0.20/0.52    inference(avatar_split_clause,[],[f369,f364,f386])).
% 0.20/0.52  fof(f386,plain,(
% 0.20/0.52    spl8_25 <=> sK1 = k3_xboole_0(sK1,k2_struct_0(sK2))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 0.20/0.52  fof(f364,plain,(
% 0.20/0.52    spl8_22 <=> r1_tarski(sK1,k2_struct_0(sK2))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 0.20/0.52  fof(f369,plain,(
% 0.20/0.52    sK1 = k3_xboole_0(sK1,k2_struct_0(sK2)) | ~spl8_22),
% 0.20/0.52    inference(resolution,[],[f366,f49])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.52  fof(f366,plain,(
% 0.20/0.52    r1_tarski(sK1,k2_struct_0(sK2)) | ~spl8_22),
% 0.20/0.52    inference(avatar_component_clause,[],[f364])).
% 0.20/0.52  fof(f367,plain,(
% 0.20/0.52    spl8_22 | ~spl8_8 | ~spl8_9 | ~spl8_12 | ~spl8_18),
% 0.20/0.52    inference(avatar_split_clause,[],[f361,f323,f241,f115,f104,f364])).
% 0.20/0.52  fof(f104,plain,(
% 0.20/0.52    spl8_8 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.20/0.52  fof(f115,plain,(
% 0.20/0.52    spl8_9 <=> l1_pre_topc(sK2)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.20/0.52  fof(f241,plain,(
% 0.20/0.52    spl8_12 <=> l1_pre_topc(k1_pre_topc(sK2,sK1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.20/0.52  fof(f323,plain,(
% 0.20/0.52    spl8_18 <=> sK1 = k2_struct_0(k1_pre_topc(sK2,sK1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.20/0.52  fof(f361,plain,(
% 0.20/0.52    r1_tarski(sK1,k2_struct_0(sK2)) | (~spl8_8 | ~spl8_9 | ~spl8_12 | ~spl8_18)),
% 0.20/0.52    inference(subsumption_resolution,[],[f360,f106])).
% 0.20/0.52  fof(f106,plain,(
% 0.20/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK2))) | ~spl8_8),
% 0.20/0.52    inference(avatar_component_clause,[],[f104])).
% 0.20/0.52  fof(f360,plain,(
% 0.20/0.52    r1_tarski(sK1,k2_struct_0(sK2)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK2))) | (~spl8_9 | ~spl8_12 | ~spl8_18)),
% 0.20/0.52    inference(subsumption_resolution,[],[f359,f117])).
% 0.20/0.52  fof(f117,plain,(
% 0.20/0.52    l1_pre_topc(sK2) | ~spl8_9),
% 0.20/0.52    inference(avatar_component_clause,[],[f115])).
% 0.20/0.52  fof(f359,plain,(
% 0.20/0.52    ~l1_pre_topc(sK2) | r1_tarski(sK1,k2_struct_0(sK2)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK2))) | (~spl8_9 | ~spl8_12 | ~spl8_18)),
% 0.20/0.52    inference(resolution,[],[f336,f127])).
% 0.20/0.52  fof(f127,plain,(
% 0.20/0.52    ( ! [X11] : (m1_pre_topc(k1_pre_topc(sK2,X11),sK2) | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK2)))) ) | ~spl8_9),
% 0.20/0.52    inference(resolution,[],[f117,f51])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_pre_topc(k1_pre_topc(X0,X1),X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(flattening,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).
% 0.20/0.52  fof(f336,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_pre_topc(k1_pre_topc(sK2,sK1),X0) | ~l1_pre_topc(X0) | r1_tarski(sK1,k2_struct_0(X0))) ) | (~spl8_12 | ~spl8_18)),
% 0.20/0.52    inference(subsumption_resolution,[],[f328,f243])).
% 0.20/0.52  fof(f243,plain,(
% 0.20/0.52    l1_pre_topc(k1_pre_topc(sK2,sK1)) | ~spl8_12),
% 0.20/0.52    inference(avatar_component_clause,[],[f241])).
% 0.20/0.52  fof(f328,plain,(
% 0.20/0.52    ( ! [X0] : (r1_tarski(sK1,k2_struct_0(X0)) | ~l1_pre_topc(k1_pre_topc(sK2,sK1)) | ~l1_pre_topc(X0) | ~m1_pre_topc(k1_pre_topc(sK2,sK1),X0)) ) | ~spl8_18),
% 0.20/0.52    inference(superposition,[],[f40,f325])).
% 0.20/0.52  fof(f325,plain,(
% 0.20/0.52    sK1 = k2_struct_0(k1_pre_topc(sK2,sK1)) | ~spl8_18),
% 0.20/0.52    inference(avatar_component_clause,[],[f323])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_pre_topc)).
% 0.20/0.52  fof(f326,plain,(
% 0.20/0.52    spl8_18 | ~spl8_8 | ~spl8_9),
% 0.20/0.52    inference(avatar_split_clause,[],[f316,f115,f104,f323])).
% 0.20/0.52  fof(f316,plain,(
% 0.20/0.52    sK1 = k2_struct_0(k1_pre_topc(sK2,sK1)) | (~spl8_8 | ~spl8_9)),
% 0.20/0.52    inference(resolution,[],[f315,f106])).
% 0.20/0.52  fof(f315,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | k2_struct_0(k1_pre_topc(sK2,X0)) = X0) ) | ~spl8_9),
% 0.20/0.52    inference(subsumption_resolution,[],[f195,f127])).
% 0.20/0.52  fof(f195,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_pre_topc(k1_pre_topc(sK2,X0),sK2) | k2_struct_0(k1_pre_topc(sK2,X0)) = X0) ) | ~spl8_9),
% 0.20/0.52    inference(subsumption_resolution,[],[f194,f117])).
% 0.20/0.52  fof(f194,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2) | ~m1_pre_topc(k1_pre_topc(sK2,X0),sK2) | k2_struct_0(k1_pre_topc(sK2,X0)) = X0) ) | ~spl8_9),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f193])).
% 0.20/0.52  fof(f193,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2) | ~m1_pre_topc(k1_pre_topc(sK2,X0),sK2) | k2_struct_0(k1_pre_topc(sK2,X0)) = X0) ) | ~spl8_9),
% 0.20/0.52    inference(resolution,[],[f126,f56])).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_pre_topc(k1_pre_topc(X0,X1),X0) | k2_struct_0(k1_pre_topc(X0,X1)) = X1) )),
% 0.20/0.52    inference(equality_resolution,[],[f47])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_pre_topc(X2) | ~m1_pre_topc(X2,X0) | k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2) )),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(flattening,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2)) => (k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_pre_topc)).
% 0.20/0.52  fof(f126,plain,(
% 0.20/0.52    ( ! [X10] : (v1_pre_topc(k1_pre_topc(sK2,X10)) | ~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK2)))) ) | ~spl8_9),
% 0.20/0.52    inference(resolution,[],[f117,f50])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_pre_topc(k1_pre_topc(X0,X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f303,plain,(
% 0.20/0.52    spl8_15 | ~spl8_16 | spl8_17 | ~spl8_8),
% 0.20/0.52    inference(avatar_split_clause,[],[f180,f104,f300,f296,f293])).
% 0.20/0.52  fof(f296,plain,(
% 0.20/0.52    spl8_16 <=> m1_subset_1(k3_xboole_0(sK1,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.20/0.52  fof(f300,plain,(
% 0.20/0.52    spl8_17 <=> v4_pre_topc(k3_xboole_0(sK1,k2_struct_0(sK2)),sK2)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.20/0.52  fof(f180,plain,(
% 0.20/0.52    ( ! [X1] : (v4_pre_topc(k3_xboole_0(sK1,k2_struct_0(sK2)),sK2) | ~m1_subset_1(k3_xboole_0(sK1,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_pre_topc(sK2,X1) | ~l1_pre_topc(X1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(sK1,X1)) ) | ~spl8_8),
% 0.20/0.52    inference(forward_demodulation,[],[f179,f48])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.52  fof(f179,plain,(
% 0.20/0.52    ( ! [X1] : (~m1_subset_1(k3_xboole_0(sK1,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_pre_topc(sK2,X1) | ~l1_pre_topc(X1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(sK1,X1) | v4_pre_topc(k3_xboole_0(k2_struct_0(sK2),sK1),sK2)) ) | ~spl8_8),
% 0.20/0.52    inference(forward_demodulation,[],[f177,f48])).
% 0.20/0.52  fof(f177,plain,(
% 0.20/0.52    ( ! [X1] : (~m1_subset_1(k3_xboole_0(k2_struct_0(sK2),sK1),k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_pre_topc(sK2,X1) | ~l1_pre_topc(X1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(sK1,X1) | v4_pre_topc(k3_xboole_0(k2_struct_0(sK2),sK1),sK2)) ) | ~spl8_8),
% 0.20/0.52    inference(superposition,[],[f55,f138])).
% 0.20/0.52  fof(f138,plain,(
% 0.20/0.52    ( ! [X1] : (k3_xboole_0(X1,sK1) = k9_subset_1(u1_struct_0(sK2),sK1,X1)) ) | ~spl8_8),
% 0.20/0.52    inference(subsumption_resolution,[],[f134,f106])).
% 0.20/0.52  fof(f134,plain,(
% 0.20/0.52    ( ! [X1] : (k3_xboole_0(X1,sK1) = k9_subset_1(u1_struct_0(sK2),sK1,X1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK2)))) ) | ~spl8_8),
% 0.20/0.52    inference(superposition,[],[f109,f52])).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.20/0.52  fof(f109,plain,(
% 0.20/0.52    ( ! [X0] : (k9_subset_1(u1_struct_0(sK2),X0,sK1) = k9_subset_1(u1_struct_0(sK2),sK1,X0)) ) | ~spl8_8),
% 0.20/0.52    inference(resolution,[],[f106,f53])).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).
% 0.20/0.52  fof(f55,plain,(
% 0.20/0.52    ( ! [X0,X3,X1] : (~m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X3,X0) | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1)) )),
% 0.20/0.52    inference(equality_resolution,[],[f45])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X3,X0) | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | v4_pre_topc(X2,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : ((v4_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (v4_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_pre_topc)).
% 0.20/0.52  fof(f244,plain,(
% 0.20/0.52    spl8_12 | ~spl8_8 | ~spl8_9),
% 0.20/0.52    inference(avatar_split_clause,[],[f234,f115,f104,f241])).
% 0.20/0.52  fof(f234,plain,(
% 0.20/0.52    l1_pre_topc(k1_pre_topc(sK2,sK1)) | (~spl8_8 | ~spl8_9)),
% 0.20/0.52    inference(resolution,[],[f233,f106])).
% 0.20/0.52  fof(f233,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | l1_pre_topc(k1_pre_topc(sK2,X0))) ) | ~spl8_9),
% 0.20/0.52    inference(resolution,[],[f127,f123])).
% 0.20/0.52  fof(f123,plain,(
% 0.20/0.52    ( ! [X5] : (~m1_pre_topc(X5,sK2) | l1_pre_topc(X5)) ) | ~spl8_9),
% 0.20/0.52    inference(resolution,[],[f117,f41])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.52  fof(f118,plain,(
% 0.20/0.52    spl8_9 | ~spl8_1 | ~spl8_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f110,f74,f59,f115])).
% 0.20/0.52  fof(f110,plain,(
% 0.20/0.52    l1_pre_topc(sK2) | (~spl8_1 | ~spl8_4)),
% 0.20/0.52    inference(resolution,[],[f86,f76])).
% 0.20/0.52  fof(f86,plain,(
% 0.20/0.52    ( ! [X5] : (~m1_pre_topc(X5,sK0) | l1_pre_topc(X5)) ) | ~spl8_1),
% 0.20/0.52    inference(resolution,[],[f61,f41])).
% 0.20/0.52  fof(f107,plain,(
% 0.20/0.52    spl8_8 | ~spl8_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f92,f64,f104])).
% 0.20/0.52  fof(f64,plain,(
% 0.20/0.52    spl8_2 <=> sK1 = sK3),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.20/0.52  fof(f92,plain,(
% 0.20/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK2))) | ~spl8_2),
% 0.20/0.52    inference(forward_demodulation,[],[f24,f66])).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    sK1 = sK3 | ~spl8_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f64])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.20/0.52    inference(cnf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.52    inference(flattening,[],[f12])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((~v4_pre_topc(X3,X2) & X1 = X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,X0)) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,negated_conjecture,(
% 0.20/0.52    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v4_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v4_pre_topc(X3,X2)))))))),
% 0.20/0.52    inference(negated_conjecture,[],[f10])).
% 0.20/0.52  fof(f10,conjecture,(
% 0.20/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v4_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v4_pre_topc(X3,X2)))))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tops_2)).
% 0.20/0.52  fof(f97,plain,(
% 0.20/0.52    spl8_6),
% 0.20/0.52    inference(avatar_split_clause,[],[f29,f94])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.52    inference(cnf_transformation,[],[f13])).
% 0.20/0.52  fof(f82,plain,(
% 0.20/0.52    spl8_5),
% 0.20/0.52    inference(avatar_split_clause,[],[f28,f79])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    v4_pre_topc(sK1,sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f13])).
% 0.20/0.52  fof(f77,plain,(
% 0.20/0.52    spl8_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f27,f74])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    m1_pre_topc(sK2,sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f13])).
% 0.20/0.52  fof(f72,plain,(
% 0.20/0.52    ~spl8_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f26,f69])).
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    spl8_3 <=> v4_pre_topc(sK3,sK2)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ~v4_pre_topc(sK3,sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f13])).
% 0.20/0.52  fof(f67,plain,(
% 0.20/0.52    spl8_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f25,f64])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    sK1 = sK3),
% 0.20/0.52    inference(cnf_transformation,[],[f13])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    spl8_1),
% 0.20/0.52    inference(avatar_split_clause,[],[f30,f59])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    l1_pre_topc(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f13])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (19798)------------------------------
% 0.20/0.52  % (19798)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (19798)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (19798)Memory used [KB]: 10874
% 0.20/0.52  % (19798)Time elapsed: 0.101 s
% 0.20/0.52  % (19798)------------------------------
% 0.20/0.52  % (19798)------------------------------
% 0.20/0.52  % (19814)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.52  % (19794)Success in time 0.161 s
%------------------------------------------------------------------------------
