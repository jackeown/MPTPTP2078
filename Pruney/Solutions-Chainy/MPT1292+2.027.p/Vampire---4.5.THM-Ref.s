%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:14 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 185 expanded)
%              Number of leaves         :   29 (  86 expanded)
%              Depth                    :    7
%              Number of atoms          :  292 ( 579 expanded)
%              Number of equality atoms :   44 ( 104 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f187,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f48,f53,f58,f63,f68,f72,f76,f80,f84,f92,f96,f116,f123,f129,f143,f151,f171,f180,f186])).

fof(f186,plain,
    ( ~ spl2_6
    | spl2_24
    | ~ spl2_25 ),
    inference(avatar_contradiction_clause,[],[f185])).

fof(f185,plain,
    ( $false
    | ~ spl2_6
    | spl2_24
    | ~ spl2_25 ),
    inference(subsumption_resolution,[],[f182,f67])).

fof(f67,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl2_6
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f182,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl2_24
    | ~ spl2_25 ),
    inference(superposition,[],[f170,f179])).

fof(f179,plain,
    ( k1_xboole_0 = k3_tarski(k1_xboole_0)
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl2_25
  <=> k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f170,plain,
    ( ~ v1_xboole_0(k3_tarski(k1_xboole_0))
    | spl2_24 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl2_24
  <=> v1_xboole_0(k3_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f180,plain,
    ( spl2_25
    | ~ spl2_17
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f173,f141,f114,f177])).

fof(f114,plain,
    ( spl2_17
  <=> ! [X0] : m1_setfam_1(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f141,plain,
    ( spl2_21
  <=> ! [X0] :
        ( k3_tarski(k1_xboole_0) = X0
        | ~ m1_setfam_1(k1_xboole_0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f173,plain,
    ( k1_xboole_0 = k3_tarski(k1_xboole_0)
    | ~ spl2_17
    | ~ spl2_21 ),
    inference(resolution,[],[f142,f115])).

fof(f115,plain,
    ( ! [X0] : m1_setfam_1(X0,k1_xboole_0)
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f114])).

fof(f142,plain,
    ( ! [X0] :
        ( ~ m1_setfam_1(k1_xboole_0,X0)
        | k3_tarski(k1_xboole_0) = X0 )
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f141])).

fof(f171,plain,
    ( ~ spl2_24
    | ~ spl2_4
    | spl2_5
    | ~ spl2_9
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f166,f148,f78,f60,f55,f168])).

fof(f55,plain,
    ( spl2_4
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f60,plain,
    ( spl2_5
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f78,plain,
    ( spl2_9
  <=> ! [X0] :
        ( ~ v1_xboole_0(u1_struct_0(X0))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f148,plain,
    ( spl2_22
  <=> u1_struct_0(sK0) = k3_tarski(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f166,plain,
    ( ~ v1_xboole_0(k3_tarski(k1_xboole_0))
    | ~ spl2_4
    | spl2_5
    | ~ spl2_9
    | ~ spl2_22 ),
    inference(subsumption_resolution,[],[f165,f62])).

fof(f62,plain,
    ( ~ v2_struct_0(sK0)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f60])).

fof(f165,plain,
    ( ~ v1_xboole_0(k3_tarski(k1_xboole_0))
    | v2_struct_0(sK0)
    | ~ spl2_4
    | ~ spl2_9
    | ~ spl2_22 ),
    inference(subsumption_resolution,[],[f156,f57])).

fof(f57,plain,
    ( l1_struct_0(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f55])).

fof(f156,plain,
    ( ~ v1_xboole_0(k3_tarski(k1_xboole_0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl2_9
    | ~ spl2_22 ),
    inference(superposition,[],[f79,f150])).

fof(f150,plain,
    ( u1_struct_0(sK0) = k3_tarski(k1_xboole_0)
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f148])).

fof(f79,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(u1_struct_0(X0))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f78])).

fof(f151,plain,
    ( spl2_22
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_12
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f146,f126,f90,f50,f45,f40,f148])).

fof(f40,plain,
    ( spl2_1
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f45,plain,
    ( spl2_2
  <=> m1_setfam_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f50,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f90,plain,
    ( spl2_12
  <=> ! [X1,X0] :
        ( k5_setfam_1(X0,X1) = X0
        | ~ m1_setfam_1(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f126,plain,
    ( spl2_19
  <=> k3_tarski(k1_xboole_0) = k5_setfam_1(u1_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f146,plain,
    ( u1_struct_0(sK0) = k3_tarski(k1_xboole_0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_12
    | ~ spl2_19 ),
    inference(forward_demodulation,[],[f145,f128])).

fof(f128,plain,
    ( k3_tarski(k1_xboole_0) = k5_setfam_1(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f126])).

fof(f145,plain,
    ( u1_struct_0(sK0) = k5_setfam_1(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_12 ),
    inference(forward_demodulation,[],[f144,f42])).

fof(f42,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f144,plain,
    ( u1_struct_0(sK0) = k5_setfam_1(u1_struct_0(sK0),sK1)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_12 ),
    inference(subsumption_resolution,[],[f138,f47])).

fof(f47,plain,
    ( m1_setfam_1(sK1,u1_struct_0(sK0))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f138,plain,
    ( ~ m1_setfam_1(sK1,u1_struct_0(sK0))
    | u1_struct_0(sK0) = k5_setfam_1(u1_struct_0(sK0),sK1)
    | ~ spl2_3
    | ~ spl2_12 ),
    inference(resolution,[],[f91,f52])).

fof(f52,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f91,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | ~ m1_setfam_1(X1,X0)
        | k5_setfam_1(X0,X1) = X0 )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f90])).

fof(f143,plain,
    ( spl2_21
    | ~ spl2_8
    | ~ spl2_12
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f139,f121,f90,f74,f141])).

fof(f74,plain,
    ( spl2_8
  <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f121,plain,
    ( spl2_18
  <=> ! [X0] : k3_tarski(k1_xboole_0) = k5_setfam_1(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f139,plain,
    ( ! [X0] :
        ( k3_tarski(k1_xboole_0) = X0
        | ~ m1_setfam_1(k1_xboole_0,X0) )
    | ~ spl2_8
    | ~ spl2_12
    | ~ spl2_18 ),
    inference(forward_demodulation,[],[f137,f122])).

fof(f122,plain,
    ( ! [X0] : k3_tarski(k1_xboole_0) = k5_setfam_1(X0,k1_xboole_0)
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f121])).

fof(f137,plain,
    ( ! [X0] :
        ( ~ m1_setfam_1(k1_xboole_0,X0)
        | k5_setfam_1(X0,k1_xboole_0) = X0 )
    | ~ spl2_8
    | ~ spl2_12 ),
    inference(resolution,[],[f91,f75])).

fof(f75,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f74])).

fof(f129,plain,
    ( spl2_19
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f124,f82,f50,f40,f126])).

fof(f82,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( k3_tarski(X1) = k5_setfam_1(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f124,plain,
    ( k3_tarski(k1_xboole_0) = k5_setfam_1(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f119,f42])).

fof(f119,plain,
    ( k3_tarski(sK1) = k5_setfam_1(u1_struct_0(sK0),sK1)
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(resolution,[],[f83,f52])).

fof(f83,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | k3_tarski(X1) = k5_setfam_1(X0,X1) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f82])).

fof(f123,plain,
    ( spl2_18
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f118,f82,f74,f121])).

fof(f118,plain,
    ( ! [X0] : k3_tarski(k1_xboole_0) = k5_setfam_1(X0,k1_xboole_0)
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(resolution,[],[f83,f75])).

fof(f116,plain,
    ( spl2_17
    | ~ spl2_7
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f112,f94,f70,f114])).

fof(f70,plain,
    ( spl2_7
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f94,plain,
    ( spl2_13
  <=> ! [X1,X0] :
        ( m1_setfam_1(X1,X0)
        | ~ r1_tarski(X0,k3_tarski(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f112,plain,
    ( ! [X0] : m1_setfam_1(X0,k1_xboole_0)
    | ~ spl2_7
    | ~ spl2_13 ),
    inference(resolution,[],[f95,f71])).

fof(f71,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f70])).

fof(f95,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k3_tarski(X1))
        | m1_setfam_1(X1,X0) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f94])).

fof(f96,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f37,f94])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_setfam_1(X1,X0)
      | ~ r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( m1_setfam_1(X1,X0)
        | ~ r1_tarski(X0,k3_tarski(X1)) )
      & ( r1_tarski(X0,k3_tarski(X1))
        | ~ m1_setfam_1(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_setfam_1(X1,X0)
    <=> r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).

fof(f92,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f34,f90])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k5_setfam_1(X0,X1) = X0
      | ~ m1_setfam_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( m1_setfam_1(X1,X0)
          | k5_setfam_1(X0,X1) != X0 )
        & ( k5_setfam_1(X0,X1) = X0
          | ~ m1_setfam_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( m1_setfam_1(X1,X0)
      <=> k5_setfam_1(X0,X1) = X0 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( m1_setfam_1(X1,X0)
      <=> k5_setfam_1(X0,X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_setfam_1)).

fof(f84,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f33,f82])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(f80,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f32,f78])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f76,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f31,f74])).

fof(f31,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f72,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f30,f70])).

fof(f30,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f68,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f29,f65])).

fof(f29,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f63,plain,(
    ~ spl2_5 ),
    inference(avatar_split_clause,[],[f24,f60])).

fof(f24,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( k1_xboole_0 = sK1
    & m1_setfam_1(sK1,u1_struct_0(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f20,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_xboole_0 = X1
            & m1_setfam_1(X1,u1_struct_0(X0))
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k1_xboole_0 = X1
          & m1_setfam_1(X1,u1_struct_0(sK0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X1] :
        ( k1_xboole_0 = X1
        & m1_setfam_1(X1,u1_struct_0(sK0))
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( k1_xboole_0 = sK1
      & m1_setfam_1(sK1,u1_struct_0(sK0))
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = X1
          & m1_setfam_1(X1,u1_struct_0(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = X1
          & m1_setfam_1(X1,u1_struct_0(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ~ ( k1_xboole_0 = X1
                & m1_setfam_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ~ ( k1_xboole_0 = X1
              & m1_setfam_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_tops_2)).

fof(f58,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f25,f55])).

fof(f25,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f53,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f26,f50])).

fof(f26,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f21])).

fof(f48,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f27,f45])).

fof(f27,plain,(
    m1_setfam_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f43,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f28,f40])).

fof(f28,plain,(
    k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:33:39 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.39  % (29940)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.18/0.39  % (29945)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.18/0.40  % (29945)Refutation found. Thanks to Tanya!
% 0.18/0.40  % SZS status Theorem for theBenchmark
% 0.18/0.40  % SZS output start Proof for theBenchmark
% 0.18/0.40  fof(f187,plain,(
% 0.18/0.40    $false),
% 0.18/0.40    inference(avatar_sat_refutation,[],[f43,f48,f53,f58,f63,f68,f72,f76,f80,f84,f92,f96,f116,f123,f129,f143,f151,f171,f180,f186])).
% 0.18/0.40  fof(f186,plain,(
% 0.18/0.40    ~spl2_6 | spl2_24 | ~spl2_25),
% 0.18/0.40    inference(avatar_contradiction_clause,[],[f185])).
% 0.18/0.40  fof(f185,plain,(
% 0.18/0.40    $false | (~spl2_6 | spl2_24 | ~spl2_25)),
% 0.18/0.40    inference(subsumption_resolution,[],[f182,f67])).
% 0.18/0.40  fof(f67,plain,(
% 0.18/0.40    v1_xboole_0(k1_xboole_0) | ~spl2_6),
% 0.18/0.40    inference(avatar_component_clause,[],[f65])).
% 0.18/0.40  fof(f65,plain,(
% 0.18/0.40    spl2_6 <=> v1_xboole_0(k1_xboole_0)),
% 0.18/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.18/0.40  fof(f182,plain,(
% 0.18/0.40    ~v1_xboole_0(k1_xboole_0) | (spl2_24 | ~spl2_25)),
% 0.18/0.40    inference(superposition,[],[f170,f179])).
% 0.18/0.40  fof(f179,plain,(
% 0.18/0.40    k1_xboole_0 = k3_tarski(k1_xboole_0) | ~spl2_25),
% 0.18/0.40    inference(avatar_component_clause,[],[f177])).
% 0.18/0.40  fof(f177,plain,(
% 0.18/0.40    spl2_25 <=> k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.18/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.18/0.40  fof(f170,plain,(
% 0.18/0.40    ~v1_xboole_0(k3_tarski(k1_xboole_0)) | spl2_24),
% 0.18/0.40    inference(avatar_component_clause,[],[f168])).
% 0.18/0.40  fof(f168,plain,(
% 0.18/0.40    spl2_24 <=> v1_xboole_0(k3_tarski(k1_xboole_0))),
% 0.18/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.18/0.40  fof(f180,plain,(
% 0.18/0.40    spl2_25 | ~spl2_17 | ~spl2_21),
% 0.18/0.40    inference(avatar_split_clause,[],[f173,f141,f114,f177])).
% 0.18/0.40  fof(f114,plain,(
% 0.18/0.40    spl2_17 <=> ! [X0] : m1_setfam_1(X0,k1_xboole_0)),
% 0.18/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.18/0.40  fof(f141,plain,(
% 0.18/0.40    spl2_21 <=> ! [X0] : (k3_tarski(k1_xboole_0) = X0 | ~m1_setfam_1(k1_xboole_0,X0))),
% 0.18/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.18/0.40  fof(f173,plain,(
% 0.18/0.40    k1_xboole_0 = k3_tarski(k1_xboole_0) | (~spl2_17 | ~spl2_21)),
% 0.18/0.40    inference(resolution,[],[f142,f115])).
% 0.18/0.40  fof(f115,plain,(
% 0.18/0.40    ( ! [X0] : (m1_setfam_1(X0,k1_xboole_0)) ) | ~spl2_17),
% 0.18/0.40    inference(avatar_component_clause,[],[f114])).
% 0.18/0.40  fof(f142,plain,(
% 0.18/0.40    ( ! [X0] : (~m1_setfam_1(k1_xboole_0,X0) | k3_tarski(k1_xboole_0) = X0) ) | ~spl2_21),
% 0.18/0.40    inference(avatar_component_clause,[],[f141])).
% 0.18/0.40  fof(f171,plain,(
% 0.18/0.40    ~spl2_24 | ~spl2_4 | spl2_5 | ~spl2_9 | ~spl2_22),
% 0.18/0.40    inference(avatar_split_clause,[],[f166,f148,f78,f60,f55,f168])).
% 0.18/0.40  fof(f55,plain,(
% 0.18/0.40    spl2_4 <=> l1_struct_0(sK0)),
% 0.18/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.18/0.40  fof(f60,plain,(
% 0.18/0.40    spl2_5 <=> v2_struct_0(sK0)),
% 0.18/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.18/0.40  fof(f78,plain,(
% 0.18/0.40    spl2_9 <=> ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.18/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.18/0.40  fof(f148,plain,(
% 0.18/0.40    spl2_22 <=> u1_struct_0(sK0) = k3_tarski(k1_xboole_0)),
% 0.18/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.18/0.40  fof(f166,plain,(
% 0.18/0.40    ~v1_xboole_0(k3_tarski(k1_xboole_0)) | (~spl2_4 | spl2_5 | ~spl2_9 | ~spl2_22)),
% 0.18/0.40    inference(subsumption_resolution,[],[f165,f62])).
% 0.18/0.40  fof(f62,plain,(
% 0.18/0.40    ~v2_struct_0(sK0) | spl2_5),
% 0.18/0.40    inference(avatar_component_clause,[],[f60])).
% 0.18/0.40  fof(f165,plain,(
% 0.18/0.40    ~v1_xboole_0(k3_tarski(k1_xboole_0)) | v2_struct_0(sK0) | (~spl2_4 | ~spl2_9 | ~spl2_22)),
% 0.18/0.40    inference(subsumption_resolution,[],[f156,f57])).
% 0.18/0.40  fof(f57,plain,(
% 0.18/0.40    l1_struct_0(sK0) | ~spl2_4),
% 0.18/0.40    inference(avatar_component_clause,[],[f55])).
% 0.18/0.40  fof(f156,plain,(
% 0.18/0.40    ~v1_xboole_0(k3_tarski(k1_xboole_0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | (~spl2_9 | ~spl2_22)),
% 0.18/0.40    inference(superposition,[],[f79,f150])).
% 0.18/0.40  fof(f150,plain,(
% 0.18/0.40    u1_struct_0(sK0) = k3_tarski(k1_xboole_0) | ~spl2_22),
% 0.18/0.40    inference(avatar_component_clause,[],[f148])).
% 0.18/0.40  fof(f79,plain,(
% 0.18/0.40    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) ) | ~spl2_9),
% 0.18/0.40    inference(avatar_component_clause,[],[f78])).
% 0.18/0.40  fof(f151,plain,(
% 0.18/0.40    spl2_22 | ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_12 | ~spl2_19),
% 0.18/0.40    inference(avatar_split_clause,[],[f146,f126,f90,f50,f45,f40,f148])).
% 0.18/0.40  fof(f40,plain,(
% 0.18/0.40    spl2_1 <=> k1_xboole_0 = sK1),
% 0.18/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.18/0.40  fof(f45,plain,(
% 0.18/0.40    spl2_2 <=> m1_setfam_1(sK1,u1_struct_0(sK0))),
% 0.18/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.18/0.40  fof(f50,plain,(
% 0.18/0.40    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.18/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.18/0.40  fof(f90,plain,(
% 0.18/0.40    spl2_12 <=> ! [X1,X0] : (k5_setfam_1(X0,X1) = X0 | ~m1_setfam_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.18/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.18/0.40  fof(f126,plain,(
% 0.18/0.40    spl2_19 <=> k3_tarski(k1_xboole_0) = k5_setfam_1(u1_struct_0(sK0),k1_xboole_0)),
% 0.18/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.18/0.40  fof(f146,plain,(
% 0.18/0.40    u1_struct_0(sK0) = k3_tarski(k1_xboole_0) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_12 | ~spl2_19)),
% 0.18/0.40    inference(forward_demodulation,[],[f145,f128])).
% 0.18/0.40  fof(f128,plain,(
% 0.18/0.40    k3_tarski(k1_xboole_0) = k5_setfam_1(u1_struct_0(sK0),k1_xboole_0) | ~spl2_19),
% 0.18/0.40    inference(avatar_component_clause,[],[f126])).
% 0.18/0.40  fof(f145,plain,(
% 0.18/0.40    u1_struct_0(sK0) = k5_setfam_1(u1_struct_0(sK0),k1_xboole_0) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_12)),
% 0.18/0.40    inference(forward_demodulation,[],[f144,f42])).
% 0.18/0.40  fof(f42,plain,(
% 0.18/0.40    k1_xboole_0 = sK1 | ~spl2_1),
% 0.18/0.40    inference(avatar_component_clause,[],[f40])).
% 0.18/0.40  fof(f144,plain,(
% 0.18/0.40    u1_struct_0(sK0) = k5_setfam_1(u1_struct_0(sK0),sK1) | (~spl2_2 | ~spl2_3 | ~spl2_12)),
% 0.18/0.40    inference(subsumption_resolution,[],[f138,f47])).
% 0.18/0.40  fof(f47,plain,(
% 0.18/0.40    m1_setfam_1(sK1,u1_struct_0(sK0)) | ~spl2_2),
% 0.18/0.40    inference(avatar_component_clause,[],[f45])).
% 0.18/0.40  fof(f138,plain,(
% 0.18/0.40    ~m1_setfam_1(sK1,u1_struct_0(sK0)) | u1_struct_0(sK0) = k5_setfam_1(u1_struct_0(sK0),sK1) | (~spl2_3 | ~spl2_12)),
% 0.18/0.40    inference(resolution,[],[f91,f52])).
% 0.18/0.40  fof(f52,plain,(
% 0.18/0.40    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl2_3),
% 0.18/0.40    inference(avatar_component_clause,[],[f50])).
% 0.18/0.40  fof(f91,plain,(
% 0.18/0.40    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_setfam_1(X1,X0) | k5_setfam_1(X0,X1) = X0) ) | ~spl2_12),
% 0.18/0.40    inference(avatar_component_clause,[],[f90])).
% 0.18/0.40  fof(f143,plain,(
% 0.18/0.40    spl2_21 | ~spl2_8 | ~spl2_12 | ~spl2_18),
% 0.18/0.40    inference(avatar_split_clause,[],[f139,f121,f90,f74,f141])).
% 0.18/0.40  fof(f74,plain,(
% 0.18/0.40    spl2_8 <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.18/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.18/0.40  fof(f121,plain,(
% 0.18/0.40    spl2_18 <=> ! [X0] : k3_tarski(k1_xboole_0) = k5_setfam_1(X0,k1_xboole_0)),
% 0.18/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.18/0.40  fof(f139,plain,(
% 0.18/0.40    ( ! [X0] : (k3_tarski(k1_xboole_0) = X0 | ~m1_setfam_1(k1_xboole_0,X0)) ) | (~spl2_8 | ~spl2_12 | ~spl2_18)),
% 0.18/0.40    inference(forward_demodulation,[],[f137,f122])).
% 0.18/0.40  fof(f122,plain,(
% 0.18/0.40    ( ! [X0] : (k3_tarski(k1_xboole_0) = k5_setfam_1(X0,k1_xboole_0)) ) | ~spl2_18),
% 0.18/0.40    inference(avatar_component_clause,[],[f121])).
% 0.18/0.40  fof(f137,plain,(
% 0.18/0.40    ( ! [X0] : (~m1_setfam_1(k1_xboole_0,X0) | k5_setfam_1(X0,k1_xboole_0) = X0) ) | (~spl2_8 | ~spl2_12)),
% 0.18/0.40    inference(resolution,[],[f91,f75])).
% 0.18/0.40  fof(f75,plain,(
% 0.18/0.40    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl2_8),
% 0.18/0.40    inference(avatar_component_clause,[],[f74])).
% 0.18/0.40  fof(f129,plain,(
% 0.18/0.40    spl2_19 | ~spl2_1 | ~spl2_3 | ~spl2_10),
% 0.18/0.40    inference(avatar_split_clause,[],[f124,f82,f50,f40,f126])).
% 0.18/0.40  fof(f82,plain,(
% 0.18/0.40    spl2_10 <=> ! [X1,X0] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.18/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.18/0.40  fof(f124,plain,(
% 0.18/0.40    k3_tarski(k1_xboole_0) = k5_setfam_1(u1_struct_0(sK0),k1_xboole_0) | (~spl2_1 | ~spl2_3 | ~spl2_10)),
% 0.18/0.40    inference(forward_demodulation,[],[f119,f42])).
% 0.18/0.40  fof(f119,plain,(
% 0.18/0.40    k3_tarski(sK1) = k5_setfam_1(u1_struct_0(sK0),sK1) | (~spl2_3 | ~spl2_10)),
% 0.18/0.40    inference(resolution,[],[f83,f52])).
% 0.18/0.40  fof(f83,plain,(
% 0.18/0.40    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k3_tarski(X1) = k5_setfam_1(X0,X1)) ) | ~spl2_10),
% 0.18/0.40    inference(avatar_component_clause,[],[f82])).
% 0.18/0.40  fof(f123,plain,(
% 0.18/0.40    spl2_18 | ~spl2_8 | ~spl2_10),
% 0.18/0.40    inference(avatar_split_clause,[],[f118,f82,f74,f121])).
% 0.18/0.40  fof(f118,plain,(
% 0.18/0.40    ( ! [X0] : (k3_tarski(k1_xboole_0) = k5_setfam_1(X0,k1_xboole_0)) ) | (~spl2_8 | ~spl2_10)),
% 0.18/0.40    inference(resolution,[],[f83,f75])).
% 0.18/0.40  fof(f116,plain,(
% 0.18/0.40    spl2_17 | ~spl2_7 | ~spl2_13),
% 0.18/0.40    inference(avatar_split_clause,[],[f112,f94,f70,f114])).
% 0.18/0.40  fof(f70,plain,(
% 0.18/0.40    spl2_7 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.18/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.18/0.40  fof(f94,plain,(
% 0.18/0.40    spl2_13 <=> ! [X1,X0] : (m1_setfam_1(X1,X0) | ~r1_tarski(X0,k3_tarski(X1)))),
% 0.18/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.18/0.40  fof(f112,plain,(
% 0.18/0.40    ( ! [X0] : (m1_setfam_1(X0,k1_xboole_0)) ) | (~spl2_7 | ~spl2_13)),
% 0.18/0.40    inference(resolution,[],[f95,f71])).
% 0.18/0.40  fof(f71,plain,(
% 0.18/0.40    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl2_7),
% 0.18/0.40    inference(avatar_component_clause,[],[f70])).
% 0.18/0.40  fof(f95,plain,(
% 0.18/0.40    ( ! [X0,X1] : (~r1_tarski(X0,k3_tarski(X1)) | m1_setfam_1(X1,X0)) ) | ~spl2_13),
% 0.18/0.40    inference(avatar_component_clause,[],[f94])).
% 0.18/0.40  fof(f96,plain,(
% 0.18/0.40    spl2_13),
% 0.18/0.40    inference(avatar_split_clause,[],[f37,f94])).
% 0.18/0.40  fof(f37,plain,(
% 0.18/0.40    ( ! [X0,X1] : (m1_setfam_1(X1,X0) | ~r1_tarski(X0,k3_tarski(X1))) )),
% 0.18/0.40    inference(cnf_transformation,[],[f23])).
% 0.18/0.40  fof(f23,plain,(
% 0.18/0.40    ! [X0,X1] : ((m1_setfam_1(X1,X0) | ~r1_tarski(X0,k3_tarski(X1))) & (r1_tarski(X0,k3_tarski(X1)) | ~m1_setfam_1(X1,X0)))),
% 0.18/0.40    inference(nnf_transformation,[],[f4])).
% 0.18/0.40  fof(f4,axiom,(
% 0.18/0.40    ! [X0,X1] : (m1_setfam_1(X1,X0) <=> r1_tarski(X0,k3_tarski(X1)))),
% 0.18/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).
% 0.18/0.40  fof(f92,plain,(
% 0.18/0.40    spl2_12),
% 0.18/0.40    inference(avatar_split_clause,[],[f34,f90])).
% 0.18/0.40  fof(f34,plain,(
% 0.18/0.40    ( ! [X0,X1] : (k5_setfam_1(X0,X1) = X0 | ~m1_setfam_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.18/0.40    inference(cnf_transformation,[],[f22])).
% 0.18/0.40  fof(f22,plain,(
% 0.18/0.40    ! [X0,X1] : (((m1_setfam_1(X1,X0) | k5_setfam_1(X0,X1) != X0) & (k5_setfam_1(X0,X1) = X0 | ~m1_setfam_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.18/0.40    inference(nnf_transformation,[],[f16])).
% 0.18/0.40  fof(f16,plain,(
% 0.18/0.40    ! [X0,X1] : ((m1_setfam_1(X1,X0) <=> k5_setfam_1(X0,X1) = X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.18/0.40    inference(ennf_transformation,[],[f7])).
% 0.18/0.40  fof(f7,axiom,(
% 0.18/0.40    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (m1_setfam_1(X1,X0) <=> k5_setfam_1(X0,X1) = X0))),
% 0.18/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_setfam_1)).
% 0.18/0.40  fof(f84,plain,(
% 0.18/0.40    spl2_10),
% 0.18/0.40    inference(avatar_split_clause,[],[f33,f82])).
% 0.18/0.40  fof(f33,plain,(
% 0.18/0.40    ( ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.18/0.40    inference(cnf_transformation,[],[f15])).
% 0.18/0.40  fof(f15,plain,(
% 0.18/0.40    ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.18/0.40    inference(ennf_transformation,[],[f5])).
% 0.18/0.40  fof(f5,axiom,(
% 0.18/0.40    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k3_tarski(X1) = k5_setfam_1(X0,X1))),
% 0.18/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).
% 0.18/0.40  fof(f80,plain,(
% 0.18/0.40    spl2_9),
% 0.18/0.40    inference(avatar_split_clause,[],[f32,f78])).
% 0.18/0.40  fof(f32,plain,(
% 0.18/0.40    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.18/0.40    inference(cnf_transformation,[],[f14])).
% 0.18/0.40  fof(f14,plain,(
% 0.18/0.40    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.18/0.40    inference(flattening,[],[f13])).
% 0.18/0.40  fof(f13,plain,(
% 0.18/0.40    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.18/0.40    inference(ennf_transformation,[],[f8])).
% 0.18/0.40  fof(f8,axiom,(
% 0.18/0.40    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.18/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.18/0.40  fof(f76,plain,(
% 0.18/0.40    spl2_8),
% 0.18/0.40    inference(avatar_split_clause,[],[f31,f74])).
% 0.18/0.40  fof(f31,plain,(
% 0.18/0.40    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.18/0.40    inference(cnf_transformation,[],[f3])).
% 0.18/0.40  fof(f3,axiom,(
% 0.18/0.40    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.18/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.18/0.40  fof(f72,plain,(
% 0.18/0.40    spl2_7),
% 0.18/0.40    inference(avatar_split_clause,[],[f30,f70])).
% 0.18/0.40  fof(f30,plain,(
% 0.18/0.40    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.18/0.40    inference(cnf_transformation,[],[f2])).
% 0.18/0.40  fof(f2,axiom,(
% 0.18/0.40    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.18/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.18/0.40  fof(f68,plain,(
% 0.18/0.40    spl2_6),
% 0.18/0.40    inference(avatar_split_clause,[],[f29,f65])).
% 0.18/0.40  fof(f29,plain,(
% 0.18/0.40    v1_xboole_0(k1_xboole_0)),
% 0.18/0.40    inference(cnf_transformation,[],[f1])).
% 0.18/0.40  fof(f1,axiom,(
% 0.18/0.40    v1_xboole_0(k1_xboole_0)),
% 0.18/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.18/0.40  fof(f63,plain,(
% 0.18/0.40    ~spl2_5),
% 0.18/0.40    inference(avatar_split_clause,[],[f24,f60])).
% 0.18/0.40  fof(f24,plain,(
% 0.18/0.40    ~v2_struct_0(sK0)),
% 0.18/0.40    inference(cnf_transformation,[],[f21])).
% 0.18/0.40  fof(f21,plain,(
% 0.18/0.40    (k1_xboole_0 = sK1 & m1_setfam_1(sK1,u1_struct_0(sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_struct_0(sK0) & ~v2_struct_0(sK0)),
% 0.18/0.40    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f20,f19])).
% 0.18/0.40  fof(f19,plain,(
% 0.18/0.40    ? [X0] : (? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(sK0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_struct_0(sK0) & ~v2_struct_0(sK0))),
% 0.18/0.40    introduced(choice_axiom,[])).
% 0.18/0.40  fof(f20,plain,(
% 0.18/0.40    ? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(sK0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (k1_xboole_0 = sK1 & m1_setfam_1(sK1,u1_struct_0(sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.18/0.40    introduced(choice_axiom,[])).
% 0.18/0.40  fof(f12,plain,(
% 0.18/0.40    ? [X0] : (? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.18/0.40    inference(flattening,[],[f11])).
% 0.18/0.40  fof(f11,plain,(
% 0.18/0.40    ? [X0] : (? [X1] : ((k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.18/0.40    inference(ennf_transformation,[],[f10])).
% 0.18/0.40  fof(f10,negated_conjecture,(
% 0.18/0.40    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0)))))),
% 0.18/0.40    inference(negated_conjecture,[],[f9])).
% 0.18/0.40  fof(f9,conjecture,(
% 0.18/0.40    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0)))))),
% 0.18/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_tops_2)).
% 0.18/0.40  fof(f58,plain,(
% 0.18/0.40    spl2_4),
% 0.18/0.40    inference(avatar_split_clause,[],[f25,f55])).
% 0.18/0.40  fof(f25,plain,(
% 0.18/0.40    l1_struct_0(sK0)),
% 0.18/0.40    inference(cnf_transformation,[],[f21])).
% 0.18/0.40  fof(f53,plain,(
% 0.18/0.40    spl2_3),
% 0.18/0.40    inference(avatar_split_clause,[],[f26,f50])).
% 0.18/0.40  fof(f26,plain,(
% 0.18/0.40    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.18/0.40    inference(cnf_transformation,[],[f21])).
% 0.18/0.40  fof(f48,plain,(
% 0.18/0.40    spl2_2),
% 0.18/0.40    inference(avatar_split_clause,[],[f27,f45])).
% 0.18/0.40  fof(f27,plain,(
% 0.18/0.40    m1_setfam_1(sK1,u1_struct_0(sK0))),
% 0.18/0.40    inference(cnf_transformation,[],[f21])).
% 0.18/0.40  fof(f43,plain,(
% 0.18/0.40    spl2_1),
% 0.18/0.40    inference(avatar_split_clause,[],[f28,f40])).
% 0.18/0.40  fof(f28,plain,(
% 0.18/0.40    k1_xboole_0 = sK1),
% 0.18/0.40    inference(cnf_transformation,[],[f21])).
% 0.18/0.40  % SZS output end Proof for theBenchmark
% 0.18/0.40  % (29945)------------------------------
% 0.18/0.40  % (29945)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.40  % (29945)Termination reason: Refutation
% 0.18/0.40  
% 0.18/0.40  % (29945)Memory used [KB]: 10618
% 0.18/0.40  % (29945)Time elapsed: 0.005 s
% 0.18/0.40  % (29945)------------------------------
% 0.18/0.40  % (29945)------------------------------
% 0.18/0.40  % (29939)Success in time 0.055 s
%------------------------------------------------------------------------------
