%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:38 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 268 expanded)
%              Number of leaves         :   25 ( 102 expanded)
%              Depth                    :   13
%              Number of atoms          :  414 (1039 expanded)
%              Number of equality atoms :  124 ( 382 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f252,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f63,f68,f73,f84,f103,f116,f167,f172,f181,f186,f206,f211,f222,f237,f243,f251])).

fof(f251,plain,
    ( ~ spl4_9
    | ~ spl4_11
    | spl4_23
    | ~ spl4_24 ),
    inference(avatar_contradiction_clause,[],[f250])).

fof(f250,plain,
    ( $false
    | ~ spl4_9
    | ~ spl4_11
    | spl4_23
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f249,f101])).

fof(f101,plain,
    ( m1_subset_1(k1_xboole_0,k1_tarski(k1_xboole_0))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl4_9
  <=> m1_subset_1(k1_xboole_0,k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f249,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_tarski(k1_xboole_0))
    | ~ spl4_11
    | spl4_23
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f247,f236])).

fof(f236,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl4_23 ),
    inference(avatar_component_clause,[],[f234])).

fof(f234,plain,
    ( spl4_23
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f247,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_tarski(k1_xboole_0))
    | ~ spl4_11
    | ~ spl4_24 ),
    inference(trivial_inequality_removal,[],[f245])).

fof(f245,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_tarski(k1_xboole_0))
    | ~ spl4_11
    | ~ spl4_24 ),
    inference(superposition,[],[f115,f242])).

fof(f242,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f240])).

fof(f240,plain,
    ( spl4_24
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f115,plain,
    ( ! [X2,X1] :
        ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
        | v1_funct_2(X2,k1_xboole_0,X1)
        | ~ m1_subset_1(X2,k1_tarski(k1_xboole_0)) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl4_11
  <=> ! [X1,X2] :
        ( ~ m1_subset_1(X2,k1_tarski(k1_xboole_0))
        | v1_funct_2(X2,k1_xboole_0,X1)
        | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f243,plain,
    ( spl4_24
    | ~ spl4_8
    | spl4_20
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f226,f219,f208,f97,f240])).

fof(f97,plain,
    ( spl4_8
  <=> ! [X0] :
        ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f208,plain,
    ( spl4_20
  <=> v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f219,plain,
    ( spl4_21
  <=> sK0 = k1_relset_1(sK0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f226,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_8
    | spl4_20
    | ~ spl4_21 ),
    inference(backward_demodulation,[],[f221,f224])).

fof(f224,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_8
    | spl4_20 ),
    inference(resolution,[],[f98,f210])).

fof(f210,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | spl4_20 ),
    inference(avatar_component_clause,[],[f208])).

fof(f98,plain,
    ( ! [X0] :
        ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f97])).

% (22369)Refutation not found, incomplete strategy% (22369)------------------------------
% (22369)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (22369)Termination reason: Refutation not found, incomplete strategy

% (22369)Memory used [KB]: 10618
% (22369)Time elapsed: 0.095 s
% (22369)------------------------------
% (22369)------------------------------
fof(f221,plain,
    ( sK0 = k1_relset_1(sK0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f219])).

fof(f237,plain,
    ( ~ spl4_23
    | ~ spl4_8
    | spl4_20 ),
    inference(avatar_split_clause,[],[f227,f208,f97,f234])).

fof(f227,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_8
    | spl4_20 ),
    inference(backward_demodulation,[],[f210,f224])).

fof(f222,plain,
    ( spl4_21
    | ~ spl4_16
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f189,f183,f178,f219])).

fof(f178,plain,
    ( spl4_16
  <=> r2_hidden(sK2,k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f183,plain,
    ( spl4_17
  <=> sK0 = k1_relset_1(sK0,k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f189,plain,
    ( sK0 = k1_relset_1(sK0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_16
    | ~ spl4_17 ),
    inference(backward_demodulation,[],[f185,f187])).

fof(f187,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_16 ),
    inference(resolution,[],[f180,f46])).

fof(f46,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f180,plain,
    ( r2_hidden(sK2,k1_tarski(k1_xboole_0))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f178])).

fof(f185,plain,
    ( sK0 = k1_relset_1(sK0,k1_xboole_0,sK2)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f183])).

fof(f211,plain,
    ( ~ spl4_20
    | spl4_14
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f192,f178,f164,f208])).

fof(f164,plain,
    ( spl4_14
  <=> v1_funct_2(sK2,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f192,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | spl4_14
    | ~ spl4_16 ),
    inference(backward_demodulation,[],[f166,f187])).

fof(f166,plain,
    ( ~ v1_funct_2(sK2,sK0,k1_xboole_0)
    | spl4_14 ),
    inference(avatar_component_clause,[],[f164])).

fof(f206,plain,
    ( spl4_9
    | ~ spl4_15
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f191,f178,f169,f100])).

fof(f169,plain,
    ( spl4_15
  <=> m1_subset_1(sK2,k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f191,plain,
    ( m1_subset_1(k1_xboole_0,k1_tarski(k1_xboole_0))
    | ~ spl4_15
    | ~ spl4_16 ),
    inference(backward_demodulation,[],[f171,f187])).

fof(f171,plain,
    ( m1_subset_1(sK2,k1_tarski(k1_xboole_0))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f169])).

fof(f186,plain,
    ( spl4_17
    | ~ spl4_3
    | ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f150,f81,f70,f65,f183])).

fof(f65,plain,
    ( spl4_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f70,plain,
    ( spl4_4
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f81,plain,
    ( spl4_5
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f150,plain,
    ( sK0 = k1_relset_1(sK0,k1_xboole_0,sK2)
    | ~ spl4_3
    | ~ spl4_4
    | spl4_5 ),
    inference(backward_demodulation,[],[f72,f147])).

fof(f147,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_3
    | ~ spl4_4
    | spl4_5 ),
    inference(subsumption_resolution,[],[f146,f67])).

fof(f67,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f146,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_4
    | spl4_5 ),
    inference(subsumption_resolution,[],[f145,f83])).

fof(f83,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f145,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_4 ),
    inference(trivial_inequality_removal,[],[f144])).

fof(f144,plain,
    ( sK0 != sK0
    | v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_4 ),
    inference(superposition,[],[f40,f72])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

% (22381)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f72,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f70])).

fof(f181,plain,
    ( spl4_16
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f176,f169,f178])).

fof(f176,plain,
    ( r2_hidden(sK2,k1_tarski(k1_xboole_0))
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f175,f29])).

fof(f29,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f175,plain,
    ( v1_xboole_0(k1_tarski(k1_xboole_0))
    | r2_hidden(sK2,k1_tarski(k1_xboole_0))
    | ~ spl4_15 ),
    inference(resolution,[],[f171,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f172,plain,
    ( spl4_15
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f162,f81,f70,f65,f60,f169])).

fof(f60,plain,
    ( spl4_2
  <=> k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f162,plain,
    ( m1_subset_1(sK2,k1_tarski(k1_xboole_0))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_5 ),
    inference(forward_demodulation,[],[f161,f62])).

fof(f62,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f161,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_3
    | ~ spl4_4
    | spl4_5 ),
    inference(forward_demodulation,[],[f151,f47])).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f151,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl4_3
    | ~ spl4_4
    | spl4_5 ),
    inference(backward_demodulation,[],[f67,f147])).

fof(f167,plain,
    ( ~ spl4_14
    | ~ spl4_3
    | ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f149,f81,f70,f65,f164])).

fof(f149,plain,
    ( ~ v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_4
    | spl4_5 ),
    inference(backward_demodulation,[],[f83,f147])).

fof(f116,plain,
    ( spl4_11
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f112,f60,f114])).

fof(f112,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X2,k1_tarski(k1_xboole_0))
        | v1_funct_2(X2,k1_xboole_0,X1)
        | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) )
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f111,f62])).

fof(f111,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(forward_demodulation,[],[f52,f48])).

fof(f48,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f52,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f103,plain,
    ( spl4_8
    | ~ spl4_9
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f95,f60,f100,f97])).

fof(f95,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_xboole_0,k1_tarski(k1_xboole_0))
        | v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f94,f62])).

fof(f94,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(forward_demodulation,[],[f50,f47])).

fof(f50,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f84,plain,
    ( ~ spl4_5
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f79,f65,f55,f81])).

fof(f55,plain,
    ( spl4_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f79,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f78,f57])).

fof(f57,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f78,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f27,f67])).

fof(f27,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) )
    & sK0 = k1_relset_1(sK0,sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2) )
        & k1_relset_1(X0,X1,X2) = X0
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2) )
      & sK0 = k1_relset_1(sK0,sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & k1_relset_1(X0,X1,X2) = X0
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & k1_relset_1(X0,X1,X2) = X0
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ( k1_relset_1(X0,X1,X2) = X0
         => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X2,X0,X1)
            & v1_funct_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( k1_relset_1(X0,X1,X2) = X0
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_funct_2)).

fof(f73,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f26,f70])).

fof(f26,plain,(
    sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f68,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f25,f65])).

fof(f25,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f63,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f28,f60])).

fof(f28,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f58,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f24,f55])).

fof(f24,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

% (22374)Refutation not found, incomplete strategy% (22374)------------------------------
% (22374)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (22374)Termination reason: Refutation not found, incomplete strategy

% (22374)Memory used [KB]: 6140
% (22374)Time elapsed: 0.105 s
% (22374)------------------------------
% (22374)------------------------------
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n014.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:43:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.49  % (22373)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.50  % (22371)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.50  % (22380)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.51  % (22374)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (22371)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (22370)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (22391)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.51  % (22390)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.51  % (22370)Refutation not found, incomplete strategy% (22370)------------------------------
% 0.22/0.51  % (22370)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (22369)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.51  % (22370)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (22370)Memory used [KB]: 10618
% 0.22/0.51  % (22370)Time elapsed: 0.095 s
% 0.22/0.51  % (22370)------------------------------
% 0.22/0.51  % (22370)------------------------------
% 0.22/0.51  % (22383)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (22375)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.52  % (22382)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f252,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f58,f63,f68,f73,f84,f103,f116,f167,f172,f181,f186,f206,f211,f222,f237,f243,f251])).
% 0.22/0.52  fof(f251,plain,(
% 0.22/0.52    ~spl4_9 | ~spl4_11 | spl4_23 | ~spl4_24),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f250])).
% 0.22/0.52  fof(f250,plain,(
% 0.22/0.52    $false | (~spl4_9 | ~spl4_11 | spl4_23 | ~spl4_24)),
% 0.22/0.52    inference(subsumption_resolution,[],[f249,f101])).
% 0.22/0.52  fof(f101,plain,(
% 0.22/0.52    m1_subset_1(k1_xboole_0,k1_tarski(k1_xboole_0)) | ~spl4_9),
% 0.22/0.52    inference(avatar_component_clause,[],[f100])).
% 0.22/0.52  fof(f100,plain,(
% 0.22/0.52    spl4_9 <=> m1_subset_1(k1_xboole_0,k1_tarski(k1_xboole_0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.52  fof(f249,plain,(
% 0.22/0.52    ~m1_subset_1(k1_xboole_0,k1_tarski(k1_xboole_0)) | (~spl4_11 | spl4_23 | ~spl4_24)),
% 0.22/0.52    inference(subsumption_resolution,[],[f247,f236])).
% 0.22/0.52  fof(f236,plain,(
% 0.22/0.52    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | spl4_23),
% 0.22/0.52    inference(avatar_component_clause,[],[f234])).
% 0.22/0.52  fof(f234,plain,(
% 0.22/0.52    spl4_23 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.22/0.52  fof(f247,plain,(
% 0.22/0.52    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_tarski(k1_xboole_0)) | (~spl4_11 | ~spl4_24)),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f245])).
% 0.22/0.52  fof(f245,plain,(
% 0.22/0.52    k1_xboole_0 != k1_xboole_0 | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_tarski(k1_xboole_0)) | (~spl4_11 | ~spl4_24)),
% 0.22/0.52    inference(superposition,[],[f115,f242])).
% 0.22/0.52  fof(f242,plain,(
% 0.22/0.52    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~spl4_24),
% 0.22/0.52    inference(avatar_component_clause,[],[f240])).
% 0.22/0.52  fof(f240,plain,(
% 0.22/0.52    spl4_24 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.22/0.52  fof(f115,plain,(
% 0.22/0.52    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_tarski(k1_xboole_0))) ) | ~spl4_11),
% 0.22/0.52    inference(avatar_component_clause,[],[f114])).
% 0.22/0.52  fof(f114,plain,(
% 0.22/0.52    spl4_11 <=> ! [X1,X2] : (~m1_subset_1(X2,k1_tarski(k1_xboole_0)) | v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.22/0.52  fof(f243,plain,(
% 0.22/0.52    spl4_24 | ~spl4_8 | spl4_20 | ~spl4_21),
% 0.22/0.52    inference(avatar_split_clause,[],[f226,f219,f208,f97,f240])).
% 0.22/0.52  fof(f97,plain,(
% 0.22/0.52    spl4_8 <=> ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.52  fof(f208,plain,(
% 0.22/0.52    spl4_20 <=> v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.22/0.52  fof(f219,plain,(
% 0.22/0.52    spl4_21 <=> sK0 = k1_relset_1(sK0,k1_xboole_0,k1_xboole_0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.22/0.52  fof(f226,plain,(
% 0.22/0.52    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl4_8 | spl4_20 | ~spl4_21)),
% 0.22/0.52    inference(backward_demodulation,[],[f221,f224])).
% 0.22/0.52  fof(f224,plain,(
% 0.22/0.52    k1_xboole_0 = sK0 | (~spl4_8 | spl4_20)),
% 0.22/0.52    inference(resolution,[],[f98,f210])).
% 0.22/0.52  fof(f210,plain,(
% 0.22/0.52    ~v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) | spl4_20),
% 0.22/0.52    inference(avatar_component_clause,[],[f208])).
% 0.22/0.52  fof(f98,plain,(
% 0.22/0.52    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl4_8),
% 0.22/0.52    inference(avatar_component_clause,[],[f97])).
% 0.22/0.52  % (22369)Refutation not found, incomplete strategy% (22369)------------------------------
% 0.22/0.52  % (22369)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (22369)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (22369)Memory used [KB]: 10618
% 0.22/0.52  % (22369)Time elapsed: 0.095 s
% 0.22/0.52  % (22369)------------------------------
% 0.22/0.52  % (22369)------------------------------
% 0.22/0.52  fof(f221,plain,(
% 0.22/0.52    sK0 = k1_relset_1(sK0,k1_xboole_0,k1_xboole_0) | ~spl4_21),
% 0.22/0.52    inference(avatar_component_clause,[],[f219])).
% 0.22/0.52  fof(f237,plain,(
% 0.22/0.52    ~spl4_23 | ~spl4_8 | spl4_20),
% 0.22/0.52    inference(avatar_split_clause,[],[f227,f208,f97,f234])).
% 0.22/0.52  fof(f227,plain,(
% 0.22/0.52    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl4_8 | spl4_20)),
% 0.22/0.52    inference(backward_demodulation,[],[f210,f224])).
% 0.22/0.52  fof(f222,plain,(
% 0.22/0.52    spl4_21 | ~spl4_16 | ~spl4_17),
% 0.22/0.52    inference(avatar_split_clause,[],[f189,f183,f178,f219])).
% 0.22/0.52  fof(f178,plain,(
% 0.22/0.52    spl4_16 <=> r2_hidden(sK2,k1_tarski(k1_xboole_0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.22/0.52  fof(f183,plain,(
% 0.22/0.52    spl4_17 <=> sK0 = k1_relset_1(sK0,k1_xboole_0,sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.22/0.52  fof(f189,plain,(
% 0.22/0.52    sK0 = k1_relset_1(sK0,k1_xboole_0,k1_xboole_0) | (~spl4_16 | ~spl4_17)),
% 0.22/0.52    inference(backward_demodulation,[],[f185,f187])).
% 0.22/0.52  fof(f187,plain,(
% 0.22/0.52    k1_xboole_0 = sK2 | ~spl4_16),
% 0.22/0.52    inference(resolution,[],[f180,f46])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.22/0.52    inference(equality_resolution,[],[f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.52    inference(rectify,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.52    inference(nnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.22/0.52  fof(f180,plain,(
% 0.22/0.52    r2_hidden(sK2,k1_tarski(k1_xboole_0)) | ~spl4_16),
% 0.22/0.52    inference(avatar_component_clause,[],[f178])).
% 0.22/0.52  fof(f185,plain,(
% 0.22/0.52    sK0 = k1_relset_1(sK0,k1_xboole_0,sK2) | ~spl4_17),
% 0.22/0.52    inference(avatar_component_clause,[],[f183])).
% 0.22/0.52  fof(f211,plain,(
% 0.22/0.52    ~spl4_20 | spl4_14 | ~spl4_16),
% 0.22/0.52    inference(avatar_split_clause,[],[f192,f178,f164,f208])).
% 0.22/0.52  fof(f164,plain,(
% 0.22/0.52    spl4_14 <=> v1_funct_2(sK2,sK0,k1_xboole_0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.22/0.52  fof(f192,plain,(
% 0.22/0.52    ~v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) | (spl4_14 | ~spl4_16)),
% 0.22/0.52    inference(backward_demodulation,[],[f166,f187])).
% 0.22/0.52  fof(f166,plain,(
% 0.22/0.52    ~v1_funct_2(sK2,sK0,k1_xboole_0) | spl4_14),
% 0.22/0.52    inference(avatar_component_clause,[],[f164])).
% 0.22/0.52  fof(f206,plain,(
% 0.22/0.52    spl4_9 | ~spl4_15 | ~spl4_16),
% 0.22/0.52    inference(avatar_split_clause,[],[f191,f178,f169,f100])).
% 0.22/0.52  fof(f169,plain,(
% 0.22/0.52    spl4_15 <=> m1_subset_1(sK2,k1_tarski(k1_xboole_0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.22/0.52  fof(f191,plain,(
% 0.22/0.52    m1_subset_1(k1_xboole_0,k1_tarski(k1_xboole_0)) | (~spl4_15 | ~spl4_16)),
% 0.22/0.52    inference(backward_demodulation,[],[f171,f187])).
% 0.22/0.52  fof(f171,plain,(
% 0.22/0.52    m1_subset_1(sK2,k1_tarski(k1_xboole_0)) | ~spl4_15),
% 0.22/0.52    inference(avatar_component_clause,[],[f169])).
% 0.22/0.52  fof(f186,plain,(
% 0.22/0.52    spl4_17 | ~spl4_3 | ~spl4_4 | spl4_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f150,f81,f70,f65,f183])).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    spl4_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    spl4_4 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.52  fof(f81,plain,(
% 0.22/0.52    spl4_5 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.52  fof(f150,plain,(
% 0.22/0.52    sK0 = k1_relset_1(sK0,k1_xboole_0,sK2) | (~spl4_3 | ~spl4_4 | spl4_5)),
% 0.22/0.52    inference(backward_demodulation,[],[f72,f147])).
% 0.22/0.52  fof(f147,plain,(
% 0.22/0.52    k1_xboole_0 = sK1 | (~spl4_3 | ~spl4_4 | spl4_5)),
% 0.22/0.52    inference(subsumption_resolution,[],[f146,f67])).
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f65])).
% 0.22/0.52  fof(f146,plain,(
% 0.22/0.52    k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl4_4 | spl4_5)),
% 0.22/0.52    inference(subsumption_resolution,[],[f145,f83])).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    ~v1_funct_2(sK2,sK0,sK1) | spl4_5),
% 0.22/0.52    inference(avatar_component_clause,[],[f81])).
% 0.22/0.52  fof(f145,plain,(
% 0.22/0.52    v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_4),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f144])).
% 0.22/0.52  fof(f144,plain,(
% 0.22/0.52    sK0 != sK0 | v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_4),
% 0.22/0.52    inference(superposition,[],[f40,f72])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  % (22381)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(nnf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(flattening,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl4_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f70])).
% 0.22/0.52  fof(f181,plain,(
% 0.22/0.52    spl4_16 | ~spl4_15),
% 0.22/0.52    inference(avatar_split_clause,[],[f176,f169,f178])).
% 0.22/0.52  fof(f176,plain,(
% 0.22/0.52    r2_hidden(sK2,k1_tarski(k1_xboole_0)) | ~spl4_15),
% 0.22/0.52    inference(subsumption_resolution,[],[f175,f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).
% 0.22/0.52  fof(f175,plain,(
% 0.22/0.52    v1_xboole_0(k1_tarski(k1_xboole_0)) | r2_hidden(sK2,k1_tarski(k1_xboole_0)) | ~spl4_15),
% 0.22/0.52    inference(resolution,[],[f171,f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.52    inference(flattening,[],[f11])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.52  fof(f172,plain,(
% 0.22/0.52    spl4_15 | ~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f162,f81,f70,f65,f60,f169])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    spl4_2 <=> k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.52  fof(f162,plain,(
% 0.22/0.52    m1_subset_1(sK2,k1_tarski(k1_xboole_0)) | (~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_5)),
% 0.22/0.52    inference(forward_demodulation,[],[f161,f62])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) | ~spl4_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f60])).
% 0.22/0.52  fof(f161,plain,(
% 0.22/0.52    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl4_3 | ~spl4_4 | spl4_5)),
% 0.22/0.52    inference(forward_demodulation,[],[f151,f47])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.52    inference(equality_resolution,[],[f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.22/0.52    inference(flattening,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.22/0.52    inference(nnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.52  fof(f151,plain,(
% 0.22/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl4_3 | ~spl4_4 | spl4_5)),
% 0.22/0.52    inference(backward_demodulation,[],[f67,f147])).
% 0.22/0.52  fof(f167,plain,(
% 0.22/0.52    ~spl4_14 | ~spl4_3 | ~spl4_4 | spl4_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f149,f81,f70,f65,f164])).
% 0.22/0.52  fof(f149,plain,(
% 0.22/0.52    ~v1_funct_2(sK2,sK0,k1_xboole_0) | (~spl4_3 | ~spl4_4 | spl4_5)),
% 0.22/0.52    inference(backward_demodulation,[],[f83,f147])).
% 0.22/0.52  fof(f116,plain,(
% 0.22/0.52    spl4_11 | ~spl4_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f112,f60,f114])).
% 0.22/0.52  fof(f112,plain,(
% 0.22/0.52    ( ! [X2,X1] : (~m1_subset_1(X2,k1_tarski(k1_xboole_0)) | v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)) ) | ~spl4_2),
% 0.22/0.52    inference(forward_demodulation,[],[f111,f62])).
% 0.22/0.52  fof(f111,plain,(
% 0.22/0.52    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)) )),
% 0.22/0.52    inference(forward_demodulation,[],[f52,f48])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.22/0.52    inference(equality_resolution,[],[f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f22])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.22/0.52    inference(equality_resolution,[],[f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  fof(f103,plain,(
% 0.22/0.52    spl4_8 | ~spl4_9 | ~spl4_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f95,f60,f100,f97])).
% 0.22/0.52  fof(f95,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_tarski(k1_xboole_0)) | v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl4_2),
% 0.22/0.52    inference(forward_demodulation,[],[f94,f62])).
% 0.22/0.52  fof(f94,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.22/0.52    inference(forward_demodulation,[],[f50,f47])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 0.22/0.52    inference(equality_resolution,[],[f49])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.52    inference(equality_resolution,[],[f43])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  fof(f84,plain,(
% 0.22/0.52    ~spl4_5 | ~spl4_1 | ~spl4_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f79,f65,f55,f81])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    spl4_1 <=> v1_funct_1(sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.52  fof(f79,plain,(
% 0.22/0.52    ~v1_funct_2(sK2,sK0,sK1) | (~spl4_1 | ~spl4_3)),
% 0.22/0.52    inference(subsumption_resolution,[],[f78,f57])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    v1_funct_1(sK2) | ~spl4_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f55])).
% 0.22/0.52  fof(f78,plain,(
% 0.22/0.52    ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_3),
% 0.22/0.52    inference(subsumption_resolution,[],[f27,f67])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) & sK0 = k1_relset_1(sK0,sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & k1_relset_1(X0,X1,X2) = X0 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) & sK0 = k1_relset_1(sK0,sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f10,plain,(
% 0.22/0.52    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & k1_relset_1(X0,X1,X2) = X0 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.22/0.52    inference(flattening,[],[f9])).
% 0.22/0.52  fof(f9,plain,(
% 0.22/0.52    ? [X0,X1,X2] : (((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & k1_relset_1(X0,X1,X2) = X0) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (k1_relset_1(X0,X1,X2) = X0 => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.22/0.52    inference(negated_conjecture,[],[f7])).
% 0.22/0.52  fof(f7,conjecture,(
% 0.22/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (k1_relset_1(X0,X1,X2) = X0 => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_funct_2)).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    spl4_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f26,f70])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    spl4_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f25,f65])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    spl4_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f28,f60])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.22/0.52    inference(cnf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    spl4_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f24,f55])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    v1_funct_1(sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  % (22374)Refutation not found, incomplete strategy% (22374)------------------------------
% 0.22/0.52  % (22374)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (22374)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (22374)Memory used [KB]: 6140
% 0.22/0.52  % (22374)Time elapsed: 0.105 s
% 0.22/0.52  % (22374)------------------------------
% 0.22/0.52  % (22374)------------------------------
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (22371)------------------------------
% 0.22/0.52  % (22371)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (22371)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (22371)Memory used [KB]: 6268
% 0.22/0.52  % (22371)Time elapsed: 0.090 s
% 0.22/0.52  % (22371)------------------------------
% 0.22/0.52  % (22371)------------------------------
% 0.22/0.52  % (22387)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.52  % (22378)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.52  % (22368)Success in time 0.152 s
%------------------------------------------------------------------------------
