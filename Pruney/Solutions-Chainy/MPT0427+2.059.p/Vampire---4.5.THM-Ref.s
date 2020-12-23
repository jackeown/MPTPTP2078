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
% DateTime   : Thu Dec  3 12:46:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 227 expanded)
%              Number of leaves         :   31 (  96 expanded)
%              Depth                    :   10
%              Number of atoms          :  309 ( 614 expanded)
%              Number of equality atoms :   55 ( 124 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f453,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f57,f61,f65,f154,f158,f171,f176,f180,f195,f232,f289,f290,f293,f336,f373,f444,f449,f452])).

fof(f452,plain,(
    spl3_47 ),
    inference(avatar_contradiction_clause,[],[f450])).

fof(f450,plain,
    ( $false
    | spl3_47 ),
    inference(resolution,[],[f448,f114])).

fof(f114,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f113,f34])).

fof(f34,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f113,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(X0,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f112])).

% (22851)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
fof(f112,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(superposition,[],[f40,f49])).

fof(f49,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).

fof(f448,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | spl3_47 ),
    inference(avatar_component_clause,[],[f447])).

fof(f447,plain,
    ( spl3_47
  <=> m1_subset_1(sK0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f449,plain,
    ( ~ spl3_47
    | spl3_46 ),
    inference(avatar_split_clause,[],[f445,f442,f447])).

fof(f442,plain,
    ( spl3_46
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f445,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | spl3_46 ),
    inference(resolution,[],[f443,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f443,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl3_46 ),
    inference(avatar_component_clause,[],[f442])).

fof(f444,plain,
    ( ~ spl3_28
    | ~ spl3_46
    | spl3_39 ),
    inference(avatar_split_clause,[],[f440,f367,f442,f284])).

fof(f284,plain,
    ( spl3_28
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f367,plain,
    ( spl3_39
  <=> r1_tarski(k8_setfam_1(sK0,k1_xboole_0),k8_setfam_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f440,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl3_39 ),
    inference(superposition,[],[f368,f49])).

fof(f368,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,k1_xboole_0),k8_setfam_1(sK0,k1_xboole_0))
    | spl3_39 ),
    inference(avatar_component_clause,[],[f367])).

fof(f373,plain,
    ( ~ spl3_39
    | spl3_1
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f372,f152,f87,f51,f367])).

fof(f51,plain,
    ( spl3_1
  <=> r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f87,plain,
    ( spl3_7
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f152,plain,
    ( spl3_11
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f372,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,k1_xboole_0),k8_setfam_1(sK0,k1_xboole_0))
    | spl3_1
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f184,f153])).

fof(f153,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f152])).

fof(f184,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0))
    | spl3_1
    | ~ spl3_7 ),
    inference(superposition,[],[f52,f88])).

fof(f88,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f87])).

fof(f52,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f336,plain,
    ( spl3_7
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f330,f230,f87])).

fof(f230,plain,
    ( spl3_24
  <=> r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f330,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_24 ),
    inference(resolution,[],[f231,f109])).

fof(f109,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f106,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

% (22860)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f106,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f85,f79])).

fof(f79,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(trivial_inequality_removal,[],[f78])).

fof(f78,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f44,f35])).

fof(f35,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f82,f45])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f47,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

% (22849)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f17,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f231,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f230])).

fof(f293,plain,
    ( ~ spl3_15
    | spl3_29 ),
    inference(avatar_split_clause,[],[f291,f287,f174])).

fof(f174,plain,
    ( spl3_15
  <=> m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f287,plain,
    ( spl3_29
  <=> r1_tarski(k1_setfam_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f291,plain,
    ( ~ m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | spl3_29 ),
    inference(resolution,[],[f288,f45])).

fof(f288,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),sK0)
    | spl3_29 ),
    inference(avatar_component_clause,[],[f287])).

fof(f290,plain,
    ( k1_xboole_0 != sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f289,plain,
    ( ~ spl3_28
    | ~ spl3_29
    | spl3_17 ),
    inference(avatar_split_clause,[],[f282,f193,f287,f284])).

fof(f193,plain,
    ( spl3_17
  <=> r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f282,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl3_17 ),
    inference(superposition,[],[f194,f49])).

fof(f194,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0))
    | spl3_17 ),
    inference(avatar_component_clause,[],[f193])).

fof(f232,plain,
    ( spl3_24
    | ~ spl3_2
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f218,f152,f55,f230])).

fof(f55,plain,
    ( spl3_2
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f218,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_11 ),
    inference(superposition,[],[f56,f153])).

fof(f56,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f195,plain,
    ( ~ spl3_17
    | spl3_1
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f191,f149,f87,f51,f193])).

fof(f149,plain,
    ( spl3_10
  <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f191,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0))
    | spl3_1
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f184,f150])).

fof(f150,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f149])).

fof(f180,plain,
    ( ~ spl3_2
    | spl3_7
    | spl3_14 ),
    inference(avatar_split_clause,[],[f177,f169,f87,f55])).

fof(f169,plain,
    ( spl3_14
  <=> r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f177,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_tarski(sK1,sK2)
    | spl3_14 ),
    inference(resolution,[],[f170,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

% (22860)Refutation not found, incomplete strategy% (22860)------------------------------
% (22860)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (22860)Termination reason: Refutation not found, incomplete strategy

% (22860)Memory used [KB]: 6012
% (22860)Time elapsed: 0.077 s
% (22860)------------------------------
% (22860)------------------------------
fof(f170,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | spl3_14 ),
    inference(avatar_component_clause,[],[f169])).

fof(f176,plain,
    ( ~ spl3_3
    | spl3_15
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f161,f149,f174,f59])).

fof(f59,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f161,plain,
    ( m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_10 ),
    inference(superposition,[],[f40,f150])).

fof(f171,plain,
    ( ~ spl3_14
    | spl3_1
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f167,f156,f149,f51,f169])).

fof(f156,plain,
    ( spl3_12
  <=> k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f167,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | spl3_1
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f160,f157])).

fof(f157,plain,
    ( k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f156])).

fof(f160,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1))
    | spl3_1
    | ~ spl3_10 ),
    inference(superposition,[],[f52,f150])).

fof(f158,plain,
    ( spl3_12
    | spl3_7
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f143,f63,f87,f156])).

fof(f63,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f143,plain,
    ( k1_xboole_0 = sK1
    | k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | ~ spl3_4 ),
    inference(resolution,[],[f128,f64])).

fof(f64,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f63])).

fof(f128,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
      | k1_xboole_0 = X3
      | k1_setfam_1(X3) = k8_setfam_1(X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f125])).

fof(f125,plain,(
    ! [X2,X3] :
      ( k1_setfam_1(X3) = k8_setfam_1(X2,X3)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) ) ),
    inference(superposition,[],[f41,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f154,plain,
    ( spl3_10
    | spl3_11
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f142,f59,f152,f149])).

fof(f142,plain,
    ( k1_xboole_0 = sK2
    | k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl3_3 ),
    inference(resolution,[],[f128,f60])).

fof(f60,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f65,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f30,f63])).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f26,f25])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
            & r1_tarski(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1))
          & r1_tarski(sK1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1))
        & r1_tarski(sK1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
   => ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).

fof(f61,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f31,f59])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f57,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f32,f55])).

fof(f32,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f53,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f33,f51])).

fof(f33,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:20:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (22854)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (22852)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (22854)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (22862)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f453,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f53,f57,f61,f65,f154,f158,f171,f176,f180,f195,f232,f289,f290,f293,f336,f373,f444,f449,f452])).
% 0.21/0.48  fof(f452,plain,(
% 0.21/0.48    spl3_47),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f450])).
% 0.21/0.48  fof(f450,plain,(
% 0.21/0.48    $false | spl3_47),
% 0.21/0.48    inference(resolution,[],[f448,f114])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(resolution,[],[f113,f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) | m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f112])).
% 0.21/0.49  % (22851)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.49    inference(superposition,[],[f40,f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.49    inference(equality_resolution,[],[f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).
% 0.21/0.49  fof(f448,plain,(
% 0.21/0.49    ~m1_subset_1(sK0,k1_zfmisc_1(sK0)) | spl3_47),
% 0.21/0.49    inference(avatar_component_clause,[],[f447])).
% 0.21/0.49  fof(f447,plain,(
% 0.21/0.49    spl3_47 <=> m1_subset_1(sK0,k1_zfmisc_1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 0.21/0.49  fof(f449,plain,(
% 0.21/0.49    ~spl3_47 | spl3_46),
% 0.21/0.49    inference(avatar_split_clause,[],[f445,f442,f447])).
% 0.21/0.49  fof(f442,plain,(
% 0.21/0.49    spl3_46 <=> r1_tarski(sK0,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 0.21/0.49  fof(f445,plain,(
% 0.21/0.49    ~m1_subset_1(sK0,k1_zfmisc_1(sK0)) | spl3_46),
% 0.21/0.49    inference(resolution,[],[f443,f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.49    inference(nnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.49  fof(f443,plain,(
% 0.21/0.49    ~r1_tarski(sK0,sK0) | spl3_46),
% 0.21/0.49    inference(avatar_component_clause,[],[f442])).
% 0.21/0.49  fof(f444,plain,(
% 0.21/0.49    ~spl3_28 | ~spl3_46 | spl3_39),
% 0.21/0.49    inference(avatar_split_clause,[],[f440,f367,f442,f284])).
% 0.21/0.49  fof(f284,plain,(
% 0.21/0.49    spl3_28 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.21/0.49  fof(f367,plain,(
% 0.21/0.49    spl3_39 <=> r1_tarski(k8_setfam_1(sK0,k1_xboole_0),k8_setfam_1(sK0,k1_xboole_0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.21/0.49  fof(f440,plain,(
% 0.21/0.49    ~r1_tarski(sK0,sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl3_39),
% 0.21/0.49    inference(superposition,[],[f368,f49])).
% 0.21/0.49  fof(f368,plain,(
% 0.21/0.49    ~r1_tarski(k8_setfam_1(sK0,k1_xboole_0),k8_setfam_1(sK0,k1_xboole_0)) | spl3_39),
% 0.21/0.49    inference(avatar_component_clause,[],[f367])).
% 0.21/0.49  fof(f373,plain,(
% 0.21/0.49    ~spl3_39 | spl3_1 | ~spl3_7 | ~spl3_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f372,f152,f87,f51,f367])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    spl3_1 <=> r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    spl3_7 <=> k1_xboole_0 = sK1),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.49  fof(f152,plain,(
% 0.21/0.49    spl3_11 <=> k1_xboole_0 = sK2),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.49  fof(f372,plain,(
% 0.21/0.49    ~r1_tarski(k8_setfam_1(sK0,k1_xboole_0),k8_setfam_1(sK0,k1_xboole_0)) | (spl3_1 | ~spl3_7 | ~spl3_11)),
% 0.21/0.49    inference(forward_demodulation,[],[f184,f153])).
% 0.21/0.49  fof(f153,plain,(
% 0.21/0.49    k1_xboole_0 = sK2 | ~spl3_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f152])).
% 0.21/0.49  fof(f184,plain,(
% 0.21/0.49    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0)) | (spl3_1 | ~spl3_7)),
% 0.21/0.49    inference(superposition,[],[f52,f88])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    k1_xboole_0 = sK1 | ~spl3_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f87])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) | spl3_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f51])).
% 0.21/0.49  fof(f336,plain,(
% 0.21/0.49    spl3_7 | ~spl3_24),
% 0.21/0.49    inference(avatar_split_clause,[],[f330,f230,f87])).
% 0.21/0.49  fof(f230,plain,(
% 0.21/0.49    spl3_24 <=> r1_tarski(sK1,k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.49  fof(f330,plain,(
% 0.21/0.49    k1_xboole_0 = sK1 | ~spl3_24),
% 0.21/0.49    inference(resolution,[],[f231,f109])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(resolution,[],[f106,f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  % (22860)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(resolution,[],[f85,f79])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f78])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.49    inference(superposition,[],[f44,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.49    inference(nnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(resolution,[],[f82,f45])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_xboole_0(X0,X1) | k1_xboole_0 = X1) )),
% 0.21/0.49    inference(resolution,[],[f47,f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  % (22849)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.49    inference(flattening,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.21/0.49  fof(f231,plain,(
% 0.21/0.49    r1_tarski(sK1,k1_xboole_0) | ~spl3_24),
% 0.21/0.49    inference(avatar_component_clause,[],[f230])).
% 0.21/0.49  fof(f293,plain,(
% 0.21/0.49    ~spl3_15 | spl3_29),
% 0.21/0.49    inference(avatar_split_clause,[],[f291,f287,f174])).
% 0.21/0.49  fof(f174,plain,(
% 0.21/0.49    spl3_15 <=> m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.49  fof(f287,plain,(
% 0.21/0.49    spl3_29 <=> r1_tarski(k1_setfam_1(sK2),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.21/0.49  fof(f291,plain,(
% 0.21/0.49    ~m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | spl3_29),
% 0.21/0.49    inference(resolution,[],[f288,f45])).
% 0.21/0.49  fof(f288,plain,(
% 0.21/0.49    ~r1_tarski(k1_setfam_1(sK2),sK0) | spl3_29),
% 0.21/0.49    inference(avatar_component_clause,[],[f287])).
% 0.21/0.49  fof(f290,plain,(
% 0.21/0.49    k1_xboole_0 != sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.49  fof(f289,plain,(
% 0.21/0.49    ~spl3_28 | ~spl3_29 | spl3_17),
% 0.21/0.49    inference(avatar_split_clause,[],[f282,f193,f287,f284])).
% 0.21/0.49  fof(f193,plain,(
% 0.21/0.49    spl3_17 <=> r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.49  fof(f282,plain,(
% 0.21/0.49    ~r1_tarski(k1_setfam_1(sK2),sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl3_17),
% 0.21/0.49    inference(superposition,[],[f194,f49])).
% 0.21/0.49  fof(f194,plain,(
% 0.21/0.49    ~r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0)) | spl3_17),
% 0.21/0.49    inference(avatar_component_clause,[],[f193])).
% 0.21/0.49  fof(f232,plain,(
% 0.21/0.49    spl3_24 | ~spl3_2 | ~spl3_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f218,f152,f55,f230])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    spl3_2 <=> r1_tarski(sK1,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.49  fof(f218,plain,(
% 0.21/0.49    r1_tarski(sK1,k1_xboole_0) | (~spl3_2 | ~spl3_11)),
% 0.21/0.49    inference(superposition,[],[f56,f153])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    r1_tarski(sK1,sK2) | ~spl3_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f55])).
% 0.21/0.49  fof(f195,plain,(
% 0.21/0.49    ~spl3_17 | spl3_1 | ~spl3_7 | ~spl3_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f191,f149,f87,f51,f193])).
% 0.21/0.49  fof(f149,plain,(
% 0.21/0.49    spl3_10 <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.49  fof(f191,plain,(
% 0.21/0.49    ~r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0)) | (spl3_1 | ~spl3_7 | ~spl3_10)),
% 0.21/0.49    inference(forward_demodulation,[],[f184,f150])).
% 0.21/0.49  fof(f150,plain,(
% 0.21/0.49    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~spl3_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f149])).
% 0.21/0.49  fof(f180,plain,(
% 0.21/0.49    ~spl3_2 | spl3_7 | spl3_14),
% 0.21/0.49    inference(avatar_split_clause,[],[f177,f169,f87,f55])).
% 0.21/0.49  fof(f169,plain,(
% 0.21/0.49    spl3_14 <=> r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.49  fof(f177,plain,(
% 0.21/0.49    k1_xboole_0 = sK1 | ~r1_tarski(sK1,sK2) | spl3_14),
% 0.21/0.49    inference(resolution,[],[f170,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.49    inference(flattening,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).
% 0.21/0.49  % (22860)Refutation not found, incomplete strategy% (22860)------------------------------
% 0.21/0.49  % (22860)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (22860)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (22860)Memory used [KB]: 6012
% 0.21/0.49  % (22860)Time elapsed: 0.077 s
% 0.21/0.49  % (22860)------------------------------
% 0.21/0.49  % (22860)------------------------------
% 0.21/0.49  fof(f170,plain,(
% 0.21/0.49    ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | spl3_14),
% 0.21/0.49    inference(avatar_component_clause,[],[f169])).
% 0.21/0.49  fof(f176,plain,(
% 0.21/0.49    ~spl3_3 | spl3_15 | ~spl3_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f161,f149,f174,f59])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.49  fof(f161,plain,(
% 0.21/0.49    m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_10),
% 0.21/0.49    inference(superposition,[],[f40,f150])).
% 0.21/0.49  fof(f171,plain,(
% 0.21/0.49    ~spl3_14 | spl3_1 | ~spl3_10 | ~spl3_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f167,f156,f149,f51,f169])).
% 0.21/0.49  fof(f156,plain,(
% 0.21/0.49    spl3_12 <=> k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.49  fof(f167,plain,(
% 0.21/0.49    ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | (spl3_1 | ~spl3_10 | ~spl3_12)),
% 0.21/0.49    inference(forward_demodulation,[],[f160,f157])).
% 0.21/0.49  fof(f157,plain,(
% 0.21/0.49    k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | ~spl3_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f156])).
% 0.21/0.49  fof(f160,plain,(
% 0.21/0.49    ~r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1)) | (spl3_1 | ~spl3_10)),
% 0.21/0.49    inference(superposition,[],[f52,f150])).
% 0.21/0.49  fof(f158,plain,(
% 0.21/0.49    spl3_12 | spl3_7 | ~spl3_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f143,f63,f87,f156])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    spl3_4 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.49  fof(f143,plain,(
% 0.21/0.49    k1_xboole_0 = sK1 | k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | ~spl3_4),
% 0.21/0.49    inference(resolution,[],[f128,f64])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f63])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) | k1_xboole_0 = X3 | k1_setfam_1(X3) = k8_setfam_1(X2,X3)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f125])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    ( ! [X2,X3] : (k1_setfam_1(X3) = k8_setfam_1(X2,X3) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))) )),
% 0.21/0.49    inference(superposition,[],[f41,f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f154,plain,(
% 0.21/0.49    spl3_10 | spl3_11 | ~spl3_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f142,f59,f152,f149])).
% 0.21/0.49  fof(f142,plain,(
% 0.21/0.49    k1_xboole_0 = sK2 | k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~spl3_3),
% 0.21/0.49    inference(resolution,[],[f128,f60])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f59])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    spl3_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f30,f63])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    (~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f26,f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (~r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ? [X2] : (~r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) => (~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.49    inference(flattening,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.49    inference(ennf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 0.21/0.49    inference(negated_conjecture,[],[f12])).
% 0.21/0.49  fof(f12,conjecture,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    spl3_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f31,f59])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    spl3_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f32,f55])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    r1_tarski(sK1,sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ~spl3_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f33,f51])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (22854)------------------------------
% 0.21/0.49  % (22854)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (22854)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (22854)Memory used [KB]: 10874
% 0.21/0.49  % (22854)Time elapsed: 0.071 s
% 0.21/0.49  % (22854)------------------------------
% 0.21/0.49  % (22854)------------------------------
% 0.21/0.49  % (22853)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (22847)Success in time 0.125 s
%------------------------------------------------------------------------------
