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
% DateTime   : Thu Dec  3 12:46:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 176 expanded)
%              Number of leaves         :   30 (  73 expanded)
%              Depth                    :    9
%              Number of atoms          :  275 ( 442 expanded)
%              Number of equality atoms :   57 (  92 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f440,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f56,f61,f84,f107,f112,f117,f127,f133,f152,f177,f189,f215,f283,f319,f320,f378,f435,f439])).

fof(f439,plain,
    ( ~ spl3_9
    | spl3_17 ),
    inference(avatar_contradiction_clause,[],[f438])).

fof(f438,plain,
    ( $false
    | ~ spl3_9
    | spl3_17 ),
    inference(subsumption_resolution,[],[f437,f150])).

fof(f150,plain,
    ( k1_xboole_0 != sK1
    | spl3_17 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl3_17
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f437,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_9 ),
    inference(resolution,[],[f106,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f106,plain,
    ( v1_xboole_0(sK1)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl3_9
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f435,plain,
    ( ~ spl3_1
    | ~ spl3_21
    | spl3_38 ),
    inference(avatar_contradiction_clause,[],[f434])).

fof(f434,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_21
    | spl3_38 ),
    inference(subsumption_resolution,[],[f433,f377])).

fof(f377,plain,
    ( ~ r1_xboole_0(sK1,k1_xboole_0)
    | spl3_38 ),
    inference(avatar_component_clause,[],[f375])).

fof(f375,plain,
    ( spl3_38
  <=> r1_xboole_0(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f433,plain,
    ( r1_xboole_0(sK1,k1_xboole_0)
    | ~ spl3_1
    | ~ spl3_21 ),
    inference(resolution,[],[f325,f41])).

fof(f41,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,X0)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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

fof(f325,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k1_xboole_0,X0)
        | r1_xboole_0(sK1,X0) )
    | ~ spl3_1
    | ~ spl3_21 ),
    inference(superposition,[],[f48,f184])).

fof(f184,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl3_21
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f48,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(sK2,X0)
        | r1_xboole_0(sK1,X0) )
    | ~ spl3_1 ),
    inference(resolution,[],[f46,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
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

fof(f46,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl3_1
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f378,plain,
    ( ~ spl3_38
    | spl3_8
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f330,f182,f100,f375])).

fof(f100,plain,
    ( spl3_8
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f330,plain,
    ( ~ r1_xboole_0(sK1,k1_xboole_0)
    | spl3_8
    | ~ spl3_21 ),
    inference(superposition,[],[f102,f184])).

fof(f102,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f100])).

fof(f320,plain,
    ( k1_xboole_0 != sK1
    | sK0 != k8_setfam_1(sK0,k1_xboole_0)
    | r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
    | ~ r1_tarski(k8_setfam_1(sK0,sK2),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f319,plain,
    ( spl3_35
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f284,f280,f316])).

fof(f316,plain,
    ( spl3_35
  <=> sK0 = k8_setfam_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f280,plain,
    ( spl3_31
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f284,plain,
    ( sK0 = k8_setfam_1(sK0,k1_xboole_0)
    | ~ spl3_31 ),
    inference(resolution,[],[f282,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k8_setfam_1(X0,k1_xboole_0) = X0 ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 != X1
      | k8_setfam_1(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f282,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f280])).

fof(f283,plain,
    ( spl3_31
    | ~ spl3_3
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f223,f149,f58,f280])).

fof(f58,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f223,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_3
    | ~ spl3_17 ),
    inference(superposition,[],[f60,f151])).

fof(f151,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f149])).

fof(f60,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f215,plain,
    ( k8_setfam_1(sK0,sK2) != k1_setfam_1(sK2)
    | k8_setfam_1(sK0,sK1) != k1_setfam_1(sK1)
    | r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
    | ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f189,plain,
    ( spl3_21
    | spl3_22
    | ~ spl3_2
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f161,f114,f53,f186,f182])).

fof(f186,plain,
    ( spl3_22
  <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f53,plain,
    ( spl3_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f114,plain,
    ( spl3_11
  <=> k1_setfam_1(sK2) = k6_setfam_1(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f161,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | k1_xboole_0 = sK2
    | ~ spl3_2
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f62,f116])).

fof(f116,plain,
    ( k1_setfam_1(sK2) = k6_setfam_1(sK0,sK2)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f114])).

fof(f62,plain,
    ( k1_xboole_0 = sK2
    | k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f55,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 = X1
      | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f55,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f177,plain,
    ( spl3_20
    | ~ spl3_3
    | ~ spl3_13
    | spl3_17 ),
    inference(avatar_split_clause,[],[f172,f149,f124,f58,f174])).

fof(f174,plain,
    ( spl3_20
  <=> k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f124,plain,
    ( spl3_13
  <=> k1_setfam_1(sK1) = k6_setfam_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f172,plain,
    ( k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | ~ spl3_3
    | ~ spl3_13
    | spl3_17 ),
    inference(forward_demodulation,[],[f171,f126])).

fof(f126,plain,
    ( k1_setfam_1(sK1) = k6_setfam_1(sK0,sK1)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f124])).

fof(f171,plain,
    ( k8_setfam_1(sK0,sK1) = k6_setfam_1(sK0,sK1)
    | ~ spl3_3
    | spl3_17 ),
    inference(subsumption_resolution,[],[f71,f150])).

fof(f71,plain,
    ( k1_xboole_0 = sK1
    | k8_setfam_1(sK0,sK1) = k6_setfam_1(sK0,sK1)
    | ~ spl3_3 ),
    inference(resolution,[],[f60,f37])).

fof(f152,plain,
    ( spl3_16
    | spl3_17
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f50,f44,f149,f145])).

fof(f145,plain,
    ( spl3_16
  <=> r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f50,plain,
    ( k1_xboole_0 = sK1
    | r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | ~ spl3_1 ),
    inference(resolution,[],[f46,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = X0
      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) ) ),
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

fof(f133,plain,
    ( spl3_14
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f128,f109,f130])).

fof(f130,plain,
    ( spl3_14
  <=> r1_tarski(k8_setfam_1(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f109,plain,
    ( spl3_10
  <=> m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f128,plain,
    ( r1_tarski(k8_setfam_1(sK0,sK2),sK0)
    | ~ spl3_10 ),
    inference(resolution,[],[f111,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f111,plain,
    ( m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f109])).

fof(f127,plain,
    ( spl3_13
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f73,f58,f124])).

fof(f73,plain,
    ( k1_setfam_1(sK1) = k6_setfam_1(sK0,sK1)
    | ~ spl3_3 ),
    inference(resolution,[],[f60,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f117,plain,
    ( spl3_11
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f64,f53,f114])).

fof(f64,plain,
    ( k1_setfam_1(sK2) = k6_setfam_1(sK0,sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f55,f34])).

fof(f112,plain,
    ( spl3_10
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f63,f53,f109])).

fof(f63,plain,
    ( m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(resolution,[],[f55,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).

fof(f107,plain,
    ( ~ spl3_8
    | spl3_9
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f51,f44,f104,f100])).

% (2202)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% (2216)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% (2212)Refutation not found, incomplete strategy% (2212)------------------------------
% (2212)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f51,plain,
    ( v1_xboole_0(sK1)
    | ~ r1_xboole_0(sK1,sK2)
    | ~ spl3_1 ),
    inference(resolution,[],[f46,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1)
      | ~ r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f84,plain,(
    ~ spl3_6 ),
    inference(avatar_split_clause,[],[f27,f81])).

fof(f81,plain,
    ( spl3_6
  <=> r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f27,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).

fof(f61,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f28,f58])).

fof(f28,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f13])).

% (2213)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f56,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f25,f53])).

fof(f25,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f47,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f26,f44])).

fof(f26,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:08:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (2205)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.46  % (2204)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.47  % (2204)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (2212)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f440,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f47,f56,f61,f84,f107,f112,f117,f127,f133,f152,f177,f189,f215,f283,f319,f320,f378,f435,f439])).
% 0.21/0.47  fof(f439,plain,(
% 0.21/0.47    ~spl3_9 | spl3_17),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f438])).
% 0.21/0.47  fof(f438,plain,(
% 0.21/0.47    $false | (~spl3_9 | spl3_17)),
% 0.21/0.47    inference(subsumption_resolution,[],[f437,f150])).
% 0.21/0.47  fof(f150,plain,(
% 0.21/0.47    k1_xboole_0 != sK1 | spl3_17),
% 0.21/0.47    inference(avatar_component_clause,[],[f149])).
% 0.21/0.47  fof(f149,plain,(
% 0.21/0.47    spl3_17 <=> k1_xboole_0 = sK1),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.47  fof(f437,plain,(
% 0.21/0.47    k1_xboole_0 = sK1 | ~spl3_9),
% 0.21/0.47    inference(resolution,[],[f106,f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.47  fof(f106,plain,(
% 0.21/0.47    v1_xboole_0(sK1) | ~spl3_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f104])).
% 0.21/0.47  fof(f104,plain,(
% 0.21/0.47    spl3_9 <=> v1_xboole_0(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.47  fof(f435,plain,(
% 0.21/0.47    ~spl3_1 | ~spl3_21 | spl3_38),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f434])).
% 0.21/0.47  fof(f434,plain,(
% 0.21/0.47    $false | (~spl3_1 | ~spl3_21 | spl3_38)),
% 0.21/0.47    inference(subsumption_resolution,[],[f433,f377])).
% 0.21/0.47  fof(f377,plain,(
% 0.21/0.47    ~r1_xboole_0(sK1,k1_xboole_0) | spl3_38),
% 0.21/0.47    inference(avatar_component_clause,[],[f375])).
% 0.21/0.47  fof(f375,plain,(
% 0.21/0.47    spl3_38 <=> r1_xboole_0(sK1,k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 0.21/0.47  fof(f433,plain,(
% 0.21/0.47    r1_xboole_0(sK1,k1_xboole_0) | (~spl3_1 | ~spl3_21)),
% 0.21/0.47    inference(resolution,[],[f325,f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.21/0.47    inference(equality_resolution,[],[f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ( ! [X0] : (r1_xboole_0(X0,X0) | k1_xboole_0 != X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).
% 0.21/0.47  fof(f325,plain,(
% 0.21/0.47    ( ! [X0] : (~r1_xboole_0(k1_xboole_0,X0) | r1_xboole_0(sK1,X0)) ) | (~spl3_1 | ~spl3_21)),
% 0.21/0.47    inference(superposition,[],[f48,f184])).
% 0.21/0.47  fof(f184,plain,(
% 0.21/0.47    k1_xboole_0 = sK2 | ~spl3_21),
% 0.21/0.47    inference(avatar_component_clause,[],[f182])).
% 0.21/0.47  fof(f182,plain,(
% 0.21/0.47    spl3_21 <=> k1_xboole_0 = sK2),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    ( ! [X0] : (~r1_xboole_0(sK2,X0) | r1_xboole_0(sK1,X0)) ) | ~spl3_1),
% 0.21/0.47    inference(resolution,[],[f46,f40])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(flattening,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    r1_tarski(sK1,sK2) | ~spl3_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f44])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    spl3_1 <=> r1_tarski(sK1,sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.47  fof(f378,plain,(
% 0.21/0.47    ~spl3_38 | spl3_8 | ~spl3_21),
% 0.21/0.47    inference(avatar_split_clause,[],[f330,f182,f100,f375])).
% 0.21/0.47  fof(f100,plain,(
% 0.21/0.47    spl3_8 <=> r1_xboole_0(sK1,sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.47  fof(f330,plain,(
% 0.21/0.47    ~r1_xboole_0(sK1,k1_xboole_0) | (spl3_8 | ~spl3_21)),
% 0.21/0.47    inference(superposition,[],[f102,f184])).
% 0.21/0.47  fof(f102,plain,(
% 0.21/0.47    ~r1_xboole_0(sK1,sK2) | spl3_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f100])).
% 0.21/0.47  fof(f320,plain,(
% 0.21/0.47    k1_xboole_0 != sK1 | sK0 != k8_setfam_1(sK0,k1_xboole_0) | r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) | ~r1_tarski(k8_setfam_1(sK0,sK2),sK0)),
% 0.21/0.47    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.47  fof(f319,plain,(
% 0.21/0.47    spl3_35 | ~spl3_31),
% 0.21/0.47    inference(avatar_split_clause,[],[f284,f280,f316])).
% 0.21/0.47  fof(f316,plain,(
% 0.21/0.47    spl3_35 <=> sK0 = k8_setfam_1(sK0,k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.21/0.47  fof(f280,plain,(
% 0.21/0.47    spl3_31 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.21/0.47  fof(f284,plain,(
% 0.21/0.47    sK0 = k8_setfam_1(sK0,k1_xboole_0) | ~spl3_31),
% 0.21/0.47    inference(resolution,[],[f282,f42])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) | k8_setfam_1(X0,k1_xboole_0) = X0) )),
% 0.21/0.47    inference(equality_resolution,[],[f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 != X1 | k8_setfam_1(X0,X1) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).
% 0.21/0.47  fof(f282,plain,(
% 0.21/0.47    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_31),
% 0.21/0.47    inference(avatar_component_clause,[],[f280])).
% 0.21/0.47  fof(f283,plain,(
% 0.21/0.47    spl3_31 | ~spl3_3 | ~spl3_17),
% 0.21/0.47    inference(avatar_split_clause,[],[f223,f149,f58,f280])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.47  fof(f223,plain,(
% 0.21/0.47    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | (~spl3_3 | ~spl3_17)),
% 0.21/0.47    inference(superposition,[],[f60,f151])).
% 0.21/0.47  fof(f151,plain,(
% 0.21/0.47    k1_xboole_0 = sK1 | ~spl3_17),
% 0.21/0.47    inference(avatar_component_clause,[],[f149])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f58])).
% 0.21/0.47  fof(f215,plain,(
% 0.21/0.47    k8_setfam_1(sK0,sK2) != k1_setfam_1(sK2) | k8_setfam_1(sK0,sK1) != k1_setfam_1(sK1) | r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) | ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))),
% 0.21/0.47    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.47  fof(f189,plain,(
% 0.21/0.47    spl3_21 | spl3_22 | ~spl3_2 | ~spl3_11),
% 0.21/0.47    inference(avatar_split_clause,[],[f161,f114,f53,f186,f182])).
% 0.21/0.47  fof(f186,plain,(
% 0.21/0.47    spl3_22 <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    spl3_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.47  fof(f114,plain,(
% 0.21/0.47    spl3_11 <=> k1_setfam_1(sK2) = k6_setfam_1(sK0,sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.47  fof(f161,plain,(
% 0.21/0.47    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | k1_xboole_0 = sK2 | (~spl3_2 | ~spl3_11)),
% 0.21/0.47    inference(forward_demodulation,[],[f62,f116])).
% 0.21/0.47  fof(f116,plain,(
% 0.21/0.47    k1_setfam_1(sK2) = k6_setfam_1(sK0,sK2) | ~spl3_11),
% 0.21/0.47    inference(avatar_component_clause,[],[f114])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    k1_xboole_0 = sK2 | k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2) | ~spl3_2),
% 0.21/0.47    inference(resolution,[],[f55,f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 = X1 | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f22])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f53])).
% 0.21/0.47  fof(f177,plain,(
% 0.21/0.47    spl3_20 | ~spl3_3 | ~spl3_13 | spl3_17),
% 0.21/0.47    inference(avatar_split_clause,[],[f172,f149,f124,f58,f174])).
% 0.21/0.47  fof(f174,plain,(
% 0.21/0.47    spl3_20 <=> k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.47  fof(f124,plain,(
% 0.21/0.47    spl3_13 <=> k1_setfam_1(sK1) = k6_setfam_1(sK0,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.47  fof(f172,plain,(
% 0.21/0.47    k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | (~spl3_3 | ~spl3_13 | spl3_17)),
% 0.21/0.47    inference(forward_demodulation,[],[f171,f126])).
% 0.21/0.47  fof(f126,plain,(
% 0.21/0.47    k1_setfam_1(sK1) = k6_setfam_1(sK0,sK1) | ~spl3_13),
% 0.21/0.47    inference(avatar_component_clause,[],[f124])).
% 0.21/0.47  fof(f171,plain,(
% 0.21/0.47    k8_setfam_1(sK0,sK1) = k6_setfam_1(sK0,sK1) | (~spl3_3 | spl3_17)),
% 0.21/0.47    inference(subsumption_resolution,[],[f71,f150])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    k1_xboole_0 = sK1 | k8_setfam_1(sK0,sK1) = k6_setfam_1(sK0,sK1) | ~spl3_3),
% 0.21/0.47    inference(resolution,[],[f60,f37])).
% 0.21/0.47  fof(f152,plain,(
% 0.21/0.47    spl3_16 | spl3_17 | ~spl3_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f50,f44,f149,f145])).
% 0.21/0.47  fof(f145,plain,(
% 0.21/0.47    spl3_16 <=> r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    k1_xboole_0 = sK1 | r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | ~spl3_1),
% 0.21/0.47    inference(resolution,[],[f46,f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = X0 | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(flattening,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).
% 0.21/0.47  fof(f133,plain,(
% 0.21/0.47    spl3_14 | ~spl3_10),
% 0.21/0.47    inference(avatar_split_clause,[],[f128,f109,f130])).
% 0.21/0.47  fof(f130,plain,(
% 0.21/0.47    spl3_14 <=> r1_tarski(k8_setfam_1(sK0,sK2),sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.47  fof(f109,plain,(
% 0.21/0.47    spl3_10 <=> m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.47  fof(f128,plain,(
% 0.21/0.47    r1_tarski(k8_setfam_1(sK0,sK2),sK0) | ~spl3_10),
% 0.21/0.47    inference(resolution,[],[f111,f39])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.47  fof(f111,plain,(
% 0.21/0.47    m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0)) | ~spl3_10),
% 0.21/0.47    inference(avatar_component_clause,[],[f109])).
% 0.21/0.47  fof(f127,plain,(
% 0.21/0.47    spl3_13 | ~spl3_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f73,f58,f124])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    k1_setfam_1(sK1) = k6_setfam_1(sK0,sK1) | ~spl3_3),
% 0.21/0.47    inference(resolution,[],[f60,f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k6_setfam_1(X0,X1) = k1_setfam_1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).
% 0.21/0.47  fof(f117,plain,(
% 0.21/0.47    spl3_11 | ~spl3_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f64,f53,f114])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    k1_setfam_1(sK2) = k6_setfam_1(sK0,sK2) | ~spl3_2),
% 0.21/0.47    inference(resolution,[],[f55,f34])).
% 0.21/0.47  fof(f112,plain,(
% 0.21/0.47    spl3_10 | ~spl3_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f63,f53,f109])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0)) | ~spl3_2),
% 0.21/0.47    inference(resolution,[],[f55,f35])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).
% 0.21/0.47  fof(f107,plain,(
% 0.21/0.47    ~spl3_8 | spl3_9 | ~spl3_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f51,f44,f104,f100])).
% 0.21/0.48  % (2202)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (2216)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.48  % (2212)Refutation not found, incomplete strategy% (2212)------------------------------
% 0.21/0.48  % (2212)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    v1_xboole_0(sK1) | ~r1_xboole_0(sK1,sK2) | ~spl3_1),
% 0.21/0.48    inference(resolution,[],[f46,f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X1,X0) | v1_xboole_0(X1) | ~r1_xboole_0(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.21/0.48    inference(flattening,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    ~spl3_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f27,f81])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    spl3_6 <=> r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.48    inference(flattening,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 0.21/0.48    inference(negated_conjecture,[],[f10])).
% 0.21/0.48  fof(f10,conjecture,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    spl3_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f28,f58])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  % (2213)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f25,f53])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    spl3_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f26,f44])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    r1_tarski(sK1,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (2204)------------------------------
% 0.21/0.48  % (2204)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (2204)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (2204)Memory used [KB]: 10874
% 0.21/0.48  % (2204)Time elapsed: 0.058 s
% 0.21/0.48  % (2204)------------------------------
% 0.21/0.48  % (2204)------------------------------
% 0.21/0.48  % (2210)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.48  % (2213)Refutation not found, incomplete strategy% (2213)------------------------------
% 0.21/0.48  % (2213)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (2213)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (2213)Memory used [KB]: 6012
% 0.21/0.48  % (2213)Time elapsed: 0.072 s
% 0.21/0.48  % (2213)------------------------------
% 0.21/0.48  % (2213)------------------------------
% 0.21/0.48  % (2212)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  % (2200)Success in time 0.123 s
%------------------------------------------------------------------------------
