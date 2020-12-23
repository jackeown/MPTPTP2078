%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 247 expanded)
%              Number of leaves         :   32 ( 108 expanded)
%              Depth                    :    8
%              Number of atoms          :  358 ( 666 expanded)
%              Number of equality atoms :   64 ( 118 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (24053)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f455,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f57,f62,f67,f73,f86,f111,f118,f155,f180,f197,f244,f259,f260,f275,f292,f307,f330,f378,f390,f398,f433,f454])).

fof(f454,plain,
    ( ~ spl3_2
    | spl3_17
    | ~ spl3_29 ),
    inference(avatar_contradiction_clause,[],[f452])).

fof(f452,plain,
    ( $false
    | ~ spl3_2
    | spl3_17
    | ~ spl3_29 ),
    inference(unit_resulting_resolution,[],[f274,f56,f274,f149,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X2)
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).

fof(f149,plain,
    ( k1_xboole_0 != sK1
    | spl3_17 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl3_17
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f56,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl3_2
  <=> r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f274,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f272])).

fof(f272,plain,
    ( spl3_29
  <=> r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f433,plain,
    ( spl3_5
    | ~ spl3_17
    | ~ spl3_27
    | ~ spl3_30 ),
    inference(avatar_contradiction_clause,[],[f432])).

fof(f432,plain,
    ( $false
    | spl3_5
    | ~ spl3_17
    | ~ spl3_27
    | ~ spl3_30 ),
    inference(subsumption_resolution,[],[f431,f46])).

fof(f46,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f431,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl3_5
    | ~ spl3_17
    | ~ spl3_27
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f430,f291])).

fof(f291,plain,
    ( sK0 = k8_setfam_1(sK0,k1_xboole_0)
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f289])).

fof(f289,plain,
    ( spl3_30
  <=> sK0 = k8_setfam_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f430,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,k1_xboole_0),sK0)
    | spl3_5
    | ~ spl3_17
    | ~ spl3_27
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f394,f254])).

fof(f254,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl3_27
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f394,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),sK0)
    | spl3_5
    | ~ spl3_17
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f393,f291])).

fof(f393,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0))
    | spl3_5
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f72,f150])).

fof(f150,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f148])).

fof(f72,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl3_5
  <=> r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f398,plain,
    ( ~ spl3_38
    | spl3_5
    | ~ spl3_17
    | ~ spl3_28
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f395,f289,f256,f148,f70,f368])).

fof(f368,plain,
    ( spl3_38
  <=> r1_tarski(k1_setfam_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f256,plain,
    ( spl3_28
  <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f395,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),sK0)
    | spl3_5
    | ~ spl3_17
    | ~ spl3_28
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f394,f258])).

fof(f258,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f256])).

fof(f390,plain,
    ( spl3_38
    | ~ spl3_39 ),
    inference(avatar_contradiction_clause,[],[f389])).

fof(f389,plain,
    ( $false
    | spl3_38
    | ~ spl3_39 ),
    inference(subsumption_resolution,[],[f387,f370])).

fof(f370,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),sK0)
    | spl3_38 ),
    inference(avatar_component_clause,[],[f368])).

fof(f387,plain,
    ( r1_tarski(k1_setfam_1(sK2),sK0)
    | ~ spl3_39 ),
    inference(resolution,[],[f377,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f377,plain,
    ( m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f375])).

fof(f375,plain,
    ( spl3_39
  <=> m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f378,plain,
    ( spl3_39
    | ~ spl3_4
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f297,f256,f64,f375])).

fof(f64,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f297,plain,
    ( m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl3_4
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f296,f66])).

fof(f66,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f296,plain,
    ( m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_28 ),
    inference(superposition,[],[f35,f258])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).

fof(f330,plain,
    ( spl3_17
    | ~ spl3_1
    | spl3_32 ),
    inference(avatar_split_clause,[],[f315,f304,f49,f148])).

fof(f49,plain,
    ( spl3_1
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f304,plain,
    ( spl3_32
  <=> r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f315,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_1
    | spl3_32 ),
    inference(subsumption_resolution,[],[f310,f51])).

fof(f51,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f310,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_tarski(sK1,sK2)
    | spl3_32 ),
    inference(resolution,[],[f306,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

fof(f306,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | spl3_32 ),
    inference(avatar_component_clause,[],[f304])).

fof(f307,plain,
    ( ~ spl3_32
    | spl3_20
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f295,f256,f177,f304])).

fof(f177,plain,
    ( spl3_20
  <=> r1_tarski(k8_setfam_1(sK0,sK2),k1_setfam_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f295,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | spl3_20
    | ~ spl3_28 ),
    inference(backward_demodulation,[],[f179,f258])).

fof(f179,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k1_setfam_1(sK1))
    | spl3_20 ),
    inference(avatar_component_clause,[],[f177])).

fof(f292,plain,
    ( spl3_30
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f281,f194,f289])).

fof(f194,plain,
    ( spl3_22
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f281,plain,
    ( sK0 = k8_setfam_1(sK0,k1_xboole_0)
    | ~ spl3_22 ),
    inference(resolution,[],[f196,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k8_setfam_1(X0,k1_xboole_0) = X0 ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f196,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f194])).

fof(f275,plain,
    ( spl3_29
    | ~ spl3_1
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f262,f252,f49,f272])).

fof(f262,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ spl3_1
    | ~ spl3_27 ),
    inference(backward_demodulation,[],[f51,f254])).

fof(f260,plain,
    ( k1_xboole_0 != sK2
    | r1_tarski(k1_xboole_0,k1_zfmisc_1(sK0))
    | ~ r1_tarski(sK2,k1_zfmisc_1(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f259,plain,
    ( spl3_27
    | spl3_28
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f250,f115,f64,f256,f252])).

fof(f115,plain,
    ( spl3_11
  <=> k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f250,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | k1_xboole_0 = sK2
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f120,f117])).

fof(f117,plain,
    ( k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f115])).

fof(f120,plain,
    ( k1_xboole_0 = sK2
    | k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2)
    | ~ spl3_4 ),
    inference(resolution,[],[f36,f66])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 = X1
      | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f244,plain,
    ( ~ spl3_26
    | spl3_22 ),
    inference(avatar_split_clause,[],[f242,f194,f234])).

fof(f234,plain,
    ( spl3_26
  <=> r1_tarski(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f242,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_zfmisc_1(sK0))
    | spl3_22 ),
    inference(resolution,[],[f195,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f195,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl3_22 ),
    inference(avatar_component_clause,[],[f194])).

fof(f197,plain,
    ( spl3_22
    | ~ spl3_3
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f188,f148,f59,f194])).

fof(f59,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f188,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_3
    | ~ spl3_17 ),
    inference(backward_demodulation,[],[f61,f150])).

fof(f61,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f180,plain,
    ( ~ spl3_20
    | spl3_5
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f173,f152,f70,f177])).

fof(f152,plain,
    ( spl3_18
  <=> k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f173,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k1_setfam_1(sK1))
    | spl3_5
    | ~ spl3_18 ),
    inference(backward_demodulation,[],[f72,f154])).

fof(f154,plain,
    ( k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f152])).

fof(f155,plain,
    ( spl3_17
    | spl3_18
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f137,f108,f59,f152,f148])).

fof(f108,plain,
    ( spl3_10
  <=> k6_setfam_1(sK0,sK1) = k1_setfam_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f137,plain,
    ( k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | k1_xboole_0 = sK1
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f119,f110])).

fof(f110,plain,
    ( k6_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f108])).

fof(f119,plain,
    ( k1_xboole_0 = sK1
    | k8_setfam_1(sK0,sK1) = k6_setfam_1(sK0,sK1)
    | ~ spl3_3 ),
    inference(resolution,[],[f36,f61])).

fof(f118,plain,
    ( spl3_11
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f103,f64,f115])).

fof(f103,plain,
    ( k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl3_4 ),
    inference(resolution,[],[f34,f66])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f111,plain,
    ( spl3_10
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f102,f59,f108])).

fof(f102,plain,
    ( k6_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | ~ spl3_3 ),
    inference(resolution,[],[f34,f61])).

fof(f86,plain,
    ( spl3_7
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f75,f64,f83])).

fof(f83,plain,
    ( spl3_7
  <=> r1_tarski(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f75,plain,
    ( r1_tarski(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_4 ),
    inference(resolution,[],[f41,f66])).

fof(f73,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f30,f70])).

fof(f30,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f22,f21])).

fof(f21,plain,
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

fof(f22,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1))
        & r1_tarski(sK1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
   => ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).

fof(f67,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f28,f64])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f62,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f27,f59])).

fof(f27,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f57,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f44,f54])).

fof(f44,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f52,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f29,f49])).

fof(f29,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:10:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.48  % (24041)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.48  % (24042)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.49  % (24057)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.49  % (24041)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  % (24053)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  fof(f455,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f52,f57,f62,f67,f73,f86,f111,f118,f155,f180,f197,f244,f259,f260,f275,f292,f307,f330,f378,f390,f398,f433,f454])).
% 0.21/0.49  fof(f454,plain,(
% 0.21/0.49    ~spl3_2 | spl3_17 | ~spl3_29),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f452])).
% 0.21/0.49  fof(f452,plain,(
% 0.21/0.49    $false | (~spl3_2 | spl3_17 | ~spl3_29)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f274,f56,f274,f149,f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | k1_xboole_0 = X0 | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.49    inference(flattening,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).
% 0.21/0.49  fof(f149,plain,(
% 0.21/0.49    k1_xboole_0 != sK1 | spl3_17),
% 0.21/0.49    inference(avatar_component_clause,[],[f148])).
% 0.21/0.49  fof(f148,plain,(
% 0.21/0.49    spl3_17 <=> k1_xboole_0 = sK1),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl3_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    spl3_2 <=> r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.49  fof(f274,plain,(
% 0.21/0.49    r1_tarski(sK1,k1_xboole_0) | ~spl3_29),
% 0.21/0.49    inference(avatar_component_clause,[],[f272])).
% 0.21/0.49  fof(f272,plain,(
% 0.21/0.49    spl3_29 <=> r1_tarski(sK1,k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.21/0.49  fof(f433,plain,(
% 0.21/0.49    spl3_5 | ~spl3_17 | ~spl3_27 | ~spl3_30),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f432])).
% 0.21/0.49  fof(f432,plain,(
% 0.21/0.49    $false | (spl3_5 | ~spl3_17 | ~spl3_27 | ~spl3_30)),
% 0.21/0.49    inference(subsumption_resolution,[],[f431,f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.49    inference(equality_resolution,[],[f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.49    inference(flattening,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.49    inference(nnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.49  fof(f431,plain,(
% 0.21/0.49    ~r1_tarski(sK0,sK0) | (spl3_5 | ~spl3_17 | ~spl3_27 | ~spl3_30)),
% 0.21/0.49    inference(forward_demodulation,[],[f430,f291])).
% 0.21/0.49  fof(f291,plain,(
% 0.21/0.49    sK0 = k8_setfam_1(sK0,k1_xboole_0) | ~spl3_30),
% 0.21/0.49    inference(avatar_component_clause,[],[f289])).
% 0.21/0.49  fof(f289,plain,(
% 0.21/0.49    spl3_30 <=> sK0 = k8_setfam_1(sK0,k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.21/0.49  fof(f430,plain,(
% 0.21/0.49    ~r1_tarski(k8_setfam_1(sK0,k1_xboole_0),sK0) | (spl3_5 | ~spl3_17 | ~spl3_27 | ~spl3_30)),
% 0.21/0.49    inference(forward_demodulation,[],[f394,f254])).
% 0.21/0.49  fof(f254,plain,(
% 0.21/0.49    k1_xboole_0 = sK2 | ~spl3_27),
% 0.21/0.49    inference(avatar_component_clause,[],[f252])).
% 0.21/0.49  fof(f252,plain,(
% 0.21/0.49    spl3_27 <=> k1_xboole_0 = sK2),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.21/0.49  fof(f394,plain,(
% 0.21/0.49    ~r1_tarski(k8_setfam_1(sK0,sK2),sK0) | (spl3_5 | ~spl3_17 | ~spl3_30)),
% 0.21/0.49    inference(forward_demodulation,[],[f393,f291])).
% 0.21/0.49  fof(f393,plain,(
% 0.21/0.49    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0)) | (spl3_5 | ~spl3_17)),
% 0.21/0.49    inference(forward_demodulation,[],[f72,f150])).
% 0.21/0.49  fof(f150,plain,(
% 0.21/0.49    k1_xboole_0 = sK1 | ~spl3_17),
% 0.21/0.49    inference(avatar_component_clause,[],[f148])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) | spl3_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f70])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    spl3_5 <=> r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.49  fof(f398,plain,(
% 0.21/0.49    ~spl3_38 | spl3_5 | ~spl3_17 | ~spl3_28 | ~spl3_30),
% 0.21/0.49    inference(avatar_split_clause,[],[f395,f289,f256,f148,f70,f368])).
% 0.21/0.49  fof(f368,plain,(
% 0.21/0.49    spl3_38 <=> r1_tarski(k1_setfam_1(sK2),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 0.21/0.49  fof(f256,plain,(
% 0.21/0.49    spl3_28 <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.21/0.49  fof(f395,plain,(
% 0.21/0.49    ~r1_tarski(k1_setfam_1(sK2),sK0) | (spl3_5 | ~spl3_17 | ~spl3_28 | ~spl3_30)),
% 0.21/0.49    inference(forward_demodulation,[],[f394,f258])).
% 0.21/0.49  fof(f258,plain,(
% 0.21/0.49    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~spl3_28),
% 0.21/0.49    inference(avatar_component_clause,[],[f256])).
% 0.21/0.49  fof(f390,plain,(
% 0.21/0.49    spl3_38 | ~spl3_39),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f389])).
% 0.21/0.49  fof(f389,plain,(
% 0.21/0.49    $false | (spl3_38 | ~spl3_39)),
% 0.21/0.49    inference(subsumption_resolution,[],[f387,f370])).
% 0.21/0.49  fof(f370,plain,(
% 0.21/0.49    ~r1_tarski(k1_setfam_1(sK2),sK0) | spl3_38),
% 0.21/0.49    inference(avatar_component_clause,[],[f368])).
% 0.21/0.49  fof(f387,plain,(
% 0.21/0.49    r1_tarski(k1_setfam_1(sK2),sK0) | ~spl3_39),
% 0.21/0.49    inference(resolution,[],[f377,f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.49    inference(nnf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.49  fof(f377,plain,(
% 0.21/0.49    m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | ~spl3_39),
% 0.21/0.49    inference(avatar_component_clause,[],[f375])).
% 0.21/0.49  fof(f375,plain,(
% 0.21/0.49    spl3_39 <=> m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.21/0.49  fof(f378,plain,(
% 0.21/0.49    spl3_39 | ~spl3_4 | ~spl3_28),
% 0.21/0.49    inference(avatar_split_clause,[],[f297,f256,f64,f375])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    spl3_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.49  fof(f297,plain,(
% 0.21/0.49    m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | (~spl3_4 | ~spl3_28)),
% 0.21/0.49    inference(subsumption_resolution,[],[f296,f66])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f64])).
% 0.21/0.49  fof(f296,plain,(
% 0.21/0.49    m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_28),
% 0.21/0.49    inference(superposition,[],[f35,f258])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).
% 0.21/0.49  fof(f330,plain,(
% 0.21/0.49    spl3_17 | ~spl3_1 | spl3_32),
% 0.21/0.49    inference(avatar_split_clause,[],[f315,f304,f49,f148])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    spl3_1 <=> r1_tarski(sK1,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.49  fof(f304,plain,(
% 0.21/0.49    spl3_32 <=> r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.21/0.49  fof(f315,plain,(
% 0.21/0.49    k1_xboole_0 = sK1 | (~spl3_1 | spl3_32)),
% 0.21/0.49    inference(subsumption_resolution,[],[f310,f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    r1_tarski(sK1,sK2) | ~spl3_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f49])).
% 0.21/0.49  fof(f310,plain,(
% 0.21/0.49    k1_xboole_0 = sK1 | ~r1_tarski(sK1,sK2) | spl3_32),
% 0.21/0.49    inference(resolution,[],[f306,f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.49    inference(flattening,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).
% 0.21/0.49  fof(f306,plain,(
% 0.21/0.49    ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | spl3_32),
% 0.21/0.49    inference(avatar_component_clause,[],[f304])).
% 0.21/0.49  fof(f307,plain,(
% 0.21/0.49    ~spl3_32 | spl3_20 | ~spl3_28),
% 0.21/0.49    inference(avatar_split_clause,[],[f295,f256,f177,f304])).
% 0.21/0.49  fof(f177,plain,(
% 0.21/0.49    spl3_20 <=> r1_tarski(k8_setfam_1(sK0,sK2),k1_setfam_1(sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.49  fof(f295,plain,(
% 0.21/0.49    ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | (spl3_20 | ~spl3_28)),
% 0.21/0.49    inference(backward_demodulation,[],[f179,f258])).
% 0.21/0.49  fof(f179,plain,(
% 0.21/0.49    ~r1_tarski(k8_setfam_1(sK0,sK2),k1_setfam_1(sK1)) | spl3_20),
% 0.21/0.49    inference(avatar_component_clause,[],[f177])).
% 0.21/0.49  fof(f292,plain,(
% 0.21/0.49    spl3_30 | ~spl3_22),
% 0.21/0.49    inference(avatar_split_clause,[],[f281,f194,f289])).
% 0.21/0.49  fof(f194,plain,(
% 0.21/0.49    spl3_22 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.49  fof(f281,plain,(
% 0.21/0.49    sK0 = k8_setfam_1(sK0,k1_xboole_0) | ~spl3_22),
% 0.21/0.49    inference(resolution,[],[f196,f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) | k8_setfam_1(X0,k1_xboole_0) = X0) )),
% 0.21/0.50    inference(equality_resolution,[],[f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).
% 0.21/0.50  fof(f196,plain,(
% 0.21/0.50    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_22),
% 0.21/0.50    inference(avatar_component_clause,[],[f194])).
% 0.21/0.50  fof(f275,plain,(
% 0.21/0.50    spl3_29 | ~spl3_1 | ~spl3_27),
% 0.21/0.50    inference(avatar_split_clause,[],[f262,f252,f49,f272])).
% 0.21/0.50  fof(f262,plain,(
% 0.21/0.50    r1_tarski(sK1,k1_xboole_0) | (~spl3_1 | ~spl3_27)),
% 0.21/0.50    inference(backward_demodulation,[],[f51,f254])).
% 0.21/0.50  fof(f260,plain,(
% 0.21/0.50    k1_xboole_0 != sK2 | r1_tarski(k1_xboole_0,k1_zfmisc_1(sK0)) | ~r1_tarski(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.50  fof(f259,plain,(
% 0.21/0.50    spl3_27 | spl3_28 | ~spl3_4 | ~spl3_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f250,f115,f64,f256,f252])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    spl3_11 <=> k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.50  fof(f250,plain,(
% 0.21/0.50    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | k1_xboole_0 = sK2 | (~spl3_4 | ~spl3_11)),
% 0.21/0.50    inference(forward_demodulation,[],[f120,f117])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~spl3_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f115])).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    k1_xboole_0 = sK2 | k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2) | ~spl3_4),
% 0.21/0.50    inference(resolution,[],[f36,f66])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 = X1 | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f244,plain,(
% 0.21/0.50    ~spl3_26 | spl3_22),
% 0.21/0.50    inference(avatar_split_clause,[],[f242,f194,f234])).
% 0.21/0.50  fof(f234,plain,(
% 0.21/0.50    spl3_26 <=> r1_tarski(k1_xboole_0,k1_zfmisc_1(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.21/0.50  fof(f242,plain,(
% 0.21/0.50    ~r1_tarski(k1_xboole_0,k1_zfmisc_1(sK0)) | spl3_22),
% 0.21/0.50    inference(resolution,[],[f195,f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f195,plain,(
% 0.21/0.50    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl3_22),
% 0.21/0.50    inference(avatar_component_clause,[],[f194])).
% 0.21/0.50  fof(f197,plain,(
% 0.21/0.50    spl3_22 | ~spl3_3 | ~spl3_17),
% 0.21/0.50    inference(avatar_split_clause,[],[f188,f148,f59,f194])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.50  fof(f188,plain,(
% 0.21/0.50    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | (~spl3_3 | ~spl3_17)),
% 0.21/0.50    inference(backward_demodulation,[],[f61,f150])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f59])).
% 0.21/0.50  fof(f180,plain,(
% 0.21/0.50    ~spl3_20 | spl3_5 | ~spl3_18),
% 0.21/0.50    inference(avatar_split_clause,[],[f173,f152,f70,f177])).
% 0.21/0.50  fof(f152,plain,(
% 0.21/0.50    spl3_18 <=> k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.50  fof(f173,plain,(
% 0.21/0.50    ~r1_tarski(k8_setfam_1(sK0,sK2),k1_setfam_1(sK1)) | (spl3_5 | ~spl3_18)),
% 0.21/0.50    inference(backward_demodulation,[],[f72,f154])).
% 0.21/0.50  fof(f154,plain,(
% 0.21/0.50    k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | ~spl3_18),
% 0.21/0.50    inference(avatar_component_clause,[],[f152])).
% 0.21/0.50  fof(f155,plain,(
% 0.21/0.50    spl3_17 | spl3_18 | ~spl3_3 | ~spl3_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f137,f108,f59,f152,f148])).
% 0.21/0.50  fof(f108,plain,(
% 0.21/0.50    spl3_10 <=> k6_setfam_1(sK0,sK1) = k1_setfam_1(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.50  fof(f137,plain,(
% 0.21/0.50    k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | k1_xboole_0 = sK1 | (~spl3_3 | ~spl3_10)),
% 0.21/0.50    inference(forward_demodulation,[],[f119,f110])).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    k6_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | ~spl3_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f108])).
% 0.21/0.50  fof(f119,plain,(
% 0.21/0.50    k1_xboole_0 = sK1 | k8_setfam_1(sK0,sK1) = k6_setfam_1(sK0,sK1) | ~spl3_3),
% 0.21/0.50    inference(resolution,[],[f36,f61])).
% 0.21/0.50  fof(f118,plain,(
% 0.21/0.50    spl3_11 | ~spl3_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f103,f64,f115])).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~spl3_4),
% 0.21/0.50    inference(resolution,[],[f34,f66])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k6_setfam_1(X0,X1) = k1_setfam_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).
% 0.21/0.50  fof(f111,plain,(
% 0.21/0.50    spl3_10 | ~spl3_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f102,f59,f108])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    k6_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | ~spl3_3),
% 0.21/0.50    inference(resolution,[],[f34,f61])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    spl3_7 | ~spl3_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f75,f64,f83])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    spl3_7 <=> r1_tarski(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    r1_tarski(sK2,k1_zfmisc_1(sK0)) | ~spl3_4),
% 0.21/0.50    inference(resolution,[],[f41,f66])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    ~spl3_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f30,f70])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    (~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f22,f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (~r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ? [X2] : (~r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) => (~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.50    inference(flattening,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 0.21/0.50    inference(negated_conjecture,[],[f9])).
% 0.21/0.50  fof(f9,conjecture,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    spl3_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f28,f64])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    spl3_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f27,f59])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    spl3_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f44,f54])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.21/0.50    inference(equality_resolution,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    spl3_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f29,f49])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    r1_tarski(sK1,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (24041)------------------------------
% 0.21/0.50  % (24041)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (24041)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (24041)Memory used [KB]: 6396
% 0.21/0.50  % (24041)Time elapsed: 0.094 s
% 0.21/0.50  % (24041)------------------------------
% 0.21/0.50  % (24041)------------------------------
% 0.21/0.50  % (24038)Success in time 0.141 s
%------------------------------------------------------------------------------
