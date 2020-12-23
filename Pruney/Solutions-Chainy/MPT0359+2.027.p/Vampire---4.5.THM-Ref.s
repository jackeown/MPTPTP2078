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
% DateTime   : Thu Dec  3 12:44:42 EST 2020

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 392 expanded)
%              Number of leaves         :   28 ( 134 expanded)
%              Depth                    :   17
%              Number of atoms          :  236 ( 617 expanded)
%              Number of equality atoms :  110 ( 367 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f435,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f92,f101,f126,f140,f241,f246,f344,f415])).

fof(f415,plain,
    ( spl2_3
    | ~ spl2_5
    | ~ spl2_11 ),
    inference(avatar_contradiction_clause,[],[f414])).

fof(f414,plain,
    ( $false
    | spl2_3
    | ~ spl2_5
    | ~ spl2_11 ),
    inference(subsumption_resolution,[],[f413,f90])).

fof(f90,plain,
    ( sK0 != sK1
    | spl2_3 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl2_3
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f413,plain,
    ( sK0 = sK1
    | ~ spl2_5
    | ~ spl2_11 ),
    inference(forward_demodulation,[],[f394,f68])).

fof(f68,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f41,f65])).

fof(f65,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f45,f40])).

fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f45,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

fof(f41,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f394,plain,
    ( sK1 = k3_subset_1(sK0,k1_xboole_0)
    | ~ spl2_5
    | ~ spl2_11 ),
    inference(backward_demodulation,[],[f139,f392])).

fof(f392,plain,
    ( k1_xboole_0 = k3_subset_1(sK0,sK1)
    | ~ spl2_11 ),
    inference(forward_demodulation,[],[f390,f43])).

fof(f43,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f390,plain,
    ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK1,sK1)
    | ~ spl2_11 ),
    inference(superposition,[],[f225,f343])).

fof(f343,plain,
    ( sK1 = k5_xboole_0(sK1,k3_subset_1(sK0,sK1))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f341])).

fof(f341,plain,
    ( spl2_11
  <=> sK1 = k5_xboole_0(sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f225,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(backward_demodulation,[],[f141,f224])).

fof(f224,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(forward_demodulation,[],[f223,f222])).

fof(f222,plain,(
    ! [X0] : k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(forward_demodulation,[],[f221,f169])).

fof(f169,plain,(
    ! [X4] : k3_tarski(k2_enumset1(X4,X4,X4,k1_xboole_0)) = X4 ),
    inference(forward_demodulation,[],[f168,f154])).

fof(f154,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f153,f68])).

fof(f153,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f148,f114])).

fof(f114,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f102,f46])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

% (4567)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
fof(f102,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f39,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f39,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f148,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f42,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f54,f50])).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f42,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f21])).

% (4564)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
fof(f21,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f168,plain,(
    ! [X4] : k3_tarski(k2_enumset1(X4,X4,X4,k1_xboole_0)) = k5_xboole_0(X4,k1_xboole_0) ),
    inference(forward_demodulation,[],[f163,f43])).

fof(f163,plain,(
    ! [X4] : k3_tarski(k2_enumset1(X4,X4,X4,k1_xboole_0)) = k5_xboole_0(X4,k5_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(superposition,[],[f71,f102])).

fof(f71,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f51,f64,f50])).

fof(f64,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f48,f63])).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f49,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f49,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f221,plain,(
    ! [X0] : k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = k3_tarski(k2_enumset1(X0,X0,X0,X0)) ),
    inference(forward_demodulation,[],[f218,f43])).

fof(f218,plain,(
    ! [X0] : k3_tarski(k2_enumset1(X0,X0,X0,X0)) = k3_tarski(k2_enumset1(X0,X0,X0,k5_xboole_0(X0,X0))) ),
    inference(superposition,[],[f72,f103])).

fof(f103,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(unit_resulting_resolution,[],[f74,f53])).

fof(f74,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f72,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f52,f64,f50,f64])).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f223,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = k3_tarski(k2_enumset1(X1,X1,X1,X1)) ),
    inference(forward_demodulation,[],[f219,f141])).

fof(f219,plain,(
    ! [X1] : k3_tarski(k2_enumset1(X1,X1,X1,X1)) = k5_xboole_0(X1,k5_xboole_0(X1,X1)) ),
    inference(superposition,[],[f71,f103])).

fof(f141,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f62,f43])).

fof(f62,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f139,plain,
    ( sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl2_5
  <=> sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f344,plain,
    ( spl2_11
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f271,f243,f238,f341])).

fof(f238,plain,
    ( spl2_7
  <=> k3_subset_1(sK0,sK1) = k3_xboole_0(k3_subset_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f243,plain,
    ( spl2_8
  <=> k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f271,plain,
    ( sK1 = k5_xboole_0(sK1,k3_subset_1(sK0,sK1))
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f268,f270])).

fof(f270,plain,
    ( sK1 = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK0))
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f267,f264])).

fof(f264,plain,
    ( sK1 = k3_tarski(k2_enumset1(sK1,sK1,sK1,k3_subset_1(sK0,sK1)))
    | ~ spl2_7 ),
    inference(forward_demodulation,[],[f263,f169])).

fof(f263,plain,
    ( k3_tarski(k2_enumset1(sK1,sK1,sK1,k3_subset_1(sK0,sK1))) = k3_tarski(k2_enumset1(sK1,sK1,sK1,k1_xboole_0))
    | ~ spl2_7 ),
    inference(forward_demodulation,[],[f258,f43])).

fof(f258,plain,
    ( k3_tarski(k2_enumset1(sK1,sK1,sK1,k3_subset_1(sK0,sK1))) = k3_tarski(k2_enumset1(sK1,sK1,sK1,k5_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1))))
    | ~ spl2_7 ),
    inference(superposition,[],[f72,f240])).

% (4567)Refutation not found, incomplete strategy% (4567)------------------------------
% (4567)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (4567)Termination reason: Refutation not found, incomplete strategy

% (4567)Memory used [KB]: 10618
% (4567)Time elapsed: 0.136 s
% (4567)------------------------------
% (4567)------------------------------
fof(f240,plain,
    ( k3_subset_1(sK0,sK1) = k3_xboole_0(k3_subset_1(sK0,sK1),sK1)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f238])).

fof(f267,plain,
    ( k3_tarski(k2_enumset1(sK1,sK1,sK1,k3_subset_1(sK0,sK1))) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK0))
    | ~ spl2_8 ),
    inference(superposition,[],[f72,f245])).

fof(f245,plain,
    ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f243])).

fof(f268,plain,
    ( k3_tarski(k2_enumset1(sK1,sK1,sK1,sK0)) = k5_xboole_0(sK1,k3_subset_1(sK0,sK1))
    | ~ spl2_8 ),
    inference(superposition,[],[f71,f245])).

fof(f246,plain,
    ( spl2_8
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f149,f80,f243])).

fof(f80,plain,
    ( spl2_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f149,plain,
    ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f82,f73])).

fof(f82,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f241,plain,
    ( spl2_7
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f133,f85,f238])).

fof(f85,plain,
    ( spl2_2
  <=> r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f133,plain,
    ( k3_subset_1(sK0,sK1) = k3_xboole_0(k3_subset_1(sK0,sK1),sK1)
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f87,f53])).

fof(f87,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f140,plain,
    ( spl2_5
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f131,f80,f137])).

fof(f131,plain,
    ( sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f82,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f126,plain,(
    spl2_4 ),
    inference(avatar_contradiction_clause,[],[f125])).

fof(f125,plain,
    ( $false
    | spl2_4 ),
    inference(subsumption_resolution,[],[f124,f39])).

fof(f124,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | spl2_4 ),
    inference(backward_demodulation,[],[f100,f123])).

fof(f123,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f120,f68])).

fof(f120,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f42,f55])).

fof(f100,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl2_4
  <=> r1_tarski(k3_subset_1(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f101,plain,
    ( ~ spl2_4
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f95,f89,f98])).

fof(f95,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f94,f91])).

fof(f91,plain,
    ( sK0 = sK1
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f89])).

fof(f94,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | sK0 != sK1
    | ~ spl2_3 ),
    inference(backward_demodulation,[],[f77,f91])).

fof(f77,plain,
    ( sK0 != sK1
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(backward_demodulation,[],[f66,f68])).

fof(f66,plain,
    ( sK1 != k3_subset_1(sK0,k1_xboole_0)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(definition_unfolding,[],[f38,f65])).

fof(f38,plain,
    ( sK1 != k2_subset_1(sK0)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( sK1 != k2_subset_1(sK0)
      | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & ( sK1 = k2_subset_1(sK0)
      | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f31])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( ( k2_subset_1(X0) != X1
          | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
        & ( k2_subset_1(X0) = X1
          | r1_tarski(k3_subset_1(X0,X1),X1) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( sK1 != k2_subset_1(sK0)
        | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
      & ( sK1 = k2_subset_1(sK0)
        | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

fof(f92,plain,
    ( spl2_2
    | spl2_3 ),
    inference(avatar_split_clause,[],[f76,f89,f85])).

fof(f76,plain,
    ( sK0 = sK1
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(backward_demodulation,[],[f67,f68])).

fof(f67,plain,
    ( sK1 = k3_subset_1(sK0,k1_xboole_0)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(definition_unfolding,[],[f37,f65])).

% (4573)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
fof(f37,plain,
    ( sK1 = k2_subset_1(sK0)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f83,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f36,f80])).

fof(f36,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n012.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:07:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.52  % (4571)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.53  % (4579)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.53  % (4556)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (4553)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (4579)Refutation not found, incomplete strategy% (4579)------------------------------
% 0.21/0.53  % (4579)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (4579)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (4579)Memory used [KB]: 10746
% 0.21/0.53  % (4579)Time elapsed: 0.115 s
% 0.21/0.53  % (4579)------------------------------
% 0.21/0.53  % (4579)------------------------------
% 0.21/0.53  % (4552)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (4552)Refutation not found, incomplete strategy% (4552)------------------------------
% 0.21/0.53  % (4552)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (4552)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (4552)Memory used [KB]: 1663
% 0.21/0.53  % (4552)Time elapsed: 0.113 s
% 0.21/0.53  % (4552)------------------------------
% 0.21/0.53  % (4552)------------------------------
% 0.21/0.53  % (4555)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (4551)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (4554)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (4574)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.30/0.54  % (4563)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.30/0.54  % (4557)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.30/0.54  % (4578)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.30/0.54  % (4580)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.30/0.54  % (4563)Refutation not found, incomplete strategy% (4563)------------------------------
% 1.30/0.54  % (4563)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (4572)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.30/0.54  % (4563)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.54  
% 1.30/0.54  % (4563)Memory used [KB]: 10746
% 1.30/0.54  % (4563)Time elapsed: 0.123 s
% 1.30/0.54  % (4563)------------------------------
% 1.30/0.54  % (4563)------------------------------
% 1.30/0.54  % (4565)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.30/0.54  % (4560)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.30/0.54  % (4566)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.30/0.55  % (4570)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.30/0.55  % (4571)Refutation found. Thanks to Tanya!
% 1.30/0.55  % SZS status Theorem for theBenchmark
% 1.30/0.55  % (4562)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.30/0.55  % (4569)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.30/0.55  % SZS output start Proof for theBenchmark
% 1.30/0.55  fof(f435,plain,(
% 1.30/0.55    $false),
% 1.30/0.55    inference(avatar_sat_refutation,[],[f83,f92,f101,f126,f140,f241,f246,f344,f415])).
% 1.30/0.55  fof(f415,plain,(
% 1.30/0.55    spl2_3 | ~spl2_5 | ~spl2_11),
% 1.30/0.55    inference(avatar_contradiction_clause,[],[f414])).
% 1.30/0.55  fof(f414,plain,(
% 1.30/0.55    $false | (spl2_3 | ~spl2_5 | ~spl2_11)),
% 1.30/0.55    inference(subsumption_resolution,[],[f413,f90])).
% 1.30/0.55  fof(f90,plain,(
% 1.30/0.55    sK0 != sK1 | spl2_3),
% 1.30/0.55    inference(avatar_component_clause,[],[f89])).
% 1.30/0.55  fof(f89,plain,(
% 1.30/0.55    spl2_3 <=> sK0 = sK1),
% 1.30/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.30/0.55  fof(f413,plain,(
% 1.30/0.55    sK0 = sK1 | (~spl2_5 | ~spl2_11)),
% 1.30/0.55    inference(forward_demodulation,[],[f394,f68])).
% 1.30/0.55  fof(f68,plain,(
% 1.30/0.55    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 1.30/0.55    inference(definition_unfolding,[],[f41,f65])).
% 1.30/0.55  fof(f65,plain,(
% 1.30/0.55    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 1.30/0.55    inference(definition_unfolding,[],[f45,f40])).
% 1.30/0.55  fof(f40,plain,(
% 1.30/0.55    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 1.30/0.55    inference(cnf_transformation,[],[f14])).
% 1.30/0.55  fof(f14,axiom,(
% 1.30/0.55    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 1.30/0.55  fof(f45,plain,(
% 1.30/0.55    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 1.30/0.55    inference(cnf_transformation,[],[f19])).
% 1.30/0.55  fof(f19,axiom,(
% 1.30/0.55    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).
% 1.30/0.55  fof(f41,plain,(
% 1.30/0.55    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.30/0.55    inference(cnf_transformation,[],[f15])).
% 1.30/0.55  fof(f15,axiom,(
% 1.30/0.55    ! [X0] : k2_subset_1(X0) = X0),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.30/0.55  fof(f394,plain,(
% 1.30/0.55    sK1 = k3_subset_1(sK0,k1_xboole_0) | (~spl2_5 | ~spl2_11)),
% 1.30/0.55    inference(backward_demodulation,[],[f139,f392])).
% 1.30/0.55  fof(f392,plain,(
% 1.30/0.55    k1_xboole_0 = k3_subset_1(sK0,sK1) | ~spl2_11),
% 1.30/0.55    inference(forward_demodulation,[],[f390,f43])).
% 1.30/0.55  fof(f43,plain,(
% 1.30/0.55    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.30/0.55    inference(cnf_transformation,[],[f9])).
% 1.30/0.55  fof(f9,axiom,(
% 1.30/0.55    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.30/0.55  fof(f390,plain,(
% 1.30/0.55    k3_subset_1(sK0,sK1) = k5_xboole_0(sK1,sK1) | ~spl2_11),
% 1.30/0.55    inference(superposition,[],[f225,f343])).
% 1.30/0.55  fof(f343,plain,(
% 1.30/0.55    sK1 = k5_xboole_0(sK1,k3_subset_1(sK0,sK1)) | ~spl2_11),
% 1.30/0.55    inference(avatar_component_clause,[],[f341])).
% 1.30/0.55  fof(f341,plain,(
% 1.30/0.55    spl2_11 <=> sK1 = k5_xboole_0(sK1,k3_subset_1(sK0,sK1))),
% 1.30/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 1.30/0.55  fof(f225,plain,(
% 1.30/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 1.30/0.55    inference(backward_demodulation,[],[f141,f224])).
% 1.30/0.55  fof(f224,plain,(
% 1.30/0.55    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 1.30/0.55    inference(forward_demodulation,[],[f223,f222])).
% 1.30/0.55  fof(f222,plain,(
% 1.30/0.55    ( ! [X0] : (k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0) )),
% 1.30/0.55    inference(forward_demodulation,[],[f221,f169])).
% 1.30/0.55  fof(f169,plain,(
% 1.30/0.55    ( ! [X4] : (k3_tarski(k2_enumset1(X4,X4,X4,k1_xboole_0)) = X4) )),
% 1.30/0.55    inference(forward_demodulation,[],[f168,f154])).
% 1.30/0.55  fof(f154,plain,(
% 1.30/0.55    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.30/0.55    inference(forward_demodulation,[],[f153,f68])).
% 1.30/0.55  fof(f153,plain,(
% 1.30/0.55    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0)) )),
% 1.30/0.55    inference(forward_demodulation,[],[f148,f114])).
% 1.30/0.55  fof(f114,plain,(
% 1.30/0.55    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) )),
% 1.30/0.55    inference(superposition,[],[f102,f46])).
% 1.30/0.55  fof(f46,plain,(
% 1.30/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.30/0.55    inference(cnf_transformation,[],[f1])).
% 1.30/0.55  fof(f1,axiom,(
% 1.30/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.30/0.55  % (4567)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.30/0.55  fof(f102,plain,(
% 1.30/0.55    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.30/0.55    inference(unit_resulting_resolution,[],[f39,f53])).
% 1.30/0.55  fof(f53,plain,(
% 1.30/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.30/0.55    inference(cnf_transformation,[],[f25])).
% 1.30/0.55  fof(f25,plain,(
% 1.30/0.55    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.30/0.55    inference(ennf_transformation,[],[f5])).
% 1.30/0.55  fof(f5,axiom,(
% 1.30/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.30/0.55  fof(f39,plain,(
% 1.30/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.30/0.55    inference(cnf_transformation,[],[f6])).
% 1.30/0.55  fof(f6,axiom,(
% 1.30/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.30/0.55  fof(f148,plain,(
% 1.30/0.55    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) )),
% 1.30/0.55    inference(unit_resulting_resolution,[],[f42,f73])).
% 1.30/0.55  fof(f73,plain,(
% 1.30/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 1.30/0.55    inference(definition_unfolding,[],[f54,f50])).
% 1.30/0.55  fof(f50,plain,(
% 1.30/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.30/0.55    inference(cnf_transformation,[],[f3])).
% 1.30/0.55  fof(f3,axiom,(
% 1.30/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.30/0.55  fof(f54,plain,(
% 1.30/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.30/0.55    inference(cnf_transformation,[],[f26])).
% 1.30/0.55  fof(f26,plain,(
% 1.30/0.55    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.30/0.55    inference(ennf_transformation,[],[f16])).
% 1.30/0.55  fof(f16,axiom,(
% 1.30/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.30/0.55  fof(f42,plain,(
% 1.30/0.55    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.30/0.55    inference(cnf_transformation,[],[f21])).
% 1.30/0.55  % (4564)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.30/0.55  fof(f21,axiom,(
% 1.30/0.55    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.30/0.55  fof(f168,plain,(
% 1.30/0.55    ( ! [X4] : (k3_tarski(k2_enumset1(X4,X4,X4,k1_xboole_0)) = k5_xboole_0(X4,k1_xboole_0)) )),
% 1.30/0.55    inference(forward_demodulation,[],[f163,f43])).
% 1.30/0.55  fof(f163,plain,(
% 1.30/0.55    ( ! [X4] : (k3_tarski(k2_enumset1(X4,X4,X4,k1_xboole_0)) = k5_xboole_0(X4,k5_xboole_0(k1_xboole_0,k1_xboole_0))) )),
% 1.30/0.55    inference(superposition,[],[f71,f102])).
% 1.30/0.55  fof(f71,plain,(
% 1.30/0.55    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.30/0.55    inference(definition_unfolding,[],[f51,f64,f50])).
% 1.30/0.55  fof(f64,plain,(
% 1.30/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 1.30/0.55    inference(definition_unfolding,[],[f48,f63])).
% 1.30/0.55  fof(f63,plain,(
% 1.30/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.30/0.55    inference(definition_unfolding,[],[f49,f61])).
% 1.30/0.55  fof(f61,plain,(
% 1.30/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.30/0.55    inference(cnf_transformation,[],[f12])).
% 1.30/0.55  fof(f12,axiom,(
% 1.30/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.30/0.55  fof(f49,plain,(
% 1.30/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.30/0.55    inference(cnf_transformation,[],[f11])).
% 1.30/0.55  fof(f11,axiom,(
% 1.30/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.30/0.55  fof(f48,plain,(
% 1.30/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.30/0.55    inference(cnf_transformation,[],[f13])).
% 1.30/0.55  fof(f13,axiom,(
% 1.30/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.30/0.55  fof(f51,plain,(
% 1.30/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.30/0.55    inference(cnf_transformation,[],[f10])).
% 1.30/0.55  fof(f10,axiom,(
% 1.30/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.30/0.55  fof(f221,plain,(
% 1.30/0.55    ( ! [X0] : (k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = k3_tarski(k2_enumset1(X0,X0,X0,X0))) )),
% 1.30/0.55    inference(forward_demodulation,[],[f218,f43])).
% 1.30/0.55  fof(f218,plain,(
% 1.30/0.55    ( ! [X0] : (k3_tarski(k2_enumset1(X0,X0,X0,X0)) = k3_tarski(k2_enumset1(X0,X0,X0,k5_xboole_0(X0,X0)))) )),
% 1.30/0.55    inference(superposition,[],[f72,f103])).
% 1.30/0.55  fof(f103,plain,(
% 1.30/0.55    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.30/0.55    inference(unit_resulting_resolution,[],[f74,f53])).
% 1.30/0.55  fof(f74,plain,(
% 1.30/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.30/0.55    inference(equality_resolution,[],[f59])).
% 1.30/0.55  fof(f59,plain,(
% 1.30/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.30/0.55    inference(cnf_transformation,[],[f35])).
% 1.30/0.55  fof(f35,plain,(
% 1.30/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.30/0.55    inference(flattening,[],[f34])).
% 1.30/0.55  fof(f34,plain,(
% 1.30/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.30/0.55    inference(nnf_transformation,[],[f2])).
% 1.30/0.55  fof(f2,axiom,(
% 1.30/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.30/0.55  fof(f72,plain,(
% 1.30/0.55    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 1.30/0.55    inference(definition_unfolding,[],[f52,f64,f50,f64])).
% 1.30/0.55  fof(f52,plain,(
% 1.30/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.30/0.55    inference(cnf_transformation,[],[f7])).
% 1.30/0.55  fof(f7,axiom,(
% 1.30/0.55    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.30/0.55  fof(f223,plain,(
% 1.30/0.55    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = k3_tarski(k2_enumset1(X1,X1,X1,X1))) )),
% 1.30/0.55    inference(forward_demodulation,[],[f219,f141])).
% 1.30/0.55  fof(f219,plain,(
% 1.30/0.55    ( ! [X1] : (k3_tarski(k2_enumset1(X1,X1,X1,X1)) = k5_xboole_0(X1,k5_xboole_0(X1,X1))) )),
% 1.30/0.55    inference(superposition,[],[f71,f103])).
% 1.30/0.55  fof(f141,plain,(
% 1.30/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 1.30/0.55    inference(superposition,[],[f62,f43])).
% 1.30/0.55  fof(f62,plain,(
% 1.30/0.55    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.30/0.55    inference(cnf_transformation,[],[f8])).
% 1.30/0.55  fof(f8,axiom,(
% 1.30/0.55    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.30/0.55  fof(f139,plain,(
% 1.30/0.55    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) | ~spl2_5),
% 1.30/0.55    inference(avatar_component_clause,[],[f137])).
% 1.30/0.55  fof(f137,plain,(
% 1.30/0.55    spl2_5 <=> sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))),
% 1.30/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.30/0.55  fof(f344,plain,(
% 1.30/0.55    spl2_11 | ~spl2_7 | ~spl2_8),
% 1.30/0.55    inference(avatar_split_clause,[],[f271,f243,f238,f341])).
% 1.30/0.55  fof(f238,plain,(
% 1.30/0.55    spl2_7 <=> k3_subset_1(sK0,sK1) = k3_xboole_0(k3_subset_1(sK0,sK1),sK1)),
% 1.30/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 1.30/0.55  fof(f243,plain,(
% 1.30/0.55    spl2_8 <=> k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 1.30/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 1.30/0.55  fof(f271,plain,(
% 1.30/0.55    sK1 = k5_xboole_0(sK1,k3_subset_1(sK0,sK1)) | (~spl2_7 | ~spl2_8)),
% 1.30/0.55    inference(forward_demodulation,[],[f268,f270])).
% 1.30/0.55  fof(f270,plain,(
% 1.30/0.55    sK1 = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK0)) | (~spl2_7 | ~spl2_8)),
% 1.30/0.55    inference(forward_demodulation,[],[f267,f264])).
% 1.30/0.55  fof(f264,plain,(
% 1.30/0.55    sK1 = k3_tarski(k2_enumset1(sK1,sK1,sK1,k3_subset_1(sK0,sK1))) | ~spl2_7),
% 1.30/0.55    inference(forward_demodulation,[],[f263,f169])).
% 1.30/0.55  fof(f263,plain,(
% 1.30/0.55    k3_tarski(k2_enumset1(sK1,sK1,sK1,k3_subset_1(sK0,sK1))) = k3_tarski(k2_enumset1(sK1,sK1,sK1,k1_xboole_0)) | ~spl2_7),
% 1.30/0.55    inference(forward_demodulation,[],[f258,f43])).
% 1.30/0.55  fof(f258,plain,(
% 1.30/0.55    k3_tarski(k2_enumset1(sK1,sK1,sK1,k3_subset_1(sK0,sK1))) = k3_tarski(k2_enumset1(sK1,sK1,sK1,k5_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1)))) | ~spl2_7),
% 1.30/0.55    inference(superposition,[],[f72,f240])).
% 1.30/0.55  % (4567)Refutation not found, incomplete strategy% (4567)------------------------------
% 1.30/0.55  % (4567)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.55  % (4567)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.55  
% 1.30/0.55  % (4567)Memory used [KB]: 10618
% 1.30/0.55  % (4567)Time elapsed: 0.136 s
% 1.30/0.55  % (4567)------------------------------
% 1.30/0.55  % (4567)------------------------------
% 1.30/0.55  fof(f240,plain,(
% 1.30/0.55    k3_subset_1(sK0,sK1) = k3_xboole_0(k3_subset_1(sK0,sK1),sK1) | ~spl2_7),
% 1.30/0.55    inference(avatar_component_clause,[],[f238])).
% 1.30/0.55  fof(f267,plain,(
% 1.30/0.55    k3_tarski(k2_enumset1(sK1,sK1,sK1,k3_subset_1(sK0,sK1))) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK0)) | ~spl2_8),
% 1.30/0.55    inference(superposition,[],[f72,f245])).
% 1.30/0.55  fof(f245,plain,(
% 1.30/0.55    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | ~spl2_8),
% 1.30/0.55    inference(avatar_component_clause,[],[f243])).
% 1.30/0.55  fof(f268,plain,(
% 1.30/0.55    k3_tarski(k2_enumset1(sK1,sK1,sK1,sK0)) = k5_xboole_0(sK1,k3_subset_1(sK0,sK1)) | ~spl2_8),
% 1.30/0.55    inference(superposition,[],[f71,f245])).
% 1.30/0.55  fof(f246,plain,(
% 1.30/0.55    spl2_8 | ~spl2_1),
% 1.30/0.55    inference(avatar_split_clause,[],[f149,f80,f243])).
% 1.30/0.55  fof(f80,plain,(
% 1.30/0.55    spl2_1 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.30/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.30/0.55  fof(f149,plain,(
% 1.30/0.55    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | ~spl2_1),
% 1.30/0.55    inference(unit_resulting_resolution,[],[f82,f73])).
% 1.30/0.55  fof(f82,plain,(
% 1.30/0.55    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl2_1),
% 1.30/0.55    inference(avatar_component_clause,[],[f80])).
% 1.30/0.55  fof(f241,plain,(
% 1.30/0.55    spl2_7 | ~spl2_2),
% 1.30/0.55    inference(avatar_split_clause,[],[f133,f85,f238])).
% 1.30/0.55  fof(f85,plain,(
% 1.30/0.55    spl2_2 <=> r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.30/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.30/0.55  fof(f133,plain,(
% 1.30/0.55    k3_subset_1(sK0,sK1) = k3_xboole_0(k3_subset_1(sK0,sK1),sK1) | ~spl2_2),
% 1.30/0.55    inference(unit_resulting_resolution,[],[f87,f53])).
% 1.30/0.55  fof(f87,plain,(
% 1.30/0.55    r1_tarski(k3_subset_1(sK0,sK1),sK1) | ~spl2_2),
% 1.30/0.55    inference(avatar_component_clause,[],[f85])).
% 1.30/0.55  fof(f140,plain,(
% 1.30/0.55    spl2_5 | ~spl2_1),
% 1.30/0.55    inference(avatar_split_clause,[],[f131,f80,f137])).
% 1.30/0.55  fof(f131,plain,(
% 1.30/0.55    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) | ~spl2_1),
% 1.30/0.55    inference(unit_resulting_resolution,[],[f82,f55])).
% 1.30/0.55  fof(f55,plain,(
% 1.30/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 1.30/0.55    inference(cnf_transformation,[],[f27])).
% 1.30/0.55  fof(f27,plain,(
% 1.30/0.55    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.30/0.55    inference(ennf_transformation,[],[f18])).
% 1.30/0.55  fof(f18,axiom,(
% 1.30/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.30/0.55  fof(f126,plain,(
% 1.30/0.55    spl2_4),
% 1.30/0.55    inference(avatar_contradiction_clause,[],[f125])).
% 1.30/0.55  fof(f125,plain,(
% 1.30/0.55    $false | spl2_4),
% 1.30/0.55    inference(subsumption_resolution,[],[f124,f39])).
% 1.30/0.55  fof(f124,plain,(
% 1.30/0.55    ~r1_tarski(k1_xboole_0,sK0) | spl2_4),
% 1.30/0.55    inference(backward_demodulation,[],[f100,f123])).
% 1.30/0.55  fof(f123,plain,(
% 1.30/0.55    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 1.30/0.55    inference(forward_demodulation,[],[f120,f68])).
% 1.30/0.55  fof(f120,plain,(
% 1.30/0.55    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0))) )),
% 1.30/0.55    inference(unit_resulting_resolution,[],[f42,f55])).
% 1.30/0.55  fof(f100,plain,(
% 1.30/0.55    ~r1_tarski(k3_subset_1(sK0,sK0),sK0) | spl2_4),
% 1.30/0.55    inference(avatar_component_clause,[],[f98])).
% 1.30/0.55  fof(f98,plain,(
% 1.30/0.55    spl2_4 <=> r1_tarski(k3_subset_1(sK0,sK0),sK0)),
% 1.30/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.30/0.55  fof(f101,plain,(
% 1.30/0.55    ~spl2_4 | ~spl2_3),
% 1.30/0.55    inference(avatar_split_clause,[],[f95,f89,f98])).
% 1.30/0.55  fof(f95,plain,(
% 1.30/0.55    ~r1_tarski(k3_subset_1(sK0,sK0),sK0) | ~spl2_3),
% 1.30/0.55    inference(subsumption_resolution,[],[f94,f91])).
% 1.30/0.55  fof(f91,plain,(
% 1.30/0.55    sK0 = sK1 | ~spl2_3),
% 1.30/0.55    inference(avatar_component_clause,[],[f89])).
% 1.30/0.55  fof(f94,plain,(
% 1.30/0.55    ~r1_tarski(k3_subset_1(sK0,sK0),sK0) | sK0 != sK1 | ~spl2_3),
% 1.30/0.55    inference(backward_demodulation,[],[f77,f91])).
% 1.30/0.55  fof(f77,plain,(
% 1.30/0.55    sK0 != sK1 | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.30/0.55    inference(backward_demodulation,[],[f66,f68])).
% 1.30/0.55  fof(f66,plain,(
% 1.30/0.55    sK1 != k3_subset_1(sK0,k1_xboole_0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.30/0.55    inference(definition_unfolding,[],[f38,f65])).
% 1.30/0.55  fof(f38,plain,(
% 1.30/0.55    sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.30/0.55    inference(cnf_transformation,[],[f32])).
% 1.30/0.55  fof(f32,plain,(
% 1.30/0.55    (sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.30/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f31])).
% 1.30/0.55  fof(f31,plain,(
% 1.30/0.55    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.30/0.55    introduced(choice_axiom,[])).
% 1.30/0.55  fof(f30,plain,(
% 1.30/0.55    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.30/0.55    inference(flattening,[],[f29])).
% 1.30/0.55  fof(f29,plain,(
% 1.30/0.55    ? [X0,X1] : (((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.30/0.55    inference(nnf_transformation,[],[f24])).
% 1.30/0.55  fof(f24,plain,(
% 1.30/0.55    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.30/0.55    inference(ennf_transformation,[],[f23])).
% 1.30/0.55  fof(f23,negated_conjecture,(
% 1.30/0.55    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 1.30/0.55    inference(negated_conjecture,[],[f22])).
% 1.30/0.55  fof(f22,conjecture,(
% 1.30/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).
% 1.30/0.55  fof(f92,plain,(
% 1.30/0.55    spl2_2 | spl2_3),
% 1.30/0.55    inference(avatar_split_clause,[],[f76,f89,f85])).
% 1.30/0.55  fof(f76,plain,(
% 1.30/0.55    sK0 = sK1 | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.30/0.55    inference(backward_demodulation,[],[f67,f68])).
% 1.30/0.55  fof(f67,plain,(
% 1.30/0.55    sK1 = k3_subset_1(sK0,k1_xboole_0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.30/0.55    inference(definition_unfolding,[],[f37,f65])).
% 1.30/0.55  % (4573)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.30/0.55  fof(f37,plain,(
% 1.30/0.55    sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.30/0.55    inference(cnf_transformation,[],[f32])).
% 1.30/0.55  fof(f83,plain,(
% 1.30/0.55    spl2_1),
% 1.30/0.55    inference(avatar_split_clause,[],[f36,f80])).
% 1.30/0.55  fof(f36,plain,(
% 1.30/0.55    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.30/0.55    inference(cnf_transformation,[],[f32])).
% 1.30/0.55  % SZS output end Proof for theBenchmark
% 1.30/0.55  % (4571)------------------------------
% 1.30/0.55  % (4571)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.55  % (4571)Termination reason: Refutation
% 1.30/0.55  
% 1.30/0.55  % (4571)Memory used [KB]: 11001
% 1.30/0.55  % (4571)Time elapsed: 0.125 s
% 1.30/0.55  % (4571)------------------------------
% 1.30/0.55  % (4571)------------------------------
% 1.30/0.55  % (4577)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.53/0.56  % (4550)Success in time 0.192 s
%------------------------------------------------------------------------------
